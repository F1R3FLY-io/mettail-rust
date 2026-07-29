//! MeTTaIL procedural macro for defining formal languages
//!
//! This crate provides the `language!` macro which defines a formal language with:
//! - AST types (Rust enums)
//! - Parser (PraTTaIL-generated Pratt + Recursive Descent)
//! - Rewrite engine (Ascent-based)
//! - Term generation and manipulation
//! - Metadata for REPL introspection
//! - Language implementation struct

#[cfg(test)]
mod doc_examples;
mod expansion_hook;
mod gen;
mod logic;

use proc_macro::TokenStream;
use quote::quote_spanned;
use syn::parse_macro_input;

use gen::runtime::wpda_codegen::generate_wpda_engine_module;
use gen::{
    generate_all, generate_blockly_definitions, generate_language_impl, generate_metadata,
    write_blockly_blocks, write_blockly_categories,
};
use logic::rules::generate_freshness_functions;
use logic::writer::spill_and_include;
use mettail_ast::compose::ComposeDef;
use mettail_ast::language::LanguageDef;
use mettail_ast::merge::{apply_extends, apply_includes, apply_mixins};
use mettail_ast::validation::validate_language;

/// Render a refusal as `compile_error!` tokens at `span`.
///
/// ⚠ The trailing semicolon is **load-bearing**, not style. `language!` expands
/// in ITEM position, and a macro invocation in item position must be delimited by
/// braces or followed by `;` — without it `rustc` stops at
/// "macros that expand to items must be delimited with braces or followed by a
/// semicolon", the `compile_error!` never expands, and the refusal's message is
/// never printed. The one working precedent in this tree
/// (`ident_capture_routing::enforce`) has always carried it.
fn refuse(span: proc_macro2::Span, message: &str) -> proc_macro2::TokenStream {
    quote_spanned!(span => compile_error!(#message);)
}

#[proc_macro]
pub fn language(input: TokenStream) -> TokenStream {
    // ★ Install the expansion panic hook before anything can panic. See
    // `expansion_hook`'s module docs for what it does and does NOT add: the
    // default handler already prints the payload and the `file:line`, including
    // for panics in `pipeline::analysis`'s spawned threads (measured). What only
    // the hook can supply is WHICH grammar was being expanded — one `rustc`
    // process expands all 54 of them.
    //
    // Installed here rather than in `expand_language` so the unit tests, which
    // call `expand_language` directly, never replace libtest's hook.
    expansion_hook::install();
    expand_language(input.into()).into()
}

/// The whole of `language!`, over `proc_macro2` tokens.
///
/// ★ Split out from the `#[proc_macro]` entry point so the macro boundary is
/// REACHABLE FROM A UNIT TEST. `proc_macro::TokenStream` and `parse_macro_input!`
/// both panic outside a live `rustc` bridge session, so as long as the body lived
/// in `language` itself, the only instrument that could observe a refusal was a
/// child `cargo build` — and consequently none of the boundary's nine refusal
/// paths had a test at all. Over `proc_macro2` tokens, `expand_language` is an
/// ordinary function: hand it a grammar, read the tokens it returns.
///
/// Every refusal RETURNS. None aborts. See the crate's `#[cfg(test)] mod
/// expansion_boundary` for the cells that assert on the returned text.
pub(crate) fn expand_language(input: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    // Clone input BEFORE parsing consumes it.
    let input_for_registry = input.clone();
    // Verbatim raw body source, emitted as `LanguageMetadata::definition_source`
    // so the exact augmented `LanguageDef` can be reconstructed at runtime via
    // `mettail_ast::auto_inject::reconstruct_language_def` (reproducing the same
    // `definition_fingerprint`). Captured before parse so it is byte-for-byte
    // the macro invocation body.
    let definition_source_str = input_for_registry.to_string();
    // `syn::parse2` rather than `parse_macro_input!`: identical behaviour on both
    // arms (the macro's error arm is itself `return err.to_compile_error()`), but
    // it accepts `proc_macro2` tokens and so works outside a bridge session.
    let mut language_def = match syn::parse2::<LanguageDef>(input) {
        Ok(def) => def,
        Err(e) => return e.to_compile_error(),
    };
    let lang_name = language_def.name.to_string();
    expansion_hook::entering(&lang_name);

    // Store binary-encoded input tokens in registry (no bridge types retained).
    // MUST happen before any processing so consuming grammars get the full
    // unprocessed rule set.
    // Fails closed on a name already taken in this compilation unit. Two specifications
    // sharing a `name:` would otherwise silently change what a third one's `extends:`
    // resolves to — see `ast::registry::duplicate_registration_diagnostic`.
    if let Err(msg) = mettail_ast::registry::register_language(&lang_name, &input_for_registry) {
        return refuse(language_def.name.span(), &msg);
    }

    // Apply composition clauses in order:
    // 1. extends — full inheritance (Error on duplicate labels)
    // 2. includes — grammar-only import (Override: local rules win)
    // 3. mixins — fragment import (Override: local rules win)
    if let Err(msg) = apply_extends(&mut language_def) {
        return refuse(language_def.name.span(), &format!("extends error:\n{msg}"));
    }

    if let Err(msg) = apply_includes(&mut language_def) {
        return refuse(language_def.name.span(), &format!("includes error:\n{msg}"));
    }

    if let Err(msg) = apply_mixins(&mut language_def) {
        return refuse(language_def.name.span(), &format!("mixins error:\n{msg}"));
    }

    if let Err(e) = validate_language(&language_def) {
        // The spanned renderer that has existed beside `ValidationError` since the
        // type was written, and that this boundary reached past for months.
        return e.to_compile_error();
    }

    // ★ #131 / #141-R2 — the `Ident`-capture ROUTING GATE, HOISTED to the macro
    // boundary from inside `generate_wpda_engine_module`.
    //
    // # Why the gate had to move, and what it did not guard where it was
    //
    // Its former home is the ELEVENTH thing this function runs. `generate_all`
    // below is the SECOND, and it reaches all 421 authored refusal sites in
    // `prattail` — including the hardened category lookups this gate exists to
    // stand in front of. Worse, a gate that returns tokens from
    // `generate_wpda_engine_module` returns them as THAT MODULE'S CONTRIBUTION:
    // `language!` kept going and still spilled five `include!` files to
    // `target/generated/<lang>/` for a grammar it had already rejected. For the
    // #131 fault the gate and its fault happened to live in the same function, so
    // it worked; for anything upstream it was a gate in name only.
    //
    // A gate must live where it can `return` THE WHOLE EXPANSION. That is here.
    //
    // # Why this position and not one further down
    //
    // It sits above `emit_auto_injection_rules` deliberately, and the verdict is
    // provably unchanged by that: auto-injection appends to `language_def.terms`
    // and `.rewrites` only (`AutoInjectionOutput` has exactly those two fields),
    // never to `.types` — and the gate's two classifiers read the rule itself
    // (`classify_rule_public`) and `language.types` (`classify_binder_in`). The
    // injected rules are `<Source>To<Target> . v:Source |- v : Target`, which
    // declare no `Ident` param and so contribute no violations of their own.
    // Rejecting before synthesising rules for a grammar that is already refused
    // is strictly less work.
    if let Some(errors) = gen::runtime::wpda_codegen::ident_capture_routing::enforce(&language_def)
    {
        return errors;
    }

    // Stage 3.13 (2026-04-30): auto-injection codegen — append synthetic
    // `<Source>To<Target> . v:Source |- v : Target ;` rules for every
    // lossless built-in promotion edge declared in the language. Runs
    // AFTER composition (so extends/includes/mixins have settled) and
    // BEFORE downstream codegen (so synthetic rules participate in
    // FIRST/FOLLOW, BP analysis, lint, etc. byte-identically to
    // user-written rules). User-defined injections are skip-listed via
    // shape match. See `macros/src/gen/runtime/wpda_codegen/auto_inject.rs`.
    //
    // Stage 3.13e (2026-05-01): also append synthetic congruence rewrites
    // (`<Source>To<Target>Cong . | S ~> T |- (<Source>To<Target> S) ~>
    // (<Source>To<Target> T) ;`) so the rewrite engine propagates inner
    // `rw_<source>` reductions through the cast wrapper into
    // `rw_<target>`. Without these, auto-injected casts absorb inner
    // reductions but never surface them — affecting 214/1331 calc_op +
    // 148/532 rho_op tests.
    let auto_inject_output =
        crate::gen::runtime::wpda_codegen::auto_inject::emit_auto_injection_rules(&language_def);
    language_def.terms.extend(auto_inject_output.terms);
    language_def.rewrites.extend(auto_inject_output.rewrites);

    // Phase 3F (predicated types): stratification analysis. Walks the
    // language's logic relations and ?guard:Guard predicates to detect
    // negation cycles. Non-stratifiable programs make Ascent's fixpoint
    // semantics undefined, so this is a hard error (STRAT01).
    //
    // ★ EVERY violation is reported, not the first. `abort!` diverged, so the
    // loop that used to stand here could never complete a second iteration and
    // carried an `#[allow(clippy::never_loop)]` to say so; an author with three
    // negation cycles fixed one per build. `compile_errors` emits one
    // `compile_error!` per cycle, which is what `ident_capture_routing::enforce`
    // has always done for its own violations.
    let strat_report = logic::stratification::analyze(&language_def);
    if let Some(errors) = strat_report.compile_errors(language_def.name.span()) {
        return errors;
    }

    // Stage-instrumentation (gated by the `walker-trace` feature +
    // `PRATTAIL_MACRO_TRACE=1`): emits a `[macro-trace] <lang> <stage>` line
    // before each heavy phase so the operator can see exactly which stage
    // exceeds the memory budget when a grammar OOMs. The env read compiles out
    // entirely on the default build (feature off ⇒ `trace` is a constant
    // `false` and every `stage!` body below is dead-stripped). `trace_diag!`'s
    // block form cannot gate a `let` initializer, so this uses the
    // `#[cfg]`/off-value idiom (see prattail/src/trace.rs module docs).
    let trace = {
        #[cfg(feature = "walker-trace")]
        {
            std::env::var("PRATTAIL_MACRO_TRACE").is_ok()
        }
        #[cfg(not(feature = "walker-trace"))]
        {
            false
        }
    };
    macro_rules! stage {
        ($name:literal) => {
            if trace {
                eprintln!("[macro-trace] {} {}", lang_name, $name);
            }
        };
    }

    stage!("generate_all.start");
    // Generate the Rust AST types and operations (also captures WFST pipeline analysis).
    //
    // ★ #141 change 7 — `generate_all` is fallible. Everything downstream of it
    // (`prattail`'s lexer soundness gates, the `LanguageSpec` bridge's option
    // decoding) hands its refusal back as a `String` instead of panicking inside
    // a cranelift-compiled proc macro, where a panic aborts `rustc` outright. The
    // refusal becomes a diagnostic HERE, at the only place that holds a span.
    let (ast_code, pipeline_analysis) = match generate_all(&language_def) {
        Ok(generated) => generated,
        Err(rejection) => return refuse(language_def.name.span(), &rejection),
    };
    stage!("generate_all.done");

    stage!("generate_freshness_functions.start");
    // Generate freshness functions (needed by Ascent rewrite clauses)
    let freshness_fns = generate_freshness_functions(&language_def);
    stage!("generate_freshness_functions.done");

    stage!("lowering_disposition_inventory.start");
    // Task #94: derive the LOWERING-DISPOSITION INVENTORY once, here, and hand it to the
    // metadata generator. One entry per declared equation orientation, rewrite, and fold,
    // recording whether the runtime lowering delivered it, delegated it to a named lane,
    // suppressed it by an explicit decision, or declined it outright. Deriving it at the top
    // level — rather than inside whichever report generator happens to run — is what makes the
    // published inventory and the lowering that produced it the same computation.
    // ★ #141 G9 — the inventory's completeness census refuses by returning tokens.
    // EMPTY for every language whose declared constructs are all accounted for,
    // which is every shipped one; non-empty it is a `compile_error!` naming the
    // constructs that left the lowering without a disposition.
    let (lowering_dispositions, disposition_refusal) =
        gen::runtime::dovetail_report::lowering_disposition_inventory(&language_def);
    stage!("lowering_disposition_inventory.done");

    stage!("generate_metadata.start");
    // Generate metadata for REPL introspection.
    //
    // ★ #141 Part A — fallible for the same reason `generate_all` is, and through
    // the same bridge. The reflected equational theory renders through `Display`'s
    // binding-power table; when the shared `LanguageDef → LanguageSpec` bridge
    // cannot decode an `options` value, that table cannot be built, and a reflection
    // rendered without it is a WRONG answer (every axiom collapses to a
    // bracket-free tautology) rather than a degraded one. The refusal becomes a
    // diagnostic here, at the only place that holds a span.
    let metadata_code =
        match generate_metadata(&language_def, &definition_source_str, &lowering_dispositions) {
            Ok(tokens) => tokens,
            Err(rejection) => return refuse(language_def.name.span(), &rejection),
        };
    stage!("generate_metadata.done");

    stage!("generate_language_impl.start");
    // Generate language implementation struct (Term wrapper + Language struct).
    // The legacy Ascent runtime backend was retired (P6); `run_ascent` resolves to
    // the fail-closed `Language` trait default, so no engine content is threaded here.
    let language_code = generate_language_impl(&language_def);
    stage!("generate_language_impl.done");

    // W7 Stage 6: WPDS-runtime engine for the language.
    // Emits a `<Lang>WpdaEngine` struct and `WpdaEngine` impl. Walker
    // (WPDS) is the sole parser backend post-Stage-10. See
    // `prattail/docs/design/wpds-migration-survey.md`.
    stage!("generate_wpda_engine_module.start");
    let wpda_engine_code = generate_wpda_engine_module(&language_def);
    stage!("generate_wpda_engine_module.done");

    // Generate test file for cargo test / cargo nextest integration.
    // Gated by `options { emit_tests: true }` (default: true).
    let emit_tests = language_def
        .options
        .get("emit_tests")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    // For a library-hosted language this writes `languages/tests/gen_{lang}_*.rs`
    // and returns nothing. For a TEST-hosted one (`options { hosted_in: … }`) it
    // returns the opt-in `{lang}_generated_tests!` wrapper, which must be spliced
    // into the expansion — the generated suite has no other way to reach a
    // definition that no longer lives in `mettail_languages`.
    let generated_test_suite = if emit_tests {
        gen::test_gen::write_test_file(&language_def, &pipeline_analysis)
    } else {
        proc_macro2::TokenStream::new()
    };

    // Generate per-language simulation CLI binary. Gated by
    // `options { emit_simulator: true }` (default: true). Like the test suite, the body is
    // spilled to `target/generated/<lang>/` and reached through an opt-in wrapper that the
    // hand-written `[[bin]]` host invokes, so the tokens must be spliced in.
    let generated_simulation_main =
        gen::test_gen::write_simulation_binary_if_enabled(&language_def);

    // Generate Blockly block definitions.
    // Gated by `options { emit_blockly: true }` (default: true).
    let emit_blockly = language_def
        .options
        .get("emit_blockly")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    if emit_blockly {
        let blockly_output = generate_blockly_definitions(&language_def);
        if let Err(e) = write_blockly_blocks(&language_def.name.to_string(), &blockly_output) {
            eprintln!("Warning: Failed to write Blockly blocks: {}", e);
        }
        if let Err(e) = write_blockly_categories(&language_def.name.to_string(), &blockly_output) {
            eprintln!("Warning: Failed to write Blockly categories: {}", e);
        }
    }

    // Generate public proptest strategies (gated behind `strategies` feature)
    let public_strategies = gen::test_gen::strategies::generate_public_strategies(&language_def);

    // Spill each large emitter to disk and replace it with an `include!` wrapper.
    // Purpose: the proc-macro → rustc bridge ships TokenStreams by value, so a
    // multi-MB returned TokenStream costs 2× that in RSS (proc-macro copy +
    // rustc copy). Writing the content to `target/generated/<lang>/<mod>.rs`
    // and returning `include!("...")` lets rustc load the source directly
    // from disk during expansion, keeping the bridge tiny. It also gives
    // humans readable files to diff and inspect after compilation.
    let ast_include = spill_and_include(&lang_name, "ast", ast_code);
    let freshness_include = spill_and_include(&lang_name, "freshness", freshness_fns);
    let metadata_include = spill_and_include(&lang_name, "metadata", metadata_code);
    let language_include = spill_and_include(&lang_name, "language", language_code);
    let wpda_include = spill_and_include(&lang_name, "wpda", wpda_engine_code);
    let strategies_include = spill_and_include(&lang_name, "strategies", public_strategies);

    quote::quote! {
        // ★ #141 G9 — the lowering-disposition census's refusal. EMPTY for every
        // language whose declared constructs are all accounted for.
        #disposition_refusal
        #ast_include
        #freshness_include
        #metadata_include
        #language_include
        #wpda_include

        /// Public proptest strategies for generating random well-formed terms.
        ///
        /// Enabled by the `strategies` feature flag. Provides tape-based
        /// iterative term builders and `arb_{cat}(max_depth)` strategy
        /// functions for property-based testing by external crates.
        #[cfg(feature = "strategies")]
        pub mod strategies {
            use super::*;
            use proptest::prelude::*;
            use proptest::strategy::BoxedStrategy;
            #strategies_include
        }

        // The opt-in `{lang}_generated_tests!` wrapper, which a hand-written host test
        // binary invokes to materialize the generated suite. Empty under
        // `options { emit_tests: false }`.
        #generated_test_suite

        // The `{lang}_simulation_main!` wrapper, which the hand-written
        // `languages/src/bin/simulate_{lang}.rs` host invokes. Empty under
        // `options { emit_simulator: false }`.
        #generated_simulation_main
    }
}

/// Define a reusable grammar fragment (types + terms only, no equations/rewrites/logic).
///
/// Fragments are stored in the in-process registry and can be mixed into
/// `language!` definitions via `mixins: [FragmentName]`.
///
/// ```
/// use mettail_macros::language_fragment;
///
/// language_fragment! {
///     name: ArithOps,
///     types { ![i32] as Int },
///     terms {
///         NumLit . |- Integer : Int;
///         Add . a:Int, b:Int |- a "+" b : Int ![ a + b ] fold;
///     }
/// }
/// ```
#[proc_macro]
pub fn language_fragment(input: TokenStream) -> TokenStream {
    // Clone input BEFORE parse_macro_input! consumes it.
    let input_for_registry: proc_macro2::TokenStream = input.clone().into();
    let fragment_def = parse_macro_input!(input as mettail_ast::fragment::FragmentDef);

    // Validate: all category references in terms exist in types
    if let Err(msg) = mettail_ast::fragment::validate_fragment(&fragment_def) {
        return refuse(fragment_def.name.span(), &msg).into();
    }

    let frag_name = fragment_def.name.to_string();
    // Fails closed on a name already taken in this compilation unit — fragments and
    // languages share one namespace because `lookup_language_def` resolves both.
    if let Err(msg) = mettail_ast::registry::register_fragment(&frag_name, &input_for_registry) {
        return refuse(fragment_def.name.span(), &msg).into();
    }

    // Fragments generate NO code — the consuming language! generates everything
    TokenStream::new()
}

/// Compose independently defined languages into a single unified language.
///
/// The composed language delegates all operations (parsing, ascent, env, etc.)
/// to the constituent sub-languages. Parsing tries each sub-language in
/// declaration order and returns the first success.
///
// ignore-justification: the expansion names `mettail_runtime::{Term, Language, ...}` and the caller-supplied `calculator`/`rholang` modules; `macros` depends on neither (and cannot depend on `languages`, which depends on `macros`), so this invocation cannot compile from inside this crate. Verified by compiling it: E0433 on `mettail_runtime`, `calculator`, `rholang`.
/// ```ignore
/// compose_languages! {
///     name: Combined,
///     languages: [calculator::Calculator, rholang::Rholang],
/// }
/// ```
///
/// This generates:
/// - `CombinedTermInner` enum with one variant per sub-language
/// - `CombinedTerm` wrapper implementing `mettail_runtime::Term`
/// - `CombinedEnv` struct with per-sub-language environments
/// - `CombinedMetadata` aggregating sub-language metadata
/// - `CombinedLanguage` struct implementing `mettail_runtime::Language`
#[proc_macro]
pub fn compose_languages(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as ComposeDef);
    let code = gen::compose_gen::generate_composed_language(&def);
    TokenStream::from(code)
}

/// ★ THE MACRO BOUNDARY'S REFUSAL PATHS, asserted on the tokens they return.
///
/// # Why these cells can exist at all, and why they did not before
///
/// Every cell here calls [`expand_language`] — the body of `language!`, split out
/// of the `#[proc_macro]` entry point precisely so a test can reach it. Before
/// that split there was no in-process instrument: `proc_macro::TokenStream` and
/// `parse_macro_input!` both require a live `rustc` bridge session, so the only
/// way to observe a refusal was a child `cargo build`, and consequently none of
/// the boundary's refusals had a test.
///
/// # ⚠ Discipline these cells are held to
///
/// * **No cell expects a panic.** No `#[should_panic]`, no `catch_unwind`. The
///   assertions are on returned token TEXT. (Under the pre-#141 boundary these
///   same calls would have *killed the test binary*: `abort!` diverges, and a
///   panic in a cranelift-compiled crate aborts the process rather than
///   unwinding. That the calls now RETURN is itself the repair being asserted.)
/// * **Every cell exercises a REFUSAL, which returns before any generator runs.**
///   That is not incidental: a cell that let an expansion succeed would write six
///   files into `target/generated/<lang>/` as a side effect of running, and the
///   campaign's generated-output manifest treats that directory as evidence.
/// * **The mutation is asserted to have applied**, and each cell carries a
///   control that must NOT discriminate.
#[cfg(test)]
mod expansion_boundary {
    use super::*;
    use proc_macro2::Span;
    use quote::quote;

    /// A minimal grammar body, parameterised by its `name:` token.
    ///
    /// `emit_*: false` keeps the fixture from reaching the test/simulator/Blockly
    /// writers even if a cell were ever to let an expansion through.
    fn well_formed_source(name: &str) -> proc_macro2::TokenStream {
        let name = syn::Ident::new(name, Span::call_site());
        quote! {
            name: #name,
            options { emit_tests: false, emit_simulator: false, emit_blockly: false },
            types { Term },
            terms {
                Plus . a:Term, b:Term |- a "+" b : Term;
            },
        }
    }

    /// The same grammar with one rule mutated to declare an `Ident` param in the
    /// Pratt machine's LEFT-OPERAND position — a position that has no
    /// representation, since an LHS is a parsed sub-term of a declared category
    /// and `Ident` is a token class. `#[n_violations]` rules carry the fault.
    fn unrouted_ident_source(name: &str, n_violations: usize) -> proc_macro2::TokenStream {
        let name = syn::Ident::new(name, Span::call_site());
        let rules = (0..n_violations).map(|i| {
            let label = syn::Ident::new(&format!("Unrouted{i}"), Span::call_site());
            let param = syn::Ident::new(&format!("m{i}"), Span::call_site());
            let literal = format!("+{i}");
            quote! { #label . #param:Ident, x:Term |- #param #literal x : Term; }
        });
        quote! {
            name: #name,
            options { emit_tests: false, emit_simulator: false, emit_blockly: false },
            types { Term },
            terms {
                Plus . a:Term, b:Term |- a "+" b : Term;
                #(#rules)*
            },
        }
    }

    /// ★ #141 change 2 — a duplicate `name:` RETURNS a `compile_error!` naming
    /// the offending language, instead of `abort!`ing.
    ///
    /// MUTATION: `RedDupAlpha` is already in the registry when the expansion
    /// begins — exactly the state a second `language! { name: RedDupAlpha }` in
    /// one crate produces. Registered directly rather than by expanding the first
    /// declaration, because a successful expansion writes six files to
    /// `target/generated/`.
    ///
    /// CONTROL that must NOT discriminate: `RedDupBeta` is registered too. A
    /// message that named it would mean the diagnostic reports "some duplicate"
    /// rather than *this* one, and a whole-string assertion would not have
    /// caught it — a vacuous-witness failure this campaign has already recorded
    /// once.
    #[test]
    fn a_duplicate_name_returns_a_compile_error_naming_that_language() {
        let body = quote! { name: RedDupAlpha, types { Term } };
        mettail_ast::registry::register_language("RedDupAlpha", &body)
            .expect("first registration must succeed — the registry is thread-local");
        mettail_ast::registry::register_language("RedDupBeta", &body)
            .expect("the control name must register cleanly");

        // MUTATION APPLIED: the two sources differ in exactly the `name:` token.
        let mutated = well_formed_source("RedDupAlpha").to_string();
        let control = well_formed_source("RedDupBeta").to_string();
        assert_eq!(
            mutated.replace("RedDupAlpha", "@"),
            control.replace("RedDupBeta", "@"),
            "the fixtures must differ in the name token and nothing else",
        );

        let rendered = expand_language(well_formed_source("RedDupAlpha")).to_string();
        assert!(
            rendered.contains("compile_error"),
            "the refusal must be a `compile_error!`, not a diverging abort: {rendered}",
        );
        assert!(
            rendered.contains("duplicate definition name"),
            "the refusal must carry the registry's diagnostic: {rendered}",
        );
        assert!(
            rendered.contains("RedDupAlpha"),
            "★ the diagnostic must name the OFFENDING language: {rendered}",
        );
        assert!(
            !rendered.contains("RedDupBeta"),
            "★ …and not the other registered one — the message must track the \
             input, not merely mention a duplicate: {rendered}",
        );
    }

    /// ★ #141-R2 — the `Ident`-routing gate now discards THE WHOLE EXPANSION.
    ///
    /// This is the assertion the hoist exists for. In its former home
    /// (`generate_wpda_engine_module`, the eleventh generator) the gate's tokens
    /// replaced one module's contribution and `language!` carried on: it still
    /// ran `generate_all` — all 421 of `prattail`'s authored refusal sites —
    /// and still spilled five `include!` files for a grammar it had rejected.
    ///
    /// Two independent witnesses that nothing downstream ran:
    ///   1. the returned tokens contain no `include!`, which every spilled
    ///      generator emits exactly one of;
    ///   2. `target/generated/<lang>/` was never created.
    ///
    /// CONTROL that must NOT discriminate: `Plus`, a perfectly routed rule, sits
    /// in the same grammar and contributes no violation of its own.
    #[test]
    fn an_unrouted_ident_discards_the_whole_expansion() {
        let source = unrouted_ident_source("RedGateOne", 1);

        // MUTATION APPLIED: the fixture really does declare an `Ident` param.
        let printed = source.to_string();
        assert!(
            printed.contains("m0 : Ident"),
            "the fixture must declare the `Ident` param under test: {printed}",
        );

        let rendered = expand_language(source).to_string();
        assert!(
            rendered.contains("compile_error"),
            "the gate must refuse this grammar: {rendered}",
        );
        for needle in ["Unrouted0", "m0", "has no token consumer", "leading position"] {
            assert!(
                rendered.contains(needle),
                "the diagnostic must contain {needle:?}: {rendered}",
            );
        }
        assert!(
            !rendered.contains("Plus"),
            "the correctly routed rule in the same grammar must not be blamed: {rendered}",
        );

        // ★ WITNESS 1 — no generator's output reached the expansion.
        assert!(
            !rendered.contains("include"),
            "★ R2: a rejected grammar must yield ONLY the refusal — an `include!` \
             here would mean a spilled generator ran anyway: {rendered}",
        );

        // ★ WITNESS 2 — and nothing was written for it.
        let dir = crate::logic::writer::lang_generated_dir("RedGateOne");
        assert!(
            !dir.exists(),
            "★ R2: `language!` must not spill files for a grammar it refused; found {}",
            dir.display(),
        );
    }

    /// ★ #141 change 2/5 — EVERY violation is reported, not the first.
    ///
    /// MUTATION: three unrouted `Ident` params instead of one. `abort!` diverged,
    /// so the pre-#141 boundary could deliver exactly one diagnostic per build no
    /// matter how many faults a grammar carried.
    #[test]
    fn every_violation_reaches_the_user_in_one_build() {
        let rendered = expand_language(unrouted_ident_source("RedGateThree", 3)).to_string();
        assert_eq!(
            rendered.matches("compile_error").count(),
            3,
            "one diagnostic per violation: {rendered}",
        );
        for label in ["Unrouted0", "Unrouted1", "Unrouted2"] {
            assert!(rendered.contains(label), "{label} must be reported too: {rendered}");
        }
    }

    /// ★ THE ANTI-VACUITY CONTROL for both gate cells above: the same fixture
    /// SHAPE, with zero offending rules, must not be refused by the gate.
    ///
    /// It must not discriminate — it passes before the change and after it. A gate
    /// that refused every grammar, or a boundary that returned `compile_error!`
    /// unconditionally, would satisfy every assertion above and fail here.
    ///
    /// ⚠ It asserts on the GATE rather than on a full expansion deliberately: a
    /// successful `expand_language` writes six files into `target/generated/` and
    /// takes seconds, and this cell's question — "is the clean grammar refused?" —
    /// is answered entirely by the gate.
    #[test]
    fn the_clean_twin_of_the_gate_fixture_is_not_refused() {
        let def: mettail_ast::language::LanguageDef =
            syn::parse2(unrouted_ident_source("RedGateClean", 0))
                .expect("the zero-violation fixture must parse");
        assert!(
            validate_language(&def).is_ok(),
            "the control grammar must be valid, or the cells above could be \
             refusing it for an unrelated reason",
        );
        assert!(
            gen::runtime::wpda_codegen::ident_capture_routing::enforce(&def).is_none(),
            "★ the gate must ADMIT the same fixture with no `Ident` param — \
             otherwise the refusals above prove only that the gate is indiscriminate",
        );
    }

    /// A grammar `syn` cannot parse returns `compile_error!` too, rather than
    /// reaching any of the paths above with a half-built `LanguageDef`.
    #[test]
    fn an_unparseable_body_returns_a_compile_error() {
        let rendered = expand_language(quote! { this is not a language }).to_string();
        assert!(
            rendered.contains("compile_error"),
            "a parse failure must still be a returned diagnostic: {rendered}",
        );
    }
}
