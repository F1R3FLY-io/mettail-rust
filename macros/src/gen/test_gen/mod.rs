//! Test file generation for `language!` specifications.
//!
//! Every section is written to `target/generated/<lang>/tests_<section>.rs` and reached
//! from a hand-written host binary through the `<lang>_generated_tests!` wrapper. Nothing
//! this module writes lives outside `target/` — see [`write_test_file`] for why that is
//! the whole point, and `macros/tests/generated_output_locality.rs` for the standing
//! proof. Generated tests cover:
//!
//! 1. **Unit tests** — one per constructor (roundtrip with concrete values)
//! 2. **Equation tests** — one per equation (symmetry via Ascent)
//! 3. **Rewrite tests** — one per rewrite rule (fires + result matches)
//! 4. **Property tests** — proptest per category (roundtrip, display idempotence, etc.)
//! 5. **Analytical tests** -- confluence, termination
//! 6. **User tests** — from `tests { }` block
//! 7. **Program tests** — application-level from `program { }` blocks
//! 8. **Dead-rule tests** — `#[ignore]` annotated

pub mod automaton_walk;
pub mod equation_tests;
pub mod rewrite_tests;
pub mod strategies;
pub mod unit_tests;

pub mod analytical_tests;
pub mod program_tests;
pub mod user_tests;

pub mod simulation_binary;
pub mod simulation_tests;

// ─── W7 Stage 9 (plan v5.1) ─────────────────────────────────────────────────
// Test_gen modules covering ambiguity-prone WPDS walker paths. Each
// emits baseline tests per language and is wired into the analytical split
// test binary below.

pub mod ambiguity_exposure;
pub mod binder_shadowing;
pub mod cross_cat_ambiguity;
pub mod pratt_bp_boundaries;
// CASE-2 Stage 3 (2026-07-15): recovery_corruption test generator retired.
// It emitted 10 per-language tests that drove the WpdaWalker event harness
// (`process_event` / `WpdaEvent`) — an API deleted in CASE-2 Stage 4 — rather
// than parsing anything. They have no pure-engine equivalent (the pure engine
// `step_canonical_pure` is a whole-run drain, not event-driven). Parser-level
// error recovery stays covered by `recovery_integration_tests` and the pure
// recovery suites. Module file `recovery_corruption.rs` was deleted.
// Stage 10.1 (2026-05-04): parity test generator deleted.
// Pre-Stage-10b parity tests compared `Cat::parse(input)` (trampoline) vs
// `parse_<Cat>_via_wpda(...)` (WPDS facade); both routes are now Walker-driven
// after Stage 10b's parse_preserving_vars rewrite. Tests became tautological.

use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The `options { hosted_in: "tests/definitions/<lang>.rs" }` declaration, if present.
///
/// `Some(path)` means the `language!` is **test-hosted**: its definition lives in
/// `languages/tests/definitions/`, not in the `languages` library, so nothing may
/// reference it as `mettail_languages::<lang>`. `None` means library-hosted — the
/// historical case, whose emission is bit-for-bit unchanged.
///
/// The path is relative to the `languages` package root. See the `hosted_in`
/// documentation in `ast/src/language/parse.rs` for the full contract.
pub fn hosted_in(language: &LanguageDef) -> Option<String> {
    language.options.get("hosted_in").and_then(|v| match v {
        mettail_ast::language::AttributeValue::Str(s) => Some(s.clone()),
        _ => None,
    })
}

/// The directory that holds proptest counterexample corpora, resolved from the manifest.
///
/// This is the single path the `language!` expansion resolves OUTSIDE `target/`, and the
/// only one it is allowed to: a corpus is an INPUT to the generated property tests, not a
/// generated source. `[package.metadata.mettail] proptest_corpus_dir` is where it is
/// declared; see `ast::manifest`.
fn proptest_corpus_dir() -> Result<PathBuf, String> {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let workspace_root = mettail_ast::manifest::find_workspace_root(Path::new(&manifest_dir))
        .ok_or_else(|| {
            format!("no `[workspace]` manifest above {manifest_dir}; cannot locate the corpus")
        })?;
    mettail_ast::manifest::proptest_corpus_dir(&workspace_root)
}

/// The `#![proptest_config(…)]` expression for a generated `proptest!` block.
///
/// # Why this is not just `ProptestConfig::with_cases(n)`
///
/// proptest's default [`FileFailurePersistence::SourceParallel`] derives the
/// counterexample-corpus path from `file!()` at the `proptest!` invocation. Every
/// generated prop section is now `include!`d from `target/generated/{lang}/tests_prop.rs`,
/// and `file!()` reports the INCLUDED file — so the default would put each corpus inside
/// `target/`, where `cargo clean` erases it. Nothing would fail; the seeds would just
/// quietly stop being replayed and coverage would evaporate silently.
///
/// Pinning [`FileFailurePersistence::Direct`] at a path under the manifest-declared
/// `proptest_corpus_dir` keeps every corpus outside `target/` and therefore durable
/// across cleans. This is deliberately the SAME rule for every language: before S4 it
/// applied only to test-hosted languages, because library-hosted sections were written
/// into `languages/tests/` and `file!()` already resolved there. Now that no generated
/// file lives outside `target/`, the distinction has no referent.
///
/// # An inherited claim that was FALSE, corrected here
///
/// The note this replaces asserted that the pin protected "nine" corpora that were
/// "COMMITTED". Neither half held. `.gitignore` carries a global `*.proptest-regressions`
/// rule, so a file at this path can never be committed, and no such file exists anywhere
/// in the repository — the three real corpora (`macros/`, `prattail/`, `rholang-runtime/`)
/// are `.txt` files under a `proptest-regressions/` DIRECTORY, proptest's default
/// `SourceParallel` layout, which no generated test uses. What the pin actually buys is
/// therefore narrower than was claimed, and still worth having: a corpus that survives
/// `cargo clean` and accumulates seeds within a working tree. Whether these corpora
/// SHOULD be committed — which would require removing the `.gitignore` rule — is a
/// question for whoever owns the test policy, not something to decide by leaving an
/// inaccurate comment in place.
pub fn proptest_config_expr(language: &LanguageDef, cases: u32) -> String {
    let lang_lower = language.name.to_string().to_lowercase();
    let corpus = format!("gen_{}_prop.proptest-regressions", lang_lower);
    match proptest_corpus_dir() {
        Ok(dir) => format!(
            "ProptestConfig {{ failure_persistence: \
             Some(Box::new(proptest::test_runner::FileFailurePersistence::Direct({:?}))), \
             ..ProptestConfig::with_cases({}) }}",
            dir.join(corpus).to_string_lossy().into_owned(),
            cases
        ),
        // ★ #141 G9. Fail LOUD rather than silently degrading to a target/-local
        // corpus — but as a `compile_error!` in the generated test source, which is
        // what "loud" requires: a `panic!` inside a proc macro prints NOTHING under
        // this workspace's cranelift dev backend (#141 RED-0). This function returns
        // the `ProptestConfig` EXPRESSION as text, and `compile_error!(…)` is an
        // expression, so the refusal substitutes for it exactly.
        Err(e) => {
            let message = format!(
                "mettail: cannot resolve the proptest corpus directory for language {}: \
                 {}. The generated proptest suite would otherwise persist its failure \
                 corpus under `target/`, where the next `cargo clean` discards the \
                 shrunken counterexamples it exists to keep.",
                language.name, e,
            );
            format!("compile_error!({message:?})")
        },
    }
}

/// Format generated Rust source before comparing/writing generated files.
///
/// The generated integration tests and simulation binaries are tracked source
/// artifacts, but the macro also refreshes them during language compilation.
/// Formatting the generated text at the write boundary keeps `cargo fmt` and
/// macro regeneration from dirtying the worktree in opposite directions. If
/// `rustfmt` is unavailable or rejects a transient generated fragment, keep the
/// old behavior and write the unformatted text.
fn format_generated_rust_source(content: &str) -> String {
    let mut child = match Command::new("rustfmt")
        .args(["--edition", "2021", "--emit", "stdout"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => return content.to_string(),
    };

    if let Some(mut stdin) = child.stdin.take() {
        if stdin.write_all(content.as_bytes()).is_err() {
            let _ = child.kill();
            let _ = child.wait();
            return content.to_string();
        }
    }

    match child.wait_with_output() {
        Ok(output) if output.status.success() => {
            String::from_utf8(output.stdout).unwrap_or_else(|_| content.to_string())
        },
        _ => content.to_string(),
    }
}

/// Write generated test files for the language, split into multiple
/// test-binary files to bound rustc peak memory per compilation unit.
///
/// # Why split?
///
/// Prior to this split, each language's tests were emitted as a single
/// monolithic `gen_{lang}.rs` (24,000+ lines for Calculator). rustc held
/// the full AST, type info, and codegen IR for that entire file in one
/// process, peaking at 96 GB RSS on a 125 GB machine — unusable on any
/// standard developer laptop.
///
/// Splitting into per-section files gives each a bounded size:
/// cargo auto-discovers `tests/*.rs` as separate integration-test
/// binaries, compiled in parallel with per-process memory proportional
/// to the file. Each binary peaks at O(file size), so a 16 GB laptop
/// can compile them all in parallel without swap thrashing.
///
/// # File map
///
/// Each emitted file is a self-contained test binary with its own
/// imports. Cross-section dependencies are isolated:
/// - `gen_{lang}_unit.rs`        — per-constructor unit tests + language-level smoke + metadata
/// - `gen_{lang}_prop.rs`        — property tests (defines AnyTerm/TapeReader/build_*/arb_*) + simulation tests that use arb_*
/// - `gen_{lang}_rewrite.rs`     — equation + rewrite rule tests
/// - `gen_{lang}_op.rs`          — operational semantics eval tests (all phases, may be further split if still too large)
/// - `gen_{lang}_analytical.rs`  — analytical + user + program tests (small)
///
/// # ONE emission path (S4)
///
/// Every language — library-hosted or test-hosted — has each section spilled, WITHOUT a
/// file header, to `target/generated/<lang>/tests_<section>.rs`, and re-exposed through
/// the opt-in `<lang>_generated_tests!` wrapper that a HAND-WRITTEN host binary invokes.
///
/// There used to be a second path: a library-hosted language had its sections written
/// straight into `languages/tests/gen_<lang>_<section>.rs`, complete with a
/// `use mettail_languages::<lang>::*;` header, as TRACKED source files. That destination
/// was computed from `CARGO_MANIFEST_DIR` regardless of which crate was compiling, so
/// **the workspace could not be built without mutating tracked files** — adding or
/// removing a spec in `languages/src/` rewrote 32 committed files. Removing that path is
/// the whole of S4; `macros/tests/generated_output_locality.rs` is the standing proof that
/// it stays removed.
///
/// The header is what forced the split in the first place: it opened with
/// `use mettail_languages::<lang>::*;`, which does not resolve once a definition leaves
/// the library (E0432). Now no section carries a header at all — the wrapper supplies the
/// imports, because only the invoking host knows the module path its definition lives at.
///
/// # What must NOT be "simplified" away: the per-section BINARY split
///
/// The sections are separate FILES because of a MEASURED incident: the original
/// monolithic `gen_{lang}.rs` (24,000+ lines for Calculator) peaked at **96 GB RSS on a
/// 125 GB machine**, because rustc holds one file's full AST, type info, and codegen IR in
/// a single process. Splitting bounded each binary's memory to O(file size).
///
/// Unifying the two WRITE paths does not touch that, but collapsing the two HOST shapes
/// would have. The wrapper's no-selector arm materializes every section into one binary,
/// which is exactly the shape that blew up; it is safe only for the small suites that use
/// it (the largest test-hosted suite, LedTest, is ~35 KB). Calculator (~344 KB) and
/// Rholang (~392 KB) must stay split, so the wrapper also offers a
/// `section <name>` arm and those languages get one host binary PER SECTION. The memory
/// profile is therefore unchanged by S4: the same sections compile in the same number of
/// processes as before.
///
/// Asking for a section a language did not emit hits a dedicated `compile_error!` arm that
/// names the sections which DO exist — a loud, self-explaining failure, which is what a
/// host that has drifted from its language deserves.
pub fn write_test_file(language: &LanguageDef, pipeline: &PipelineAnalysis) -> TokenStream {
    let lang_name = language.name.to_string();

    // Group H: WFST static verification — emit warnings at codegen time
    verify_display_parseability(language, pipeline);

    // Build every section once; where each one LANDS depends on the host.
    let mut sections: Vec<(&'static str, String)> = Vec::with_capacity(4);
    sections.push(("unit", generate_unit_section(language, pipeline)));
    sections.push(("prop", generate_prop_section(language, pipeline)));
    if !language.equations.is_empty() || !language.rewrites.is_empty() {
        sections.push(("rewrite", generate_rewrite_section(language)));
    }
    let analytical_content = generate_analytical_section(language, pipeline);
    if !analytical_content.is_empty() {
        sections.push(("analytical", analytical_content));
    }

    // Stage 10.1 (2026-05-04): parity-section emission deleted alongside the `parity`
    // module. The dual-codegen comparison was tautological after Stage 10b's
    // parse_preserving_vars rewrite (both routes Walker-driven).
    emit_inline_test_suite(&lang_name, &sections)
}

/// Build the opt-in `<lang>_generated_tests!` wrapper.
///
/// Each section is spilled (header-less) to `target/generated/<lang>/` and pulled
/// back in by an absolute-path `include!`, so the wrapper itself stays a handful
/// of tokens. That matters: a test-hosted definition is `#[path]`-included by
/// SEVERAL binaries (its host, other consumers, and its `simulate_*` CLI), and
/// every one of them must parse this expansion even when it never invokes it.
///
/// # Why the suite is opt-in rather than unconditional
///
/// Emitting the `#[test]` functions directly into the expansion would give a copy
/// to every binary that includes the definition. `languages/tests/set_automaton_size_optimal.rs`
/// alone includes 15 test-hosted definitions, so it would acquire ~1050 duplicated
/// tests and the suite total would stop meaning anything. Exactly ONE designated
/// host binary invokes the wrapper; every other consumer simply does not.
///
/// # Two arms: whole suite, or one section
///
/// The no-selector arm materializes EVERY section into the invoking binary. That is the
/// right shape for a small suite and the wrong one for a large suite: a single binary
/// holding all of Calculator's or Rholang's tests is the shape that peaked at 96 GB RSS
/// (see [`write_test_file`]). The `section <name>` arm materializes exactly one, so a
/// large language gets one host binary per section and keeps the bounded-memory profile
/// the split was introduced for.
///
/// The section arms are matched FIRST. `$($definition:tt)*` matches any token sequence
/// including one that starts with `section`, so a catch-all placed first would swallow
/// every selective invocation and silently materialize the whole suite.
///
/// # Invocation
///
// ignore-justification: `#[path = "definitions/acdemo.rs"] mod acdemo;` loads a file off disk relative to the including source file; a doctest has no such file, and the `acdemo_generated_tests!` wrapper it then invokes is emitted BY this crate into that definition, so neither half can exist here.
/// ```ignore
/// // Whole suite, one binary — for a small test-hosted definition:
/// #[path = "definitions/acdemo.rs"]
/// mod acdemo;
/// acdemo::acdemo_generated_tests!(crate::acdemo);
///
/// // One section per binary — for a large library-hosted language:
/// mettail_languages::calculator_generated_tests!(section unit, mettail_languages::calculator);
/// ```
///
/// The definition's module path is a parameter rather than a baked `crate::<lang>`
/// so the wrapper does not silently re-bind `crate::` to whichever crate root it
/// happens to expand in — the trap that already constrains
/// `languages/src/composition/composed_lang.rs`. It is matched as a `tt` sequence,
/// not `$spec:path`: a `path` fragment is an opaque AST node and cannot be used in
/// a `use` declaration, whereas a `tt` sequence interpolates literally.
fn emit_inline_test_suite(lang_name: &str, sections: &[(&'static str, String)]) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let macro_ident = format_ident!("{}_generated_tests", lang_lower);

    let mut section_mods = Vec::with_capacity(sections.len());
    let mut section_arms = Vec::with_capacity(sections.len());
    for (section, content) in sections {
        let formatted = format_generated_rust_source(content);
        let path = match crate::logic::writer::write_lang_module(
            lang_name,
            &format!("tests_{}", section),
            &formatted,
        ) {
            Ok(path) => path,
            Err(e) => {
                eprintln!(
                    "Warning: Failed to spill test section for {} ({}): {}",
                    lang_name, section, e
                );
                continue;
            },
        };
        let include = crate::logic::writer::include_stmt(&path);
        let mod_ident = format_ident!("gen_{}_{}", lang_lower, section);
        let section_ident = format_ident!("{}", section);
        let one_section = quote! {
            #[allow(unused_imports, dead_code)]
            mod #mod_ident {
                use $($definition)*::*;
                use mettail_runtime::BehavioralPred;
                use mettail_runtime::Language;
                #include
            }
        };
        section_arms.push(quote! {
            (section #section_ident, $($definition:tt)*) => { #one_section };
        });
        section_mods.push(one_section);
    }

    let section_names = sections
        .iter()
        .map(|(section, _)| *section)
        .collect::<Vec<_>>()
        .join(", ");
    // A `section` selector this language has no arm for must say SO, naming what exists.
    // Without this arm the request would fall through to the catch-all, which would try to
    // read `section <name>` as the definition's module path and report
    // "expected one of `::`, `;`, or `as`" — a hard error, but one that points at Rust
    // syntax instead of at the mistake.
    let unknown_section_message = format!(
        "`{}` has no generated test section by that name. Sections emitted for this \
         language: {}. A host asks for one with \
         `{}_generated_tests!(section <name>, <path to the definition module>);`",
        lang_name, section_names, lang_lower
    );
    let unknown_section_arm = quote! {
        (section $unknown:tt, $($definition:tt)*) => {
            compile_error!(#unknown_section_message);
        };
    };
    let doc = format!(
        "Opt-in generated test suite for the `{}` language definition.\n\n\
         Sections emitted: {}.\n\n\
         Invoke ONCE per section-or-suite, from the crate root of a designated host test \
         binary:\n\
         - whole suite in one binary: `{}_generated_tests!(<path to the definition module>);`\n\
         - one section per binary: `{}_generated_tests!(section unit, <path to the definition module>);`\n\n\
         A large language must use the per-section form: one binary holding every section \
         is the shape that peaked at 96 GB RSS.",
        lang_name, section_names, lang_lower, lang_lower
    );

    quote! {
        #[doc = #doc]
        #[macro_export]
        macro_rules! #macro_ident {
            // Selective arms FIRST: both arms below match these too.
            #(#section_arms)*
            #unknown_section_arm
            ($($definition:tt)*) => {
                #(#section_mods)*
            };
        }
        pub use #macro_ident;
    }
}

/// Emit the standard header shared by every per-section file.
///
/// The header is comments ONLY — no inner attribute, no import. Every section is
/// `include!`d into a `mod` the `<lang>_generated_tests!` wrapper generates, and both
/// would be errors there rather than style warts: an inner attribute is illegal once
/// `include!` has placed content mid-module, and the definition's import can only be
/// supplied by the wrapper, which alone knows the module path it was invoked with.
///
/// Before S4 this took a `hosted` flag and emitted a crate-level `#![allow(…)]` plus
/// `use mettail_languages::<lang>::*;` for library-hosted languages, whose sections were
/// written as standalone test binaries into tracked `languages/tests/` files. Those files
/// are gone; the flag had one reachable value left.
fn emit_test_file_header(
    out: &mut String,
    lang_name: &str,
    lang_name_lower: &str,
    section: &str,
    dead_rules_note: Option<&str>,
) {
    out.push_str(&format!(
        "// AUTO-GENERATED by language! macro for {} ({}) — do not edit\n",
        lang_name, section
    ));
    out.push_str("// Regenerated on each compilation of the language definition.\n");
    out.push_str(&format!(
        "// Included by the `{}_generated_tests!` wrapper; its hosts live under \
         `languages/tests/`.\n\n",
        lang_name_lower
    ));

    if let Some(rules) = dead_rules_note {
        // ★ #112/D4 — the label says WHAT WAS MEASURED, not a verdict.
        //
        // This line used to read `// Dead rules detected by WFST analysis: […]`, over a
        // set that (a) contained Tier-3 `WfstUnreachable` false positives — 143 of them
        // in Rholang, `Proc::POutput` among them — and (b) is not a WFST result at all
        // now that Tier 3 is out: it is Tier 1 (`literal rule in a category with no
        // native_type`) plus Tier 2 (`infix/var rule in a category with no reachable
        // prefix rule`) plus SYM01 (`guard proven UNSAT`). Neither half of the old
        // sentence survived contact with the set it described.
        //
        // A caption that reads as a deadness verdict over a set that is not one is a
        // defect independently of the false positives — a reader who trusts it deletes
        // a live rule — so the caption is fixed even though the false positives are
        // gone. It names the three admission criteria so a reader can check an entry
        // rather than believe it.
        out.push_str(&format!(
            "// Rules with no reachable parse: literal-in-a-category-with-no-native-type \
             (Tier 1), infix/var-in-an-unreachable-category (Tier 2), or a guard proven \
             UNSAT (SYM01). NOT a WFST prefix-dispatch verdict — see \
             `prattail::pipeline::dead_rules::collect_dead_rule_labels_with_ignored`: {}\n\n",
            rules
        ));
    }
}

/// Generate the per-constructor unit-test section (smallest; no helpers).
fn generate_unit_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut out = String::with_capacity(16384);
    // 2026-05-14: sort the dead-rules set into a Vec before formatting
    // so generated test files don't churn on each compile due to HashSet
    // iteration order. The set is informational (a comment), so any
    // deterministic ordering is fine; alphabetical reads cleanly.
    let dead_rules_str = if !pipeline.dead_rule_labels.is_empty() {
        let mut sorted: Vec<&String> = pipeline.dead_rule_labels.iter().collect();
        sorted.sort();
        Some(format!("{:?}", sorted))
    } else {
        None
    };
    emit_test_file_header(
        &mut out,
        &lang_name,
        &lang_name_lower,
        "unit",
        dead_rules_str.as_deref(),
    );

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Unit tests (one per constructor)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    // Language struct smoke test
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_language_instantiates() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str(&format!("    assert_eq!(lang.name(), \"{}\");\n", lang_name));
    out.push_str("}\n\n");

    // Metadata non-empty
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_metadata_populated() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str("    let meta = lang.metadata();\n");
    out.push_str(
        "    assert!(!meta.types().is_empty(), \"language should have at least one type\");\n",
    );
    out.push_str(
        "    assert!(!meta.terms().is_empty(), \"language should have at least one term\");\n",
    );
    out.push_str("}\n\n");

    // Per-constructor tests
    out.push_str(&unit_tests::generate_unit_tests(language, pipeline));
    out
}

/// Generate the property-test section (defines AnyTerm/TapeReader/build_*/arb_*
/// helpers and includes simulation tests that call `arb_*`).
fn generate_prop_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let mut out = String::with_capacity(32768);
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "prop", None);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Proptest strategies + property tests (tape-based)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
    out.push_str(&strategies::generate_strategies(language));
    out.push('\n');

    // Simulation tests call `arb_*` strategies — keep them co-located so
    // the strategy-helper functions stay in the same compilation unit.
    out.push_str(&simulation_tests::generate_simulation_tests(language, pipeline));
    out
}

/// Generate the rewrite/equation tests section (no helpers required).
/// ⚠ Takes no [`PipelineAnalysis`]. It used to, for exactly one purpose: handing
/// `dead_rule_labels` to `rewrite_tests` so a "dead" rewrite's generated execution test
/// could be `#[ignore]`d. That oracle was unsound and is gone (#112/D4 — the argument is
/// in `rewrite_tests`'s module header), and the parameter went with it so no future
/// caller can reintroduce the coupling by having it already in scope.
fn generate_rewrite_section(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let mut out = String::with_capacity(8192);
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "rewrite", None);

    if !language.equations.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Equation tests (one per equation)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&equation_tests::generate_equation_tests(language));
    }

    if !language.rewrites.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Rewrite tests (one per rewrite rule)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&rewrite_tests::generate_rewrite_tests(language));
    }

    out
}

/// Generate the analytical/user/program tests section (small).
fn generate_analytical_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();

    let a = analytical_tests::generate_analytical_tests(language, pipeline);
    let u = user_tests::generate_user_tests(language);
    let p = program_tests::generate_program_tests(language);
    let ambiguity = ambiguity_exposure::generate_ambiguity_exposure_section(language).to_string();
    let binder = binder_shadowing::generate_binder_shadowing_section(language).to_string();
    let cross_cat = cross_cat_ambiguity::generate_cross_cat_ambiguity_section(language).to_string();
    let pratt_bp = pratt_bp_boundaries::generate_pratt_bp_boundaries_section(language).to_string();

    if a.trim().is_empty()
        && u.trim().is_empty()
        && p.trim().is_empty()
        && ambiguity.trim().is_empty()
        && binder.trim().is_empty()
        && cross_cat.trim().is_empty()
        && pratt_bp.trim().is_empty()
    {
        return String::new();
    }

    let mut out = String::with_capacity(
        a.len()
            + u.len()
            + p.len()
            + ambiguity.len()
            + binder.len()
            + cross_cat.len()
            + pratt_bp.len()
            + 1024,
    );
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "analytical", None);
    push_analytical_subsection(&mut out, "__mettail_analytical", &a);
    push_analytical_subsection(&mut out, "__mettail_user_tests", &u);
    push_analytical_subsection(&mut out, "__mettail_program_tests", &p);
    push_analytical_subsection(&mut out, "__mettail_ambiguity_exposure", &ambiguity);
    push_analytical_subsection(&mut out, "__mettail_binder_shadowing", &binder);
    push_analytical_subsection(&mut out, "__mettail_cross_cat_ambiguity", &cross_cat);
    push_analytical_subsection(&mut out, "__mettail_pratt_bp_boundaries", &pratt_bp);
    out
}

fn push_analytical_subsection(out: &mut String, module_name: &str, content: &str) {
    if content.trim().is_empty() {
        return;
    }
    out.push_str("mod ");
    out.push_str(module_name);
    out.push_str(" {\n");
    out.push_str("use super::*;\n");
    out.push_str(content);
    out.push_str("\n}\n\n");
}

/// Spill the per-language simulation CLI body and return its `<lang>_simulation_main!`
/// wrapper, or nothing when `options { emit_simulator: false }`.
///
/// The returned tokens MUST be spliced into the expansion: the wrapper is the only way a
/// hand-written `languages/src/bin/simulate_<lang>.rs` host can reach the generated body.
/// See [`simulation_binary::write_simulation_binary`].
pub fn write_simulation_binary_if_enabled(language: &LanguageDef) -> TokenStream {
    let emit = language
        .options
        .get("emit_simulator")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    match emit {
        true => simulation_binary::write_simulation_binary(language),
        false => TokenStream::new(),
    }
}

// The old monolithic `generate_test_file` has been replaced by per-section
// `generate_*_section` functions above. See `write_test_file` for the new
// split-file emission orchestration.

// Note: The old inline `generate_analytical_tests()` function has been replaced
// by the `analytical_tests` module. The new module generates tests without any
// feature gates -- the testkit always links against prattail.

/// Group H: WFST static verification of Display parseability.
///
/// Checks that every constructor's label is known to the pipeline analysis.
/// If a constructor is in `dead_rule_labels`, warns that its Display output
/// may not be parseable. Called at codegen time (not at test time).
fn verify_display_parseability(language: &LanguageDef, pipeline: &PipelineAnalysis) {
    let lang_name = language.name.to_string();

    for rule in &language.terms {
        let label = rule.label.to_string();
        if pipeline.dead_rule_labels.contains(&label) {
            eprintln!(
                "  ({}) WFST warning: constructor {} is a dead rule — \
                 its Display output may not be parseable",
                lang_name, label
            );
        }
    }

    // Check auto-generated variants against dead rules
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        if crate::gen::category_emits_implicit_var(&lang_type.name, language) {
            let var_label = crate::gen::generate_var_label(&lang_type.name).to_string();
            if pipeline.dead_rule_labels.contains(&var_label) {
                eprintln!(
                    "  ({}) WFST warning: auto-generated {} variable rule is a dead rule",
                    lang_name, cat
                );
            }
        }
        if let Some(native_type) = &lang_type.native_type {
            let lit_label = crate::gen::generate_literal_label(native_type).to_string();
            if pipeline.dead_rule_labels.contains(&lit_label) {
                eprintln!(
                    "  ({}) WFST warning: auto-generated {} literal rule is a dead rule",
                    lang_name, cat
                );
            }
        }
    }

    // Check for unreachable categories
    for cat in &pipeline.unreachable_categories {
        eprintln!(
            "  ({}) WFST warning: category {} is fully unreachable — all its rules are dead",
            lang_name, cat
        );
    }
}
