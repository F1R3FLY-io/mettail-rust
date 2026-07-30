//! Tape-based proptest strategy generation for `language!` categories.
//!
//! Instead of using `prop_recursive` (which creates recursive strategy call
//! chains that overflow the stack on deeply nested terms), this module
//! generates a **tape-based iterative term builder**.
//!
//! ## Design
//!
//! Proptest generates a flat `Vec<u8>` "instruction tape". An iterative
//! work-stack interprets it to build a term:
//!
//! ```text
//! fn arb_int(max_depth: u32) -> BoxedStrategy<Int> {
//!     proptest::collection::vec(any::<u8>(), 1..max_tape_size(max_depth))
//!         .prop_map(move |tape| build_int_from_tape(&tape, max_depth))
//!         .boxed()
//! }
//! ```
//!
//! The `build_int_from_tape` function uses a work-stack:
//! - Start with a `BuildInt { depth: max_depth }` task
//! - Pop a task, consume a byte from the tape to choose a constructor
//! - If depth > 0: push child tasks for the constructor's fields
//! - If depth == 0: choose a leaf constructor (literal, nullary)
//! - Store results in a `Vec<Option<AnyTerm>>` indexed by slot IDs
//!
//! Proptest shrinking produces shorter tapes which produce simpler terms.
//!
//! Cross-category references (e.g., an `Int` field inside a `Bool` variant)
//! push a `Build{OtherCat}` task onto the same work-stack — no recursive
//! function calls.

use crate::gen::native::native_type_to_string;
use crate::gen::term_ops::subst::{rule_to_variant_kind, FieldInfo, VariantKind};
use crate::gen::{generate_literal_label, generate_var_label};
use mettail_ast::language::LanguageDef;

use proc_macro2::TokenStream;
use quote::quote;

/// The `CollectionType` a collection field must carry, or the GENERATED-SOURCE
/// TEXT that refuses.
///
/// # Why the refusal is text rather than a `TokenStream`
///
/// ★ #141 G4. Four sites in this module read `field.coll_type` on a field that
/// `field.is_collection` already says is a collection, and all four ended in
/// `.unwrap_or_else(|| panic!(…))`. Under this workspace's cranelift dev backend
/// a `panic!` inside a proc macro prints NOTHING — rustc dies with
/// `fatal runtime error: Rust cannot catch foreign exceptions` and the payload
/// never appears (#141 RED-0, 2026-07-29) — so all four messages were unreadable.
///
/// This module does not build a `TokenStream`; it builds a `String` of Rust
/// SOURCE which `test_gen` writes to `languages/tests/gen_<lang>_*.rs` and
/// `rustc` then compiles. The refusal therefore travels as a `compile_error!`
/// LINE in that source. It is still a token by the time it matters — rustc
/// expands and reports it, naming the file and line of the generated builder —
/// and unlike a `panic!` it cannot be swallowed by the backend. What it cannot
/// carry is a span into the `language!` invocation, so the message names the
/// category and the rule explicitly instead of pointing at them.
///
/// The caller pushes the returned line and substitutes a placeholder expression
/// for the field, because `compile_error!` fires on expansion regardless of what
/// the surrounding code does with the slot.
fn coll_type_or_refusal<'a>(
    field: &'a FieldInfo,
    rule_label: &str,
) -> Result<&'a mettail_ast::types::CollectionType, String> {
    field.coll_type.as_ref().ok_or_else(|| {
        format!(
            "            compile_error!(\"mettail: the collection field of category \
             `{category}` on rule `{rule_label}` carries no `coll_type`, so the tape \
             builder cannot know which container to build. Every collection field is \
             supposed to carry one by construction (`is_collection` and `coll_type` are \
             set together when the field is synthesised), so this is a MACRO BUG rather \
             than a grammar bug — please report it.\");\n",
            category = field.category,
        )
    })
}

/// Check if a category has explicit binder rules (single or multi-binder).
///
/// Categories with binders produce FreeVar-containing terms where identity
/// may differ after a parse-display roundtrip. This affects whether we can
/// use structural PartialEq or must fall back to display-string comparison.
fn category_has_binders(category: &syn::Ident, language: &LanguageDef) -> bool {
    // Check grammar rules for binder patterns
    for rule in language.terms.iter().filter(|r| r.category == *category) {
        if !rule.bindings.is_empty() {
            return true;
        }
        // Also check term_context for binder params (Abstraction/MultiBinderAbstraction)
        if let Some(ctx) = &rule.term_context {
            use mettail_ast::grammar::TermParam;
            for param in ctx {
                if matches!(
                    param,
                    TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. }
                ) {
                    return true;
                }
            }
        }
    }
    // Also, every category has auto-generated Lam/MLam binders,
    // but those are internal — check if the category has rules that
    // EXPLICITLY bind variables (user-defined binders).
    false
}

/// Generate proptest strategy functions for all categories as source code string.
///
/// The returned string is inserted directly into the generated test file,
/// which already has `use mettail_languages::{lang}::*;` and
/// `use mettail_runtime::Language;` imports.
pub fn generate_strategies(language: &LanguageDef) -> String {
    let mut out = String::with_capacity(16384);

    // Imports needed by the generated strategies
    out.push_str("use proptest::prelude::*;\n");
    out.push_str("use proptest::strategy::BoxedStrategy;\n\n");

    // Generate the AnyTerm enum (heterogeneous term wrapper)
    generate_any_term_enum(language, &mut out);

    // Generate the BuildTask enum
    generate_build_task_enum(language, &mut out);

    // Generate the tape helper
    generate_tape_reader(&mut out);

    // Generate build_from_tape function per category
    for lang_type in &language.types {
        generate_build_from_tape(&lang_type.name, language, &mut out);
    }

    // Generate arb_ strategy functions per category
    for lang_type in &language.types {
        generate_arb_strategy(&lang_type.name, language, &mut out);
    }

    // Generate proptest blocks
    generate_proptest_blocks(language, &mut out);

    out
}

/// Generate the `AnyTerm` enum that wraps all category types.
fn generate_any_term_enum(language: &LanguageDef, out: &mut String) {
    out.push_str("/// Heterogeneous term wrapper for the tape-based builder.\n");
    out.push_str("#[allow(dead_code)]\n");
    out.push_str("#[derive(Clone)]\n");
    out.push_str("enum AnyTerm {\n");
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        out.push_str(&format!("    Wrap{}({}),\n", cat, cat));
    }
    out.push_str("}\n\n");

    // Unwrap helpers
    let multi_category = language.types.len() > 1;
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();
        // The `_ => panic!(…)` catch-all is reachable only when `AnyTerm` has >1 variant; for a
        // single-category language the sole `Wrap<Cat>(v)` arm is exhaustive, so the wildcard would
        // be an unreachable pattern. Emit it only for multi-category languages.
        let wrong_variant_arm = if multi_category {
            format!("\n            _ => panic!(\"AnyTerm::unwrap_{}: wrong variant\"),", cat_lower)
        } else {
            String::new()
        };
        out.push_str(&format!(
            "impl AnyTerm {{\n    #[allow(dead_code)]\n    fn unwrap_{}(self) -> {} {{\n        match self {{\n            AnyTerm::Wrap{}(v) => v,{}\n        }}\n    }}\n}}\n\n",
            cat_lower, cat, cat, wrong_variant_arm
        ));
    }
}

/// Generate the `BuildTask` enum with one variant per category.
fn generate_build_task_enum(language: &LanguageDef, out: &mut String) {
    out.push_str("/// Work item for the tape-based iterative term builder.\n");
    out.push_str("#[allow(dead_code)]\n");
    out.push_str("enum BuildTask {\n");
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        out.push_str(&format!(
            "    /// Build a {} term at the given depth, storing result in the given slot.\n",
            cat
        ));
        out.push_str(&format!("    Build{} {{ depth: u32, slot: usize }},\n", cat));
    }
    out.push_str("}\n\n");
}

/// Generate the TapeReader helper struct.
fn generate_tape_reader(out: &mut String) {
    out.push_str(
        r#"/// Helper to consume bytes from the tape.
#[allow(dead_code)]
struct TapeReader<'a> {
    tape: &'a [u8],
    pos: usize,
}

#[allow(dead_code)]
impl<'a> TapeReader<'a> {
    fn new(tape: &'a [u8]) -> Self {
        TapeReader { tape, pos: 0 }
    }

    /// Read the next byte. On exhaustion return 0 — do NOT wrap. Byte 0 maps
    /// to constructor choice `0 % N == 0`, which is ALWAYS a leaf: every
    /// `build_*_from_tape` match emits its leaf arms before its recursive arms
    /// (see `classify_variants`), so choice 0 selects `leaves[0]` and the
    /// recursion bottoms out to the simplest term — the documented intent
    /// "shorter tapes = simpler terms". The old `pos % len` wrap RE-READ the
    /// same recursive-constructor byte at every level, so a 1-byte tape
    /// `[0x38]` built a COMPLETE binary tree down to max_depth (0x38 ->
    /// `MulBigRat` at all internal nodes -> `error*error*...`), which drove
    /// BigRat::parse into the exponential cross-category axis (~9s).
    fn next_byte(&mut self) -> u8 {
        if self.pos >= self.tape.len() {
            return 0;
        }
        let b = self.tape[self.pos];
        self.pos += 1;
        b
    }

    /// Read a u32 from 4 bytes (little-endian); reads 0 past end of tape.
    fn next_u32(&mut self) -> u32 {
        let b0 = self.next_byte() as u32;
        let b1 = self.next_byte() as u32;
        let b2 = self.next_byte() as u32;
        let b3 = self.next_byte() as u32;
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }

    /// Read an i32 from tape bytes.
    ///
    /// Returns the full i32 range. Overflow in `![a + b]` native eval paths is
    /// handled by the `SafeArith` trait and the `rust_code_rewrite` pass in the
    /// `language!` macro: arithmetic operators are rewritten to `safe_add`,
    /// `safe_mul`, etc., which return `Option<T>` on overflow rather than
    /// panicking. This removes the need for a restricted range here.
    fn next_i32(&mut self) -> i32 {
        self.next_u32() as i32
    }

    /// Read an i64 from tape bytes.
    fn next_i64(&mut self) -> i64 {
        let lo = self.next_u32() as i64;
        let hi = self.next_u32() as i64;
        lo | (hi << 32)
    }

    /// Read an f64 from tape bytes.
    fn next_f64(&mut self) -> f64 {
        let bits = self.next_i64() as u64;
        let val = f64::from_bits(bits);
        // Avoid NaN/Inf which cause issues with Eq/Ord
        if val.is_nan() || val.is_infinite() { 0.0 } else { val }
    }

    /// Read an f32 from tape bytes.
    fn next_f32(&mut self) -> f32 {
        let bits = self.next_u32();
        let val = f32::from_bits(bits);
        if val.is_nan() || val.is_infinite() { 0.0f32 } else { val }
    }

    /// Read a bool from tape.
    fn next_bool(&mut self) -> bool {
        self.next_byte() & 1 == 1
    }

    /// Read a short string from tape.
    fn next_string(&mut self) -> String {
        let len = (self.next_byte() % 8) as usize;
        (0..len)
            .map(|_| {
                let b = self.next_byte();
                // Map to printable ASCII range 'a'-'z'
                (b'a' + (b % 26)) as char
            })
            .collect()
    }
}

"#,
    );
}

/// Classify variants of a category into leaf vs recursive for the tape builder.
struct VariantClassification {
    /// (label_str, code to build the term from tape)
    leaves: Vec<(String, String)>,
    /// (label_str, code to build the term + push children)
    recursive: Vec<(String, String)>,
}

/// Classify all variants of a category.
/// Collect only spec-defined variants for a category — excludes auto-generated
/// Lam/MLam/Apply/MApply constructors that produce unparseable Display output.
/// Includes auto-Var and auto-Literal since those ARE parseable.
///
/// Phase 3A (predicated types): rules with `?guard:Guard` slots are NOW
/// included. Guard slots are synthesized as `BehavioralPred::Top` (trivially
/// open) during tape-based building, enabling structural coverage of guarded
/// constructors without requiring a random predicate synthesizer.  Guard
/// evaluation semantics remain testable via hand-written integration tests.
fn collect_spec_only_variants(category: &syn::Ident, language: &LanguageDef) -> Vec<VariantKind> {
    let mut variants = Vec::new();

    // 1. Spec-defined rules from language.terms (includes guarded constructors)
    for rule in language.terms.iter().filter(|r| r.category == *category) {
        // Skip internal-only rules whose surface begins with a `__`-prefixed
        // terminal (CommWhere `__comm_where`, GuardThen `__guard_then`): they
        // have no user-facing surface, so generating them as random terms yields
        // Display strings the parser cannot re-parse. They still PARSE (for
        // internal AST round-tripping) — just not generated.
        //
        // Rholang's `PParInternal` (`__ppar`) was a third such rule until
        // 2026-07-29, when it was deleted as a vestige of the pre-braced `PPar`
        // grammar. It is worth naming here because it was also the one rule that
        // FALSIFIED the "they still PARSE" clause: measured before deletion,
        // `__ppar(Nil, Nil)` did not parse at all. The clause holds for the two
        // remaining rules; do not extend it to a new `__` rule without measuring.
        // ★ #150 — THE SHARED CLASSIFIER, called on the HOT PATH. The census
        // (`gen::generatability::tests`) calls the same function, so "what the tape builder
        // skips" and "what the ledger measures" are one computation.
        if crate::gen::generatability::tape_rule_gap(rule).is_some() {
            continue;
        }
        variants.push(rule_to_variant_kind(rule, language));
    }

    // 2. Auto-generated Var — emitted ONLY for categories that get a
    //    parseable synthetic Var rule per `synthetic.rs:231-249`. The
    //    spec-derived predicate `category_emits_parseable_auto_var`
    //    mirrors that logic exactly: category in `language.types`,
    //    `native_type.is_none()`, no explicit Var rule. Categories with
    //    `native_type` (e.g., `![i32] as Int`) do NOT get a parseable
    //    auto-Var — emitting one here produces Display output (`"z"`)
    //    that the parser cannot re-parse.
    if crate::gen::category_emits_parseable_auto_var(category, language) {
        let var_label = generate_var_label(category);
        variants.push(VariantKind::Var { label: var_label });
    }

    // 3. Auto-generated Literal — emitted ONLY when the spec admits a
    //    parseable auto-Literal. Symmetric to auto-Var, gated by the
    //    spec-derived predicate.
    if crate::gen::category_emits_parseable_auto_literal(category, language) {
        let lit_label = language
            .types
            .iter()
            .find(|t| t.name == *category)
            .and_then(|t| t.native_type.as_ref())
            .map(|nt| generate_literal_label(nt))
            .expect("native type should exist");
        variants.push(VariantKind::Literal { label: lit_label });
    }

    // DO NOT include auto-generated Lam/MLam/Apply/MApply — they produce
    // Display output (^v.{...}, $$cat(...)) that the parser cannot re-parse.

    variants
}


/// (A4) How many builtin `m:Ident` params the rule named `(cat, label)` declares.
///
/// The tape builder reads `FieldInfo::opaque_leaf`, which cannot tell an `m:Ident` param from
/// a `v@Tok` capture of a declared kind — and the two are governed by different lexer
/// patterns. This reaches back to the RULE for that distinction; see
/// [`crate::gen::term_gen::ident_param_count`] for why inferring it from the leaf kind is
/// unsound. Returns 0 when no such rule exists (a synthesized variant has no term context).
fn ident_param_count_for(cat: &str, label: &str, language: &LanguageDef) -> usize {
    language
        .terms
        .iter()
        .find(|r| r.category == *cat && r.label == *label)
        .map_or(0, crate::gen::term_gen::ident_param_count)
}

fn classify_variants(category: &syn::Ident, language: &LanguageDef) -> VariantClassification {
    let cat = category.to_string();
    let variants = collect_spec_only_variants(category, language);

    let mut leaves = Vec::new();
    let mut recursive = Vec::new();

    for variant in &variants {
        // ★★ #150 — THE SEVEN `continue`s THAT USED TO BE SCATTERED THROUGH THE ARMS BELOW ARE
        // NOW ONE CALL. `tape_variant_gap` is the only implementation of these tests, and the
        // ledger census calls the SAME function — so "what the tape builder skips" and "what the
        // ledger measures" cannot diverge, because there is no second implementation to diverge
        // from. Each refusal now carries a named `GeneratorGap` instead of falling off the loop.
        //
        // ⚠ The all-token-text LEAF case is deliberately NOT a gap: `tape_variant_gap` answers
        // `None` for it so it falls through to its own arm below, which pushes a leaf. Its
        // condition implies the `NoRecursiveField` gap's, so the order inside that function is
        // load-bearing — see its doc comment.
        if crate::gen::generatability::tape_variant_gap(variant, &cat, language).is_some() {
            continue;
        }
        match variant {
            // ★ #141 G5 — generated-source EXPRESSION position: the leaf's build
            // code is a Rust expression written as text, and `compile_error!(…)`
            // is an expression. Emitting the leaf with a refusing body keeps the
            // tape builder's arm count intact and makes the diagnostic what
            // `rustc` reports for it. See `VariantKind::Refused`.
            VariantKind::Refused { label, message } => {
                leaves.push((label.to_string(), format!("compile_error!({message:?})")));
            },
            VariantKind::Nullary { label } => {
                let label_str = label.to_string();
                leaves.push((
                    label_str.clone(),
                    format!("AnyTerm::Wrap{}({}::{})", cat, cat, label_str),
                ));
            },
            // Stage 0 identity — STAYS (see `unit_tests.rs`: test_gen has its
            // own collector, so this arm is unreachable for `CollectionLiteral`).
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                let label_str = label.to_string();
                // F1: spec-derived — `category_emits_parseable_auto_literal`
                // gates this site, so `native_type` MUST be present.
                // Replace `unwrap_or_else(|| "i32")` with `expect`.
                let native_type_str = language
                    .types
                    .iter()
                    .find(|t| t.name == *category)
                    .and_then(|t| t.native_type.as_ref())
                    .map(|t| native_type_to_string(t))
                    .expect("VariantKind::Literal requires the category to have a native_type per the spec");

                let build_code =
                    generate_literal_build_code(&cat, &label_str, &native_type_str, language);
                leaves.push((label_str, build_code));
            },
            VariantKind::Var { label } => {
                // F2: spec-derived var name. Replaces hard-coded
                // `["a","b","c","x","y","z"]` array with a single
                // identifier admitted by the language's effective
                // Ident pattern. The tape byte is consumed (preserving
                // deterministic replay) but the chosen name is
                // spec-determined.
                let label_str = label.to_string();
                let var_name = crate::gen::spec_admitted_var_name(language);
                let code = format!(
                    r#"{{
    let _ = reader.next_byte(); // consume tape byte for replay determinism
    AnyTerm::Wrap{cat}({cat}::{label}(
        mettail_runtime::OrdVar(
            mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var("{var_name}")
            )
        )
    ))
}}"#,
                    cat = cat,
                    label = label_str,
                    var_name = var_name,
                );
                leaves.push((label_str, code));
            },
            VariantKind::Regular { label, fields } => {
                // Check if any field references a known category (recursive)
                let has_recursive_field = fields
                    .iter()
                    .any(|f| language.types.iter().any(|t| t.name == f.category));



                // (A4) A variant whose fields are ALL token-text leaves (`m:Ident`, `v@Tok`)
                // is a LEAF, not a drop. It has no category child to recurse into, so
                // `has_recursive_field` is false and it used to `continue` — vanishing from
                // the generated property suite with no diagnostic, exactly as it vanished
                // from `term_gen`. Its text comes from the same spec-derived, pattern-
                // validated pool the other generators use.
                if !fields.is_empty()
                    && !has_recursive_field
                    && fields.iter().all(|f| {
                        f.opaque_leaf
                            == Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText)
                    })
                    // ★ POSITIVE evidence that these text fields are `m:Ident` PARAMS, not
                    // `v@Tok` captures of a DECLARED kind. `ident_samples` walks the
                    // language's effective `Ident` pattern, which governs the former and not
                    // the latter (`L9ModalToy`'s `Word = "<[a-z]+>"`). A `v@Tok` variant
                    // keeps its previous treatment — dropped here, and served correctly by
                    // `capture_only_construction` in the term generators, which samples each
                    // capture's own declared kind.
                    && ident_param_count_for(&cat, &label.to_string(), language)
                        == fields.len()
                {
                    let label_str = label.to_string();
                    // ★ #141 G4. Generated-source EXPRESSION position: each arg is a
                    // Rust expression written as text, and `compile_error!(…)` is an
                    // expression, so the refusal substitutes for the pool lookup in
                    // every slot. `{:?}` on the message renders it as an escaped Rust
                    // string literal, which the pattern's `Debug` form needs.
                    let args: Vec<String> = match crate::gen::term_gen::ident_samples(language) {
                        Ok(samples) => (0..fields.len())
                            .map(|_| {
                                format!(
                                    "[{}][(reader.next_byte() as usize) % {}].to_string()",
                                    samples
                                        .iter()
                                        .map(|s| format!("{s:?}"))
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                    samples.len(),
                                )
                            })
                            .collect(),
                        Err(message) => (0..fields.len())
                            .map(|_| format!("compile_error!({message:?})"))
                            .collect(),
                    };
                    leaves.push((
                        label_str.clone(),
                        format!(
                            "AnyTerm::Wrap{cat}({cat}::{label}({args}))",
                            cat = cat,
                            label = label_str,
                            args = args.join(", "),
                        ),
                    ));
                    continue;
                }



                let label_str = label.to_string();
                let code = generate_regular_build_code(&cat, &label_str, fields, language);
                recursive.push((label_str, code));
            },
            VariantKind::Collection { label, element_cat, coll_type } => {
                // Collections are recursive (contain elements).
                let label_str = label.to_string();
                let code = generate_collection_build_code(
                    &cat,
                    &label_str,
                    &element_cat.to_string(),
                    coll_type,
                );
                recursive.push((label_str, code));
            },
            VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
                let label_str = label.to_string();
                let code = generate_binder_build_code(
                    &cat,
                    &label_str,
                    pre_scope_fields,
                    &body_cat.to_string(),
                    false,
                    language,
                );
                recursive.push((label_str, code));
            },
            VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
                let label_str = label.to_string();
                let code = generate_binder_build_code(
                    &cat,
                    &label_str,
                    pre_scope_fields,
                    &body_cat.to_string(),
                    true,
                    language,
                );
                recursive.push((label_str, code));
            },
        }
    }

    // Ensure there's at least one leaf. By construction (Sites 1 & 2
    // above), `leaves` was populated only from spec-derived sources:
    // (a) explicit Nullary/Literal/Var rules from `language.terms`, OR
    // (b) auto-Var iff `category_emits_parseable_auto_var` returns true
    //     (which requires the category to be user-defined with no
    //     `native_type` and no explicit Var rule), OR
    // (c) auto-Literal iff `category_emits_parseable_auto_literal`
    //     returns true.
    //
    // If `leaves` is still empty, the spec genuinely admits no
    // parseable leaf for this category — emit a `compile_error!` rather
    // than fabricating an unparseable Var. This honors the directive:
    // "all generation must come directly from the language! spec".
    // Fabricating a Var leaf when the spec doesn't admit one was the
    // root cause of the optsmoke `int_display_parse_roundtrip` /
    // `bool_display_parse_roundtrip` failures (2026-04-29).
    if leaves.is_empty() {
        let cat_name = cat.clone();
        let code = format!(
            r#"compile_error!("category `{cat}` has no spec-defined parseable leaf — \
add a Var rule, a literal rule (via `![T] as {cat}` types{{}} entry), \
or a nullary constructor in the language! spec to enable proptest generation")"#,
            cat = cat_name,
        );
        leaves.push(("__no_parseable_leaf".to_string(), code));
    }

    VariantClassification { leaves, recursive }
}

/// Generate code to build a literal value from tape, projected onto
/// the domain admitted by the language's lexical pattern for the
/// relevant token kind.
///
/// The tape reader's raw domain (`next_i64` full i64; `next_f64` any
/// finite non-NaN) is **unchanged** — projection happens at the call
/// site so the emitted Rust code maps the raw value onto surface-valid
/// literals. The classification decision is made at codegen time by
/// `automaton_walk::classify::classify_token` on the language's
/// effective Integer / Float pattern (user override or default), so
/// the result is grammar-aware:
///
/// - `Integer` canonical (`[0-9]+` default): emit non-negative
///   projection `(v.unsigned_abs() as i64) & i64::MAX`. The full tape
///   domain is still consumed, preserving deterministic replay; only
///   the *sign* is normalised at emission.
/// - `SignedInt` canonical (`-?[0-9]+`, only present via user
///   override): emit the raw `v` — full i64 roundtrips.
/// - `Float` / `SignedFloat`: analogous for `f64`.
/// - `Unclassified`: fall back to the current raw emission; the
///   caller may still hit parse failures, which are now loudly
///   reported by the strengthened roundtrip contract.
fn generate_literal_build_code(
    cat: &str,
    label: &str,
    native_type: &str,
    language: &LanguageDef,
) -> String {
    use crate::gen::test_gen::automaton_walk::classify::{
        classify_token, effective_pattern_for, CanonicalKind,
    };

    match native_type {
        "i32" | "i64" => {
            let pat = effective_pattern_for(language, "Integer");
            match classify_token(&pat) {
                CanonicalKind::SignedInt => {
                    if native_type == "i32" {
                        format!(
                            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_i32()))",
                            cat = cat, label = label,
                        )
                    } else {
                        format!(
                            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_i64()))",
                            cat = cat, label = label,
                        )
                    }
                }
                _ => {
                    // Default + unclassified: project to non-negative.
                    // Surface grammar's Integer pattern `[0-9]+` does
                    // not accept a leading `-`. Displaying a negative
                    // `NumLit` would produce unparseable text.
                    if native_type == "i32" {
                        format!(
                            "AnyTerm::Wrap{cat}({cat}::{label}((reader.next_i32().unsigned_abs() as i32) & i32::MAX))",
                            cat = cat, label = label,
                        )
                    } else {
                        format!(
                            "AnyTerm::Wrap{cat}({cat}::{label}((reader.next_i64().unsigned_abs() as i64) & i64::MAX))",
                            cat = cat, label = label,
                        )
                    }
                }
            }
        }
        "u32" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_u32()))",
            cat = cat,
            label = label,
        ),
        "u64" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_u32() as u64))",
            cat = cat,
            label = label,
        ),
        "f64" => {
            let pat = effective_pattern_for(language, "Float");
            match classify_token(&pat) {
                CanonicalKind::SignedFloat => format!(
                    "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalFloat64::from(reader.next_f64())))",
                    cat = cat, label = label,
                ),
                _ => format!(
                    "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalFloat64::from(reader.next_f64().abs())))",
                    cat = cat, label = label,
                ),
            }
        }
        "f32" => {
            let pat = effective_pattern_for(language, "Float");
            match classify_token(&pat) {
                CanonicalKind::SignedFloat => format!(
                    "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalFloat32::from(reader.next_f32())))",
                    cat = cat, label = label,
                ),
                _ => format!(
                    "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalFloat32::from(reader.next_f32().abs())))",
                    cat = cat, label = label,
                ),
            }
        }
        "bool" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_bool()))",
            cat = cat,
            label = label,
        ),
        "str" | "String" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_string()))",
            cat = cat,
            label = label,
        ),
        // Collection types: generate empty collections rather than broken `as _` casts.
        "Vec" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(Vec::new()))",
            cat = cat,
            label = label,
        ),
        "HashBag" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::HashBag::new()))",
            cat = cat,
            label = label,
        ),
        "HashMapLit" | "HashMap" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::HashMapLit::new()))",
            cat = cat,
            label = label,
        ),
        // Rholang 1.4 (main) collection / wrapper leaves: generate empty/default
        // values rather than the broken `reader.next_i32() as _` fallback (i32 does
        // not cast to these wrapper types). `Set`→`HashSetLit`, `Pathmap`→`PathMapLit`,
        // and the zipper categories carry an `Arc<…ZipperLit>` native type (last path
        // segment `Arc`); all implement `Default`.
        "HashSetLit" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::HashSetLit::new()))",
            cat = cat,
            label = label,
        ),
        "PathMapLit" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::PathMapLit::new()))",
            cat = cat,
            label = label,
        ),
        "Arc" => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(::core::default::Default::default()))",
            cat = cat,
            label = label,
        ),
        // Canonical numeric wrappers: use From<i32> or Default
        nt if nt.ends_with("BigInt") || nt.ends_with("CanonicalBigInt") => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from(reader.next_i32()))))",
            cat = cat,
            label = label,
        ),
        nt if nt.ends_with("BigRat") || nt.ends_with("CanonicalBigRat") => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalBigRat::from(num_rational::Ratio::from_integer(num_bigint::BigInt::from(reader.next_i32())))))",
            cat = cat,
            label = label,
        ),
        nt if nt.ends_with("FixedPoint") || nt.ends_with("CanonicalFixedPoint") => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(mettail_runtime::CanonicalFixedPoint::new(num_bigint::BigInt::from(reader.next_i32()), 0)))",
            cat = cat,
            label = label,
        ),
        _ => format!(
            "AnyTerm::Wrap{cat}({cat}::{label}(reader.next_i32() as _))",
            cat = cat,
            label = label,
        ),
    }
}

/// Generate code for building a Regular variant from the tape.
///
/// Returns a code string that:
/// 1. Allocates child slots
/// 2. Pushes BuildTask for each child (in reverse for correct ordering)
/// 3. After the loop processes children, assembles the constructor
fn generate_regular_build_code(
    cat: &str,
    label: &str,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> String {
    let mut code = String::new();
    code.push_str("{\n");

    // Allocate slots for children
    let num_children = fields.len();
    code.push_str(&format!(
        "    let base_slot = slots.len();\n    slots.extend(std::iter::repeat(None).take({}));\n",
        num_children
    ));

    // Push child tasks in REVERSE order (stack is LIFO)
    for (i, field) in fields.iter().enumerate().rev() {
        let field_cat = field.category.to_string();
        let is_known = language.types.iter().any(|t| t.name == field.category);
        if is_known && !field.is_collection {
            code.push_str(&format!(
                "    stack.push(BuildTask::Build{} {{ depth: child_depth, slot: base_slot + {} }});\n",
                field_cat, i
            ));
        } else if field.is_collection {
            // For collection fields in a Regular variant, we'll handle them
            // inline during assembly.
            let elem_cat = field.category.to_string();
            code.push_str(&format!(
                "    // Collection field {} ({}): handled during assembly\n",
                i, elem_cat
            ));
        }
    }

    // The assembly happens as a deferred step — we record what needs assembly
    code.push_str(&format!(
        "    assembly.push(AssemblyOp::Regular{} {{ label: \"{}\", base_slot, num_fields: {} }});\n",
        cat, label, num_children
    ));
    code.push_str("}\n");

    code
}

/// Generate code for building a Collection variant from the tape.
fn generate_collection_build_code(
    cat: &str,
    label: &str,
    element_cat: &str,
    coll_type: &mettail_ast::types::CollectionType,
) -> String {
    let coll_type_str = match coll_type {
        mettail_ast::types::CollectionType::HashBag
        | mettail_ast::types::CollectionType::HashMap
        | mettail_ast::types::CollectionType::PathMap => "HashBag",
        mettail_ast::types::CollectionType::HashSet => "HashSet",
        mettail_ast::types::CollectionType::Vec => "Vec",
    };

    format!(
        r#"{{
    let num_elems = (reader.next_byte() % 4) as usize; // 0-3 elements
    let base_slot = slots.len();
    slots.extend(std::iter::repeat(None).take(num_elems));
    for i in (0..num_elems).rev() {{
        stack.push(BuildTask::Build{elem_cat} {{ depth: child_depth, slot: base_slot + i }});
    }}
    assembly.push(AssemblyOp::Collection{cat} {{ label: "{label}", base_slot, num_elems, coll_type: "{coll_type}" }});
}}"#,
        elem_cat = element_cat,
        cat = cat,
        label = label,
        coll_type = coll_type_str,
    )
}

/// Generate code for building a Binder or MultiBinder variant from the tape.
fn generate_binder_build_code(
    cat: &str,
    label: &str,
    pre_scope_fields: &[FieldInfo],
    body_cat: &str,
    is_multi: bool,
    language: &LanguageDef,
) -> String {
    let num_pre_scope = pre_scope_fields.len();
    // Total slots: pre_scope fields + 1 body
    let total_children = num_pre_scope + 1;

    let mut code = String::new();
    code.push_str("{\n");
    code.push_str(&format!(
        "    let base_slot = slots.len();\n    slots.extend(std::iter::repeat(None).take({}));\n",
        total_children
    ));

    // Push body task (last slot) first since it's pushed in reverse
    code.push_str(&format!(
        "    stack.push(BuildTask::Build{} {{ depth: child_depth, slot: base_slot + {} }});\n",
        body_cat, num_pre_scope
    ));

    // Push pre-scope fields in reverse
    for (i, field) in pre_scope_fields.iter().enumerate().rev() {
        let field_cat = field.category.to_string();
        let is_known = language.types.iter().any(|t| t.name == field.category);
        if is_known && !field.is_collection {
            code.push_str(&format!(
                "    stack.push(BuildTask::Build{} {{ depth: child_depth, slot: base_slot + {} }});\n",
                field_cat, i
            ));
        }
    }

    let binder_kind = if is_multi { "Multi" } else { "Single" };
    code.push_str(&format!(
        "    assembly.push(AssemblyOp::Binder{cat} {{ label: \"{label}\", base_slot, num_pre_scope: {num_pre_scope}, binder_kind: \"{binder_kind}\" }});\n",
        cat = cat,
        label = label,
        num_pre_scope = num_pre_scope,
        binder_kind = binder_kind,
    ));

    code.push_str("}\n");
    code
}

/// Generate the `build_{cat}_from_tape` function for one category.
///
/// This is the core of the tape-based approach. Instead of the complex
/// generic assembly machinery, we use a simpler direct approach:
/// the tape is consumed left-to-right to build the term recursively
/// but using an explicit stack instead of the call stack.
fn generate_build_from_tape(category: &syn::Ident, language: &LanguageDef, out: &mut String) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();
    let classification = classify_variants(category, language);

    // Use a simpler approach: direct recursive builder with explicit depth
    // tracking but iterative work-stack for the actual construction.
    //
    // The build function reads bytes from the tape to choose constructors,
    // then directly builds the term. This avoids the complex slot/assembly
    // machinery and is clearer.

    out.push_str(&format!("/// Build a `{}` term from an instruction tape.\n", cat));
    out.push_str(&format!(
        "///\n/// Consumes bytes from the tape to choose constructors.\n/// At depth 0, only leaf constructors (nullary, literal, var) are chosen.\n/// At depth > 0, recursive constructors are also available.\n"
    ));
    out.push_str("#[allow(dead_code, unused_variables, clippy::let_and_return)]\n");
    out.push_str(&format!(
        "fn build_{cat_lower}_from_tape(reader: &mut TapeReader<'_>, depth: u32) -> {cat} {{\n",
        cat_lower = cat_lower,
        cat = cat,
    ));

    let num_leaves = classification.leaves.len();
    let num_recursive = classification.recursive.len();
    let total = num_leaves + num_recursive;

    // At depth 0, only choose leaves
    out.push_str("    if depth == 0 {\n");
    if num_leaves == 1 {
        // Only one leaf — use it directly
        let (_, ref code) = classification.leaves[0];
        // Actually, let's keep it simpler: build the term directly
        out.push_str(&format!("        let result = {};\n", code));
        out.push_str(&format!("        return result.unwrap_{}();\n", cat_lower));
    } else {
        out.push_str(&format!(
            "        let choice = (reader.next_byte() as usize) % {};\n",
            num_leaves
        ));
        out.push_str("        let result = match choice {\n");
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            if i == num_leaves - 1 {
                out.push_str(&format!("            _ => {},\n", code));
            } else {
                out.push_str(&format!("            {} => {},\n", i, code));
            }
        }
        out.push_str("        };\n");
        out.push_str(&format!("        return result.unwrap_{}();\n", cat_lower));
    }
    out.push_str("    }\n\n");

    // At depth > 0, can choose leaves or recursive constructors
    if num_recursive == 0 {
        // No recursive constructors — always choose a leaf
        out.push_str("    // No recursive constructors, fall back to leaf\n");
        out.push_str(&format!("    build_{}_from_tape(reader, 0)\n", cat_lower));
    } else {
        // Bias toward recursive constructors at higher depths to ensure interesting terms
        out.push_str(&format!("    let choice = (reader.next_byte() as usize) % {};\n", total));
        out.push_str("    let child_depth = depth - 1;\n");
        out.push_str("    match choice {\n");

        // Leaves first
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            out.push_str(&format!("        {} => {}.unwrap_{}(),\n", i, code, cat_lower));
        }

        // Then recursive constructors
        for (i, (label, _)) in classification.recursive.iter().enumerate() {
            let idx = num_leaves + i;
            let is_last = idx == total - 1;

            let match_prefix = if is_last {
                "        _ =>".to_string()
            } else {
                format!("        {} =>", idx)
            };

            let code = generate_direct_recursive_build(&cat, label, category, language);
            out.push_str(&format!("{} {{\n", match_prefix));
            out.push_str(&code);
            out.push_str("        },\n");
        }

        out.push_str("    }\n");
    }

    out.push_str("}\n\n");
}

/// Generate direct recursive build code for a specific variant.
///
/// This produces code that calls `build_{cat}_from_tape` for each child field,
/// directly constructing the term. The "iteration" comes from the fact that
/// proptest generates the flat tape; the build function simply walks it.
fn generate_direct_recursive_build(
    cat: &str,
    label: &str,
    category: &syn::Ident,
    language: &LanguageDef,
) -> String {
    let variants = collect_spec_only_variants(category, language);

    // Find the variant with this label
    let variant = variants.iter().find(|v| match v {
        VariantKind::Regular { label: l, .. }
        | VariantKind::Collection { label: l, .. }
        | VariantKind::Binder { label: l, .. }
        | VariantKind::MultiBinder { label: l, .. } => l.to_string() == label,
        _ => false,
    });

    let variant = match variant {
        Some(v) => v,
        None => {
            return format!(
                "            // Unknown variant {}\n            build_{}_from_tape(reader, 0)\n",
                label,
                cat.to_lowercase()
            )
        },
    };

    let cat_lower = cat.to_lowercase();

    match variant {
        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();
            let mut code = String::new();

            let mut field_exprs = Vec::new();
            for (i, field) in fields.iter().enumerate() {
                let field_cat = field.category.to_string();
                let field_cat_lower = field_cat.to_lowercase();
                let is_known = language.types.iter().any(|t| t.name == field.category);

                if field.is_optional && field.is_collection {
                    // Phase 4 #3 (2026-05-12): Optional-Collection — visit
                    // both None and Some(empty Container) arms based on
                    // a tape byte. Spec admits both; generator must too.
                    let coll_type = match coll_type_or_refusal(field, &label_str) {
                        Ok(coll_type) => coll_type,
                        Err(refusal) => {
                            code.push_str(&refusal);
                            field_exprs.push("Default::default()".to_string());
                            continue;
                        },
                    };
                    match coll_type {
                        mettail_ast::types::CollectionType::HashBag => {
                            code.push_str(&format!(
                                "            let f{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                                 let num_elems = (reader.next_byte() % 4) as usize;\n\
                                                 let mut bag = mettail_runtime::HashBag::new();\n\
                                                 for _ in 0..num_elems {{ bag.insert(build_{fc}_from_tape(reader, child_depth)); }}\n\
                                                 Some(bag)\n\
                                             }};\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("f{}", i));
                        },
                        // Phase 4 #5b (2026-05-12): Optional-HashMap.
                        mettail_ast::types::CollectionType::HashMap
                        | mettail_ast::types::CollectionType::PathMap => {
                            code.push_str(&format!(
                                "            let f{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                                 let num_elems = (reader.next_byte() % 4) as usize;\n\
                                                 let mut m = mettail_runtime::HashMapLit::default();\n\
                                                 for _ in 0..num_elems {{\n\
                                                     let k = build_{fc}_from_tape(reader, child_depth);\n\
                                                     let v = build_{fc}_from_tape(reader, child_depth);\n\
                                                     m.insert(k, v);\n\
                                                 }}\n\
                                                 Some(m)\n\
                                             }};\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("f{}", i));
                        },
                        mettail_ast::types::CollectionType::HashSet => {
                            code.push_str(&format!(
                                "            let f{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                                 let num_elems = (reader.next_byte() % 4) as usize;\n\
                                                 let mut s = std::collections::HashSet::new();\n\
                                                 for _ in 0..num_elems {{ s.insert(build_{fc}_from_tape(reader, child_depth)); }}\n\
                                                 Some(s)\n\
                                             }};\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("f{}", i));
                        },
                        mettail_ast::types::CollectionType::Vec => {
                            code.push_str(&format!(
                                "            let f{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                                 let num_elems = (reader.next_byte() % 4) as usize;\n\
                                                 let v: Vec<_> = (0..num_elems).map(|_| build_{fc}_from_tape(reader, child_depth)).collect();\n\
                                                 Some(v)\n\
                                             }};\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("f{}", i));
                        },
                    }
                } else if field.is_collection {
                    // F5: spec-derived coll_type — every collection field
                    // MUST carry coll_type per the language! spec; missing is
                    // a synthetic insertion bug, surfaced loudly.
                    let coll_type = match coll_type_or_refusal(field, &label_str) {
                        Ok(coll_type) => coll_type,
                        Err(refusal) => {
                            code.push_str(&refusal);
                            field_exprs.push("Default::default()".to_string());
                            continue;
                        },
                    };
                    match coll_type {
                        mettail_ast::types::CollectionType::HashBag => {
                            code.push_str(&format!(
                                "            let num_elems_{i} = (reader.next_byte() % 4) as usize;\n\
                                             let mut coll_{i} = mettail_runtime::HashBag::new();\n\
                                             for _ in 0..num_elems_{i} {{\n\
                                                 coll_{i}.insert(build_{fc}_from_tape(reader, child_depth));\n\
                                             }}\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("coll_{}", i));
                        },
                        // Phase 4 #5b (2026-05-12): HashMap binder field —
                        // tape-driven construction produces `HashMapLit::default()`,
                        // then inserts pairs (each key + value from tape).
                        mettail_ast::types::CollectionType::HashMap
                        | mettail_ast::types::CollectionType::PathMap => {
                            code.push_str(&format!(
                                "            let num_elems_{i} = (reader.next_byte() % 4) as usize;\n\
                                             let mut coll_{i} = mettail_runtime::HashMapLit::default();\n\
                                             for _ in 0..num_elems_{i} {{\n\
                                                 let k = build_{fc}_from_tape(reader, child_depth);\n\
                                                 let v = build_{fc}_from_tape(reader, child_depth);\n\
                                                 coll_{i}.insert(k, v);\n\
                                             }}\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("coll_{}", i));
                        },
                        mettail_ast::types::CollectionType::HashSet => {
                            code.push_str(&format!(
                                "            let num_elems_{i} = (reader.next_byte() % 4) as usize;\n\
                                             let mut coll_{i} = std::collections::HashSet::new();\n\
                                             for _ in 0..num_elems_{i} {{\n\
                                                 coll_{i}.insert(build_{fc}_from_tape(reader, child_depth));\n\
                                             }}\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("coll_{}", i));
                        },
                        mettail_ast::types::CollectionType::Vec => {
                            code.push_str(&format!(
                                "            let num_elems_{i} = (reader.next_byte() % 4) as usize;\n\
                                             let coll_{i}: Vec<_> = (0..num_elems_{i}).map(|_| {{\n\
                                                 build_{fc}_from_tape(reader, child_depth)\n\
                                             }}).collect();\n",
                                i = i,
                                fc = field_cat_lower,
                            ));
                            field_exprs.push(format!("coll_{}", i));
                        },
                    }
                } else if field.is_optional && field.is_predicate {
                    // Task #14 (Option<Guard>): `Option<BehavioralPred>`
                    // guard slot — tape byte picks None / Some(Top). No
                    // `build_guard_from_tape` exists (Guard is not a
                    // language category), and the term arm's
                    // `Option<Arc<{cat}>>` type is wrong here. `Top` per
                    // the mandatory-guard arm below (renders `true()`,
                    // display-stable under re-parse — the guarded_rho
                    // prop suite is green with tape-built Top today).
                    code.push_str(&format!(
                        "            let f{i}: Option<mettail_runtime::BehavioralPred> = if reader.next_byte() & 1 == 0 {{ None }} else {{ Some(mettail_runtime::BehavioralPred::Top) }};\n",
                        i = i,
                    ));
                    field_exprs.push(format!("f{}", i));
                } else if field.is_optional {
                    // F7: Opt-Group — Optional fields visit BOTH None
                    // and Some(...) arms based on a tape byte. Spec
                    // admits both, so generator must too. Replaces
                    // the prior None-only emission.
                    let field_cat_lower = field_cat.to_lowercase();
                    code.push_str(&format!(
                        "            let f{i}: Option<std::sync::Arc<{fc}>> = if reader.next_byte() & 1 == 0 {{ None }} else {{ Some(std::sync::Arc::new(build_{fcl}_from_tape(reader, child_depth))) }};\n",
                        i = i,
                        fc = field_cat,
                        fcl = field_cat_lower,
                    ));
                    field_exprs.push(format!("f{}", i));
                } else if field.opaque_leaf
                    == Some(crate::gen::term_ops::subst::OpaqueLeafKind::TokenText)
                    && ident_param_count_for(cat, &label.to_string(), language) > 0
                {
                    // (A4) A token-text leaf (`m:Ident`, `v@Tok`) is a BARE `String`, never
                    // `Arc<Cat>`, and there is no `build_<cat>_from_tape` for it — it is not
                    // a category. Its text comes from the spec-derived, pattern-validated
                    // pool; a tape byte selects from that pool so proptest replay stays
                    // deterministic and shrinking still shortens the tape.
                    //
                    // ⚠ WITHOUT THIS BRANCH the field fell through to the "Unknown category"
                    // arm below, which emits `Arc::new(build_<OWNER>_from_tape(..))` — the
                    // owning category's builder, into a `String` slot. That is generated code
                    // that does not type-check, i.e. a BUILD BREAK rather than the silent
                    // coverage loss the sibling sites had. It had never fired only because no
                    // shipped grammar pairs an `m:Ident` param with a category child.
                    // ★ #141 G4. Generated-source STATEMENT position: the refusal
                    // becomes the `let f{i} = …;` binding's initializer, so the
                    // slot still exists for the constructor call below and the
                    // diagnostic is what rustc reports for it.
                    let initializer = match crate::gen::term_gen::ident_samples(language) {
                        Ok(samples) => {
                            let pool = samples
                                .iter()
                                .map(|s| format!("{s:?}"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!(
                                "[{pool}][(reader.next_byte() as usize) % {n}].to_string()",
                                n = samples.len(),
                            )
                        },
                        Err(message) => format!("compile_error!({message:?})"),
                    };
                    code.push_str(&format!("            let f{i} = {initializer};\n"));
                    field_exprs.push(format!("f{}", i));
                } else if is_known {
                    code.push_str(&format!(
                        "            let f{i} = std::sync::Arc::new(build_{fc}_from_tape(reader, child_depth));\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                    field_exprs.push(format!("f{}", i));
                } else if field.is_predicate {
                    // Guard slot — spec-derived: when the rule carries
                    // no refinement_types predicate the spec genuinely
                    // admits any term in this slot, so `Top` is the
                    // spec's default (NOT a placeholder). Once
                    // refinement predicate lowering (B8) lands, this
                    // call will resolve to the spec's actual predicate
                    // via `spec_witness_predicate_for_guard`.
                    code.push_str(&format!(
                        "            let pred_{i} = mettail_runtime::BehavioralPred::Top;\n",
                        i = i,
                    ));
                    field_exprs.push(format!("pred_{}", i));
                } else {
                    // Unknown category — shouldn't happen for known languages
                    code.push_str(&format!(
                        "            let f{} = std::sync::Arc::new(build_{}_from_tape(reader, 0));\n",
                        i, cat_lower,
                    ));
                    field_exprs.push(format!("f{}", i));
                }
            }

            code.push_str(&format!(
                "            {}::{}({})\n",
                cat,
                label_str,
                field_exprs.join(", "),
            ));

            code
        },

        VariantKind::Collection { label, element_cat, coll_type } => {
            let label_str = label.to_string();
            let elem_cat_lower = element_cat.to_string().to_lowercase();

            match coll_type {
                mettail_ast::types::CollectionType::HashBag
                | mettail_ast::types::CollectionType::HashMap
                | mettail_ast::types::CollectionType::PathMap => {
                    format!(
                        "            let num_elems = (reader.next_byte() % 4) as usize;\n\
                                     let mut bag = mettail_runtime::HashBag::new();\n\
                                     for _ in 0..num_elems {{\n\
                                         bag.insert(build_{fc}_from_tape(reader, child_depth));\n\
                                     }}\n\
                                     {cat}::{label}(bag)\n",
                        fc = elem_cat_lower,
                        cat = cat,
                        label = label_str,
                    )
                },
                mettail_ast::types::CollectionType::HashSet => {
                    format!(
                        "            let num_elems = (reader.next_byte() % 4) as usize;\n\
                                     let mut set = std::collections::HashSet::new();\n\
                                     for _ in 0..num_elems {{\n\
                                         set.insert(build_{fc}_from_tape(reader, child_depth));\n\
                                     }}\n\
                                     {cat}::{label}(set)\n",
                        fc = elem_cat_lower,
                        cat = cat,
                        label = label_str,
                    )
                },
                mettail_ast::types::CollectionType::Vec => {
                    format!(
                        "            let num_elems = (reader.next_byte() % 4) as usize;\n\
                                     let elems: Vec<_> = (0..num_elems).map(|_| {{\n\
                                         build_{fc}_from_tape(reader, child_depth)\n\
                                     }}).collect();\n\
                                     {cat}::{label}(elems)\n",
                        fc = elem_cat_lower,
                        cat = cat,
                        label = label_str,
                    )
                },
            }
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_direct_build(
                cat,
                &label.to_string(),
                pre_scope_fields,
                &body_cat.to_string(),
                false,
                language,
            )
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_direct_build(
                cat,
                &label.to_string(),
                pre_scope_fields,
                &body_cat.to_string(),
                true,
                language,
            )
        },

        _ => {
            format!("            build_{}_from_tape(reader, 0)\n", cat_lower)
        },
    }
}

/// Generate direct build code for a binder variant.
fn generate_binder_direct_build(
    cat: &str,
    label: &str,
    pre_scope_fields: &[FieldInfo],
    body_cat: &str,
    is_multi: bool,
    language: &LanguageDef,
) -> String {
    let body_cat_lower = body_cat.to_lowercase();
    let mut code = String::new();

    // Build pre-scope fields
    let mut pre_scope_exprs = Vec::new();
    for (i, field) in pre_scope_fields.iter().enumerate() {
        let field_cat = field.category.to_string();
        let field_cat_lower = field_cat.to_lowercase();
        let is_known = language.types.iter().any(|t| t.name == field.category);

        // Phase 4 #4 (2026-05-12): Optional-Collection pre-scope field — visit
        // both None and Some(Container) arms based on a tape byte. AST shape
        // is `Option<Container>` (bare, no Box). Mirrors the Regular path in
        // `generate_constructor_match_arms`.
        if field.is_optional && field.is_collection {
            let coll_type = match coll_type_or_refusal(field, label) {
                Ok(coll_type) => coll_type,
                Err(refusal) => {
                    code.push_str(&refusal);
                    pre_scope_exprs.push("Default::default()".to_string());
                    continue;
                },
            };
            match coll_type {
                mettail_ast::types::CollectionType::HashBag
                | mettail_ast::types::CollectionType::HashMap
                | mettail_ast::types::CollectionType::PathMap => {
                    code.push_str(&format!(
                        "            let pre_{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                         let num_elems = (reader.next_byte() % 4) as usize;\n\
                                         let mut bag = mettail_runtime::HashBag::new();\n\
                                         for _ in 0..num_elems {{ bag.insert(build_{fc}_from_tape(reader, child_depth)); }}\n\
                                         Some(bag)\n\
                                     }};\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                },
                mettail_ast::types::CollectionType::HashSet => {
                    code.push_str(&format!(
                        "            let pre_{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                         let num_elems = (reader.next_byte() % 4) as usize;\n\
                                         let mut s = std::collections::HashSet::new();\n\
                                         for _ in 0..num_elems {{ s.insert(build_{fc}_from_tape(reader, child_depth)); }}\n\
                                         Some(s)\n\
                                     }};\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                },
                mettail_ast::types::CollectionType::Vec => {
                    code.push_str(&format!(
                        "            let pre_{i} = if reader.next_byte() & 1 == 0 {{ None }} else {{\n\
                                         let num_elems = (reader.next_byte() % 4) as usize;\n\
                                         let v: Vec<_> = (0..num_elems).map(|_| build_{fc}_from_tape(reader, child_depth)).collect();\n\
                                         Some(v)\n\
                                     }};\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                },
            }
            pre_scope_exprs.push(format!("pre_{}", i));
            continue;
        }

        if is_known && !field.is_collection {
            code.push_str(&format!(
                "            let pre_{i} = std::sync::Arc::new(build_{fc}_from_tape(reader, child_depth));\n",
                i = i,
                fc = field_cat_lower,
            ));
            pre_scope_exprs.push(format!("pre_{}", i));
        } else if field.is_predicate {
            if field.is_optional {
                // Task #14 (Option<Guard>): pre-scope twin of the Regular
                // tape-builder's optional-guard arm — tape byte picks
                // None / Some(Top) for an `Option<BehavioralPred>` field.
                // Dormant until a Binder-rule optional guard exists.
                code.push_str(&format!(
                    "            let pred_{i}: Option<mettail_runtime::BehavioralPred> = if reader.next_byte() & 1 == 0 {{ None }} else {{ Some(mettail_runtime::BehavioralPred::Top) }};\n",
                    i = i,
                ));
            } else {
                // Guard slot — spec-derived: same rationale as above.
                // `Top` is the spec's default for unspecified guards.
                code.push_str(&format!(
                    "            let pred_{i} = mettail_runtime::BehavioralPred::Top;\n",
                    i = i,
                ));
            }
            pre_scope_exprs.push(format!("pred_{}", i));
        } else if field.is_collection {
            // F5: spec-derived coll_type — every collection field MUST
            // carry coll_type per the language! spec.
            let coll_type = match coll_type_or_refusal(field, label) {
                Ok(coll_type) => coll_type,
                Err(refusal) => {
                    code.push_str(&refusal);
                    pre_scope_exprs.push("Default::default()".to_string());
                    continue;
                },
            };
            match coll_type {
                mettail_ast::types::CollectionType::Vec => {
                    code.push_str(&format!(
                        "            let n_{i} = (reader.next_byte() % 3) as usize;\n\
                                     let pre_{i}: Vec<_> = (0..n_{i}).map(|_| build_{fc}_from_tape(reader, child_depth)).collect();\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                    pre_scope_exprs.push(format!("pre_{}", i));
                },
                _ => {
                    // HashBag/HashSet not typical for pre-scope, but handle
                    code.push_str(&format!(
                        "            let pre_{i} = Vec::<{fc}>::new();\n",
                        i = i,
                        fc = field_cat,
                    ));
                    pre_scope_exprs.push(format!("pre_{}", i));
                },
            }
        }
    }

    // Build the scope
    // F8: spec-derived binder name prefix; replaces hard-coded "v".
    let var_prefix = crate::gen::spec_admitted_var_name(language);
    if is_multi {
        code.push_str(&format!(
            "            let num_binders = ((reader.next_byte() % 3) + 1) as usize;\n\
                         let binders: Vec<mettail_runtime::Binder<String>> = (0..num_binders)\n\
                             .map(|j| {{\n\
                                 let name = format!(\"{vp}{{}}\", j);\n\
                                 mettail_runtime::Binder(mettail_runtime::get_or_create_var(&name))\n\
                             }})\n\
                             .collect();\n\
                         let body = build_{bc}_from_tape(reader, child_depth);\n\
                         let scope = mettail_runtime::Scope::new(binders, std::sync::Arc::new(body));\n",
            vp = var_prefix,
            bc = body_cat_lower,
        ));
    } else {
        code.push_str(&format!(
            "            let binder_name = format!(\"{vp}{{}}\", reader.next_byte() % 8);\n\
                         let binder = mettail_runtime::Binder(mettail_runtime::get_or_create_var(&binder_name));\n\
                         let body = build_{bc}_from_tape(reader, child_depth);\n\
                         let scope = mettail_runtime::Scope::new(binder, std::sync::Arc::new(body));\n",
            vp = var_prefix,
            bc = body_cat_lower,
        ));
    }

    // Assemble
    if pre_scope_exprs.is_empty() {
        code.push_str(&format!("            {}::{}(scope)\n", cat, label,));
    } else {
        code.push_str(&format!(
            "            {}::{}({}, scope)\n",
            cat,
            label,
            pre_scope_exprs.join(", "),
        ));
    }

    code
}

/// Generate `arb_{cat}` strategy function for one category.
fn generate_arb_strategy(category: &syn::Ident, _language: &LanguageDef, out: &mut String) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();

    out.push_str(&format!("/// Generate an arbitrary `{}` term with bounded depth.\n", cat));
    out.push_str(&format!(
        "///\n/// Uses a flat `Vec<u8>` tape interpreted by `build_{}_from_tape`.\n/// Proptest shrinking produces shorter tapes = simpler terms.\n",
        cat_lower
    ));
    out.push_str("#[allow(dead_code)]\n");
    out.push_str(&format!(
        "fn arb_{cat_lower}(max_depth: u32) -> BoxedStrategy<{cat}> {{\n\
         \x20   // Tape size scales with depth: deeper terms need more bytes\n\
         \x20   let max_tape = (10 * (max_depth as usize + 1)).max(20);\n\
         \x20   proptest::collection::vec(any::<u8>(), 1..max_tape)\n\
         \x20       .prop_map(move |tape| {{\n\
         \x20           let mut reader = TapeReader::new(&tape);\n\
         \x20           build_{cat_lower}_from_tape(&mut reader, max_depth)\n\
         \x20       }})\n\
         \x20       .boxed()\n\
         }}\n\n",
        cat_lower = cat_lower,
        cat = cat,
    ));
}

/// Generate proptest blocks that exercise the generated strategies.
fn generate_proptest_blocks(language: &LanguageDef, out: &mut String) {
    out.push_str("proptest! {\n");
    out.push_str(&format!(
        "    #![proptest_config({})]\n\n",
        super::proptest_config_expr(language, 100)
    ));

    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();
        // Runtime-only opaque natives (e.g. ReadZipper/WriteZipper) have no
        // surface syntax, so a Display→parse roundtrip is ill-posed for them
        // (their Display, e.g. `readZipper@0`, is unparseable by construction).
        // Skip ONLY the parse-involving tests (4 & 5) for them; the non-parse
        // tests (debug/display/clone) stay, so `arb_<cat>` keeps a referent.
        let is_runtime_only =
            crate::gen::category_is_runtime_only_native(&lang_type.name, language);

        // Generation depth for the display->parse roundtrip (test 4): uniform
        // depth 3 for EVERY category. The former per-category depth-2 cap for
        // cross-category-ambiguous categories is retired: the walker's k-best
        // extraction (ROOT-P) elects derivations in weight order instead of
        // materializing the exponential cross-category parse family, so even
        // maximally-ambiguous shared-operator chains at depth 3 parse in
        // milliseconds (acceptance receipts:
        // `scratchpad/zz_probes/logs_kbest_s4/`).
        let roundtrip_depth = 3;

        // Test 1: Generated terms can be Debug-formatted without panic
        out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_debug_does_not_panic(term in arb_{cat_lower}(4)) {{\n\
             \x20       let _ = format!(\"{{:?}}\", term);\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
        ));

        // Test 2: Generated terms can be Display-formatted without panic
        out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_display_does_not_panic(term in arb_{cat_lower}(4)) {{\n\
             \x20       let _ = format!(\"{{}}\", term);\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
        ));

        // Test 3: Clone round-trip
        out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_clone_eq(term in arb_{cat_lower}(4)) {{\n\
             \x20       let cloned = term.clone();\n\
             \x20       prop_assert_eq!(term, cloned);\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
        ));

        // Test 4: Display round-trip — CANONICAL-DISPLAY IDEMPOTENCE, not
        // AST equality: the emitted body asserts
        // `Display(Parse(Display(Parse(s)))) == Display(Parse(s))` (the
        // canonical form re-parses to something that displays identically),
        // NEVER `parse(display(term)) == term`. Guard slots rely on this:
        // `BehavioralPred::Top` displays as `true()`, which re-parses to
        // `RelationQuery("true", [])` — display-stable by design, so the
        // roundtrip holds even though the ASTs differ.
        // Only if the category has a parse method — all categories do via PraTTaIL.
        // Skipped for runtime-only opaque natives (no surface form to parse).
        //
        // GENERATION DEPTH (`roundtrip_depth`, computed above): uniform depth 3
        // for every category. The displayed surface is a parenthesis-minimal
        // operator tree (Display omits precedence-redundant parens to keep
        // one-cycle idempotence — see `macros/src/gen/syntax/display.rs`).
        // Categories whose operator terminals are SHARED with other categories
        // over syntaxless cross-category projections (e.g. Calculator's
        // `+ * / bitand bitor` across Int/BigInt/BigRat/Float/Fixed/UInt32)
        // still multiply the WPDA parse forest along the cross-category edge
        // axis, but the walker's k-best extraction (ROOT-P;
        // `prattail/src/wpda_walker.rs`) elects derivations in weight order
        // without materializing the exponential family, so maximally-ambiguous
        // depth-3 chains parse in milliseconds (acceptance receipts:
        // `scratchpad/zz_probes/logs_kbest_s4/`). The TapeReader is
        // non-wrapping, so short/shrunk tapes yield SIMPLE terms and proptest
        // shrinking converges on minimal counterexamples.
        if !is_runtime_only {
            out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_display_parse_roundtrip(term in arb_{cat_lower}({depth})) {{\n\
             \x20       let displayed = format!(\"{{}}\", term);\n\
             \x20       // Skip terms whose display is too long (parser may overflow).\n\
             \x20       // NOTE: length is only a coarse backstop against degenerate\n\
             \x20       // displays; cross-category-shared operator chains are parsed\n\
             \x20       // via the walker's k-best extraction, so depth-3 terms are cheap.\n\
             \x20       if displayed.len() > 500 {{\n\
             \x20           return Ok(());\n\
             \x20       }}\n\
             \x20       // GRAMMAR-AWARE ROUNDTRIP CONTRACT (strengthened from\n\
             \x20       // silent-skip): the literal-build codegen now projects\n\
             \x20       // tape values onto the language's admitted literal\n\
             \x20       // domain (see rust_code_rewrite + automaton_walk::classify).\n\
             \x20       // Any parse failure here is a real regression — the\n\
             \x20       // generator emitted something the grammar does not admit.\n\
             \x20       // Canonical-form idempotence:\n\
             \x20       //   Parse(Display(Parse(s))) ≡ Parse(s) for any s that\n\
             \x20       //   the generator emits.\n\
             \x20       let parsed = {cat}::parse(&displayed)\n\
             \x20           .unwrap_or_else(|e| panic!(\n\
             \x20               \"arb_{cat_lower} produced unparseable surface term {{:?}}: {{:?}}\",\n\
             \x20               displayed, e));\n\
             \x20       let canonical = format!(\"{{}}\", parsed);\n\
             \x20       if canonical.len() > 500 {{ return Ok(()); }}\n\
             \x20       let reparsed = {cat}::parse(&canonical).unwrap_or_else(|e| panic!(\n\
             \x20           \"Parse(Display(Parse(s))) should succeed for canonical form {{:?}}: {{:?}}\",\n\
             \x20           canonical, e));\n\
             \x20       let recanonical = format!(\"{{}}\", reparsed);\n\
             \x20       // Snapshot before the move: `prop_assert_eq!` consumes both operands.\n\
             \x20       let __first_surface = canonical.clone();\n\
             \x20       prop_assert_eq!(canonical, recanonical,\n\
             \x20           \"Display should be idempotent after canonicalization: \\\n\
             \x20            display(parse(display(parse(display(t))))) == display(parse(display(t)))\");\n\
             \x20       // ★ CONVERGENCE WITH AN EXPLICIT BOUND (2026-07-26). The assertion above\n\
             \x20       // is a FIXPOINT test at depth 2, and when it fails it prints two opaque\n\
             \x20       // strings and no diagnosis. A surface synonym does not fail it randomly:\n\
             \x20       // it sheds exactly ONE surface per nesting layer, so the layer count IS\n\
             \x20       // the measurement. This loop reports it — \"converged in 3, expected 1\"\n\
             \x20       // says at once that the term carries a synonym two levels deep, which is\n\
             \x20       // the fact `languages/tests/surface_synonymy_gate.rs` then localises to a\n\
             \x20       // class and a member.\n\
             \x20       let mut __surface = __first_surface.clone();\n\
             \x20       let mut __layers = 0usize;\n\
             \x20       for _ in 0..8 {{\n\
             \x20           let __next_term = match {cat}::parse(&__surface) {{\n\
             \x20               Ok(t) => t,\n\
             \x20               Err(e) => {{\n\
             \x20                   prop_assert!(false,\n\
             \x20                       \"the canonical surface {{:?}} stopped parsing at layer {{}}: {{:?}}\",\n\
             \x20                       __surface, __layers, e);\n\
             \x20                   unreachable!()\n\
             \x20               }},\n\
             \x20           }};\n\
             \x20           let __next = format!(\"{{}}\", __next_term);\n\
             \x20           if __next == __surface {{ break; }}\n\
             \x20           __surface = __next;\n\
             \x20           __layers += 1;\n\
             \x20       }}\n\
             \x20       prop_assert_eq!(__layers, 0,\n\
             \x20           \"Display/Parse converged in {{}} extra layer(s), expected 0: the surface \\\n\
             \x20            sheds one spelling per layer, which is the signature of a SURFACE \\\n\
             \x20            SYNONYM whose class has no declared canonical member. First surface \\\n\
             \x20            {{:?}}, fixpoint {{:?}}.\", __layers, __first_surface, __surface);\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
            cat = cat,
            depth = roundtrip_depth,
        ));
        }

        // Test 5 (Group F): Strong roundtrip canonical stability.
        // Some grammars intentionally canonicalize display surfaces at parse time
        // (for example by making implicit category projections explicit). The
        // stable long-term contract is therefore not raw string equality with the
        // pre-canonical surface, but idempotence once a parse/display pair has
        // chosen its canonical representative.
        // Uses depth 1 and limits displayed string length to avoid stack
        // overflow during parsing or PartialEq comparison of nested terms.
        let cat_has_binders = category_has_binders(&lang_type.name, language);
        if !cat_has_binders && !is_runtime_only {
            out.push_str(&format!(
                "    #[test]\n\
                 \x20   fn {cat_lower}_strong_roundtrip(term in arb_{cat_lower}(1)) {{\n\
                 \x20       mettail_runtime::clear_var_cache();\n\
                 \x20       let displayed = format!(\"{{}}\", term);\n\
                 \x20       // Skip terms whose display is too long (parser may overflow)\n\
                 \x20       if displayed.len() > 500 {{\n\
                 \x20           return Ok(());\n\
                 \x20       }}\n\
                 \x20       mettail_runtime::clear_var_cache();\n\
                 \x20       if let Ok(parsed) = {cat}::parse(&displayed) {{\n\
                 \x20           let canonical = format!(\"{{}}\", parsed);\n\
                 \x20           if canonical.len() > 500 {{ return Ok(()); }}\n\
                 \x20           mettail_runtime::clear_var_cache();\n\
                 \x20           let reparsed = {cat}::parse(&canonical).unwrap_or_else(|e| panic!(\n\
                 \x20               \"Strong roundtrip: canonical form {{:?}} did not parse: {{:?}}\",\n\
                 \x20               canonical, e));\n\
                 \x20           let recanonical = format!(\"{{}}\", reparsed);\n\
                 \x20           prop_assert_eq!(&canonical, &recanonical,\n\
                 \x20               \"Strong roundtrip: canonical display not stable after double parse\");\n\
                 \x20       }}\n\
                 \x20   }}\n\n",
                cat_lower = cat_lower,
                cat = cat,
            ));
        } else {
            // For categories with binders, test alpha-equivalent roundtrip via display
            out.push_str(&format!(
                "    #[test]\n\
                 \x20   fn {cat_lower}_strong_roundtrip_via_display(term in arb_{cat_lower}(1)) {{\n\
                 \x20       mettail_runtime::clear_var_cache();\n\
                 \x20       let displayed = format!(\"{{}}\", term);\n\
                 \x20       // Skip terms whose display is too long (parser may overflow)\n\
                 \x20       if displayed.len() > 500 {{\n\
                 \x20           return Ok(());\n\
                 \x20       }}\n\
                 \x20       mettail_runtime::clear_var_cache();\n\
                 \x20       if let Ok(parsed) = {cat}::parse(&displayed) {{\n\
                 \x20           let canonical = format!(\"{{}}\", parsed);\n\
                 \x20           if canonical.len() > 500 {{ return Ok(()); }}\n\
                 \x20           mettail_runtime::clear_var_cache();\n\
                 \x20           let reparsed = {cat}::parse(&canonical).unwrap_or_else(|e| panic!(\n\
                 \x20               \"Strong roundtrip (display proxy): canonical form {{:?}} did not parse: {{:?}}\",\n\
                 \x20               canonical, e));\n\
                 \x20           let recanonical = format!(\"{{}}\", reparsed);\n\
                 \x20           prop_assert_eq!(&canonical, &recanonical,\n\
                 \x20               \"Strong roundtrip (display proxy): canonical display not stable after double parse\");\n\
                 \x20       }}\n\
                 \x20   }}\n\n",
                cat_lower = cat_lower,
                cat = cat,
            ));
        }

        // Test 6 (Group E): Parse determinism — parsing the same displayed string twice
        // produces identical display output. This tests that the parser is deterministic
        // without invoking run_ascent (which can overflow the stack on random terms).
        out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_parse_determinism(term in arb_{cat_lower}(2)) {{\n\
             \x20       mettail_runtime::clear_var_cache();\n\
             \x20       let displayed = format!(\"{{}}\", term);\n\
             \x20       // Skip terms whose display is too long (parser may overflow)\n\
             \x20       if displayed.len() > 500 {{\n\
             \x20           return Ok(());\n\
             \x20       }}\n\
             \x20       mettail_runtime::clear_var_cache();\n\
             \x20       let p1 = {cat}::parse(&displayed);\n\
             \x20       mettail_runtime::clear_var_cache();\n\
             \x20       let p2 = {cat}::parse(&displayed);\n\
             \x20       match (p1, p2) {{\n\
             \x20           (Ok(t1), Ok(t2)) => {{\n\
             \x20               let d1 = format!(\"{{}}\", t1);\n\
             \x20               let d2 = format!(\"{{}}\", t2);\n\
             \x20               prop_assert_eq!(d1, d2,\n\
             \x20                   \"Parse determinism failed: two parses of the same string differ\");\n\
             \x20           }}\n\
             \x20           (Err(_), Err(_)) => {{ /* Both failed — consistent */ }}\n\
             \x20           (Ok(_), Err(e)) | (Err(e), Ok(_)) => {{\n\
             \x20               prop_assert!(false,\n\
             \x20                   \"Parse determinism failed: one parse succeeded, other failed: {{}}\", e);\n\
             \x20           }}\n\
             \x20       }}\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
            cat = cat,
        ));
    }

    out.push_str("}\n");
}

// ══════════════════════════════════════════════════════════════════════════════
// Public strategy generation (Phase 1: public strategy exposure)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate public proptest strategies as a `TokenStream` for inclusion in
/// the `language!` macro expansion.
///
/// This produces the same tape-based builder infrastructure as
/// [`generate_strategies`], but:
/// - All items have `pub` visibility so external crates can use them.
/// - The output is a [`proc_macro2::TokenStream`] (for macro expansion)
///   rather than a `String` (for test file writing).
/// - Wrapped in `#[cfg(feature = "strategies")]` by the caller.
///
/// The generated code includes:
/// - `pub struct TapeReader<'a>` — byte-tape consumer
/// - `pub enum AnyTerm` — heterogeneous term wrapper with `pub fn unwrap_{cat}()`
/// - `pub enum BuildTask` — work-stack items for iterative term building
/// - `pub fn build_{cat}_from_tape(reader, depth) -> Cat` — per-category builders
/// - `pub fn arb_{cat}(max_depth: u32) -> BoxedStrategy<Cat>` — per-category strategies
///
/// ## Design: String → TokenStream bridge
///
/// Rather than duplicating the complex variant classification and code generation
/// logic, this function reuses the string-based generation functions, applies
/// visibility transformations, and parses the result into a `TokenStream` via
/// `syn::parse_str`. This ensures the public and private strategies stay in lock-step.
pub fn generate_public_strategies(language: &LanguageDef) -> TokenStream {
    let mut out = String::with_capacity(16384);

    // Generate the AnyTerm enum (public)
    generate_public_any_term_enum(language, &mut out);

    // Generate the BuildTask enum (public)
    generate_public_build_task_enum(language, &mut out);

    // Generate the public tape reader
    generate_public_tape_reader(&mut out);

    // Generate public build_from_tape function per category
    for lang_type in &language.types {
        generate_public_build_from_tape(&lang_type.name, language, &mut out);
    }

    // Generate public arb_ strategy functions per category
    for lang_type in &language.types {
        generate_public_arb_strategy(&lang_type.name, language, &mut out);
    }

    // Parse the generated string into a TokenStream.
    // If parsing fails (should not happen for well-formed generation), emit
    // a compile_error so the user sees a clear diagnostic.
    match syn::parse_str::<proc_macro2::TokenStream>(&out) {
        Ok(ts) => ts,
        Err(err) => {
            let msg = format!(
                "Failed to parse generated public strategies: {}. \
                 Generated code:\n{}",
                err, out
            );
            quote! { compile_error!(#msg); }
        },
    }
}

/// Generate the public `AnyTerm` enum.
fn generate_public_any_term_enum(language: &LanguageDef, out: &mut String) {
    out.push_str("/// Heterogeneous term wrapper for the tape-based builder.\n");
    out.push_str("#[allow(dead_code)]\n");
    out.push_str("#[derive(Clone)]\n");
    out.push_str("pub enum AnyTerm {\n");
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        out.push_str(&format!("    Wrap{}({}),\n", cat, cat));
    }
    out.push_str("}\n\n");

    // Unwrap helpers (public)
    out.push_str("impl AnyTerm {\n");
    let multi_category = language.types.len() > 1;
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();
        out.push_str(&format!(
            "    /// Unwrap the inner `{}` value, panicking if the variant is wrong.\n",
            cat
        ));
        out.push_str("    #[allow(dead_code)]\n");
        // Single-category `AnyTerm` has one variant; a `_ =>` arm would be an unreachable pattern.
        let wrong_variant_arm = if multi_category {
            format!(
                "\x20           _ => panic!(\"AnyTerm::unwrap_{cat_lower}: wrong variant\"),\n",
                cat_lower = cat_lower
            )
        } else {
            String::new()
        };
        out.push_str(&format!(
            "    pub fn unwrap_{cat_lower}(self) -> {cat} {{\n\
             \x20       match self {{\n\
             \x20           AnyTerm::Wrap{cat}(v) => v,\n\
             {wrong_variant_arm}\
             \x20       }}\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
            cat = cat,
            wrong_variant_arm = wrong_variant_arm,
        ));
    }
    out.push_str("}\n\n");
}

/// Generate the public `BuildTask` enum.
fn generate_public_build_task_enum(language: &LanguageDef, out: &mut String) {
    out.push_str("/// Work item for the tape-based iterative term builder.\n");
    out.push_str("#[allow(dead_code)]\n");
    out.push_str("pub enum BuildTask {\n");
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        out.push_str(&format!(
            "    /// Build a {} term at the given depth, storing result in the given slot.\n",
            cat
        ));
        out.push_str(&format!("    Build{} {{ depth: u32, slot: usize }},\n", cat));
    }
    out.push_str("}\n\n");
}

/// Generate the public TapeReader helper struct.
fn generate_public_tape_reader(out: &mut String) {
    out.push_str(
        r#"/// Helper to consume bytes from a proptest-generated instruction tape.
#[allow(dead_code)]
pub struct TapeReader<'a> {
    tape: &'a [u8],
    pos: usize,
}

#[allow(dead_code)]
impl<'a> TapeReader<'a> {
    /// Create a new tape reader over the given byte slice.
    pub fn new(tape: &'a [u8]) -> Self {
        TapeReader { tape, pos: 0 }
    }

    /// Read the next byte. On exhaustion return 0 — do NOT wrap (byte 0 selects
    /// constructor choice 0, always a leaf, so an exhausted tape bottoms the
    /// recursion out to the simplest term). See the private `TapeReader` for the
    /// full rationale; the old `pos % len` wrap re-read the same recursive
    /// constructor byte at every level and built complete trees from short tapes.
    pub fn next_byte(&mut self) -> u8 {
        if self.pos >= self.tape.len() {
            return 0;
        }
        let b = self.tape[self.pos];
        self.pos += 1;
        b
    }

    /// Read a u32 from 4 bytes (little-endian); reads 0 past end of tape.
    pub fn next_u32(&mut self) -> u32 {
        let b0 = self.next_byte() as u32;
        let b1 = self.next_byte() as u32;
        let b2 = self.next_byte() as u32;
        let b3 = self.next_byte() as u32;
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }

    /// Read an i32 from tape bytes.
    pub fn next_i32(&mut self) -> i32 {
        self.next_u32() as i32
    }

    /// Read an i64 from tape bytes.
    pub fn next_i64(&mut self) -> i64 {
        let lo = self.next_u32() as i64;
        let hi = self.next_u32() as i64;
        lo | (hi << 32)
    }

    /// Read an f64 from tape bytes.
    pub fn next_f64(&mut self) -> f64 {
        let bits = self.next_i64() as u64;
        let val = f64::from_bits(bits);
        // Avoid NaN/Inf which cause issues with Eq/Ord
        if val.is_nan() || val.is_infinite() { 0.0 } else { val }
    }

    /// Read an f32 from tape bytes.
    pub fn next_f32(&mut self) -> f32 {
        let bits = self.next_u32();
        let val = f32::from_bits(bits);
        if val.is_nan() || val.is_infinite() { 0.0f32 } else { val }
    }

    /// Read a bool from tape.
    pub fn next_bool(&mut self) -> bool {
        self.next_byte() & 1 == 1
    }

    /// Read a short string from tape.
    pub fn next_string(&mut self) -> String {
        let len = (self.next_byte() % 8) as usize;
        (0..len)
            .map(|_| {
                let b = self.next_byte();
                // Map to printable ASCII range 'a'-'z'
                (b'a' + (b % 26)) as char
            })
            .collect()
    }
}

"#,
    );
}

/// Generate a public `build_{cat}_from_tape` function for one category.
///
/// Mirrors [`generate_build_from_tape`] but with `pub` visibility.
fn generate_public_build_from_tape(
    category: &syn::Ident,
    language: &LanguageDef,
    out: &mut String,
) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();
    let classification = classify_variants(category, language);

    out.push_str(&format!("/// Build a `{}` term from an instruction tape.\n", cat));
    out.push_str("///\n/// Consumes bytes from the tape to choose constructors.\n/// At depth 0, only leaf constructors (nullary, literal, var) are chosen.\n/// At depth > 0, recursive constructors are also available.\n");
    out.push_str("#[allow(dead_code, unused_variables, clippy::let_and_return)]\n");
    out.push_str(&format!(
        "pub fn build_{cat_lower}_from_tape(reader: &mut TapeReader<'_>, depth: u32) -> {cat} {{\n",
        cat_lower = cat_lower,
        cat = cat,
    ));

    let num_leaves = classification.leaves.len();
    let num_recursive = classification.recursive.len();
    let total = num_leaves + num_recursive;

    // At depth 0, only choose leaves
    out.push_str("    if depth == 0 {\n");
    if num_leaves == 1 {
        let (_, ref code) = classification.leaves[0];
        out.push_str(&format!("        let result = {};\n", code));
        out.push_str(&format!("        return result.unwrap_{}();\n", cat_lower));
    } else {
        out.push_str(&format!(
            "        let choice = (reader.next_byte() as usize) % {};\n",
            num_leaves
        ));
        out.push_str("        let result = match choice {\n");
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            if i == num_leaves - 1 {
                out.push_str(&format!("            _ => {},\n", code));
            } else {
                out.push_str(&format!("            {} => {},\n", i, code));
            }
        }
        out.push_str("        };\n");
        out.push_str(&format!("        return result.unwrap_{}();\n", cat_lower));
    }
    out.push_str("    }\n\n");

    // At depth > 0, can choose leaves or recursive constructors
    if num_recursive == 0 {
        out.push_str("    // No recursive constructors, fall back to leaf\n");
        out.push_str(&format!("    build_{}_from_tape(reader, 0)\n", cat_lower));
    } else {
        out.push_str(&format!("    let choice = (reader.next_byte() as usize) % {};\n", total));
        out.push_str("    let child_depth = depth - 1;\n");
        out.push_str("    match choice {\n");

        // Leaves first
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            out.push_str(&format!("        {} => {}.unwrap_{}(),\n", i, code, cat_lower));
        }

        // Then recursive constructors
        for (i, (label, _)) in classification.recursive.iter().enumerate() {
            let idx = num_leaves + i;
            let is_last = idx == total - 1;

            let match_prefix = if is_last {
                "        _ =>".to_string()
            } else {
                format!("        {} =>", idx)
            };

            let code = generate_direct_recursive_build(&cat, label, category, language);
            out.push_str(&format!("{} {{\n", match_prefix));
            out.push_str(&code);
            out.push_str("        },\n");
        }

        out.push_str("    }\n");
    }

    out.push_str("}\n\n");
}

/// Generate a public `arb_{cat}` strategy function for one category.
fn generate_public_arb_strategy(category: &syn::Ident, _language: &LanguageDef, out: &mut String) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();

    out.push_str(&format!("/// Generate an arbitrary `{}` term with bounded depth.\n", cat));
    out.push_str(&format!(
        "///\n/// Uses a flat `Vec<u8>` tape interpreted by `build_{}_from_tape`.\n/// Proptest shrinking produces shorter tapes = simpler terms.\n",
        cat_lower
    ));
    out.push_str("#[allow(dead_code)]\n");
    out.push_str(&format!(
        "pub fn arb_{cat_lower}(max_depth: u32) -> BoxedStrategy<{cat}> {{\n\
         \x20   // Tape size scales with depth: deeper terms need more bytes\n\
         \x20   let max_tape = (10 * (max_depth as usize + 1)).max(20);\n\
         \x20   proptest::collection::vec(proptest::prelude::any::<u8>(), 1..max_tape)\n\
         \x20       .prop_map(move |tape| {{\n\
         \x20           let mut reader = TapeReader::new(&tape);\n\
         \x20           build_{cat_lower}_from_tape(&mut reader, max_depth)\n\
         \x20       }})\n\
         \x20       .boxed()\n\
         }}\n\n",
        cat_lower = cat_lower,
        cat = cat,
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **A-8, the THIRD site** — the proptest tape builder.
    ///
    /// The design brief named two places an `Ident` position was dropped
    /// (`term_gen/random.rs`, `term_gen/exhaustive.rs`). This is a third, and it is WORSE
    /// than a drop: a token-text field beside a category child fell through to the "Unknown
    /// category" arm, which emits `Arc::new(build_<OWNER>_from_tape(..))` into a `String`
    /// slot — generated code that does not type-check. It had never fired only because no
    /// shipped grammar pairs an `m:Ident` param with a category child; the collapse this
    /// capability enables is exactly that shape, on a language whose generated property
    /// suite IS emitted.
    ///
    /// ★ CONTROL, so this cannot pass by admitting everything: a `*flt(…)` guest-body
    /// variant must still be ABSENT from the generated strategies — it has no tape
    /// construction and no reliably re-parseable Display.
    #[test]
    fn token_text_field_is_a_string_in_the_tape_builder() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: IdentStrategyGen,
                types { Proc }
                tokens {
                    FltOpenBrace = "box\\{" push(flt_body) ;
                    raw mode flt_body {
                        FltCloseBrace = "\\}" pop ;
                        GuestChunk = "[^{}]+" ;
                    }
                }
                terms {
                    Nil . |- "0" : Proc ;
                    Named . m:Ident |- "tag" m : Proc ;
                    Call . recv:Proc, m:Ident |- "call" "(" recv "," m ")" : Proc ;
                    Guest . |- *flt(node, FltOpenBrace, FltCloseBrace) : Proc ;
                }
            "#,
        )
        .expect("the fixture language must parse");
        let code = generate_strategies(&language);

        // The MIXED variant's text slot is a bare `String`, chosen from the spec-derived
        // pool — never `Arc::new(build_proc_from_tape(..))`, which is what the pre-A
        // fall-through emitted there.
        assert!(
            code.contains("Proc::Call("),
            "the mixed ident-bearing constructor must be generated at all:\n{code}",
        );
        assert!(
            code.contains(".to_string();"),
            "the token-text slot must be filled with an owned `String`:\n{code}",
        );
        // The IDENT-ONLY variant is a LEAF, not a silent drop.
        assert!(
            code.contains("Proc::Named("),
            "an ident-only constructor must be generated as a leaf rather than dropped:\n\
             {code}",
        );
        // CONTROL: the guest-body variant stays out.
        assert!(
            !code.contains("Proc::Guest("),
            "a guest-body constructor has no tape construction and must stay EXCLUDED — \
             otherwise this test would be passing by admitting everything:\n{code}",
        );
    }

    /// **A-4, the PROVENANCE discrimination.** `OpaqueLeafKind::TokenText` is shared by an
    /// `m:Ident` param and a DECLARED `v@Tok` capture, and they are governed by DIFFERENT
    /// lexer patterns. The generator samples the effective `Ident` pattern, so it may only do
    /// so on POSITIVE evidence of an `m:Ident` param.
    ///
    /// ★ MUTATION IT REJECTS: dropping the `ident_param_count_for(..)` guard puts an `Ident`
    /// sample (`"a"`) into a field the grammar says must match `Word = "<[a-z]+>"` — a
    /// generated term whose `Display` does not re-lex, failing the round-trip property with a
    /// message pointing at the parser rather than at the sampler. This was a real defect in
    /// the first cut of this change, caught by re-reading the generated output for
    /// `L9ModalToy` rather than by any assertion, which is why it now has one.
    #[test]
    fn declared_token_kind_capture_is_not_sampled_from_the_ident_pattern() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: DeclaredKindStrategyGen,
                types { ![i32] as Num }
                tokens {
                    Word = "<[a-z]+>" ;
                }
                terms {
                    AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] ;
                    Tagged . |- "tag" w@Word : Num ![w.len() as i32];
                }
            "#,
        )
        .expect("the fixture language must parse");
        let code = generate_strategies(&language);
        // The `Ident`-pattern samples are `"A"` / `"AA"` / `"AAA"` (the shortest strings the
        // default `[a-zA-Z_][a-zA-Z0-9_]*` DFA accepts, repeated); none may appear in a field
        // the grammar governs with `Word`.
        for wrong in ["Num::Tagged(\"A\"", "Num::Tagged(\"AA\"", "Num::Tagged(\"a\""] {
            assert!(
                !code.replace(' ', "").contains(&wrong.replace(' ', "")),
                "a `v@Word` capture must NOT be sampled from the `Ident` pattern ({wrong}):\n\
                 {code}",
            );
        }
        // ANTI-VACUITY: the generator did run and did produce this category's builder.
        assert!(
            code.contains("build_num_from_tape"),
            "the strategies generator must have produced a builder for `Num`, otherwise the \
             absence above is an absence of output rather than of the defect:\n{code}",
        );
    }

    #[test]
    fn pre_scope_optional_pred_tape_builds_both_arms() {
        // Task #14 gate-1: the pre-scope tape builder must emit the
        // None/Some(Top) toggle for an `Option<BehavioralPred>` pre-scope
        // field (pre-#14 it emitted a bare `Top` — ill-typed), and keep
        // the bare `Top` for the mandatory shape (byte-identity with the
        // guarded_rho prop suite).
        let language = crate::gen::empty_language_for_tests();
        let opt_pred = FieldInfo {
            category: quote::format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: true,
            opaque_leaf: None,
        };
        let code =
            generate_binder_direct_build("Proc", "PFoo", &[opt_pred], "Proc", false, &language);
        assert!(
            code.contains(
                "let pred_0: Option<mettail_runtime::BehavioralPred> = \
                 if reader.next_byte() & 1 == 0 { None } else \
                 { Some(mettail_runtime::BehavioralPred::Top) };"
            ),
            "optional pre-scope pred must tape-toggle None/Some(Top): {code}",
        );

        let mandatory_pred = FieldInfo {
            category: quote::format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: false,
            opaque_leaf: None,
        };
        let code = generate_binder_direct_build(
            "Proc",
            "PFoo",
            &[mandatory_pred],
            "Proc",
            false,
            &language,
        );
        assert!(
            code.contains("let pred_0 = mettail_runtime::BehavioralPred::Top;"),
            "mandatory pre-scope pred keeps the bare Top emission: {code}",
        );
    }
}
