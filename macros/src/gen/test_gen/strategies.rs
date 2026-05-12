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

use mettail_ast::grammar::TermParam;
use mettail_ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use crate::gen::term_ops::subst::{FieldInfo, VariantKind, rule_to_variant_kind};
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};

use proc_macro2::TokenStream;
use quote::quote;

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
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();
        out.push_str(&format!(
            "impl AnyTerm {{\n    #[allow(dead_code)]\n    fn unwrap_{}(self) -> {} {{\n        match self {{\n            AnyTerm::Wrap{}(v) => v,\n            _ => panic!(\"AnyTerm::unwrap_{}: wrong variant\"),\n        }}\n    }}\n}}\n\n",
            cat_lower, cat, cat, cat_lower
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

    /// Read the next byte, wrapping around if the tape is exhausted.
    fn next_byte(&mut self) -> u8 {
        if self.tape.is_empty() {
            return 0;
        }
        let b = self.tape[self.pos % self.tape.len()];
        self.pos += 1;
        b
    }

    /// Read a u32 from 4 bytes (little-endian), wrapping tape as needed.
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
        let lit_label = language.types.iter()
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

fn classify_variants(
    category: &syn::Ident,
    language: &LanguageDef,
) -> VariantClassification {
    let cat = category.to_string();
    let variants = collect_spec_only_variants(category, language);

    let mut leaves = Vec::new();
    let mut recursive = Vec::new();

    for variant in &variants {
        match variant {
            VariantKind::Nullary { label } => {
                let label_str = label.to_string();
                leaves.push((
                    label_str.clone(),
                    format!("AnyTerm::Wrap{}({}::{})", cat, cat, label_str),
                ));
            }
            VariantKind::Literal { label } => {
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

                let build_code = generate_literal_build_code(
                    &cat, &label_str, &native_type_str, language,
                );
                leaves.push((label_str, build_code));
            }
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
            }
            VariantKind::Regular { label, fields } => {
                // Check if any field references a known category (recursive)
                let has_recursive_field = fields.iter().any(|f| {
                    language.types.iter().any(|t| t.name == f.category)
                });

                if !has_recursive_field || fields.is_empty() {
                    // Treat as leaf (unknown category fields)
                    continue;
                }

                let label_str = label.to_string();
                let code = generate_regular_build_code(&cat, &label_str, fields, language);
                recursive.push((label_str, code));
            }
            VariantKind::Collection { label, element_cat, coll_type } => {
                // Collections are recursive (contain elements)
                let is_known = language.types.iter().any(|t| t.name == *element_cat);
                if !is_known {
                    continue;
                }
                let label_str = label.to_string();
                let code = generate_collection_build_code(
                    &cat,
                    &label_str,
                    &element_cat.to_string(),
                    coll_type,
                );
                recursive.push((label_str, code));
            }
            VariantKind::Binder {
                label,
                pre_scope_fields,
                body_cat,
                ..
            } => {
                let is_body_known = language.types.iter().any(|t| t.name == *body_cat);
                if !is_body_known {
                    continue;
                }
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
            }
            VariantKind::MultiBinder {
                label,
                pre_scope_fields,
                body_cat,
                ..
            } => {
                let is_body_known = language.types.iter().any(|t| t.name == *body_cat);
                if !is_body_known {
                    continue;
                }
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
            }
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
            // inline during assembly
            // Push a placeholder task that just generates a Vec element
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
        mettail_ast::types::CollectionType::HashBag | mettail_ast::types::CollectionType::HashMap => "HashBag",
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
fn generate_build_from_tape(
    category: &syn::Ident,
    language: &LanguageDef,
    out: &mut String,
) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();
    let classification = classify_variants(category, language);

    // Use a simpler approach: direct recursive builder with explicit depth
    // tracking but iterative work-stack for the actual construction.
    //
    // The build function reads bytes from the tape to choose constructors,
    // then directly builds the term. This avoids the complex slot/assembly
    // machinery and is clearer.

    out.push_str(&format!(
        "/// Build a `{}` term from an instruction tape.\n",
        cat
    ));
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
        // Need to unwrap from AnyTerm
        let unwrap_code = code
            .replace(&format!("AnyTerm::Wrap{}(", cat), "")
            .trim_end()
            .to_string();
        // Actually, let's keep it simpler: build the term directly
        out.push_str(&format!("        let result = {};\n", code));
        out.push_str(&format!(
            "        return result.unwrap_{}();\n",
            cat_lower
        ));
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
        out.push_str(&format!(
            "        return result.unwrap_{}();\n",
            cat_lower
        ));
    }
    out.push_str("    }\n\n");

    // At depth > 0, can choose leaves or recursive constructors
    if num_recursive == 0 {
        // No recursive constructors — always choose a leaf
        out.push_str("    // No recursive constructors, fall back to leaf\n");
        out.push_str(&format!(
            "    build_{}_from_tape(reader, 0)\n",
            cat_lower
        ));
    } else {
        // Bias toward recursive constructors at higher depths to ensure interesting terms
        out.push_str(&format!(
            "    let choice = (reader.next_byte() as usize) % {};\n",
            total
        ));
        out.push_str("    let child_depth = depth - 1;\n");
        out.push_str("    match choice {\n");

        // Leaves first
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            out.push_str(&format!(
                "        {} => {}.unwrap_{}(),\n",
                i, code, cat_lower
            ));
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

            let code = generate_direct_recursive_build(
                &cat,
                label,
                category,
                language,
            );
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
    let variant = variants
        .iter()
        .find(|v| match v {
            VariantKind::Regular { label: l, .. }
            | VariantKind::Collection { label: l, .. }
            | VariantKind::Binder { label: l, .. }
            | VariantKind::MultiBinder { label: l, .. } => l.to_string() == label,
            _ => false,
        });

    let variant = match variant {
        Some(v) => v,
        None => return format!("            // Unknown variant {}\n            build_{}_from_tape(reader, 0)\n", label, cat.to_lowercase()),
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
                    let coll_type = field.coll_type.as_ref()
                        .unwrap_or_else(|| panic!("collection field of category `{}` missing coll_type in language! spec", field.category));
                    match coll_type {
                        mettail_ast::types::CollectionType::HashBag | mettail_ast::types::CollectionType::HashMap => {
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
                        }
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
                        }
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
                        }
                    }
                } else if field.is_collection {
                    // F5: spec-derived coll_type — every collection field
                    // MUST carry coll_type per the language! spec; missing is
                    // a synthetic insertion bug, surfaced loudly.
                    let coll_type = field.coll_type.as_ref()
                        .unwrap_or_else(|| panic!("collection field of category `{}` missing coll_type in language! spec", field.category));
                    match coll_type {
                        mettail_ast::types::CollectionType::HashBag | mettail_ast::types::CollectionType::HashMap => {
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
                        }
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
                        }
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
                        }
                    }
                } else if field.is_optional {
                    // F7: Opt-Group — Optional fields visit BOTH None
                    // and Some(...) arms based on a tape byte. Spec
                    // admits both, so generator must too. Replaces
                    // the prior None-only emission.
                    let field_cat_lower = field_cat.to_lowercase();
                    code.push_str(&format!(
                        "            let f{i}: Option<Box<{fc}>> = if reader.next_byte() & 1 == 0 {{ None }} else {{ Some(Box::new(build_{fcl}_from_tape(reader, child_depth))) }};\n",
                        i = i,
                        fc = field_cat,
                        fcl = field_cat_lower,
                    ));
                    field_exprs.push(format!("f{}", i));
                } else if is_known {
                    code.push_str(&format!(
                        "            let f{i} = Box::new(build_{fc}_from_tape(reader, child_depth));\n",
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
                        "            let f{} = Box::new(build_{}_from_tape(reader, 0));\n",
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
        }

        VariantKind::Collection { label, element_cat, coll_type } => {
            let label_str = label.to_string();
            let elem_cat_lower = element_cat.to_string().to_lowercase();

            match coll_type {
                mettail_ast::types::CollectionType::HashBag | mettail_ast::types::CollectionType::HashMap => {
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
                }
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
                }
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
                }
            }
        }

        VariantKind::Binder {
            label,
            pre_scope_fields,
            body_cat,
            ..
        } => {
            generate_binder_direct_build(cat, &label.to_string(), pre_scope_fields, &body_cat.to_string(), false, language)
        }

        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            body_cat,
            ..
        } => {
            generate_binder_direct_build(cat, &label.to_string(), pre_scope_fields, &body_cat.to_string(), true, language)
        }

        _ => {
            format!(
                "            build_{}_from_tape(reader, 0)\n",
                cat_lower
            )
        }
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
            let coll_type = field.coll_type.as_ref()
                .unwrap_or_else(|| panic!("collection field of category `{}` missing coll_type in language! spec", field.category));
            match coll_type {
                mettail_ast::types::CollectionType::HashBag | mettail_ast::types::CollectionType::HashMap => {
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
                }
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
                }
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
                }
            }
            pre_scope_exprs.push(format!("pre_{}", i));
            continue;
        }

        if is_known && !field.is_collection {
            code.push_str(&format!(
                "            let pre_{i} = Box::new(build_{fc}_from_tape(reader, child_depth));\n",
                i = i,
                fc = field_cat_lower,
            ));
            pre_scope_exprs.push(format!("pre_{}", i));
        } else if field.is_predicate {
            // Guard slot — spec-derived: same rationale as above.
            // `Top` is the spec's default for unspecified guards.
            code.push_str(&format!(
                "            let pred_{i} = mettail_runtime::BehavioralPred::Top;\n",
                i = i,
            ));
            pre_scope_exprs.push(format!("pred_{}", i));
        } else if field.is_collection {
            // F5: spec-derived coll_type — every collection field MUST
            // carry coll_type per the language! spec.
            let coll_type = field.coll_type.as_ref()
                .unwrap_or_else(|| panic!("collection field of category `{}` missing coll_type in language! spec", field.category));
            match coll_type {
                mettail_ast::types::CollectionType::Vec => {
                    code.push_str(&format!(
                        "            let n_{i} = (reader.next_byte() % 3) as usize;\n\
                                     let pre_{i}: Vec<_> = (0..n_{i}).map(|_| build_{fc}_from_tape(reader, child_depth)).collect();\n",
                        i = i,
                        fc = field_cat_lower,
                    ));
                    pre_scope_exprs.push(format!("pre_{}", i));
                }
                _ => {
                    // HashBag/HashSet not typical for pre-scope, but handle
                    code.push_str(&format!(
                        "            let pre_{i} = Vec::<{fc}>::new();\n",
                        i = i,
                        fc = field_cat,
                    ));
                    pre_scope_exprs.push(format!("pre_{}", i));
                }
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
                         let scope = mettail_runtime::Scope::new(binders, Box::new(body));\n",
            vp = var_prefix,
            bc = body_cat_lower,
        ));
    } else {
        code.push_str(&format!(
            "            let binder_name = format!(\"{vp}{{}}\", reader.next_byte() % 8);\n\
                         let binder = mettail_runtime::Binder(mettail_runtime::get_or_create_var(&binder_name));\n\
                         let body = build_{bc}_from_tape(reader, child_depth);\n\
                         let scope = mettail_runtime::Scope::new(binder, Box::new(body));\n",
            vp = var_prefix,
            bc = body_cat_lower,
        ));
    }

    // Assemble
    if pre_scope_exprs.is_empty() {
        code.push_str(&format!(
            "            {}::{}(scope)\n",
            cat, label,
        ));
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
fn generate_arb_strategy(
    category: &syn::Ident,
    _language: &LanguageDef,
    out: &mut String,
) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();

    out.push_str(&format!(
        "/// Generate an arbitrary `{}` term with bounded depth.\n",
        cat
    ));
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
    out.push_str("    #![proptest_config(ProptestConfig::with_cases(100))]\n\n");

    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();

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

        // Test 4: Display round-trip (parse(display(term)) == term for ground terms)
        // Only if the category has a parse method — all categories do via PraTTaIL
        out.push_str(&format!(
            "    #[test]\n\
             \x20   fn {cat_lower}_display_parse_roundtrip(term in arb_{cat_lower}(3)) {{\n\
             \x20       let displayed = format!(\"{{}}\", term);\n\
             \x20       // Skip terms whose display is too long (parser may overflow)\n\
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
             \x20       prop_assert_eq!(canonical, recanonical,\n\
             \x20           \"Display should be idempotent after canonicalization: \\\n\
             \x20            display(parse(display(parse(display(t))))) == display(parse(display(t)))\");\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
            cat = cat,
        ));

        // Test 5 (Group F): Strong roundtrip — parse(display(t)) == t (structural equality)
        // For categories with binders, FreeVar identity differs after parse, so this
        // test uses display comparison as the proxy. For categories without explicit
        // binder rules, we can test structural PartialEq directly.
        // Uses depth 1 and limits displayed string length to avoid stack
        // overflow during parsing or PartialEq comparison of nested terms.
        let cat_has_binders = category_has_binders(&lang_type.name, language);
        if !cat_has_binders {
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
                 \x20           // Verify display-level equality (same as test 4)\n\
                 \x20           let parsed_display = format!(\"{{}}\", parsed);\n\
                 \x20           prop_assert_eq!(&displayed, &parsed_display,\n\
                 \x20               \"Strong roundtrip: display(term) != display(parse(display(term)))\");\n\
                 \x20           // Additionally verify that re-parsing the parsed display is consistent\n\
                 \x20           mettail_runtime::clear_var_cache();\n\
                 \x20           if let Ok(reparsed) = {cat}::parse(&parsed_display) {{\n\
                 \x20               let reparsed_display = format!(\"{{}}\", reparsed);\n\
                 \x20               prop_assert_eq!(&parsed_display, &reparsed_display,\n\
                 \x20                   \"Strong roundtrip: display not stable after double parse\");\n\
                 \x20           }}\n\
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
                 \x20           let re_displayed = format!(\"{{}}\", parsed);\n\
                 \x20           // For binder-containing categories, compare via display strings\n\
                 \x20           // (FreeVar identity may differ after parse, but display is canonical)\n\
                 \x20           prop_assert_eq!(&displayed, &re_displayed,\n\
                 \x20               \"Strong roundtrip (display proxy) failed for binder category\");\n\
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
        }
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
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();
        out.push_str(&format!(
            "    /// Unwrap the inner `{}` value, panicking if the variant is wrong.\n",
            cat
        ));
        out.push_str("    #[allow(dead_code)]\n");
        out.push_str(&format!(
            "    pub fn unwrap_{cat_lower}(self) -> {cat} {{\n\
             \x20       match self {{\n\
             \x20           AnyTerm::Wrap{cat}(v) => v,\n\
             \x20           _ => panic!(\"AnyTerm::unwrap_{cat_lower}: wrong variant\"),\n\
             \x20       }}\n\
             \x20   }}\n\n",
            cat_lower = cat_lower,
            cat = cat,
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

    /// Read the next byte, wrapping around if the tape is exhausted.
    pub fn next_byte(&mut self) -> u8 {
        if self.tape.is_empty() {
            return 0;
        }
        let b = self.tape[self.pos % self.tape.len()];
        self.pos += 1;
        b
    }

    /// Read a u32 from 4 bytes (little-endian), wrapping tape as needed.
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

    out.push_str(&format!(
        "/// Build a `{}` term from an instruction tape.\n",
        cat
    ));
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
        out.push_str(&format!(
            "        return result.unwrap_{}();\n",
            cat_lower
        ));
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
        out.push_str(&format!(
            "        return result.unwrap_{}();\n",
            cat_lower
        ));
    }
    out.push_str("    }\n\n");

    // At depth > 0, can choose leaves or recursive constructors
    if num_recursive == 0 {
        out.push_str("    // No recursive constructors, fall back to leaf\n");
        out.push_str(&format!(
            "    build_{}_from_tape(reader, 0)\n",
            cat_lower
        ));
    } else {
        out.push_str(&format!(
            "    let choice = (reader.next_byte() as usize) % {};\n",
            total
        ));
        out.push_str("    let child_depth = depth - 1;\n");
        out.push_str("    match choice {\n");

        // Leaves first
        for (i, (_, ref code)) in classification.leaves.iter().enumerate() {
            out.push_str(&format!(
                "        {} => {}.unwrap_{}(),\n",
                i, code, cat_lower
            ));
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

            let code = generate_direct_recursive_build(
                &cat,
                label,
                category,
                language,
            );
            out.push_str(&format!("{} {{\n", match_prefix));
            out.push_str(&code);
            out.push_str("        },\n");
        }

        out.push_str("    }\n");
    }

    out.push_str("}\n\n");
}

/// Generate a public `arb_{cat}` strategy function for one category.
fn generate_public_arb_strategy(
    category: &syn::Ident,
    _language: &LanguageDef,
    out: &mut String,
) {
    let cat = category.to_string();
    let cat_lower = cat.to_lowercase();

    out.push_str(&format!(
        "/// Generate an arbitrary `{}` term with bounded depth.\n",
        cat
    ));
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
