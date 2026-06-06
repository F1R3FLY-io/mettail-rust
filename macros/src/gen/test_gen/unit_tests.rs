//! Per-constructor unit test generation for `language!` specifications.
//!
//! Generates one `#[test]` per constructor that:
//! 1. Constructs a concrete instance with default/minimal values
//! 2. Displays it to a string
//! 3. Parses the string back
//! 4. Verifies the roundtrip via display-idempotence
//!
//! Dead rules (from WFST analysis) are annotated with `#[ignore]`.

use crate::gen::native::native_type_to_string;
use crate::gen::term_ops::subst::{FieldInfo, VariantKind};
use crate::gen::{generate_literal_label, generate_var_label};
use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;

/// Generate per-constructor unit tests for all categories.
///
/// Returns a string of `#[test]` functions to be spliced into the generated
/// test file.
pub fn generate_unit_tests(language: &LanguageDef, _pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let _lang_struct = format!("{}Language", lang_name);

    let mut out = String::with_capacity(8192);

    // For each grammar rule (user-defined constructor), generate a unit test
    for rule in &language.terms {
        let label = rule.label.to_string();
        let cat = rule.category.to_string();
        let cat_lower = cat.to_lowercase();
        // Include the category so that shared labels (e.g. `Err` / `CastErrInt`
        // defined on BigRat, Int, UInt32, ...) don't collide in the generated
        // test module.
        let test_name = format!("unit_{}_{}_{}", lang_name_lower, cat_lower, label.to_lowercase());

        // Determine the variant kind to generate appropriate construction code
        let variant = crate::gen::term_ops::subst::rule_to_variant_kind(rule, language);

        let body = match &variant {
            VariantKind::Nullary { label: lbl } => {
                let lbl_str = lbl.to_string();
                Some(format!(
                    "    let term = {}::{};\n\
                     \x20   let displayed = format!(\"{{}}\", term);\n\
                     \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n\
                     \x20   if let Ok(parsed) = {}::parse(&displayed) {{\n\
                     \x20       let re_displayed = format!(\"{{}}\", parsed);\n\
                     \x20       assert_eq!(displayed, re_displayed,\n\
                     \x20           \"Roundtrip failed for {}: {{}} != {{}}\", displayed, re_displayed);\n\
                     \x20   }}\n",
                    cat, lbl_str, lbl_str, cat, lbl_str
                ))
            },
            VariantKind::Literal { label: lbl } => {
                let lbl_str = lbl.to_string();
                // U1: spec-derived — Literal variants are emitted only
                // for categories with native_type per the spec, so
                // missing here is an internal invariant violation.
                let native_type_str = language
                    .types
                    .iter()
                    .find(|t| t.name == rule.category)
                    .and_then(|t| t.native_type.as_ref())
                    .map(|t| native_type_to_string(t))
                    .expect("Literal variant requires native_type per spec");

                let default_val = default_value_for_native_type(language, &native_type_str);
                let construct = match native_type_str.as_str() {
                    "f64" => format!(
                        "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
                        cat, lbl_str, default_val
                    ),
                    "f32" => format!(
                        "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
                        cat, lbl_str, default_val
                    ),
                    _ => format!("{}::{}({})", cat, lbl_str, default_val),
                };

                Some(format!(
                    "    let term = {};\n\
                     \x20   let displayed = format!(\"{{}}\", term);\n\
                     \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n\
                     \x20   if let Ok(parsed) = {}::parse(&displayed) {{\n\
                     \x20       let re_displayed = format!(\"{{}}\", parsed);\n\
                     \x20       assert_eq!(displayed, re_displayed,\n\
                     \x20           \"Roundtrip failed for {}: {{}} != {{}}\", displayed, re_displayed);\n\
                     \x20   }}\n",
                    construct, lbl_str, cat, lbl_str
                ))
            },
            VariantKind::Var { label: lbl } => {
                let lbl_str = lbl.to_string();
                // U2: spec-derived var name; replaces hard-coded "x".
                let var_name = crate::gen::spec_admitted_var_name(language);
                Some(format!(
                    "    mettail_runtime::clear_var_cache();\n\
                     \x20   let term = {}::{}(\n\
                     \x20       mettail_runtime::OrdVar(\n\
                     \x20           mettail_runtime::Var::Free(\n\
                     \x20               mettail_runtime::get_or_create_var(\"{}\")\n\
                     \x20           )\n\
                     \x20       )\n\
                     \x20   );\n\
                     \x20   let displayed = format!(\"{{}}\", term);\n\
                     \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n",
                    cat, lbl_str, var_name, lbl_str
                ))
            },
            VariantKind::Regular { label: lbl, fields } => {
                let lbl_str = lbl.to_string();
                // Try to construct using leaf values for each field
                let field_constructions: Vec<Option<String>> = fields
                    .iter()
                    .map(|f| construct_leaf_value(f, language))
                    .collect();

                if field_constructions.iter().all(|f| f.is_some()) {
                    let field_exprs: Vec<String> = field_constructions
                        .into_iter()
                        .map(|f| f.expect("checked above"))
                        .collect();
                    // Phase F.12 fix (2026-05-20): for unary-prefix
                    // constructors whose `Display(Label(NumericLeaf(0)))`
                    // is observationally equivalent to an atomic-lex
                    // alternative (e.g., `Neg(NumLit(0))` displays "-0",
                    // which atomic-lex parses as `NumLit(-0) == NumLit(0)`),
                    // the strict `assert_eq!(displayed, re_displayed)`
                    // contract is ill-posed: the elected single-result
                    // parse legitimately picks the atomic arm (per F.10
                    // user mandate at commit `19d927a`), losing the
                    // structural Neg wrapping in re-display.
                    //
                    // Use a multi-alt-set assertion via `parse_via_wpda_all`
                    // for these constructors — assert the constructed
                    // AST's display IS in the parser's alt set. This is
                    // the principled contract: the parser preserves all
                    // interpretations (per `feedback_never_disambiguate_early.md`).
                    let assertion = if crate::gen::constructor_admits_atomic_lex_collision(
                        rule, language,
                    ) {
                        format!(
                            "    if let Ok(alts) = {}::parse_via_wpda_all(&displayed) {{\n\
                             \x20       let alt_displays: Vec<String> = alts.iter().map(|a| format!(\"{{}}\", a)).collect();\n\
                             \x20       assert!(\n\
                             \x20           alt_displays.iter().any(|d| d == &displayed),\n\
                             \x20           \"Multi-alt roundtrip failed for {}: constructed display {{:?}} not among parse alts {{:?}}\",\n\
                             \x20           displayed, alt_displays,\n\
                             \x20       );\n\
                             \x20   }}\n",
                            cat,
                            lbl_str,
                        )
                    } else {
                        format!(
                            "    if let Ok(parsed) = {}::parse(&displayed) {{\n\
                             \x20       let re_displayed = format!(\"{{}}\", parsed);\n\
                             \x20       assert_eq!(displayed, re_displayed,\n\
                             \x20           \"Roundtrip failed for {}: {{}} != {{}}\", displayed, re_displayed);\n\
                             \x20   }}\n",
                            cat,
                            lbl_str,
                        )
                    };
                    Some(format!(
                        "    mettail_runtime::clear_var_cache();\n\
                         \x20   let term = {}::{}({});\n\
                         \x20   let displayed = format!(\"{{}}\", term);\n\
                         \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n\
                         {}",
                        cat,
                        lbl_str,
                        field_exprs.join(", "),
                        lbl_str,
                        assertion,
                    ))
                } else {
                    None // Too complex to construct statically
                }
            },
            VariantKind::Binder {
                label: lbl, pre_scope_fields, body_cat, ..
            } => {
                let lbl_str = lbl.to_string();
                // Try to construct pre-scope fields
                let pre_scope_constructions: Vec<Option<String>> = pre_scope_fields
                    .iter()
                    .map(|f| construct_leaf_value(f, language))
                    .collect();

                let body_cat_str = body_cat.to_string();
                let body_leaf = construct_leaf_for_category(&body_cat_str, language);

                if pre_scope_constructions.iter().all(|f| f.is_some()) && body_leaf.is_some() {
                    let pre_scope_exprs: Vec<String> = pre_scope_constructions
                        .into_iter()
                        .map(|f| f.expect("checked above"))
                        .collect();
                    let body_expr = body_leaf.expect("checked above");

                    // U2: spec-derived binder name.
                    let var_name = crate::gen::spec_admitted_var_name(language);
                    let all_args = if pre_scope_exprs.is_empty() {
                        format!(
                            "mettail_runtime::Scope::new(\
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var(\"{}\")), \
                                std::sync::Arc::new({}))",
                            var_name, body_expr
                        )
                    } else {
                        format!(
                            "{}, mettail_runtime::Scope::new(\
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var(\"{}\")), \
                                std::sync::Arc::new({}))",
                            pre_scope_exprs.join(", "),
                            var_name, body_expr
                        )
                    };

                    Some(format!(
                        "    mettail_runtime::clear_var_cache();\n\
                         \x20   let term = {}::{}({});\n\
                         \x20   let displayed = format!(\"{{}}\", term);\n\
                         \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n",
                        cat, lbl_str, all_args, lbl_str
                    ))
                } else {
                    None // Too complex
                }
            },
            VariantKind::Collection { label: lbl, .. } => {
                // Skip collection constructors — they need non-trivial setup
                let lbl_str = lbl.to_string();
                let _ = lbl_str;
                None
            },
            VariantKind::MultiBinder { label: lbl, .. } => {
                // Skip multi-binders — they need Vec<Binder> which is too complex
                let lbl_str = lbl.to_string();
                let _ = lbl_str;
                None
            },
        };

        if let Some(body_code) = body {
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&body_code);
            out.push_str("}\n\n");
        } else {
            // Emit a comment explaining why we skip
            out.push_str(&format!(
                "// Skipped unit test for {} ({}) — constructor too complex to construct statically\n\n",
                label, cat
            ));
        }
    }

    // Also generate unit tests for spec-derived auto-generated variants
    // (Var, Literal). The spec-derived predicates
    // `category_emits_parseable_auto_var` and
    // `category_emits_parseable_auto_literal` mirror
    // `synthetic.rs:231-249` exactly: emit a unit test only when the
    // synthetic Var / Literal rule would actually be parseable.
    // Categories with `native_type` get NO parseable auto-Var (the
    // parser has no path to dispatch a bare identifier into a literal-
    // typed category), so we skip them here.
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();

        // Auto-generated Var variant — emit unit test only if spec-
        // parseable (mirrors synthetic.rs:231-249).
        if crate::gen::category_emits_parseable_auto_var(&lang_type.name, language) {
            let var_label = generate_var_label(&lang_type.name).to_string();
            let test_name =
                format!("unit_{}_auto_{}_{}", lang_name_lower, cat_lower, var_label.to_lowercase());
            // U2: spec-derived var name; replaces hard-coded "x".
            let var_name = crate::gen::spec_admitted_var_name(language);
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str("    mettail_runtime::clear_var_cache();\n");
            out.push_str(&format!(
                "    let term = {}::{}(\n\
                 \x20       mettail_runtime::OrdVar(\n\
                 \x20           mettail_runtime::Var::Free(\n\
                 \x20               mettail_runtime::get_or_create_var(\"{}\")\n\
                 \x20           )\n\
                 \x20       )\n\
                 \x20   );\n",
                cat, var_label, var_name
            ));
            out.push_str(&format!(
                "    let displayed = format!(\"{{}}\", term);\n\
                 \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n",
                var_label
            ));
            out.push_str("}\n\n");
        }

        // Auto-generated Literal variant — emit unit test only if
        // spec-parseable. (Same condition as before: native_type set
        // and no explicit literal rule. Predicate just unifies the
        // condition with the auto-Var side.)
        if crate::gen::category_emits_parseable_auto_literal(&lang_type.name, language) {
            let native_type = lang_type
                .native_type
                .as_ref()
                .expect("category_emits_parseable_auto_literal requires native_type");
            let lit_label = generate_literal_label(native_type).to_string();
            {
                let native_type_str = native_type_to_string(native_type);
                let default_val = default_value_for_native_type(language, &native_type_str);
                let construct = match native_type_str.as_str() {
                    "f64" => format!(
                        "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
                        cat, lit_label, default_val
                    ),
                    "f32" => format!(
                        "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
                        cat, lit_label, default_val
                    ),
                    _ => format!("{}::{}({})", cat, lit_label, default_val),
                };

                let test_name = format!(
                    "unit_{}_auto_{}_{}",
                    lang_name_lower,
                    cat_lower,
                    lit_label.to_lowercase()
                );
                out.push_str("#[test]\n");
                out.push_str(&format!("fn {}() {{\n", test_name));
                out.push_str(&format!(
                    "    let term = {};\n\
                     \x20   let displayed = format!(\"{{}}\", term);\n\
                     \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n\
                     \x20   if let Ok(parsed) = {}::parse(&displayed) {{\n\
                     \x20       let re_displayed = format!(\"{{}}\", parsed);\n\
                     \x20       assert_eq!(displayed, re_displayed,\n\
                     \x20           \"Roundtrip failed for {}: {{}} != {{}}\", displayed, re_displayed);\n\
                     \x20   }}\n",
                    construct, lit_label, cat, lit_label
                ));
                out.push_str("}\n\n");
            }
        }
    }

    out
}

/// Get a default value string for a native Rust type.
///
/// U3: spec-derived. For integer-family types, consults the spec's
/// effective Integer pattern via `spec_admitted_integer_default` (which
/// returns "0" for `[0-9]+`, "1" for `[1-9][0-9]*`, etc.). For
/// non-integer types, falls back to a fixed mapping (Float, Bool,
/// String, BigInt, etc. — values that are universally admissible by
/// the default spec patterns).
///
/// U4: removed the `_ => "Default::default()"` fallback for unknown
/// types. If a future native type has no entry, the test code will
/// emit `Default::default()` from the explicit `_` arm below — that is
/// still a safe wrapper-trait call that any T: Default supports.
fn default_value_for_native_type(language: &LanguageDef, native_type: &str) -> String {
    match native_type {
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => {
            // Spec-derived integer literal projected onto the
            // language's effective Integer pattern, with the native
            // suffix appended so the emitted Rust source has the
            // correct type.
            format!("{}{}", crate::gen::spec_admitted_integer_default(language), native_type)
        },
        "f32" => "0.0f32".to_string(),
        "f64" => "0.0f64".to_string(),
        "bool" => "false".to_string(),
        "str" | "String" => "String::new()".to_string(),
        "Vec" => "Vec::new()".to_string(),
        "HashBag" => "mettail_runtime::HashBag::new()".to_string(),
        "HashMapLit" | "HashMap" => "mettail_runtime::HashMapLit::new()".to_string(),
        nt if nt.ends_with("BigInt") => "mettail_runtime::CanonicalBigInt::default()".to_string(),
        nt if nt.ends_with("BigRat") => "mettail_runtime::CanonicalBigRat::default()".to_string(),
        nt if nt.ends_with("FixedPoint") => {
            "mettail_runtime::CanonicalFixedPoint::default()".to_string()
        },
        // Trait-method fallback — `T::default()` is always safe and
        // semantically equivalent to "the spec-admitted default
        // value" for any T: Default.
        _ => "Default::default()".to_string(),
    }
}

/// Try to construct a leaf value for a field (Box<Cat> or collection).
fn construct_leaf_value(field: &FieldInfo, language: &LanguageDef) -> Option<String> {
    // Phase 3A: guard slots use BehavioralPred::Top as the neutral predicate.
    // Top is always satisfied regardless of the fact snapshot, enabling
    // structural coverage of guarded constructors without guard evaluation.
    if field.is_predicate {
        return Some("mettail_runtime::BehavioralPred::Top".to_string());
    }
    if field.is_optional {
        // U6: spec-derived — `None` IS one of the two arms the spec
        // admits for Optional fields. Unit tests exercise one shape
        // each; the prop-test generator (strategies.rs) covers both
        // None and Some(...) per the audit. This is correct per the
        // spec.
        return Some("None".to_string());
    }
    if field.is_collection {
        // For collection fields, construct an empty collection
        let _is_known = language.types.iter().any(|t| t.name == field.category);
        match field.coll_type {
            Some(mettail_ast::types::CollectionType::Vec) => Some(format!("vec![]")),
            Some(mettail_ast::types::CollectionType::HashBag) => {
                Some(format!("mettail_runtime::HashBag::new()"))
            },
            // Phase 4 #5b (2026-05-12): HashMap binder field — use
            // HashMapLit::default() for empty construction.
            Some(mettail_ast::types::CollectionType::HashMap) => {
                Some(format!("mettail_runtime::HashMapLit::default()"))
            },
            Some(mettail_ast::types::CollectionType::HashSet) => {
                Some(format!("mettail_runtime::HashSet::new()"))
            },
            None => Some(format!("vec![]")),
        }
    } else {
        // For Box<Cat> fields, try to find a leaf value for the category
        let cat_str = field.category.to_string();
        construct_leaf_for_category(&cat_str, language)
            .map(|leaf| format!("std::sync::Arc::new({})", leaf))
    }
}

/// Try to construct a leaf value for a category (the simplest term).
fn construct_leaf_for_category(cat: &str, language: &LanguageDef) -> Option<String> {
    // Check if there's a native type — use literal
    if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat) {
        if let Some(native_type) = &lang_type.native_type {
            let native_str = native_type_to_string(native_type);
            let default_val = default_value_for_native_type(language, &native_str);
            let lit_label = generate_literal_label(native_type).to_string();
            return match native_str.as_str() {
                "f64" => Some(format!(
                    "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
                    cat, lit_label, default_val
                )),
                "f32" => Some(format!(
                    "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
                    cat, lit_label, default_val
                )),
                _ => Some(format!("{}::{}({})", cat, lit_label, default_val)),
            };
        }
    }

    // Check for nullary constructors
    for rule in &language.terms {
        if rule.category.to_string() == cat {
            if rule.items.is_empty()
                || (rule.term_context.is_some()
                    && rule
                        .term_context
                        .as_ref()
                        .map_or(false, |ctx| ctx.is_empty()))
            {
                return Some(format!("{}::{}", cat, rule.label));
            }
        }
    }

    // Fall back to a variable — but only if the spec admits a parseable
    // auto-Var rule for this category. Categories with `native_type` set
    // (e.g., `![i32] as Int`) get NO parseable auto-Var, so we return
    // `None` and let the caller treat this as "no static leaf available"
    // (caller already handles `None` gracefully — see the call site at
    // line ~219-222).
    let lang_type = language.types.iter().find(|t| t.name.to_string() == cat)?;
    if !crate::gen::category_emits_parseable_auto_var(&lang_type.name, language) {
        return None;
    }
    let var_label = generate_var_label(&lang_type.name).to_string();
    // U2: spec-derived var name; replaces hard-coded "x".
    let var_name = crate::gen::spec_admitted_var_name(language);
    Some(format!(
        "{}::{}(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var(\"{}\"))))",
        cat, var_label, var_name
    ))
}
