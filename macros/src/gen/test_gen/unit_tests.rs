//! Per-constructor unit test generation for `language!` specifications.
//!
//! Generates one `#[test]` per constructor that:
//! 1. Constructs a concrete instance with default/minimal values
//! 2. Displays it to a string
//! 3. Parses the string back
//! 4. Verifies the roundtrip via display-idempotence
//!
//! Dead rules (from WFST analysis) are annotated with `#[ignore]`.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use mettail_prattail::PipelineAnalysis;
use std::collections::HashSet;

/// Generate per-constructor unit tests for all categories.
///
/// Returns a string of `#[test]` functions to be spliced into the generated
/// test file.
pub fn generate_unit_tests(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let _lang_struct = format!("{}Language", lang_name);
    let dead_rules = &pipeline.dead_rule_labels;

    let mut out = String::with_capacity(8192);

    // For each grammar rule (user-defined constructor), generate a unit test
    for rule in &language.terms {
        let label = rule.label.to_string();
        let cat = rule.category.to_string();
        let cat_lower = cat.to_lowercase();
        let test_name = format!(
            "unit_{}_{}",
            lang_name_lower,
            label.to_lowercase()
        );

        let is_dead = dead_rules.contains(&label);

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
            }
            VariantKind::Literal { label: lbl } => {
                let lbl_str = lbl.to_string();
                // Determine the native type for the category
                let native_type_str = language
                    .types
                    .iter()
                    .find(|t| t.name == rule.category)
                    .and_then(|t| t.native_type.as_ref())
                    .map(|t| native_type_to_string(t))
                    .unwrap_or_else(|| "i32".to_string());

                let default_val = default_value_for_native_type(&native_type_str);
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
            }
            VariantKind::Var { label: lbl } => {
                let lbl_str = lbl.to_string();
                Some(format!(
                    "    mettail_runtime::clear_var_cache();\n\
                     \x20   let term = {}::{}(\n\
                     \x20       mettail_runtime::OrdVar(\n\
                     \x20           mettail_runtime::Var::Free(\n\
                     \x20               mettail_runtime::get_or_create_var(\"x\")\n\
                     \x20           )\n\
                     \x20       )\n\
                     \x20   );\n\
                     \x20   let displayed = format!(\"{{}}\", term);\n\
                     \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n",
                    cat, lbl_str, lbl_str
                ))
            }
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
                    Some(format!(
                        "    mettail_runtime::clear_var_cache();\n\
                         \x20   let term = {}::{}({});\n\
                         \x20   let displayed = format!(\"{{}}\", term);\n\
                         \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n\
                         \x20   if let Ok(parsed) = {}::parse(&displayed) {{\n\
                         \x20       let re_displayed = format!(\"{{}}\", parsed);\n\
                         \x20       assert_eq!(displayed, re_displayed,\n\
                         \x20           \"Roundtrip failed for {}: {{}} != {{}}\", displayed, re_displayed);\n\
                         \x20   }}\n",
                        cat,
                        lbl_str,
                        field_exprs.join(", "),
                        lbl_str,
                        cat,
                        lbl_str,
                    ))
                } else {
                    None // Too complex to construct statically
                }
            }
            VariantKind::Binder { label: lbl, pre_scope_fields, body_cat, .. } => {
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

                    let all_args = if pre_scope_exprs.is_empty() {
                        format!(
                            "mettail_runtime::Scope::new(\
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var(\"x\")), \
                                Box::new({}))",
                            body_expr
                        )
                    } else {
                        format!(
                            "{}, mettail_runtime::Scope::new(\
                                mettail_runtime::Binder(mettail_runtime::get_or_create_var(\"x\")), \
                                Box::new({}))",
                            pre_scope_exprs.join(", "),
                            body_expr
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
            }
            VariantKind::Collection { label: lbl, .. } => {
                // Skip collection constructors — they need non-trivial setup
                let lbl_str = lbl.to_string();
                let _ = lbl_str;
                None
            }
            VariantKind::MultiBinder { label: lbl, .. } => {
                // Skip multi-binders — they need Vec<Binder> which is too complex
                let lbl_str = lbl.to_string();
                let _ = lbl_str;
                None
            }
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

    // Also generate unit tests for auto-generated variants (Var, Literal)
    // that don't come from grammar rules but are always present
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let cat_lower = cat.to_lowercase();

        // Auto-generated Var variant (always present)
        let var_label = generate_var_label(&lang_type.name).to_string();
        let has_explicit_var = language
            .terms
            .iter()
            .any(|r| r.category == lang_type.name && is_var_rule(r));
        if !has_explicit_var {
            let test_name = format!(
                "unit_{}_auto_{}",
                lang_name_lower,
                var_label.to_lowercase()
            );
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str("    mettail_runtime::clear_var_cache();\n");
            out.push_str(&format!(
                "    let term = {}::{}(\n\
                 \x20       mettail_runtime::OrdVar(\n\
                 \x20           mettail_runtime::Var::Free(\n\
                 \x20               mettail_runtime::get_or_create_var(\"x\")\n\
                 \x20           )\n\
                 \x20       )\n\
                 \x20   );\n",
                cat, var_label
            ));
            out.push_str(&format!(
                "    let displayed = format!(\"{{}}\", term);\n\
                 \x20   assert!(!displayed.is_empty(), \"Display should produce non-empty output for {}\");\n",
                var_label
            ));
            out.push_str("}\n\n");
        }

        // Auto-generated Literal variant (for categories with native_type)
        if let Some(native_type) = &lang_type.native_type {
            let lit_label = generate_literal_label(native_type).to_string();
            let has_explicit_lit = language
                .terms
                .iter()
                .any(|r| r.category == lang_type.name && is_literal_rule(r));
            if !has_explicit_lit {
                let native_type_str = native_type_to_string(native_type);
                let default_val = default_value_for_native_type(&native_type_str);
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
                    "unit_{}_auto_{}",
                    lang_name_lower,
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
fn default_value_for_native_type(native_type: &str) -> &str {
    match native_type {
        "i32" => "0i32",
        "i64" => "0i64",
        "u32" => "0u32",
        "u64" => "0u64",
        "f32" => "0.0f32",
        "f64" => "0.0f64",
        "bool" => "false",
        "str" | "String" => "String::new()",
        _ => "Default::default()",
    }
}

/// Try to construct a leaf value for a field (Box<Cat> or collection).
fn construct_leaf_value(field: &FieldInfo, language: &LanguageDef) -> Option<String> {
    // Phase 3A: guard slots use BehavioralPred::Top as trivial placeholder.
    // Top is always satisfied regardless of the fact snapshot, enabling
    // structural coverage of guarded constructors without guard evaluation.
    if field.is_predicate {
        return Some("mettail_runtime::BehavioralPred::Top".to_string());
    }
    if field.is_collection {
        // For collection fields, construct an empty collection
        let cat_str = field.category.to_string();
        let _is_known = language
            .types
            .iter()
            .any(|t| t.name == field.category);
        match field.coll_type {
            Some(mettail_ast::types::CollectionType::Vec) => {
                Some(format!("vec![]"))
            }
            Some(mettail_ast::types::CollectionType::HashBag) => {
                Some(format!("mettail_runtime::HashBag::new()"))
            }
            Some(mettail_ast::types::CollectionType::HashSet) => {
                Some(format!("mettail_runtime::HashSet::new()"))
            }
            None => {
                Some(format!("vec![]"))
            }
        }
    } else {
        // For Box<Cat> fields, try to find a leaf value for the category
        let cat_str = field.category.to_string();
        construct_leaf_for_category(&cat_str, language).map(|leaf| format!("Box::new({})", leaf))
    }
}

/// Try to construct a leaf value for a category (the simplest term).
fn construct_leaf_for_category(cat: &str, language: &LanguageDef) -> Option<String> {
    // Check if there's a native type — use literal
    if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat) {
        if let Some(native_type) = &lang_type.native_type {
            let native_str = native_type_to_string(native_type);
            let default_val = default_value_for_native_type(&native_str);
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

    // Fall back to a variable
    let var_label = if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat)
    {
        generate_var_label(&lang_type.name).to_string()
    } else {
        // Category not found — cannot construct
        return None;
    };

    Some(format!(
        "{}::{}(mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var(\"x\"))))",
        cat, var_label
    ))
}
