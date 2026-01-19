//! Ascent relation declarations
//!
//! Generates relation declarations for categories, equality, rewrites,
//! and collection projections.

use crate::ast::theory::{TheoryDef, Condition, RewriteRule};
use crate::ast::grammar::TermParam;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Generate all relation declarations for a theory
pub fn generate_relations(theory: &TheoryDef) -> TokenStream {
    let mut relations = Vec::new();

    // Category exploration relations (unadorned)
    for export in &theory.exports {
        let cat = &export.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            relation #cat_lower(#cat);
        });
    }

    // Equality relations (per-category, typed)
    for export in &theory.exports {
        let cat = &export.name;
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            #[ds(crate::eqrel)]
            relation #eq_rel(#cat, #cat);
        });
    }

    // Rewrite relations (per-category, typed)
    for export in &theory.exports {
        let cat = &export.name;
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            relation #rw_rel(#cat, #cat);
        });
    }

    // Collection projection relations (automatic)
    // For each constructor with a collection field, generate a "contains" relation
    // Example: PPar(HashBag<Proc>) generates: relation ppar_contains(Proc, Proc);
    let projection_relations = generate_collection_projection_relations(theory);
    relations.extend(projection_relations);

    // Environment relations (for EnvQuery conditions)
    let env_relations = generate_env_relations(theory);
    relations.extend(env_relations);

    quote! {
        #(#relations)*
    }
}

/// Generate collection projection relations
///
/// For each constructor with a collection field, automatically generate a "contains" relation
/// that relates the parent term to each element in the collection.
///
/// Example: For PPar(HashBag<Proc>), generates:
/// ```text
/// relation ppar_contains(Proc, Proc);
/// ```
///
/// These relations are populated by rules in the categories module.
fn generate_collection_projection_relations(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut relations = Vec::new();

    for rule in &theory.terms {
        // Skip multi-binder constructors (they have term_context with MultiAbstraction)
        let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
            ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        if is_multi_binder {
            continue;
        }
        
        // Check if this constructor has a collection field
        if let Some(elem_cat) = theory.collection_element_type(&rule.label) {
            let parent_cat = &rule.category;
            let constructor = &rule.label;

            // Generate relation name: <constructor_lowercase>_contains
            let rel_name = format_ident!("{}_contains", constructor.to_string().to_lowercase());

            relations.push(quote! {
                relation #rel_name(#parent_cat, #elem_cat);
            });
        }
    }

    relations
}

/// Generate environment relations for EnvQuery conditions
///
/// For each EnvQuery condition in rewrite rules, generate the corresponding relation.
/// Example: `if env_var(x, v) then ...` generates `relation env_var(String, i32);`
fn generate_env_relations(theory: &TheoryDef) -> Vec<TokenStream> {
    use std::collections::HashSet;

    let mut relations = Vec::new();
    let mut seen_relations = HashSet::new();

    // Find all EnvQuery conditions in rewrite rules
    for rewrite in &theory.rewrites {
        for condition in &rewrite.conditions {
            if let Condition::EnvQuery { relation, args: _ } = condition {
                let rel_name = relation.to_string();

                // Avoid duplicates
                if seen_relations.contains(&rel_name) {
                    continue;
                }
                seen_relations.insert(rel_name.clone());

                // Determine the relation type based on the category and native type
                // For calculator: env_var(x, v) where x is String (var name) and v is i32 (value)
                // We need to find which category this applies to and get its native type
                let category = extract_category_from_rewrite(rewrite, theory);
                if let Some(category) = category {
                    if let Some(export) = theory.exports.iter().find(|e| e.name == category) {
                        if let Some(native_type) = &export.native_type {
                            // Generate relation: env_var(String, native_type)
                            // First arg is always String (variable name), second is the native type (value)
                            relations.push(quote! {
                                relation #relation(String, #native_type);
                            });
                        }
                    }
                }
            }
        }
    }

    relations
}

/// Extract the category from a rewrite rule (from LHS)
fn extract_category_from_rewrite(
    rewrite: &RewriteRule,
    theory: &TheoryDef,
) -> Option<proc_macro2::Ident> {
    // Try to extract category from LHS pattern
    if let Some(constructor) = rewrite.left.constructor_name() {
        // Find the rule with this constructor
        theory
            .terms
            .iter()
            .find(|r| &r.label == constructor)
            .map(|rule| rule.category.clone())
    } else {
        None
    }
}
