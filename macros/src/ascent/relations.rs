//! Ascent relation declarations
//!
//! Generates relation declarations for categories, equality, rewrites,
//! and collection projections.

use crate::ascent::congruence::get_constructor_collection_element_type;
use crate::ast::TheoryDef;
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
        // Check if this constructor has a collection field
        if let Some(elem_cat) = get_constructor_collection_element_type(&rule.label, theory) {
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
/// Automatically generates `env_var(String, Category)` relations for ALL exported categories.
/// This enables automatic variable assignment and retrieval for every category.
/// Works with both native types (i32) and custom category types (Proc, Expr, etc.)
fn generate_env_relations(theory: &TheoryDef) -> Vec<TokenStream> {
    use crate::ast::Condition;
    use std::collections::HashSet;

    let mut relations = Vec::new();
    let mut seen_categories = HashSet::new();

    // First, collect categories from explicit EnvQuery conditions (for backward compatibility)
    for rewrite in &theory.rewrites {
        for condition in &rewrite.conditions {
            if let Condition::EnvQuery { relation, args: _ } = condition {
                let rel_name = relation.to_string();
                if rel_name != "env_var" {
                    // Only handle env_var automatically, other relation names are user-defined
                    continue;
                }

                // Determine the relation type based on the category
                let category = extract_category_from_rewrite(rewrite, theory);
                if let Some(category) = category {
                    seen_categories.insert(category.to_string());
                }
            }
        }
    }

    // Automatically generate env_var relations for ALL exported categories
    // Use category-specific relation names to avoid conflicts (e.g., env_var_proc, env_var_name)
    for export in &theory.exports {
        let category = &export.name;
        let cat_str = category.to_string().to_lowercase();
        let env_rel_name = format_ident!("env_var_{}", cat_str);

        // Check if category has native type - if so, use native type; otherwise use category
        if let Some(native_type) = &export.native_type {
            // For native types, use the native type directly (e.g., i32 instead of Int)
            relations.push(quote! {
                relation #env_rel_name(String, #native_type);
            });
        } else {
            // For custom types, use the category type (e.g., Proc, Expr)
            relations.push(quote! {
                relation #env_rel_name(String, #category);
            });
        }
    }

    relations
}

/// Extract the category from a rewrite rule (from LHS)
fn extract_category_from_rewrite(
    rewrite: &crate::ast::RewriteRule,
    theory: &TheoryDef,
) -> Option<proc_macro2::Ident> {
    use crate::ast::Expr;

    // Try to extract category from LHS pattern
    match &rewrite.left {
        Expr::Apply { constructor, .. } => {
            // Find the rule with this constructor
            theory
                .terms
                .iter()
                .find(|r| r.label == *constructor)
                .map(|rule| rule.category.clone())
        },
        Expr::Var(_) => None,
        Expr::Subst { .. } => None,
        Expr::CollectionPattern { .. } => None,
    }
}
