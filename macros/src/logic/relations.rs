//! Ascent relation declarations
//!
//! Generates relation declarations for categories, equality, rewrites,
//! and collection projections.

use crate::ast::grammar::TermParam;
use crate::ast::language::LanguageDef;
use crate::ast::types::EvalMode;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Generate all relation declarations for a theory
pub fn generate_relations(language: &LanguageDef) -> TokenStream {
    let mut relations = Vec::new();

    // Category exploration relations (unadorned)
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            relation #cat_lower(#cat);
        });
    }

    // Equality relations (per-category, typed)
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            #[ds(crate::eqrel)]
            relation #eq_rel(#cat, #cat);
        });
    }

    // Rewrite relations (per-category, typed)
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
        relations.push(quote! {
            relation #rw_rel(#cat, #cat);
        });
    }

    // Fold (big-step eval) relations for categories that have fold-mode constructors
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let has_fold = language
            .terms
            .iter()
            .any(|r| r.category == *cat && r.eval_mode == Some(EvalMode::Fold));
        if has_fold {
            let fold_rel = format_ident!("fold_{}", cat.to_string().to_lowercase());
            relations.push(quote! {
                relation #fold_rel(#cat, #cat);
            });
        }
    }

    // Collection projection relations (automatic)
    // For each constructor with a collection field, generate a "contains" relation
    // Example: PPar(HashBag<Proc>) generates: relation ppar_contains(Proc, Proc);
    let projection_relations = generate_collection_projection_relations(language);
    relations.extend(projection_relations);

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
fn generate_collection_projection_relations(language: &LanguageDef) -> Vec<TokenStream> {
    let mut relations = Vec::new();

    for rule in &language.terms {
        // Skip multi-binder constructors (they have term_context with MultiAbstraction)
        let is_multi_binder = rule.term_context.as_ref().is_some_and(|ctx| {
            ctx.iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        if is_multi_binder {
            continue;
        }

        // Check if this constructor has a collection field
        if let Some(elem_cat) = language.collection_element_type(&rule.label) {
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
