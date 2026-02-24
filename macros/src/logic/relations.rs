//! Ascent relation declarations
//!
//! Generates relation declarations for categories, equality, rewrites,
//! and collection projections. Also provides a full list of (name, param_types)
//! for unified extraction into custom_relations.

use super::common::relation_names;
use crate::ast::grammar::TermParam;
use crate::ast::language::LanguageDef;
use crate::ast::types::EvalMode;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// One relation entry for extraction: (field name ident, param type names as strings).
pub struct RelationForExtraction {
    pub name: proc_macro2::Ident,
    pub param_types: Vec<String>,
}

/// List all relations that appear in the ascent program (generated + custom logic).
/// Used to populate custom_relations in one unified pass.
pub fn list_all_relations_for_extraction(language: &LanguageDef) -> Vec<RelationForExtraction> {
    let mut out = Vec::new();

    // Category relations: proc(Proc), name(Name), ...
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        out.push(RelationForExtraction {
            name: cat_lower,
            param_types: vec![cat.to_string()],
        });
    }

    // Equality: eq_proc(Proc, Proc), ...
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
        let ty = cat.to_string();
        out.push(RelationForExtraction {
            name: eq_rel,
            param_types: vec![ty.clone(), ty],
        });
    }

    // Rewrite: rw_proc(Proc, Proc), ...
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
        let ty = cat.to_string();
        out.push(RelationForExtraction {
            name: rw_rel,
            param_types: vec![ty.clone(), ty],
        });
    }

    // Fold relations
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let has_fold = language
            .terms
            .iter()
            .any(|r| r.category == *cat && r.eval_mode == Some(EvalMode::Fold));
        if has_fold {
            let fold_rel = format_ident!("fold_{}", cat.to_string().to_lowercase());
            let ty = cat.to_string();
            out.push(RelationForExtraction {
                name: fold_rel,
                param_types: vec![ty.clone(), ty],
            });
        }
    }

    // step_term(primary)
    if let Some(primary) = language.types.first() {
        out.push(RelationForExtraction {
            name: format_ident!("step_term"),
            param_types: vec![primary.name.to_string()],
        });
    }

    // Collection projection: ppar_contains(Proc, Proc), ...
    for rule in &language.terms {
        let is_multi_binder = rule.term_context.as_ref().is_some_and(|ctx| {
            ctx.iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
        });
        if is_multi_binder {
            continue;
        }
        if let Some(elem_cat) = language.collection_element_type(&rule.label) {
            let parent_cat = &rule.category;
            let rel_name = format_ident!("{}_contains", rule.label.to_string().to_lowercase());
            out.push(RelationForExtraction {
                name: rel_name,
                param_types: vec![parent_cat.to_string(), elem_cat.to_string()],
            });
        }
    }

    // Custom logic relations (do not duplicate: custom names must not clash with generated)
    if let Some(logic) = &language.logic {
        for rel in &logic.relations {
            let name = format_ident!("{}", rel.name.to_string());
            let param_types = rel.param_types.clone();
            out.push(RelationForExtraction { name, param_types });
        }
    }

    out
}

/// Generate all relation declarations for a theory
pub fn generate_relations(language: &LanguageDef) -> TokenStream {
    let mut relations = Vec::new();

    for lang_type in &language.types {
        let rn = relation_names(&lang_type.name);
        let cat = &rn.cat;
        let cat_lower = &rn.cat_lower;
        let eq_rel = &rn.eq_rel;
        let rw_rel = &rn.rw_rel;
        let fold_rel = &rn.fold_rel;

        // Category exploration relation (unadorned)
        relations.push(quote! {
            relation #cat_lower(#cat);
        });

        // Equality relation (typed)
        relations.push(quote! {
            #[ds(crate::eqrel)]
            relation #eq_rel(#cat, #cat);
        });

        // Rewrite relation (typed)
        relations.push(quote! {
            relation #rw_rel(#cat, #cat);
        });

        // Fold (big-step eval) relation, only if this category has fold-mode constructors
        let has_fold = language
            .terms
            .iter()
            .any(|r| r.category == *cat && r.eval_mode == Some(EvalMode::Fold));
        if has_fold {
            relations.push(quote! {
                relation #fold_rel(#cat, #cat);
            });
        }
    }

    // step_term(primary): holds only the term being stepped (seeded by runtime).
    // Used by logic to add application results without blow-up (e.g. trans: only apply contexts to the stepped term).
    if let Some(primary) = language.types.first() {
        let cat = &primary.name;
        relations.push(quote! {
            relation step_term(#cat);
        });
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
