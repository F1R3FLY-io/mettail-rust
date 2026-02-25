#![allow(clippy::cmp_owned)]

//! Category exploration and deconstruction rules
//!
//! Generates Ascent rules for:
//! - Category exploration (following rewrite edges)
//! - Term deconstruction (extracting subterms)
//! - Collection projections (extracting elements from collections)
//! - Congruence rules for equality

use super::common::{
    compute_category_reachability, has_collection_field, in_cat_filter, is_multi_binder,
    relation_names, CategoryFilter,
};
use crate::ast::grammar::TermParam;
use crate::ast::{
    grammar::{GrammarItem, GrammarRule},
    language::LanguageDef,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Generate category exploration rules.
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
/// This is used for the core Ascent struct in SCC splitting.
pub fn generate_category_rules(language: &LanguageDef, cat_filter: CategoryFilter) -> TokenStream {
    let mut rules = Vec::new();

    // Compute reachability for pruning dead cross-category rules
    let reachable = compute_category_reachability(language);

    // For core struct, further restrict reachable to only core-category pairs
    let core_reachable;
    let effective_reachable = if let Some(filter) = cat_filter {
        core_reachable = reachable
            .iter()
            .filter(|(s, t)| filter.contains(s) && filter.contains(t))
            .cloned()
            .collect();
        &core_reachable
    } else {
        &reachable
    };

    // Consolidated subterm extraction: one rule per reachable (src, tgt) pair
    let consolidated =
        super::helpers::generate_consolidated_deconstruction_rules(language, effective_reachable);
    rules.extend(consolidated);

    for lang_type in &language.types {
        let cat = &lang_type.name;

        // Skip categories not in the filter
        if !in_cat_filter(cat, cat_filter) {
            continue;
        }

        let rn = relation_names(cat);
        let cat_lower = &rn.cat_lower;
        let rw_rel = &rn.rw_rel;

        // Expand via rewrites: add rewritten terms to enable further exploration
        // Clone c1 so we insert an owned value; Ascent may bind c1 by reference (e.g. &Str).
        rules.push(quote! {
            #cat_lower(c1.clone()) <-- #cat_lower(c0), #rw_rel(c0, c1);
        });

        // PERFORMANCE OPTIMIZATION (2026-01-27):
        // The following closure rules were too slow because they computed O(R × E²) rewrites:
        //   cat(t) <-- cat(s), eq_cat(s, t)
        //   rw_cat(s1, t) <-- rw_cat(s0, t), eq_cat(s0, s1)
        //   rw_cat(s, t1) <-- rw_cat(s, t0), eq_cat(t0, t1)
        //
        // Instead, rewrite rules now use inline equation matching:
        //   rw_cat(s_orig, t) <-- eq_cat(s_orig, s), [pattern match s], ...
        //
        // This computes the same semantics but with O(R × E) complexity instead of O(R × E²).
        // See docs/design/exploring/01-27-equation-computation.md for details.
        //
        // User-defined equation rules directly add their produced terms to proc (see rules.rs).
        // This avoids iterating over all equation pairs (which includes O(|proc|²) congruence pairs).

        // Collection projection population rules for this category
        let projection_rules = generate_collection_projection_population(cat, language);
        rules.extend(projection_rules);

        // Projection seeding rules for this category
        // This adds collection elements to their category relations
        let seeding_rules = generate_projection_seeding_rules(cat, language);
        rules.extend(seeding_rules);

        // Special rules for multi-binder + collection constructors (e.g. PInputs)
        // These CANNOT be consolidated because they have unique semantics
        let special_rules = generate_special_deconstruction_rules(cat, language);
        rules.extend(special_rules);

        // Generate consolidated rewrite congruence rules for auto-generated Apply/MApply variants
        // Only for reachable (src, domain) pairs
        let congruence_rules = super::helpers::generate_consolidated_congruence_rules(
            cat,
            language,
            effective_reachable,
        );
        rules.extend(congruence_rules);
    }

    quote! {
        #(#rules)*
    }
}

/// Generate deconstruction for a constructor that has both a collection field and a binding
/// (e.g. PInputs(Vec(Name), Scope<..., Proc>)).
///
/// Produces:
/// - One rule adding each collection element to its category: `name(n)` for each `n` in the vec.
/// - One rule adding the scope to the same category wrapped as MLam{body_cat} (multi-binder)
///   so the scope is visible as a lambda term without extracting the body.
///
/// This does not cause the same fact explosion as full collection deconstruction because
/// (1) the collection is a Vec (bounded by syntax), and (2) we add one MLam term, not the body.
fn generate_collection_plus_binding_deconstruction(
    category: &Ident,
    constructor: &GrammarRule,
) -> Option<Vec<TokenStream>> {
    use crate::ast::types::TypeExpr;

    // Only for multi-binder + collection (e.g. PInputs): term_context has MultiAbstraction and Simple(Vec)
    let term_context = constructor.term_context.as_ref()?;
    let has_multi = term_context
        .iter()
        .any(|p| matches!(p, TermParam::MultiAbstraction { .. }));
    let has_collection = term_context
        .iter()
        .any(|p| matches!(p, TermParam::Simple { ty: TypeExpr::Collection { .. }, .. }));
    if !has_multi || !has_collection || constructor.bindings.len() != 1 {
        return None;
    }

    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let label = &constructor.label;

    // Find collection element type and binding body type from items
    let mut element_type: Option<&Ident> = None;
    for item in &constructor.items {
        if let GrammarItem::Collection { element_type: e, .. } = item {
            element_type = Some(e);
            break;
        }
    }
    let element_type = element_type?;
    let elem_cat_lower = format_ident!("{}", element_type.to_string().to_lowercase());

    let (_binder_idx, body_indices) = &constructor.bindings[0];
    let body_idx = body_indices.first()?;
    let body_cat = match &constructor.items[*body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => return None,
    };
    // Multi-binder scope → wrap as MLam{body_cat} so the scope appears in the category as a lambda
    let mlam_variant = format_ident!("MLam{}", body_cat);

    // Rust enum has two fields: (collection_vec, scope). Vec uses .iter(), not (elem, _count).
    Some(vec![
        quote! {
            #elem_cat_lower(elem.clone()) <--
                #cat_lower(t),
                if let #category::#label(ref vec_field, _) = t,
                for elem in vec_field.iter();
        },
        quote! {
            #cat_lower(#category::#mlam_variant(scope.clone())) <--
                #cat_lower(t),
                if let #category::#label(_, scope) = t;
        },
    ])
}

/// Generate special deconstruction rules that cannot be consolidated into helpers.
///
/// This handles:
/// - Multi-binder + collection constructors (e.g. PInputs) which have unique
///   deconstruction logic (iterate Vec + wrap scope as MLam)
fn generate_special_deconstruction_rules(
    category: &Ident,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for constructor in language.terms.iter().filter(|r| r.category == *category) {
        // Only handle multi-binder + collection constructors
        if !is_multi_binder(constructor) || !has_collection_field(constructor) {
            continue;
        }
        if let Some(special_rules) =
            generate_collection_plus_binding_deconstruction(category, constructor)
        {
            rules.extend(special_rules);
        }
    }

    rules
}

/// Generate collection projection population rules
/// For each constructor with a collection field, generate rules that populate
/// the corresponding "contains" relation.
///
/// Example: For PPar(HashBag<Proc>), generates:
/// ```text
/// ppar_contains(parent.clone(), elem.clone()) <--
///     proc(parent),
///     if let Proc::PPar(ref bag_field) = parent,
///     for (elem, _count) in bag_field.iter();
/// ```
///
/// This creates a database of all collection-element relationships that can be
/// efficiently queried and joined by Ascent.
fn generate_collection_projection_population(
    category: &Ident,
    language: &LanguageDef,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    // Find all constructors for this category
    let constructors: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.category == *category)
        .collect();

    for constructor in constructors {
        // Skip multi-binder constructors (they have term_context with MultiAbstraction)
        if is_multi_binder(constructor) {
            continue;
        }

        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let GrammarItem::Collection {
                element_type,
                coll_type,
                ..
            } = item
            {
                // Found a collection field - generate projection rule
                let parent_cat = &constructor.category;
                let parent_cat_lower = format_ident!("{}", parent_cat.to_string().to_lowercase());
                let constructor_label = &constructor.label;
                let _elem_cat = element_type;

                // Generate relation name: <constructor_lowercase>_contains
                let rel_name =
                    format_ident!("{}_contains", constructor_label.to_string().to_lowercase());

                let (binding, iter_clause) = match coll_type {
                    crate::ast::types::CollectionType::Vec => {
                        (quote! { ref coll_field }, quote! { for elem in coll_field.iter(); })
                    },
                    crate::ast::types::CollectionType::HashBag
                    | crate::ast::types::CollectionType::HashSet => (
                        quote! { ref coll_field },
                        quote! { for (elem, _count) in coll_field.iter(); },
                    ),
                };

                rules.push(quote! {
                    #rel_name(parent.clone(), elem.clone()) <--
                        #parent_cat_lower(parent),
                        if let #parent_cat::#constructor_label(#binding) = parent,
                        #iter_clause
                });

                // Only handle one collection per constructor for now
                break;
            }
        }
    }

    rules
}

/// Generate rules to seed category relations from projection relations
/// This allows base rewrites to match on collection elements without eager deconstruction.
///
/// Example: For PPar(HashBag<Proc>) with projection relation ppar_contains(Proc, Proc),
/// generates:
/// ```text
/// proc(elem) <-- ppar_contains(_parent, elem);
/// ```
///
/// This is much more efficient than eager deconstruction because:
/// 1. Elements are only added to proc when they're actually in a ppar_contains fact
/// 2. No redundant facts for elements that appear in multiple collections
/// 3. Lazy evaluation: only computes what's needed
fn generate_projection_seeding_rules(category: &Ident, language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    let _cat_lower = format_ident!("{}", category.to_string().to_lowercase());

    // Find all constructors for this category that have collections
    let constructors: Vec<&GrammarRule> = language
        .terms
        .iter()
        .filter(|r| r.category == *category)
        .collect();

    for constructor in constructors {
        // Skip multi-binder constructors
        if is_multi_binder(constructor) {
            continue;
        }

        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let GrammarItem::Collection { element_type, .. } = item {
                // Found a collection field
                let elem_cat = element_type;
                let elem_cat_lower = format_ident!("{}", elem_cat.to_string().to_lowercase());
                let constructor_label = &constructor.label;

                // Generate relation name: <constructor_lowercase>_contains
                let rel_name =
                    format_ident!("{}_contains", constructor_label.to_string().to_lowercase());

                // Generate seeding rule: elem_cat(elem) <-- contains_rel(_parent, elem);
                // Clone elem so we insert owned; Ascent may bind elem by reference.
                rules.push(quote! {
                    #elem_cat_lower(elem.clone()) <-- #rel_name(_parent, elem);
                });

                // Only handle one collection per constructor
                break;
            }
        }
    }

    rules
}
