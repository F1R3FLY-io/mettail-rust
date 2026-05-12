#![allow(clippy::cmp_owned)]

//! Category exploration and deconstruction rules
//!
//! Generates Ascent rules for:
//! - Category exploration (following rewrite edges)
//! - Term deconstruction (extracting subterms)
//! - Collection projections (extracting elements from collections)
//! - Congruence rules for equality

use super::common::{
    compute_category_reachability, compute_demanded_categories, filter_reachable_by_demand,
    has_collection_field, in_cat_filter, is_multi_binder, relation_names, CategoryFilter,
};
use mettail_ast::grammar::TermParam;
use mettail_ast::{
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
///
/// ## A-RT06: Demand-Driven Relation Population
///
/// Cross-category deconstruction rules are filtered by demand analysis: only `(src, tgt)`
/// pairs where `tgt` is referenced by at least one equation, rewrite, or logic rule are
/// generated. Self-loop pairs `(src, src)` are always kept. This avoids eagerly populating
/// category relations with subterms that no rule ever reads.
pub fn generate_category_rules(language: &LanguageDef, cat_filter: CategoryFilter) -> TokenStream {
    let mut rules = Vec::new();

    // Compute reachability for pruning dead cross-category rules
    let reachable = compute_category_reachability(language);

    // A-RT06: Demand-driven filtering — only generate deconstruction for (src, tgt) pairs
    // where tgt is referenced by at least one equation/rewrite/logic rule body.
    let demanded = compute_demanded_categories(language);
    let demand_filtered = filter_reachable_by_demand(&reachable, &demanded);

    // Emit lint diagnostic when demand filtering prunes pairs (only for the main struct,
    // not for the core struct where cat_filter is Some — avoids duplicate diagnostics).
    if cat_filter.is_none() {
        let pruned_count = reachable.len() - demand_filtered.len();
        if pruned_count > 0 {
            let pruned_pairs: Vec<String> = reachable
                .difference(&demand_filtered)
                .map(|(s, t)| format!("({}, {})", s, t))
                .collect();
            mettail_prattail::lint::emit_diagnostic(&mettail_prattail::lint::LintDiagnostic {
                id: mettail_prattail::lint::DiagnosticId::G34,
                name: "demand-driven-deconstruction",
                severity: mettail_prattail::lint::LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "A-RT06: pruned {} unreferenced cross-category deconstruction pair(s): {}",
                    pruned_count,
                    pruned_pairs.join(", "),
                ),
                hint: Some(
                    "these (src, tgt) pairs are structurally reachable but no equation/rewrite/logic rule references tgt"
                        .to_string(),
                ),
                grammar_name: Some(language.name.to_string()),
                source_location: None,
            });
        }
    }

    // For core struct, further restrict reachable to only core-category pairs
    let core_reachable;
    let effective_reachable = if let Some(filter) = cat_filter {
        core_reachable = demand_filtered
            .iter()
            .filter(|(s, t)| filter.contains(s) && filter.contains(t))
            .cloned()
            .collect();
        &core_reachable
    } else {
        &demand_filtered
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

        // Expand via rewrites: add rewritten terms to enable further exploration.
        // Normalize the rewritten term to eagerly collapse cancellation pairs
        // (e.g., PDrop(NQuote(P)) → P) before inserting into the category relation.
        // Without this, cancellation pairs introduced by rewrites would persist
        // as un-collapsed terms in the Ascent fixpoint.
        //
        // BCG05: Normalize-on-insert deduplication.
        // Before normalizing, compute a structural hash of the pre-normalized term
        // and check a thread-local HashSet. If the hash was already seen, skip the
        // entire rule firing — the normalized form was already inserted in a prior
        // iteration. This avoids redundant normalize() calls when the same term
        // appears via multiple rewrite paths.
        rules.push(quote! {
            #cat_lower(c1.clone().normalize()) <-- #cat_lower(c0), #rw_rel(c0, c1),
                if {
                    use std::hash::{Hash, Hasher};
                    let mut __bcg05_h = std::hash::DefaultHasher::new();
                    c1.hash(&mut __bcg05_h);
                    let __bcg05_hash = __bcg05_h.finish();
                    thread_local! {
                        static __BCG05_EXPAND: std::cell::RefCell<(u64, std::collections::HashSet<u64>)> =
                            std::cell::RefCell::new((0, std::collections::HashSet::new()));
                    }
                    let __epoch = mettail_runtime::bcg05_epoch();
                    __BCG05_EXPAND.with(|s| {
                        let mut guard = s.borrow_mut();
                        if guard.0 != __epoch {
                            guard.0 = __epoch;
                            guard.1.clear();
                        }
                        guard.1.insert(__bcg05_hash)
                    })
                };
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

/// Generate deconstruction for a constructor that has both one-or-more collection fields
/// and a binding (e.g. PInputs(Vec(Name), Scope<..., Proc>) — 2 fields;
/// or Phase 4 #2 TaggedInputs(Vec(Proc), Vec(Name), Scope<..., Proc>) — 3 fields).
///
/// Produces:
/// - One rule per collection field, adding each collection element to its category:
///   `name(n)` for each `n` in the names vec; `proc(p)` for each `p` in the tags vec.
/// - One rule adding the scope to the binding-body category wrapped as MLam{body_cat}
///   (multi-binder) so the scope is visible as a lambda term without extracting the body.
///
/// Phase 4 #2 (2026-05-12): generalized from the prior fixed 2-field
/// `(ref vec_field, _) | (_, scope)` patterns to an arity-aware
/// emission. AST field positional indices are derived from
/// `term_context`: each `TermParam` corresponds to ONE AST field; the
/// term_context order matches the AST tuple-variant field order.
///
/// Constraints:
/// - Scope must still be present in term_context (caller filters
///   `is_multi_binder`).
/// - At least one Collection field must be present (caller filters
///   `has_collection_field`).
/// - The Collection fields and the Scope can be in ANY order within
///   term_context (no longer hardcoded "Scope last").
///
/// This does not cause the same fact explosion as full collection
/// deconstruction because (1) collections are bounded by syntax, and
/// (2) we add one MLam term per rule, not the body.
fn generate_collection_plus_binding_deconstruction(
    category: &Ident,
    constructor: &GrammarRule,
) -> Option<Vec<TokenStream>> {
    use mettail_ast::types::TypeExpr;

    // Only for multi-binder + collection (e.g. PInputs, TaggedInputs):
    // term_context has MultiAbstraction and at least one Simple(Collection).
    let term_context = constructor.term_context.as_ref()?;
    if constructor.bindings.len() != 1 {
        return None;
    }

    // Phase 4 #2 (2026-05-12): walk term_context to collect Collection
    // field indices + the Scope field index. Each TermParam maps to one
    // AST tuple-variant field at the same positional index.
    let mut collection_fields: Vec<(usize, Ident)> = Vec::new();
    let mut scope_field_idx: Option<usize> = None;
    for (i, param) in term_context.iter().enumerate() {
        match param {
            TermParam::Simple {
                ty: TypeExpr::Collection { element, .. },
                ..
            } => {
                if let TypeExpr::Base(elem) = element.as_ref() {
                    collection_fields.push((i, elem.clone()));
                }
            }
            TermParam::MultiAbstraction { .. } => {
                scope_field_idx = Some(i);
            }
            _ => {}
        }
    }
    if collection_fields.is_empty() {
        return None;
    }
    let scope_field_idx = scope_field_idx?;
    let total_fields = term_context.len();

    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let label = &constructor.label;

    let (_binder_idx, body_indices) = &constructor.bindings[0];
    let body_idx = body_indices.first()?;
    let body_cat = match &constructor.items[*body_idx] {
        GrammarItem::NonTerminal { ident: cat, .. } => cat,
        _ => return None,
    };
    // Multi-binder scope → wrap as MLam{body_cat} so the scope appears in the category as a lambda
    let mlam_variant = format_ident!("MLam{}", body_cat);

    let mut rules: Vec<TokenStream> = Vec::with_capacity(collection_fields.len() + 1);

    // Phase 4 #2 generalization: one projection rule per Collection field.
    // Each rule binds `vec_field` at the Collection's positional index;
    // other fields (including the Scope and any sibling Collections) are
    // wildcarded with `_`.
    for (coll_idx, elem_type) in &collection_fields {
        let elem_cat_lower = format_ident!("{}", elem_type.to_string().to_lowercase());
        let pattern_fields: Vec<TokenStream> = (0..total_fields)
            .map(|i| {
                if i == *coll_idx {
                    quote! { ref vec_field }
                } else {
                    quote! { _ }
                }
            })
            .collect();
        rules.push(quote! {
            #elem_cat_lower(elem.clone()) <--
                #cat_lower(t),
                if let #category::#label(#(#pattern_fields),*) = t,
                for elem in vec_field.iter();
        });
    }

    // Scope-wrap rule: bind `scope` at the Scope field's positional index;
    // other fields wildcarded.
    let scope_pattern_fields: Vec<TokenStream> = (0..total_fields)
        .map(|i| {
            if i == scope_field_idx {
                quote! { scope }
            } else {
                quote! { _ }
            }
        })
        .collect();
    rules.push(quote! {
        #cat_lower(#category::#mlam_variant(scope.clone())) <--
            #cat_lower(t),
            if let #category::#label(#(#scope_pattern_fields),*) = t;
    });

    Some(rules)
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

        // B9 / Class 2 (2026-05-08): skip multi-Simple-param constructors
        // whose collection slot is part of a binder-rule body. The
        // generated `if let Proc::Label(ref coll_field) = parent` pattern
        // expects a single-arg tuple variant (Class-5 collection-literal
        // pattern); for Class-2 binder rules with shape e.g.
        // `Choose . a:Proc, qs:Vec(Proc)`, the variant has 2 fields and
        // the pattern would fail with E0023. Future work: emit a Class-2
        // variant of the projection that matches the multi-field tuple
        // and projects the collection slot.
        if let Some(ref ctx) = constructor.term_context {
            let simple_count = ctx
                .iter()
                .filter(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
                .count();
            if simple_count > 1 {
                continue;
            }
        }

        // Check if this constructor has a collection field
        for item in &constructor.items {
            if let GrammarItem::Collection { element_type, coll_type, .. } = item {
                // Found a collection field - generate projection rule
                let parent_cat = &constructor.category;
                let parent_cat_lower = format_ident!("{}", parent_cat.to_string().to_lowercase());
                let constructor_label = &constructor.label;
                let _elem_cat = element_type;

                // Generate relation name: <constructor_lowercase>_contains
                let rel_name =
                    format_ident!("{}_contains", constructor_label.to_string().to_lowercase());

                let (binding, iter_clause) = match coll_type {
                    mettail_ast::types::CollectionType::HashMap => {
                        // Map-as-collection fields are not supported in Phase 1.
                        continue;
                    },
                    mettail_ast::types::CollectionType::Vec => {
                        (quote! { ref coll_field }, quote! { for elem in coll_field.iter(); })
                    },
                    mettail_ast::types::CollectionType::HashBag
                    | mettail_ast::types::CollectionType::HashSet => (
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

        // B9 / Class 2 (2026-05-08): skip multi-Simple-param constructors
        // whose collection slot is part of a binder-rule body — same
        // rationale as `generate_collection_projection_population`.
        if let Some(ref ctx) = constructor.term_context {
            let simple_count = ctx
                .iter()
                .filter(|p| matches!(p, mettail_ast::grammar::TermParam::Simple { .. }))
                .count();
            if simple_count > 1 {
                continue;
            }
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
