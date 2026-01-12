#![allow(
    clippy::cmp_owned,
    clippy::too_many_arguments,
    clippy::needless_borrow,
    clippy::for_kv_map,
    clippy::let_and_return,
    clippy::unused_enumerate_index,
    clippy::expect_fun_call,
    clippy::collapsible_match,
    clippy::unwrap_or_default,
    clippy::unnecessary_filter_map
)]

use super::analysis::{
    find_base_rewrites_for_category, CaptureInfo, CollectionCongruenceInfo, ElementPatternInfo,
};
use super::regular::{
    extract_regular_congruence_pattern, find_regular_congruences_for_category,
    generate_regular_congruence_clause,
};
use crate::ascent::rewrites::rhs::generate_rhs_construction;
use crate::ast::{Expr, TheoryDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Generate congruence for collection constructors
/// Example: if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})
/// Generates:
/// ```text
/// rw_proc(parent, result) <--
///     ppar_contains(parent, elem),
///     rw_proc(elem, elem_rewritten),
///     if let Proc::PPar(ref bag) = parent,
///     let rest = { let mut b = bag.clone(); b.remove(&elem); b },
///     let result = Proc::PPar({
///         let mut bag = rest;
///         Proc::insert_into_ppar(&mut bag, elem_rewritten);
///         bag
///     });
/// ```
pub fn generate_collection_congruence(
    category: &Ident,
    _cat_lower: &Ident,
    rw_rel: &Ident,
    constructor: &Ident,
    _source_var: &Ident,
    _target_var: &Ident,
    _rest_var: Option<&Ident>,
    theory: &TheoryDef,
) -> Option<TokenStream> {
    // Get the element category by finding this constructor's collection field
    let rule = theory.terms.iter().find(|r| r.label == *constructor)?;

    let elem_cat = rule.items.iter().find_map(|item| {
        if let crate::ast::GrammarItem::Collection { element_type, .. } = item {
            Some(element_type.clone())
        } else {
            None
        }
    })?;

    // Generate relation name for projection
    let contains_rel = format_ident!("{}_contains", constructor.to_string().to_lowercase());

    // Generate the element rewrite relation
    let elem_rw_rel = format_ident!("rw_{}", elem_cat.to_string().to_lowercase());

    // Generate flatten helper name
    let constructor_lower = format_ident!("{}", constructor.to_string().to_lowercase());
    let insert_helper = format_ident!("insert_into_{}", constructor_lower);

    Some(quote! {
        #rw_rel(parent, result) <--
            #contains_rel(parent, elem),
            #elem_rw_rel(*elem, elem_rewritten),
            if let #category::#constructor(ref bag) = parent,
            let rest = {
                let mut b = bag.clone();
                b.remove(elem);
                b
            },
            let result = #category::#constructor({
                let mut bag = rest;
                #category::#insert_helper(&mut bag, elem_rewritten.clone());
                bag
            }).normalize();
    })
}

/// Generate congruence clauses for a collection congruence using projections
/// This is the new approach that generates clauses for both base rewrites and regular congruences
pub fn generate_new_collection_congruence_clauses(
    cong_idx: usize,
    cong_info: &CollectionCongruenceInfo,
    base_patterns: &[Vec<ElementPatternInfo>],
    theory: &TheoryDef,
) -> Vec<TokenStream> {
    let mut clauses = Vec::new();

    let rw_rel = format_ident!("rw_{}", cong_info.parent_category.to_string().to_lowercase());
    let parent_cat = &cong_info.parent_category;
    let constructor = &cong_info.constructor;
    let constructor_lower = format_ident!("{}", constructor.to_string().to_lowercase());
    let insert_helper = format_ident!("insert_into_{}", constructor_lower);

    // Find all base rewrites that involve this element category
    let base_rewrites = find_base_rewrites_for_category(&cong_info.element_category, theory);

    // Find all regular congruences on this element category
    let regular_congruences =
        find_regular_congruences_for_category(&cong_info.element_category, theory);

    // Generate clauses for base rewrites
    // Each base rewrite gets ONE clause that may join multiple projections
    for (base_idx, base_rule) in base_rewrites.iter().enumerate() {
        // Use the updated patterns with captures extracted during projection generation
        let element_patterns = if base_idx < base_patterns.len() {
            &base_patterns[base_idx]
        } else {
            continue; // Skip if patterns weren't generated for this base rewrite
        };

        if element_patterns.is_empty() {
            continue;
        }

        // Generate ONE clause for this base rewrite, joining all its projections
        let clause = generate_joined_base_rewrite_clause(
            cong_idx,
            base_idx,
            cong_info,
            element_patterns,
            &base_rule.right,
            &rw_rel,
            parent_cat,
            constructor,
            &insert_helper,
            theory,
        );
        clauses.push(clause);
    }

    // Generate clauses for regular congruences
    for (reg_idx, reg_cong) in regular_congruences.iter().enumerate() {
        if let Some(pattern) = extract_regular_congruence_pattern(reg_cong, theory) {
            let clause = generate_regular_congruence_clause(
                cong_idx,
                reg_idx,
                cong_info,
                &pattern,
                &rw_rel,
                parent_cat,
                constructor,
                &insert_helper,
                theory,
            );
            clauses.push(clause);
        }
    }

    // Generate a general collection congruence clause for ANY rewrite from elements
    // This handles auto-generated rewrites (like variable substitution) that aren't
    // covered by the projection-based clauses above
    let contains_rel = format_ident!("{}_contains", constructor.to_string().to_lowercase());
    let elem_rw_rel = format_ident!("rw_{}", cong_info.element_category.to_string().to_lowercase());
    clauses.push(quote! {
        #rw_rel(parent, result) <--
            #contains_rel(parent, elem),
            #elem_rw_rel(elem.clone(), elem_rewritten),
            if let #parent_cat::#constructor(ref bag) = parent,
            let remaining = {
                let mut b = bag.clone();
                b.remove(&elem);
                b
            },
            let result = #parent_cat::#constructor({
                let mut bag_result = remaining;
                #parent_cat::#insert_helper(&mut bag_result, elem_rewritten.clone());
                bag_result
            }).normalize();
    });

    clauses
}

/// Generate congruence clause for a base rewrite with possibly multiple element patterns
/// For multi-element patterns (like communication), joins all projections
/// For single-element patterns (like drop-quote), uses one projection
fn generate_joined_base_rewrite_clause(
    cong_idx: usize,
    base_idx: usize,
    _cong_info: &CollectionCongruenceInfo,
    patterns: &[ElementPatternInfo],
    rhs: &Expr,
    rw_rel: &Ident,
    parent_cat: &Ident,
    constructor: &Ident,
    insert_helper: &Ident,
    theory: &TheoryDef,
) -> TokenStream {
    use std::collections::HashMap;

    // First pass: identify shared variables (appear in multiple patterns) and track their categories
    let mut var_pattern_counts: HashMap<String, Vec<(usize, Ident)>> = HashMap::new();
    for (pat_idx, pattern) in patterns.iter().enumerate() {
        for capture in &pattern.captures {
            var_pattern_counts
                .entry(capture.var_name.clone())
                .or_insert_with(Vec::new)
                .push((pat_idx, capture.category.clone()));
        }
    }

    let shared_vars: HashMap<String, (Vec<usize>, Ident)> = var_pattern_counts
        .iter()
        .filter(|(_, pattern_cats)| pattern_cats.len() > 1)
        .map(|(name, pattern_cats)| {
            let pattern_idxs: Vec<_> = pattern_cats.iter().map(|(idx, _)| *idx).collect();
            let category = pattern_cats[0].1.clone(); // All should have the same category
            (name.clone(), (pattern_idxs, category))
        })
        .collect();

    // Generate projection joins for all patterns
    let mut projection_calls = Vec::new();
    let mut elem_vars = Vec::new();
    let mut all_capture_vars = Vec::new();
    let mut rest_vars = Vec::new(); // Track rest variables

    for (pat_idx, pattern) in patterns.iter().enumerate() {
        let rel_name = format_ident!(
            "{}_proj_c{}_b{}_p{}",
            pattern.constructor.to_string().to_lowercase(),
            cong_idx,
            base_idx,
            pat_idx
        );

        // Generate projection call arguments
        let mut proj_args = vec![quote! { parent }];
        let mut pattern_capture_vars = Vec::new();

        // Extract captures for all patterns (including nested ones)
        for capture in &pattern.captures {
            // Check if this is a rest variable (marked by field_idx == usize::MAX)
            let is_rest = capture.field_idx == usize::MAX;

            // ALWAYS use pattern-specific names for all variables
            // We'll add eq_* checks for shared variables separately
            let cap_name = format_ident!("cap_{}_p{}", capture.var_name.to_lowercase(), pat_idx);
            proj_args.push(quote! { #cap_name });

            // Only add to capture_vars if it's not a rest variable
            // Rest variables are tracked separately for RHS reconstruction
            if !is_rest {
                pattern_capture_vars.push((cap_name.clone(), capture.clone()));
            } else {
                // Track rest variables separately
                let rest_var_name =
                    syn::Ident::new(&capture.var_name, proc_macro2::Span::call_site());
                rest_vars.push((cap_name.clone(), rest_var_name));
            }
        }

        let elem_var = format_ident!("elem_{}", pat_idx);
        proj_args.push(quote! { #elem_var });
        elem_vars.push(elem_var);
        all_capture_vars.extend(pattern_capture_vars);

        // Add rest variable from pattern-level rest (if present and not already in captures)
        // This handles rest at the pattern's collection level (e.g., {A, B, ...rest})
        if let Some(rest_var) = &pattern.rest_var {
            // Check if this rest was already added via captures (nested rest)
            let already_added = rest_vars
                .iter()
                .any(|(_, rv)| rv.to_string() == rest_var.to_string());
            if !already_added {
                let rest_ident =
                    format_ident!("rest_{}_p{}", rest_var.to_string().to_lowercase(), pat_idx);
                proj_args.push(quote! { #rest_ident });
                rest_vars.push((rest_ident, rest_var.clone()));
            }
        }

        projection_calls.push(quote! {
            #rel_name(#(#proj_args),*)
        });
    }

    // Generate equational checks for shared variables
    // For each shared variable, check equality between all its occurrences using eq_* relation
    let mut equational_checks = Vec::new();
    for (var_name, (pattern_idxs, category)) in &shared_vars {
        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

        // For each pair of occurrences, add eq_category(cap_var_p0, cap_var_p1)
        // We only need to check the first occurrence against all others (transitivity handled by eqrel)
        if pattern_idxs.len() > 1 {
            let first_idx = pattern_idxs[0];
            let first_var = format_ident!("cap_{}_p{}", var_name.to_lowercase(), first_idx);

            for &other_idx in &pattern_idxs[1..] {
                let other_var = format_ident!("cap_{}_p{}", var_name.to_lowercase(), other_idx);
                equational_checks.push(quote! {
                    #eq_rel(#first_var.clone(), #other_var.clone())
                });
            }
        }
    }

    // For nested patterns, we now extract ALL captures via projection (using full pattern matching)
    // So we can use direct RHS reconstruction for all cases
    let rhs_term = generate_rhs_reconstruction(rhs, &all_capture_vars, &rest_vars, theory);
    let rhs_generation = quote! {
        let rhs_term = #rhs_term
    };

    // Generate element removal for all matched elements
    let elem_removal = if elem_vars.len() == 1 {
        let elem_var = &elem_vars[0];
        quote! {
            let remaining = {
                let mut b = bag.clone();
                b.remove(#elem_var);
                b
            }
        }
    } else {
        let removals = elem_vars.iter().map(|ev| quote! { b.remove(#ev); });
        quote! {
            let remaining = {
                let mut b = bag.clone();
                #(#removals)*
                b
            }
        }
    };

    // Build the clause body, conditionally including equational checks
    let clause_body = if equational_checks.is_empty() {
        quote! {
            #rw_rel(parent, result) <--
                #(#projection_calls),*,
                #rhs_generation,
                if let #parent_cat::#constructor(ref bag) = parent,
                #elem_removal,
                let result = #parent_cat::#constructor({
                    let mut bag_result = remaining;
                    #parent_cat::#insert_helper(&mut bag_result, rhs_term);
                    bag_result
                }).normalize();
        }
    } else {
        quote! {
            #rw_rel(parent, result) <--
                #(#projection_calls),*,
                #(#equational_checks),*,
                #rhs_generation,
                if let #parent_cat::#constructor(ref bag) = parent,
                #elem_removal,
                let result = #parent_cat::#constructor({
                    let mut bag_result = remaining;
                    #parent_cat::#insert_helper(&mut bag_result, rhs_term);
                    bag_result
                }).normalize();
        }
    };

    clause_body
}

/// Helper to generate RHS reconstruction from captured variables
/// For congruence clauses, extracts elements from collection RHS
fn generate_rhs_reconstruction(
    rhs: &Expr,
    captures: &[(Ident, CaptureInfo)],
    rest_vars: &[(Ident, Ident)], // (rest_binding_ident, rest_var_name)
    theory: &TheoryDef,
) -> TokenStream {
    // Build a bindings map for RHS generator
    // For shared variables (appearing in multiple patterns), use only the FIRST occurrence
    let mut bindings = std::collections::HashMap::new();
    for (var_ident, capture_info) in captures {
        // Only insert if not already present (to use first occurrence)
        bindings
            .entry(capture_info.var_name.clone())
            .or_insert_with(|| quote! { #var_ident.clone() });
    }

    // Add rest variables to bindings (as HashBag)
    for (rest_ident, rest_var_name) in rest_vars {
        bindings.insert(rest_var_name.to_string(), quote! { #rest_ident.clone() });
    }

    // Special case: if RHS is a collection constructor with collection pattern inside,
    // extract just the elements (since insert_into_X will add them to the collection)
    if let Expr::Apply { constructor: _, args } = rhs {
        // Check if this has a collection argument
        for arg in args {
            if let Expr::CollectionPattern { elements, rest, .. } = arg {
                // This is a collection RHS like (PPar {(subst P x (NQuote Q))})
                // We need to generate code for the element(s), not the whole PPar

                if elements.len() == 1 && rest.is_none() {
                    // Single element, no rest - just generate that element
                    return generate_rhs_construction(&elements[0], &bindings, theory);
                } else if elements.len() > 1 || rest.is_some() {
                    // Multiple elements or rest - need to handle merging
                    let element_terms: Vec<_> = elements
                        .iter()
                        .map(|e| generate_rhs_construction(e, &bindings, theory))
                        .collect();

                    if let Some(rest_var) = rest {
                        // Has rest - need to merge
                        if let Some(rest_binding) = bindings.get(&rest_var.to_string()) {
                            // Generate: insert all elements into rest
                            return quote! {
                                {
                                    let mut bag = (#rest_binding).clone();
                                    #(bag.insert(#element_terms);)*
                                    bag
                                }
                            };
                        }
                    }

                    // No rest - just the elements
                    // For communication, the RHS should be a single element
                    if element_terms.len() == 1 {
                        return element_terms[0].clone();
                    }
                }
            }
        }
    }

    // Default: use rewrite RHS generation (handles Subst correctly with .substitute_X methods)
    generate_rhs_construction(rhs, &bindings, theory)
}
