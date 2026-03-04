//! Equation rules generation for Ascent Datalog.
//!
//! Generates:
//! - Reflexivity rules (eq_cat(t, t) for all t)
//! - Equality congruence rules (if args equal, constructed terms equal)
//! - User-defined equation rules

use super::common::{
    generate_tls_pool_iter, in_cat_filter, relation_names, CategoryFilter, PoolArm,
};
use crate::ast::grammar::{GrammarItem, GrammarRule};
use crate::ast::language::LanguageDef;
use crate::logic::rules as unified_rules;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeMap;
use syn::Ident;

/// Main entry point: Generate all equation rules.
///
/// This includes:
/// 1. Reflexivity rules for all categories
/// 2. Demand-driven equality congruence for existing terms
/// 3. User-defined equations
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
/// When `analysis` is `Some`, dead constructors are skipped in congruence rules (Sprint 1 DCE).
/// When `subsumed_equations` is non-empty, subsumed equations are eliminated (Sprint A N10 DCE).
/// When `cancellation_equations` is non-empty, cancellation pair equations are suppressed from
/// eqrel generation (they would cause non-convergence via symmetric expansion).
pub fn generate_equation_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
    subsumed_equations: &std::collections::HashSet<usize>,
    cancellation_equations: &std::collections::HashSet<usize>,
) -> TokenStream {
    let mut rules = Vec::new();

    // 1. Add reflexivity for eq relations
    rules.extend(generate_reflexivity_rules(language, cat_filter));

    // 2. Add demand-driven congruence rules for all constructors
    // These only equate terms that already exist, not synthesize new ones
    rules.extend(generate_congruence_rules(language, cat_filter, analysis));

    // 3. Generate user-defined equation rules using unified approach,
    //    filtering out subsumed equations (Sprint A N10 DCE) and
    //    cancellation pair equations (would cause non-convergence)
    rules.extend(unified_rules::generate_equation_rules(language, cat_filter, subsumed_equations, cancellation_equations));

    quote! {
        #(#rules)*
    }
}

/// Generate only reflexivity rules (public for pre-stratum use).
///
/// The pre-stratum needs reflexivity to initialize the eq relations but does not
/// need congruence or user-defined equation rules.
pub fn generate_equation_rules_reflexivity_only(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> TokenStream {
    let rules = generate_reflexivity_rules(language, cat_filter);
    quote! { #(#rules)* }
}

/// Generate reflexivity rules: eq_cat(t, t) for all t in cat
fn generate_reflexivity_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> Vec<TokenStream> {
    language
        .types
        .iter()
        .filter(|lang_type| in_cat_filter(&lang_type.name, cat_filter))
        .map(|lang_type| {
            let rn = relation_names(&lang_type.name);
            let cat_lower = &rn.cat_lower;
            let eq_rel = &rn.eq_rel;
            quote! {
                #eq_rel(t.clone(), t.clone()) <-- #cat_lower(t);
            }
        })
        .collect()
}

/// Generate demand-driven congruence rules for equality.
///
/// Groups constructors by `(result_category, field_types_tuple)` and generates
/// one consolidated rule per group using `match (s, t)` to extract fields.
///
/// Uses thread-local Vec pools for zero-allocation iteration.
///
/// Before: one rule per constructor
/// After: one rule per unique (category, field_types) signature
///
/// For terms that already exist: if their args are equal, then the terms are equal.
/// This is demand-driven and avoids O(N²) term explosion.
fn generate_congruence_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
) -> Vec<TokenStream> {
    // Group constructors by (category, ordered field types)
    // Key: (category_str, vec of field_type_str)
    let mut groups: BTreeMap<(String, Vec<String>), Vec<&GrammarRule>> = BTreeMap::new();

    let var_str = "Var";
    let int_str = "Integer";

    for grammar_rule in &language.terms {
        // Skip categories not in the filter
        if !in_cat_filter(&grammar_rule.category, cat_filter) {
            continue;
        }

        // Sprint 1 DCE: skip dead constructors — their congruence rules can never fire
        if let Some(ref a) = analysis {
            if a.dead_rule_labels.contains(&grammar_rule.label.to_string()) {
                continue;
            }
        }

        // Skip binders (alpha-equivalence is complex)
        if !grammar_rule.bindings.is_empty() {
            continue;
        }

        // Skip collections (built-in equality)
        if grammar_rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }))
        {
            continue;
        }

        // Collect non-terminal argument categories
        let arg_cats: Vec<String> = grammar_rule
            .items
            .iter()
            .filter_map(|item| {
                if let GrammarItem::NonTerminal(cat) = item {
                    Some(cat.to_string())
                } else {
                    None
                }
            })
            .collect();

        if arg_cats.is_empty() {
            continue; // Nullary constructor
        }

        // Skip constructors with Var or Integer arguments
        if arg_cats.iter().any(|c| c == var_str || c == int_str) {
            continue;
        }

        let key = (grammar_rule.category.to_string(), arg_cats);
        groups.entry(key).or_default().push(grammar_rule);
    }

    // Generate one consolidated rule per group.
    // Sprint 3: sort constructors within each group by WFST weight (lower = more frequent first)
    // for better branch prediction in the match arms.
    let mut rules = Vec::with_capacity(groups.len());
    for (pool_counter, ((cat_str, field_type_strs), constructors)) in groups.iter().enumerate() {
        // Weight-sorted constructors: most frequent (lowest weight) first
        let mut sorted_constructors: Vec<&&GrammarRule> = constructors.iter().collect();
        if let Some(ref a) = analysis {
            sorted_constructors.sort_by(|a_rule, b_rule| {
                let a_weight = a.constructor_weights
                    .get(&a_rule.label.to_string())
                    .copied()
                    .unwrap_or(f64::INFINITY);
                let b_weight = a.constructor_weights
                    .get(&b_rule.label.to_string())
                    .copied()
                    .unwrap_or(f64::INFINITY);
                a_weight.total_cmp(&b_weight)
            });
        }
        let constructors = &sorted_constructors;
        let category = format_ident!("{}", cat_str);
        let rn = relation_names(&category);
        let cat_rel = &rn.cat_lower;
        let eq_rel = &rn.eq_rel;

        let arity = field_type_strs.len();

        // Field names for the for-binding
        let s_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("s_f{}", i)).collect();
        let t_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("t_f{}", i)).collect();

        // Build pool arms for (s, t) extraction
        let pool_arms: Vec<PoolArm> = constructors
            .iter()
            .map(|rule| {
                let label = &rule.label;
                let s_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("sf{}", i)).collect();
                let t_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("tf{}", i)).collect();

                // Push a tuple of (s_f0, s_f1, ..., t_f0, t_f1, ...)
                let push_fields: Vec<TokenStream> = s_pat_fields
                    .iter()
                    .chain(t_pat_fields.iter())
                    .map(|f| quote! { #f.as_ref().clone() })
                    .collect();

                PoolArm {
                    pattern: quote! {
                        (#category::#label(#(#s_pat_fields),*), #category::#label(#(#t_pat_fields),*))
                    },
                    pushes: vec![quote! { buf.push((#(#push_fields),*)); }],
                }
            })
            .collect();

        // For-binding: (s_f0, s_f1, ..., t_f0, t_f1, ...)
        let for_bindings: Vec<&Ident> = s_fields.iter().chain(t_fields.iter()).collect();

        // Sprint 4: Equality checks for corresponding field pairs, ordered by
        // category diversity (most diverse first → fail-fast in semi-naive evaluation).
        //
        // Higher category weight (from WFST analysis) → more diverse → check first.
        // Rationale: categories with many constructors produce many distinct terms,
        // making equality checks more likely to fail early, pruning the join.
        //
        // Note: The O(|cat|²) cross-product from `cat(s), cat(t)` is inherent in
        // Ascent's evaluation model — the pool filters same-constructor pairs AFTER
        // the cross-product is formed. This reordering optimizes the constant factor
        // by failing non-matching pairs faster in the eq_checks.
        let mut eq_check_pairs: Vec<(usize, String)> = field_type_strs
            .iter()
            .enumerate()
            .map(|(i, ft_str)| (i, ft_str.clone()))
            .collect();

        // Sort by category weight descending (highest weight = most diverse = check first)
        if let Some(ref a) = analysis {
            eq_check_pairs.sort_by(|(_, ft_a), (_, ft_b)| {
                let w_a = a.category_weights
                    .get(ft_a)
                    .copied()
                    .unwrap_or(0.0);
                let w_b = a.category_weights
                    .get(ft_b)
                    .copied()
                    .unwrap_or(0.0);
                // Higher weight first (descending) → more diverse → fail-fast
                w_b.total_cmp(&w_a)
            });
        }

        let eq_checks: Vec<TokenStream> = eq_check_pairs
            .iter()
            .map(|(i, ft_str)| {
                let eq_arg_rel = format_ident!("eq_{}", ft_str.to_lowercase());
                let sf = &s_fields[*i];
                let tf = &t_fields[*i];
                quote! { #eq_arg_rel(#sf, #tf) }
            })
            .collect();

        // TLS pool with unique name per group
        let pool_name = format_ident!("POOL_{}_EQ_CONG_{}", cat_str.to_uppercase(), pool_counter);

        // Element type is the tuple of all s_fields and t_fields
        let field_types: Vec<TokenStream> = field_type_strs
            .iter()
            .map(|ft_str| {
                let ft = format_ident!("{}", ft_str);
                quote! { #ft }
            })
            .collect();
        // Double the field types: s fields then t fields
        let all_field_types: Vec<&TokenStream> =
            field_types.iter().chain(field_types.iter()).collect();
        let elem_type = quote! { (#(#all_field_types),*) };
        let match_expr = quote! { (s, t) };
        let for_iter = generate_tls_pool_iter(&pool_name, &elem_type, &match_expr, &pool_arms);

        rules.push(quote! {
            #eq_rel(s.clone(), t.clone()) <--
                #cat_rel(s),
                #cat_rel(t),
                for (#(#for_bindings),*) in #for_iter,
                #(#eq_checks),*;
        });
    }

    rules
}
