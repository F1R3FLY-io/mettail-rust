//! Equation rules generation for Ascent Datalog.
//!
//! Generates:
//! - Reflexivity rules (eq_cat(t, t) for all t)
//! - Equality congruence rules (if args equal, constructed terms equal)
//! - User-defined equation rules

use super::common::relation_names;
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
pub fn generate_equation_rules(language: &LanguageDef) -> TokenStream {
    let mut rules = Vec::new();

    // 1. Add reflexivity for eq relations
    rules.extend(generate_reflexivity_rules(language));

    // 2. Add demand-driven congruence rules for all constructors
    // These only equate terms that already exist, not synthesize new ones
    rules.extend(generate_congruence_rules(language));

    // 3. Generate user-defined equation rules using unified approach
    rules.extend(unified_rules::generate_equation_rules(language));

    quote! {
        #(#rules)*
    }
}

/// Generate reflexivity rules: eq_cat(t, t) for all t in cat
fn generate_reflexivity_rules(language: &LanguageDef) -> Vec<TokenStream> {
    language
        .types
        .iter()
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
/// Before: one rule per constructor
/// After: one rule per unique (category, field_types) signature
///
/// For terms that already exist: if their args are equal, then the terms are equal.
/// This is demand-driven and avoids O(N²) term explosion.
fn generate_congruence_rules(language: &LanguageDef) -> Vec<TokenStream> {
    // Group constructors by (category, ordered field types)
    // Key: (category_str, vec of field_type_str)
    let mut groups: BTreeMap<(String, Vec<String>), Vec<&GrammarRule>> = BTreeMap::new();

    let var_str = "Var";
    let int_str = "Integer";

    for grammar_rule in &language.terms {
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

    // Generate one consolidated rule per group
    let mut rules = Vec::with_capacity(groups.len());

    for ((cat_str, field_type_strs), constructors) in &groups {
        let category = format_ident!("{}", cat_str);
        let rn = relation_names(&category);
        let cat_rel = &rn.cat_lower;
        let eq_rel = &rn.eq_rel;

        let arity = field_type_strs.len();

        // Field names for the for-binding
        let s_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("s_f{}", i)).collect();
        let t_fields: Vec<Ident> = (0..arity).map(|i| format_ident!("t_f{}", i)).collect();

        // Build match arms for (s, t) extraction
        let match_arms: Vec<TokenStream> = constructors
            .iter()
            .map(|rule| {
                let label = &rule.label;
                let s_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("sf{}", i)).collect();
                let t_pat_fields: Vec<Ident> =
                    (0..arity).map(|i| format_ident!("tf{}", i)).collect();

                // Extractions: s fields then t fields
                let extractions: Vec<TokenStream> = s_pat_fields
                    .iter()
                    .chain(t_pat_fields.iter())
                    .map(|f| quote! { #f.as_ref().clone() })
                    .collect();

                quote! {
                    (#category::#label(#(#s_pat_fields),*), #category::#label(#(#t_pat_fields),*)) =>
                        vec![(#(#extractions),*)],
                }
            })
            .collect();

        // For-binding: (s_f0, s_f1, ..., t_f0, t_f1, ...)
        let for_bindings: Vec<&Ident> = s_fields.iter().chain(t_fields.iter()).collect();

        // Equality checks for corresponding field pairs
        let eq_checks: Vec<TokenStream> = field_type_strs
            .iter()
            .enumerate()
            .map(|(i, ft_str)| {
                let eq_arg_rel = format_ident!("eq_{}", ft_str.to_lowercase());
                let sf = &s_fields[i];
                let tf = &t_fields[i];
                quote! { #eq_arg_rel(#sf, #tf) }
            })
            .collect();

        rules.push(quote! {
            #eq_rel(s.clone(), t.clone()) <--
                #cat_rel(s),
                #cat_rel(t),
                for (#(#for_bindings),*) in (match (s, t) {
                    #(#match_arms)*
                    _ => vec![],
                }).into_iter(),
                #(#eq_checks),*;
        });
    }

    rules
}
