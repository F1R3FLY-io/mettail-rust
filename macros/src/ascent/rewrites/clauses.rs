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

use super::generate_ascent_pattern;
use super::rhs::generate_ascent_rhs;
use crate::ascent::congruence::extract_category;
use crate::ast::{Expr, RewriteRule, TheoryDef};
use crate::utils::has_native_type;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::Ident;

/// Generate Ascent clauses for rewrite rules (for equational matching)
/// This is the new approach that allows duplicate variables to use eq_cat() relations
pub fn generate_rewrite_clauses(theory: &TheoryDef) -> Vec<TokenStream> {
    use crate::ascent::congruence;

    let mut all_clauses = Vec::new();

    // Find which categories are covered by collection congruences
    let collection_cong_categories =
        congruence::find_collection_congruence_element_categories(theory);

    for (_rule_idx, rule) in theory.rewrites.iter().enumerate() {
        // Skip congruence rules (handled elsewhere)
        if rule.premise.is_some() {
            continue;
        }

        // Check if this base rewrite's LHS involves a collection pattern for a category
        // that's covered by a collection congruence
        let is_covered_by_congruence = if congruence::contains_collection_pattern(&rule.left) {
            // This rule has a collection pattern in its LHS
            // We only skip if the ROOT of the LHS is a collection constructor that's covered
            // by a collection congruence.
            //
            // For example:
            // - (PPar {(PIn ...), (POut ...)}) => ... should be SKIPPED (root is PPar collection)
            // - (PAmb M (PPar {...})) => ... should NOT be skipped (root is PAmb, not a collection)

            if let Expr::Apply { constructor, .. } = &rule.left {
                // Check if this constructor has a collection field
                if let Some(elem_cat) =
                    congruence::get_constructor_collection_element_type(constructor, theory)
                {
                    // Root is a collection constructor
                    // Check if this element category is covered by a collection congruence
                    collection_cong_categories.contains(&elem_cat)
                } else {
                    // Root is not a collection constructor, but may contain nested collections
                    // Generate the rule directly (don't skip)
                    false
                }
            } else {
                false
            }
        } else {
            false
        };

        if is_covered_by_congruence {
            // Skip this rule - it will be handled by congruence-driven projection
            continue;
        }

        // OLD PATH: For non-collection patterns or uncovered categories
        all_clauses.push(generate_rewrite_clause(rule, theory));
    }

    all_clauses
}

/// Generate a single rewrite rule as an Ascent clause
/// Example output:
/// rw_proc(s, t) <--
///     proc(s),
///     if let Proc::PPar(p_in, p_out) = s,
///     if let Proc::PInput(chan1, scope) = &**p_in,
///     if let Proc::POutput(chan2, q) = &**p_out,
///     eq_name((**chan1).clone(), (**chan2).clone()),
///     let (x, p) = scope.clone().unbind(),
///     if !p.contains_free(&x),
///     let t = p.substitute(&x, &Name::NQuote((**q).clone()));
fn generate_rewrite_clause(rule: &RewriteRule, theory: &TheoryDef) -> TokenStream {
    let category = extract_category(&rule.left, theory)
        .expect("Failed to extract category from rewrite rule LHS");
    let cat_lower = quote::format_ident!("{}", category.to_string().to_lowercase());
    let rw_rel = quote::format_ident!("rw_{}", category.to_string().to_lowercase());

    // Track variable occurrences for duplicate detection
    let mut var_occurrences: HashMap<String, Vec<usize>> = HashMap::new();
    let mut occurrence_idx = 0;
    collect_variable_occurrences(&rule.left, &mut var_occurrences, &mut occurrence_idx);

    // Identify which variables appear multiple times (need equational matching)
    let duplicate_vars: std::collections::HashSet<String> = var_occurrences
        .into_iter()
        .filter(|(_, occurrences)| occurrences.len() > 1)
        .map(|(var_name, _)| var_name)
        .collect();

    // Generate pattern matching clauses
    let mut bindings: HashMap<String, TokenStream> = HashMap::new();
    let mut variable_categories: HashMap<String, Ident> = HashMap::new();
    let mut equational_checks: Vec<TokenStream> = Vec::new();
    let mut clauses = Vec::new();

    // Start with proc(s) clause
    clauses.push(quote! { #cat_lower(s) });

    // Generate pattern matching with category tracking
    let lhs_category = extract_category(&rule.left, theory)
        .expect("Failed to extract category from rewrite rule LHS");
    generate_ascent_pattern(
        &rule.left,
        &quote::format_ident!("s"),
        &lhs_category,
        theory,
        &mut bindings,
        &mut variable_categories,
        &mut clauses,
        &duplicate_vars,
        &mut equational_checks,
    );

    // Add equational checks for duplicate variables
    clauses.extend(equational_checks);

    // Add condition checks (freshness or environment queries)
    for condition in &rule.conditions {
        match condition {
            crate::ast::Condition::Freshness(freshness) => {
                let var_name = freshness.var.to_string();
                let term_name = match &freshness.term {
                    crate::ast::FreshnessTarget::Var(id) => id.to_string(),
                    crate::ast::FreshnessTarget::CollectionRest(id) => id.to_string(),
                };

                let var_binding = bindings.get(&var_name).unwrap_or_else(|| {
                    panic!(
                        "Freshness variable '{}' not bound. Available bindings: {:?}",
                        var_name,
                        bindings.keys().collect::<Vec<_>>()
                    )
                });
                let term_binding = bindings.get(&term_name).unwrap_or_else(|| {
                    panic!(
                        "Freshness term '{}' not bound. Available bindings: {:?}",
                        term_name,
                        bindings.keys().collect::<Vec<_>>()
                    )
                });

                clauses.push(quote! {
                    if is_fresh(&#var_binding, &#term_binding)
                });
            },
            crate::ast::Condition::EnvQuery { relation, args } => {
                // Generate Ascent clause that queries the environment relation
                // Example: if env_var(x, v) then (VarRef x) => (NumLit v)
                // Pattern: (VarRef x) binds x to OrdVar
                // Condition: env_var(x, v) means query env_var with x's name, bind v to the value
                // RHS: (NumLit v) uses v which is bound from the query

                if args.len() < 2 {
                    panic!("EnvQuery condition requires at least 2 arguments (variable name and value)");
                }

                let var_arg = &args[0]; // x - bound from LHS pattern
                let val_arg = &args[1]; // v - will be bound from env_var query

                let var_binding = bindings.get(&var_arg.to_string()).unwrap_or_else(|| {
                    panic!(
                        "EnvQuery variable '{}' not bound. Available bindings: {:?}",
                        var_arg,
                        bindings.keys().collect::<Vec<_>>()
                    )
                });

                // Extract variable name from OrdVar
                // OrdVar contains Var::Free(FreeVar) which has pretty_name
                let var_name_extraction = quote! {
                    {
                        let var_name_opt = match #var_binding {
                            mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                fv.pretty_name.clone()
                            }
                            _ => None
                        };
                        var_name_opt
                    }
                };

                // Generate clause: env_var(var_name, val) where:
                // - var_name is extracted from the OrdVar (x binding)
                // - val is bound from the query and will be used in RHS as v
                let val_binding_name = format_ident!("{}", val_arg.to_string());
                clauses.push(quote! {
                    if let Some(var_name) = #var_name_extraction,
                    #relation(var_name, #val_binding_name)
                });

                // Add val_binding to bindings so RHS can use it
                // Note: Ascent binds relation values by reference, so we dereference here
                // since native types like i32 need to be passed by value to constructors
                bindings.insert(val_arg.to_string(), quote! { *#val_binding_name });
            },
        }
    }

    // Generate RHS
    let rhs = generate_ascent_rhs(&rule.right, &bindings, theory);

    // Only call normalize() if the category has collection constructors
    if category_has_collections(&lhs_category, theory) {
        clauses.push(quote! { let t = (#rhs).normalize() });
    } else {
        clauses.push(quote! { let t = #rhs });
    }

    // Generate main rewrite clause
    let main_clause = quote! {
        #rw_rel(s, t) <--
            #(#clauses),*;
    };

    // Generate fact creation clauses for env_actions
    let mut fact_clauses = Vec::new();
    for action in &rule.env_actions {
        let crate::ast::EnvAction::CreateFact { relation, args } = action;
        let rel_ident = format_ident!("{}", relation);

        // Build fact creation clause body - we need pattern matching but not RHS construction
        // Only take clauses before "let t = ..." (the pattern matching part)
        let mut fact_body_clauses: Vec<TokenStream> = clauses
            .iter()
            .take_while(|c| {
                let clause_str = c.to_string();
                !clause_str.contains("let t =")
            })
            .cloned()
            .collect();

        let mut fact_args = Vec::new();
        let mut var_name_extractions = Vec::new();

        for arg_name in args {
            let binding = bindings
                .get(&arg_name.to_string())
                .expect(&format!("Variable '{}' not bound in rewrite rule", arg_name));

            // Check if this is a Var type (need to extract name from OrdVar)
            if variable_categories
                .get(&arg_name.to_string())
                .map(|cat| cat.to_string() == "Var")
                .unwrap_or(false)
            {
                // Extract variable name from OrdVar
                // The binding is created from pattern matching: for Var fields, the binding is OrdVar.clone()
                // So #binding is already OrdVar, we can match it directly
                let var_name_ident = format_ident!("{}_name", arg_name);
                let var_name_extraction = quote! {
                    if let Some(#var_name_ident) = {
                        let var_name_opt = match #binding {
                            mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                fv.pretty_name.clone()
                            }
                            _ => None
                        };
                        var_name_opt
                    }
                };
                var_name_extractions.push(var_name_extraction);
                fact_args.push(quote! { #var_name_ident });
            } else {
                // Check if this is a native type (like i32)
                let is_native = if let Some(cat) = variable_categories.get(&arg_name.to_string()) {
                    cat.to_string() == "Integer" || has_native_type(cat, theory).is_some()
                } else {
                    false
                };

                if is_native {
                    // Native type - binding is already the value (e.g., i32)
                    fact_args.push(quote! { #binding });
                } else {
                    // Non-native type - use binding as-is
                    fact_args.push(quote! { #binding });
                }
            }
        }

        // Add variable name extractions to the body clauses
        fact_body_clauses.extend(var_name_extractions);

        // Generate fact creation clause
        // This creates facts when the pattern matches
        fact_clauses.push(quote! {
            #rel_ident(#(#fact_args),*) <--
                #(#fact_body_clauses),*;
        });
    }

    quote! {
        #main_clause
        #(#fact_clauses)*
    }
}

/// Check if a category has any collection constructors
fn category_has_collections(category: &Ident, theory: &TheoryDef) -> bool {
    use crate::ast::GrammarItem;

    theory.terms.iter().any(|rule| {
        rule.category == *category
            && rule
                .items
                .iter()
                .any(|item| matches!(item, GrammarItem::Collection { .. }))
    })
}

/// Collect all variable occurrences in an expression (for duplicate detection)
fn collect_variable_occurrences(
    expr: &Expr,
    occurrences: &mut HashMap<String, Vec<usize>>,
    idx: &mut usize,
) {
    match expr {
        Expr::Var(var) => {
            let var_name = var.to_string();
            occurrences
                .entry(var_name)
                .or_insert_with(Vec::new)
                .push(*idx);
            *idx += 1;
        },
        Expr::Apply { args, .. } => {
            for arg in args {
                collect_variable_occurrences(arg, occurrences, idx);
            }
        },
        Expr::Subst { term, .. } => {
            collect_variable_occurrences(term, occurrences, idx);
        },
        Expr::CollectionPattern { elements, rest, .. } => {
            for elem in elements {
                collect_variable_occurrences(elem, occurrences, idx);
            }
            if let Some(rest_var) = rest {
                let var_name = rest_var.to_string();
                occurrences
                    .entry(var_name)
                    .or_insert_with(Vec::new)
                    .push(*idx);
                *idx += 1;
            }
        },
        // Lambda - collect from body (binder is bound, not an occurrence)
        Expr::Lambda { body, .. } | Expr::MultiLambda { body, .. } => {
            collect_variable_occurrences(body, occurrences, idx);
        },
    }
}
