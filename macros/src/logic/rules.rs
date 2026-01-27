//! Unified rule generation for equations and rewrites.
//!
//! This module provides `generate_rule_clause`, the core abstraction that
//! generates Ascent Datalog clauses from Pattern-based rules.
//!
//! Key insight: Equations and rewrites differ only in:
//! 1. The relation they write to (`eq_cat` vs `rw_cat`)
//! 2. Whether they're bidirectional (equations) or directional (rewrites)

use crate::ast::pattern::{Pattern, AscentClauses, VariableBinding};
use crate::ast::language::{LanguageDef, Condition, FreshnessCondition, FreshnessTarget};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;

/// Unified rule generator for both equations and rewrites.
///
/// # Arguments
/// * `left` - LHS pattern to match
/// * `right` - RHS pattern to construct
/// * `conditions` - Freshness/env conditions
/// * `relation_name` - Target relation (`eq_proc` or `rw_proc`)
/// * `theory` - Theory definition
///
/// # Example
/// For equation `(PDrop (NQuote P)) == P`:
/// ```text
/// eq_proc(s.clone(), t) <--
///     proc(s),
///     if let Proc::PDrop(f0) = s,
///     let f0_deref = &**f0,
///     if let Name::NQuote(f0_f0) = f0_deref,
///     let p = f0_f0.clone(),
///     let t = p.clone();
/// ```
pub fn generate_rule_clause(
    left: &Pattern,
    right: &Pattern,
    conditions: &[Condition],
    relation_name: &syn::Ident,
    language: &LanguageDef,
) -> TokenStream {
    // 1. Determine category from LHS
    let category = left.category(language)
        .expect("Cannot determine category from LHS pattern");
    generate_rule_clause_with_category(left, right, conditions, relation_name, category, language)
}

/// Generate a rule clause with an explicitly provided category.
/// Useful when the LHS is a variable and category must come from context.
pub fn generate_rule_clause_with_category(
    left: &Pattern,
    right: &Pattern,
    conditions: &[Condition],
    relation_name: &syn::Ident,
    category: &syn::Ident,
    language: &LanguageDef,
) -> TokenStream {
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    
    // 2. Find duplicate variables for equational matching
    let mut all_vars = left.var_occurrences();
    for (var, count) in right.var_occurrences() {
        *all_vars.entry(var).or_insert(0) += count;
    }
    let duplicate_vars: HashSet<_> = all_vars.into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(var, _)| var)
        .collect();
    
    // 3. Generate LHS matching clauses
    let lhs_var = format_ident!("s");
    let lhs_clauses = left.to_ascent_clauses(&lhs_var, category, language, &duplicate_vars);
    
    // 4. Generate condition checks and collect env query bindings
    let (condition_clauses, env_bindings) = generate_condition_clauses(conditions, &lhs_clauses);
    
    // 5. Merge LHS bindings with env query bindings for RHS generation
    let mut all_bindings = lhs_clauses.bindings.clone();
    all_bindings.extend(env_bindings);
    
    // 6. Generate RHS construction
    let rhs_var = format_ident!("t");
    let rhs_expr = right.to_ascent_rhs(&all_bindings, language);
    
    // 7. Assemble the rule
    let clauses = &lhs_clauses.clauses;
    let eq_checks = &lhs_clauses.equational_checks;
    
    // Wrap RHS expression with .normalize() for immediate beta-reduction
    if condition_clauses.is_empty() && eq_checks.is_empty() {
        quote! {
            #relation_name(#lhs_var.clone(), #rhs_var) <--
                #cat_lower(#lhs_var),
                #(#clauses,)*
                let #rhs_var = (#rhs_expr).normalize();
        }
    } else if eq_checks.is_empty() {
        quote! {
            #relation_name(#lhs_var.clone(), #rhs_var) <--
                #cat_lower(#lhs_var),
                #(#clauses,)*
                #(#condition_clauses,)*
                let #rhs_var = (#rhs_expr).normalize();
        }
    } else if condition_clauses.is_empty() {
        quote! {
            #relation_name(#lhs_var.clone(), #rhs_var) <--
                #cat_lower(#lhs_var),
                #(#clauses,)*
                #(#eq_checks,)*
                let #rhs_var = (#rhs_expr).normalize();
        }
    } else {
        quote! {
            #relation_name(#lhs_var.clone(), #rhs_var) <--
                #cat_lower(#lhs_var),
                #(#clauses,)*
                #(#eq_checks,)*
                #(#condition_clauses,)*
                let #rhs_var = (#rhs_expr).normalize();
        }
    }
}

/// Generate condition clauses from freshness and env conditions.
/// 
/// For EnvQuery conditions like `if env_var(x, v) then`:
/// - First arg (x) is looked up from LHS bindings (typically OrdVar)
/// - Variable name is extracted from OrdVar
/// - Second arg (v) is bound from the relation query result
/// 
/// Returns: (clauses, env_bindings) where env_bindings maps val_arg names to dereferenced values
fn generate_condition_clauses(
    conditions: &[Condition],
    lhs_clauses: &AscentClauses,
) -> (Vec<TokenStream>, std::collections::HashMap<String, VariableBinding>) {
    let mut clauses = Vec::new();
    let mut env_bindings = std::collections::HashMap::new();
    
    // Get a default lang_type from existing bindings
    let default_lang_type = lhs_clauses.bindings.values().next()
        .map(|b| b.lang_type.clone())
        .unwrap_or_else(|| format_ident!("Unknown"));
    
    for cond in conditions {
        match cond {
            Condition::Freshness(freshness) => {
                if let Some(clause) = generate_freshness_clause(freshness, lhs_clauses) {
                    clauses.push(clause);
                }
            }
            Condition::EnvQuery { relation, args } => {
                if args.len() < 2 {
                    panic!("EnvQuery condition requires at least 2 arguments (variable name and value)");
                }
                
                let var_arg = &args[0]; // The OrdVar to extract name from
                let val_arg = &args[1]; // The result to bind
                
                // Get binding for var_arg from LHS
                let var_arg_name = var_arg.to_string();
                let var_binding_expr = lhs_clauses.bindings.get(&var_arg_name)
                    .map(|b| b.expression.clone())
                    .unwrap_or_else(|| quote! { #var_arg });
                
                // Generate code to extract variable name from OrdVar
                let var_name_extraction = quote! {
                    {
                        let var_name_opt = match #var_binding_expr {
                            mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv)) => {
                                fv.pretty_name.clone()
                            }
                            _ => None
                        };
                        var_name_opt
                    }
                };
                
                // val_arg will be bound from the relation query (as a reference)
                let val_binding_name = format_ident!("{}", val_arg.to_string());
                clauses.push(quote! {
                    if let Some(var_name) = #var_name_extraction,
                    #relation(var_name, #val_binding_name)
                });
                
                // Add to env_bindings with dereference - Ascent binds relation values by reference
                // So if env_var is (String, i32), val_binding_name is &i32, and we need *val_binding_name
                env_bindings.insert(val_arg.to_string(), VariableBinding {
                    expression: quote! { *#val_binding_name },
                    lang_type: default_lang_type.clone(),
                    scope_kind: None,
                });
            }
        }
    }
    
    (clauses, env_bindings)
}

/// Generate a freshness condition clause.
fn generate_freshness_clause(
    freshness: &FreshnessCondition,
    lhs_clauses: &AscentClauses,
) -> Option<TokenStream> {
    let var_name = freshness.var.to_string();
    let var_binding = &lhs_clauses.bindings.get(&var_name)?.expression;
    
    match &freshness.term {
        FreshnessTarget::Var(term_var) => {
            let term_name = term_var.to_string();
            let term_binding = &lhs_clauses.bindings.get(&term_name)?.expression;
            
            // Generate: if !term_binding.free_vars().contains(&var_binding)
            // var_binding is a FreeVar<String> from a binder
            // free_vars() returns HashSet<FreeVar<String>>
            Some(quote! {
                if !mettail_runtime::BoundTerm::free_vars(&#term_binding).contains(&#var_binding)
            })
        }
        FreshnessTarget::CollectionRest(rest_var) => {
            let rest_name = rest_var.to_string();
            let rest_binding = &lhs_clauses.bindings.get(&rest_name)?.expression;
            
            // Check freshness in all elements of the rest collection
            // var_binding is a FreeVar<String> from a binder
            Some(quote! {
                if #rest_binding.clone().iter().all(|(elem, _)| !mettail_runtime::BoundTerm::free_vars(elem).contains(&#var_binding))
            })
        }
    }
}

/// Generate all equation rules for a theory.
pub fn generate_equation_rules(language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    
    for eq in &language.equations {
        // Determine category - try LHS first, then RHS
        let category = eq.left.category(language)
            .or_else(|| eq.right.category(language));
            
        if let Some(category) = category {
            let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
            
            // Convert freshness conditions to Condition enum
            let conditions: Vec<Condition> = eq.conditions.iter()
                .map(|f| Condition::Freshness(f.clone()))
                .collect();
            
            // Forward direction: left => right
            rules.push(generate_rule_clause_with_category(
                &eq.left,
                &eq.right,
                &conditions,
                &eq_rel,
                category,
                language,
            ));
            
            // Backward direction: right => left (equations are symmetric)
            rules.push(generate_rule_clause_with_category(
                &eq.right,
                &eq.left,
                &conditions,
                &eq_rel,
                category,
                language,
            ));
        }
    }
    
    rules
}

/// Generate all base rewrite rules for a theory.
/// (Congruence rules are handled separately.)
pub fn generate_rewrite_rules(language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    
    for rw in &language.rewrites {
        // Skip congruence rules (those with premise)
        if rw.premise.is_some() {
            continue;
        }
        
        // Determine category from LHS
        if let Some(category) = rw.left.category(language) {
            let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
            
            rules.push(generate_rule_clause(
                &rw.left,
                &rw.right,
                &rw.conditions,
                &rw_rel,
                language,
            ));
        }
    }
    
    rules
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::pattern::PatternTerm;
    use quote::format_ident;
    
    #[test]
    fn test_duplicate_var_detection() {
        // Pattern: (Cons P P) - P appears twice
        let pattern = Pattern::Term(PatternTerm::Apply {
            constructor: format_ident!("Cons"),
            args: vec![
                Pattern::Term(PatternTerm::Var(format_ident!("P"))),
                Pattern::Term(PatternTerm::Var(format_ident!("P"))),
            ],
        });
        
        let duplicates = pattern.duplicate_vars();
        assert!(duplicates.contains("P"));
        assert_eq!(duplicates.len(), 1);
    }
}
