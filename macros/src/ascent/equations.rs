//! Equation rules generation for Ascent Datalog.
//!
//! Generates:
//! - Reflexivity rules (eq_cat(t, t) for all t)
//! - Equality congruence rules (if args equal, constructed terms equal)
//! - User-defined equation rules

use crate::ascent::rules as unified_rules;
use crate::ast::{grammar::GrammarItem, theory::TheoryDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

/// Main entry point: Generate all equation rules.
///
/// This includes:
/// 1. Reflexivity rules for all categories
/// 2. Equality congruence for all constructors
/// 3. User-defined equations
pub fn generate_equation_rules(theory: &TheoryDef) -> TokenStream {
    let mut rules = Vec::new();

    // 1. Add reflexivity for eq relations
    rules.extend(generate_reflexivity_rules(theory));

    // 2. Add congruence rules for all constructors
    rules.extend(generate_congruence_rules(theory));

    // 3. Generate user-defined equation rules using unified approach
    rules.extend(unified_rules::generate_equation_rules(theory));

    quote! {
        #(#rules)*
    }
}

/// Generate reflexivity rules: eq_cat(t, t) for all t in cat
fn generate_reflexivity_rules(theory: &TheoryDef) -> Vec<TokenStream> {
    theory
        .exports
        .iter()
        .map(|export| {
            let cat = &export.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
            quote! {
                #eq_rel(t.clone(), t.clone()) <-- #cat_lower(t);
            }
        })
        .collect()
}

/// Generate congruence rules for equality.
///
/// For each constructor: if all args are equal, then constructed terms are equal.
/// Example: eq_proc(Cons(x), Cons(y)) <-- name(x), name(y), eq_name(x, y);
fn generate_congruence_rules(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for grammar_rule in &theory.terms {
        let category = &grammar_rule.category;
        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

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

        // Collect non-terminal arguments
        let args: Vec<&Ident> = grammar_rule
            .items
            .iter()
            .filter_map(|item| {
                if let GrammarItem::NonTerminal(cat) = item {
                    Some(cat)
                } else {
                    None
                }
            })
            .collect();

        if args.is_empty() {
            continue; // Nullary constructor
        }

        // Skip constructors with Var or Integer arguments
        if args
            .iter()
            .any(|cat| cat.to_string() == "Var" || cat.to_string() == "Integer")
        {
            continue;
        }

        // Generate variable names
        let lhs_vars: Vec<Ident> = (0..args.len()).map(|i| format_ident!("x{}", i)).collect();
        let rhs_vars: Vec<Ident> = (0..args.len()).map(|i| format_ident!("y{}", i)).collect();

        // Generate body clauses
        let mut body_clauses = Vec::new();
        for (cat, (lhs, rhs)) in args.iter().zip(lhs_vars.iter().zip(rhs_vars.iter())) {
            let cat_rel = format_ident!("{}", cat.to_string().to_lowercase());
            let eq_arg_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
            body_clauses.push(quote! { #cat_rel(#lhs) });
            body_clauses.push(quote! { #cat_rel(#rhs) });
            body_clauses.push(quote! { #eq_arg_rel(#lhs.clone(), #rhs.clone()) });
        }

        // Generate head
        let lhs_boxed: Vec<TokenStream> = lhs_vars
            .iter()
            .map(|v| quote! { Box::new(#v.clone()) })
            .collect();
        let rhs_boxed: Vec<TokenStream> = rhs_vars
            .iter()
            .map(|v| quote! { Box::new(#v.clone()) })
            .collect();
        let label = &grammar_rule.label;

        rules.push(quote! {
            #eq_rel(
                #category::#label(#(#lhs_boxed),*),
                #category::#label(#(#rhs_boxed),*)
            ) <-- #(#body_clauses),*;
        });
    }

    rules
}
