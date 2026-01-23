//! Equation rules generation for Ascent Datalog.
//!
//! Generates:
//! - Reflexivity rules (eq_cat(t, t) for all t)
//! - Equality congruence rules (if args equal, constructed terms equal)
//! - User-defined equation rules

use crate::logic::rules as unified_rules;
use crate::ast::{grammar::GrammarItem, language::LanguageDef};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
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
            let cat = &lang_type.name;
            let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
            let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
            quote! {
                #eq_rel(t.clone(), t.clone()) <-- #cat_lower(t);
            }
        })
        .collect()
}

/// Generate demand-driven congruence rules for equality.
///
/// For terms that already exist: if their args are equal, then the terms are equal.
/// 
/// Unlike the original approach which synthesizes new terms:
///   eq(Op(x), Op(y)) <-- eq(x, y)  // Creates new terms!
///
/// This approach only equates existing terms:
///   eq(s, t) <-- cat(s), if let Op(x) = s, cat(t), if let Op(y) = t, eq(x, y)
///
/// This is demand-driven and avoids O(N²) term explosion.
fn generate_congruence_rules(language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for grammar_rule in &language.terms {
        let category = &grammar_rule.category;
        let cat_rel = format_ident!("{}", category.to_string().to_lowercase());
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
            continue; // Nullary constructor - no congruence needed
        }

        // Skip constructors with Var or Integer arguments
        if args
            .iter()
            .any(|cat| cat.to_string() == "Var" || cat.to_string() == "Integer")
        {
            continue;
        }

        let label = &grammar_rule.label;
        
        // Generate field names for pattern matching
        let s_fields: Vec<Ident> = (0..args.len()).map(|i| format_ident!("s_f{}", i)).collect();
        let t_fields: Vec<Ident> = (0..args.len()).map(|i| format_ident!("t_f{}", i)).collect();

        // Build the pattern for destructuring
        let s_pattern = quote! { #category::#label(#(ref #s_fields),*) };
        let t_pattern = quote! { #category::#label(#(ref #t_fields),*) };

        // Build equality checks for each field
        let eq_checks: Vec<TokenStream> = args.iter().zip(s_fields.iter().zip(t_fields.iter()))
            .map(|(arg_cat, (s_f, t_f))| {
                let eq_arg_rel = format_ident!("eq_{}", arg_cat.to_string().to_lowercase());
                quote! { #eq_arg_rel(#s_f.as_ref().clone(), #t_f.as_ref().clone()) }
            })
            .collect();

        rules.push(quote! {
            #eq_rel(s.clone(), t.clone()) <--
                #cat_rel(s),
                if let #s_pattern = s,
                #cat_rel(t),
                if let #t_pattern = t,
                #(#eq_checks),*;
        });
    }

    rules
}
