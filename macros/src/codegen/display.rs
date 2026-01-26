// Pretty-printing generation for MeTTaIL theories
//
// This module generates Display trait implementations for AST types,
// allowing them to be pretty-printed back to source syntax.

#![allow(clippy::cmp_owned)]

use crate::ast::{GrammarItem, GrammarRule, TheoryDef};
use crate::codegen::{generate_literal_label, generate_var_label, is_integer_rule, is_var_rule};
use crate::utils::has_native_type;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate Display implementations for all exported categories
pub fn generate_display(theory: &TheoryDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &theory.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate Display impl for each exported category
    let impls: Vec<TokenStream> = theory
        .exports
        .iter()
        .map(|export| {
            let cat_name = &export.name;

            let rules = rules_by_cat
                .get(&cat_name.to_string())
                .map(|v| v.as_slice())
                .unwrap_or(&[]);

            generate_display_impl(cat_name, rules, theory)
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Generate Display impl for a single category
fn generate_display_impl(
    category: &syn::Ident,
    rules: &[&GrammarRule],
    theory: &TheoryDef,
) -> TokenStream {
    let mut match_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_display_arm(rule, theory))
        .collect();

    // Check if Var variant was auto-generated
    // Var variants are now auto-generated for ALL categories (native and non-native)
    let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
    if !has_var_rule {
        let var_arm = generate_auto_var_display_arm(category);
        match_arms.push(var_arm);
    }

    // Check if literal variant was auto-generated for native types
    let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
    if let Some(native_type) = has_native_type(category, theory) {
        if !has_integer_rule {
            let literal_label = generate_literal_label(native_type);
            match_arms.push(quote! {
                #category::#literal_label(val) => write!(f, "{}", val)
            });
        }
    }

    // Add Assign display arm: <var_name> = <rhs>
    match_arms.push(quote! {
        #category::Assign(ord_var, rhs) => {
            let var_name = match &ord_var.0 {
                mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
                mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
            };
            write!(f, "{} = {}", var_name, rhs)
        }
    });

    quote! {
        impl std::fmt::Display for #category {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#match_arms),*
                }
            }
        }
    }
}

/// Generate a match arm for displaying a single constructor
fn generate_display_arm(rule: &GrammarRule, theory: &TheoryDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Check if this has binders
    if !rule.bindings.is_empty() {
        return generate_binder_display_arm(rule, theory);
    }

    // Build parameter map for HOL syntax
    let param_map: std::collections::HashMap<String, syn::Ident> = rule
        .parameters
        .iter()
        .map(|p| (p.name.to_string(), p.param_type.clone()))
        .collect();

    // Collect resolved types for parameters (we'll store them separately)
    let resolved_types: Vec<syn::Ident> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => {
                // HOL syntax: resolve parameter names to their types
                let resolved_ident = param_map
                    .get(&ident.to_string())
                    .cloned()
                    .unwrap_or_else(|| ident.clone());
                Some(resolved_ident)
            },
            _ => None,
        })
        .collect();

    // Collect field names and their types (using references into resolved_types)
    let mut resolved_idx = 0;
    let fields: Vec<(String, Option<&syn::Ident>)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal(_) => {
                let result = Some((format!("f{}", i), resolved_types.get(resolved_idx)));
                resolved_idx += 1;
                result
            },
            GrammarItem::Collection { .. } => Some((format!("f{}", i), None)), // Collection field
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant - just print terminals
        let output = format_terminals(rule);
        quote! {
            #category::#label => write!(f, #output)
        }
    } else {
        // Tuple variant - pattern match fields
        let field_names: Vec<syn::Ident> = fields
            .iter()
            .map(|(name, _)| syn::Ident::new(name, proc_macro2::Span::call_site()))
            .collect();

        // Check if any fields are Var - they need special handling
        let has_var = fields.iter().any(|(_, nt_opt)| {
            if let Some(nt) = nt_opt {
                nt.to_string() == "Var"
            } else {
                false
            }
        });

        if has_var {
            // Generate code that extracts names from Vars
            let mut format_parts = Vec::new();
            let mut format_args_tokens = Vec::new();
            let mut part_str = String::new();
            let mut field_iter = fields.iter().zip(field_names.iter());

            for item in &rule.items {
                match item {
                    GrammarItem::Terminal(term) => {
                        let escaped = term.replace("{", "{{").replace("}", "}}");
                        part_str.push_str(&escaped);
                    },
                    GrammarItem::NonTerminal(nt) if nt.to_string() == "Var" => {
                        if !part_str.is_empty() {
                            format_parts.push(part_str.clone());
                            part_str.clear();
                        }
                        if let Some((_, field_name)) = field_iter.next() {
                            format_parts.push("{}".to_string());
                            // Var fields are always OrdVar, need to extract the variable name
                            format_args_tokens.push(quote! {
                                match &(#field_name).0 {
                                    mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
                                    mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_"),
                                }
                            });
                        }
                    },
                    GrammarItem::NonTerminal(_) => {
                        if !part_str.is_empty() {
                            format_parts.push(part_str.clone());
                            part_str.clear();
                        }
                        if let Some((_, field_name)) = field_iter.next() {
                            format_parts.push("{}".to_string());
                            format_args_tokens.push(quote! { #field_name });
                        }
                    },
                    _ => {},
                }
            }

            if !part_str.is_empty() {
                format_parts.push(part_str);
            }

            let format_str = format_parts.join("");

            quote! {
                #category::#label(#(#field_names),*) => write!(f, #format_str, #(#format_args_tokens),*)
            }
        } else {
            // No Var fields - use simple approach
            let (format_str, format_args) = build_format_string(rule, &fields);

            quote! {
                #category::#label(#(#field_names),*) => write!(f, #format_str, #(#format_args),*)
            }
        }
    }
}

/// Generate display for a constructor with binders
fn generate_binder_display_arm(rule: &GrammarRule, _theory: &TheoryDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Collect regular fields (not binder, not body)
    let mut regular_fields = Vec::new();
    let mut has_scope = false;
    let mut field_idx = 0;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::NonTerminal(_) if i == body_idx => {
                has_scope = true;
            },
            GrammarItem::NonTerminal(_) => {
                regular_fields.push(format!("f{}", field_idx));
                field_idx += 1;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Skip - it's in the scope
            },
            _ => {},
        }
    }

    // Build pattern: regular fields + scope
    let mut all_fields = regular_fields.clone();
    if has_scope {
        all_fields.push("scope".to_string());
    }

    let field_idents: Vec<syn::Ident> = all_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Build format string with placeholders for all parts
    let format_str = build_binder_format_string_simple(rule);

    // Build format args: regular fields, then binder name, then body
    let regular_field_idents: Vec<syn::Ident> = regular_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    quote! {
        #category::#label(#(#field_idents),*) => {
            // Use unbind() to get fresh variables with proper names for display
            let (binder, body) = scope.clone().unbind();
            let binder_name = binder.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
            write!(f, #format_str, #(#regular_field_idents,)* binder_name, body)
        }
    }
}

/// Build format string and args for a rule (no Var fields)
fn build_format_string(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
) -> (String, Vec<TokenStream>) {
    let mut format_str = String::new();
    let mut format_args = Vec::new();
    let mut field_iter = fields.iter();

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(term) => {
                // Escape braces in format strings
                let escaped = term.replace("{", "{{").replace("}", "}}");
                format_str.push_str(&escaped);
            },
            GrammarItem::NonTerminal(_) => {
                // Regular fields
                if let Some((name, _)) = field_iter.next() {
                    format_str.push_str("{}");
                    let field_ident = syn::Ident::new(name, proc_macro2::Span::call_site());
                    format_args.push(quote! { #field_ident });
                }
            },
            GrammarItem::Collection { separator, delimiters, .. } => {
                // Collection field - format with custom separator
                if let Some((name, _)) = field_iter.next() {
                    format_str.push_str("{}");
                    let field_ident = syn::Ident::new(name, proc_macro2::Span::call_site());

                    // Generate custom formatting for collection with separator
                    let sep = separator.clone();
                    if let Some((open, close)) = delimiters {
                        // With delimiters: {elem1 | elem2 | elem3}
                        format_args.push(quote! {
                            {
                                let mut s = String::from(#open);
                                let items: Vec<String> = #field_ident.iter().map(|(elem, count)| {
                                    // For multisets, repeat element by count
                                    (0..count).map(|_| elem.to_string()).collect::<Vec<_>>().join(&format!(" {} ", #sep))
                                }).collect();
                                if !items.is_empty() {
                                    s.push_str(&items.join(&format!(" {} ", #sep)));
                                }
                                s.push_str(#close);
                                s
                            }
                        });
                    } else {
                        // Without delimiters
                        format_args.push(quote! {
                            {
                                let items: Vec<String> = #field_ident.iter().map(|(elem, count)| {
                                    (0..count).map(|_| elem.to_string()).collect::<Vec<_>>().join(&format!(" {} ", #sep))
                                }).collect();
                                items.join(&format!(" {} ", #sep))
                            }
                        });
                    }
                }
            },
            GrammarItem::Binder { .. } => {
                // Binders are handled separately in binder rules
            },
        }
    }

    (format_str, format_args)
}

/// Build format string for a rule with binders (simplified)
fn build_binder_format_string_simple(rule: &GrammarRule) -> String {
    let mut format_str = String::new();

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    let mut prev_was_nonterminal = false;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::Terminal(term) => {
                // Escape braces in format strings
                let escaped = term.replace("{", "{{").replace("}", "}}");
                format_str.push_str(&escaped);
                prev_was_nonterminal = false;
            },
            GrammarItem::NonTerminal(_) if i == body_idx => {
                // Body - will be provided from scope.unbind()
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::NonTerminal(_) => {
                // Regular field
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Collection { .. } => {
                // Collection field
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Binder - will be provided from scope.unbind()
                if prev_was_nonterminal {
                    format_str.push(' ');
                }
                format_str.push_str("{}");
                prev_was_nonterminal = true;
            },
            GrammarItem::Binder { .. } => {},
        }
    }

    format_str
}

/// Format just the terminals for a unit variant
fn format_terminals(rule: &GrammarRule) -> String {
    rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::Terminal(term) => Some(term.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Generate display match arm for an auto-generated Var variant
fn generate_auto_var_display_arm(category: &syn::Ident) -> TokenStream {
    // Generate Var label: first letter + "Var"
    let var_label = generate_var_label(category);

    quote! {
        #category::#var_label(var) => {
            match &var.0 {
                mettail_runtime::Var::Free(fv) => {
                    let name = fv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    write!(f, "{}", name)
                }
                mettail_runtime::Var::Bound(bv) => {
                    let name = bv.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    write!(f, "{}", name)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    #[test]
    fn test_display_generation() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Expr),
                native_type: None,
            }],
            terms: vec![
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(Zero),
                    category: parse_quote!(Expr),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                },
                GrammarRule {
                    parameters: Vec::new(),
                    return_type: None,
                    rust_code: None,
                    eval_mode: None,
                    label: parse_quote!(Add),
                    category: parse_quote!(Expr),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Expr)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Expr)),
                    ],
                    bindings: vec![],
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let display_impl = generate_display(&theory);
        let code = display_impl.to_string();

        println!("Generated Display:\n{}", code);

        assert!(code.contains("impl std :: fmt :: Display for Expr"));
        assert!(code.contains("Expr :: Zero"));
        assert!(code.contains("Expr :: Add"));
    }
}
