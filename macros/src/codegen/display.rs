// Pretty-printing generation for MeTTaIL theories
//
// This module generates Display trait implementations for AST types,
// allowing them to be pretty-printed back to source syntax.

#![allow(clippy::cmp_owned)]

use crate::ast::{GrammarItem, GrammarRule, TheoryDef, SyntaxToken, TermParam};
use crate::codegen::{generate_var_label, is_var_rule};
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
    // Skip for native types - they don't have Var variants
    let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
    if !has_var_rule && has_native_type(category, theory).is_none() {
        let var_arm = generate_auto_var_display_arm(category);
        match_arms.push(var_arm);
    }

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

    // Check if this uses new syntax_pattern - generate display from pattern
    if let (Some(syntax_pattern), Some(term_context)) = (&rule.syntax_pattern, &rule.term_context) {
        return generate_syntax_pattern_display_arm(rule, syntax_pattern, term_context);
    }

    // Check if this has binders (old syntax)
    if !rule.bindings.is_empty() {
        return generate_binder_display_arm(rule, theory);
    }

    // Collect field names and their types
    let fields: Vec<(String, Option<&syn::Ident>)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal(ident) => Some((format!("f{}", i), Some(ident))),
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

/// Generate display for a constructor using new syntax_pattern
fn generate_syntax_pattern_display_arm(
    rule: &GrammarRule, 
    syntax_pattern: &[SyntaxToken], 
    term_context: &[TermParam]
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Build a map from parameter names to their info
    let mut param_names: Vec<String> = Vec::new();
    let mut has_abstraction = false;
    let mut abstraction_binder: Option<String> = None;
    let mut abstraction_body: Option<String> = None;
    
    for param in term_context {
        match param {
            TermParam::Simple { name, .. } => {
                param_names.push(name.to_string());
            },
            TermParam::Abstraction { binder, body, .. } => {
                has_abstraction = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
            },
            TermParam::MultiAbstraction { binder, body, .. } => {
                has_abstraction = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
            },
        }
    }

    // Build format string and args from syntax pattern
    let mut format_str = String::new();
    let mut format_args: Vec<TokenStream> = Vec::new();
    
    for token in syntax_pattern {
        match token {
            SyntaxToken::Literal(s) => {
                // Escape braces in format strings
                let escaped = s.replace('{', "{{").replace('}', "}}");
                format_str.push_str(&escaped);
            },
            SyntaxToken::Ident(id) => {
                let name = id.to_string();
                format_str.push_str("{}");
                
                // Check if this is the binder from an abstraction
                if Some(&name) == abstraction_binder.as_ref() {
                    format_args.push(quote! { binder_name });
                }
                // Check if this is the body from an abstraction
                else if Some(&name) == abstraction_body.as_ref() {
                    format_args.push(quote! { body });
                }
                // Simple parameter - reference directly
                else {
                    let field_ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
                    format_args.push(quote! { #field_ident });
                }
            },
        }
    }

    // Generate field pattern for match arm
    // Simple params come first, then scope (if there's an abstraction)
    let mut field_idents: Vec<syn::Ident> = param_names
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();
    
    if has_abstraction {
        field_idents.push(syn::Ident::new("scope", proc_macro2::Span::call_site()));
        
        quote! {
            #category::#label(#(#field_idents),*) => {
                let (binder, body) = scope.clone().unbind();
                let binder_name = binder.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                write!(f, #format_str, #(#format_args),*)
            }
        }
    } else if field_idents.is_empty() {
        // Nullary constructor - unit variant pattern
        quote! {
            #category::#label => write!(f, #format_str)
        }
    } else {
        // Tuple variant pattern
        quote! {
            #category::#label(#(#field_idents),*) => write!(f, #format_str, #(#format_args),*)
        }
    }
}

/// Generate display for a constructor with binders (old syntax)
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
                    label: parse_quote!(Zero),
                    category: parse_quote!(Expr),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(Add),
                    category: parse_quote!(Expr),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Expr)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Expr)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
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
