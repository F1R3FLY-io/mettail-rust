#![allow(clippy::cmp_owned, clippy::single_match)]

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, TermParam},
    language::LanguageDef,
    types::{CollectionType, TypeExpr},
};
use crate::gen::{generate_literal_label, generate_var_label, is_integer_rule, is_var_rule};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate just the AST enums (without parser)
pub fn generate_ast_enums(language: &LanguageDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &language.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate enum for each exported category
    let enums: Vec<TokenStream> = language.types.iter().map(|lang_type| {
        let cat_name = &lang_type.name;

        let rules = rules_by_cat
            .get(&cat_name.to_string())
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));
        let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, language)
        }).collect();

        // Auto-generate NumLit variant for native types without explicit Integer rule
        if let Some(native_type) = &lang_type.native_type {
            if !has_integer_rule {
                let literal_label = generate_literal_label(native_type);
                let native_type_cloned = native_type.clone();
                variants.push(quote! {
                    #literal_label(#native_type_cloned)
                });
            }
        }

        // Auto-generate Var variant if no explicit Var rule exists
        if !has_var_rule {
            let var_label = generate_var_label(cat_name);
            variants.push(quote! {
                #var_label(mettail_runtime::OrdVar)
            });
        }

        // Auto-generate lambda variants for every domain category
        // This creates Lam{Domain} and MLam{Domain} for each domain type
        for domain_lang_type in &language.types {
            // Skip native types (e.g., Int) - can't use as lambda binder
            if domain_lang_type.native_type.is_some() {
                continue;
            }

            let domain_name = &domain_lang_type.name;

            // Single-binder lambda: Lam{Domain}
            let lam_variant = syn::Ident::new(
                &format!("Lam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #lam_variant(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#cat_name>>)
            });

            // Multi-binder lambda: MLam{Domain}
            let mlam_variant = syn::Ident::new(
                &format!("MLam{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mlam_variant(mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<#cat_name>>)
            });

            // Application variant: Apply{Domain}
            // Represents unevaluated application of a lambda to an argument
            let apply_variant = syn::Ident::new(
                &format!("Apply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #apply_variant(Box<#cat_name>, Box<#domain_name>)
            });

            // Multi-application variant: MApply{Domain}
            let mapply_variant = syn::Ident::new(
                &format!("MApply{}", domain_name),
                proc_macro2::Span::call_site()
            );
            variants.push(quote! {
                #mapply_variant(Box<#cat_name>, Vec<#domain_name>)
            });
        }

        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, mettail_runtime::BoundTerm)]
            pub enum #cat_name {
                #(#variants),*
            }
        }
    }).collect();

    quote! {
        #(#enums)*
    }
}

fn generate_variant(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let label = &rule.label;

    // Check if this rule uses new syntax (term_context)
    if let Some(ref term_context) = rule.term_context {
        return generate_variant_from_term_context(label, term_context);
    }

    // Check if this rule has bindings (old syntax)
    if !rule.bindings.is_empty() {
        // This constructor has binders - generate Scope type
        return generate_binder_variant(rule);
    }

    // Count non-terminal and collection items (these become fields)
    #[derive(Clone)]
    enum FieldType {
        NonTerminal(syn::Ident),
        Collection {
            coll_type: CollectionType,
            element_type: syn::Ident,
        },
    }

    let fields: Vec<FieldType> = rule
        .items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => Some(FieldType::NonTerminal(ident.clone())),
            GrammarItem::Collection { coll_type, element_type, .. } => {
                Some(FieldType::Collection {
                    coll_type: coll_type.clone(),
                    element_type: element_type.clone(),
                })
            },
            GrammarItem::Binder { .. } => None, // Handled above
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        #[allow(clippy::cmp_owned)]
        match &fields[0] {
            FieldType::NonTerminal(ident) if ident.to_string() == "Integer" => {
                // Special case: Integer field - use the category's native type
                let category = &rule.category;

                // Integer requires native type (should be validated earlier)
                if let Some(native_type) = language
                    .types
                    .iter()
                    .find(|t| t.name == *category)
                    .and_then(|t| t.native_type.as_ref())
                {
                    let native_type_cloned = native_type.clone();
                    quote! { #label(#native_type_cloned) }
                } else {
                    // Fallback to i32 if native type not found
                    quote! { #label(i32) }
                }
            },
            FieldType::NonTerminal(ident) if ident.to_string() == "Var" => {
                // Special case: Var field - always use OrdVar
                quote! { #label(mettail_runtime::OrdVar) }
            },
            FieldType::NonTerminal(ident) => {
                // Single non-terminal field
                quote! { #label(Box<#ident>) }
            },
            FieldType::Collection { coll_type, element_type } => {
                // Single collection field
                let coll_type_ident = match coll_type {
                    CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                    CollectionType::HashSet => quote! { std::collections::HashSet },
                    CollectionType::Vec => quote! { Vec },
                };
                quote! { #label(#coll_type_ident<#element_type>) }
            },
        }
    } else {
        // Multiple fields - tuple variant
        let field_types: Vec<TokenStream> = fields
            .iter()
            .map(|f| match f {
                FieldType::NonTerminal(ident) if ident.to_string() == "Var" => {
                    quote! { mettail_runtime::OrdVar }
                },
                FieldType::NonTerminal(ident) => {
                    quote! { Box<#ident> }
                },
                FieldType::Collection { coll_type, element_type } => {
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    quote! { #coll_type_ident<#element_type> }
                },
            })
            .collect();

        quote! { #label(#(#field_types),*) }
    }
}

/// Generate variant from new term_context syntax
fn generate_variant_from_term_context(
    label: &syn::Ident,
    term_context: &[TermParam],
) -> TokenStream {
    let mut fields: Vec<TokenStream> = Vec::new();

    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                // Simple parameter: generate appropriate field type
                let field_type = type_expr_to_field_type(ty);
                fields.push(field_type);
            },
            TermParam::Abstraction { ty, .. } => {
                // Single abstraction: ^x.p:[A -> B]
                // Generates: Scope<Binder<String>, Box<B>>
                if let TypeExpr::Arrow { codomain, .. } = ty {
                    let body_type = type_expr_to_rust_type(codomain);
                    fields.push(quote! {
                        mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#body_type>>
                    });
                }
            },
            TermParam::MultiAbstraction { ty, .. } => {
                // Multi-abstraction: ^[xs].p:[Name* -> B]
                // Generates: Scope<Vec<Binder<String>>, Box<B>>
                if let TypeExpr::Arrow { codomain, .. } = ty {
                    let body_type = type_expr_to_rust_type(codomain);
                    fields.push(quote! {
                        mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, Box<#body_type>>
                    });
                }
            },
        }
    }

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else if fields.len() == 1 {
        let field = &fields[0];
        quote! { #label(#field) }
    } else {
        quote! { #label(#(#fields),*) }
    }
}

fn generate_binder_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // For now, support single binder binding in single body
    // Future: support multiple binders and bodies
    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Get the binder and body categories
    let _binder_cat = match &rule.items[*binder_idx] {
        GrammarItem::Binder { category } => category,
        _ => panic!("Binding index doesn't point to a Binder"),
    };

    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal(cat) => cat,
        _ => panic!("Body index doesn't point to a NonTerminal"),
    };

    let mut fields = Vec::new();

    for (i, item) in rule.items.iter().enumerate() {
        if i == *binder_idx {
            // Skip the binder - it's part of the Scope
            continue;
        }

        if i == body_idx {
            // This is the body - generate Scope
            fields.push(quote! {
                mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<#body_cat>>
            });
        } else {
            // Regular field (comes before or after, but not binder or body)
            match item {
                GrammarItem::NonTerminal(cat) => {
                    if cat.to_string() == "Var" {
                        fields.push(quote! { mettail_runtime::Var<String> });
                    } else {
                        fields.push(quote! { Box<#cat> });
                    }
                },
                GrammarItem::Collection { coll_type, element_type, .. } => {
                    // Collection becomes a field with the appropriate collection type
                    let coll_type_ident = match coll_type {
                        CollectionType::HashBag => quote! { mettail_runtime::HashBag },
                        CollectionType::HashSet => quote! { std::collections::HashSet },
                        CollectionType::Vec => quote! { Vec },
                    };
                    fields.push(quote! { #coll_type_ident<#element_type> });
                },
                GrammarItem::Binder { .. } => {
                    // Should have been skipped above
                    panic!("Unexpected binder at position {}", i);
                },
                GrammarItem::Terminal(_) => {
                    // Terminals don't become fields
                },
            }
        }
    }

    // Generate the variant
    quote! {
        #label(#(#fields),*)
    }
}

/// Convert TypeExpr to a Rust field type (for enum variant fields)
fn type_expr_to_field_type(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if name == "Var" {
                quote! { mettail_runtime::OrdVar }
            } else if name == "Integer" {
                quote! { i64 }
            } else {
                quote! { Box<#ident> }
            }
        },
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag => quote! { mettail_runtime::HashBag<#elem_type> },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        },
        TypeExpr::Arrow { .. } => {
            // Arrow types in simple params shouldn't happen, but handle gracefully
            quote! { Box<dyn std::any::Any> }
        },
        TypeExpr::MultiBinder(inner) => {
            // MultiBinder in simple context: Vec<T>
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        },
    }
}

/// Convert TypeExpr to a Rust type (for use inside Box<>, etc.)
fn type_expr_to_rust_type(ty: &TypeExpr) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            quote! { #ident }
        },
        TypeExpr::Collection { coll_type, element } => {
            let elem_type = type_expr_to_rust_type(element);
            match coll_type {
                CollectionType::HashBag => quote! { mettail_runtime::HashBag<#elem_type> },
                CollectionType::HashSet => quote! { std::collections::HashSet<#elem_type> },
                CollectionType::Vec => quote! { Vec<#elem_type> },
            }
        },
        TypeExpr::Arrow { domain, codomain } => {
            let dom = type_expr_to_rust_type(domain);
            let cod = type_expr_to_rust_type(codomain);
            quote! { (#dom -> #cod) }
        },
        TypeExpr::MultiBinder(inner) => {
            let inner_type = type_expr_to_rust_type(inner);
            quote! { Vec<#inner_type> }
        },
    }
}
