#![allow(clippy::cmp_owned, clippy::single_match)]

use crate::ast::{
    grammar::{GrammarItem, GrammarRule, TermParam},
    language::{CollectionCategory, LanguageDef},
    types::{CollectionType, TypeExpr},
};
use crate::gen::native::native_type_to_string;
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

/// Generate variant from rule.items when we have term_context, so field types match
/// collect_nonterminal_fields (used by pool/congruence). Returns None if items contain binders etc.
fn generate_variant_from_items_for_term_context(
    rule: &GrammarRule,
    _language: &LanguageDef,
) -> Option<TokenStream> {
    let label = &rule.label;
    let mut field_types: Vec<TokenStream> = Vec::new();
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(ident) => {
                let name = ident.to_string();
                let ft = if name == "Var" {
                    quote! { mettail_runtime::OrdVar }
                } else {
                    let field_ident = format_ident!("{}", name);
                    quote! { Box<#field_ident> }
                };
                field_types.push(ft);
            },
            GrammarItem::Collection {
                coll_type,
                element_type,
                ..
            } => {
                let coll_ts = match coll_type {
                    CollectionType::HashBag => quote! { mettail_runtime::HashBag<#element_type> },
                    CollectionType::HashSet => quote! { std::collections::HashSet<#element_type> },
                    CollectionType::Vec => quote! { Vec<#element_type> },
                };
                field_types.push(coll_ts);
            },
            _ => return None,
        }
    }
    if field_types.is_empty() {
        return None;
    }
    Some(if field_types.len() == 1 {
        let f = &field_types[0];
        quote! { #label(#f) }
    } else {
        quote! { #label(#(#field_types),*) }
    })
}

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

        let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
        let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));

        let mut variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule, language)
        }).collect();

        // Auto-generate literal variant for native types without explicit literal rule.
        // Skip for collection categories (List/Bag) — they get ListLit/BagLit below instead.
        let is_collection_category = lang_type.collection_kind.is_some();
        if let Some(native_type) = &lang_type.native_type {
            if !has_literal_rule && !is_collection_category {
                let literal_label = generate_literal_label(native_type);
                let type_str = native_type_to_string(native_type);
                // str is unsized; use String. f32/f64 use canonical wrapper for Eq/Hash/Ord.
                let payload_type = if type_str == "str" {
                    quote! { std::string::String }
                } else if type_str == "f64" {
                    quote! { mettail_runtime::CanonicalFloat64 }
                } else if type_str == "f32" {
                    quote! { mettail_runtime::CanonicalFloat32 }
                } else {
                    quote! { #native_type }
                };
                variants.push(quote! {
                    #literal_label(#payload_type)
                });
            }
        }

        // Auto-generate literal variant for List/Bag (payload from native_type when set, else Vec<elem>/HashBag<elem>)
        let elem_type = language
            .types
            .iter()
            .find(|t| t.name.to_string() == "Proc")
            .map(|t| &t.name)
            .or_else(|| language.types.first().map(|t| &t.name));
        if let Some(ref collection_kind) = lang_type.collection_kind.as_ref() {
            let payload_opt: Option<TokenStream> = if let Some(ref native_type) = lang_type.native_type {
                Some(quote! { #native_type })
            } else if let Some(elem_type) = elem_type {
                Some(match collection_kind {
                    CollectionCategory::List(_) => quote! { Vec<#elem_type> },
                    CollectionCategory::Bag(_) => quote! { mettail_runtime::HashBag<#elem_type> },
                })
            } else {
                None
            };
            if let (Some(payload_type), false) = (payload_opt, has_literal_rule) {
                let literal_label = match collection_kind {
                    CollectionCategory::List(_) => quote::format_ident!("ListLit"),
                    CollectionCategory::Bag(_) => quote::format_ident!("BagLit"),
                };
                variants.push(quote! {
                    #literal_label(#payload_type)
                });
            }
        }

        // Auto-generate Var variant if no explicit Var rule exists (skip for List/Bag - value-only categories)
        let is_collection_category = lang_type.collection_kind.is_some();
        if !has_var_rule && !is_collection_category {
            let var_label = generate_var_label(cat_name);
            variants.push(quote! {
                #var_label(mettail_runtime::OrdVar)
            });
        }

        // Auto-generate lambda variants for every domain category (skip for List/Bag - value-only categories)
        // This creates Lam{Domain} and MLam{Domain} for each domain type
        if !is_collection_category {
        for domain_lang_type in &language.types {
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
        }

        // All category enums use full derives; float categories use canonical wrapper payload (Eq/Hash/Ord).
        let derives = quote! { #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, mettail_runtime::BoundTerm)] };
        quote! {
            #derives
            pub enum #cat_name {
                #(#variants),*
            }
        }
    }).collect();

    quote! {
        #(#enums)*
    }
}

/// Rust type for a literal rule's single field (Integer, Boolean, StringLiteral, FloatLiteral).
fn literal_payload_type(nt: &str, category: &syn::Ident, language: &LanguageDef) -> TokenStream {
    let native_type_for_category = || {
        language
            .types
            .iter()
            .find(|t| t.name == *category)
            .and_then(|t| t.native_type.as_ref())
    };
    match nt {
        "Integer" => {
            if let Some(native_type) = native_type_for_category() {
                quote! { #native_type }
            } else {
                quote! { i32 }
            }
        },
        "Boolean" => quote! { bool },
        "StringLiteral" => quote! { std::string::String },
        "FloatLiteral" => {
            if let Some(native_type) = native_type_for_category() {
                let s = native_type_to_string(native_type);
                if s == "f32" {
                    quote! { mettail_runtime::CanonicalFloat32 }
                } else {
                    quote! { mettail_runtime::CanonicalFloat64 }
                }
            } else {
                quote! { mettail_runtime::CanonicalFloat64 }
            }
        },
        _ => quote! { std::string::String }, // fallback for str/other
    }
}

fn generate_variant(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let label = &rule.label;

    // Check if this rule uses new syntax (term_context).
    // Prefer generating from items (from convert_term_context_to_items) so enum matches
    // pool/congruence (collect_nonterminal_fields uses items). Use format_ident so types resolve.
    if let Some(ref term_context) = rule.term_context {
        if !rule.items.is_empty() {
            if let Some(ts) = generate_variant_from_items_for_term_context(rule, language) {
                return ts;
            }
        }
        return generate_variant_from_term_context(label, term_context, language, &rule.category);
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
            FieldType::NonTerminal(ident)
                if crate::gen::is_literal_nonterminal(&ident.to_string()) =>
            {
                // Literal rule: payload type from nonterminal name (Integer, Boolean, StringLiteral, FloatLiteral)
                let nt = ident.to_string();
                let payload_type = literal_payload_type(&nt, &rule.category, language);
                quote! { #label(#payload_type) }
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
    language: &LanguageDef,
    category: &syn::Ident,
) -> TokenStream {
    let mut fields: Vec<TokenStream> = Vec::new();

    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                // Use type name string then format_ident so the emitted type resolves correctly
                // in the macro expansion scope (avoids wrong type when ident span differs).
                let field_type =
                    type_expr_to_field_type_with_fresh_ident(ty, Some((language, category)));
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

/// Like type_expr_to_field_type but for Base(ident) uses format_ident from the type name string,
/// so the emitted type resolves correctly in the macro expansion scope.
fn type_expr_to_field_type_with_fresh_ident(
    ty: &TypeExpr,
    language_category: Option<(&LanguageDef, &syn::Ident)>,
) -> TokenStream {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if name == "Var" {
                quote! { mettail_runtime::OrdVar }
            } else if name == "Integer" {
                quote! { i64 }
            } else if name == "Boolean" {
                quote! { bool }
            } else if name == "StringLiteral" {
                quote! { std::string::String }
            } else if name == "FloatLiteral" {
                let canonical = language_category
                    .and_then(|(lang, cat)| {
                        lang.types
                            .iter()
                            .find(|t| t.name == *cat)
                            .and_then(|t| t.native_type.as_ref())
                    })
                    .map(|native_type| {
                        let s = native_type_to_string(native_type);
                        if s == "f32" {
                            quote! { mettail_runtime::CanonicalFloat32 }
                        } else {
                            quote! { mettail_runtime::CanonicalFloat64 }
                        }
                    })
                    .unwrap_or_else(|| quote! { mettail_runtime::CanonicalFloat64 });
                canonical
            } else {
                let field_ident = format_ident!("{}", name);
                quote! { Box<#field_ident> }
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
            quote! { Box<dyn std::any::Any> }
        },
        TypeExpr::MultiBinder(inner) => {
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
