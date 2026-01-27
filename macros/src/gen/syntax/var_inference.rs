#![allow(clippy::cmp_owned)]

use crate::ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

use crate::ast::{grammar::{GrammarItem, GrammarRule, TermParam}, types::{TypeExpr, CollectionType}};
use crate::gen::{generate_var_label, is_var_rule};

/// Generate variable category inference methods for lambda type checking
/// 
/// For each category, generates methods that find what type a variable
/// is used as within that term. Used by the parser to select the correct
/// Lam{Domain} variant based on how the binder is used in the body.
/// 
/// Generates:
/// - `VarCategory` enum for base categories
/// - `InferredType` enum for full types including function types
/// - `infer_var_category` for backward compatibility (returns base category)
/// - `infer_var_type` for full type inference (returns function types)
pub fn generate_var_category_inference(language: &LanguageDef) -> TokenStream {
    // Get non-native categories
    let categories: Vec<_> = language.types.iter()
        .filter(|e| e.native_type.is_none())
        .collect();
    
    if categories.is_empty() {
        return quote! {};
    }
    
    // Generate an enum for the possible categories
    let cat_variants: Vec<TokenStream> = categories.iter()
        .map(|e| {
            let name = &e.name;
            quote! { #name }
        })
        .collect();
    
    let cat_names: Vec<_> = categories.iter().map(|e| &e.name).collect();
    
    // Generate the inference methods for each category
    let impls: Vec<TokenStream> = categories.iter().map(|export| {
        let cat_name = &export.name;
        
        // Get rules for this category
        let rules: Vec<_> = language.terms.iter()
            .filter(|r| r.category == *cat_name)
            .collect();
        
        // Generate match arms for basic category inference
        let mut match_arms: Vec<TokenStream> = rules.iter().filter_map(|rule| {
            generate_var_inference_arm(rule, &cat_names, language)
        }).collect();
        
        // Add arm for Var variant - if variable name matches, return this category
        let var_label = generate_var_label(cat_name);
        match_arms.push(quote! {
            #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(VarCategory::#cat_name);
                }
                None
            }
        });
        
        // Add wildcard arm for other variants (lambdas, etc.)
        match_arms.push(quote! {
            _ => None
        });
        
        // Generate match arms for full type inference (including function types)
        let mut type_match_arms: Vec<TokenStream> = rules.iter().filter_map(|rule| {
            generate_var_type_inference_arm(rule, &cat_names)
        }).collect();
        
        // Add arm for Var variant - returns base type
        type_match_arms.push(quote! {
            #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
                if fv.pretty_name.as_deref() == Some(var_name) {
                    return Some(InferredType::Base(VarCategory::#cat_name));
                }
                None
            }
        });
        
        // Generate arms for Apply variants - detect function position usage
        for domain in &cat_names {
            let apply_variant = syn::Ident::new(&format!("Apply{}", domain), proc_macro2::Span::call_site());
            type_match_arms.push(quote! {
                #cat_name::#apply_variant(ref lam, ref arg) => {
                    // Check if variable is in function position
                    if let #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) = **lam {
                        if fv.pretty_name.as_deref() == Some(var_name) {
                            // Variable is being applied - it's a function type
                            return Some(InferredType::Arrow(
                                Box::new(InferredType::Base(VarCategory::#domain)),
                                Box::new(InferredType::Base(VarCategory::#cat_name))
                            ));
                        }
                    }
                    // Otherwise recurse into lambda and argument
                    if let Some(t) = lam.infer_var_type(var_name) {
                        return Some(t);
                    }
                    if let Some(t) = arg.infer_var_type(var_name) {
                        return Some(t);
                    }
                    None
                }
            });
            
            // MApply variant
            let mapply_variant = syn::Ident::new(&format!("MApply{}", domain), proc_macro2::Span::call_site());
            type_match_arms.push(quote! {
                #cat_name::#mapply_variant(ref lam, ref args) => {
                    // Check if variable is in function position
                    if let #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) = **lam {
                        if fv.pretty_name.as_deref() == Some(var_name) {
                            // Variable is being applied - it's a multi-arg function type
                            return Some(InferredType::MultiArrow(
                                Box::new(InferredType::Base(VarCategory::#domain)),
                                Box::new(InferredType::Base(VarCategory::#cat_name))
                            ));
                        }
                    }
                    // Otherwise recurse
                    if let Some(t) = lam.infer_var_type(var_name) {
                        return Some(t);
                    }
                    for arg in args.iter() {
                        if let Some(t) = arg.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                    None
                }
            });
            
            // Lam variant - recurse into body
            let lam_variant = syn::Ident::new(&format!("Lam{}", domain), proc_macro2::Span::call_site());
            type_match_arms.push(quote! {
                #cat_name::#lam_variant(ref scope) => {
                    // Recurse into lambda body
                    if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                        return Some(t);
                    }
                    None
                }
            });
            
            // MLam variant - recurse into body
            let mlam_variant = syn::Ident::new(&format!("MLam{}", domain), proc_macro2::Span::call_site());
            type_match_arms.push(quote! {
                #cat_name::#mlam_variant(ref scope) => {
                    // Recurse into multi-lambda body
                    if let Some(t) = scope.unsafe_body().infer_var_type(var_name) {
                        return Some(t);
                    }
                    None
                }
            });
        }
        
        // Add wildcard arm for other variants
        type_match_arms.push(quote! {
            _ => None
        });
        
        quote! {
            impl #cat_name {
                /// Find what category a variable is used as in this term (base type only)
                pub fn infer_var_category(&self, var_name: &str) -> Option<VarCategory> {
                    match self {
                        #(#match_arms),*
                    }
                }
                
                /// Find the full type of a variable from its usage in this term
                /// 
                /// Returns function types when variable is used in application position.
                /// For example, in `$name(f, x)`, `f` has type `[Name -> Proc]`.
                pub fn infer_var_type(&self, var_name: &str) -> Option<InferredType> {
                    match self {
                        #(#type_match_arms),*
                    }
                }
            }
        }
    }).collect();
    
    quote! {
        /// Enum representing possible variable categories for type inference
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum VarCategory {
            #(#cat_variants),*
        }
        
        /// Inferred type for a variable, including function types
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub enum InferredType {
            /// Base category (Name, Proc, etc.)
            Base(VarCategory),
            /// Function type [Domain -> Codomain]
            Arrow(Box<InferredType>, Box<InferredType>),
            /// Multi-argument function type [Domain* -> Codomain]
            MultiArrow(Box<InferredType>, Box<InferredType>),
        }
        
        impl InferredType {
            /// Get the base representation type (what category stores this type)
            /// 
            /// For function types, returns the codomain's base type since
            /// `[A -> B]` is represented as a `B` value (specifically a `LamA` variant).
            pub fn base_type(&self) -> VarCategory {
                match self {
                    InferredType::Base(cat) => *cat,
                    InferredType::Arrow(_, codomain) => codomain.base_type(),
                    InferredType::MultiArrow(_, codomain) => codomain.base_type(),
                }
            }
        }
        
        impl std::fmt::Display for InferredType {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    InferredType::Base(cat) => write!(f, "{:?}", cat),
                    InferredType::Arrow(domain, codomain) => write!(f, "[{} -> {}]", domain, codomain),
                    InferredType::MultiArrow(domain, codomain) => write!(f, "[{}* -> {}]", domain, codomain),
                }
            }
        }
        
        #(#impls)*
    }
}

/// Field kind for inference generation
#[derive(Clone)]
enum InferFieldKind {
    Simple,          // Regular field
    HashBag,         // HashBag collection (iter returns (&T, usize))
    Vec,             // Vec collection (iter returns &T)
    Binder,          // Scope with single binder
    MultiBinder,     // Scope with multiple binders
}

/// Generate a match arm for variable inference in a constructor
fn generate_var_inference_arm(
    rule: &GrammarRule,
    all_cats: &[&syn::Ident],
    _language: &LanguageDef,
) -> Option<TokenStream> {
    let category = &rule.category;
    let label = &rule.label;
    
    // Skip Var rules (handled separately)
    if is_var_rule(rule) {
        return None;
    }
    
    // Get field info from term_context or bindings
    let fields: Vec<(syn::Ident, syn::Ident, InferFieldKind)> = if let Some(ctx) = &rule.term_context {
        ctx.iter().enumerate().filter_map(|(i, param)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match param {
                TermParam::Simple { ty, .. } => {
                    let field_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == field_cat.to_string()) {
                        let kind = match ty {
                            TypeExpr::Collection { coll_type: CollectionType::HashBag, .. } => InferFieldKind::HashBag,
                            TypeExpr::Collection { coll_type: CollectionType::Vec, .. } => InferFieldKind::Vec,
                            TypeExpr::Collection { coll_type: CollectionType::HashSet, .. } => InferFieldKind::Vec, // HashSet iter is like Vec
                            _ => InferFieldKind::Simple,
                        };
                        Some((field_name, field_cat, kind))
                    } else {
                        None
                    }
                }
                TermParam::Abstraction { ty, .. } => {
                    // For binders, we need to check the body inside the scope
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                TermParam::MultiAbstraction { ty, .. } => {
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::MultiBinder))
                    } else {
                        None
                    }
                }
            }
        }).collect()
    } else {
        // Old syntax - use items
        rule.items.iter().enumerate().filter_map(|(i, item)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match item {
                GrammarItem::NonTerminal(nt) => {
                    if all_cats.iter().any(|c| c.to_string() == nt.to_string()) {
                        Some((field_name, nt.clone(), InferFieldKind::Simple))
                    } else {
                        None
                    }
                }
                GrammarItem::Collection { element_type, coll_type, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == element_type.to_string()) {
                        let kind = match coll_type {
                            CollectionType::HashBag => InferFieldKind::HashBag,
                            CollectionType::Vec => InferFieldKind::Vec,
                            CollectionType::HashSet => InferFieldKind::Vec,
                        };
                        Some((field_name, element_type.clone(), kind))
                    } else {
                        None
                    }
                }
                GrammarItem::Binder { category, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == category.to_string()) {
                        Some((field_name, category.clone(), InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }).collect()
    };
    
    if fields.is_empty() {
        // No recursive fields - check if this is a unit variant
        let has_any_fields = if let Some(ctx) = &rule.term_context {
            !ctx.is_empty()
        } else {
            !rule.items.iter().all(|i| matches!(i, GrammarItem::Terminal(_)))
        };
        
        return Some(if has_any_fields {
            quote! { #category::#label(..) => None }
        } else {
            quote! { #category::#label => None }
        });
    }
    
    // Generate pattern and recursive calls
    let field_patterns: Vec<TokenStream> = fields.iter().map(|(name, _, _)| {
        quote! { ref #name }
    }).collect();
    
    let recursive_calls: Vec<TokenStream> = fields.iter().map(|(name, _field_cat, kind)| {
        match kind {
            InferFieldKind::HashBag => {
                // HashBag.iter() returns (&T, usize), need to extract element
                quote! {
                    for (item, _count) in #name.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                }
            }
            InferFieldKind::Vec => {
                // Vec.iter() returns &T
                quote! {
                    for item in #name.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                }
            }
            InferFieldKind::Binder => {
                // Scope - access the body via unsafe_body()
                quote! {
                    if let Some(cat) = #name.unsafe_body().infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
            InferFieldKind::MultiBinder => {
                // Same as Binder
                quote! {
                    if let Some(cat) = #name.unsafe_body().infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
            InferFieldKind::Simple => {
                quote! {
                    if let Some(cat) = #name.infer_var_category(var_name) {
                        return Some(cat);
                    }
                }
            }
        }
    }).collect();
    
    Some(quote! {
        #category::#label(#(#field_patterns),*) => {
            #(#recursive_calls)*
            None
        }
    })
}

/// Generate a match arm for full type inference in a constructor
/// 
/// Similar to generate_var_inference_arm but returns InferredType instead of VarCategory
fn generate_var_type_inference_arm(
    rule: &GrammarRule,
    all_cats: &[&syn::Ident],
) -> Option<TokenStream> {
    let category = &rule.category;
    let label = &rule.label;
    
    // Skip Var rules (handled separately)
    if is_var_rule(rule) {
        return None;
    }
    
    // Get field info from term_context or bindings
    let fields: Vec<(syn::Ident, syn::Ident, InferFieldKind)> = if let Some(ctx) = &rule.term_context {
        ctx.iter().enumerate().filter_map(|(i, param)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match param {
                TermParam::Simple { ty, .. } => {
                    let field_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == field_cat.to_string()) {
                        let kind = match ty {
                            TypeExpr::Collection { coll_type: CollectionType::HashBag, .. } => InferFieldKind::HashBag,
                            TypeExpr::Collection { coll_type: CollectionType::Vec, .. } => InferFieldKind::Vec,
                            TypeExpr::Collection { coll_type: CollectionType::HashSet, .. } => InferFieldKind::Vec,
                            _ => InferFieldKind::Simple,
                        };
                        Some((field_name, field_cat, kind))
                    } else {
                        None
                    }
                }
                TermParam::Abstraction { ty, .. } => {
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                TermParam::MultiAbstraction { ty, .. } => {
                    let body_cat = extract_base_cat(ty);
                    if all_cats.iter().any(|c| c.to_string() == body_cat.to_string()) {
                        Some((field_name, body_cat, InferFieldKind::MultiBinder))
                    } else {
                        None
                    }
                }
            }
        }).collect()
    } else {
        // Old syntax - use items
        rule.items.iter().enumerate().filter_map(|(i, item)| {
            let field_name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
            match item {
                GrammarItem::NonTerminal(nt) => {
                    if all_cats.iter().any(|c| c.to_string() == nt.to_string()) {
                        Some((field_name, nt.clone(), InferFieldKind::Simple))
                    } else {
                        None
                    }
                }
                GrammarItem::Collection { element_type, coll_type, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == element_type.to_string()) {
                        let kind = match coll_type {
                            CollectionType::HashBag => InferFieldKind::HashBag,
                            CollectionType::Vec => InferFieldKind::Vec,
                            CollectionType::HashSet => InferFieldKind::Vec,
                        };
                        Some((field_name, element_type.clone(), kind))
                    } else {
                        None
                    }
                }
                GrammarItem::Binder { category, .. } => {
                    if all_cats.iter().any(|c| c.to_string() == category.to_string()) {
                        Some((field_name, category.clone(), InferFieldKind::Binder))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }).collect()
    };
    
    if fields.is_empty() {
        // No recursive fields - check if this is a unit variant
        let has_any_fields = if let Some(ctx) = &rule.term_context {
            !ctx.is_empty()
        } else {
            !rule.items.iter().all(|i| matches!(i, GrammarItem::Terminal(_)))
        };
        
        return Some(if has_any_fields {
            quote! { #category::#label(..) => None }
        } else {
            quote! { #category::#label => None }
        });
    }
    
    // Generate pattern and recursive calls
    let field_patterns: Vec<TokenStream> = fields.iter().map(|(name, _, _)| {
        quote! { ref #name }
    }).collect();
    
    let recursive_calls: Vec<TokenStream> = fields.iter().map(|(name, _field_cat, kind)| {
        match kind {
            InferFieldKind::HashBag => {
                quote! {
                    for (item, _count) in #name.iter() {
                        if let Some(t) = item.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                }
            }
            InferFieldKind::Vec => {
                quote! {
                    for item in #name.iter() {
                        if let Some(t) = item.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                }
            }
            InferFieldKind::Binder => {
                quote! {
                    if let Some(t) = #name.unsafe_body().infer_var_type(var_name) {
                        return Some(t);
                    }
                }
            }
            InferFieldKind::MultiBinder => {
                quote! {
                    if let Some(t) = #name.unsafe_body().infer_var_type(var_name) {
                        return Some(t);
                    }
                }
            }
            InferFieldKind::Simple => {
                quote! {
                    if let Some(t) = #name.infer_var_type(var_name) {
                        return Some(t);
                    }
                }
            }
        }
    }).collect();
    
    Some(quote! {
        #category::#label(#(#field_patterns),*) => {
            #(#recursive_calls)*
            None
        }
    })
}

/// Extract the base category from a type expression
fn extract_base_cat(ty: &TypeExpr) -> syn::Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_cat(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_cat(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_cat(inner),
    }
}