#![allow(clippy::cmp_owned)]

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

use crate::gen::{generate_var_label, is_var_rule};
use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, TermParam},
    types::{CollectionType, TypeExpr},
};

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
    // All categories (needed for Env and type inference even when native_type is set)
    let categories: Vec<_> = language.types.iter().collect();

    if categories.is_empty() {
        return quote! {};
    }

    // Categories that have binder rules (Abstraction/MultiAbstraction) - only these get Apply/Lam arms
    let _categories_with_binders: std::collections::HashSet<_> = language
        .terms
        .iter()
        .filter(|r| {
            r.term_context.as_ref().is_some_and(|ctx| {
                ctx.iter().any(|p| {
                    matches!(p, TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. })
                })
            })
        })
        .map(|r| r.category.to_string())
        .collect();

    // Generate an enum for the possible categories
    let cat_variants: Vec<TokenStream> = categories
        .iter()
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

        // Generate arms for Apply/Lam variants for domains that actually have
        // HOL variants auto-gen'd on this category. Post-HOL-B: matches only
        // pairs flagged by `compute_hol_domain_pairs`; emitting an arm
        // referencing a non-existent variant would be a compile error.
        let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
        let cat_str_inf = cat_name.to_string();
        let domain_cats: Vec<_> = cat_names
            .iter()
            .filter(|c| {
                language.types.iter().any(|t| t.name.to_string() == c.to_string())
                    && hol_pairs.contains(&(cat_str_inf.clone(), c.to_string()))
            })
            .collect();
        for domain in &domain_cats {
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
    Simple,  // Regular field
    HashBag, // HashBag collection (iter returns (&T, usize))
    Vec,     // Vec collection (iter returns &T)
    /// Phase 4 #5b (2026-05-12): HashMap collection. `iter()` returns
    /// `(&K, &V)`. Inference must visit BOTH k and v (each may
    /// contain free variables). For the Phase 4 #5b empty-only pilot
    /// invariant `K == V`, both are the same category, so the recursive
    /// call yields the same result type whether invoked on k or v.
    HashMap,
    Binder,      // Scope with single binder
    MultiBinder, // Scope with multiple binders
}

/// Opt-Group: whether a field is wrapped in `Option<T>`. Inner params of
/// `#opt(...)` produce `Option<...>` fields on the AST variant; the
/// generated recursion must gate on `if let Some(__v) = #name.as_ref()`
/// so the recursion only fires when the optional was matched. Top-level
/// (non-optional) fields use `Direct` and bind unconditionally.
#[derive(Clone, Copy)]
enum InferFieldWrap {
    Direct,
    Optional,
}

/// Opt-Group: build the flat field list from a term context, expanding
/// `TermParam::Optional { params }` into its inner params (each contributing
/// its own field at a flat index, matching the variant emission in
/// `enums.rs::generate_variant_from_term_context`). Non-recursive fields
/// (those whose category is not in `all_cats`) are skipped from the
/// returned list — they need no recursion call. Field name = `f{flat_idx}`.
fn collect_inference_fields(
    params: &[TermParam],
    all_cats: &[&syn::Ident],
    flat_idx: &mut usize,
    wrap: InferFieldWrap,
    out: &mut Vec<(syn::Ident, syn::Ident, InferFieldKind, InferFieldWrap)>,
) {
    for param in params {
        match param {
            TermParam::Simple { ty, .. } => {
                let i = *flat_idx;
                *flat_idx += 1;
                let field_cat = extract_base_cat(ty);
                if all_cats
                    .iter()
                    .any(|c| c.to_string() == field_cat.to_string())
                {
                    let kind = match ty {
                        TypeExpr::Collection { coll_type: CollectionType::HashBag, .. } => {
                            InferFieldKind::HashBag
                        },
                        TypeExpr::Collection { coll_type: CollectionType::Vec, .. } => {
                            InferFieldKind::Vec
                        },
                        TypeExpr::Collection { coll_type: CollectionType::HashSet, .. } => {
                            InferFieldKind::Vec
                        },
                        // Phase 4 #5b (2026-05-12): HashMap(K, V).
                        TypeExpr::Collection { coll_type: CollectionType::HashMap, .. }
                        | TypeExpr::Map { .. } => InferFieldKind::HashMap,
                        _ => InferFieldKind::Simple,
                    };
                    let name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                    out.push((name, field_cat, kind, wrap));
                }
            },
            TermParam::Abstraction { ty, .. } => {
                let i = *flat_idx;
                *flat_idx += 1;
                let body_cat = extract_base_cat(ty);
                if all_cats
                    .iter()
                    .any(|c| c.to_string() == body_cat.to_string())
                {
                    let name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                    out.push((name, body_cat, InferFieldKind::Binder, wrap));
                }
            },
            TermParam::MultiAbstraction { ty, .. } => {
                let i = *flat_idx;
                *flat_idx += 1;
                let body_cat = extract_base_cat(ty);
                if all_cats
                    .iter()
                    .any(|c| c.to_string() == body_cat.to_string())
                {
                    let name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                    out.push((name, body_cat, InferFieldKind::MultiBinder, wrap));
                }
            },
            TermParam::GuardBody { .. } => {
                *flat_idx += 1;
            },
            TermParam::Optional { params: inner } => {
                // Inner params each consume their own flat slot. Mark
                // recursion as Optional-wrapped so the emitter gates the
                // sub-call on `if let Some(__v) = field.as_ref() { ... }`.
                collect_inference_fields(inner, all_cats, flat_idx, InferFieldWrap::Optional, out);
            },
        }
    }
}

/// Opt-Group: total flat field count for the term context, accounting for
/// Optional flattening. Used to compute `total` in the destructure-pattern
/// emission so positional `_` placeholders match the variant's actual
/// field layout.
fn flat_term_param_count(params: &[TermParam]) -> usize {
    params
        .iter()
        .map(|p| match p {
            TermParam::Optional { params: inner } => flat_term_param_count(inner),
            _ => 1,
        })
        .sum()
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

    // Get field info from term_context or bindings.
    //
    // Phase 3A-C4 (predicated types): variable bind names use the
    // destructure position (not the term_context index) so they
    // match the variant's actual field layout. Predicate slots are
    // skipped from the field list but tracked separately so the
    // destructure pattern can use `_` placeholders at their positions.
    let fields: Vec<(syn::Ident, syn::Ident, InferFieldKind, InferFieldWrap)> = if let Some(ctx) =
        &rule.term_context
    {
        let mut out = Vec::new();
        let mut idx = 0usize;
        collect_inference_fields(ctx, all_cats, &mut idx, InferFieldWrap::Direct, &mut out);
        out
    } else {
        // Old syntax - use items
        rule.items
            .iter()
            .enumerate()
            .filter_map(|(i, item)| {
                let field_name =
                    syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                match item {
                    GrammarItem::NonTerminal { ident: nt, .. } => {
                        if all_cats.iter().any(|c| c.to_string() == nt.to_string()) {
                            Some((
                                field_name,
                                nt.clone(),
                                InferFieldKind::Simple,
                                InferFieldWrap::Direct,
                            ))
                        } else {
                            None
                        }
                    },
                    GrammarItem::Collection { element_type, coll_type, .. } => {
                        if all_cats
                            .iter()
                            .any(|c| c.to_string() == element_type.to_string())
                        {
                            let kind = match coll_type {
                                CollectionType::HashBag
                                | CollectionType::HashMap
                                | CollectionType::PathMap => {
                                    InferFieldKind::HashBag
                                },
                                CollectionType::Vec => InferFieldKind::Vec,
                                CollectionType::HashSet => InferFieldKind::Vec,
                            };
                            Some((field_name, element_type.clone(), kind, InferFieldWrap::Direct))
                        } else {
                            None
                        }
                    },
                    GrammarItem::Binder { category, .. } => {
                        if all_cats
                            .iter()
                            .any(|c| c.to_string() == category.to_string())
                        {
                            Some((
                                field_name,
                                category.clone(),
                                InferFieldKind::Binder,
                                InferFieldWrap::Direct,
                            ))
                        } else {
                            None
                        }
                    },
                    _ => None,
                }
            })
            .collect()
    };

    if fields.is_empty() {
        // No recursive fields - check if this is a unit variant
        let has_any_fields = if let Some(ctx) = &rule.term_context {
            !ctx.is_empty()
        } else {
            !rule
                .items
                .iter()
                .all(|i| matches!(i, GrammarItem::Terminal(_)))
        };

        return Some(if has_any_fields {
            quote! { #category::#label(..) => None }
        } else {
            quote! { #category::#label => None }
        });
    }

    // Generate pattern and recursive calls.
    //
    // Phase 3A-C4: only the new (term_context) path can have
    // GuardBody slots. For new-syntax rules with predicate slots,
    // emit `_` placeholders interleaved with bound names so the
    // destructure positions match the actual variant layout. For
    // old-syntax rules and new-syntax rules without predicates,
    // use the original pattern (one bound pattern per kept field).
    //
    // Opt-Group: `total` uses the FLAT field count (Optional inner
    // params each contribute one slot to the variant) so positional
    // `_` placeholders match the actual variant layout.
    let has_guard_slot = rule
        .term_context
        .as_ref()
        .map(|ctx| {
            fn has_guard(params: &[TermParam]) -> bool {
                params.iter().any(|p| match p {
                    TermParam::GuardBody { .. } => true,
                    TermParam::Optional { params: inner } => has_guard(inner),
                    _ => false,
                })
            }
            has_guard(ctx)
        })
        .unwrap_or(false);

    // Three cases for destructure pattern:
    //   1. New syntax (term_context): variant arity =
    //      flat_term_param_count(ctx). Use positional `_` placeholders
    //      at unbound positions (predicate slots, non-recursive
    //      Simples, non-recursive inner-of-Optional fields), and
    //      `ref f{i}` at bound positions. Field name `f{i}` is the
    //      flat field index, matching the variant's emitted layout.
    //   2. Old syntax (items): field names f{N} come from the items
    //      index (skipping terminals), so they don't correspond to
    //      variant positions. Emit one `ref f{name}` per kept field,
    //      relying on positional binding by pattern length matching
    //      variant arity (= count of non-terminals).
    let _ = has_guard_slot; // new-syntax path is uniform regardless
    let is_new_syntax = rule.term_context.is_some();
    let field_patterns: Vec<TokenStream> = if is_new_syntax {
        let total = rule
            .term_context
            .as_ref()
            .map(|c| flat_term_param_count(c))
            .unwrap_or(0);
        let bound_indices: std::collections::HashSet<usize> = fields
            .iter()
            .filter_map(|(name, _, _, _)| {
                let s = name.to_string();
                s.strip_prefix('f').and_then(|n| n.parse::<usize>().ok())
            })
            .collect();
        (0..total)
            .map(|i| {
                if bound_indices.contains(&i) {
                    let name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                    quote! { ref #name }
                } else {
                    quote! { _ }
                }
            })
            .collect()
    } else {
        // Old syntax: emit one bound pattern per kept field.
        fields
            .iter()
            .map(|(name, _, _, _)| quote! { ref #name })
            .collect()
    };

    let recursive_calls: Vec<TokenStream> = fields
        .iter()
        .map(|(name, _field_cat, kind, wrap)| {
            let inner = match kind {
                InferFieldKind::HashBag => quote! {
                    for (item, _count) in __v.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                },
                InferFieldKind::Vec => quote! {
                    for item in __v.iter() {
                        if let Some(cat) = item.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                },
                // Phase 4 #5b (2026-05-12): HashMap iter yields (&K, &V) —
                // probe both since either side may carry a free variable.
                InferFieldKind::HashMap => quote! {
                    for (k, v) in __v.iter() {
                        if let Some(cat) = k.infer_var_category(var_name) {
                            return Some(cat);
                        }
                        if let Some(cat) = v.infer_var_category(var_name) {
                            return Some(cat);
                        }
                    }
                },
                InferFieldKind::Binder | InferFieldKind::MultiBinder => quote! {
                    if let Some(cat) = __v.unsafe_body().infer_var_category(var_name) {
                        return Some(cat);
                    }
                },
                InferFieldKind::Simple => quote! {
                    if let Some(cat) = __v.infer_var_category(var_name) {
                        return Some(cat);
                    }
                },
            };
            match wrap {
                InferFieldWrap::Direct => quote! { { let __v = #name; #inner } },
                InferFieldWrap::Optional => quote! {
                    if let Some(__v) = #name.as_ref() { #inner }
                },
            }
        })
        .collect();

    if field_patterns.is_empty() {
        Some(quote! {
            #category::#label(..) => {
                None
            }
        })
    } else {
        Some(quote! {
            #category::#label(#(#field_patterns),*) => {
                #(#recursive_calls)*
                None
            }
        })
    }
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
    let fields: Vec<(syn::Ident, syn::Ident, InferFieldKind, InferFieldWrap)> = if let Some(ctx) =
        &rule.term_context
    {
        let mut out = Vec::new();
        let mut idx = 0usize;
        collect_inference_fields(ctx, all_cats, &mut idx, InferFieldWrap::Direct, &mut out);
        out
    } else {
        // Old syntax - use items
        rule.items
            .iter()
            .enumerate()
            .filter_map(|(i, item)| {
                let field_name =
                    syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                match item {
                    GrammarItem::NonTerminal { ident: nt, .. } => {
                        if all_cats.iter().any(|c| c.to_string() == nt.to_string()) {
                            Some((
                                field_name,
                                nt.clone(),
                                InferFieldKind::Simple,
                                InferFieldWrap::Direct,
                            ))
                        } else {
                            None
                        }
                    },
                    GrammarItem::Collection { element_type, coll_type, .. } => {
                        if all_cats
                            .iter()
                            .any(|c| c.to_string() == element_type.to_string())
                        {
                            let kind = match coll_type {
                                CollectionType::HashBag
                                | CollectionType::HashMap
                                | CollectionType::PathMap => {
                                    InferFieldKind::HashBag
                                },
                                CollectionType::Vec => InferFieldKind::Vec,
                                CollectionType::HashSet => InferFieldKind::Vec,
                            };
                            Some((field_name, element_type.clone(), kind, InferFieldWrap::Direct))
                        } else {
                            None
                        }
                    },
                    GrammarItem::Binder { category, .. } => {
                        if all_cats
                            .iter()
                            .any(|c| c.to_string() == category.to_string())
                        {
                            Some((
                                field_name,
                                category.clone(),
                                InferFieldKind::Binder,
                                InferFieldWrap::Direct,
                            ))
                        } else {
                            None
                        }
                    },
                    _ => None,
                }
            })
            .collect()
    };

    if fields.is_empty() {
        // No recursive fields - check if this is a unit variant
        let has_any_fields = if let Some(ctx) = &rule.term_context {
            !ctx.is_empty()
        } else {
            !rule
                .items
                .iter()
                .all(|i| matches!(i, GrammarItem::Terminal(_)))
        };

        return Some(if has_any_fields {
            quote! { #category::#label(..) => None }
        } else {
            quote! { #category::#label => None }
        });
    }

    // Generate pattern and recursive calls.
    //
    // Phase 3A-C4: positional `_` placeholders for predicate slots
    // (see `infer_var_category` for the rationale).
    //
    // Opt-Group: `total` uses flat field count (Optional inner params
    // contribute one slot each), and recursive calls use Optional-wrap
    // gating when the field is `Option<T>`.
    let has_guard_slot = rule
        .term_context
        .as_ref()
        .map(|ctx| {
            fn has_guard(params: &[TermParam]) -> bool {
                params.iter().any(|p| match p {
                    TermParam::GuardBody { .. } => true,
                    TermParam::Optional { params: inner } => has_guard(inner),
                    _ => false,
                })
            }
            has_guard(ctx)
        })
        .unwrap_or(false);

    let _ = has_guard_slot;
    let is_new_syntax = rule.term_context.is_some();
    let field_patterns: Vec<TokenStream> = if is_new_syntax {
        let total = rule
            .term_context
            .as_ref()
            .map(|c| flat_term_param_count(c))
            .unwrap_or(0);
        let bound_indices: std::collections::HashSet<usize> = fields
            .iter()
            .filter_map(|(name, _, _, _)| {
                let s = name.to_string();
                s.strip_prefix('f').and_then(|n| n.parse::<usize>().ok())
            })
            .collect();
        (0..total)
            .map(|i| {
                if bound_indices.contains(&i) {
                    let name = syn::Ident::new(&format!("f{}", i), proc_macro2::Span::call_site());
                    quote! { ref #name }
                } else {
                    quote! { _ }
                }
            })
            .collect()
    } else {
        // Old syntax: emit one bound pattern per kept field.
        fields
            .iter()
            .map(|(name, _, _, _)| quote! { ref #name })
            .collect()
    };

    let recursive_calls: Vec<TokenStream> = fields
        .iter()
        .map(|(name, _field_cat, kind, wrap)| {
            let inner = match kind {
                InferFieldKind::HashBag => quote! {
                    for (item, _count) in __v.iter() {
                        if let Some(t) = item.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                },
                InferFieldKind::Vec => quote! {
                    for item in __v.iter() {
                        if let Some(t) = item.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                },
                // Phase 4 #5b (2026-05-12): HashMap iter yields (&K, &V) —
                // probe both since either side may carry a free variable.
                InferFieldKind::HashMap => quote! {
                    for (k, v) in __v.iter() {
                        if let Some(t) = k.infer_var_type(var_name) {
                            return Some(t);
                        }
                        if let Some(t) = v.infer_var_type(var_name) {
                            return Some(t);
                        }
                    }
                },
                InferFieldKind::Binder | InferFieldKind::MultiBinder => quote! {
                    if let Some(t) = __v.unsafe_body().infer_var_type(var_name) {
                        return Some(t);
                    }
                },
                InferFieldKind::Simple => quote! {
                    if let Some(t) = __v.infer_var_type(var_name) {
                        return Some(t);
                    }
                },
            };
            match wrap {
                InferFieldWrap::Direct => quote! { { let __v = #name; #inner } },
                InferFieldWrap::Optional => quote! {
                    if let Some(__v) = #name.as_ref() { #inner }
                },
            }
        })
        .collect();

    if field_patterns.is_empty() {
        Some(quote! {
            #category::#label(..) => {
                None
            }
        })
    } else {
        Some(quote! {
            #category::#label(#(#field_patterns),*) => {
                #(#recursive_calls)*
                None
            }
        })
    }
}

/// Extract the base category from a type expression
fn extract_base_cat(ty: &TypeExpr) -> syn::Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_cat(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_cat(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_cat(inner),
        TypeExpr::Refined { base, .. } => extract_base_cat(base),
        TypeExpr::Map { value, .. } => extract_base_cat(value),
    }
}
