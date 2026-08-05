#![allow(clippy::cmp_owned)]

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::gen::capture::capture_layout;
use crate::gen::term_ops::collection_walk::{for_each_subterm, WalkOrder};
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

    let task_variants: Vec<TokenStream> = categories
        .iter()
        .map(|export| {
            let cat = &export.name;
            let variant = format_ident!("Infer{}", cat);
            quote! { #variant(*const #cat) }
        })
        .collect();

    let category_handlers: Vec<TokenStream> = categories
        .iter()
        .map(|export| generate_category_handler(&export.name, &cat_names, language))
        .collect();
    let type_handlers: Vec<TokenStream> = categories
        .iter()
        .map(|export| generate_type_handler(&export.name, &cat_names, language))
        .collect();

    let category_dispatch: Vec<TokenStream> = categories
        .iter()
        .map(|export| {
            let cat = &export.name;
            let variant = format_ident!("Infer{}", cat);
            let handler = format_ident!("infer_category_handle_{}", cat.to_string().to_lowercase());
            quote! { InferenceTask::#variant(ptr) => #handler(stack, ptr, var_name) }
        })
        .collect();
    let type_dispatch: Vec<TokenStream> = categories
        .iter()
        .map(|export| {
            let cat = &export.name;
            let variant = format_ident!("Infer{}", cat);
            let handler = format_ident!("infer_type_handle_{}", cat.to_string().to_lowercase());
            quote! { InferenceTask::#variant(ptr) => #handler(stack, ptr, var_name) }
        })
        .collect();

    let impls: Vec<TokenStream> = categories
        .iter()
        .map(|export| {
            let cat = &export.name;
            let task = format_ident!("Infer{}", cat);
            quote! {
                impl #cat {
                    /// Find the first use of `var_name` in recursive field order and return
                    /// its base category. Uses an explicit PDA worklist, so native stack
                    /// consumption is independent of term depth.
                    pub fn infer_var_category(&self, var_name: &str) -> Option<VarCategory> {
                        let mut stack = INFERENCE_TASK_POOL.with(|pool| pool.take());
                        stack.clear();
                        stack.push(InferenceTask::#task(self as *const _));
                        let result = infer_var_category_iterative(&mut stack, var_name);
                        stack.clear();
                        INFERENCE_TASK_POOL.with(|pool| pool.set(stack));
                        result
                    }

                    /// Find the first full type of `var_name` in recursive field order.
                    /// Application-position variables produce function types. Uses the same
                    /// pooled explicit PDA as base-category inference.
                    pub fn infer_var_type(&self, var_name: &str) -> Option<InferredType> {
                        let mut stack = INFERENCE_TASK_POOL.with(|pool| pool.take());
                        stack.clear();
                        stack.push(InferenceTask::#task(self as *const _));
                        let result = infer_var_type_iterative(&mut stack, var_name);
                        stack.clear();
                        INFERENCE_TASK_POOL.with(|pool| pool.set(stack));
                        result
                    }
                }
            }
        })
        .collect();

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

        /// A node awaiting the ordered depth-first variable-inference visit.
        #[allow(dead_code)]
        enum InferenceTask {
            #(#task_variants),*
        }

        // SAFETY: every pointer is derived from a live public-method `&self`,
        // consumed on that same thread before the method returns, and never
        // retained in the pool.
        unsafe impl Send for InferenceTask {}
        unsafe impl Sync for InferenceTask {}

        thread_local! {
            static INFERENCE_TASK_POOL: std::cell::Cell<Vec<InferenceTask>> =
                std::cell::Cell::new(Vec::new());
        }

        #(#category_handlers)*
        #(#type_handlers)*

        fn infer_var_category_iterative(
            stack: &mut Vec<InferenceTask>,
            var_name: &str,
        ) -> Option<VarCategory> {
            while let Some(task) = stack.pop() {
                let result = match task {
                    #(#category_dispatch),*
                };
                if result.is_some() {
                    return result;
                }
            }
            None
        }

        fn infer_var_type_iterative(
            stack: &mut Vec<InferenceTask>,
            var_name: &str,
        ) -> Option<InferredType> {
            while let Some(task) = stack.pop() {
                let result = match task {
                    #(#type_dispatch),*
                };
                if result.is_some() {
                    return result;
                }
            }
            None
        }

        #(#impls)*
    }
}

fn generate_category_handler(
    cat_name: &syn::Ident,
    cat_names: &[&syn::Ident],
    language: &LanguageDef,
) -> TokenStream {
    let rules: Vec<_> = language
        .terms
        .iter()
        .filter(|rule| rule.category == *cat_name)
        .collect();
    let mut arms: Vec<TokenStream> = rules
        .iter()
        .filter_map(|rule| generate_var_inference_arm(rule, cat_names, language))
        .collect();
    let var_label = generate_var_label(cat_name);
    arms.push(quote! {
        #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
            (fv.pretty_name.as_deref() == Some(var_name))
                .then_some(VarCategory::#cat_name)
        }
    });
    arms.push(quote! { _ => None });
    let handler = format_ident!("infer_category_handle_{}", cat_name.to_string().to_lowercase());
    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #handler(
            stack: &mut Vec<InferenceTask>,
            ptr: *const #cat_name,
            var_name: &str,
        ) -> Option<VarCategory> {
            let value = unsafe { &*ptr };
            match value { #(#arms),* }
        }
    }
}

fn generate_type_handler(
    cat_name: &syn::Ident,
    cat_names: &[&syn::Ident],
    language: &LanguageDef,
) -> TokenStream {
    let rules: Vec<_> = language
        .terms
        .iter()
        .filter(|rule| rule.category == *cat_name)
        .collect();
    let mut arms: Vec<TokenStream> = rules
        .iter()
        .filter_map(|rule| generate_var_type_inference_arm(rule, cat_names))
        .collect();
    let var_label = generate_var_label(cat_name);
    arms.push(quote! {
        #cat_name::#var_label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
            (fv.pretty_name.as_deref() == Some(var_name))
                .then_some(InferredType::Base(VarCategory::#cat_name))
        }
    });

    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let cat_string = cat_name.to_string();
    for domain in cat_names
        .iter()
        .filter(|domain| hol_pairs.contains(&(cat_string.clone(), domain.to_string())))
    {
        let apply = format_ident!("Apply{}", domain);
        let multi_apply = format_ident!("MApply{}", domain);
        let lambda = format_ident!("Lam{}", domain);
        let multi_lambda = format_ident!("MLam{}", domain);
        let task = format_ident!("Infer{}", cat_name);
        let argument_task = format_ident!("Infer{}", domain);
        arms.push(quote! {
            #cat_name::#apply(ref lam, ref arg) => {
                if let #cat_name::#var_label(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(InferredType::Arrow(
                            Box::new(InferredType::Base(VarCategory::#domain)),
                            Box::new(InferredType::Base(VarCategory::#cat_name)),
                        ));
                    }
                }
                // LIFO reverse of the recursive order: lambda, then argument.
                stack.push(InferenceTask::#argument_task(&**arg as *const _));
                stack.push(InferenceTask::#task(&**lam as *const _));
                None
            }
        });
        arms.push(quote! {
            #cat_name::#multi_apply(ref lam, ref args) => {
                if let #cat_name::#var_label(
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))
                ) = **lam {
                    if fv.pretty_name.as_deref() == Some(var_name) {
                        return Some(InferredType::MultiArrow(
                            Box::new(InferredType::Base(VarCategory::#domain)),
                            Box::new(InferredType::Base(VarCategory::#cat_name)),
                        ));
                    }
                }
                for arg in args.iter().rev() {
                    stack.push(InferenceTask::#argument_task(arg as *const _));
                }
                stack.push(InferenceTask::#task(&**lam as *const _));
                None
            }
        });
        for lambda_variant in [lambda, multi_lambda] {
            arms.push(quote! {
                #cat_name::#lambda_variant(ref scope) => {
                    stack.push(InferenceTask::#task(&**scope.unsafe_body() as *const _));
                    None
                }
            });
        }
    }
    arms.push(quote! { _ => None });

    let handler = format_ident!("infer_type_handle_{}", cat_name.to_string().to_lowercase());
    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #handler(
            stack: &mut Vec<InferenceTask>,
            ptr: *const #cat_name,
            var_name: &str,
        ) -> Option<InferredType> {
            let value = unsafe { &*ptr };
            match value { #(#arms),* }
        }
    }
}

/// Field kind for inference generation
#[derive(Clone, Debug, PartialEq, Eq)]
enum InferFieldKind {
    Simple,
    /// A container of subterms. Ordered inference uses the shared collection
    /// boundary in reverse-for-LIFO mode, including PathMap's keys and the
    /// value positions present only in homogeneous map mode.
    Collection(CollectionType),
    Binder,      // Scope with single binder
    MultiBinder, // Scope with multiple binders
}

/// Opt-Group: whether a field is wrapped in `Option<T>`. Inner params of
/// `#opt(...)` produce `Option<...>` fields on the AST variant; the
/// generated recursion must gate on `if let Some(__v) = #name.as_ref()`
/// so the recursion only fires when the optional was matched. Top-level
/// (non-optional) fields use `Direct` and bind unconditionally.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    let mut tasks: Vec<_> = params.iter().rev().map(|param| (param, wrap)).collect();
    while let Some((param, wrap)) = tasks.pop() {
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
                        TypeExpr::Collection { coll_type, .. } => {
                            InferFieldKind::Collection(coll_type.clone())
                        },
                        TypeExpr::Map { .. } => InferFieldKind::Collection(CollectionType::HashMap),
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
                tasks.extend(
                    inner
                        .iter()
                        .rev()
                        .map(|param| (param, InferFieldWrap::Optional)),
                );
            },
        }
    }
}

/// Opt-Group: total flat field count for the term context, accounting for
/// Optional flattening. Used to compute `total` in the destructure-pattern
/// emission so positional `_` placeholders match the variant's actual
/// field layout.
fn flat_term_param_count(params: &[TermParam]) -> usize {
    let mut count = 0;
    let mut stack: Vec<_> = params.iter().collect();
    while let Some(param) = stack.pop() {
        if let TermParam::Optional { params: inner } = param {
            stack.extend(inner);
        } else {
            count += 1;
        }
    }
    count
}

fn contains_guard_param(params: &[TermParam]) -> bool {
    let mut stack: Vec<_> = params.iter().collect();
    while let Some(param) = stack.pop() {
        match param {
            TermParam::GuardBody { .. } => return true,
            TermParam::Optional { params: inner } => stack.extend(inner),
            _ => {},
        }
    }
    false
}

/// Push one field's child positions onto the ordered inference worklist.
/// Callers emit fields in reverse and this helper emits collection positions
/// in reverse, so LIFO pop order is byte-for-byte the recursive visitor's
/// original field/element order.
fn inference_field_push(
    name: &syn::Ident,
    field_cat: &syn::Ident,
    kind: &InferFieldKind,
    wrap: InferFieldWrap,
) -> TokenStream {
    let task = format_ident!("Infer{}", field_cat);
    let inner = match kind {
        InferFieldKind::Simple => quote! {
            stack.push(InferenceTask::#task(&**__v as *const _));
        },
        InferFieldKind::Binder | InferFieldKind::MultiBinder => quote! {
            stack.push(InferenceTask::#task(&**__v.unsafe_body() as *const _));
        },
        InferFieldKind::Collection(coll_type) => for_each_subterm(
            coll_type,
            &quote! { __v },
            WalkOrder::ReverseForLifo,
            &|element, _| {
                quote! {
                    stack.push(InferenceTask::#task(#element as *const _));
                }
            },
        ),
    };
    match wrap {
        InferFieldWrap::Direct => quote! {{
            let __v = #name;
            #inner
        }},
        InferFieldWrap::Optional => quote! {
            if let Some(__v) = #name.as_ref() {
                #inner
            }
        },
    }
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

    // L9-3: a capture-bearing rule's fields are token-text `String` leaves (plus
    // any simple params); a captured token introduces no inferable host-category
    // free variable, so bind all fields with `..` and infer nothing. (A
    // var-bearing simple param interleaved with a capture is used by no grammar;
    // inference conservatively returns None there.)
    if let Some(sp) = rule.syntax_pattern.as_deref() {
        if capture_layout(rule.term_context.as_deref().unwrap_or(&[]), sp).is_some() {
            return Some(quote! { #category::#label(..) => None });
        }
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
                            let kind = InferFieldKind::Collection(coll_type.clone());
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
        .map(|ctx| contains_guard_param(ctx))
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
        .rev()
        .map(|(name, field_cat, kind, wrap)| inference_field_push(name, field_cat, kind, *wrap))
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

    // L9-3: a capture-bearing rule holds token-text leaves (no inferable free
    // variable); bind all fields with `..` and infer nothing (twin of the arm
    // in `generate_var_inference_arm`; arity-safe against the tuple variant).
    if let Some(sp) = rule.syntax_pattern.as_deref() {
        if capture_layout(rule.term_context.as_deref().unwrap_or(&[]), sp).is_some() {
            return Some(quote! { #category::#label(..) => None });
        }
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
                            let kind = InferFieldKind::Collection(coll_type.clone());
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
        .map(|ctx| contains_guard_param(ctx))
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
        .rev()
        .map(|(name, field_cat, kind, wrap)| inference_field_push(name, field_cat, kind, *wrap))
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
    let mut ty = ty;
    loop {
        ty = match ty {
            TypeExpr::Base(ident) => return ident.clone(),
            TypeExpr::Collection { element, .. } => element,
            TypeExpr::Arrow { codomain, .. } => codomain,
            TypeExpr::MultiBinder(inner) => inner,
            TypeExpr::Refined { base, .. } => base,
            TypeExpr::Map { value, .. } => value,
        };
    }
}

#[cfg(test)]
#[path = "../../../tests/support/var_inference_recursive_oracle.rs"]
mod recursive_oracle;
