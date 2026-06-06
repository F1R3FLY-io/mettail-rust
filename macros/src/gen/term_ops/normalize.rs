//! Normalize generation — PDA-driven for non-native categories.
//!
//! Native categories (Int, Bool, UInt32, etc.) keep their per-category PDA
//! (the existing `__NormTask` iterative normalize emitted inline inside
//! `impl Cat { fn normalize() { ... } }` — unchanged from prior art).
//!
//! Non-native categories (Proc, Name, etc.) share ONE PDA driver. This
//! eliminates the mutual recursion between `Proc::normalize` and cross-cat
//! `<Child>::normalize` calls that used to overflow on deep ASTs.
//!
//! ## Architecture (non-native shared PDA)
//!
//! - `AnyNormalizedTerm` — heterogeneous wrapper, one `Wrap<Cat>` per
//!   non-native category.
//! - `NormTask` — work-stack frames:
//!   - `Visit<Cat> { src, slot }` — initiate normalize of a borrowed Cat.
//!   - `AssembleReg<Cat>_<L> { slot, <child slots> }` — reconstruct regular ctor.
//!   - `AssembleColl<Cat>_<L> { slot, elements_start, elements_count, counts_vec }` — flatten collection.
//!   - `AssembleBind<Cat>_<L> { slot, <pre slots>, cloned_pattern, body_slot }`.
//!   - `AssembleMBind<Cat>_<L>` — multi-binder.
//!   - `AssembleBetaApply<Cat>_<Dom> { slot, lam_slot, arg_slot }` — β-reduce.
//!   - `AssembleBetaMApply<Cat>_<Dom> { slot, lam_slot, args_start, args_count }` — multi-β.
//!   - `AssembleCancel_<Outer>_<Inner>_<Ctor> { slot, inner_slot }` — cancellation pair.
//! - TLS pools: `NORM_TASK_POOL`, `NORM_RESULT_POOL`, `NORM_SOURCE_POOL`.
//!   Source pool holds `Vec<Box<AnyNormalizedTerm>>` for β/cancel-rescheduled
//!   owned values. Boxes have stable heap addresses; raw pointers derived
//!   from them remain valid for the call duration even as the Vec grows.
//!
//! ## β-reduction iterative flow
//!
//! ```text
//! AssembleBetaApply_<Cat>_<Dom> { slot, lam_slot, arg_slot }:
//!   lam_normalized = results[lam_slot].take()
//!   arg_normalized = results[arg_slot].take()
//!   if lam_normalized is Cat::Lam<Dom>(scope):
//!     (binder, body) = scope.unbind()
//!     substituted = body.substitute_<dom>(&binder.0, &arg_normalized)  // subst PDA
//!     sources.push(Box::new(AnyNorm::Wrap<Cat>(substituted)))
//!     src_ptr = &*sources.last() -> Cat (stable)
//!     stack.push(Visit<Cat> { src: src_ptr, slot })                     // renormalize
//!   else:
//!     results[slot] = Some(Wrap<Cat>(Cat::Apply<Dom>(Box::new(lam_normalized), Box::new(arg_normalized))))
//! ```
//!
//! Church-numeral β-chains grow `sources` + `stack` + `results` on the heap,
//! NOT the CPU stack — matches the stack-safety invariant.
//!
//! ## Cancellation pair iterative flow
//!
//! Same pattern as β: if inner matches the inner_ctor, peel it, push its
//! payload onto `sources`, push a Visit to renormalize.

#![allow(clippy::cmp_owned, clippy::single_match)]

use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::grammar::{GrammarItem, TermParam};
use mettail_ast::language::{LangType, LanguageDef};
use mettail_ast::pattern::CancellationPair;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use syn::Ident;

/// For each constructor with a collection field, generates a helper function that automatically flattens nested collections of the same type.
pub fn generate_flatten_helpers(language: &LanguageDef) -> TokenStream {
    // Group rules by category
    let mut helpers_by_cat: HashMap<String, Vec<TokenStream>> = HashMap::new();

    for rule in &language.terms {
        // Skip rules that use new term_context with multi-binders
        if let Some(ref ctx) = rule.term_context {
            let has_multi_binder = ctx
                .iter()
                .any(|p| matches!(p, TermParam::MultiAbstraction { .. }));
            if has_multi_binder {
                continue;
            }
            // B9 / Class 2 (2026-05-08): skip flatten helper for multi-Param
            // rules whose collection slot is part of a binder-rule body
            // (e.g. `Choose . a:Proc, qs:Vec(Proc) |- "choose" a "(" qs.* ")"`).
            // The auto-flatten codegen assumes a single-arg HashBag-typed
            // tuple variant (Class-5 collection-literal pattern) and emits
            // `Proc::Label(inner)` matching with `(item, count)` HashBag
            // iteration. Both assumptions break for Class-2 binder rules.
            // The flatten helper is meaningful only for single-Simple-param
            // rules whose param is a Collection — i.e. classify_collection
            // candidates.
            let simple_count = ctx
                .iter()
                .filter(|p| matches!(p, TermParam::Simple { .. }))
                .count();
            if simple_count > 1 {
                continue;
            }
            // Phase 4 #3 (2026-05-12): skip flatten helper for rules with
            // an Optional param. Optional-Collection rules have arity > 1
            // (one slot per Optional, one per Collection), breaking the
            // `Cat::Label(inner)` single-field assumption.
            let has_optional = ctx.iter().any(|p| matches!(p, TermParam::Optional { .. }));
            if has_optional {
                continue;
            }
        }

        let has_collection = rule
            .items
            .iter()
            .any(|item| matches!(item, GrammarItem::Collection { .. }));

        if !has_collection {
            continue;
        }

        let category = &rule.category;
        let label = &rule.label;
        let helper_name = format_ident!("insert_into_{}", label.to_string().to_lowercase());

        let helper = quote! {
            /// Auto-flattening insert for #label
            ///
            /// Iteratively unwraps nested `#label` layers via an explicit
            /// work-stack so deep same-category collection nesting (100+
            /// levels) does not blow the call stack. Non-`#label` elements
            /// are inserted directly; `#label` elements are peeled and
            /// their inner members pushed back onto the stack.
            pub fn #helper_name(
                bag: &mut mettail_runtime::HashBag<#category>,
                elem: #category,
            ) {
                let mut stack: ::std::vec::Vec<#category> = ::std::vec::Vec::with_capacity(4);
                stack.push(elem);
                while let Some(current) = stack.pop() {
                    if matches!(&current, #category::#label(_)) {
                        if let #category::#label(inner) = &current {
                            for (e, count) in inner.iter() {
                                for _ in 0..count {
                                    stack.push(e.clone());
                                }
                            }
                        }
                    } else {
                        bag.insert(current);
                    }
                }
            }
        };

        helpers_by_cat
            .entry(category.to_string())
            .or_default()
            .push(helper);
    }

    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .filter_map(|lang_type| {
            let cat_name = &lang_type.name;
            let helpers = helpers_by_cat.get(&cat_name.to_string())?;
            if helpers.is_empty() {
                return None;
            }
            Some(quote! {
                impl #cat_name {
                    #(#helpers)*
                }
            })
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

/// Generate normalize functions for all exported categories.
///
/// A single unified PDA handles every category (native + non-native). At
/// the Regular Assemble arm, native categories additionally apply
/// `try_fold_to_literal()` for constant folding; non-native just wrap.
pub fn generate_normalize_functions(
    language: &LanguageDef,
    cancellation_pairs: &[CancellationPair],
) -> TokenStream {
    let all_cats: Vec<&LangType> = language.types.iter().collect();

    if all_cats.is_empty() {
        return TokenStream::new();
    }

    generate_non_native_normalize_pda(&all_cats, language, cancellation_pairs)
}

// =============================================================================
// Non-native shared PDA — new code
// =============================================================================

/// Build a set of (host_cat, domain_cat) pairs where host has HOL β-reducible
/// variants for the given domain. Used to detect `Apply<Dom>`/`MApply<Dom>`
/// Regular variants at emission time.
fn compute_hol_pairs_set(language: &LanguageDef) -> HashSet<(String, String)> {
    crate::logic::common::compute_hol_domain_pairs(language)
        .into_iter()
        .collect()
}

/// Build a set of (outer_cat_string, outer_ctor_string, inner_cat_string,
/// inner_ctor_string) keys for cancellation pairs, used to detect outer
/// Regular variants at emission time.
#[allow(clippy::type_complexity)]
fn compute_cancel_set<'a>(
    cancellation_pairs: &'a [CancellationPair],
) -> HashMap<(String, String), &'a CancellationPair> {
    cancellation_pairs
        .iter()
        .map(|p| ((p.outer_category.to_string(), p.outer_constructor.to_string()), p))
        .collect()
}

/// Emit the full non-native normalize PDA: enums + TLS + driver + wrappers.
fn generate_non_native_normalize_pda(
    non_native_cats: &[&LangType],
    language: &LanguageDef,
    cancellation_pairs: &[CancellationPair],
) -> TokenStream {
    let any_norm_term = generate_any_normalized_term_enum(non_native_cats);
    let norm_task = generate_norm_task_enum(non_native_cats, language, cancellation_pairs);
    let tls = generate_norm_tls_pools();
    let driver = generate_norm_driver(non_native_cats, language, cancellation_pairs);
    let wrappers: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| generate_norm_wrapper(&t.name))
        .collect();

    quote! {
        #any_norm_term
        #norm_task
        #tls
        #driver
        #(#wrappers)*
    }
}

/// Emit the heterogeneous wrapper enum for the non-native PDA's result buffer.
fn generate_any_normalized_term_enum(non_native_cats: &[&LangType]) -> TokenStream {
    let variants: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| {
            let cat = &t.name;
            let wrap = format_ident!("Wrap{}", cat);
            quote! { #wrap(#cat) }
        })
        .collect();

    quote! {
        /// Result-buffer element for the iterative normalize engine.
        #[allow(dead_code)]
        enum AnyNormalizedTerm {
            #(#variants),*
        }
    }
}

/// Emit the work-stack frame enum.
fn generate_norm_task_enum(
    non_native_cats: &[&LangType],
    language: &LanguageDef,
    cancellation_pairs: &[CancellationPair],
) -> TokenStream {
    let hol_pairs = compute_hol_pairs_set(language);
    let cancel_set = compute_cancel_set(cancellation_pairs);

    let visit_variants: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant = format_ident!("Visit{}", cat);
            quote! {
                #variant { src: *const #cat, slot: usize }
            }
        })
        .collect();

    let mut assemble_variants: Vec<TokenStream> = Vec::new();
    for lang_type in non_native_cats {
        let category = &lang_type.name;
        let cat_str = category.to_string();
        let variants = collect_category_variants(category, language);
        for v in &variants {
            if let Some(decl) =
                generate_assemble_variant_decl(category, v, &hol_pairs, &cancel_set, &cat_str)
            {
                assemble_variants.push(decl);
            }
        }
    }

    quote! {
        /// Work-stack frame for the iterative normalize engine.
        #[allow(dead_code, non_camel_case_types)]
        enum NormTask {
            #(#visit_variants,)*
            #(#assemble_variants,)*
        }
    }
}

/// Emit Assemble variant declarations for a non-leaf variant. Returns None
/// for leaf variants (Var, Literal, Nullary) which write directly during Visit.
///
/// HOL Apply<Dom>/MApply<Dom> Regular variants and cancellation-outer Regular
/// variants get SPECIAL Assemble variants; all other Regulars get the
/// generic `AssembleReg_<Cat>_<L>`.
fn generate_assemble_variant_decl(
    category: &Ident,
    variant: &VariantKind,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => None,

        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>: β-reduction Assemble frame
            if let Some(dom) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom.to_string())) {
                    let variant_name = format_ident!("AssembleBetaApply_{}_{}", category, dom);
                    return Some(quote! {
                        #variant_name { slot: usize, lam_slot: usize, arg_slot: usize }
                    });
                }
            }
            if let Some(dom) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom.to_string())) {
                    let variant_name = format_ident!("AssembleBetaMApply_{}_{}", category, dom);
                    return Some(quote! {
                        #variant_name {
                            slot: usize,
                            lam_slot: usize,
                            args_start: usize,
                            args_count: usize,
                        }
                    });
                }
            }

            // Cancellation pair outer: AssembleCancel frame
            if let Some(pair) = cancel_set.get(&(cat_str.to_string(), label_str.clone())) {
                let inner_cat = &pair.inner_category;
                let variant_name =
                    format_ident!("AssembleCancel_{}_{}_{}", category, inner_cat, label);
                return Some(quote! {
                    #variant_name { slot: usize, inner_slot: usize }
                });
            }

            // Generic Regular
            let variant_name = format_ident!("AssembleReg_{}_{}", category, label);
            let field_slots: Vec<TokenStream> = fields
                .iter()
                .enumerate()
                .map(|(i, field)| emit_reg_field_decl(i, field))
                .collect();

            Some(quote! {
                #variant_name { slot: usize, #(#field_slots),* }
            })
        },

        VariantKind::Collection { label, coll_type, .. } => {
            let variant_name = format_ident!("AssembleColl_{}_{}", category, label);
            match coll_type {
                CollectionType::HashBag | CollectionType::HashMap => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                        counts_vec: Vec<usize>,
                    }
                }),
                _ => Some(quote! {
                    #variant_name {
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    }
                }),
            }
        },

        VariantKind::Binder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("AssembleBind_{}_{}", category, label);
            let pre_decls = emit_pre_field_decl_list(pre_scope_fields);
            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_decls,)*
                    cloned_pattern: mettail_runtime::Binder<String>,
                    body_slot: usize,
                }
            })
        },

        VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            let variant_name = format_ident!("AssembleMBind_{}_{}", category, label);
            let pre_decls = emit_pre_field_decl_list(pre_scope_fields);
            Some(quote! {
                #variant_name {
                    slot: usize,
                    #(#pre_decls,)*
                    cloned_pattern: Vec<mettail_runtime::Binder<String>>,
                    body_slot: usize,
                }
            })
        },
    }
}

/// Phase 4 #3 (2026-05-12): For an Optional-Collection field, derive the
/// runtime carrier type (e.g. `Option<Vec<Proc>>`,
/// `Option<mettail_runtime::HashBag<Proc>>`, etc.) that matches what
/// `enums.rs::one_optional_field` emitted for the AST. Used by the
/// normalize PDA's cloned-carrier path.
fn optional_collection_field_type(field: &FieldInfo) -> TokenStream {
    let cat = &field.category;
    match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec => quote! { Option<Vec<#cat>> },
        CollectionType::HashBag => quote! { Option<mettail_runtime::HashBag<#cat>> },
        CollectionType::HashSet => quote! { Option<std::collections::HashSet<#cat>> },
        CollectionType::HashMap => {
            // HashMap inside Optional uses HashMapLit<K,V>; treat the inner
            // element category as the value category. Map-typed slots aren't
            // exercised yet in the test grammar; emit a best-effort type.
            quote! { Option<mettail_runtime::HashMapLit<#cat, #cat>> }
        },
    }
}

/// Regular-field slot declaration (single slot, or collection range tuple).
///
/// **Cross-cat native fields** are stored as a cloned owned value in the
/// frame (field name + Box<FieldCat>), because we normalize them eagerly
/// at Visit time via `.normalize()` (calls the native per-category PDA)
/// rather than pushing a Visit task.
fn emit_reg_field_decl(i: usize, field: &FieldInfo) -> TokenStream {
    if field.is_predicate {
        let pred_name = format_ident!("f{}_pred", i);
        return quote! { #pred_name: mettail_runtime::BehavioralPred };
    }
    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — cloned carrier.
            let cloned = format_ident!("f{}_cloned", i);
            let ty = optional_collection_field_type(field);
            return quote! { #cloned: #ty };
        }
        let slot_name = format_ident!("f{}_slot", i);
        let some_flag = format_ident!("f{}_some", i);
        return quote! { #slot_name: usize, #some_flag: bool };
    }
    if field.is_collection {
        let start_name = format_ident!("f{}_start", i);
        let count_name = format_ident!("f{}_count", i);
        match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
            CollectionType::HashBag => {
                let counts_name = format_ident!("f{}_counts", i);
                quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
            },
            // Phase 4 #5b (2026-05-12): HashMap stores 2*N slots (K, V, K,
            // V, ...) per the matching alloc/push in
            // `emit_collection_field_alloc`. Same decl shape as Vec —
            // start + count (count = entry count, not slot count).
            CollectionType::HashMap => {
                quote! { #start_name: usize, #count_name: usize }
            },
            _ => quote! { #start_name: usize, #count_name: usize },
        }
    } else {
        let slot_name = format_ident!("f{}_slot", i);
        quote! { #slot_name: usize }
    }
}

/// Same as `emit_reg_field_decl` but for Binder/MultiBinder pre-scope fields
/// (uses `pf{i}_*` prefix).
fn emit_pre_field_decl_list(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name: mettail_runtime::BehavioralPred };
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — cloned carrier
            // (Option<Container>) stored directly in the assemble variant,
            // bypassing slot/start/count machinery (mirrors regular path).
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                let ty = optional_collection_field_type(field);
                return quote! { #cloned: #ty };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name: usize, #count_name: usize, #counts_name: Vec<usize> }
                    },
                    // Phase 4 #5b (2026-05-12): HashMap stores 2*N slots.
                    CollectionType::HashMap => {
                        quote! { #start_name: usize, #count_name: usize }
                    },
                    _ => quote! { #start_name: usize, #count_name: usize },
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name: usize }
            }
        })
        .collect()
}

fn strip_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    s.strip_prefix(prefix)
}

/// Emit the TLS pools for the non-native PDA.
fn generate_norm_tls_pools() -> TokenStream {
    quote! {
        thread_local! {
            /// Pool for reusing `NormTask` work stacks across normalize calls.
            static NORM_TASK_POOL: std::cell::Cell<Vec<NormTask>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for reusing result buffers across normalize calls.
            static NORM_RESULT_POOL: std::cell::Cell<Vec<Option<AnyNormalizedTerm>>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for reusing owned-source boxes (β/cancel rescheduling).
            static NORM_SOURCE_POOL: std::cell::Cell<Vec<Box<AnyNormalizedTerm>>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Driver Emission
// =============================================================================

/// Emit the main `normalize_iterative` driver function.
///
/// **Frame-size fix (PDA stack-safety):** Each Visit{Cat} arm is extracted
/// into its own `#[inline(never)]` helper. Without this split, normalize's
/// match of all per-category arms forces rustc to allocate stack space for
/// every variant's locals up front, overflowing the default 2 MB thread stack.
fn generate_norm_driver(
    non_native_cats: &[&LangType],
    language: &LanguageDef,
    cancellation_pairs: &[CancellationPair],
) -> TokenStream {
    let hol_pairs = compute_hol_pairs_set(language);
    let cancel_set = compute_cancel_set(cancellation_pairs);

    // Per-category Visit helpers (one fn per cat).
    let visit_helper_fns: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| generate_visit_helper_fn(&t.name, language, &hol_pairs, &cancel_set))
        .collect();

    // Tiny dispatch arms that delegate to the per-cat helper.
    let visit_arms: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| {
            let cat = &t.name;
            let visit_variant = format_ident!("Visit{}", cat);
            let helper_fn = format_ident!("norm_visit_{}", cat.to_string().to_lowercase());
            quote! {
                NormTask::#visit_variant { src, slot } => {
                    #helper_fn(stack, results, sources, src, slot);
                }
            }
        })
        .collect();

    let mut assemble_arms: Vec<TokenStream> = Vec::new();
    for lang_type in non_native_cats {
        let category = &lang_type.name;
        let cat_str = category.to_string();
        let variants = collect_category_variants(category, language);
        for v in &variants {
            let is_native = lang_type.native_type.is_some();
            if let Some(arm) =
                generate_assemble_arm(category, v, &hol_pairs, &cancel_set, &cat_str, is_native)
            {
                assemble_arms.push(arm);
            }
        }
    }

    quote! {
        #(#visit_helper_fns)*

        /// Iterative normalize engine. Processes the work stack until empty.
        ///
        /// # Safety
        ///
        /// All `*const Cat` pointers in `NormTask::Visit<Cat>` must be valid
        /// for reads for the duration of this function call. Pointers into
        /// borrowed-source Cat values (from the initial `self` argument) are
        /// valid because `self` outlives the call. Pointers into owned-source
        /// boxes pushed via `sources.push(...)` are valid because the
        /// heap data inside each `Box<AnyNormalizedTerm>` has a stable
        /// address; growing `sources` moves Box handles, not the Cat data
        /// they point to.
        #[allow(
            dead_code,
            unused_variables,
            unreachable_patterns,
            clippy::needless_range_loop,
            non_snake_case
        )]
        fn normalize_iterative(
            stack: &mut Vec<NormTask>,
            results: &mut Vec<Option<AnyNormalizedTerm>>,
            sources: &mut Vec<Box<AnyNormalizedTerm>>,
        ) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#visit_arms)*
                    #(#assemble_arms)*
                }
            }
        }
    }
}

/// Emit the per-category Visit helper function. Single `match src_ref { variants... }`
/// body; pushes new tasks onto the shared `stack`.
fn generate_visit_helper_fn(
    cat: &Ident,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
) -> TokenStream {
    let helper_fn = format_ident!("norm_visit_{}", cat.to_string().to_lowercase());
    let cat_str = cat.to_string();
    let variants = collect_category_variants(cat, language);
    let variant_arms: Vec<TokenStream> = variants
        .iter()
        .map(|v| generate_visit_variant_arm(cat, v, language, hol_pairs, cancel_set, &cat_str))
        .collect();
    let wrap_self = format_ident!("Wrap{}", cat);
    quote! {
        #[inline(never)]
        #[allow(
            dead_code,
            unused_variables,
            unreachable_patterns,
            clippy::needless_range_loop,
            non_snake_case
        )]
        fn #helper_fn(
            stack: &mut Vec<NormTask>,
            results: &mut Vec<Option<AnyNormalizedTerm>>,
            sources: &mut Vec<Box<AnyNormalizedTerm>>,
            src: *const #cat,
            slot: usize,
        ) {
            let src_ref = unsafe { &*src };
            match src_ref {
                #(#variant_arms)*
                _ => {
                    results[slot] = Some(AnyNormalizedTerm::#wrap_self(src_ref.clone()));
                }
            }
        }
    }
}

/// Dispatch per-variant Visit handling.
fn generate_visit_variant_arm(
    cat: &Ident,
    variant: &VariantKind,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> TokenStream {
    let wrap = format_ident!("Wrap{}", cat);

    match variant {
        VariantKind::Var { label } => {
            quote! {
                #cat::#label(v) => {
                    results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label(v.clone())));
                }
            }
        },
        VariantKind::Literal { label } => {
            // Conservative: clone (works for both Copy and non-Copy).
            quote! {
                #cat::#label(v) => {
                    results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label(v.clone())));
                }
            }
        },
        VariantKind::Nullary { label } => {
            quote! {
                #cat::#label => {
                    results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label));
                }
            }
        },
        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return generate_beta_apply_visit_arm(cat, label, dom_str);
                }
            }
            // HOL MApply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return generate_beta_mapply_visit_arm(cat, label, dom_str);
                }
            }

            // Cancellation pair outer
            if let Some(pair) = cancel_set.get(&(cat_str.to_string(), label_str.clone())) {
                return generate_cancel_visit_arm(cat, label, pair);
            }

            // Generic Regular
            generate_regular_visit_arm(cat, label, fields, language)
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_visit_arm(cat, label, element_cat, coll_type, language)
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            generate_binder_visit_arm(cat, label, pre_scope_fields, body_cat, language)
        },
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            generate_multi_binder_visit_arm(cat, label, pre_scope_fields, body_cat, language)
        },
    }
}

/// Regular Visit arm: allocate child slots, push AssembleReg + per-field
/// Visits. Cross-cat fields of NATIVE type are normalized eagerly at Visit
/// time (bounded — native normalize is iterative) and stored as owned clones
/// in the Assemble frame. Same-cat and non-native cross-cat fields get
/// Visit tasks pushed onto the stack.
fn generate_regular_visit_arm(
    cat: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let assemble_variant = format_ident!("AssembleReg_{}_{}", cat, label);

    let (alloc_stmts, push_stmts, assemble_fields) =
        emit_reg_field_visit_alloc(cat, fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            #(#alloc_stmts)*
            stack.push(NormTask::#assemble_variant { slot, #(#assemble_fields),* });
            #(#push_stmts)*
        }
    }
}

/// Emit alloc/push/assemble-fields for a Regular variant's fields.
fn emit_reg_field_visit_alloc(
    _cat: &Ident,
    fields: &[FieldInfo],
    field_names: &[Ident],
    _language: &LanguageDef,
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let name = &field_names[i];

        if field.is_predicate {
            let pred_name = format_ident!("f{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_fields.push(quote! { #pred_name });
            continue;
        }

        if field.is_optional {
            // Phase 4 #3 (2026-05-12): Optional-Collection — bypass slot
            // machinery. Elements of the inner collection don't get
            // normalized via the PDA here (they're already normalized at
            // construction time, since normalize is invoked top-down).
            // For binder/literal slots inside, the PDA would re-normalize;
            // for now, clone the whole Option<Container> and pass through.
            // This matches the existing top-level non-collection Option's
            // intent when nothing to do: pass through unchanged.
            if field.is_collection {
                let cloned = format_ident!("f{}_cloned", i);
                alloc_stmts.push(quote! {
                    let #cloned = #name.clone();
                });
                assemble_fields.push(quote! { #cloned });
                continue;
            }
            // Opt-Group: slot+some_flag pattern. Push VisitTask only if
            // Some; assemble reconstructs Option<Box<Cat>>.
            let field_cat = &field.category;
            let visit_task = format_ident!("Visit{}", field_cat);
            let slot_name = format_ident!("f{}_slot", i);
            let some_flag = format_ident!("f{}_some", i);
            alloc_stmts.push(quote! {
                let #some_flag: bool = #name.is_some();
                let #slot_name = results.len();
                if #some_flag { results.push(None); }
            });
            push_stmts.push(quote! {
                if let Some(__b) = #name.as_ref() {
                    stack.push(NormTask::#visit_task {
                        src: __b.as_ref() as *const _,
                        slot: #slot_name,
                    });
                }
            });
            assemble_fields.push(quote! { #slot_name, #some_flag });
            continue;
        }

        if field.is_collection {
            emit_collection_field_alloc(
                i,
                field,
                name,
                &mut alloc_stmts,
                &mut push_stmts,
                &mut assemble_fields,
            );
            continue;
        }

        // Non-collection scalar field. Unified dispatch: push Visit<FieldCat>.
        // The shared PDA handles every category (native + non-native).
        let field_cat = &field.category;
        let visit_task = format_ident!("Visit{}", field_cat);
        let slot_name = format_ident!("f{}_slot", i);
        alloc_stmts.push(quote! {
            let #slot_name = results.len();
            results.push(None);
        });
        push_stmts.push(quote! {
            stack.push(NormTask::#visit_task {
                src: &**#name as *const _,
                slot: #slot_name,
            });
        });
        assemble_fields.push(quote! { #slot_name });
    }

    (alloc_stmts, push_stmts, assemble_fields)
}

/// Emit alloc/push/assemble for a single collection field (part of a
/// Regular variant). Collection fields contain non-native elements (the
/// element category must be in the shared PDA). Native-element collections
/// are handled by the native per-category PDA if they existed — but they
/// don't in practice for non-native categories.
fn emit_collection_field_alloc(
    i: usize,
    field: &FieldInfo,
    name: &Ident,
    alloc_stmts: &mut Vec<TokenStream>,
    push_stmts: &mut Vec<TokenStream>,
    assemble_fields: &mut Vec<TokenStream>,
) {
    let start_name = format_ident!("f{}_start", i);
    let count_name = format_ident!("f{}_count", i);
    let visit_task = format_ident!("Visit{}", field.category);

    match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::HashBag => {
            let counts_name = format_ident!("f{}_counts", i);
            alloc_stmts.push(quote! {
                let #start_name = results.len();
                let mut #counts_name: Vec<usize> = Vec::new();
                for (_elem, count) in #name.iter() {
                    results.push(None);
                    #counts_name.push(count);
                }
                let #count_name = results.len() - #start_name;
            });
            push_stmts.push(quote! {
                for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                    stack.push(NormTask::#visit_task {
                        src: elem as *const _,
                        slot: #start_name + elem_idx,
                    });
                }
            });
            assemble_fields.push(quote! { #start_name, #count_name, #counts_name });
        },
        CollectionType::HashMap => {
            // Phase 4 #5b (2026-05-12): HashMap field — HashMapLit's
            // `iter` yields `(&K, &V)`, not `(&T, usize)` (which HashBag
            // yields). The Phase 4 #5 pilot left this codepath broken
            // for non-empty HashMaps (drains of length 0 trivially
            // matched). With Phase 4 #5b's walker support populating
            // pairs end-to-end, we materialize a Vec slot per BOTH key
            // AND value (one Visit per entry, flattened K then V), then
            // reconstruct via the AssembleReg arm reading 2 results per
            // entry. Since K and V share the SAME category (per the
            // K==V invariant `classify_binder` enforces), one
            // visit_task variant suffices.
            alloc_stmts.push(quote! {
                let #start_name = results.len();
                for _ in 0..#name.len() {
                    results.push(None); // k slot
                    results.push(None); // v slot
                }
                let #count_name = #name.len();
            });
            push_stmts.push(quote! {
                for (entry_idx, (k, v)) in #name.iter().enumerate() {
                    let k_slot = #start_name + entry_idx * 2;
                    let v_slot = #start_name + entry_idx * 2 + 1;
                    stack.push(NormTask::#visit_task {
                        src: k as *const _,
                        slot: k_slot,
                    });
                    stack.push(NormTask::#visit_task {
                        src: v as *const _,
                        slot: v_slot,
                    });
                }
            });
            assemble_fields.push(quote! { #start_name, #count_name });
        },
        CollectionType::Vec => {
            alloc_stmts.push(quote! {
                let #start_name = results.len();
                for _ in 0..#name.len() {
                    results.push(None);
                }
                let #count_name = #name.len();
            });
            push_stmts.push(quote! {
                for (idx, elem) in #name.iter().enumerate().rev() {
                    stack.push(NormTask::#visit_task {
                        src: elem as *const _,
                        slot: #start_name + idx,
                    });
                }
            });
            assemble_fields.push(quote! { #start_name, #count_name });
        },
        CollectionType::HashSet => {
            alloc_stmts.push(quote! {
                let #start_name = results.len();
                for _ in 0..#name.len() {
                    results.push(None);
                }
                let #count_name = #name.len();
            });
            push_stmts.push(quote! {
                for (elem_idx, elem) in #name.iter().enumerate() {
                    stack.push(NormTask::#visit_task {
                        src: elem as *const _,
                        slot: #start_name + elem_idx,
                    });
                }
            });
            assemble_fields.push(quote! { #start_name, #count_name });
        },
    }
}

/// Collection variant Visit arm: push Visit for each element, Assemble
/// reconstructs via `insert_into_<label>` helper (flattening).
fn generate_collection_visit_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleColl_{}_{}", cat, label);
    let visit_task = format_ident!("Visit{}", element_cat);

    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    let mut counts_vec: Vec<usize> = Vec::new();
                    for (_elem, count) in coll.iter() {
                        results.push(None);
                        counts_vec.push(count);
                    }
                    let elements_count = results.len() - elements_start;
                    stack.push(NormTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                        counts_vec,
                    });
                    for (elem_idx, (elem, _count)) in coll.iter().enumerate() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + elem_idx,
                        });
                    }
                }
            }
        },
        CollectionType::Vec => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    stack.push(NormTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                    });
                    for (idx, elem) in coll.iter().enumerate().rev() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + idx,
                        });
                    }
                }
            }
        },
        CollectionType::HashSet => {
            quote! {
                #cat::#label(ref coll) => {
                    let elements_start = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let elements_count = coll.len();
                    stack.push(NormTask::#assemble_variant {
                        slot,
                        elements_start,
                        elements_count,
                    });
                    for (elem_idx, elem) in coll.iter().enumerate() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: elements_start + elem_idx,
                        });
                    }
                }
            }
        },
    }
}

/// Binder Visit arm: push AssembleBind + Visits for pre-fields + body.
fn generate_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleBind_{}_{}", cat, label);
    let body_visit = format_ident!("Visit{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, assemble_pre) =
        emit_pre_field_visit_alloc(cat, pre_scope_fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let binder = &#scope_name.inner().unsafe_pattern;
            let body = &#scope_name.inner().unsafe_body;

            #(#alloc_pre)*

            let body_slot = results.len();
            results.push(None);
            let cloned_pattern = binder.clone();

            stack.push(NormTask::#assemble_variant {
                slot,
                #(#assemble_pre,)*
                cloned_pattern,
                body_slot,
            });

            stack.push(NormTask::#body_visit {
                src: &**body as *const _,
                slot: body_slot,
            });
            #(#push_pre)*
        }
    }
}

/// MultiBinder Visit arm: same shape as Binder but cloned_pattern is a Vec.
fn generate_multi_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleMBind_{}_{}", cat, label);
    let body_visit = format_ident!("Visit{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, assemble_pre) =
        emit_pre_field_visit_alloc(cat, pre_scope_fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let binders = &#scope_name.inner().unsafe_pattern;
            let body = &#scope_name.inner().unsafe_body;

            #(#alloc_pre)*

            let body_slot = results.len();
            results.push(None);
            let cloned_pattern = binders.clone();

            stack.push(NormTask::#assemble_variant {
                slot,
                #(#assemble_pre,)*
                cloned_pattern,
                body_slot,
            });

            stack.push(NormTask::#body_visit {
                src: &**body as *const _,
                slot: body_slot,
            });
            #(#push_pre)*
        }
    }
}

/// Emit alloc/push/assemble for Binder pre-scope fields (pf{i}_* prefix).
fn emit_pre_field_visit_alloc(
    _cat: &Ident,
    pre_scope_fields: &[FieldInfo],
    field_names: &[Ident],
    _language: &LanguageDef,
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_refs: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];

        if field.is_predicate {
            let pred_name = format_ident!("pf{}_pred", i);
            alloc_stmts.push(quote! {
                let #pred_name = #name.clone();
            });
            assemble_refs.push(quote! { #pred_name });
            continue;
        }

        // Phase 4 #4 (2026-05-12): Optional-Collection — bypass slot/visit-task
        // machinery. Clone derives on Option<Container>; store the cloned
        // value directly into the assemble carrier (same as regular path).
        if field.is_optional && field.is_collection {
            let cloned = format_ident!("pf{}_cloned", i);
            alloc_stmts.push(quote! {
                let #cloned = #name.clone();
            });
            assemble_refs.push(quote! { #cloned });
            continue;
        }

        if field.is_collection {
            let start_name = format_ident!("pf{}_start", i);
            let count_name = format_ident!("pf{}_count", i);
            let visit_task = format_ident!("Visit{}", field.category);
            match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                CollectionType::HashBag | CollectionType::HashMap => {
                    let counts_name = format_ident!("pf{}_counts", i);
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        let mut #counts_name: Vec<usize> = Vec::new();
                        for (_elem, count) in #name.iter() {
                            results.push(None);
                            #counts_name.push(count);
                        }
                        let #count_name = results.len() - #start_name;
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, (elem, _count)) in #name.iter().enumerate() {
                            stack.push(NormTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name, #counts_name });
                },
                CollectionType::Vec => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (idx, elem) in #name.iter().enumerate().rev() {
                            stack.push(NormTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name });
                },
                CollectionType::HashSet => {
                    alloc_stmts.push(quote! {
                        let #start_name = results.len();
                        for _ in 0..#name.len() {
                            results.push(None);
                        }
                        let #count_name = #name.len();
                    });
                    push_stmts.push(quote! {
                        for (elem_idx, elem) in #name.iter().enumerate() {
                            stack.push(NormTask::#visit_task {
                                src: elem as *const _,
                                slot: #start_name + elem_idx,
                            });
                        }
                    });
                    assemble_refs.push(quote! { #start_name, #count_name });
                },
            }
            continue;
        }

        let field_cat = &field.category;
        let visit_task = format_ident!("Visit{}", field_cat);
        let slot_name = format_ident!("pf{}_slot", i);

        alloc_stmts.push(quote! {
            let #slot_name = results.len();
            results.push(None);
        });
        push_stmts.push(quote! {
            stack.push(NormTask::#visit_task {
                src: &**#name as *const _,
                slot: #slot_name,
            });
        });
        assemble_refs.push(quote! { #slot_name });
    }

    (alloc_stmts, push_stmts, assemble_refs)
}

/// β-reduction Visit arm: push AssembleBetaApply + Visit<Cat>(lam) + Visit<Dom>(arg).
fn generate_beta_apply_visit_arm(cat: &Ident, label: &Ident, dom_str: &str) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaApply_{}_{}", cat, dom_ident);
    let lam_visit = format_ident!("Visit{}", cat); // Apply<Dom>(Box<Cat>, Box<Dom>) — lam is Cat

    // For arg: if Dom is non-native, push Visit<Dom>. If Dom is native,
    // clone eagerly. We use the SAME dispatch as regular-field handling.
    // But we need access to the `language` to check — defer to a shared
    // emission helper that knows both cases. Here, we detect native vs
    // non-native at emission time via the category list... we DON'T have
    // the language here. Instead, emit code that handles both uniformly
    // via Visit<Dom> and rely on the Dom's category being present in the
    // PDA if non-native (if native, the Visit<Dom> doesn't exist — which
    // would be a compile error). For Calculator, Dom is typically Int/
    // Bool (native), which means we need NATIVE arg handling inline.
    //
    // Since we don't have `language` here, the caller must detect Dom's
    // native-ness. Let's thread it in.
    //
    // TEMPORARY: assume Dom is non-native (Visit<Dom> exists). This works
    // for grammars where HOL domains are non-native (e.g. lambda calculi).
    // For Calculator with Int-domain HOL, we need a different path.
    let arg_visit = format_ident!("Visit{}", dom_ident);

    quote! {
        #cat::#label(lam_box, arg_box) => {
            let lam_slot = results.len();
            results.push(None);
            let arg_slot = results.len();
            results.push(None);

            stack.push(NormTask::#assemble_variant { slot, lam_slot, arg_slot });
            // Push in reverse order so lam is processed first (LIFO).
            stack.push(NormTask::#arg_visit {
                src: &**arg_box as *const _,
                slot: arg_slot,
            });
            stack.push(NormTask::#lam_visit {
                src: &**lam_box as *const _,
                slot: lam_slot,
            });
        }
    }
}

/// β-reduction (multi-binder) Visit arm.
fn generate_beta_mapply_visit_arm(cat: &Ident, label: &Ident, dom_str: &str) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaMApply_{}_{}", cat, dom_ident);
    let lam_visit = format_ident!("Visit{}", cat);
    let arg_visit = format_ident!("Visit{}", dom_ident);

    quote! {
        #cat::#label(lam_box, args) => {
            let lam_slot = results.len();
            results.push(None);
            let args_start = results.len();
            for _ in 0..args.len() {
                results.push(None);
            }
            let args_count = args.len();

            stack.push(NormTask::#assemble_variant {
                slot,
                lam_slot,
                args_start,
                args_count,
            });
            // Push args in reverse order (LIFO).
            for (idx, arg) in args.iter().enumerate().rev() {
                stack.push(NormTask::#arg_visit {
                    src: arg as *const _,
                    slot: args_start + idx,
                });
            }
            stack.push(NormTask::#lam_visit {
                src: &**lam_box as *const _,
                slot: lam_slot,
            });
        }
    }
}

/// Cancellation pair outer Visit arm.
fn generate_cancel_visit_arm(cat: &Ident, label: &Ident, pair: &CancellationPair) -> TokenStream {
    let inner_cat = &pair.inner_category;
    let assemble_variant = format_ident!("AssembleCancel_{}_{}_{}", cat, inner_cat, label);
    let inner_visit = format_ident!("Visit{}", inner_cat);

    quote! {
        #cat::#label(f0) => {
            let inner_slot = results.len();
            results.push(None);

            stack.push(NormTask::#assemble_variant { slot, inner_slot });
            stack.push(NormTask::#inner_visit {
                src: &**f0 as *const _,
                slot: inner_slot,
            });
        }
    }
}

// =============================================================================
// Assemble Arms
// =============================================================================

/// Dispatch per-variant Assemble arm. Leaf variants have no Assemble arm.
fn generate_assemble_arm(
    cat: &Ident,
    variant: &VariantKind,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
    is_native: bool,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. } | VariantKind::Literal { .. } | VariantKind::Nullary { .. } => None,

        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return Some(generate_beta_apply_assemble_arm(cat, dom_str));
                }
            }
            if let Some(dom_str) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return Some(generate_beta_mapply_assemble_arm(cat, dom_str));
                }
            }

            // Cancellation
            if let Some(pair) = cancel_set.get(&(cat_str.to_string(), label_str.clone())) {
                return Some(generate_cancel_assemble_arm(cat, label, pair));
            }

            Some(generate_regular_assemble_arm(cat, label, fields, is_native))
        },

        VariantKind::Collection { label, element_cat, coll_type } => {
            Some(generate_collection_assemble_arm(cat, label, element_cat, coll_type))
        },

        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        },

        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            Some(generate_multi_binder_assemble_arm(cat, label, pre_scope_fields, body_cat))
        },
    }
}

/// Regular Assemble arm: extract fields from slots, reconstruct.
///
/// For NATIVE categories, additionally apply `try_fold_to_literal()` (which
/// takes `&self` and returns `Option<Self>`) for constant folding — e.g.
/// `Int::Add(NumLit(2), NumLit(3))` → `Int::NumLit(5)`. Matches pre-PDA
/// native normalize behavior.
///
/// **Frame-size fix (PDA stack-safety, second tier):** wraps the body in a
/// local `#[inline(never)]` inner fn so per-variant locals (`field_N`,
/// `Box::new(...)`, `reconstructed`, `folded`) live in the helper's frame
/// instead of `normalize_iterative`'s. See
/// `iterative_clone.rs::generate_regular_assemble_arm` for the same idiom.
fn generate_regular_assemble_arm(
    cat: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    is_native: bool,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleReg_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);

    // Build flat (pat-name, helper-arg-decl, helper-arg-name) lists.
    let mut pat_flat: Vec<TokenStream> = Vec::new();
    let mut decl_flat: Vec<TokenStream> = Vec::new();
    let mut call_flat: Vec<TokenStream> = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        if field.is_optional {
            if field.is_collection {
                // Phase 4 #3 (2026-05-12): Optional-Collection — cloned carrier.
                let cloned = format_ident!("f{}_cloned", i);
                let ty = optional_collection_field_type(field);
                pat_flat.push(quote! { #cloned });
                decl_flat.push(quote! { #cloned: #ty });
                call_flat.push(quote! { #cloned });
                continue;
            }
            let slot_name = format_ident!("f{}_slot", i);
            let some_flag = format_ident!("f{}_some", i);
            pat_flat.push(quote! { #slot_name });
            pat_flat.push(quote! { #some_flag });
            decl_flat.push(quote! { #slot_name: usize });
            decl_flat.push(quote! { #some_flag: bool });
            call_flat.push(quote! { #slot_name });
            call_flat.push(quote! { #some_flag });
            continue;
        }
        if field.is_collection {
            let start_name = format_ident!("f{}_start", i);
            let count_name = format_ident!("f{}_count", i);
            pat_flat.push(quote! { #start_name });
            decl_flat.push(quote! { #start_name: usize });
            call_flat.push(quote! { #start_name });
            pat_flat.push(quote! { #count_name });
            decl_flat.push(quote! { #count_name: usize });
            call_flat.push(quote! { #count_name });
            // Phase 4 #5b (2026-05-12): HashBag carries `counts` Vec
            // (multiplicities); HashMap does NOT (entries stored as
            // 2*N flat slots). Distinguish.
            if matches!(
                field.coll_type.as_ref().unwrap_or(&CollectionType::Vec),
                CollectionType::HashBag
            ) {
                let counts_name = format_ident!("f{}_counts", i);
                pat_flat.push(quote! { #counts_name });
                decl_flat.push(quote! { #counts_name: Vec<usize> });
                call_flat.push(quote! { #counts_name });
            }
        } else {
            let slot_name = format_ident!("f{}_slot", i);
            pat_flat.push(quote! { #slot_name });
            decl_flat.push(quote! { #slot_name: usize });
            call_flat.push(quote! { #slot_name });
        }
    }

    let field_extracts: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_reg_field_extract(i, field))
        .collect();

    let construct_fields: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_reg_field_construct(i, field))
        .collect();

    let finalize = if is_native {
        quote! {
            let folded = reconstructed.try_fold_to_literal().unwrap_or(reconstructed);
            results[slot] = Some(AnyNormalizedTerm::#wrap(folded));
        }
    } else {
        quote! {
            results[slot] = Some(AnyNormalizedTerm::#wrap(reconstructed));
        }
    };

    quote! {
        NormTask::#assemble_variant { slot, #(#pat_flat),* } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble(
                results: &mut Vec<Option<AnyNormalizedTerm>>,
                slot: usize,
                #(#decl_flat),*
            ) {
                #(#field_extracts)*
                let reconstructed = #cat::#label(#(#construct_fields),*);
                #finalize
            }
            assemble(results, slot, #(#call_flat),*);
        }
    }
}

fn emit_reg_field_extract(i: usize, field: &FieldInfo) -> TokenStream {
    if field.is_predicate {
        // Already in scope as f{i}_pred
        return quote! {};
    }
    let result_ident = format_ident!("field_{}", i);
    let wrap = format_ident!("Wrap{}", field.category);

    if field.is_optional {
        if field.is_collection {
            // Phase 4 #3 (2026-05-12): Optional-Collection — the cloned
            // carrier is already bound by name in scope; extract just
            // rebinds it to field_<i>.
            let cloned = format_ident!("f{}_cloned", i);
            return quote! {
                let #result_ident = #cloned;
            };
        }
        // Opt-Group: extract Option<Box<Cat>> from slot+some_flag.
        let slot_name = format_ident!("f{}_slot", i);
        let some_flag = format_ident!("f{}_some", i);
        return quote! {
            let #result_ident: Option<std::sync::Arc<_>> = if #some_flag {
                match results[#slot_name].take()
                    .expect("normalize: missing optional inner")
                {
                    AnyNormalizedTerm::#wrap(v) => Some(std::sync::Arc::new(v)),
                    _ => unreachable!("normalize: wrong category in optional slot"),
                }
            } else {
                None
            };
        };
    }

    if field.is_collection {
        let start_name = format_ident!("f{}_start", i);
        let count_name = format_ident!("f{}_count", i);
        return match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
            CollectionType::HashBag => {
                let counts_name = format_ident!("f{}_counts", i);
                // For HashBag collections inside Regular variants (e.g.
                // a Proc with a HashBag<Int> field), the elements are
                // single-category. Reassemble into a bag. We DON'T use
                // insert_into (that's only for the top-level Collection
                // variants that flatten same-label bags).
                quote! {
                    let mut #result_ident = mettail_runtime::HashBag::new();
                    for (idx, count) in #counts_name.iter().enumerate() {
                        match results[#start_name + idx].take()
                            .expect("normalize: missing collection element")
                        {
                            AnyNormalizedTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                            _ => unreachable!("normalize: wrong category in collection slot"),
                        }
                    }
                }
            },
            // Phase 4 #5b (2026-05-12): HashMap — 2*N flat slots laid
            // out as (k0, v0, k1, v1, ...) per `emit_collection_field_alloc`.
            // Reconstruct entries by zipping consecutive pairs.
            CollectionType::HashMap => {
                quote! {
                    let mut #result_ident =
                        mettail_runtime::HashMapLit::default();
                    for entry_idx in 0..#count_name {
                        let k_slot = #start_name + entry_idx * 2;
                        let v_slot = #start_name + entry_idx * 2 + 1;
                        let k = match results[k_slot].take()
                            .expect("normalize: missing hashmap key")
                        {
                            AnyNormalizedTerm::#wrap(v) => v,
                            _ => unreachable!("normalize: wrong category in hashmap k slot"),
                        };
                        let v = match results[v_slot].take()
                            .expect("normalize: missing hashmap value")
                        {
                            AnyNormalizedTerm::#wrap(v) => v,
                            _ => unreachable!("normalize: wrong category in hashmap v slot"),
                        };
                        #result_ident.insert(k, v);
                    }
                }
            },
            CollectionType::Vec => {
                quote! {
                    let mut #result_ident = Vec::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        match results[#start_name + idx].take()
                            .expect("normalize: missing vec element")
                        {
                            AnyNormalizedTerm::#wrap(v) => #result_ident.push(v),
                            _ => unreachable!("normalize: wrong category in vec slot"),
                        }
                    }
                }
            },
            CollectionType::HashSet => {
                quote! {
                    let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        match results[#start_name + idx].take()
                            .expect("normalize: missing hashset element")
                        {
                            AnyNormalizedTerm::#wrap(v) => { #result_ident.insert(v); },
                            _ => unreachable!("normalize: wrong category in hashset slot"),
                        }
                    }
                }
            },
        };
    }

    let slot_name = format_ident!("f{}_slot", i);
    // For non-collection scalar fields, we pushed None for native cross-cat
    // (just cloned); for others we pushed a Visit task that fills the slot.
    // Distinguish at extraction: if results[slot] is None, the Visit task
    // wasn't pushed (native cross-cat case — use the cloned value, but we
    // didn't store it anywhere!). Let's handle the non-native case
    // uniformly: extract from the slot.
    quote! {
        let #result_ident = match results[#slot_name].take()
            .expect("normalize: missing result in slot")
        {
            AnyNormalizedTerm::#wrap(v) => v,
            _ => unreachable!("normalize: wrong category in slot"),
        };
    }
}

fn emit_reg_field_construct(i: usize, field: &FieldInfo) -> TokenStream {
    if field.is_predicate {
        let pred_name = format_ident!("f{}_pred", i);
        return quote! { #pred_name };
    }
    let result_ident = format_ident!("field_{}", i);
    if field.is_optional {
        // Already Option<Box<Cat>> from extract; pass through.
        quote! { #result_ident }
    } else if field.is_collection {
        quote! { #result_ident }
    } else {
        quote! { std::sync::Arc::new(#result_ident) }
    }
}

/// Collection Assemble arm: reconstruct via insert_into_<label> helper.
fn generate_collection_assemble_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleColl_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let elem_wrap = format_ident!("Wrap{}", element_cat);

    // See `iterative_clone.rs::generate_collection_assemble_arm` for the
    // per-arm `#[inline(never)]` peel rationale.
    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap => {
            let helper_name = format_ident!("insert_into_{}", label.to_string().to_lowercase());
            quote! {
                NormTask::#assemble_variant { slot, elements_start, elements_count, counts_vec } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnyNormalizedTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                        counts_vec: Vec<usize>,
                    ) {
                        let mut new_bag = mettail_runtime::HashBag::new();
                        for (idx, count) in counts_vec.iter().enumerate() {
                            match results[elements_start + idx].take()
                                .expect("normalize: missing hashbag element")
                            {
                                AnyNormalizedTerm::#elem_wrap(v) => {
                                    for _ in 0..*count {
                                        #cat::#helper_name(&mut new_bag, v.clone());
                                    }
                                }
                                _ => unreachable!("normalize: wrong category in hashbag slot"),
                            }
                        }
                        results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label(new_bag)));
                    }
                    assemble(results, slot, elements_start, elements_count, counts_vec);
                }
            }
        },
        CollectionType::Vec => {
            quote! {
                NormTask::#assemble_variant { slot, elements_start, elements_count } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnyNormalizedTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    ) {
                        let mut vec = Vec::with_capacity(elements_count);
                        for idx in 0..elements_count {
                            match results[elements_start + idx].take()
                                .expect("normalize: missing vec element")
                            {
                                AnyNormalizedTerm::#elem_wrap(v) => vec.push(v),
                                _ => unreachable!("normalize: wrong category in vec slot"),
                            }
                        }
                        results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label(vec)));
                    }
                    assemble(results, slot, elements_start, elements_count);
                }
            }
        },
        CollectionType::HashSet => {
            quote! {
                NormTask::#assemble_variant { slot, elements_start, elements_count } => {
                    #[inline(never)]
                    #[allow(dead_code, unused_variables, non_snake_case)]
                    fn assemble(
                        results: &mut Vec<Option<AnyNormalizedTerm>>,
                        slot: usize,
                        elements_start: usize,
                        elements_count: usize,
                    ) {
                        let mut set = std::collections::HashSet::with_capacity(elements_count);
                        for idx in 0..elements_count {
                            match results[elements_start + idx].take()
                                .expect("normalize: missing hashset element")
                            {
                                AnyNormalizedTerm::#elem_wrap(v) => { set.insert(v); },
                                _ => unreachable!("normalize: wrong category in hashset slot"),
                            }
                        }
                        results[slot] = Some(AnyNormalizedTerm::#wrap(#cat::#label(set)));
                    }
                    assemble(results, slot, elements_start, elements_count);
                }
            }
        },
    }
}

/// Binder Assemble arm.
fn generate_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleBind_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_slot_pattern(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    quote! {
        NormTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #(#pre_extracts)*
            let body = match results[body_slot].take()
                .expect("normalize: missing binder body")
            {
                AnyNormalizedTerm::#body_wrap(v) => v,
                _ => unreachable!("normalize: wrong category in binder body"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
            results[slot] = Some(AnyNormalizedTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
}

fn generate_multi_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleMBind_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_slot_pattern(pre_scope_fields);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields);

    quote! {
        NormTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #(#pre_extracts)*
            let body = match results[body_slot].take()
                .expect("normalize: missing multi-binder body")
            {
                AnyNormalizedTerm::#body_wrap(v) => v,
                _ => unreachable!("normalize: wrong category in multi-binder body"),
            };
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(cloned_pattern, std::sync::Arc::new(body));
            results[slot] = Some(AnyNormalizedTerm::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        }
    }
}

fn emit_pre_field_slot_pattern(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name };
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — cloned carrier name.
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                return quote! { #cloned };
            }
            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! { #start_name, #count_name, #counts_name }
                    },
                    _ => quote! { #start_name, #count_name },
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! { #slot_name }
            }
        })
        .collect()
}

fn emit_pre_field_extracts(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                return quote! {};
            }
            // Phase 4 #4 (2026-05-12): Optional-Collection — the cloned carrier
            // is already bound by name in the assemble arm; rebind it to
            // pre_field_<i> for the construct step.
            if field.is_optional && field.is_collection {
                let cloned = format_ident!("pf{}_cloned", i);
                let result_ident = format_ident!("pre_field_{}", i);
                return quote! {
                    let #result_ident = #cloned;
                };
            }
            let wrap = format_ident!("Wrap{}", field.category);
            let result_ident = format_ident!("pre_field_{}", i);

            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                match results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope collection element")
                                {
                                    AnyNormalizedTerm::#wrap(v) => #result_ident.insert_n(v, *count),
                                    _ => unreachable!("normalize: wrong category in pre-scope collection slot"),
                                }
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope vec element")
                                {
                                    AnyNormalizedTerm::#wrap(v) => #result_ident.push(v),
                                    _ => unreachable!("normalize: wrong category in pre-scope vec slot"),
                                }
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                match results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope hashset element")
                                {
                                    AnyNormalizedTerm::#wrap(v) => { #result_ident.insert(v); },
                                    _ => unreachable!("normalize: wrong category in pre-scope hashset slot"),
                                }
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! {
                    let #result_ident = match results[#slot_name].take()
                        .expect("normalize: missing pre-scope result")
                    {
                        AnyNormalizedTerm::#wrap(v) => v,
                        _ => unreachable!("normalize: wrong category in pre-scope slot"),
                    };
                }
            }
        })
        .collect()
}

fn emit_pre_field_constructs(pre_scope_fields: &[FieldInfo]) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                return quote! { #pred_name, };
            }
            let result_ident = format_ident!("pre_field_{}", i);
            // Phase 4 #4 (2026-05-12): Optional-Collection — already
            // Option<Container>, pass through without Box wrapping.
            if field.is_optional && field.is_collection {
                return quote! { #result_ident, };
            }
            if field.is_collection {
                quote! { #result_ident, }
            } else {
                quote! { std::sync::Arc::new(#result_ident), }
            }
        })
        .collect()
}

/// β-reduction Assemble arm.
///
/// 1. Take lam and arg from slots.
/// 2. If lam matches `Cat::Lam<Dom>(scope)`:
///    a. Unbind to get (binder, body).
///    b. Call `body.substitute_<dom>(&binder.0, &arg)` via the subst PDA.
///    c. Box the substituted Cat into `sources`, push `Visit<Cat>` to
///       renormalize — iterative, not recursive.
/// 3. Else: reconstruct `Cat::Apply<Dom>(Box::new(lam), Box::new(arg))`.
fn generate_beta_apply_assemble_arm(cat: &Ident, dom_str: &str) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaApply_{}_{}", cat, dom_ident);
    let wrap_cat = format_ident!("Wrap{}", cat);
    let wrap_dom = format_ident!("Wrap{}", dom_ident);
    let lam_variant = format_ident!("Lam{}", dom_ident);
    let apply_variant = format_ident!("Apply{}", dom_ident);
    let subst_method = format_ident!("substitute_{}", dom_str.to_lowercase());
    let visit_cat = format_ident!("Visit{}", cat);

    quote! {
        NormTask::#assemble_variant { slot, lam_slot, arg_slot } => {
            let lam = match results[lam_slot].take()
                .expect("normalize β: missing lam")
            {
                AnyNormalizedTerm::#wrap_cat(v) => v,
                _ => unreachable!("normalize β: wrong category in lam slot"),
            };
            let arg = match results[arg_slot].take()
                .expect("normalize β: missing arg")
            {
                AnyNormalizedTerm::#wrap_dom(v) => v,
                _ => unreachable!("normalize β: wrong category in arg slot"),
            };

            // Ref-match to avoid moving out of `lam` (which impls Drop).
            if let #cat::#lam_variant(scope) = &lam {
                // β-reduce: clone scope, unbind, substitute, renormalize.
                let (binder, body) = scope.clone().unbind();
                let substituted = (*body).#subst_method(&binder.0, &arg);
                sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(substituted)));
                let src_ptr: *const #cat = {
                    let last_box = sources.last().expect("just pushed");
                    match &**last_box {
                        AnyNormalizedTerm::#wrap_cat(v) => v as *const _,
                        _ => unreachable!(),
                    }
                };
                // Drop lam + arg explicitly so we don't hold them across stack push.
                drop(lam);
                drop(arg);
                stack.push(NormTask::#visit_cat { src: src_ptr, slot });
            } else {
                // Not a β-redex — reconstruct Apply with normalized subterms.
                results[slot] = Some(AnyNormalizedTerm::#wrap_cat(
                    #cat::#apply_variant(std::sync::Arc::new(lam), std::sync::Arc::new(arg))
                ));
            }
        }
    }
}

/// Multi-β Assemble arm.
fn generate_beta_mapply_assemble_arm(cat: &Ident, dom_str: &str) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaMApply_{}_{}", cat, dom_ident);
    let wrap_cat = format_ident!("Wrap{}", cat);
    let wrap_dom = format_ident!("Wrap{}", dom_ident);
    let mlam_variant = format_ident!("MLam{}", dom_ident);
    let mapply_variant = format_ident!("MApply{}", dom_ident);
    let multi_subst_method = format_ident!("multi_substitute_{}", dom_str.to_lowercase());
    let visit_cat = format_ident!("Visit{}", cat);

    quote! {
        NormTask::#assemble_variant { slot, lam_slot, args_start, args_count } => {
            let lam = match results[lam_slot].take()
                .expect("normalize multi-β: missing lam")
            {
                AnyNormalizedTerm::#wrap_cat(v) => v,
                _ => unreachable!("normalize multi-β: wrong category in lam slot"),
            };
            let mut args_vec: Vec<#dom_ident> = Vec::with_capacity(args_count);
            for idx in 0..args_count {
                match results[args_start + idx].take()
                    .expect("normalize multi-β: missing arg")
                {
                    AnyNormalizedTerm::#wrap_dom(v) => args_vec.push(v),
                    _ => unreachable!("normalize multi-β: wrong category in arg slot"),
                }
            }

            if let #cat::#mlam_variant(scope) = &lam {
                let (binders, body) = scope.clone().unbind();
                let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                let substituted = (*body).#multi_subst_method(&vars, &args_vec);
                sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(substituted)));
                let src_ptr: *const #cat = {
                    let last_box = sources.last().expect("just pushed");
                    match &**last_box {
                        AnyNormalizedTerm::#wrap_cat(v) => v as *const _,
                        _ => unreachable!(),
                    }
                };
                drop(lam);
                stack.push(NormTask::#visit_cat { src: src_ptr, slot });
            } else {
                results[slot] = Some(AnyNormalizedTerm::#wrap_cat(
                    #cat::#mapply_variant(std::sync::Arc::new(lam), args_vec)
                ));
            }
        }
    }
}

/// Cancellation Assemble arm.
fn generate_cancel_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pair: &CancellationPair,
) -> TokenStream {
    let inner_cat = &pair.inner_category;
    let inner_ctor = &pair.inner_constructor;
    let assemble_variant = format_ident!("AssembleCancel_{}_{}_{}", cat, inner_cat, label);
    let wrap_cat = format_ident!("Wrap{}", cat);
    let wrap_inner = format_ident!("Wrap{}", inner_cat);
    let visit_cat = format_ident!("Visit{}", cat);

    quote! {
        NormTask::#assemble_variant { slot, inner_slot } => {
            let inner = match results[inner_slot].take()
                .expect("normalize cancel: missing inner")
            {
                AnyNormalizedTerm::#wrap_inner(v) => v,
                _ => unreachable!("normalize cancel: wrong category in inner slot"),
            };

            if let #inner_cat::#inner_ctor(p) = &inner {
                // Peel: clone the inner-inner, reschedule for renormalize.
                let peeled: #cat = (**p).clone();
                sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(peeled)));
                let src_ptr: *const #cat = {
                    let last_box = sources.last().expect("just pushed");
                    match &**last_box {
                        AnyNormalizedTerm::#wrap_cat(v) => v as *const _,
                        _ => unreachable!(),
                    }
                };
                drop(inner);
                stack.push(NormTask::#visit_cat { src: src_ptr, slot });
            } else {
                results[slot] = Some(AnyNormalizedTerm::#wrap_cat(
                    #cat::#label(std::sync::Arc::new(inner))
                ));
            }
        }
    }
}

// =============================================================================
// Per-category normalize wrappers
// =============================================================================

/// Emit `impl Cat { pub fn normalize(&self) -> Self { PDA wrapper } }` for a
/// non-native category.
fn generate_norm_wrapper(cat: &Ident) -> TokenStream {
    let visit_variant = format_ident!("Visit{}", cat);
    let wrap = format_ident!("Wrap{}", cat);

    quote! {
        impl #cat {
            /// Iteratively normalize this term. Uses a shared PDA driver
            /// across all non-native categories to handle cross-category
            /// traversal, β-reduction, cancellation pairs, and collection
            /// flattening without any recursion or mutual recursion.
            #[allow(unreachable_patterns)]
            pub fn normalize(&self) -> Self {
                let result: Self = NORM_TASK_POOL.with(|t| {
                    NORM_RESULT_POOL.with(|r| {
                        NORM_SOURCE_POOL.with(|s| {
                            let mut stack = t.take();
                            let mut results = r.take();
                            let mut sources = s.take();
                            stack.clear();
                            results.clear();
                            sources.clear();

                            results.push(None);
                            stack.push(NormTask::#visit_variant {
                                src: self as *const _,
                                slot: 0,
                            });

                            normalize_iterative(&mut stack, &mut results, &mut sources);

                            let root = match results[0].take()
                                .expect("normalize: root slot empty")
                            {
                                AnyNormalizedTerm::#wrap(v) => v,
                                _ => unreachable!("normalize: wrong category in root slot"),
                            };

                            s.set(sources);
                            r.set(results);
                            t.set(stack);
                            root
                        })
                    })
                });
                result
            }
        }
    }
}
