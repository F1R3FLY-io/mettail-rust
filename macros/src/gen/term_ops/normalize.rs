//! Normalize generation — PDA-driven for non-native categories.
//!
//! Every semantic category shares one explicit-worklist PDA. This eliminates
//! mutual recursion between category-specific `normalize` methods while
//! preserving generated native folds at the category assembly boundary.
//!
//! ## Architecture (non-native shared PDA)
//!
//! - `AnyNormalizedTerm` is the typed result coproduct, with one `Wrap<Cat>`
//!   injection per semantic category.
//! - `__MettailDovetailRebuildValue` is the shared typed field coproduct used
//!   by both normalization and Dovetail reconstruction.
//! - `Visit<Cat>` normalizes a borrowed category value.
//! - `AssembleTagged<Cat>` schedules the category-local field program for an
//!   ordinary constructor. `AssembleShared<Cat>` invokes the one exact typed
//!   constructor kernel after its field values have been produced.
//! - Optional absence, ordered sequences, collection carriers, and binder
//!   fields are represented explicitly in the shared value stack. Reverse
//!   scheduling on the task stack preserves semantic field order.
//! - `AssembleBetaApply<Cat>` and `AssembleBetaMApply<Cat>` carry a dense
//!   constructor tag. Domain selection happens inside one host-category
//!   dispatcher rather than in a host-by-domain task family.
//! - Cancellation and owned-source revisit frames remain disjoint special
//!   transitions. Their non-reduction paths use exact typed construction.
//! - TLS pools: `NORM_TASK_POOL`, `NORM_RESULT_POOL`, `NORM_VALUE_POOL`, and
//!   `NORM_SOURCE_POOL`.
//!   Source pool holds `Vec<Box<AnyNormalizedTerm>>` for β/cancel-rescheduled
//!   owned values. Boxes have stable heap addresses; raw pointers derived
//!   from them remain valid for the call duration even as the Vec grows.
//!
//! ## β-reduction iterative flow
//!
//! ```text
//! AssembleBetaApply<Cat> { constructor, slot, lam_slot, arg_slot }:
//!   lam_normalized = results[lam_slot].take()
//!   arg_normalized = results[arg_slot].take()
//!   if lam_normalized is an admitted Cat::Lam<Domain>(scope):
//!     choose Domain from the checked constructor tag
//!     (binder, body) = scope.unbind()
//!     substituted = body.substitute_<domain>(&binder.0, &arg_normalized)
//!     sources.push(Box::new(AnyNorm::Wrap<Cat>(substituted)))
//!     src_ptr = &*sources.last() -> Cat (stable)
//!     stack.push(Visit<Cat> { src: src_ptr, slot })
//!   else:
//!     feed lam_normalized and arg_normalized to the shared typed constructor kernel
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

use crate::gen::runtime::dovetail_report::semantic_adapter::{
    SemanticAdapterLayout, SemanticCategoryLayout, SemanticCollectionProjection,
    SemanticFieldLayout, SemanticFieldProjection, SemanticVariantLayout,
};
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::grammar::{GrammarItem, TermParam};
use mettail_ast::language::{LangType, LanguageDef};
use mettail_ast::pattern::CancellationPair;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use syn::Ident;

use crate::gen::native_carrier::NativeRecursiveCarrier;

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

        // (#101 sibling) The helper is an ASSOCIATIVITY device — it peels a nested
        // `Cat::Label(inner)` and re-inserts its members — and its emitted body is
        // `HashBag`-shaped throughout: a `&mut HashBag<Cat>` parameter, `(elem, count)`
        // iteration, `bag.insert`. That is right for the unordered multiset containers, whose
        // `normalize` Assemble arm is the only caller (see `generate_collection_assemble_arm`,
        // which dispatches on exactly `HashBag | HashMap | PathMap`).
        //
        // An ORDERED (`Vec`) collection constructor has no associativity to exploit and no
        // caller: its Assemble arm rebuilds the vector positionally. Emitting the helper for
        // one produced `HashBag<Cat>`-typed code against a `Vec<Cat>` field — three compile
        // errors per constructor in a language that could therefore never be declared. The
        // corpus has zero ordered whole-constructor collections (every one is a `HashBag`), so
        // gating on the container is byte-identical for every existing language.
        let flattenable_collection = rule.items.iter().any(|item| {
            matches!(
                item,
                GrammarItem::Collection {
                    coll_type: CollectionType::HashBag
                        | CollectionType::HashMap
                        | CollectionType::PathMap,
                    ..
                }
            )
        });

        if !flattenable_collection {
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
    let all_cats: Vec<&LangType> = crate::gen::semantic_transit_types(language).collect();

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
    let semantic_layout = match SemanticAdapterLayout::derive(language) {
        Ok(layout) => layout,
        Err(error) => {
            let message = format!("normalize semantic adapter layout: {error}");
            return quote! { compile_error!(#message); };
        },
    };
    let shared_typed_assembly =
        crate::gen::runtime::dovetail_report::reconstruct::typed_assembly_support(
            language,
            &semantic_layout,
        );
    let any_norm_term = generate_any_normalized_term_enum(non_native_cats);
    let norm_task =
        generate_norm_task_enum(non_native_cats, &semantic_layout, language, cancellation_pairs);
    let tls = generate_norm_tls_pools();
    let driver =
        generate_norm_driver(non_native_cats, &semantic_layout, language, cancellation_pairs);
    let wrappers: Vec<TokenStream> = crate::gen::semantic_types(language)
        .map(|t| generate_norm_wrapper(&t.name))
        .collect();

    quote! {
        #shared_typed_assembly
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
    let borrow_methods: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|target| {
            let target_cat = &target.name;
            let method = any_norm_borrow_method(target_cat);
            let arms: Vec<TokenStream> = non_native_cats
                .iter()
                .map(|actual| {
                    let actual_cat = &actual.name;
                    let wrap = format_ident!("Wrap{}", actual_cat);
                    if actual_cat == target_cat {
                        quote! { Self::#wrap(value) => Some(value) }
                    } else {
                        quote! { Self::#wrap(_) => None }
                    }
                })
                .collect();
            quote! {
                #[inline]
                fn #method(&self) -> Option<&#target_cat> {
                    match self {
                        #(#arms),*
                    }
                }
            }
        })
        .collect();
    let take_sequence_functions: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|target| {
            let category = &target.name;
            let function = any_norm_take_sequence_function(category);
            let take = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
                category,
            );
            quote! {
                #[inline]
                fn #function(
                    results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
                    start: usize,
                    count: usize,
                ) -> Vec<#category> {
                    let mut values = Vec::with_capacity(count);
                    for index in 0..count {
                        values.push(
                            results[start + index]
                                .take()
                                .expect("normalize: missing typed sequence element")
                                .#take()
                                .expect("normalize: typed sequence category mismatch"),
                        );
                    }
                    values
                }
            }
        })
        .collect();

    quote! {
        /// Result-buffer element for the iterative normalize engine.
        #[derive(Clone)]
        #[allow(dead_code)]
        enum AnyNormalizedTerm {
            #(#variants),*
        }

        impl AnyNormalizedTerm {
            #(#borrow_methods)*
        }

        #(#take_sequence_functions)*
    }
}

fn any_norm_borrow_method(category: &Ident) -> Ident {
    let encoded = category
        .to_string()
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("__mettail_borrow_normalized_{encoded}")
}

fn any_norm_take_sequence_function(category: &Ident) -> Ident {
    let encoded = category
        .to_string()
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("__mettail_take_normalized_sequence_{encoded}")
}

/// Emit the work-stack frame enum.
fn generate_norm_task_enum(
    non_native_cats: &[&LangType],
    semantic_layout: &SemanticAdapterLayout,
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

    // One typed ordinary-assembly frame per category.  The source pointer uses
    // the same lifetime seam as Visit<Cat>; the dense constructor tag and exact
    // result interval are the complete dynamic frame.  Constructor-specific
    // carriers no longer inflate NormTask's algebraic data type.
    let tagged_assemble_variants: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let cat = category.category();
            let variant = format_ident!("AssembleTagged{}", cat);
            quote! {
                #variant {
                    src: *const #cat,
                    constructor: u32,
                    slot: usize,
                    value_base: usize,
                    value_count: usize,
                }
            }
        })
        .collect();

    let shared_assemble_variants: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let cat = category.category();
            let variant = format_ident!("AssembleShared{}", cat);
            quote! {
                #variant {
                    constructor: u32,
                    slot: usize,
                    value_base: usize,
                    value_count: usize,
                }
            }
        })
        .collect();

    let pack_sequence_variants: Vec<TokenStream> = semantic_layout
        .ordered_sequence_elements()
        .map(|category| {
            let variant = format_ident!("PackSharedSequence{}", category);
            quote! {
                #variant { value_base: usize, value_count: usize }
            }
        })
        .collect();

    let tagged_beta_variants: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .flat_map(|category| {
            let cat = category.category();
            let cat_name = cat.to_string();
            let has_apply = category.variants().iter().any(|variant| {
                matches!(variant.kind(), VariantKind::Regular { label, .. }
                if strip_prefix(&label.to_string(), "Apply").is_some_and(|domain| {
                    hol_pairs.contains(&(cat_name.clone(), domain.to_string()))
                }))
            });
            let has_mapply = category.variants().iter().any(|variant| {
                matches!(variant.kind(), VariantKind::Regular { label, .. }
                if strip_prefix(&label.to_string(), "MApply").is_some_and(|domain| {
                    hol_pairs.contains(&(cat_name.clone(), domain.to_string()))
                }))
            });
            let apply = has_apply.then(|| {
                let task = format_ident!("AssembleBetaApply{}", cat);
                quote! {
                    #task {
                        constructor: u32,
                        slot: usize,
                        lam_slot: usize,
                        arg_slot: usize,
                    }
                }
            });
            let mapply = has_mapply.then(|| {
                let task = format_ident!("AssembleBetaMApply{}", cat);
                quote! {
                    #task {
                        constructor: u32,
                        slot: usize,
                        lam_slot: usize,
                        args_start: usize,
                        args_count: usize,
                    }
                }
            });
            apply.into_iter().chain(mapply)
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
            #(#tagged_assemble_variants,)*
            #(#shared_assemble_variants,)*
            #(#pack_sequence_variants,)*
            #(#tagged_beta_variants,)*
            MoveResultToShared { slot: usize, repeat: usize },
            PushSharedValue(__MettailDovetailRebuildValue),
            #(#assemble_variants,)*
        }
    }
}

/// Emit Assemble variant declarations for a non-leaf variant. Returns None
/// for leaf variants (Var, Literal, Nullary) which write directly during Visit.
///
/// HOL Apply<Dom>/MApply<Dom> Regular variants and cancellation-outer Regular
/// variants get special Assemble variants.  Every ordinary Regular uses the
/// category's single tagged assembly frame emitted above.
fn generate_assemble_variant_decl(
    category: &Ident,
    variant: &VariantKind,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. }
        | VariantKind::Literal { .. }
        | VariantKind::CollectionLiteral { .. }
        | VariantKind::Nullary { .. } => None,

        VariantKind::RecursiveNativeLiteral { label, .. } => {
            let variant_name = format_ident!("AssembleNative_{}_{}", category, label);
            Some(quote! {
                #variant_name {
                    slot: usize,
                    mode: mettail_runtime::PathMapMode,
                    elements_start: usize,
                    elements_count: usize,
                    focus: Vec<u8>,
                }
            })
        },

        // ★ #141 G5 — `Some`, never `None`: `None` means "no arm for this
        // variant", which would DISCARD the refusal. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => Some(quote! { compile_error!(#message); }),

        VariantKind::Regular { label, .. } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>: β-reduction Assemble frame
            if let Some(dom) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom.to_string())) {
                    return None;
                }
            }
            if let Some(dom) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom.to_string())) {
                    return None;
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

            // Ordinary constructors use AssembleTagged<Cat>.
            None
        },

        VariantKind::Collection { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => None,
    }
}

/// Phase 4 #3 (2026-05-12): For an Optional-Collection field, derive the
/// runtime carrier type (e.g. `Option<Vec<Proc>>`,
/// `Option<mettail_runtime::HashBag<Proc>>`, etc.) that matches what
/// `enums.rs::one_optional_field` emitted for the AST. Used by the
/// normalize PDA's cloned-carrier path.
#[cfg(test)]
fn optional_collection_field_type(field: &FieldInfo) -> TokenStream {
    let cat = &field.category;
    match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
        CollectionType::Vec => quote! { Option<Vec<#cat>> },
        CollectionType::HashBag => quote! { Option<mettail_runtime::HashBag<#cat>> },
        CollectionType::HashSet => quote! { Option<std::collections::HashSet<#cat>> },
        CollectionType::HashMap | CollectionType::PathMap => {
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
#[cfg(test)]
fn emit_reg_field_decl(i: usize, field: &FieldInfo, language: &LanguageDef) -> TokenStream {
    if field.is_semantic_boundary(language) {
        let carrier = format_ident!("f{}_data", i);
        let ty = field.semantic_boundary_carrier_type();
        return quote! { #carrier: #ty };
    }
    if field.is_opaque_leaf() {
        // L9-3/L9-4: opaque capture leaves (token-text `String` / guest-body
        // `Arc<FltNode>`) are OPAQUE to normalization — cloned through as a bare
        // carrier (not a host term; never β-reduces or α-renames). Mirrors the
        // predicate carrier; the field type is the leaf kind's own type.
        let text_name = format_ident!("f{}_text", i);
        let ty = field.opaque_leaf_type();
        return quote! { #text_name: #ty };
    }
    if field.is_predicate {
        let pred_name = format_ident!("f{}_pred", i);
        // Task #14 (Option<Guard>): a guard inside `#opt(...)` lowers to an
        // `Option<BehavioralPred>` variant field, so the frame slot must
        // carry the same type (the Visit-time `#name.clone()` then matches
        // with zero edits). Predicates are OPAQUE to normalization: cloned
        // through untouched — `None` normalizes to `None`, NEVER to
        // `Some(Top)` (that would render a phantom `where true()` and break
        // the display/parse round-trip).
        if field.is_optional {
            return quote! { #pred_name: Option<mettail_runtime::BehavioralPred> };
        }
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
#[cfg(test)]
fn emit_pre_field_decl_list(
    pre_scope_fields: &[FieldInfo],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_semantic_boundary(language) {
                let carrier = format_ident!("pf{}_data", i);
                let ty = field.semantic_boundary_carrier_type();
                return quote! { #carrier: #ty };
            }
            if field.is_predicate {
                let pred_name = format_ident!("pf{}_pred", i);
                // Task #14 (Option<Guard>): Option-aware pre-scope twin of
                // `emit_reg_field_decl` — dormant until a Binder-rule
                // optional guard exists (in-tree Binder guards are all
                // mandatory), but required for decl/clone type agreement.
                if field.is_optional {
                    return quote! { #pred_name: Option<mettail_runtime::BehavioralPred> };
                }
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
            static NORM_RESULT_POOL:
                std::cell::Cell<Vec<Option<__MettailDovetailRebuildValue>>> =
                std::cell::Cell::new(Vec::new());

            /// Pool for the shared typed-assembly value stack.  Successful
            /// constructor assembly consumes its exact suffix and publishes
            /// one typed result, so nested visits restore their caller's base.
            static NORM_VALUE_POOL:
                std::cell::Cell<Vec<__MettailDovetailRebuildValue>> =
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
    semantic_layout: &SemanticAdapterLayout,
    language: &LanguageDef,
    cancellation_pairs: &[CancellationPair],
) -> TokenStream {
    let hol_pairs = compute_hol_pairs_set(language);
    let cancel_set = compute_cancel_set(cancellation_pairs);

    // Per-category Visit helpers (one fn per cat).
    let visit_helper_fns: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| generate_visit_helper_fn(category, language, &hol_pairs, &cancel_set))
        .collect();

    let tagged_assemble_helper_fns: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let is_native = language
                .get_type(category.category())
                .is_some_and(|lang_type| lang_type.native_type.is_some());
            generate_tagged_assemble_helper_fn(
                category,
                language,
                &hol_pairs,
                &cancel_set,
                is_native,
            )
        })
        .collect();

    let shared_assemble_helper_fns: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let is_native = language
                .get_type(category.category())
                .is_some_and(|lang_type| lang_type.native_type.is_some());
            generate_shared_assemble_helper_fn(category, is_native)
        })
        .collect();

    let (tagged_beta_helper_fns, tagged_beta_assemble_arms): (Vec<TokenStream>, Vec<TokenStream>) =
        semantic_layout
            .categories()
            .iter()
            .map(|category| generate_tagged_beta_support(category, &hol_pairs))
            .unzip();

    // Tiny dispatch arms that delegate to the per-cat helper.
    let visit_arms: Vec<TokenStream> = non_native_cats
        .iter()
        .map(|t| {
            let cat = &t.name;
            let visit_variant = format_ident!("Visit{}", cat);
            let helper_fn = format_ident!("norm_visit_{}", cat.to_string().to_lowercase());
            quote! {
                NormTask::#visit_variant { src, slot } => {
                    #helper_fn(stack, results, values, sources, src, slot);
                }
            }
        })
        .collect();

    let tagged_assemble_arms: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let cat = category.category();
            let variant = format_ident!("AssembleTagged{}", cat);
            let helper = format_ident!("norm_assemble_{}", cat.to_string().to_lowercase());
            quote! {
                NormTask::#variant {
                    src,
                    constructor,
                    slot,
                    value_base,
                    value_count,
                } => {
                    #helper(
                        results,
                        values,
                        src,
                        constructor,
                        slot,
                        value_base,
                        value_count,
                    );
                }
            }
        })
        .collect();

    let shared_assemble_arms: Vec<TokenStream> = semantic_layout
        .categories()
        .iter()
        .map(|category| {
            let cat = category.category();
            let variant = format_ident!("AssembleShared{}", cat);
            let helper = format_ident!("norm_assemble_shared_{}", cat.to_string().to_lowercase());
            quote! {
                NormTask::#variant {
                    constructor,
                    slot,
                    value_base,
                    value_count,
                } => {
                    #helper(results, values, constructor, slot, value_base, value_count);
                }
            }
        })
        .collect();

    let pack_sequence_arms: Vec<TokenStream> = semantic_layout
        .ordered_sequence_elements()
        .map(|category| {
            let task = format_ident!("PackSharedSequence{}", category);
            let sequence =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_seq_value_variant(
                    category,
                );
            let take = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
                category,
            );
            quote! {
                NormTask::#task { value_base, value_count } => {
                    let value_end = value_base
                        .checked_add(value_count)
                        .expect("normalize: sequence value interval overflow");
                    assert_eq!(
                        values.len(),
                        value_end,
                        "normalize: sequence value interval mismatch",
                    );
                    let mut sequence = Vec::with_capacity(value_count);
                    for value in values.drain(value_base..) {
                        sequence.push(
                            value.#take()
                                .expect("normalize: wrong category in sequence value"),
                        );
                    }
                    values.push(__MettailDovetailRebuildValue::#sequence(sequence));
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
            if let Some(arm) = generate_assemble_arm(category, v, &hol_pairs, &cancel_set, &cat_str)
            {
                assemble_arms.push(arm);
            }
        }
    }

    quote! {
        #(#visit_helper_fns)*
        #(#tagged_assemble_helper_fns)*
        #(#shared_assemble_helper_fns)*
        #(#tagged_beta_helper_fns)*

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
            results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
            values: &mut Vec<__MettailDovetailRebuildValue>,
            sources: &mut Vec<Box<AnyNormalizedTerm>>,
        ) {
            while let Some(task) = stack.pop() {
                match task {
                    #(#visit_arms)*
                    #(#tagged_assemble_arms)*
                    #(#shared_assemble_arms)*
                    #(#pack_sequence_arms)*
                    NormTask::MoveResultToShared { slot, repeat } => {
                        assert!(repeat > 0, "normalize: zero shared-value repeat");
                        let value = results[slot]
                            .take()
                            .expect("normalize: missing shared child result");
                        for _ in 1..repeat {
                            values.push(value.clone());
                        }
                        values.push(value);
                    }
                    NormTask::PushSharedValue(value) => values.push(value),
                    #(#tagged_beta_assemble_arms)*
                    #(#assemble_arms)*
                }
            }
        }
    }
}

/// Emit the per-category Visit helper function. Single `match src_ref { variants... }`
/// body; pushes new tasks onto the shared `stack`.
fn generate_visit_helper_fn(
    category: &SemanticCategoryLayout,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
) -> TokenStream {
    let cat = category.category();
    let helper_fn = format_ident!("norm_visit_{}", cat.to_string().to_lowercase());
    let cat_str = cat.to_string();
    let variant_arms: Vec<TokenStream> = category
        .variants()
        .iter()
        .map(|variant| {
            generate_visit_variant_arm(cat, variant, language, hol_pairs, cancel_set, &cat_str)
        })
        .collect();
    let wrap_self = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
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
            results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
            values: &mut Vec<__MettailDovetailRebuildValue>,
            sources: &mut Vec<Box<AnyNormalizedTerm>>,
            src: *const #cat,
            slot: usize,
        ) {
            let src_ref = unsafe { &*src };
            match src_ref {
                #(#variant_arms)*
                _ => {
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#wrap_self(src_ref.clone()),
                    );
                }
            }
        }
    }
}

/// Dispatch per-variant Visit handling.
fn generate_visit_variant_arm(
    cat: &Ident,
    variant: &SemanticVariantLayout,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> TokenStream {
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let constructor_tag = variant.constructor_tag();

    match variant.kind() {
        // ★ #141 G5 — a classification that refuses carries its diagnostic into
        // the emitted code, where `rustc` renders it. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => quote! { compile_error!(#message); },
        VariantKind::Var { label } => {
            quote! {
                #cat::#label(v) => {
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#wrap(#cat::#label(v.clone())),
                    );
                }
            }
        },
        // Stage 0 identity — MOVES in Stage 5 (normalize must recurse into
        // collection-literal elements).
        VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
            // Conservative: clone (works for both Copy and non-Copy).
            quote! {
                #cat::#label(v) => {
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#wrap(#cat::#label(v.clone())),
                    );
                }
            }
        },
        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            generate_recursive_native_visit_arm(cat, label, carrier)
        },
        VariantKind::Nullary { label } => {
            quote! {
                #cat::#label => {
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#wrap(#cat::#label),
                    );
                }
            }
        },
        VariantKind::Regular { label, fields } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return generate_beta_apply_visit_arm(cat, label, dom_str, constructor_tag);
                }
            }
            // HOL MApply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return generate_beta_mapply_visit_arm(cat, label, dom_str, constructor_tag);
                }
            }

            // Cancellation pair outer
            if let Some(pair) = cancel_set.get(&(cat_str.to_string(), label_str.clone())) {
                return generate_cancel_visit_arm(cat, label, pair);
            }

            if variant.all_fields_invertible() {
                generate_fused_regular_visit_arm(cat, label, variant)
            } else {
                generate_regular_visit_arm(cat, label, fields, constructor_tag, language)
            }
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            match variant.collection_projection() {
                Some(SemanticCollectionProjection::AcBag)
                | Some(SemanticCollectionProjection::OrderedSequence) => {
                    generate_fused_collection_visit_arm(cat, label, element_cat, coll_type, variant)
                },
                Some(SemanticCollectionProjection::Opaque) | None => generate_collection_visit_arm(
                    cat,
                    label,
                    element_cat,
                    coll_type,
                    constructor_tag,
                    language,
                ),
            }
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            if variant.all_fields_invertible() {
                generate_fused_binder_visit_arm(cat, label, variant)
            } else {
                generate_binder_visit_arm(
                    cat,
                    label,
                    pre_scope_fields,
                    body_cat,
                    constructor_tag,
                    language,
                )
            }
        },
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            if variant.all_fields_invertible() {
                generate_fused_binder_visit_arm(cat, label, variant)
            } else {
                generate_multi_binder_visit_arm(
                    cat,
                    label,
                    pre_scope_fields,
                    body_cat,
                    constructor_tag,
                    language,
                )
            }
        },
    }
}

fn generate_recursive_native_visit_arm(
    cat: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
) -> TokenStream {
    let assemble = format_ident!("AssembleNative_{}_{}", cat, label);
    let pathmap = carrier.pathmap_ref(&quote! { native });
    let focus = carrier.focus_ref(&quote! { native });
    let pushes = carrier.for_each_borrowed_subterm(
        &quote! { native },
        crate::gen::native_carrier::NativeCarrierWalkOrder::ReverseForLifo,
        &|child_category, child| {
            let visit = format_ident!("Visit{}", child_category);
            quote! {
                __native_next_slot -= 1;
                stack.push(NormTask::#visit {
                    src: #child as *const _,
                    slot: __native_next_slot,
                });
            }
        },
    );
    quote! {
        #cat::#label(native) => {
            let mode = (#pathmap).mode();
            let elements_count = match mode {
                mettail_runtime::PathMapMode::Empty => 0,
                mettail_runtime::PathMapMode::Set => (#pathmap).len(),
                mettail_runtime::PathMapMode::Map => (#pathmap).len().saturating_mul(2),
            };
            let elements_start = results.len();
            results.resize_with(elements_start + elements_count, || None);
            stack.push(NormTask::#assemble {
                slot,
                mode,
                elements_start,
                elements_count,
                focus: (*#focus).clone(),
            });
            let mut __native_next_slot = elements_start + elements_count;
            #pushes
            debug_assert_eq!(__native_next_slot, elements_start);
        }
    }
}

/// Allocate normalized-result slots for one exact field and emit the visit
/// work that fills them. Structural coefficients remain in the borrowed typed
/// source and are injected into the shared coproduct by the assembly frame.
/// Consequently one recursive child contributes one Visit task, not a Visit
/// followed by a separate move task.
fn emit_fused_field_visit_parts(
    layout: &SemanticFieldLayout,
    source: &Ident,
) -> (TokenStream, TokenStream) {
    let field_index = layout.index();
    let category = &layout.field().category;
    let visit = format_ident!("Visit{}", category);
    let slot = format_ident!("__fused_field_{}_slot", field_index);
    let start = format_ident!("__fused_field_{}_start", field_index);
    let count = format_ident!("__fused_field_{}_count", field_index);

    match layout.projection() {
        SemanticFieldProjection::Child => (
            quote! {
                let #slot = results.len();
                results.push(None);
            },
            quote! {
                stack.push(NormTask::#visit {
                    src: &**#source as *const _,
                    slot: #slot,
                });
            },
        ),
        SemanticFieldProjection::OptionalChild => (
            quote! {
                let #slot = results.len();
                if #source.is_some() {
                    results.push(None);
                }
            },
            quote! {
                if let Some(__fused_child) = #source.as_ref() {
                    stack.push(NormTask::#visit {
                        src: &**__fused_child as *const _,
                        slot: #slot,
                    });
                }
            },
        ),
        SemanticFieldProjection::OrderedSequence => (
            quote! {
                let #start = results.len();
                let #count = #source.len();
                results.resize_with(#start + #count, || None);
            },
            quote! {
                for (__fused_index, __fused_element) in #source.iter().enumerate().rev() {
                    stack.push(NormTask::#visit {
                        src: __fused_element as *const _,
                        slot: #start + __fused_index,
                    });
                }
            },
        ),
        SemanticFieldProjection::OptionalOrderedSequence => (
            quote! {
                let #start = results.len();
                let #count = #source.as_ref().map_or(0usize, Vec::len);
                results.resize_with(#start + #count, || None);
            },
            quote! {
                if let Some(__fused_sequence) = #source.as_ref() {
                    for (__fused_index, __fused_element) in
                        __fused_sequence.iter().enumerate().rev()
                    {
                        stack.push(NormTask::#visit {
                            src: __fused_element as *const _,
                            slot: #start + __fused_index,
                        });
                    }
                }
            },
        ),
        SemanticFieldProjection::Withheld
        | SemanticFieldProjection::TokenText
        | SemanticFieldProjection::OptionalTokenText => (TokenStream::new(), TokenStream::new()),
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => (
            quote! {
                compile_error!("mettail internal error: fused normalization admitted an opaque field");
            },
            TokenStream::new(),
        ),
    }
}

fn generate_fused_regular_visit_arm(
    cat: &Ident,
    label: &Ident,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let VariantKind::Regular { fields, .. } = variant.kind() else {
        return quote! {
            compile_error!("mettail internal error: fused regular producer received a non-regular layout");
        };
    };
    debug_assert_eq!(fields.len(), variant.fields().len());
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let parts: Vec<(TokenStream, TokenStream)> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .map(|(layout, source)| emit_fused_field_visit_parts(layout, source))
        .collect();
    let allocations = parts.iter().map(|(allocation, _)| allocation);
    let pushes = parts.iter().rev().map(|(_, push)| push);
    let assemble = format_ident!("AssembleTagged{}", cat);
    let constructor = variant.constructor_tag();

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let value_base = results.len();
            #(#allocations)*
            let value_count = results.len() - value_base;
            stack.push(NormTask::#assemble {
                src,
                constructor: #constructor,
                slot,
                value_base,
                value_count,
            });
            #(#pushes)*
        }
    }
}

fn generate_fused_collection_visit_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    _coll_type: &CollectionType,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let assemble = format_ident!("AssembleTagged{}", cat);
    let visit = format_ident!("Visit{}", element_cat);
    let constructor = variant.constructor_tag();
    match variant
        .collection_projection()
        .expect("fused collection producer requires a checked projection")
    {
        SemanticCollectionProjection::AcBag => quote! {
            #cat::#label(ref collection) => {
                let value_base = results.len();
                results.resize_with(value_base + collection.len(), || None);
                let value_count = collection.len();
                stack.push(NormTask::#assemble {
                    src,
                    constructor: #constructor,
                    slot,
                    value_base,
                    value_count,
                });
                for (__fused_index, (__fused_element, _)) in collection.iter().enumerate() {
                    stack.push(NormTask::#visit {
                        src: __fused_element as *const _,
                        slot: value_base + __fused_index,
                    });
                }
            }
        },
        SemanticCollectionProjection::OrderedSequence => quote! {
            #cat::#label(ref collection) => {
                let value_base = results.len();
                results.resize_with(value_base + collection.len(), || None);
                let value_count = collection.len();
                stack.push(NormTask::#assemble {
                    src,
                    constructor: #constructor,
                    slot,
                    value_base,
                    value_count,
                });
                for (__fused_index, __fused_element) in collection.iter().enumerate().rev() {
                    stack.push(NormTask::#visit {
                        src: __fused_element as *const _,
                        slot: value_base + __fused_index,
                    });
                }
            }
        },
        SemanticCollectionProjection::Opaque => quote! {
            compile_error!("mettail internal error: opaque collection reached fused normalization assembly");
        },
    }
}

fn generate_fused_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let (pre_scope_fields, body_cat) = match variant.kind() {
        VariantKind::Binder { pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { pre_scope_fields, body_cat, .. } => {
            (pre_scope_fields, body_cat)
        },
        _ => {
            return quote! {
                compile_error!("mettail internal error: fused binder producer received a non-binder layout");
            };
        },
    };
    debug_assert_eq!(pre_scope_fields.len(), variant.fields().len());
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope = &field_names[total_fields - 1];
    let parts: Vec<(TokenStream, TokenStream)> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .map(|(layout, source)| emit_fused_field_visit_parts(layout, source))
        .collect();
    let allocations = parts.iter().map(|(allocation, _)| allocation);
    let pushes = parts.iter().rev().map(|(_, push)| push);
    let assemble = format_ident!("AssembleTagged{}", cat);
    let body_visit = format_ident!("Visit{}", body_cat);
    let constructor = variant.constructor_tag();

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let value_base = results.len();
            #(#allocations)*
            let body_slot = results.len();
            results.push(None);
            let value_count = results.len() - value_base;
            stack.push(NormTask::#assemble {
                src,
                constructor: #constructor,
                slot,
                value_base,
                value_count,
            });
            stack.push(NormTask::#body_visit {
                src: &*#scope.inner().unsafe_body as *const _,
                slot: body_slot,
            });
            #(#pushes)*
        }
    }
}

/// Schedule one exact invertible field as a producer for the shared typed
/// assembly stack.  Each logical field publishes exactly one coproduct value;
/// ordered sequences normalize their children first and are then packed into
/// one typed sequence value.  Optional absence remains an indexed structural
/// value, never an omitted slot.
fn emit_shared_field_schedule(layout: &SemanticFieldLayout, source: &Ident) -> TokenStream {
    let field_index = layout.index();
    let absent_index = field_index as u32;
    let category = &layout.field().category;
    let visit = format_ident!("Visit{}", category);
    let slot = format_ident!("__shared_field_{}_slot", field_index);
    let sequence_base = quote! {
        value_base
            .checked_add(#field_index)
            .expect("normalize: shared field base overflow")
    };

    match layout.projection() {
        SemanticFieldProjection::Child => quote! {
            let #slot = results.len();
            results.push(None);
            stack.push(NormTask::MoveResultToShared { slot: #slot, repeat: 1usize });
            stack.push(NormTask::#visit {
                src: &**#source as *const _,
                slot: #slot,
            });
        },
        SemanticFieldProjection::OptionalChild => quote! {
            if let Some(__shared_child) = #source.as_ref() {
                let #slot = results.len();
                results.push(None);
                stack.push(NormTask::MoveResultToShared { slot: #slot, repeat: 1usize });
                stack.push(NormTask::#visit {
                    src: &**__shared_child as *const _,
                    slot: #slot,
                });
            } else {
                stack.push(NormTask::PushSharedValue(
                    __MettailDovetailRebuildValue::FieldAbsent(#absent_index),
                ));
            }
        },
        SemanticFieldProjection::Withheld => {
            let value =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_withheld_value_variant(
                    category,
                );
            quote! {
                stack.push(NormTask::PushSharedValue(
                    __MettailDovetailRebuildValue::#value((*#source).clone()),
                ));
            }
        },
        SemanticFieldProjection::TokenText => quote! {
            stack.push(NormTask::PushSharedValue(
                __MettailDovetailRebuildValue::TokenText((*#source).clone()),
            ));
        },
        SemanticFieldProjection::OptionalTokenText => quote! {
            if let Some(__shared_text) = #source.as_ref() {
                stack.push(NormTask::PushSharedValue(
                    __MettailDovetailRebuildValue::TokenText(__shared_text.clone()),
                ));
            } else {
                stack.push(NormTask::PushSharedValue(
                    __MettailDovetailRebuildValue::FieldAbsent(#absent_index),
                ));
            }
        },
        SemanticFieldProjection::OrderedSequence => {
            let pack = format_ident!("PackSharedSequence{}", category);
            quote! {
                let __shared_sequence_base = #sequence_base;
                stack.push(NormTask::#pack {
                    value_base: __shared_sequence_base,
                    value_count: #source.len(),
                });
                for __shared_element in #source.iter().rev() {
                    let __shared_element_slot = results.len();
                    results.push(None);
                    stack.push(NormTask::MoveResultToShared {
                        slot: __shared_element_slot,
                        repeat: 1usize,
                    });
                    stack.push(NormTask::#visit {
                        src: __shared_element as *const _,
                        slot: __shared_element_slot,
                    });
                }
            }
        },
        SemanticFieldProjection::OptionalOrderedSequence => {
            let pack = format_ident!("PackSharedSequence{}", category);
            quote! {
                if let Some(__shared_sequence) = #source.as_ref() {
                    let __shared_sequence_base = #sequence_base;
                    stack.push(NormTask::#pack {
                        value_base: __shared_sequence_base,
                        value_count: __shared_sequence.len(),
                    });
                    for __shared_element in __shared_sequence.iter().rev() {
                        let __shared_element_slot = results.len();
                        results.push(None);
                        stack.push(NormTask::MoveResultToShared {
                            slot: __shared_element_slot,
                            repeat: 1usize,
                        });
                        stack.push(NormTask::#visit {
                            src: __shared_element as *const _,
                            slot: __shared_element_slot,
                        });
                    }
                } else {
                    stack.push(NormTask::PushSharedValue(
                        __MettailDovetailRebuildValue::FieldAbsent(#absent_index),
                    ));
                }
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
            let message = format!(
                "mettail internal error: normalization scheduled non-invertible field `{category}`",
            );
            quote! { compile_error!(#message); }
        },
    }
}

fn generate_shared_regular_visit_arm(
    cat: &Ident,
    label: &Ident,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let VariantKind::Regular { fields, .. } = variant.kind() else {
        return quote! {
            compile_error!("mettail internal error: shared regular producer received a non-regular layout");
        };
    };
    debug_assert_eq!(fields.len(), variant.fields().len());
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let schedules: Vec<TokenStream> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .rev()
        .map(|(layout, source)| emit_shared_field_schedule(layout, source))
        .collect();
    let assemble = format_ident!("AssembleShared{}", cat);
    let constructor = variant.constructor_tag();
    let value_count = fields.len();

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let value_base = values.len();
            stack.push(NormTask::#assemble {
                constructor: #constructor,
                slot,
                value_base,
                value_count: #value_count,
            });
            #(#schedules)*
        }
    }
}

fn generate_shared_collection_visit_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    _coll_type: &CollectionType,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let assemble = format_ident!("AssembleShared{}", cat);
    let visit = format_ident!("Visit{}", element_cat);
    let constructor = variant.constructor_tag();
    match variant
        .collection_projection()
        .expect("shared collection producer requires a checked projection")
    {
        SemanticCollectionProjection::AcBag => quote! {
            #cat::#label(ref collection) => {
                let value_base = values.len();
                let value_count = collection.iter().try_fold(0usize, |total, (_, count)| {
                    total.checked_add(count)
                }).expect("normalize: associative collection multiplicity overflow");
                stack.push(NormTask::#assemble {
                    constructor: #constructor,
                    slot,
                    value_base,
                    value_count,
                });
                for (element, count) in collection.iter() {
                    assert!(count > 0, "normalize: zero associative multiplicity");
                    let element_slot = results.len();
                    results.push(None);
                    stack.push(NormTask::MoveResultToShared {
                        slot: element_slot,
                        repeat: count,
                    });
                    stack.push(NormTask::#visit {
                        src: element as *const _,
                        slot: element_slot,
                    });
                }
            }
        },
        SemanticCollectionProjection::OrderedSequence => {
            let pack = format_ident!("PackSharedSequence{}", element_cat);
            quote! {
                #cat::#label(ref collection) => {
                    let value_base = values.len();
                    stack.push(NormTask::#assemble {
                        constructor: #constructor,
                        slot,
                        value_base,
                        value_count: 1usize,
                    });
                    stack.push(NormTask::#pack {
                        value_base,
                        value_count: collection.len(),
                    });
                    for element in collection.iter().rev() {
                        let element_slot = results.len();
                        results.push(None);
                        stack.push(NormTask::MoveResultToShared {
                            slot: element_slot,
                            repeat: 1usize,
                        });
                        stack.push(NormTask::#visit {
                            src: element as *const _,
                            slot: element_slot,
                        });
                    }
                }
            }
        },
        SemanticCollectionProjection::Opaque => {
            quote! {
                compile_error!("mettail internal error: opaque collection reached shared normalization assembly");
            }
        },
    }
}

fn generate_shared_binder_visit_arm(
    cat: &Ident,
    label: &Ident,
    variant: &SemanticVariantLayout,
    multi: bool,
) -> TokenStream {
    let (pre_scope_fields, body_cat) = match variant.kind() {
        VariantKind::Binder { pre_scope_fields, body_cat, .. }
        | VariantKind::MultiBinder { pre_scope_fields, body_cat, .. } => {
            (pre_scope_fields, body_cat)
        },
        _ => {
            return quote! {
                compile_error!("mettail internal error: shared binder producer received a non-binder layout");
            };
        },
    };
    debug_assert_eq!(pre_scope_fields.len(), variant.fields().len());
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope = &field_names[total_fields - 1];
    let schedules: Vec<TokenStream> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .rev()
        .map(|(layout, source)| emit_shared_field_schedule(layout, source))
        .collect();
    let assemble = format_ident!("AssembleShared{}", cat);
    let body_visit = format_ident!("Visit{}", body_cat);
    let constructor = variant.constructor_tag();
    let value_count = pre_scope_fields.len() + 2;
    let binder_value = if multi {
        quote! {
            __MettailDovetailRebuildValue::MultiBinders(
                #scope.inner().unsafe_pattern.clone(),
            )
        }
    } else {
        quote! {
            __MettailDovetailRebuildValue::SingleBinder(
                #scope.inner().unsafe_pattern.clone(),
            )
        }
    };

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let value_base = values.len();
            let body_slot = results.len();
            results.push(None);
            stack.push(NormTask::#assemble {
                constructor: #constructor,
                slot,
                value_base,
                value_count: #value_count,
            });
            #(#schedules)*
            stack.push(NormTask::PushSharedValue(#binder_value));
            stack.push(NormTask::MoveResultToShared {
                slot: body_slot,
                repeat: 1usize,
            });
            stack.push(NormTask::#body_visit {
                src: &*#scope.inner().unsafe_body as *const _,
                slot: body_slot,
            });
        }
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
    constructor_tag: u32,
    language: &LanguageDef,
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let assemble_variant = format_ident!("AssembleTagged{}", cat);

    let (alloc_stmts, push_stmts, _assemble_fields) =
        emit_reg_field_visit_alloc(cat, fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let value_base = results.len();
            #(#alloc_stmts)*
            let value_count = results.len() - value_base;
            stack.push(NormTask::#assemble_variant {
                src,
                constructor: #constructor_tag,
                slot,
                value_base,
                value_count,
            });
            #(#push_stmts)*
        }
    }
}

/// Emit alloc/push/assemble-fields for a Regular variant's fields.
fn emit_reg_field_visit_alloc(
    _cat: &Ident,
    fields: &[FieldInfo],
    field_names: &[Ident],
    language: &LanguageDef,
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_fields: Vec<TokenStream> = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let name = &field_names[i];

        if field.is_semantic_boundary(language) {
            let carrier = format_ident!("f{}_data", i);
            alloc_stmts.push(quote! {
                let #carrier = #name.clone();
            });
            assemble_fields.push(quote! { #carrier });
            continue;
        }

        if field.is_opaque_leaf() {
            // L9-3: clone the token-text `String` into the Assemble carrier;
            // no Visit/descent (mirrors the predicate leaf below).
            let text_name = format_ident!("f{}_text", i);
            alloc_stmts.push(quote! {
                let #text_name = #name.clone();
            });
            assemble_fields.push(quote! { #text_name });
            continue;
        }

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
        CollectionType::HashMap | CollectionType::PathMap => {
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
    constructor_tag: u32,
    _language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleTagged{}", cat);
    let visit_task = format_ident!("Visit{}", element_cat);

    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
            quote! {
                #cat::#label(ref coll) => {
                    let value_base = results.len();
                    for (_elem, count) in coll.iter() {
                        results.push(None);
                    }
                    let value_count = results.len() - value_base;
                    stack.push(NormTask::#assemble_variant {
                        src,
                        constructor: #constructor_tag,
                        slot,
                        value_base,
                        value_count,
                    });
                    for (elem_idx, (elem, _count)) in coll.iter().enumerate() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: value_base + elem_idx,
                        });
                    }
                }
            }
        },
        CollectionType::Vec => {
            quote! {
                #cat::#label(ref coll) => {
                    let value_base = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let value_count = coll.len();
                    stack.push(NormTask::#assemble_variant {
                        src,
                        constructor: #constructor_tag,
                        slot,
                        value_base,
                        value_count,
                    });
                    for (idx, elem) in coll.iter().enumerate().rev() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: value_base + idx,
                        });
                    }
                }
            }
        },
        CollectionType::HashSet => {
            quote! {
                #cat::#label(ref coll) => {
                    let value_base = results.len();
                    for _ in 0..coll.len() {
                        results.push(None);
                    }
                    let value_count = coll.len();
                    stack.push(NormTask::#assemble_variant {
                        src,
                        constructor: #constructor_tag,
                        slot,
                        value_base,
                        value_count,
                    });
                    for (elem_idx, elem) in coll.iter().enumerate() {
                        stack.push(NormTask::#visit_task {
                            src: elem as *const _,
                            slot: value_base + elem_idx,
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
    constructor_tag: u32,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleTagged{}", cat);
    let body_visit = format_ident!("Visit{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, _assemble_pre) =
        emit_pre_field_visit_alloc(cat, pre_scope_fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let body = &#scope_name.inner().unsafe_body;

            let value_base = results.len();
            #(#alloc_pre)*

            let body_slot = results.len();
            results.push(None);
            let value_count = results.len() - value_base;

            stack.push(NormTask::#assemble_variant {
                src,
                constructor: #constructor_tag,
                slot,
                value_base,
                value_count,
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
    constructor_tag: u32,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleTagged{}", cat);
    let body_visit = format_ident!("Visit{}", body_cat);

    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope_name = &field_names[total_fields - 1];

    let (alloc_pre, push_pre, _assemble_pre) =
        emit_pre_field_visit_alloc(cat, pre_scope_fields, &field_names, language);

    quote! {
        #cat::#label(#(ref #field_names),*) => {
            let body = &#scope_name.inner().unsafe_body;

            let value_base = results.len();
            #(#alloc_pre)*

            let body_slot = results.len();
            results.push(None);
            let value_count = results.len() - value_base;

            stack.push(NormTask::#assemble_variant {
                src,
                constructor: #constructor_tag,
                slot,
                value_base,
                value_count,
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
    language: &LanguageDef,
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let mut alloc_stmts: Vec<TokenStream> = Vec::new();
    let mut push_stmts: Vec<TokenStream> = Vec::new();
    let mut assemble_refs: Vec<TokenStream> = Vec::new();

    for (i, field) in pre_scope_fields.iter().enumerate() {
        let name = &field_names[i];

        if field.is_semantic_boundary(language) {
            let carrier = format_ident!("pf{}_data", i);
            alloc_stmts.push(quote! {
                let #carrier = #name.clone();
            });
            assemble_refs.push(quote! { #carrier });
            continue;
        }

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
                CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
fn generate_beta_apply_visit_arm(
    cat: &Ident,
    label: &Ident,
    dom_str: &str,
    constructor_tag: u32,
) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaApply{}", cat);
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

            stack.push(NormTask::#assemble_variant {
                constructor: #constructor_tag,
                slot,
                lam_slot,
                arg_slot,
            });
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
fn generate_beta_mapply_visit_arm(
    cat: &Ident,
    label: &Ident,
    dom_str: &str,
    constructor_tag: u32,
) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaMApply{}", cat);
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
                constructor: #constructor_tag,
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

/// Consume one exact producer suffix through the common typed assembly
/// kernel, then project the resulting category value back into normalization's
/// random-access result buffer.  Dovetail and normalization therefore share
/// the constructor bodies and all exact typed eliminators.
fn generate_shared_assemble_helper_fn(
    category: &SemanticCategoryLayout,
    is_native: bool,
) -> TokenStream {
    let cat = category.category();
    let helper = format_ident!("norm_assemble_shared_{}", cat.to_string().to_lowercase());
    let construct =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_construct_fn_name(cat);
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let finish = if is_native {
        quote! {
            let normalized = reconstructed
                .try_fold_to_literal()
                .unwrap_or(reconstructed);
            results[slot] = Some(__MettailDovetailRebuildValue::#wrap(normalized));
        }
    } else {
        quote! {
            results[slot] = Some(__MettailDovetailRebuildValue::#wrap(reconstructed));
        }
    };

    quote! {
        #[inline(never)]
        #[allow(dead_code, unused_variables, non_snake_case)]
        fn #helper(
            results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
            values: &mut Vec<__MettailDovetailRebuildValue>,
            constructor: u32,
            slot: usize,
            value_base: usize,
            value_count: usize,
        ) {
            let reconstructed = #construct(
                constructor,
                value_base,
                value_count,
                values,
            )
            .expect("normalize: shared typed assembly rejected producer values");
            assert_eq!(
                values.len(),
                value_base,
                "normalize: shared assembly leaked values into its caller",
            );
            #finish
        }
    }
}

/// Emit one typed ordinary-constructor assembler for a semantic category.
///
/// The work-stack frame contains no constructor-specific Rust payload.  It
/// carries the already-borrowed typed source, the dense constructor tag from
/// `SemanticAdapterLayout`, and the exact interval of normalized recursive
/// values.  Each arm re-derives only the field partition from the typed source
/// and refuses a tag/source or interval mismatch before publishing a result.
fn generate_tagged_assemble_helper_fn(
    category: &SemanticCategoryLayout,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    is_native: bool,
) -> TokenStream {
    let cat = category.category();
    let helper = format_ident!("norm_assemble_{}", cat.to_string().to_lowercase());
    let cat_str = cat.to_string();
    let arms: Vec<TokenStream> = category
        .variants()
        .iter()
        .filter_map(|variant| {
            generate_tagged_assemble_case(
                cat, variant, language, hol_pairs, cancel_set, &cat_str, is_native,
            )
        })
        .collect();

    quote! {
        #[inline(never)]
        #[allow(
            dead_code,
            unused_variables,
            unreachable_patterns,
            clippy::needless_range_loop,
            non_snake_case
        )]
        fn #helper(
            results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
            values: &mut Vec<__MettailDovetailRebuildValue>,
            src: *const #cat,
            constructor: u32,
            slot: usize,
            value_base: usize,
            value_count: usize,
        ) {
            let value_end = value_base
                .checked_add(value_count)
                .expect("normalize: tagged value interval overflow");
            assert!(
                value_end <= results.len(),
                "normalize: tagged value interval outside result buffer",
            );
            // SAFETY: `AssembleTagged<Cat>` carries the same pointer placed in
            // the worklist by `Visit<Cat>`.  The normalize driver documents the
            // borrowed-input and pooled-owned-source lifetime invariant.
            let src_ref = unsafe { &*src };
            match (constructor, src_ref) {
                #(#arms)*
                _ => panic!("normalize: constructor tag/source mismatch"),
            }
        }
    }
}

fn generate_tagged_assemble_case(
    cat: &Ident,
    variant: &SemanticVariantLayout,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
    is_native: bool,
) -> Option<TokenStream> {
    match variant.kind() {
        VariantKind::Regular { .. } => {
            if variant.all_fields_invertible() {
                generate_fused_regular_assemble_case(cat, variant, hol_pairs, cancel_set, cat_str)
            } else {
                generate_tagged_regular_assemble_case(
                    cat, variant, language, hol_pairs, cancel_set, cat_str, is_native,
                )
            }
        },
        VariantKind::Collection { label, element_cat, coll_type } => {
            match variant.collection_projection() {
                Some(SemanticCollectionProjection::Opaque) | None => {
                    Some(generate_tagged_collection_assemble_case(
                        cat,
                        variant.constructor_tag(),
                        label,
                        element_cat,
                        coll_type,
                    ))
                },
                Some(SemanticCollectionProjection::AcBag)
                | Some(SemanticCollectionProjection::OrderedSequence) => {
                    Some(generate_fused_collection_assemble_case(cat, variant))
                },
            }
        },
        VariantKind::Binder { label, pre_scope_fields, body_cat, .. } => {
            if variant.all_fields_invertible() {
                Some(generate_fused_binder_assemble_case(cat, variant, false))
            } else {
                Some(generate_tagged_binder_assemble_case(
                    cat,
                    variant.constructor_tag(),
                    label,
                    pre_scope_fields,
                    body_cat,
                    language,
                    false,
                ))
            }
        },
        VariantKind::MultiBinder { label, pre_scope_fields, body_cat, .. } => {
            if variant.all_fields_invertible() {
                Some(generate_fused_binder_assemble_case(cat, variant, true))
            } else {
                Some(generate_tagged_binder_assemble_case(
                    cat,
                    variant.constructor_tag(),
                    label,
                    pre_scope_fields,
                    body_cat,
                    language,
                    true,
                ))
            }
        },
        _ => None,
    }
}

/// Materialize one checked field from completed normalization result slots into
/// the shared typed coproduct. This is the proved producer fusion: structural
/// coefficients are injected here and recursive results are moved exactly
/// once, immediately before the common constructor kernel runs.
fn emit_fused_field_materialization(layout: &SemanticFieldLayout, source: &Ident) -> TokenStream {
    let field_index = layout.index();
    let absent_index = field_index as u32;
    let category = &layout.field().category;
    match layout.projection() {
        SemanticFieldProjection::Child => quote! {
            values.push(
                results[__result_cursor]
                    .take()
                    .expect("normalize: fused child result missing"),
            );
            __result_cursor = __result_cursor
                .checked_add(1usize)
                .expect("normalize: fused child cursor overflow");
        },
        SemanticFieldProjection::OptionalChild => quote! {
            if #source.is_some() {
                values.push(
                    results[__result_cursor]
                        .take()
                        .expect("normalize: fused optional child result missing"),
                );
                __result_cursor = __result_cursor
                    .checked_add(1usize)
                    .expect("normalize: fused optional child cursor overflow");
            } else {
                values.push(__MettailDovetailRebuildValue::FieldAbsent(#absent_index));
            }
        },
        SemanticFieldProjection::Withheld => {
            let value =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_withheld_value_variant(
                    category,
                );
            quote! {
                values.push(__MettailDovetailRebuildValue::#value((*#source).clone()));
            }
        },
        SemanticFieldProjection::TokenText => quote! {
            values.push(__MettailDovetailRebuildValue::TokenText((*#source).clone()));
        },
        SemanticFieldProjection::OptionalTokenText => quote! {
            if let Some(__fused_text) = #source.as_ref() {
                values.push(__MettailDovetailRebuildValue::TokenText(__fused_text.clone()));
            } else {
                values.push(__MettailDovetailRebuildValue::FieldAbsent(#absent_index));
            }
        },
        SemanticFieldProjection::OrderedSequence => {
            let take_sequence = any_norm_take_sequence_function(category);
            let sequence =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_seq_value_variant(
                    category,
                );
            quote! {
                let __fused_length = #source.len();
                let __fused_sequence = #take_sequence(
                    results,
                    __result_cursor,
                    __fused_length,
                );
                __result_cursor = __result_cursor
                    .checked_add(__fused_length)
                    .expect("normalize: fused sequence cursor overflow");
                values.push(__MettailDovetailRebuildValue::#sequence(__fused_sequence));
            }
        },
        SemanticFieldProjection::OptionalOrderedSequence => {
            let take_sequence = any_norm_take_sequence_function(category);
            let sequence =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_seq_value_variant(
                    category,
                );
            quote! {
                if let Some(__fused_source_sequence) = #source.as_ref() {
                    let __fused_length = __fused_source_sequence.len();
                    let __fused_sequence = #take_sequence(
                        results,
                        __result_cursor,
                        __fused_length,
                    );
                    __result_cursor = __result_cursor
                        .checked_add(__fused_length)
                        .expect("normalize: fused optional sequence cursor overflow");
                    values.push(__MettailDovetailRebuildValue::#sequence(__fused_sequence));
                } else {
                    values.push(__MettailDovetailRebuildValue::FieldAbsent(#absent_index));
                }
            }
        },
        SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => quote! {
            compile_error!("mettail internal error: fused normalization materialized an opaque field");
        },
    }
}

fn generate_fused_regular_assemble_case(
    cat: &Ident,
    variant: &SemanticVariantLayout,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> Option<TokenStream> {
    let VariantKind::Regular { label, fields } = variant.kind() else {
        return None;
    };
    let label_str = label.to_string();
    if strip_prefix(&label_str, "Apply")
        .is_some_and(|domain| hol_pairs.contains(&(cat_str.to_string(), domain.to_string())))
        || strip_prefix(&label_str, "MApply")
            .is_some_and(|domain| hol_pairs.contains(&(cat_str.to_string(), domain.to_string())))
        || cancel_set.contains_key(&(cat_str.to_string(), label_str))
    {
        return None;
    }
    debug_assert_eq!(fields.len(), variant.fields().len());
    let constructor = variant.constructor_tag();
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let materialize: Vec<TokenStream> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .map(|(layout, source)| emit_fused_field_materialization(layout, source))
        .collect();
    let shared_count = fields.len();
    let assemble_shared = format_ident!("norm_assemble_shared_{}", cat.to_string().to_lowercase());

    Some(quote! {
        (#constructor, #cat::#label(#(ref #field_names),*)) => {
            let __shared_value_base = values.len();
            let mut __result_cursor = value_base;
            #(#materialize)*
            assert_eq!(
                __result_cursor,
                value_end,
                "normalize: fused regular result-count mismatch",
            );
            #assemble_shared(
                results,
                values,
                #constructor,
                slot,
                __shared_value_base,
                #shared_count,
            );
        },
    })
}

fn generate_fused_collection_assemble_case(
    cat: &Ident,
    variant: &SemanticVariantLayout,
) -> TokenStream {
    let VariantKind::Collection { label, element_cat, .. } = variant.kind() else {
        return quote! {
            compile_error!("mettail internal error: fused collection assembler received a non-collection layout");
        };
    };
    let constructor = variant.constructor_tag();
    let assemble_shared = format_ident!("norm_assemble_shared_{}", cat.to_string().to_lowercase());
    match variant
        .collection_projection()
        .expect("fused collection assembler requires a checked projection")
    {
        SemanticCollectionProjection::AcBag => quote! {
            (#constructor, #cat::#label(ref collection)) => {
                let __shared_value_base = values.len();
                let mut __result_cursor = value_base;
                let mut __shared_value_count = 0usize;
                for (_, __multiplicity) in collection.iter() {
                    assert!(__multiplicity > 0, "normalize: zero fused bag multiplicity");
                    let __value = results[__result_cursor]
                        .take()
                        .expect("normalize: fused bag element missing");
                    __result_cursor = __result_cursor
                        .checked_add(1usize)
                        .expect("normalize: fused bag cursor overflow");
                    __shared_value_count = __shared_value_count
                        .checked_add(__multiplicity)
                        .expect("normalize: fused bag multiplicity overflow");
                    for _ in 1..__multiplicity {
                        values.push(__value.clone());
                    }
                    values.push(__value);
                }
                assert_eq!(
                    __result_cursor,
                    value_end,
                    "normalize: fused bag result-count mismatch",
                );
                #assemble_shared(
                    results,
                    values,
                    #constructor,
                    slot,
                    __shared_value_base,
                    __shared_value_count,
                );
            },
        },
        SemanticCollectionProjection::OrderedSequence => {
            let take_sequence = any_norm_take_sequence_function(element_cat);
            let sequence =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_seq_value_variant(
                    element_cat,
                );
            quote! {
                (#constructor, #cat::#label(ref collection)) => {
                    let __shared_value_base = values.len();
                    let __sequence = #take_sequence(results, value_base, value_count);
                    assert_eq!(
                        value_count,
                        collection.len(),
                        "normalize: fused ordered collection result-count mismatch",
                    );
                    values.push(__MettailDovetailRebuildValue::#sequence(__sequence));
                    #assemble_shared(
                        results,
                        values,
                        #constructor,
                        slot,
                        __shared_value_base,
                        1usize,
                    );
                },
            }
        },
        SemanticCollectionProjection::Opaque => quote! {
            compile_error!("mettail internal error: opaque collection reached fused normalization assembly");
        },
    }
}

fn generate_fused_binder_assemble_case(
    cat: &Ident,
    variant: &SemanticVariantLayout,
    multi: bool,
) -> TokenStream {
    let (label, pre_scope_fields) = match variant.kind() {
        VariantKind::Binder { label, pre_scope_fields, .. }
        | VariantKind::MultiBinder { label, pre_scope_fields, .. } => (label, pre_scope_fields),
        _ => {
            return quote! {
                compile_error!("mettail internal error: fused binder assembler received a non-binder layout");
            };
        },
    };
    debug_assert_eq!(pre_scope_fields.len(), variant.fields().len());
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope = &field_names[total_fields - 1];
    let materialize: Vec<TokenStream> = variant
        .fields()
        .iter()
        .zip(&field_names)
        .map(|(layout, source)| emit_fused_field_materialization(layout, source))
        .collect();
    let binder = if multi {
        quote! {
            __MettailDovetailRebuildValue::MultiBinders(
                #scope.inner().unsafe_pattern.clone(),
            )
        }
    } else {
        quote! {
            __MettailDovetailRebuildValue::SingleBinder(
                #scope.inner().unsafe_pattern.clone(),
            )
        }
    };
    let constructor = variant.constructor_tag();
    let shared_count = pre_scope_fields.len() + 2;
    let assemble_shared = format_ident!("norm_assemble_shared_{}", cat.to_string().to_lowercase());

    quote! {
        (#constructor, #cat::#label(#(ref #field_names),*)) => {
            let __shared_value_base = values.len();
            let mut __result_cursor = value_base;
            #(#materialize)*
            values.push(
                results[__result_cursor]
                    .take()
                    .expect("normalize: fused binder body missing"),
            );
            __result_cursor = __result_cursor
                .checked_add(1usize)
                .expect("normalize: fused binder body cursor overflow");
            values.push(#binder);
            assert_eq!(
                __result_cursor,
                value_end,
                "normalize: fused binder result-count mismatch",
            );
            #assemble_shared(
                results,
                values,
                #constructor,
                slot,
                __shared_value_base,
                #shared_count,
            );
        },
    }
}

fn generate_tagged_regular_assemble_case(
    cat: &Ident,
    variant: &SemanticVariantLayout,
    language: &LanguageDef,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
    is_native: bool,
) -> Option<TokenStream> {
    let VariantKind::Regular { label, fields } = variant.kind() else {
        return None;
    };
    let label_str = label.to_string();
    if strip_prefix(&label_str, "Apply")
        .is_some_and(|domain| hol_pairs.contains(&(cat_str.to_string(), domain.to_string())))
        || strip_prefix(&label_str, "MApply")
            .is_some_and(|domain| hol_pairs.contains(&(cat_str.to_string(), domain.to_string())))
        || cancel_set.contains_key(&(cat_str.to_string(), label_str))
    {
        return None;
    }

    let constructor_tag = variant.constructor_tag();
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let frame_bindings = emit_tagged_regular_frame_bindings(fields, &field_names, language);
    let field_extracts: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_reg_field_extract(i, field, language))
        .collect();
    let construct_fields: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_reg_field_construct(i, field, language))
        .collect();
    let finalize = if is_native {
        quote! {
            let folded = reconstructed.try_fold_to_literal().unwrap_or(reconstructed);
            results[slot] = Some(__MettailDovetailRebuildValue::#wrap(folded));
        }
    } else {
        quote! {
            results[slot] = Some(__MettailDovetailRebuildValue::#wrap(reconstructed));
        }
    };

    Some(quote! {
        (#constructor_tag, #cat::#label(#(ref #field_names),*)) => {
            let mut __value_cursor = value_base;
            #(#frame_bindings)*
            assert_eq!(
                __value_cursor,
                value_end,
                "normalize: tagged constructor value-count mismatch",
            );
            #(#field_extracts)*
            let reconstructed = #cat::#label(#(#construct_fields),*);
            #finalize
        },
    })
}

/// Bind the legacy field-extraction names to a contiguous tagged value range.
/// Nonrecursive coefficients are cloned from the typed source instead of
/// riding in a constructor-specific task payload.
fn emit_tagged_regular_frame_bindings(
    fields: &[FieldInfo],
    field_names: &[Ident],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let source = &field_names[i];
            if field.is_semantic_boundary(language) {
                let carrier = format_ident!("f{}_data", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_opaque_leaf() {
                let carrier = format_ident!("f{}_text", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_predicate {
                let carrier = format_ident!("f{}_pred", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_optional {
                if field.is_collection {
                    let carrier = format_ident!("f{}_cloned", i);
                    return quote! { let #carrier = (*#source).clone(); };
                }
                let slot = format_ident!("f{}_slot", i);
                let present = format_ident!("f{}_some", i);
                return quote! {
                    let #slot = __value_cursor;
                    let #present = #source.is_some();
                    if #present {
                        __value_cursor = __value_cursor
                            .checked_add(1)
                            .expect("normalize: optional field interval overflow");
                    }
                };
            }
            if field.is_collection {
                let start = format_ident!("f{}_start", i);
                let count = format_ident!("f{}_count", i);
                return match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag => {
                        let counts = format_ident!("f{}_counts", i);
                        quote! {
                            let #start = __value_cursor;
                            let #counts: Vec<usize> =
                                #source.iter().map(|(_element, count)| count).collect();
                            let #count = #counts.len();
                            __value_cursor = __value_cursor
                                .checked_add(#count)
                                .expect("normalize: bag field interval overflow");
                        }
                    },
                    CollectionType::HashMap | CollectionType::PathMap => quote! {
                        let #start = __value_cursor;
                        let #count = #source.len();
                        let __field_slots = #count
                            .checked_mul(2)
                            .expect("normalize: map field interval overflow");
                        __value_cursor = __value_cursor
                            .checked_add(__field_slots)
                            .expect("normalize: map field interval overflow");
                    },
                    CollectionType::Vec | CollectionType::HashSet => quote! {
                        let #start = __value_cursor;
                        let #count = #source.len();
                        __value_cursor = __value_cursor
                            .checked_add(#count)
                            .expect("normalize: collection field interval overflow");
                    },
                };
            }

            let slot = format_ident!("f{}_slot", i);
            quote! {
                let #slot = __value_cursor;
                __value_cursor = __value_cursor
                    .checked_add(1)
                    .expect("normalize: scalar field interval overflow");
            }
        })
        .collect()
}

fn generate_tagged_collection_assemble_case(
    cat: &Ident,
    constructor_tag: u32,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let take_element =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(element_cat);
    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
            let helper_name = format_ident!("insert_into_{}", label.to_string().to_lowercase());
            quote! {
                (#constructor_tag, #cat::#label(ref coll)) => {
                    let counts: Vec<usize> =
                        coll.iter().map(|(_element, count)| count).collect();
                    let elements_count = counts.len();
                    assert_eq!(
                        value_base.checked_add(elements_count),
                        Some(value_end),
                        "normalize: tagged bag value-count mismatch",
                    );
                    let mut new_bag = mettail_runtime::HashBag::new();
                    for (idx, count) in counts.iter().enumerate() {
                        let value = results[value_base + idx]
                            .take()
                            .expect("normalize: missing hashbag element")
                            .#take_element()
                            .expect("normalize: wrong category in hashbag slot");
                        for _ in 0..*count {
                            #cat::#helper_name(&mut new_bag, value.clone());
                        }
                    }
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#wrap(#cat::#label(new_bag)),
                    );
                },
            }
        },
        CollectionType::Vec => quote! {
            (#constructor_tag, #cat::#label(ref coll)) => {
                let elements_count = coll.len();
                assert_eq!(
                    value_base.checked_add(elements_count),
                    Some(value_end),
                    "normalize: tagged sequence value-count mismatch",
                );
                let mut normalized = Vec::with_capacity(elements_count);
                for index in 0..elements_count {
                    let value = results[value_base + index].take()
                        .expect("normalize: missing vec element")
                        .#take_element()
                        .expect("normalize: wrong category in vec slot");
                    normalized.push(value);
                }
                results[slot] = Some(
                    __MettailDovetailRebuildValue::#wrap(#cat::#label(normalized)),
                );
            },
        },
        CollectionType::HashSet => quote! {
            (#constructor_tag, #cat::#label(ref coll)) => {
                let elements_count = coll.len();
                assert_eq!(
                    value_base.checked_add(elements_count),
                    Some(value_end),
                    "normalize: tagged set value-count mismatch",
                );
                let mut normalized =
                    std::collections::HashSet::with_capacity(elements_count);
                for index in 0..elements_count {
                    let value = results[value_base + index].take()
                        .expect("normalize: missing hashset element")
                        .#take_element()
                        .expect("normalize: wrong category in hashset slot");
                    normalized.insert(value);
                }
                results[slot] = Some(
                    __MettailDovetailRebuildValue::#wrap(#cat::#label(normalized)),
                );
            },
        },
    }
}

fn generate_tagged_binder_assemble_case(
    cat: &Ident,
    constructor_tag: u32,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
    multi: bool,
) -> TokenStream {
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let take_body =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(body_cat);
    let total_fields = pre_scope_fields.len() + 1;
    let field_names: Vec<Ident> = (0..total_fields).map(|i| format_ident!("f{}", i)).collect();
    let scope = &field_names[total_fields - 1];
    let frame_bindings =
        emit_tagged_pre_field_frame_bindings(pre_scope_fields, &field_names, language);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields, language);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields, language);
    let missing_body = if multi {
        "normalize: missing multi-binder body"
    } else {
        "normalize: missing binder body"
    };
    let wrong_body = if multi {
        "normalize: wrong category in multi-binder body"
    } else {
        "normalize: wrong category in binder body"
    };

    quote! {
        (#constructor_tag, #cat::#label(#(ref #field_names),*)) => {
            let mut __value_cursor = value_base;
            #(#frame_bindings)*
            let body_slot = __value_cursor;
            __value_cursor = __value_cursor
                .checked_add(1)
                .expect("normalize: binder body interval overflow");
            assert_eq!(
                __value_cursor,
                value_end,
                "normalize: tagged binder value-count mismatch",
            );
            let cloned_pattern = #scope.inner().unsafe_pattern.clone();
            #(#pre_extracts)*
            let body = results[body_slot]
                .take()
                .expect(#missing_body)
                .#take_body()
                .expect(#wrong_body);
            let new_scope = mettail_runtime::Scope::from_parts_unsafe(
                cloned_pattern,
                std::sync::Arc::new(body),
            );
            results[slot] = Some(__MettailDovetailRebuildValue::#wrap(
                #cat::#label(#(#pre_construct)* new_scope)
            ));
        },
    }
}

fn emit_tagged_pre_field_frame_bindings(
    pre_scope_fields: &[FieldInfo],
    field_names: &[Ident],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let source = &field_names[i];
            if field.is_semantic_boundary(language) {
                let carrier = format_ident!("pf{}_data", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_predicate {
                let carrier = format_ident!("pf{}_pred", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_optional && field.is_collection {
                let carrier = format_ident!("pf{}_cloned", i);
                return quote! { let #carrier = (*#source).clone(); };
            }
            if field.is_collection {
                let start = format_ident!("pf{}_start", i);
                let count = format_ident!("pf{}_count", i);
                return match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                        let counts = format_ident!("pf{}_counts", i);
                        quote! {
                            let #start = __value_cursor;
                            let #counts: Vec<usize> =
                                #source.iter().map(|(_element, count)| count).collect();
                            let #count = #counts.len();
                            __value_cursor = __value_cursor
                                .checked_add(#count)
                                .expect("normalize: pre-scope bag interval overflow");
                        }
                    },
                    CollectionType::Vec | CollectionType::HashSet => quote! {
                        let #start = __value_cursor;
                        let #count = #source.len();
                        __value_cursor = __value_cursor
                            .checked_add(#count)
                            .expect("normalize: pre-scope collection interval overflow");
                    },
                };
            }
            let slot = format_ident!("pf{}_slot", i);
            quote! {
                let #slot = __value_cursor;
                __value_cursor = __value_cursor
                    .checked_add(1)
                    .expect("normalize: pre-scope field interval overflow");
            }
        })
        .collect()
}

/// Dispatch per-variant Assemble arm. Leaf variants have no Assemble arm.
fn generate_assemble_arm(
    cat: &Ident,
    variant: &VariantKind,
    hol_pairs: &HashSet<(String, String)>,
    cancel_set: &HashMap<(String, String), &CancellationPair>,
    cat_str: &str,
) -> Option<TokenStream> {
    match variant {
        VariantKind::Var { .. }
        | VariantKind::Literal { .. }
        | VariantKind::CollectionLiteral { .. }
        | VariantKind::Nullary { .. } => None,

        VariantKind::RecursiveNativeLiteral { label, carrier } => {
            Some(generate_recursive_native_assemble_arm(cat, label, carrier))
        },

        // ★ #141 G5 — `Some`, never `None`: `None` means "no arm for this
        // variant", which would DISCARD the refusal. See `VariantKind::Refused`.
        VariantKind::Refused { message, .. } => Some(quote! { compile_error!(#message); }),

        VariantKind::Regular { label, .. } => {
            let label_str = label.to_string();

            // HOL Apply<Dom>
            if let Some(dom_str) = strip_prefix(&label_str, "Apply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return None;
                }
            }
            if let Some(dom_str) = strip_prefix(&label_str, "MApply") {
                if hol_pairs.contains(&(cat_str.to_string(), dom_str.to_string())) {
                    return None;
                }
            }

            // Cancellation
            if let Some(pair) = cancel_set.get(&(cat_str.to_string(), label_str.clone())) {
                return Some(generate_cancel_assemble_arm(cat, label, pair));
            }

            // Ordinary Regular constructors are assembled by the category's
            // single layout-derived tagged helper.
            None
        },

        VariantKind::Collection { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => None,
    }
}

fn generate_recursive_native_assemble_arm(
    cat: &Ident,
    label: &Ident,
    carrier: &NativeRecursiveCarrier,
) -> TokenStream {
    let assemble = format_ident!("AssembleNative_{}_{}", cat, label);
    let wrap = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let take_key = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
        carrier.key_category(),
    );
    let take_value = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
        carrier.value_category(),
    );
    let payload = carrier.construct(&quote! { pathmap }, &quote! { focus });
    quote! {
        NormTask::#assemble {
            slot,
            mode,
            elements_start,
            elements_count,
            focus,
        } => {
            #[inline(never)]
            fn assemble(
                results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
                slot: usize,
                mode: mettail_runtime::PathMapMode,
                elements_start: usize,
                elements_count: usize,
                focus: Vec<u8>,
            ) {
                let pathmap = match mode {
                    mettail_runtime::PathMapMode::Empty => {
                        assert_eq!(elements_count, 0);
                        mettail_runtime::PathMapLit::Empty
                    },
                    mettail_runtime::PathMapMode::Set => {
                        let mut entries = mettail_runtime::HashMapLit::new();
                        for index in 0..elements_count {
                            let key = results[elements_start + index].take()
                                .expect("normalize: missing zipper set key")
                                .#take_key()
                                .expect("normalize: zipper set-key category mismatch");
                            entries.insert(key, ());
                        }
                        mettail_runtime::PathMapLit::Set(entries)
                    },
                    mettail_runtime::PathMapMode::Map => {
                        assert_eq!(elements_count % 2, 0);
                        let mut entries = mettail_runtime::HashMapLit::new();
                        let mut index = 0;
                        while index < elements_count {
                            let key = results[elements_start + index].take()
                                .expect("normalize: missing zipper map key")
                                .#take_key()
                                .expect("normalize: zipper map-key category mismatch");
                            let value = results[elements_start + index + 1].take()
                                .expect("normalize: missing zipper map value")
                                .#take_value()
                                .expect("normalize: zipper map-value category mismatch");
                            entries.insert(key, value);
                            index += 2;
                        }
                        mettail_runtime::PathMapLit::Map(entries)
                    },
                };
                results[slot] = Some(__MettailDovetailRebuildValue::#wrap(
                    #cat::#label(#payload)
                ));
            }
            assemble(
                results,
                slot,
                mode,
                elements_start,
                elements_count,
                focus,
            );
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
/// instead of `normalize_iterative`'s. (The same `#[inline(never)]` peel
/// idiom is shared with the sibling iterative term-ops.)
#[cfg(test)]
fn generate_regular_assemble_arm(
    cat: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    is_native: bool,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleReg_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);

    // Build flat (pat-name, helper-arg-decl, helper-arg-name) lists.
    let mut pat_flat: Vec<TokenStream> = Vec::new();
    let mut decl_flat: Vec<TokenStream> = Vec::new();
    let mut call_flat: Vec<TokenStream> = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        if field.is_semantic_boundary(language) {
            let carrier = format_ident!("f{}_data", i);
            let ty = field.semantic_boundary_carrier_type();
            pat_flat.push(quote! { #carrier });
            decl_flat.push(quote! { #carrier: #ty });
            call_flat.push(quote! { #carrier });
            continue;
        }
        if field.is_opaque_leaf() {
            // L9-3/L9-4: the opaque-leaf carrier rides the frame as `f{i}_text`
            // (declared by `emit_reg_field_decl`, cloned in the Visit arm);
            // extract is a no-op and construct passes it through unchanged.
            let text_name = format_ident!("f{}_text", i);
            let text_ty = field.opaque_leaf_type();
            pat_flat.push(quote! { #text_name });
            decl_flat.push(quote! { #text_name: #text_ty });
            call_flat.push(quote! { #text_name });
            continue;
        }
        if field.is_predicate {
            // Task #14 (Option<Guard>): predicate-FIRST, mirroring the
            // Binder pre-scope precedent (`emit_pre_field_decl_list` /
            // `emit_reg_field_extract` / `emit_reg_field_construct` are all
            // predicate-first). Without this arm a NON-optional Regular
            // predicate fell through to the scalar else (binding
            // `f{i}_slot: usize` against the decl's `f{i}_pred`), and an
            // optional one destructured nonexistent `f{i}_slot`/`f{i}_some`
            // fields (E0026/E0027) while construct referenced the unbound
            // `f{i}_pred` (E0425). The pred rides the frame by name; the
            // extract step is a no-op and construct passes it through.
            let pred_name = format_ident!("f{}_pred", i);
            let pred_ty = if field.is_optional {
                quote! { Option<mettail_runtime::BehavioralPred> }
            } else {
                quote! { mettail_runtime::BehavioralPred }
            };
            pat_flat.push(quote! { #pred_name });
            decl_flat.push(quote! { #pred_name: #pred_ty });
            call_flat.push(quote! { #pred_name });
            continue;
        }
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
        .map(|(i, field)| emit_reg_field_extract(i, field, language))
        .collect();

    let construct_fields: Vec<TokenStream> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| emit_reg_field_construct(i, field, language))
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

fn emit_reg_field_extract(i: usize, field: &FieldInfo, language: &LanguageDef) -> TokenStream {
    if field.is_predicate || field.is_opaque_leaf() || field.is_semantic_boundary(language) {
        // Already in scope as f{i}_pred / f{i}_text — nothing to extract.
        return quote! {};
    }
    let result_ident = format_ident!("field_{}", i);
    let take = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
        &field.category,
    );

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
                Some(std::sync::Arc::new(
                    results[#slot_name]
                        .take()
                        .expect("normalize: missing optional inner")
                        .#take()
                        .expect("normalize: wrong category in optional slot"),
                ))
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
                        let value = results[#start_name + idx].take()
                            .expect("normalize: missing collection element")
                            .#take()
                            .expect("normalize: wrong category in collection slot");
                        #result_ident.insert_n(value, *count);
                    }
                }
            },
            // Phase 4 #5b (2026-05-12): HashMap — 2*N flat slots laid
            // out as (k0, v0, k1, v1, ...) per `emit_collection_field_alloc`.
            // Reconstruct entries by zipping consecutive pairs.
            CollectionType::HashMap | CollectionType::PathMap => {
                quote! {
                    let mut #result_ident =
                        mettail_runtime::HashMapLit::default();
                    for entry_idx in 0..#count_name {
                        let k_slot = #start_name + entry_idx * 2;
                        let v_slot = #start_name + entry_idx * 2 + 1;
                        let k = results[k_slot].take()
                            .expect("normalize: missing hashmap key")
                            .#take()
                            .expect("normalize: wrong category in hashmap k slot");
                        let v = results[v_slot].take()
                            .expect("normalize: missing hashmap value")
                            .#take()
                            .expect("normalize: wrong category in hashmap v slot");
                        #result_ident.insert(k, v);
                    }
                }
            },
            CollectionType::Vec => {
                quote! {
                    let mut #result_ident = Vec::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        let value = results[#start_name + idx].take()
                            .expect("normalize: missing vec element")
                            .#take()
                            .expect("normalize: wrong category in vec slot");
                        #result_ident.push(value);
                    }
                }
            },
            CollectionType::HashSet => {
                quote! {
                    let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                    for idx in 0..#count_name {
                        let value = results[#start_name + idx].take()
                            .expect("normalize: missing hashset element")
                            .#take()
                            .expect("normalize: wrong category in hashset slot");
                        #result_ident.insert(value);
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
        let #result_ident = results[#slot_name].take()
            .expect("normalize: missing result in slot")
            .#take()
            .expect("normalize: wrong category in slot");
    }
}

fn emit_reg_field_construct(i: usize, field: &FieldInfo, language: &LanguageDef) -> TokenStream {
    if field.is_semantic_boundary(language) {
        let carrier = format_ident!("f{}_data", i);
        return quote! { #carrier };
    }
    if field.is_opaque_leaf() {
        // L9-3: pass the bare `String` carrier through (never Arc-wrapped).
        let text_name = format_ident!("f{}_text", i);
        return quote! { #text_name };
    }
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
#[cfg(test)]
fn generate_collection_assemble_arm(
    cat: &Ident,
    label: &Ident,
    element_cat: &Ident,
    coll_type: &CollectionType,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleColl_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let elem_wrap = format_ident!("Wrap{}", element_cat);

    // Per-arm `#[inline(never)]` peel rationale — shared with the sibling
    // iterative term-ops.
    match coll_type {
        CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
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
#[cfg(test)]
fn generate_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleBind_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_slot_pattern(pre_scope_fields, language);
    // Residual #11-2 (2026-07-14): typed helper-param decls for the peel, in
    // one-to-one arity/name agreement with `slot_pattern` for every in-tree
    // pre-scope shape (scalar/predicate/Vec/opt-collection — verified: no
    // HashBag/HashMap pre-scope field exists in any of the 22 languages, so the
    // latent HashMap decl/pattern asymmetry stays dead).
    let pre_decls = emit_pre_field_decl_list(pre_scope_fields, language);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields, language);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields, language);

    // PRE-PEEL body (residual #11-2, 2026-07-14): the arm body inlined directly
    // in `normalize_iterative`, summing this variant's locals into the driver
    // frame. Commented-out-never-deleted per the disable policy; replaced by the
    // `#[inline(never)]` per-arm peel below (pure code motion — same statements,
    // same `.expect(...)` messages, same drop/eval order; only the machine-code
    // frame moves into the helper).
    /*
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
    */
    // Frame-bound constraint: the body must NOT inline in the driver — the
    // 400 Bind arms (rholang) each carry `body`/`new_scope`/ctor locals, whose
    // -O0 alloca sum overflowed the 2 MiB thread stack. Peel into a local
    // `#[inline(never)]` fn (touches `results` only — no stack/sources).
    quote! {
        NormTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_binder(
                results: &mut Vec<Option<AnyNormalizedTerm>>,
                slot: usize,
                #(#pre_decls,)*
                cloned_pattern: mettail_runtime::Binder<String>,
                body_slot: usize,
            ) {
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
            assemble_binder(results, slot, #(#slot_pattern,)* cloned_pattern, body_slot);
        }
    }
}

#[cfg(test)]
fn generate_multi_binder_assemble_arm(
    cat: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    body_cat: &Ident,
    language: &LanguageDef,
) -> TokenStream {
    let assemble_variant = format_ident!("AssembleMBind_{}_{}", cat, label);
    let wrap = format_ident!("Wrap{}", cat);
    let body_wrap = format_ident!("Wrap{}", body_cat);

    let slot_pattern = emit_pre_field_slot_pattern(pre_scope_fields, language);
    // Residual #11-2 (2026-07-14): typed helper-param decls for the peel (see
    // `generate_binder_assemble_arm` for the arity-agreement argument).
    let pre_decls = emit_pre_field_decl_list(pre_scope_fields, language);
    let pre_extracts = emit_pre_field_extracts(pre_scope_fields, language);
    let pre_construct = emit_pre_field_constructs(pre_scope_fields, language);

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion).
    /*
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
    */
    // Frame-bound constraint: the 401 MBind arms (rholang) must not inline in
    // the driver; peel into a local `#[inline(never)]` fn (touches `results`
    // only). `cloned_pattern` is the multi-binder Vec.
    quote! {
        NormTask::#assemble_variant { slot, #(#slot_pattern,)* cloned_pattern, body_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_multi_binder(
                results: &mut Vec<Option<AnyNormalizedTerm>>,
                slot: usize,
                #(#pre_decls,)*
                cloned_pattern: Vec<mettail_runtime::Binder<String>>,
                body_slot: usize,
            ) {
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
            assemble_multi_binder(results, slot, #(#slot_pattern,)* cloned_pattern, body_slot);
        }
    }
}

#[cfg(test)]
fn emit_pre_field_slot_pattern(
    pre_scope_fields: &[FieldInfo],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_semantic_boundary(language) {
                let carrier = format_ident!("pf{}_data", i);
                return quote! { #carrier };
            }
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

fn emit_pre_field_extracts(
    pre_scope_fields: &[FieldInfo],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_semantic_boundary(language) {
                return quote! {};
            }
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
            let take =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
                    &field.category,
                );
            let result_ident = format_ident!("pre_field_{}", i);

            if field.is_collection {
                let start_name = format_ident!("pf{}_start", i);
                let count_name = format_ident!("pf{}_count", i);
                match field.coll_type.as_ref().unwrap_or(&CollectionType::Vec) {
                    CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                        let counts_name = format_ident!("pf{}_counts", i);
                        quote! {
                            let mut #result_ident = mettail_runtime::HashBag::new();
                            for (idx, count) in #counts_name.iter().enumerate() {
                                let value = results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope collection element")
                                    .#take()
                                    .expect("normalize: wrong category in pre-scope collection slot");
                                #result_ident.insert_n(value, *count);
                            }
                        }
                    }
                    CollectionType::Vec => {
                        quote! {
                            let mut #result_ident = Vec::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                let value = results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope vec element")
                                    .#take()
                                    .expect("normalize: wrong category in pre-scope vec slot");
                                #result_ident.push(value);
                            }
                        }
                    }
                    CollectionType::HashSet => {
                        quote! {
                            let mut #result_ident = std::collections::HashSet::with_capacity(#count_name);
                            for idx in 0..#count_name {
                                let value = results[#start_name + idx].take()
                                    .expect("normalize: missing pre-scope hashset element")
                                    .#take()
                                    .expect("normalize: wrong category in pre-scope hashset slot");
                                #result_ident.insert(value);
                            }
                        }
                    }
                }
            } else {
                let slot_name = format_ident!("pf{}_slot", i);
                quote! {
                    let #result_ident = results[#slot_name].take()
                        .expect("normalize: missing pre-scope result")
                        .#take()
                        .expect("normalize: wrong category in pre-scope slot");
                }
            }
        })
        .collect()
}

fn emit_pre_field_constructs(
    pre_scope_fields: &[FieldInfo],
    language: &LanguageDef,
) -> Vec<TokenStream> {
    pre_scope_fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            if field.is_semantic_boundary(language) {
                let carrier = format_ident!("pf{}_data", i);
                return quote! { #carrier, };
            }
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

/// Emit category-factored beta and multi-beta transitions.
///
/// The surface contains one `Apply<Domain>` and `MApply<Domain>` constructor
/// for every admitted host/domain pair, but their semantic transition differs
/// only by the domain-specific typed substitution method.  The compact frame
/// therefore carries the exact constructor tag, extracts the host lambda once,
/// and dispatches through one category-local domain table.  This is the Rust
/// instance of `NewSpecial(kind, category, constructor)` in
/// `TaggedNormalizationMachine.v`.
fn generate_tagged_beta_support(
    category: &SemanticCategoryLayout,
    hol_pairs: &HashSet<(String, String)>,
) -> (TokenStream, TokenStream) {
    let cat = category.category();
    let cat_name = cat.to_string();
    let mut apply_domains = Vec::<(u32, Ident)>::new();
    let mut mapply_domains = Vec::<(u32, Ident)>::new();
    for variant in category.variants() {
        let VariantKind::Regular { label, .. } = variant.kind() else {
            continue;
        };
        let label_name = label.to_string();
        if let Some(domain) = strip_prefix(&label_name, "Apply") {
            if hol_pairs.contains(&(cat_name.clone(), domain.to_string())) {
                apply_domains.push((variant.constructor_tag(), format_ident!("{}", domain)));
            }
        } else if let Some(domain) = strip_prefix(&label_name, "MApply") {
            if hol_pairs.contains(&(cat_name.clone(), domain.to_string())) {
                mapply_domains.push((variant.constructor_tag(), format_ident!("{}", domain)));
            }
        }
    }
    if apply_domains.is_empty() && mapply_domains.is_empty() {
        return (TokenStream::new(), TokenStream::new());
    }

    let mut lambda_domains: Vec<String> = hol_pairs
        .iter()
        .filter(|(host, _)| host == &cat_name)
        .map(|(_, domain)| domain.clone())
        .collect();
    lambda_domains.sort();
    lambda_domains.dedup();
    let lam_variants: Vec<Ident> = lambda_domains
        .iter()
        .map(|domain| format_ident!("Lam{}", domain))
        .collect();
    let mlam_variants: Vec<Ident> = lambda_domains
        .iter()
        .map(|domain| format_ident!("MLam{}", domain))
        .collect();

    let wrap_cat = format_ident!("Wrap{}", cat);
    let visit_cat = format_ident!("Visit{}", cat);
    let borrow_cat = any_norm_borrow_method(cat);
    let take_cat =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(cat);
    let construct =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_construct_fn_name(cat);
    let category_value =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let revisit = format_ident!("norm_revisit_owned_{}", cat_name.to_lowercase());
    let revisit_fn = quote! {
        #[inline]
        fn #revisit(
            stack: &mut Vec<NormTask>,
            sources: &mut Vec<Box<AnyNormalizedTerm>>,
            slot: usize,
            term: #cat,
        ) {
            sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(term)));
            let src_ptr: *const #cat = {
                let source = sources.last().expect("normalize: owned revisit missing source");
                source
                    .#borrow_cat()
                    .expect("normalize: owned revisit category mismatch") as *const _
            };
            stack.push(NormTask::#visit_cat { src: src_ptr, slot });
        }
    };

    let apply_helper = format_ident!("norm_assemble_beta_apply_{}", cat_name.to_lowercase());
    let apply_task = format_ident!("AssembleBetaApply{}", cat);
    let apply_domain_arms: Vec<TokenStream> = apply_domains
        .iter()
        .map(|(constructor, domain)| {
            let substitute = format_ident!("substitute_{}", domain.to_string().to_lowercase());
            let take_domain =
                crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(
                    domain,
                );
            quote! {
                #constructor => {
                    let arg = argument
                        .#take_domain()
                        .expect("normalize beta: argument category mismatch");
                    let (binder, body) = scope.unbind();
                    let substituted = (*body).#substitute(&binder.0, &arg);
                    drop(lam);
                    drop(arg);
                    #revisit(stack, sources, slot, substituted);
                }
            }
        })
        .collect();
    let apply_fn = (!apply_domains.is_empty()).then(|| {
        quote! {
            #[inline(never)]
            fn #apply_helper(
                stack: &mut Vec<NormTask>,
                results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
                values: &mut Vec<__MettailDovetailRebuildValue>,
                sources: &mut Vec<Box<AnyNormalizedTerm>>,
                constructor: u32,
                slot: usize,
                lam_slot: usize,
                arg_slot: usize,
            ) {
                let lam = results[lam_slot]
                    .take()
                    .expect("normalize beta: missing lambda")
                    .#take_cat()
                    .expect("normalize beta: lambda category mismatch");
                let argument = results[arg_slot]
                    .take()
                    .expect("normalize beta: missing argument");
                let scope = match &lam {
                    #(#cat::#lam_variants(scope) => Some(scope.clone()),)*
                    _ => None,
                };
                if let Some(scope) = scope {
                    match constructor {
                        #(#apply_domain_arms,)*
                        _ => panic!("normalize beta: unknown tagged constructor"),
                    }
                } else {
                    let value_base = values.len();
                    values.push(__MettailDovetailRebuildValue::#category_value(lam));
                    values.push(argument);
                    let rebuilt = #construct(
                        constructor,
                        value_base,
                        2usize,
                        values,
                    )
                    .expect("normalize beta: shared fallback assembly failed");
                    assert_eq!(values.len(), value_base);
                    results[slot] = Some(
                        __MettailDovetailRebuildValue::#category_value(rebuilt),
                    );
                }
            }
        }
    });
    let apply_arm = (!apply_domains.is_empty()).then(|| {
        quote! {
            NormTask::#apply_task {
                constructor,
                slot,
                lam_slot,
                arg_slot,
            } => {
                #apply_helper(
                    stack,
                    results,
                    values,
                    sources,
                    constructor,
                    slot,
                    lam_slot,
                    arg_slot,
                );
            }
        }
    });

    let mapply_helper = format_ident!("norm_assemble_beta_mapply_{}", cat_name.to_lowercase());
    let mapply_task = format_ident!("AssembleBetaMApply{}", cat);
    let mapply_domain_arms: Vec<TokenStream> = mapply_domains
        .iter()
        .map(|(constructor, domain)| {
            let mapply = format_ident!("MApply{}", domain);
            let substitute =
                format_ident!("multi_substitute_{}", domain.to_string().to_lowercase());
            let take_sequence = any_norm_take_sequence_function(domain);
            quote! {
                #constructor => {
                    let arguments = #take_sequence(results, args_start, args_count);
                    if let Some(scope) = scope {
                        let (binders, body) = scope.unbind();
                        let variables: Vec<_> = binders.iter().map(|binder| &binder.0).collect();
                        let substituted = (*body).#substitute(&variables, &arguments);
                        drop(lam);
                        #revisit(stack, sources, slot, substituted);
                    } else {
                        results[slot] = Some(__MettailDovetailRebuildValue::#category_value(
                            #cat::#mapply(std::sync::Arc::new(lam), arguments),
                        ));
                    }
                }
            }
        })
        .collect();
    let mapply_fn = (!mapply_domains.is_empty()).then(|| {
        quote! {
            #[inline(never)]
            fn #mapply_helper(
                stack: &mut Vec<NormTask>,
                results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
                sources: &mut Vec<Box<AnyNormalizedTerm>>,
                constructor: u32,
                slot: usize,
                lam_slot: usize,
                args_start: usize,
                args_count: usize,
            ) {
                let lam = results[lam_slot]
                    .take()
                    .expect("normalize multi-beta: missing lambda")
                    .#take_cat()
                    .expect("normalize multi-beta: lambda category mismatch");
                let scope = match &lam {
                    #(#cat::#mlam_variants(scope) => Some(scope.clone()),)*
                    _ => None,
                };
                match constructor {
                    #(#mapply_domain_arms,)*
                    _ => panic!("normalize multi-beta: unknown tagged constructor"),
                }
            }
        }
    });
    let mapply_arm = (!mapply_domains.is_empty()).then(|| {
        quote! {
            NormTask::#mapply_task {
                constructor,
                slot,
                lam_slot,
                args_start,
                args_count,
            } => {
                #mapply_helper(
                    stack,
                    results,
                    sources,
                    constructor,
                    slot,
                    lam_slot,
                    args_start,
                    args_count,
                );
            }
        }
    });

    (quote! { #revisit_fn #apply_fn #mapply_fn }, quote! { #apply_arm #mapply_arm })
}

/// β-reduction Assemble arm retained only as a generator-level oracle for the
/// tagged special-transition implementation above.
///
/// 1. Take lam and arg from slots.
/// 2. If lam matches `Cat::Lam<Dom>(scope)`:
///    a. Unbind to get (binder, body).
///    b. Call `body.substitute_<dom>(&binder.0, &arg)` via the subst PDA.
///    c. Box the substituted Cat into `sources`, push `Visit<Cat>` to
///       renormalize — iterative, not recursive.
/// 3. Else: reconstruct `Cat::Apply<Dom>(Box::new(lam), Box::new(arg))`.
#[cfg(test)]
fn generate_beta_apply_assemble_arm(
    cat: &Ident,
    dom_str: &str,
    lam_doms: &[String],
) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaApply_{}_{}", cat, dom_ident);
    let wrap_cat = format_ident!("Wrap{}", cat);
    let wrap_dom = format_ident!("Wrap{}", dom_ident);
    let apply_variant = format_ident!("Apply{}", dom_ident);
    let subst_method = format_ident!("substitute_{}", dom_str.to_lowercase());
    let visit_cat = format_ident!("Visit{}", cat);
    // #307 eval-layer fix (2026-06-11): β accepts EVERY Lam<D'> tag of
    // this category (the surface `^x.{p}` is tag-ambiguous across the
    // synthetic Lam{BinderCat} rules — the winner's tag is arbitrary;
    // binding lives in the body's typed occurrences). Substitution uses
    // the APPLICATION's domain method, which hits exactly the
    // Dom-typed bound occurrences; the domain-exact tag is listed
    // first for readability, the behavior is identical across arms.
    let mut ordered: Vec<&String> = lam_doms.iter().collect();
    ordered.sort_by_key(|d| (d.as_str() != dom_str, d.as_str().to_string()));
    let lam_variants: Vec<Ident> = ordered
        .iter()
        .map(|d| format_ident!("Lam{}", d.as_str()))
        .collect();

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion —
    // identical statements, `.expect(...)` messages, `drop(lam); drop(arg);`
    // ordering, and the `sources.push` -> stable-pointer -> `stack.push(Visit)`
    // sequence; the `src_ptr` raw-pointer idiom is motion-safe because Box heap
    // addresses are stable).
    /*
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
            // Per-tag arms ONLY extract the scope (tiny frames — 13
            // duplicated full bodies blew the 2MiB test-thread stack in
            // debug builds); the single β body follows.
            let __scope = match &lam {
                #(
                    #cat::#lam_variants(scope) => Some(scope.clone()),
                )*
                _ => None,
            };
            if let Some(scope) = __scope {
                // β-reduce: unbind, substitute, renormalize.
                let (binder, body) = scope.unbind();
                let substituted = (*body).#subst_method(&binder.0, &arg);
                sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(substituted)));
                let src_ptr: *const #cat = {
                    let last_box = sources.last().expect("just pushed");
                    match &**last_box {
                        AnyNormalizedTerm::#wrap_cat(v) => v as *const _,
                        _ => unreachable!(),
                    }
                };
                // Drop lam + arg explicitly so we don't hold them across
                // stack push.
                drop(lam);
                drop(arg);
                stack.push(NormTask::#visit_cat { src: src_ptr, slot });
            } else {
                // Not a β-redex — reconstruct Apply with normalized
                // subterms.
                results[slot] = Some(AnyNormalizedTerm::#wrap_cat(
                    #cat::#apply_variant(std::sync::Arc::new(lam), std::sync::Arc::new(arg))
                ));
            }
        }
    }
    */
    // Frame-bound constraint: the 400 BetaApply arms (rholang) each carry
    // `lam`/`arg`/`substituted` (Proc by value), the per-tag scope-clone match,
    // and staging temps — heaviest unpeeled family. Peel into a local
    // `#[inline(never)]` fn on the Tier-1 (stack, results, sources) shape.
    quote! {
        NormTask::#assemble_variant { slot, lam_slot, arg_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_beta_apply(
                stack: &mut Vec<NormTask>,
                results: &mut Vec<Option<AnyNormalizedTerm>>,
                sources: &mut Vec<Box<AnyNormalizedTerm>>,
                slot: usize,
                lam_slot: usize,
                arg_slot: usize,
            ) {
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
                // Per-tag arms ONLY extract the scope (tiny frames — 13
                // duplicated full bodies blew the 2MiB test-thread stack in
                // debug builds); the single β body follows.
                let __scope = match &lam {
                    #(
                        #cat::#lam_variants(scope) => Some(scope.clone()),
                    )*
                    _ => None,
                };
                if let Some(scope) = __scope {
                    // β-reduce: unbind, substitute, renormalize.
                    let (binder, body) = scope.unbind();
                    let substituted = (*body).#subst_method(&binder.0, &arg);
                    sources.push(Box::new(AnyNormalizedTerm::#wrap_cat(substituted)));
                    let src_ptr: *const #cat = {
                        let last_box = sources.last().expect("just pushed");
                        match &**last_box {
                            AnyNormalizedTerm::#wrap_cat(v) => v as *const _,
                            _ => unreachable!(),
                        }
                    };
                    // Drop lam + arg explicitly so we don't hold them across
                    // stack push.
                    drop(lam);
                    drop(arg);
                    stack.push(NormTask::#visit_cat { src: src_ptr, slot });
                } else {
                    // Not a β-redex — reconstruct Apply with normalized
                    // subterms.
                    results[slot] = Some(AnyNormalizedTerm::#wrap_cat(
                        #cat::#apply_variant(std::sync::Arc::new(lam), std::sync::Arc::new(arg))
                    ));
                }
            }
            assemble_beta_apply(stack, results, sources, slot, lam_slot, arg_slot);
        }
    }
}

/// Multi-β Assemble arm.
#[cfg(test)]
fn generate_beta_mapply_assemble_arm(
    cat: &Ident,
    dom_str: &str,
    lam_doms: &[String],
) -> TokenStream {
    let dom_ident = format_ident!("{}", dom_str);
    let assemble_variant = format_ident!("AssembleBetaMApply_{}_{}", cat, dom_ident);
    let wrap_cat = format_ident!("Wrap{}", cat);
    let wrap_dom = format_ident!("Wrap{}", dom_ident);
    let mapply_variant = format_ident!("MApply{}", dom_ident);
    let multi_subst_method = format_ident!("multi_substitute_{}", dom_str.to_lowercase());
    let visit_cat = format_ident!("Visit{}", cat);
    // #307 eval-layer fix (2026-06-11): multi-β accepts EVERY MLam<D'>
    // tag (symmetric with the Apply generalization — the tag carries no
    // binding information; the typed multi-substitution does).
    let mut ordered: Vec<&String> = lam_doms.iter().collect();
    ordered.sort_by_key(|d| (d.as_str() != dom_str, d.as_str().to_string()));
    let mlam_variants: Vec<Ident> = ordered
        .iter()
        .map(|d| format_ident!("MLam{}", d.as_str()))
        .collect();

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion;
    // `Vec::with_capacity(args_count)` preallocation preserved verbatim).
    /*
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

            let __scope = match &lam {
                #(
                    #cat::#mlam_variants(scope) => Some(scope.clone()),
                )*
                _ => None,
            };
            if let Some(scope) = __scope {
                let (binders, body) = scope.unbind();
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
    */
    // Frame-bound constraint: the 400 BetaMApply arms (rholang) add
    // `args_vec: Vec<Dom>` + per-loop temps to the BetaApply shape. Peel into a
    // local `#[inline(never)]` fn on the Tier-1 (stack, results, sources) shape.
    quote! {
        NormTask::#assemble_variant { slot, lam_slot, args_start, args_count } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_beta_mapply(
                stack: &mut Vec<NormTask>,
                results: &mut Vec<Option<AnyNormalizedTerm>>,
                sources: &mut Vec<Box<AnyNormalizedTerm>>,
                slot: usize,
                lam_slot: usize,
                args_start: usize,
                args_count: usize,
            ) {
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

                let __scope = match &lam {
                    #(
                        #cat::#mlam_variants(scope) => Some(scope.clone()),
                    )*
                    _ => None,
                };
                if let Some(scope) = __scope {
                    let (binders, body) = scope.unbind();
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
            assemble_beta_mapply(stack, results, sources, slot, lam_slot, args_start, args_count);
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
    let result_cat = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_variant(cat);
    let take_inner =
        crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(inner_cat);
    let visit_cat = format_ident!("Visit{}", cat);

    // PRE-PEEL body (residual #11-2, 2026-07-14): commented-out-never-deleted;
    // replaced by the `#[inline(never)]` per-arm peel below (pure code motion).
    /*
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
    */
    // Frame-bound constraint: the AssembleCancel arm carries `inner`/`peeled`
    // (Cat by value) + staging temps; peel into a local `#[inline(never)]` fn on
    // the Tier-1 (stack, results, sources) shape (uniform with the β families).
    quote! {
        NormTask::#assemble_variant { slot, inner_slot } => {
            #[inline(never)]
            #[allow(dead_code, unused_variables, non_snake_case)]
            fn assemble_cancel(
                stack: &mut Vec<NormTask>,
                results: &mut Vec<Option<__MettailDovetailRebuildValue>>,
                sources: &mut Vec<Box<AnyNormalizedTerm>>,
                slot: usize,
                inner_slot: usize,
            ) {
                let inner = results[inner_slot].take()
                    .expect("normalize cancel: missing inner")
                    .#take_inner()
                    .expect("normalize cancel: wrong category in inner slot");

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
                    results[slot] = Some(__MettailDovetailRebuildValue::#result_cat(
                        #cat::#label(std::sync::Arc::new(inner))
                    ));
                }
            }
            assemble_cancel(stack, results, sources, slot, inner_slot);
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
    let take = crate::gen::runtime::dovetail_report::reconstruct::rebuild_value_take_method(cat);

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
                        NORM_VALUE_POOL.with(|v| {
                            NORM_SOURCE_POOL.with(|s| {
                                let mut stack = t.take();
                                let mut results = r.take();
                                let mut values = v.take();
                                let mut sources = s.take();
                                stack.clear();
                                results.clear();
                                values.clear();
                                sources.clear();

                                results.push(None);
                                stack.push(NormTask::#visit_variant {
                                    src: self as *const _,
                                    slot: 0,
                                });

                                normalize_iterative(
                                    &mut stack,
                                    &mut results,
                                    &mut values,
                                    &mut sources,
                                );
                                assert!(
                                    values.is_empty(),
                                    "normalize: root leaked shared assembly values",
                                );

                                let root = results[0].take()
                                    .expect("normalize: root slot empty")
                                    .#take()
                                    .expect("normalize: wrong category in root slot");

                                s.set(sources);
                                v.set(values);
                                r.set(results);
                                t.set(stack);
                                root
                            })
                        })
                    })
                });
                result
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn language() -> LanguageDef {
        crate::gen::empty_language_for_tests()
    }

    fn pred_field(optional: bool) -> FieldInfo {
        FieldInfo {
            category: format_ident!("Guard"),
            is_collection: false,
            coll_type: None,
            is_predicate: true,
            is_optional: optional,
            opaque_leaf: None,
        }
    }

    fn scalar_field(cat: &str) -> FieldInfo {
        FieldInfo {
            category: format_ident!("{}", cat),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        }
    }

    #[test]
    fn reg_field_decl_bare_pred_unchanged() {
        // Task #14 gate-1: the mandatory-guard decl must emit the exact
        // pre-#14 tokens (byte-identity for guarded_rho's shape).
        let tokens = emit_reg_field_decl(1, &pred_field(false), &language()).to_string();
        assert_eq!(tokens, "f1_pred : mettail_runtime :: BehavioralPred");
    }

    #[test]
    fn reg_field_decl_optional_pred_is_option_typed() {
        let tokens = emit_reg_field_decl(1, &pred_field(true), &language()).to_string();
        assert_eq!(tokens, "f1_pred : Option < mettail_runtime :: BehavioralPred >",);
    }

    #[test]
    fn reg_assemble_arm_optional_pred_coherent() {
        // The guardoptsmoke PCheck shape: (Arc<Int>, Option<BehavioralPred>)
        // on a native category. Pre-#14 the assemble arm destructured
        // nonexistent `f1_slot`/`f1_some` (E0026/E0027) and construct
        // referenced the unbound `f1_pred` (E0425).
        let cat = format_ident!("Int");
        let label = format_ident!("PCheck");
        let fields = vec![scalar_field("Int"), pred_field(true)];
        let arm =
            generate_regular_assemble_arm(&cat, &label, &fields, true, &language()).to_string();
        assert!(
            arm.contains("f1_pred : Option < mettail_runtime :: BehavioralPred >"),
            "helper decl must carry the Option type: {arm}",
        );
        assert!(
            !arm.contains("f1_slot") && !arm.contains("f1_some"),
            "the pred slot must not use the Opt-Group slot/some machinery: {arm}",
        );
        assert!(
            arm.contains("f0_slot : usize"),
            "the scalar slot stays on the slot machinery: {arm}",
        );
    }

    #[test]
    fn reg_assemble_arm_bare_pred_latent_break_fixed() {
        // The latent NON-optional Regular-pred break: the loop had no
        // is_predicate arm, so a bare pred fell to the scalar else and
        // bound `f1_slot: usize` against the decl's `f1_pred`.
        let cat = format_ident!("Proc");
        let label = format_ident!("PGuarded");
        let fields = vec![scalar_field("Proc"), pred_field(false)];
        let arm =
            generate_regular_assemble_arm(&cat, &label, &fields, false, &language()).to_string();
        assert!(
            arm.contains("f1_pred : mettail_runtime :: BehavioralPred"),
            "bare pred must bind by its decl name/type: {arm}",
        );
        assert!(
            !arm.contains("f1_slot"),
            "bare pred must not fall through to the scalar slot binding: {arm}",
        );
    }

    #[test]
    fn tagged_normalization_removes_constructor_specific_collection_frames() {
        let language = crate::gen::singleton_collection_language_for_tests();
        let generated = generate_normalize_functions(&language, &[])
            .to_string()
            .replace(' ', "");
        assert!(
            generated.contains("AssembleTagged"),
            "normalization must emit the typed tagged frame family",
        );
        assert!(
            !generated.contains("AssembleColl_"),
            "whole-collection constructors must not regain private task variants",
        );
        assert!(
            !generated.contains("AssembleReg_"),
            "regular constructors must not regain private task variants",
        );
    }

    #[test]
    fn tagged_beta_frames_are_factored_by_host_category_not_domain() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: TaggedBetaShape,
                types { Term Name },
                terms {
                    TZero . |- "t" : Term;
                    NZero . |- "n" : Name;
                    Bind . ^x.body:[Name -> Term] |- "bind" x "." body : Term;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("tagged-beta fixture must parse");
        let categories: Vec<&LangType> = crate::gen::semantic_transit_types(&language).collect();
        let layout = SemanticAdapterLayout::derive(&language)
            .expect("tagged-beta fixture must have a complete semantic layout");
        let tasks = generate_norm_task_enum(&categories, &layout, &language, &[])
            .to_string()
            .replace(' ', "");

        for category in ["Term", "Name"] {
            let apply = format!("AssembleBetaApply{category}{{");
            let mapply = format!("AssembleBetaMApply{category}{{");
            assert_eq!(
                tasks.matches(&apply).count(),
                1,
                "one beta task must serve every domain of host {category}: {tasks}",
            );
            assert_eq!(
                tasks.matches(&mapply).count(),
                1,
                "one multi-beta task must serve every domain of host {category}: {tasks}",
            );
        }
        assert_eq!(tasks.matches("AssembleBetaApply").count(), 2);
        assert_eq!(tasks.matches("AssembleBetaMApply").count(), 2);
        assert!(
            !tasks.contains("AssembleBetaApply_") && !tasks.contains("AssembleBetaMApply_"),
            "the former host-by-domain task family must remain absent: {tasks}",
        );
    }

    #[test]
    fn legacy_constructor_assembly_oracles_remain_available_only_to_tests() {
        let cat = format_ident!("Proc");
        let label = format_ident!("Par");
        let body = format_ident!("Proc");
        let domains = vec!["Proc".to_string()];
        assert!(!generate_collection_assemble_arm(&cat, &label, &cat, &CollectionType::HashBag,)
            .is_empty());
        assert!(!generate_binder_assemble_arm(&cat, &label, &[], &body, &language()).is_empty());
        assert!(
            !generate_multi_binder_assemble_arm(&cat, &label, &[], &body, &language()).is_empty(),
        );
        assert!(!generate_beta_apply_assemble_arm(&cat, "Proc", &domains).is_empty());
        assert!(!generate_beta_mapply_assemble_arm(&cat, "Proc", &domains).is_empty());
    }
}
