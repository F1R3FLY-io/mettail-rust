//! Inc 1 — Moniker NativeHandler: binder-congruence normal form.
//!
//! Generates, for a HOST-LESS language with structural-congruence equations
//! (e.g. Ambient), a capture-safe `binder_congruence_nf` that floats `new`
//! binders outward to a canonical normal form. Every move goes through moniker
//! `Scope::unbind` (freshen + open) → reassemble → `Scope::new` (re-close,
//! recomputing de-Bruijn coordinates LOCALLY) — NEVER `from_parts_unsafe`, which
//! is the capture-unsoundness `run_ascent` exhibits.
//!
//! The single load-bearing correctness detail: every freshness GATE is checked
//! against the ORIGINAL binder (`scope.unsafe_pattern()`), NOT the
//! `unbind`-freshened one. `is_fresh(Binder(x'), N)` with `x'` from `unbind`
//! always returns true (x' is brand-new and cannot occur in any pre-existing N),
//! which would silently disable the guard and re-introduce capture. See
//! `docs/architecture/dovetail/ambient-binder/inc1-handler-spec.md`.
//!
//! Disposition gate: emitted iff the language declares equations AND has no
//! `RhoNativeJoin` obligation (no host RSpace). Ambient qualifies; rhocalc /
//! guarded_rho route their binders/COMM to the host and are NOT emitted.

use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashSet;

/// The handler is emitted iff:
///   1. the language declares structural-congruence equations,
///   2. it is host-less (no `RhoNativeJoin` channel/join disposition), and
///   3. it has a surface SINGLE-binder constructor over the primary category
///      (e.g. Ambient's `PNew . ^x.p`).
///
/// Condition 3 both distinguishes a name-restriction calculus (Ambient) from a
/// message-passing process calculus — whose binders are MULTI-binders tied to
/// COMM (rhocalc/guarded_rho: `PInputs . ^[xs]`, `PNew . ^[xs]`) and are routed
/// to the host RSpace — and keeps the float (`impl Cat`) and term-wrapper
/// (`impl {Name}TermInner`) emissions consistent: both depend on a single binder
/// existing.
pub(crate) fn should_emit_binder_congruence(language: &LanguageDef) -> bool {
    !language.equations.is_empty()
        && has_no_host_disposition(language)
        && surface_single_binder_label(language).is_some()
}

/// A language is host-backed iff any of its guard obligations is a
/// `RhoNativeJoin` (a Rho-native guarded join / RSpace atomic continuation).
fn has_no_host_disposition(language: &LanguageDef) -> bool {
    use mettail_rholang_codegen::backend::{collect_guard_obligations, RhoGuardObligationKind};
    !collect_guard_obligations(language)
        .iter()
        .any(|o| matches!(o.kind, RhoGuardObligationKind::RhoNativeJoin))
}

/// The label of the surface (user-declared) single-binder constructor over the
/// primary category, if any (e.g. Ambient `PNew`). Auto-injected HOL binders
/// (`LamProc`, …) are excluded — they are not in `terms`.
fn surface_single_binder_label(language: &LanguageDef) -> Option<syn::Ident> {
    let proc_cat = &language.types.first()?.name;
    let user_labels: HashSet<String> = language.terms.iter().map(|r| r.label.to_string()).collect();
    collect_category_variants(proc_cat, language)
        .iter()
        .find_map(|v| match v {
            VariantKind::Binder { label, body_cat, .. }
                if user_labels.contains(&label.to_string()) && body_cat == proc_cat =>
            {
                Some(label.clone())
            },
            _ => None,
        })
}

/// Generate the binder-congruence normal-form handler for the primary category.
pub fn generate_binder_congruence(language: &LanguageDef) -> TokenStream {
    if !should_emit_binder_congruence(language) {
        return quote! {};
    }

    let proc_cat = language
        .types
        .first()
        .expect("language has a primary category")
        .name
        .clone();

    // Surface (user-declared) constructor labels — the auto-injected HOL
    // machinery (Lam*/Apply*/MApply*) is NOT in `terms` and passes through.
    let user_labels: HashSet<String> = language.terms.iter().map(|r| r.label.to_string()).collect();

    let variants = collect_category_variants(&proc_cat, language);

    // The surface single-binder constructor (`PNew`) — guaranteed to exist by
    // `should_emit_binder_congruence`.
    let binder_label = surface_single_binder_label(language)
        .expect("should_emit_binder_congruence guarantees a surface single binder");

    // Build the per-variant float arms.
    let mut arms: Vec<TokenStream> = Vec::new();

    for v in &variants {
        match v {
            // The `new` constructor: open, NF the body, re-close, then canonically
            // reorder any adjacent `new`-run (NewComm).
            VariantKind::Binder { label, body_cat, .. }
                if *label == binder_label && *body_cat == proc_cat =>
            {
                arms.push(quote! {
                    #proc_cat::#label(__scope) => {
                        let (__binder, __opened) = __scope.clone().unbind();
                        let __body_nf = (*__opened).binder_congruence_nf();
                        // Collect the maximal adjacent new-run rooted here and
                        // re-close in the alpha-canonical (FIX-A) order.
                        let mut __binders = ::std::vec![__binder];
                        let mut __core = __body_nf;
                        while let #proc_cat::#label(__inner) = &__core {
                            let (__b2, __body2) = __inner.clone().unbind();
                            __binders.push(__b2);
                            __core = (*__body2).binder_congruence_nf();
                        }
                        #proc_cat::__bcn_close_new_run_canonical(__binders, __core)
                    }
                });
            },
            // A surface prefix `C(N.., P)` with exactly one primary-category field:
            // float a `new` out of P iff its (ORIGINAL) binder is fresh in the
            // other fields (FIX-B = the standard `x ∉ fn(N)`).
            VariantKind::Regular { label, fields } if user_labels.contains(&label.to_string()) => {
                let proc_field_positions: Vec<usize> = fields
                    .iter()
                    .enumerate()
                    .filter(|(_, f)| f.category == proc_cat && !f.is_collection && !f.is_optional)
                    .map(|(i, _)| i)
                    .collect();
                // Only the "prefix" shape (exactly one primary-category body field,
                // remaining fields non-collection) is floated; anything else passes
                // through (handled by the catch-all).
                if proc_field_positions.len() != 1 {
                    continue;
                }
                let body_pos = proc_field_positions[0];
                let binds: Vec<syn::Ident> = (0..fields.len())
                    .map(|i| quote::format_ident!("__f{}", i))
                    .collect();
                let body_bind = &binds[body_pos];
                // Freshness against every OTHER field (each is a `BoundTerm`).
                let other_fresh: Vec<TokenStream> = binds
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != body_pos)
                    .map(|(_, b)| quote! { is_fresh(__s.unsafe_pattern(), #b.as_ref()) })
                    .collect();
                let fresh_guard = if other_fresh.is_empty() {
                    quote! { true }
                } else {
                    quote! { #(#other_fresh)&&* }
                };
                // Rebuild the prefix with the floated (opened) body.
                let rebuild_opened: Vec<TokenStream> = binds
                    .iter()
                    .enumerate()
                    .map(|(i, b)| {
                        if i == body_pos {
                            quote! { __opened }
                        } else {
                            quote! { #b.clone() }
                        }
                    })
                    .collect();
                // Rebuild with the normalized (not floated) body.
                let rebuild_nf: Vec<TokenStream> = binds
                    .iter()
                    .enumerate()
                    .map(|(i, b)| {
                        if i == body_pos {
                            quote! { ::std::sync::Arc::new(__body_nf) }
                        } else {
                            quote! { #b.clone() }
                        }
                    })
                    .collect();
                arms.push(quote! {
                    #proc_cat::#label(#(#binds),*) => {
                        let __body_nf = (** #body_bind).binder_congruence_nf();
                        if let #proc_cat::#binder_label(__s) = &__body_nf {
                            if #fresh_guard {
                                let (__fb, __opened) = __s.clone().unbind();
                                return #proc_cat::#binder_label(
                                    ::mettail_runtime::Scope::new(
                                        __fb,
                                        ::std::sync::Arc::new(
                                            #proc_cat::#label(#(#rebuild_opened),*),
                                        ),
                                    ),
                                );
                            }
                        }
                        #proc_cat::#label(#(#rebuild_nf),*)
                    }
                });
            },
            // The parallel bag (`PPar`): scope-extrude a `new` member outward iff
            // its ORIGINAL binder is fresh in the residual multiset.
            VariantKind::Collection { label, element_cat, .. }
                if user_labels.contains(&label.to_string()) && *element_cat == proc_cat =>
            {
                arms.push(quote! {
                    #proc_cat::#label(__bag) => {
                        // Normalize each distinct member, count-preserving.
                        let __nfd: ::std::vec::Vec<(#proc_cat, usize)> = __bag
                            .iter()
                            .map(|(__m, __c)| (__m.binder_congruence_nf(), __c))
                            .collect();
                        for __i in 0..__nfd.len() {
                            if let #proc_cat::#binder_label(__s) = &__nfd[__i].0 {
                                // Residual = all members minus ONE occurrence of member __i.
                                let mut __residual: ::std::vec::Vec<#proc_cat> = ::std::vec::Vec::new();
                                for __j in 0..__nfd.len() {
                                    let __take = if __j == __i { __nfd[__j].1 - 1 } else { __nfd[__j].1 };
                                    for _ in 0..__take {
                                        __residual.push(__nfd[__j].0.clone());
                                    }
                                }
                                let __residual_bag = #proc_cat::#label(
                                    __residual.iter().cloned().collect(),
                                );
                                if is_fresh(__s.unsafe_pattern(), &__residual_bag) {
                                    let (__fb, __opened) = __s.clone().unbind();
                                    let mut __inner = __residual;
                                    __inner.push((*__opened).clone());
                                    return #proc_cat::#binder_label(
                                        ::mettail_runtime::Scope::new(
                                            __fb,
                                            ::std::sync::Arc::new(
                                                #proc_cat::#label(
                                                    __inner.into_iter().collect(),
                                                ),
                                            ),
                                        ),
                                    );
                                }
                            }
                        }
                        // No extrusion: rebuild with normalized members.
                        let mut __all: ::std::vec::Vec<#proc_cat> = ::std::vec::Vec::new();
                        for (__m, __c) in __nfd {
                            for _ in 0..__c {
                                __all.push(__m.clone());
                            }
                        }
                        #proc_cat::#label(__all.into_iter().collect())
                    }
                });
            },
            _ => {},
        }
    }

    quote! {
        impl #proc_cat {
            /// Binder-congruence normal form: float `new`s outward to a fixpoint.
            /// (Inc 1 — capture-safe via moniker `unbind`/`Scope::new`.)
            pub fn binder_congruence_nf(&self) -> #proc_cat {
                let mut __current = self.__bcn_float_pass();
                // Termination backstop: each `__bcn_float_pass` fully normalizes
                // children then floats one level, so the fixpoint is reached in
                // O(term size) passes; this fuel is a paranoia bound far above any
                // realistic term (the `term_eq` fixpoint check is the real
                // terminator). Each float strictly decreases the "new-depth"
                // potential (Σ over news of constructor nodes between the new and
                // the root).
                let mut __fuel: usize = 1_000_000;
                loop {
                    let __next = __current.__bcn_float_pass();
                    if ::mettail_runtime::BoundTerm::term_eq(&__next, &__current) {
                        break;
                    }
                    __current = __next;
                    if __fuel == 0 {
                        break;
                    }
                    __fuel -= 1;
                }
                __current
            }

            /// One bottom-up float pass (recurse into children, then float here).
            fn __bcn_float_pass(&self) -> #proc_cat {
                match self {
                    #(#arms)*
                    // Leaf variants (PZero/PVar) and the auto-injected HOL
                    // machinery (Lam*/Apply*/MApply*) do not occur in parsed
                    // surface terms of a host-less binder calculus; they carry no
                    // floatable `new` and pass through unchanged.
                    __other => __other.clone(),
                }
            }

            /// Re-close a `new`-run `[b0, b1, ..., b_{k-1}]` around `core` in the
            /// alpha-canonical order (NewComm): the permutation that minimizes the
            /// alpha-canonical (FIX-A) semantic key of the fully re-closed run.
            /// `k` is small in practice (`new`-runs are short); capped to avoid a
            /// factorial blow-up.
            fn __bcn_close_new_run_canonical(
                __binders: ::std::vec::Vec<::mettail_runtime::Binder<String>>,
                __core: #proc_cat,
            ) -> #proc_cat {
                fn __close_run(
                    __order: &[::mettail_runtime::Binder<String>],
                    __core: &#proc_cat,
                ) -> #proc_cat {
                    let mut __acc = __core.clone();
                    for __b in __order.iter().rev() {
                        __acc = #proc_cat::#binder_label(::mettail_runtime::Scope::new(
                            __b.clone(),
                            ::std::sync::Arc::new(__acc),
                        ));
                    }
                    __acc
                }
                fn __key(__t: &#proc_cat) -> ::std::vec::Vec<u8> {
                    let mut __h = ::mettail_runtime::FramedSemanticKeyHasher::default();
                    __t.semantic_hash(&mut __h);
                    __h.into_key()
                }
                let __n = __binders.len();
                if __n <= 1 || __n > 6 {
                    return __close_run(&__binders, &__core);
                }
                // Enumerate permutations of indices 0..n (Heap's algorithm).
                let mut __idx: ::std::vec::Vec<usize> = (0..__n).collect();
                let mut __c = ::std::vec![0usize; __n];
                let mut __best: ::std::option::Option<(::std::vec::Vec<u8>, #proc_cat)> = None;
                let __consider = |__perm: &[usize],
                                  __best: &mut ::std::option::Option<(::std::vec::Vec<u8>, #proc_cat)>| {
                    let __order: ::std::vec::Vec<::mettail_runtime::Binder<String>> =
                        __perm.iter().map(|&__i| __binders[__i].clone()).collect();
                    let __closed = __close_run(&__order, &__core);
                    let __k = __key(&__closed);
                    if __best.as_ref().map_or(true, |(__bk, _)| __k < *__bk) {
                        *__best = Some((__k, __closed));
                    }
                };
                __consider(&__idx, &mut __best);
                let mut __i = 0usize;
                while __i < __n {
                    if __c[__i] < __i {
                        if __i % 2 == 0 {
                            __idx.swap(0, __i);
                        } else {
                            __idx.swap(__c[__i], __i);
                        }
                        __consider(&__idx, &mut __best);
                        __c[__i] += 1;
                        __i = 0;
                    } else {
                        __c[__i] = 0;
                        __i += 1;
                    }
                }
                __best.expect("at least one permutation considered").1
            }
        }
    }
}

/// Generate the `try_direct_eval`-facing wrapper that maps the binder-congruence
/// NF over a term (and its `Ambiguous` alternatives), returning `Some` iff some
/// alternative made observable progress (else `None`, preserving fail-closed).
pub fn generate_binder_congruence_term_wrapper(
    language: &LanguageDef,
    inner_enum: &syn::Ident,
) -> TokenStream {
    if !should_emit_binder_congruence(language) {
        return quote! {};
    }
    let proc_cat = language
        .types
        .first()
        .expect("language has a primary category")
        .name
        .clone();
    // Per-type arms: only the primary process category floats; other categories
    // pass through (a `new` lives in the process category).
    let other_cats: Vec<syn::Ident> = language
        .types
        .iter()
        .skip(1)
        .map(|t| t.name.clone())
        .collect();
    let other_arms: Vec<TokenStream> = other_cats
        .iter()
        .map(|c| quote! { #inner_enum::#c(__x) => (#inner_enum::#c(__x.clone()), false), })
        .collect();
    quote! {
        impl #inner_enum {
            /// Binder-congruence NF over a (possibly ambiguous) term. `Some(nf)`
            /// iff observable progress; `None` preserves the fail-closed seam.
            pub fn binder_congruence_nf_term(&self) -> ::std::option::Option<#inner_enum> {
                fn __one(__t: &#inner_enum) -> (#inner_enum, bool) {
                    match __t {
                        #inner_enum::#proc_cat(__p) => {
                            let __nf = __p.binder_congruence_nf();
                            let __progressed = !::mettail_runtime::BoundTerm::term_eq(&__nf, __p);
                            (#inner_enum::#proc_cat(__nf), __progressed)
                        }
                        #(#other_arms)*
                        #inner_enum::Ambiguous(__alts) => {
                            let mut __any = false;
                            let __mapped: ::std::vec::Vec<#inner_enum> = __alts
                                .iter()
                                .map(|__a| {
                                    let (__m, __p) = __one(__a);
                                    if __p { __any = true; }
                                    __m
                                })
                                .collect();
                            (#inner_enum::from_alternatives(__mapped), __any)
                        }
                    }
                }
                let (__nf, __progressed) = __one(self);
                if __progressed { Some(__nf) } else { None }
            }
        }
    }
}
