//! Inc 1 / A-S5.4a — Moniker binder-congruence direct evaluator: normal form.
//!
//! Generates, for a language without a RhoNativeJoin obligation but with
//! structural-congruence equations (e.g. Ambient), a capture-safe
//! `binder_congruence_nf` that floats `new`
//! binders outward to a canonical normal form. Every move goes through moniker
//! `Scope::unbind` (freshen + open) → reassemble → `Scope::new` (re-close,
//! recomputing de-Bruijn coordinates LOCALLY) — NEVER `from_parts_unsafe`, which
//! is the capture-unsoundness `run_ascent` exhibits.
//!
//! A-S5.4a (design v2 §3.2, AM-2/AM-6): the float is UNCONDITIONAL —
//! freshen-then-float, never gated. `unbind` freshens the binder to a
//! globally-fresh name (moniker's process-global gensym), so the freshened
//! binder cannot occur free in any pre-existing sibling/field and re-closing
//! over the widened body captures nothing; the float therefore NEVER stalls.
//! Theory (`ma_theory_alignment.md`): α-conversion is definitional identity in
//! Cardelli–Gordon, so freshen-then-float is one free α step followed by a
//! (Struct Res Par) / (Struct Res Amb) / documented-extension instance whose
//! side condition holds BY CONSTRUCTION. The pre-A-S5.4a freshness gates
//! (`is_fresh` against the ORIGINAL binder) made the NF hint-sensitive and
//! non-maximal (the refuted F1 stall); with the gates dropped, the outer
//! `term_eq`-terminated fixpoint loop in `binder_congruence_nf` drives every
//! `new` maximally outward. The generated per-language `is_fresh` fn remains an
//! uncalled pub API (AM-6b) — freshness is now discharged by construction, not
//! checked. FV: `formal/rocq/rho_bridge/theories/BinderFloatCanonicalization.v`
//! (freshening totality; redex exposure over the C-G subset).
//!
//! FLATNESS OBLIGATION (AM-2): at the bag arm's extrusion seam, a `new` whose
//! opened body is ITSELF the same collection constructor is SPLICED into the
//! widened bag (via the generated `insert_into_<label>` auto-flatten helper —
//! the exact host mirror of `add_flattened_bag`'s work-stack peel), never
//! pushed as one nested element: mettail absorbs (Struct Par Comm/Assoc)
//! REPRESENTATIONALLY in the HashBag, so every bag producer must preserve
//! bag-flatness or sibling redexes stay hidden with no ≡ rule to dissolve them
//! (`float_preserves_bag_flatness` in the FV file).
//!
//! Disposition gate: emitted iff the language declares equations AND has no
//! `RhoNativeJoin` obligation (no host RSpace). Ambient qualifies; rholang /
//! guarded_rho route their binders/COMM to the host and are NOT emitted.
//!
//! ★★ A-S5.4c — THE CONVERSE ADMISSION: EVERY FLOAT ARM IS LICENSED BY A
//! DECLARED EQUATION.
//!
//! The disposition gate above says WHETHER a language gets a handler. It says
//! nothing about WHICH constructors that handler may float across, and until
//! A-S5.4c nothing did: the arms were derived from
//! `collect_category_variants(proc_cat, language)` — the primary category's TERM
//! FORMERS — so the handler floated the binder outward through EVERY constructor
//! of the category, licensed or not. For Ambient the term formers and the
//! declared float equations coincide (`InNew`/`OutNew`/`OpenNew`/`AmbNew` +
//! `ScopeExtrusion` name exactly `PIn`/`POut`/`POpen`/`PAmb`/`PPar`), which is
//! why the surplus was invisible. For Pi they do not, and the surplus was not
//! merely surplus:
//!
//! * `Pi` declares `ScopeExt` (a `PPar` collection float), `NewComm` and
//!   `RepUnfold`; it declares NO prefix float at all;
//! * the generated handler nonetheless emitted prefix float arms for `POut` AND
//!   for `PRep`;
//! * ★★ the `PRep` arm is `!(νx.P) ⟶ νx.(!P)`, which is UNSOUND in the
//!   π-calculus. The left creates a FRESH NAME PER REPLICA; the right SHARES ONE
//!   NAME across all replicas, so two replicas that could not interact become
//!   able to. This is NOT a capture-avoidance side condition, so no amount of
//!   `unbind` freshening repairs it — the A-S5.4a soundness argument below is an
//!   α-conversion argument, and α-conversion has nothing to say about
//!   replication. The justification did not cover the arm it was justifying.
//!
//! The repair is the CONVERSE of the A-S5.4b equations gate. That gate
//! (`rho_net_lower::equations_boundary_canonicalizable`) asks whether every
//! declared EQUATION is a recognized float; this asks whether every emitted ARM
//! is a declared equation. Both directions are needed and only one existed.
//!
//! The arms are therefore now read off `float_satellite_table` — the SAME
//! equation-derived table the in-Rho `^float` receiver family derives its
//! `^float-hoist:{C}` / `^float-merge:{op}` satellites from
//! (`rho_net_float::float_program_par`). One derivation, two consumers: the host
//! NF and the in-Rho lane float across exactly the same constructors BY
//! CONSTRUCTION, and a language gets a float it did not declare in neither.
//! `generated_float_arms_are_exactly_the_declared_float_equations` pins the
//! converse over every bundled language, and
//! `rep_float_arm_is_not_emitted_without_a_declared_float_equation` pins the
//! π-calculus instance directly.
//!
//! ⚠ NOT covered by A-S5.4c (logged, deliberately out of its scope): the binder
//! arm's `__bcn_close_new_run_canonical` reorders an adjacent binder run into the
//! α-canonical order, which is an application of binder-binder COMMUTATION
//! (`NewComm`), and it is applied whether or not the language declares that
//! equation. Every float-bearing bundled language does declare it (Ambient
//! `NewComm`, Pi `NewComm`), so nothing in the corpus is affected today; a future
//! language that declares a float without a commutation would get the reordering
//! unlicensed, which is the same defect one arm over.

use crate::gen::term_ops::subst::{collect_category_variants, VariantKind};
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::float_satellite_table;
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
/// COMM (rholang/guarded_rho: `PInputs . ^[xs]`, `PNew . ^[xs]`) and are routed
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

    // ★ A-S5.4c (module docs): the LICENCE. Every float arm below must name a
    // constructor this language declared a float equation for — the converse of
    // the A-S5.4b equations gate. Derived by the same per-equation recognizer
    // walk the in-Rho `^float` satellites are derived from, so the two lanes
    // float across identical constructors by construction.
    let declared_floats = float_satellite_table(language);

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
            // A surface prefix `C(N.., P)` with exactly one primary-category field
            // AND a DECLARED prefix float equation naming `C` (A-S5.4c): float a
            // `new` out of P unconditionally (A-S5.4a unbind-first float — the
            // pre-A-S5.4a `is_fresh` gate against the original binder is dropped;
            // `unbind` freshens, so the float is capture-safe by construction and
            // never stalls). Unconditional AT a licensed site; no site is licensed
            // by the mere existence of the constructor.
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
                // ★ A-S5.4c: the licence. `float_index`/`arity` are matched too, not
                // just the constructor name — the recognizer records WHICH argument
                // the equation floats out of, and an arm that floated a different
                // field would be a different (undeclared) congruence. The shape
                // agreement is not an accident: `rho_net_lower::float_constructor_shape`
                // computes `primary_field_index` by this exact filter (AM-6e), so a
                // recognized prefix equation always names this `body_pos`.
                if !declared_floats
                    .hoist
                    .iter()
                    .any(|(constructor, float_index, arity)| {
                        *constructor == label.to_string()
                            && *float_index == body_pos
                            && *arity == fields.len()
                    })
                {
                    continue;
                }
                let binds: Vec<syn::Ident> = (0..fields.len())
                    .map(|i| quote::format_ident!("__f{}", i))
                    .collect();
                let body_bind = &binds[body_pos];
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
                // Rebuild with the normalized (not floated) body — the no-`new`
                // case (the body NF is not binder-headed; nothing to float).
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
                            // A-S5.4a: unconditional unbind-first float — freshen
                            // (moniker `unbind`, a process-global gensym) then
                            // float. The freshened binder cannot occur free in
                            // any other field, so re-closing captures nothing.
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
                        #proc_cat::#label(#(#rebuild_nf),*)
                    }
                });
            },
            // The parallel bag (`PPar`), WHEN a collection float equation declares
            // it (A-S5.4c — Ambient's `ScopeExtrusion`, Pi's `ScopeExt`, both the
            // C-G (Struct Res Par) shape): scope-extrude the FIRST `new` member
            // outward unconditionally (A-S5.4a — the pre-A-S5.4a `is_fresh`
            // residual gate is dropped; `unbind` freshens, so extrusion is
            // capture-safe by construction). Successive `new`s are pulled into
            // the canonical run by the enclosing fixpoint + binder-arm
            // run-collection.
            VariantKind::Collection { label, element_cat, .. }
                if user_labels.contains(&label.to_string())
                    && *element_cat == proc_cat
                    && declared_floats.merge_ops.contains(&label.to_string()) =>
            {
                // AM-2: the generated auto-flatten insert (`insert_into_<label>`,
                // term_ops/normalize.rs — the host mirror of `add_flattened_bag`)
                // splices a same-constructor opened body's members into the
                // widened bag instead of nesting one bag element.
                let insert_helper =
                    quote::format_ident!("insert_into_{}", label.to_string().to_lowercase());
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
                                let __total: usize = __nfd.iter().map(|(_, __c)| *__c).sum();
                                let mut __residual: ::std::vec::Vec<#proc_cat> =
                                    ::std::vec::Vec::with_capacity(__total - 1);
                                for __j in 0..__nfd.len() {
                                    let __take = if __j == __i { __nfd[__j].1 - 1 } else { __nfd[__j].1 };
                                    for _ in 0..__take {
                                        __residual.push(__nfd[__j].0.clone());
                                    }
                                }
                                // A-S5.4a: unconditional extrusion — `unbind`
                                // freshens the binder (process-global gensym), so
                                // it cannot occur free in the residual and
                                // re-closing captures nothing.
                                let (__fb, __opened) = __s.clone().unbind();
                                // AM-2 (bag-flatness at the extrusion seam): a
                                // same-constructor opened body SPLICES its members
                                // into the widened bag (work-stack peel, any
                                // depth); any other body inserts as one member.
                                let mut __inner_bag: ::mettail_runtime::HashBag<#proc_cat> =
                                    __residual.into_iter().collect();
                                #proc_cat::#insert_helper(&mut __inner_bag, (*__opened).clone());
                                return #proc_cat::#binder_label(
                                    ::mettail_runtime::Scope::new(
                                        __fb,
                                        ::std::sync::Arc::new(
                                            #proc_cat::#label(__inner_bag),
                                        ),
                                    ),
                                );
                            }
                        }
                        // No `new` member: rebuild with normalized members.
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

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_rholang_codegen::{
        equations_boundary_canonicalizable, language_has_float_handler, reconstruct_language_def,
    };

    /// Reconstruct a bundled language definition from its source file: the body is everything
    /// between the real `language!` invocation's opening `{` and the LAST `}` in the file (the
    /// macro's own closing brace — the same body-text convention the `rholang-codegen` a_s5c
    /// suite uses, i.e. what the macro embeds as `LanguageMetadata::definition_source`). A file's
    /// comments may mention `language!` before OR after the invocation (`acdemo.rs`,
    /// `calculator.rs`), so every mention is tried and the one that reconstructs wins — exactly
    /// one does (the invocation), and a file where none does panics with the last error.
    fn bundled_def(name: &str, source: &str) -> mettail_ast::language::LanguageDef {
        let close = source
            .rfind('}')
            .expect("a language file closes the macro brace");
        let mut search_from = 0;
        let mut last_error = String::from("no language! mention found");
        while let Some(found) = source[search_from..].find("language!") {
            let macro_at = search_from + found;
            if let Some(open_offset) = source[macro_at..].find('{') {
                let open = macro_at + open_offset;
                if open < close {
                    match reconstruct_language_def(&source[open + 1..close]) {
                        Ok(def) => return def,
                        Err(error) => last_error = error.to_string(),
                    }
                }
            }
            search_from = macro_at + "language!".len();
        }
        panic!("bundled language {name} must reconstruct: {last_error}");
    }

    /// Every bundled standalone language definition — the PRODUCTION `language!` files under
    /// `languages/src` PLUS the non-production ones under `languages/tests/definitions`
    /// (`bench_common.rs` declares no language and the `composition/` / `rholang/`
    /// subdirectories hold fragments, not standalone definitions).
    ///
    /// Task #11 split the definitions by role: `languages/src/` is production-only, and every
    /// demonstration / fixture grammar is TEST-HOSTED (`options { hosted_in: … }`). Both roles
    /// are listed here, and that totality is the point — this table is what proves the
    /// binder-congruence disposition agrees with `rholang-codegen` for EVERY bundled language,
    /// so a definition dropping out of it would silently narrow the agreement proof.
    ///
    /// `include_str!` needs a LITERAL path, so the table cannot derive a definition's location
    /// from its own `hosted_in`; it is hand-maintained on purpose. The enforcement is that a
    /// definition which moves without its entry being updated fails the `macros` build
    /// immediately and by name — loud and unmissable, never silent drift.
    ///
    /// ⚠ THAT ENFORCEMENT ONLY CATCHES A MOVE, NEVER AN ADDITION. A definition that is simply
    /// never listed compiles fine and is silently outside every guard below — the table fails
    /// OPEN, reporting success over a shrinking domain as the language set grows. It did:
    /// `json`, `monoid`, `pi` and `turing` were added to `languages/src/` (production, per this
    /// comment's own claim) and never added here, so half the production corpus sat outside the
    /// three guards below — including `pi`, whose generated float handler carried an UNSOUND
    /// replication arm (`!(νx.P) ⟶ νx.!P`) that the guard asserting "Ambient is the ONLY
    /// float-bearing language" structurally could not see. The four are listed now.
    /// ⚠ The residual risk is unchanged in kind: this is still a hand-written mirror of two
    /// directory listings, and the next definition added to either can be omitted just as
    /// silently. The durable repair is to DERIVE the subject list (a `read_dir` completeness
    /// assertion against `languages/src` + `languages/tests/definitions`, which `include_str!`
    /// cannot do but a test can), not to maintain it.
    const BUNDLED_LANGUAGES: &[(&str, &str)] = &[
        (
            "acbagdemo",
            include_str!("../../../../languages/tests/definitions/acbagdemo.rs"),
        ),
        ("acdemo", include_str!("../../../../languages/tests/definitions/acdemo.rs")),
        ("ambdemo", include_str!("../../../../languages/tests/definitions/ambdemo.rs")),
        ("ambient", include_str!("../../../../languages/src/ambient.rs")),
        (
            "ambnewdemo",
            include_str!("../../../../languages/tests/definitions/ambnewdemo.rs"),
        ),
        ("appsubst", include_str!("../../../../languages/tests/definitions/appsubst.rs")),
        (
            "bicongdemo",
            include_str!("../../../../languages/tests/definitions/bicongdemo.rs"),
        ),
        ("calculator", include_str!("../../../../languages/src/calculator.rs")),
        (
            "class2hashmapsmoke",
            include_str!("../../../../languages/tests/definitions/class2hashmapsmoke.rs"),
        ),
        (
            "class2multi",
            include_str!("../../../../languages/tests/definitions/class2multi.rs"),
        ),
        (
            "class2optsmoke",
            include_str!("../../../../languages/tests/definitions/class2optsmoke.rs"),
        ),
        (
            "class2smoke",
            include_str!("../../../../languages/tests/definitions/class2smoke.rs"),
        ),
        (
            "class3multi",
            include_str!("../../../../languages/tests/definitions/class3multi.rs"),
        ),
        (
            "class3opt",
            include_str!("../../../../languages/tests/definitions/class3opt.rs"),
        ),
        ("commdemo", include_str!("../../../../languages/tests/definitions/commdemo.rs")),
        ("ctxdemo", include_str!("../../../../languages/tests/definitions/ctxdemo.rs")),
        (
            "fortran_model",
            include_str!("../../../../languages/tests/definitions/fortran_model.rs"),
        ),
        (
            "guarded_rho",
            include_str!("../../../../languages/tests/definitions/guarded_rho.rs"),
        ),
        (
            "guardoptsmoke",
            include_str!("../../../../languages/tests/definitions/guardoptsmoke.rs"),
        ),
        (
            "inoutdemo",
            include_str!("../../../../languages/tests/definitions/inoutdemo.rs"),
        ),
        ("json", include_str!("../../../../languages/src/json.rs")),
        (
            "lambdademo",
            include_str!("../../../../languages/tests/definitions/lambdademo.rs"),
        ),
        ("lambda", include_str!("../../../../languages/src/lambda.rs")),
        ("led_test", include_str!("../../../../languages/tests/definitions/led_test.rs")),
        ("monoid", include_str!("../../../../languages/src/monoid.rs")),
        (
            "nativedemo",
            include_str!("../../../../languages/tests/definitions/nativedemo.rs"),
        ),
        (
            "nativefolddemo",
            include_str!("../../../../languages/tests/definitions/nativefolddemo.rs"),
        ),
        ("nlacdemo", include_str!("../../../../languages/tests/definitions/nlacdemo.rs")),
        ("optsmoke", include_str!("../../../../languages/tests/definitions/optsmoke.rs")),
        ("pi", include_str!("../../../../languages/src/pi.rs")),
        (
            "refinementsmoke",
            include_str!("../../../../languages/tests/definitions/refinementsmoke.rs"),
        ),
        (
            "reserved_model",
            include_str!("../../../../languages/tests/definitions/reserved_model.rs"),
        ),
        ("rholang", include_str!("../../../../languages/src/rholang.rs")),
        ("swapdemo", include_str!("../../../../languages/tests/definitions/swapdemo.rs")),
        ("turing", include_str!("../../../../languages/src/turing.rs")),
    ];

    /// A-S5.4b CROSS-CRATE AGREEMENT (design v2 §3.2): for EVERY bundled language definition, the
    /// `rholang-codegen` restatement `language_has_float_handler` (the equations-gate recognizer's
    /// handler leg) must agree with this module's `should_emit_binder_congruence` (the emission
    /// disposition). This test lives in `macros` because only `macros` sees BOTH predicates; any
    /// drift in either crate's three conditions (equations non-empty / no `RhoNativeJoin`
    /// obligation / surface single binder) fails loudly, per language.
    #[test]
    fn language_has_float_handler_agrees_with_should_emit_binder_congruence() {
        for (name, source) in BUNDLED_LANGUAGES {
            let def = bundled_def(name, source);
            assert_eq!(
                should_emit_binder_congruence(&def),
                language_has_float_handler(&def),
                "cross-crate drift on {name}: macros should_emit_binder_congruence != \
                 rholang-codegen language_has_float_handler"
            );
        }
    }

    /// The bundled corpus fact the A-S5.4b admission rests on, restated over the COMPLETE corpus.
    /// TWO languages bear the host float handler (equations + host-less + surface single binder):
    /// the production Ambient and the production Pi. They are NOT interchangeable, and the
    /// difference is the point of A-S5.4b:
    ///
    /// * Ambient's equations are wholly float-discharged, so `equations_boundary_canonicalizable`
    ///   ADMITS it and the in-Rho lane installs the `^float` family for it;
    /// * Pi's are not — `RepUnfold . |- (PRep P) = (PPar {P, (PRep P)})` is a replication
    ///   unfolding, no kind of binder float — so the in-Rho lane correctly REFUSES Pi.
    ///
    /// ★ That refusal is what made the host-side defect visible: the two lanes disagreed about
    /// Pi, and the lane that derived from the DECLARATIONS was the one that was right. Pinning
    /// both dispositions here keeps the asymmetry deliberate instead of incidental.
    ///
    /// ⚠ Until this corpus was completed (the previous commit) this test asserted `["ambient"]`
    /// and passed — over a table that did not contain Pi. It is the expected-value list that is
    /// pinned here, deliberately, as a tripwire for a NEW float-bearing language; the SUBJECT
    /// list it ranges over is the thing that must never again be narrower than it claims.
    #[test]
    fn bundled_float_handler_languages_are_ambient_and_pi_with_only_ambient_canonicalizable() {
        let float_bearing: Vec<&str> = BUNDLED_LANGUAGES
            .iter()
            .filter(|(name, source)| should_emit_binder_congruence(&bundled_def(name, source)))
            .map(|(name, _)| *name)
            .collect();
        assert_eq!(
            float_bearing,
            ["ambient", "pi"],
            "the host float handler's bundled corpus is exactly the production Ambient and Pi"
        );
        let bundled = |wanted: &str| {
            BUNDLED_LANGUAGES
                .iter()
                .find(|(name, _)| *name == wanted)
                .map(|(name, source)| bundled_def(name, source))
                .unwrap_or_else(|| panic!("{wanted} is bundled"))
        };
        assert!(
            equations_boundary_canonicalizable(&bundled("ambient")),
            "the production Ambient's corrected equations are fully float-discharged"
        );
        assert!(
            !equations_boundary_canonicalizable(&bundled("pi")),
            "Pi's RepUnfold is not a binder float, so the in-Rho lane must refuse Pi — if this \
             ever admits, the ^float family would be installed for a language whose equational \
             theory it cannot discharge"
        );
    }

    /// ★★ A-S5.4c THE CONVERSE ADMISSION (module docs): for every bundled language that bears the
    /// handler, the generated float arms are EXACTLY the constructors its declared equations
    /// license — no constructor floated without an equation, and no declared float missing an arm.
    ///
    /// This is the direction nothing checked. `equations_boundary_canonicalizable` checks that
    /// every declared EQUATION is a recognized float; this checks that every emitted ARM is a
    /// declared equation. Pi failed it: `ScopeExt` licenses `PPar` and nothing else, yet the
    /// handler emitted prefix float arms for `POut` and for `PRep` — the latter being
    /// `!(νx.P) ⟶ νx.(!P)`, unsound in the π-calculus.
    ///
    /// The check reads the GENERATED ARTIFACT (the match-arm head `Cat :: Label (` in the emitted
    /// token stream) rather than re-running the generator's own arm selection, so it is a
    /// comparison of the code against the declaration and not a tautology.
    #[test]
    fn generated_float_arms_are_exactly_the_declared_float_equations() {
        for (name, source) in BUNDLED_LANGUAGES {
            let def = bundled_def(name, source);
            if !should_emit_binder_congruence(&def) {
                continue;
            }
            let primary = def
                .types
                .first()
                .expect("a float-handler language has a primary category")
                .name
                .to_string();
            let binder = surface_single_binder_label(&def)
                .expect("a float-handler language has a surface single binder")
                .to_string();
            let declared = float_satellite_table(&def);
            let tokens = generate_binder_congruence(&def).to_string();
            for rule in def.terms.iter().filter(|rule| rule.category == primary) {
                let label = rule.label.to_string();
                // The binder's own arm is the recursion/run-canonicalization arm, not a float
                // ACROSS a constructor; it is licensed by the handler existing at all.
                if label == binder {
                    continue;
                }
                let licensed = declared
                    .hoist
                    .iter()
                    .any(|(constructor, _, _)| *constructor == label)
                    || declared.merge_ops.contains(&label);
                // The emitted arm head, e.g. `Proc :: PRep (`. The trailing ` (` is load-bearing:
                // without it `PIn` would match inside `PInputs`.
                let emitted = tokens.contains(&format!("{primary} :: {label} ("));
                assert_eq!(
                    emitted,
                    licensed,
                    "{name}: {primary}::{label} — the generated float handler {} an arm for it, \
                     and the declared equations {} a float for it. A float arm with no equation \
                     is a congruence the language never authorised (A-S5.4c); a declared float \
                     with no arm is a normal form that misses redexes.",
                    if emitted { "HAS" } else { "has NO" },
                    if licensed { "DO declare" } else { "declare NO" },
                );
            }
        }
    }

    /// ★★ A-S5.4c, the π-calculus instance, stated as the smallest grammar that triggers it: a
    /// language declaring ONLY the `PPar` collection float (`ScopeExt`) must not get a float arm
    /// for its replication constructor. `PRep`'s arm is `!(νx.P) ⟶ νx.(!P)`, which does not hold
    /// in the π-calculus — the left creates a fresh name per replica, the right shares one name
    /// across all replicas — and it is not a capture-avoidance failure, so the A-S5.4a
    /// freshen-then-float argument cannot license it.
    ///
    /// The fixture is modelled on `languages/tests/definitions/refinementsmoke.rs` (a minimal
    /// synthetic grammar) but lives inline: it exists to be fed to `generate_binder_congruence`,
    /// never to be compiled as a language, so a file under `tests/definitions/` would add a
    /// `#[path]`-less orphan for no gain.
    #[test]
    fn rep_float_arm_is_not_emitted_without_a_declared_float_equation() {
        const REP_FLOAT_GATE: &str = r#"
            name: RepFloatGate,
            types { P Name },
            terms {
                PZero . P ::= "0" ;
                PRep . P ::= "!" P ;
                PNew . ^x.p:[Name -> P] |- "new" "(" x "," p ")" : P ;
                PPar . P ::= HashBag(P) sep "|" delim "{" "}" ;
            },
            equations {
                ScopeExt . | x # ...rest
                         |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
            },
            rewrites { }
        "#;
        let def = reconstruct_language_def(REP_FLOAT_GATE)
            .expect("the RepFloatGate fixture reconstructs");
        assert!(
            should_emit_binder_congruence(&def),
            "the fixture declares equations, is host-less and has a surface single binder, so it \
             does bear the handler — the arm set is what is under test, not the disposition"
        );
        let tokens = generate_binder_congruence(&def).to_string();
        assert!(
            !tokens.contains("PRep"),
            "A-S5.4c: RepFloatGate declares a float for PPar and for nothing else, so the \
             generated normal form must not float `new` out of PRep — `!(new x. P)` is NOT \
             `new x. !P` in the pi-calculus (fresh name per replica vs one name shared across \
             every replica), and freshening cannot repair it"
        );
        assert!(
            tokens.contains("P :: PPar ("),
            "the DECLARED float (ScopeExt over PPar) must still be emitted — the converse \
             admission restricts the arms to the declarations, it does not drop them"
        );
    }

    /// A-S5.4b BUILD CHECK (design v2 §3.4, inverted to unconditional-float-required): the
    /// equations-gate recognizer's soundness is VERSIONED on the A-S5.4a unconditional
    /// unbind-first float — a conditional (gated) float would re-open the refuted F1
    /// incompleteness, so the generated handler must carry NO `is_fresh` gate and must
    /// freshen-then-float through moniker `unbind`.
    ///
    /// ⚠ This ranged over Ambient alone and therefore inherited the corpus blind spot the
    /// previous commit closed — it would have said nothing about a second float-bearing language.
    /// It now ranges over every language that bears the handler, derived from the corpus rather
    /// than named. (A-S5.4c does not weaken what is asserted here: the float is still
    /// unconditional AT the sites the equations license; what changed is which sites those are.)
    #[test]
    fn generated_float_is_unconditional_no_is_fresh_gate() {
        let mut checked = 0usize;
        for (name, source) in BUNDLED_LANGUAGES {
            let def = bundled_def(name, source);
            if !should_emit_binder_congruence(&def) {
                continue;
            }
            checked += 1;
            let tokens = generate_binder_congruence(&def).to_string();
            assert!(
                !tokens.contains("is_fresh"),
                "A-S5.4a regression on {name}: the generated float must be UNCONDITIONAL (no \
                 is_fresh gate) — the A-S5.4b equations-gate admission is unsound over a \
                 conditional float"
            );
            assert!(
                tokens.contains("unbind"),
                "{name}: the unconditional float freshen-then-floats through moniker unbind"
            );
        }
        assert!(
            checked >= 2,
            "this check is only worth running over a corpus that actually contains float-handler \
             languages; {checked} were found, so it has gone vacuous again"
        );
    }
}
