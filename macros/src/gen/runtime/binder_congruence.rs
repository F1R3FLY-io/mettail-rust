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
//! `new` maximally outward. The former generated per-language `is_fresh` helper
//! was an uncalled public API after this change and has been retired (#95):
//! freshness is discharged by construction, not checked. FV:
//! `formal/rocq/rho_bridge/theories/BinderFloatCanonicalization.v`
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

/// ⚠ `pub(crate)` on a `#[cfg(test)]` module, deliberately.
///
/// [`tests::bundled_languages`] is THE corpus census — the one derivation of "every
/// `language!` body under the manifest-declared roots, reconstructed exactly as the
/// generator would see it". It was written here because this file needed it first; it is
/// not about binder congruence, and a second guard now reads it
/// (`dovetail_report::typed_report`'s fold-body gate).
///
/// Copying the walk into that module instead would recreate precisely the failure this
/// file's own header spends forty lines on: *"a walk written out `n` times is a walk that
/// can be widened `n − 1` times"* — the hand-written `BUNDLED_LANGUAGES` table failed OPEN
/// three times because more than one place decided what the corpus was. One census, read
/// by every guard that needs one.
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use mettail_ast::auto_inject::reconstruct_language_def_from_tokens;
    use mettail_ast::language_scan;
    use mettail_rholang_codegen::{
        equations_boundary_canonicalizable, language_has_float_handler, reconstruct_language_def,
    };
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};
    use syn::Item;

    // ══════════════════════════════════════════════════════════════════════════════
    // THE BUNDLED SUBJECT — derived from the corpus, never written down
    // ══════════════════════════════════════════════════════════════════════════════

    /// The workspace root, found by walking up to the `Cargo.toml` that declares
    /// `[workspace]` rather than by counting `..` segments from `CARGO_MANIFEST_DIR`.
    fn workspace_root() -> PathBuf {
        mettail_ast::manifest::find_workspace_root(Path::new(env!("CARGO_MANIFEST_DIR")))
            .expect("`macros` is a workspace member, so some ancestor declares [workspace]")
    }

    /// One `language!` body as the corpus holds it, before any decision about it.
    ///
    /// `tokens` is the macro's OWN token stream, taken from `syn`'s `ItemMacro`. It is not
    /// a slice of source text, and that distinction is the whole of §2 of this repair —
    /// see [`bundled_languages`].
    struct DeclaredBody {
        /// Repository-relative, `/`-separated: `languages/src/ambient.rs`.
        path: String,
        /// The declared `name:`, verbatim: `Ambient`, `X2Base`.
        name: String,
        /// The macro's own tokens — exactly what the compiler hands the proc-macro.
        tokens: TokenStream,
        /// The body AS WRITTEN: parsed, with neither composition nor auto-injection
        /// applied. An exemption row asserts over this, because for the exempt class it is
        /// the only form that exists outside the macro.
        parsed: LanguageDef,
    }

    /// Whether a body declares `extends` / `includes` / `mixins`.
    ///
    /// This is the ONE property that decides whether a declared language can be
    /// reconstructed outside the macro at all; see [`RECONSTRUCTION_EXEMPT`].
    fn is_composed(def: &LanguageDef) -> bool {
        !def.extends_names.is_empty()
            || !def.include_names.is_empty()
            || !def.mixin_names.is_empty()
    }

    /// Every item-level `language!` body in `items`, INCLUDING those inside inline
    /// `mod { … }` blocks.
    ///
    /// The inline recursion is load-bearing: `languages/tests/x2_lookahead_bracket_probe.rs`
    /// declares `X2Base`, `X2Look` and `X2Teeth`, one in each of three inline `pub mod`s. A
    /// NON-inline `#[path = "…"] mod` has `content == None` and contributes nothing here,
    /// which is correct — the declaration belongs to the file that spells it, and counting
    /// it twice would put one grammar in the subject under two paths.
    fn collect_bodies(items: &[Item], path: &str, out: &mut Vec<DeclaredBody>) {
        for item in items {
            match item {
                Item::Macro(item_macro) => {
                    if item_macro.mac.path.is_ident("language") {
                        let tokens = item_macro.mac.tokens.clone();
                        let parsed: LanguageDef = syn::parse2(tokens.clone()).unwrap_or_else(|e| {
                            panic!(
                                "{path}: a `language!` body does not parse as a LanguageDef: {e}"
                            )
                        });
                        out.push(DeclaredBody {
                            path: path.to_owned(),
                            name: parsed.name.to_string(),
                            tokens,
                            parsed,
                        });
                    }
                },
                Item::Mod(item_mod) => {
                    if let Some((_, nested)) = &item_mod.content {
                        collect_bodies(nested, path, out);
                    }
                },
                _ => {},
            }
        }
    }

    /// EVERY `language!` body declared under the manifest-declared language roots, sorted
    /// by `(path, name)`.
    ///
    /// # The floor, and why it is here rather than in each caller
    ///
    /// Every guard below has the shape "for every bundled language, P holds". A derivation
    /// that found NOTHING would satisfy all of them, silently and permanently — which is
    /// the precise failure mode the hand-written table had, only faster. The floor makes an
    /// empty or collapsed census a loud failure at the source, so no caller can inherit a
    /// vacuous subject. (Form borrowed from
    /// `rholang-runtime/tests/rholang_query_bind.rs::every_declared_query_bind_surface_is_covered_behaviourally`.)
    fn declared_bodies() -> Vec<DeclaredBody> {
        let root = workspace_root();
        let files = language_scan::language_files(&root).unwrap_or_else(|err| {
            panic!(
                "cannot determine the language definition roots: {err}\n\nThe bundled \
                 subject IS that scan, so it must not continue with a guess: an empty or \
                 narrowed root list would make every guard below pass over nothing."
            )
        });

        let mut bodies = Vec::new();
        for path in files {
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            // A declaration necessarily spells `language!` followed by a delimiter, so this
            // gate cannot hide one; it only spares `syn` the generated test hosts and
            // simulator binaries that the package-wide root also walks.
            if !language_scan::mentions_language_invocation(&source) {
                continue;
            }
            let file = syn::parse_file(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
            let relative = language_scan::repo_relative(&root, &path);
            collect_bodies(&file.items, &relative, &mut bodies);
        }

        bodies.sort_by(|a, b| (&a.path, &a.name).cmp(&(&b.path, &b.name)));
        assert!(
            bodies.len() >= 50,
            "the census found {} `language!` bodie(s) under the declared roots. The corpus \
             holds well over fifty, so the walk or the parse gate has changed shape and \
             every guard below would be reporting success over a domain that is not the \
             corpus — the exact failure the hand-written table exhibited three times.",
            bodies.len()
        );
        bodies
    }

    /// A bundled language: its location, its declared name, and the exact macro-time
    /// augmented definition the generator would see.
    pub(crate) struct BundledLanguage {
        pub(crate) path: String,
        pub(crate) name: String,
        pub(crate) def: LanguageDef,
    }

    /// ★★ EVERY bundled language definition, DERIVED from the corpus.
    ///
    /// # What this replaced
    ///
    /// A hand-written `const BUNDLED_LANGUAGES: &[(&str, &str)]` of `include_str!` rows —
    /// a mirror of two directory listings, maintained by hand, whose own header said it
    /// should not be one. Its argument for existing was that `include_str!` needs a LITERAL
    /// path, so a `const` cannot derive a definition's location from its own `hosted_in`.
    /// ★ That is true of a `const` and IRRELEVANT here: this table is `#[cfg(test)]`-only,
    /// it is never read by the generator, and a test function may call `std::fs::read_dir`
    /// — as `ast/tests/dovetail_language_inventory.rs` and `dovetail/tests/language_inventory.rs`
    /// already do. The only property `include_str!` bought was build-time MOVE detection,
    /// which is moot once there is no entry to keep in step.
    ///
    /// # The hazard it kept reproducing
    ///
    /// `include_str!` catches a MOVE and never an ADDITION. A definition that was simply
    /// never listed compiled fine and sat outside every guard the table fed, so the table
    /// reported success over a SHRINKING DOMAIN as the language set grew:
    ///
    /// | # | omitted | what it cost |
    /// |---|---|---|
    /// | 1 | `json`, `monoid`, `pi`, `turing` | `pi`'s generated float handler carried an UNSOUND replication arm (`!(νx.P) ⟶ νx.!P`); the guard asserting "Ambient is the ONLY float-bearing language" structurally could not see it |
    /// | 2 | `binder_law_demo`, `congruence_lane_demo`, `typed_drop_demo` | two of the three BEAR the handler, so the same guard again answered over a domain that did not contain the whole question |
    /// | 3 | `token_text_leaf_demo` (added in `53199ac4`) | RED at committed `HEAD` when this derivation was written: `ast/tests/language_name_keyed_artifacts.rs`'s completeness assertion was failing on it, before any widening |
    ///
    /// The lesson the second occurrence taught, in the old header's own words, is that
    /// **"complete the list" is not a repair — DERIVING the list is**. This is that
    /// derivation. It cannot omit a definition, because it never names one.
    ///
    /// # Two corrections to what the old header asserted
    ///
    /// 1. It excluded *"the `composition/` / `rholang/` subdirectories [which] hold
    ///    fragments, not standalone definitions"*. True of `rholang/` (zero declarations)
    ///    and of `bench_common.rs`; **false of `composition/`**, which holds FOUR
    ///    item-level `language!` bodies — `BaseMath`, `ExtMath`, `ImportedMath`,
    ///    `MixedMath`. The only written argument for the table being a subset rather than
    ///    the domain was a false statement of fact. `BaseMath` declares no composition
    ///    clause and is bundled like any other; the other three are the exemption below.
    /// 2. The domain was never two directories. It is the manifest-declared
    ///    `[package.metadata.mettail] language_roots`, walked recursively — the SAME walk
    ///    the three inventory audits use, shared as `mettail_ast::language_scan`.
    ///
    /// # Why the tokens, and not the source text
    ///
    /// The old extractor took `source.rfind('}')` as the macro's closing brace. That holds
    /// only when the `language!` is the LAST ITEM IN THE FILE — true of
    /// `languages/src/*.rs` and `languages/tests/definitions/*.rs`, and false of every one
    /// of the six top-level `languages/tests/*.rs` declarations, which continue with
    /// `#[test] fn …` afterwards. For those, every candidate slice ran past the body, the
    /// reconstruction failed on all of them, and the extractor reached a bare `panic!` —
    /// under the cranelift dev backend, the mute abort `dovetail/tests/panic_expectation_gate.rs`
    /// exists to keep out of this tree. Handing `syn` the macro's own `mac.tokens` cannot
    /// be handed the wrong bytes, and a failure is a `syn::Result` that NAMES the file.
    ///
    /// # Keyed by `(path, name)`, never by file stem
    ///
    /// The old map did `out.insert(stem, path)`, so a file declaring TWO languages yielded
    /// ONE entry — and the completeness check compared two counts that had been collapsed
    /// the same way, so it passed. Latent only while the scan could not reach a
    /// multi-declaration file; `languages/tests/x2_lookahead_bracket_probe.rs` holds three.
    ///
    /// # ⚠ The `__bcn_close_new_run_canonical` residual is NOT touched, and was checked
    ///
    /// The module header logs that the binder arm applies `NewComm` reordering whether or
    /// not the language declares that equation. Every body this widening newly covers has
    /// EMPTY or ABSENT `equations`, so [`should_emit_binder_congruence`] is `false` for
    /// every one of them, no handler is emitted, and none of them declares a float without
    /// a commutation. The residual therefore does not go live here; it stays exactly as
    /// logged, deliberately out of scope.
    pub(crate) fn bundled_languages() -> Vec<BundledLanguage> {
        let mut bundled = Vec::new();
        let mut failures = Vec::new();

        for body in declared_bodies() {
            if RECONSTRUCTION_EXEMPT
                .iter()
                .any(|row| row.path == body.path && row.name == body.name)
            {
                continue;
            }
            match reconstruct_language_def_from_tokens(body.tokens.clone()) {
                Ok(def) => bundled.push(BundledLanguage { path: body.path, name: body.name, def }),
                Err(error) => failures.push(format!("{} :: {} — {error}", body.path, body.name)),
            }
        }

        assert!(
            failures.is_empty(),
            "{} declared language(s) do not reconstruct, so the guards below would range \
             over a subset of the corpus without saying so:\n  {}\n\nEither the definition \
             is malformed, or it belongs to a class `ast/src/auto_inject` cannot rebuild \
             outside the macro — in which case give it a `RECONSTRUCTION_EXEMPT` row that \
             names the defect and its owner, never silence.",
            failures.len(),
            failures.join("\n  "),
        );
        assert!(
            bundled.len() >= 50,
            "only {} language(s) reconstructed; the subject has collapsed and every guard \
             below would be measuring a fragment of the corpus",
            bundled.len()
        );
        bundled
    }

    // ══════════════════════════════════════════════════════════════════════════════
    // The one class that cannot reconstruct — typed, owned, and asserted EXACTLY
    // ══════════════════════════════════════════════════════════════════════════════

    /// Why a declared language may be left out of the derived bundled subject.
    ///
    /// One variant, three inhabitants. A row is an OPEN DEFECT WITH AN OWNER, never a shrug
    /// and never a licence: the test below re-derives the exempt set from the corpus and
    /// asserts EQUALITY, and each row must still assert what IS true of the language it
    /// excuses. (Form: `languages/tests/literal_domain_agreement.rs::Exception`.)
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Why {
        /// ⚠ **OPEN DEFECT — owner: `ast/src/auto_inject.rs:122-124`.**
        ///
        /// `apply_extends` / `apply_includes` / `apply_mixins` resolve each base or
        /// fragment through `ast::registry::lookup_language_def`, which is the *macro-time*
        /// in-process registry. At reconstruction time that registry is empty, the lookup
        /// returns `None`, and all three turn that into an `Err` naming the base they could
        /// not find. So a composed language does not reconstruct to an EMPTY definition —
        /// it does not reconstruct at all.
        ///
        /// `auto_inject`'s own note states the remedy and its scope: *"Reconstructing a
        /// composed language exactly would require serializing the resolved base/fragment
        /// sources into the registry at runtime — that is a separate, later task."* Until
        /// that lands, asserting cross-crate agreement over these three would be a
        /// tautology about a language that does not exist outside the macro.
        CompositionNotResolvedAtReconstruction,
    }

    /// A declared language deliberately outside the derived bundled subject.
    struct Exempt {
        /// Repository-relative path of the declaring file.
        path: &'static str,
        /// The declared `name:`, verbatim.
        name: &'static str,
        /// The defect that makes the exemption necessary, and whose owner is named on it.
        why: Why,
    }

    /// The complete exemption set: the three COMPOSED languages, and nothing else.
    ///
    /// Asserted with `==` against the corpus, so it can neither grow silently nor rot once
    /// `auto_inject`'s "separate, later task" lands. `BaseMath` — in the same directory,
    /// and part of what the old header wrongly called "fragments, not standalone
    /// definitions" — declares no composition clause, reconstructs exactly, and is bundled.
    const RECONSTRUCTION_EXEMPT: &[Exempt] = &[
        Exempt {
            path: "languages/src/composition/extended_lang.rs",
            name: "ExtMath",
            why: Why::CompositionNotResolvedAtReconstruction,
        },
        Exempt {
            path: "languages/src/composition/grammar_import_lang.rs",
            name: "ImportedMath",
            why: Why::CompositionNotResolvedAtReconstruction,
        },
        Exempt {
            path: "languages/src/composition/mixed_lang.rs",
            name: "MixedMath",
            why: Why::CompositionNotResolvedAtReconstruction,
        },
    ];

    /// ★ The exemption set is EXACTLY the composed languages, and every row still asserts.
    ///
    /// Three things are checked, because a row that merely names a language is the shrug
    /// this whole repair exists to remove:
    ///
    /// 1. **Equality with the corpus.** The composed set is re-derived structurally on every
    ///    run. A row that stops being justified fails here; a new composed language must be
    ///    classified deliberately instead of inheriting an exemption.
    /// 2. **The defect is real, and is the one named.** The reconstruction must actually
    ///    FAIL, with a registry-lookup error. If it ever succeeds, `auto_inject`'s "separate,
    ///    later task" has landed and the row must be deleted so the derivation covers it.
    /// 3. **The exemption cannot be hiding a float-bearing language.** Over the body AS
    ///    WRITTEN — which is all that exists outside the macro — the equations are empty and
    ///    [`should_emit_binder_congruence`] is `false`. So excluding these three cannot
    ///    narrow the float-handler claim the guards below make, which is the exact way the
    ///    hand-written table went wrong three times.
    #[test]
    fn reconstruction_exemptions_are_exactly_the_composed_languages() {
        let bodies = declared_bodies();

        let composed: BTreeSet<(String, String)> = bodies
            .iter()
            .filter(|body| is_composed(&body.parsed))
            .map(|body| (body.path.clone(), body.name.clone()))
            .collect();
        let exempt: BTreeSet<(String, String)> = RECONSTRUCTION_EXEMPT
            .iter()
            .map(|row| (row.path.to_owned(), row.name.to_owned()))
            .collect();

        assert_eq!(
            exempt,
            composed,
            "`RECONSTRUCTION_EXEMPT` and the composed languages in the corpus have \
             diverged.\n  exempt but NOT composed: {:?}\n  composed but NOT exempt: {:?}\n\n\
             Composition is the ONLY sanctioned reason to leave a declared language out of \
             the derived subject (`ast/src/auto_inject.rs:122-124` owns the fix and calls \
             it a separate task). Anything else must be bundled — 'it is only a demo' is a \
             criterion this corpus has already refuted, since `binder_law_demo` and \
             `typed_drop_demo` are demonstration grammars that DO bear the float handler.",
            exempt.difference(&composed).collect::<Vec<_>>(),
            composed.difference(&exempt).collect::<Vec<_>>(),
        );
        assert!(
            !composed.is_empty(),
            "no composed language was found, so the equality above compared two empty sets"
        );

        for row in RECONSTRUCTION_EXEMPT {
            let body = bodies
                .iter()
                .find(|body| body.path == row.path && body.name == row.name)
                .unwrap_or_else(|| {
                    panic!(
                        "`RECONSTRUCTION_EXEMPT` names {} :: {}, which the corpus scan does \
                         not find. A row for a language that is not there excuses nothing \
                         and hides the next real one.",
                        row.path, row.name
                    )
                });

            match row.why {
                Why::CompositionNotResolvedAtReconstruction => {
                    assert!(
                        is_composed(&body.parsed),
                        "{} :: {} is exempted as a composed language but declares no \
                         `extends`/`includes`/`mixins`",
                        row.path,
                        row.name
                    );

                    let error = reconstruct_language_def_from_tokens(body.tokens.clone())
                        .err()
                        .unwrap_or_else(|| {
                            panic!(
                                "{} :: {} now RECONSTRUCTS. The composed-language defect \
                                 this row records has been fixed — delete the row so the \
                                 derived subject covers it, and check whether \
                                 `ast/src/auto_inject.rs:122-124`'s note can go with it.",
                                row.path, row.name
                            )
                        })
                        .to_string();
                    assert!(
                        error.contains("not found in registry"),
                        "{} :: {} fails to reconstruct, but not for the reason this row \
                         claims. The exemption is for an unresolved composition clause; \
                         this error is something else and must be diagnosed rather than \
                         absorbed:\n  {error}",
                        row.path,
                        row.name
                    );

                    assert!(
                        body.parsed.equations.is_empty(),
                        "{} :: {} is exempted from the bundled subject but declares \
                         equations, so the float-handler disposition over it is NOT \
                         vacuous and the exemption would be narrowing a claim the guards \
                         below make",
                        row.path,
                        row.name
                    );
                    assert!(
                        !should_emit_binder_congruence(&body.parsed),
                        "{} :: {} is exempted from the bundled subject but BEARS the float \
                         handler as written. Excluding it narrows exactly the claim the \
                         hand-written table narrowed three times; reconstruct it instead.",
                        row.path,
                        row.name
                    );
                },
            }
        }
    }

    /// ★ The derived subject accounts for the WHOLE corpus: every declared `language!` body
    /// is either BUNDLED or EXEMPT, never neither and never both.
    ///
    /// This is the property the hand-written table could not state. A list can only be
    /// checked against the corpus by a SECOND thing that enumerates the corpus — which is
    /// why the repair took three attempts and a separate guard in another crate. Here the
    /// subject IS the enumeration, so the partition is checkable in one place: a language
    /// that silently dropped out would have to drop out of `declared_bodies` itself, and the
    /// floor there makes that loud.
    ///
    /// It also reports the census, which is the number every guard below ranges over.
    #[test]
    fn every_declared_language_is_either_bundled_or_exempt() {
        let declared: BTreeSet<(String, String)> = declared_bodies()
            .iter()
            .map(|body| (body.path.clone(), body.name.clone()))
            .collect();
        let bundled: BTreeSet<(String, String)> = bundled_languages()
            .iter()
            .map(|language| (language.path.clone(), language.name.clone()))
            .collect();
        let exempt: BTreeSet<(String, String)> = RECONSTRUCTION_EXEMPT
            .iter()
            .map(|row| (row.path.to_owned(), row.name.to_owned()))
            .collect();

        assert!(
            bundled.is_disjoint(&exempt),
            "language(s) are both bundled and exempt, so the exemption is not excluding what \
             it claims to: {:?}",
            bundled.intersection(&exempt).collect::<Vec<_>>()
        );
        let covered: BTreeSet<(String, String)> = bundled.union(&exempt).cloned().collect();
        assert_eq!(
            covered,
            declared,
            "the derived subject does not partition the corpus.\n  declared but NEITHER \
             bundled nor exempt: {:?}\n  covered but not declared: {:?}",
            declared.difference(&covered).collect::<Vec<_>>(),
            covered.difference(&declared).collect::<Vec<_>>(),
        );

        eprintln!(
            "note: the derived bundled subject is {} language(s); {} declared, {} exempt \
             (composed).",
            bundled.len(),
            declared.len(),
            exempt.len(),
        );
    }

    /// A-S5.4b CROSS-CRATE AGREEMENT (design v2 §3.2): for EVERY bundled language definition, the
    /// `rholang-codegen` restatement `language_has_float_handler` (the equations-gate recognizer's
    /// handler leg) must agree with this module's `should_emit_binder_congruence` (the emission
    /// disposition). This test lives in `macros` because only `macros` sees BOTH predicates; any
    /// drift in either crate's three conditions (equations non-empty / no `RhoNativeJoin`
    /// obligation / surface single binder) fails loudly, per language.
    #[test]
    fn language_has_float_handler_agrees_with_should_emit_binder_congruence() {
        for language in bundled_languages() {
            assert_eq!(
                should_emit_binder_congruence(&language.def),
                language_has_float_handler(&language.def),
                "cross-crate drift on {} :: {}: macros should_emit_binder_congruence != \
                 rholang-codegen language_has_float_handler",
                language.path,
                language.name,
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
    /// ⚠ Until this corpus was completed (`359220f3`) this test asserted `["ambient"]` and passed
    /// — over a table that did not contain Pi. It is the expected-value list that is pinned here,
    /// deliberately, as a tripwire for a NEW float-bearing language; the SUBJECT list it ranges
    /// over is the thing that must never again be narrower than it claims.
    ///
    /// ⚠⚠ IT HAPPENED A SECOND TIME, and this is the record of it. The completion in `359220f3`
    /// added the four PRODUCTION grammars (`json`, `monoid`, `pi`, `turing`) and stopped there;
    /// three TEST-HOSTED definitions — `binder_law_demo`, `congruence_lane_demo` and
    /// `typed_drop_demo` — were still absent, so this test again asserted a two-element answer
    /// over a domain that did not contain the whole question. Two of the three bear the handler.
    /// They were surfaced by `ast/tests/language_name_keyed_artifacts.rs`, the `read_dir`
    /// completeness assertion the corpus note above asks for, which now fails whenever a
    /// definition file declares a `language!` and is not listed. The lesson the second
    /// occurrence teaches, which the first did not, is that "complete the list" is not a repair
    /// — DERIVING the list is; the note's own prescription was right and had simply not been
    /// carried out.
    ///
    /// # Why the demonstration grammars bear it, and why that is not a defect
    ///
    /// `BinderLawDemo` and `TypedDropDemo` are Task #94 declination demonstrations. Each declares
    /// `Nu . ^x.body:[Term -> Term]` — a surface single binder over the primary category — plus
    /// non-empty equations and no `RhoNativeJoin` obligation, which are exactly the three
    /// conditions of [`should_emit_binder_congruence`]. So the handler is emitted, correctly.
    /// Their equations (`PairComm`, `FreshSwap`) are NOT float laws — the binder sits at the root
    /// of neither side — so [`equations_boundary_canonicalizable`] REFUSES both, exactly as it
    /// refuses Pi, and no `^float` family is installed for a theory it cannot discharge. The
    /// converse admission below independently confirms the emitted arm set is empty for them.
    /// `CongruenceLaneDemo`, the third newly-listed definition, does not bear the handler at all.
    ///
    /// The claim this test defends is therefore split in two, because the two halves have
    /// different lifetimes: the PRODUCTION claim (Ambient and Pi and nothing else) is a
    /// statement about the shipped language set and must stay exact; the corpus-wide list is a
    /// tripwire over everything bundled, demonstrations included.
    ///
    /// ★ THE SUBJECT IS NOW DERIVED, so the third recurrence cannot happen: this ranges over
    /// [`bundled_languages`], which enumerates the corpus rather than reading a list. Two
    /// consequences, both deliberate:
    ///
    /// * The expected set is compared as a `BTreeSet`, not an ordered `Vec`. The old order
    ///   (`ambient`, `binder_law_demo`, `typed_drop_demo`, `pi`) was an artifact of WHERE the
    ///   three late rows happened to be pasted into the table — never a property of anything —
    ///   and a derived subject sorts by path. Dropping an asserted property is a DIVERGENCE and
    ///   is recorded as one; what is asserted instead is exactly the claim with content.
    /// * The identity is `path :: Name`, the declared name rather than the file stem. The two
    ///   diverge for four definitions (`fortran_model`/`FortranModel`, `guarded_rho`/`GuardedRho`,
    ///   `led_test`/`LedTest`, `reserved_model`/`ReservedModel`) and a stem cannot address
    ///   `languages/tests/x2_lookahead_bracket_probe.rs` at all, which declares three languages.
    #[test]
    fn bundled_float_handler_languages_are_ambient_and_pi_with_only_ambient_canonicalizable() {
        let bundled = bundled_languages();
        let float_bearing: BTreeSet<String> = bundled
            .iter()
            .filter(|language| should_emit_binder_congruence(&language.def))
            .map(|language| format!("{} :: {}", language.path, language.name))
            .collect();
        let expected: BTreeSet<String> = [
            "languages/src/ambient.rs :: Ambient",
            "languages/src/pi.rs :: Pi",
            "languages/tests/definitions/binder_law_demo.rs :: BinderLawDemo",
            "languages/tests/definitions/typed_drop_demo.rs :: TypedDropDemo",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        assert_eq!(
            float_bearing, expected,
            "the host float handler's bundled corpus is exactly the production Ambient and Pi \
             plus the two Task #94 declination demonstrations, each of which declares a surface \
             single binder over its primary category alongside non-empty equations"
        );

        // The PRODUCTION half, stated separately so it stays exact as demonstration grammars
        // come and go. `languages/src/` is the shipped set; `languages/tests/definitions/` is not.
        const PRODUCTION_FLOAT_BEARING: &[&str] = &["Ambient", "Pi"];
        const DEMONSTRATION_FLOAT_BEARING: &[&str] = &["BinderLawDemo", "TypedDropDemo"];
        for language in bundled
            .iter()
            .filter(|language| should_emit_binder_congruence(&language.def))
        {
            let name = language.name.as_str();
            assert!(
                PRODUCTION_FLOAT_BEARING.contains(&name)
                    || DEMONSTRATION_FLOAT_BEARING.contains(&name),
                "`{name}` ({}) bears the host float handler and is in neither the production nor \
                 the demonstration list; classify it deliberately rather than letting the set drift",
                language.path,
            );
        }

        let by_name = |wanted: &str| -> &LanguageDef {
            &bundled
                .iter()
                .find(|language| language.name == wanted)
                .unwrap_or_else(|| panic!("{wanted} is bundled"))
                .def
        };
        assert!(
            equations_boundary_canonicalizable(by_name("Ambient")),
            "the production Ambient's corrected equations are fully float-discharged"
        );
        assert!(
            !equations_boundary_canonicalizable(by_name("Pi")),
            "Pi's RepUnfold is not a binder float, so the in-Rho lane must refuse Pi — if this \
             ever admits, the ^float family would be installed for a language whose equational \
             theory it cannot discharge"
        );
        for demo in DEMONSTRATION_FLOAT_BEARING {
            assert!(
                !equations_boundary_canonicalizable(by_name(demo)),
                "`{demo}`'s equations put the binder at the root of neither side, so they are \
                 not float laws and the in-Rho lane must refuse it exactly as it refuses Pi — if \
                 this ever admits, the ^float family would be installed over a theory it cannot \
                 discharge, which is the Pi defect recurring under a different name"
            );
        }
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
        for language in bundled_languages() {
            let name = format!("{} :: {}", language.path, language.name);
            let def = language.def;
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
        for language in bundled_languages() {
            let name = format!("{} :: {}", language.path, language.name);
            let def = language.def;
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
