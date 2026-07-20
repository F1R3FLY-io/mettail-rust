//! Inc 1 / A-S5.4a — Ambient binder-congruence direct-evaluator validation.
//!
//! The handler floats `new`s outward (capture-safe via moniker
//! `unbind`/`Scope::new`). A-S5.4a (design v2 §3.2): the float is
//! UNCONDITIONAL — freshen-then-float, never gated. The pre-A-S5.4a `is_fresh`
//! gates (checked against the ORIGINAL binder — the retired FIX-B discipline)
//! made the NF hint-sensitive and non-maximal (the F1 stall, pinned positively
//! below); capture-safety now rests entirely on `unbind`'s process-global
//! gensym: the freshened binder cannot occur free in any pre-existing
//! sibling/field, so re-closing captures nothing (α is definitional identity in
//! Cardelli–Gordon — `ma_theory_alignment.md`; FV:
//! `BinderFloatCanonicalization.v`). AM-2: at the bag extrusion seam a
//! bag-bodied `new` SPLICES its opened members (flat, never a nested bag
//! element). These tests exercise the evaluator through the real seam
//! (`Language::try_direct_eval`) and pin the two mandatory A-S5.4a subjects
//! structurally (`BoundTerm::term_eq` — never pretty-string goldens; AM-6c).
#![cfg(feature = "ambient")]

use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::Language;

/// Float a source term through the handler; `Some(display)` iff it made progress.
fn float(src: &str) -> Option<String> {
    let lang = AmbientLanguage;
    let term = lang.parse_term(src).expect("Ambient term parses");
    lang.try_direct_eval(term.as_ref()).map(|t| format!("{t}"))
}

#[test]
fn prefix_float_does_not_capture_a_shared_name() {
    // The load-bearing capture-safety test. Construct `open(x, new(x, 0))` where
    // the channel name and the `new`'s binder SHARE one `FreeVar` identity — the
    // situation a prior rewrite/substitution can produce (the parser keeps
    // binders fresh, so this cannot be reached by parsing alone). A naïve float
    // (`run_ascent`'s `from_parts_unsafe`, no re-close) would move the channel
    // `x` under `new^x` and CAPTURE it. A-S5.4a: the handler now ALWAYS floats
    // (the pre-A-S5.4a gate stalled this subject instead) via moniker
    // `unbind`→`Scope::new` (capture-avoiding alpha-renaming): the binder is
    // freshened to `x'`, so the channel `x` stays FREE in the result — the
    // assertion survives the gate removal because it pins exactly the
    // freshen-then-float capture-safety, not the stall.
    use mettail_languages::ambient::{Name, Proc};
    use mettail_runtime::{Binder, BoundTerm, FreeVar, OrdVar, Scope, Var};
    use std::sync::Arc;

    let x = FreeVar::fresh(Some("x".to_string()));
    let channel = Arc::new(Name::NVar(OrdVar(Var::Free(x.clone()))));
    let new_x = Proc::PNew(Scope::new(Binder(x.clone()), Arc::new(Proc::PZero)));
    let term = Proc::POpen(channel, Arc::new(new_x));

    let floated = term.binder_congruence_nf();
    let free = BoundTerm::free_vars(&floated);
    assert!(
        free.contains(&x),
        "the channel `x` must remain FREE after the float (no capture); \
         got free_vars {free:?} for {floated}"
    );
}

#[test]
fn floats_prefix_when_binder_fresh_in_name() {
    // `open(a, new(x, 0))`: floats to `new(x', open(a, 0))`. Progress ⇒ Some.
    // (A-S5.4a: the float is unconditional — this subject floated before the
    // gate removal too, since x was fresh in `a`; the name records the historic
    // gated scenario, the behavior is now unconditional.)
    assert!(float("open(a, new(x, 0))").is_some(), "a prefix-enclosed `new` floats out");
}

#[test]
fn floats_prefix_in_new() {
    // `in(n, new(x, 0))` ⇒ `new(x, in(n, 0))` (InNew), n ≠ x.
    assert!(float("in(n, new(x, 0))").is_some(), "InNew floats");
}

#[test]
fn capturing_witness_in_z_new_x_does_not_capture() {
    // `new(z, in(z, new(x, 0)))`: the inner `new(x,0)` floats out of `in(z, ·)`
    // (A-S5.4a: unconditionally — freshen-then-float). Re-closing recomputes
    // de-Bruijn coordinates locally, so the channel `z` stays bound to the OUTER
    // `new(z, ·)` — NOT captured. The handler must produce a result, and it must
    // round-trip (parse back) to a well-formed term.
    let lang = AmbientLanguage;
    let term = lang.parse_term("new(z, in(z, new(x, 0)))").expect("parses");
    let floated = lang
        .try_direct_eval(term.as_ref())
        .expect("the inner new floats out of the in-prefix");
    let displayed = format!("{floated}");
    // The result must re-parse (well-formed) — a captured term would still parse,
    // but the round-trip confirms the handler produced valid syntax.
    lang.parse_term(&displayed)
        .unwrap_or_else(|e| panic!("floated term must re-parse: {displayed:?}: {e}"));
}

#[test]
fn handler_is_deterministic() {
    // The same source floated twice must yield byte-identical output (no
    // transient `unique_id` leaks into the result — re-close erases the freshened
    // binder identity from the alpha-canonical key, and Display is name-stable).
    let a = float("new(z, in(z, new(x, 0)))");
    let b = float("new(z, in(z, new(x, 0)))");
    assert_eq!(a, b, "handler output must be deterministic");
}

#[test]
fn ground_term_does_not_float() {
    // A term with no floatable `new` redex makes no progress ⇒ None (fail-closed
    // preserved for the seam — the no-`new` case is unchanged by A-S5.4a).
    assert_eq!(float("0"), None);
    assert_eq!(float("{ open(n, 0) | n [ 0 ] }"), None, "no `new` ⇒ no float");
}

#[test]
fn f1_subject_floats_and_exposes_the_in_redex_structure() {
    // A-S5.4a mandatory pin (a) — the F1 counterexample subject (design v2 §3.1,
    // probe P1): `{ new(x, n[{in(m, 0)}]) | m[x[0]] }`, where the free `x` in the
    // SIBLING member shares the binder's FreeVar identity. Pre-A-S5.4a the
    // `is_fresh` residual gate STALLED the extrusion (x free in the residual), so
    // the In-redex existed modulo ≡ but was syntactically ABSENT — the refuted
    // `float_nf_exposes_redexes` counterexample. Post-fix the float extrudes
    // with an α-freshened binder and the canonical NF exposes the In-redex
    // structure `{ n[{in(m,·), …}], m[·], … }` under the binder prefix; the
    // original `x` stays FREE (no capture). Pinned STRUCTURALLY via
    // `BoundTerm::term_eq` (α-aware, multiset bags) — never a pretty-string
    // golden (AM-6c: post-float NFs can carry hint-colliding bound names).
    use mettail_languages::ambient::{Name, Proc};
    use mettail_runtime::{Binder, BoundTerm, FreeVar, OrdVar, Scope, Var};
    use std::sync::Arc;

    let x = FreeVar::fresh(Some("x".to_string()));
    let n = FreeVar::fresh(Some("n".to_string()));
    let m = FreeVar::fresh(Some("m".to_string()));
    let name =
        |v: &FreeVar<String>| Arc::new(Name::NVar(OrdVar(Var::Free(v.clone()))));

    // member 1: new(x, n[{ in(m, 0) }])
    let in_m = Proc::PIn(name(&m), Arc::new(Proc::PZero));
    let amb_n = Proc::PAmb(
        name(&n),
        Arc::new(Proc::PPar(std::iter::once(in_m.clone()).collect())),
    );
    let member1 = Proc::PNew(Scope::new(Binder(x.clone()), Arc::new(amb_n.clone())));
    // member 2: m[ x[0] ] — the free x that stalled the conditional float (F1).
    let amb_x = Proc::PAmb(name(&x), Arc::new(Proc::PZero));
    let member2 = Proc::PAmb(name(&m), Arc::new(amb_x));
    let subject = Proc::PPar([member1, member2.clone()].into_iter().collect());

    let nf = subject.binder_congruence_nf();

    // The canonical NF: the binder floats to the root (α-freshened — the binder
    // identity is erased by α-aware term_eq, so ANY fresh binder witnesses it)
    // and the In-redex structure is syntactically present in the bag under it.
    let w = FreeVar::fresh(Some("w".to_string()));
    let expected = Proc::PNew(Scope::new(
        Binder(w),
        Arc::new(Proc::PPar([amb_n, member2].into_iter().collect())),
    ));
    assert!(
        BoundTerm::term_eq(&nf, &expected),
        "the F1 subject must float to the In-redex-exposing canonical NF; got {nf}"
    );
    // No capture: the original free `x` survives free (unbind freshened the
    // binder away from it).
    let free = BoundTerm::free_vars(&nf);
    assert!(
        free.contains(&x),
        "the sibling's `x` must remain FREE after the unconditional float; \
         got free_vars {free:?} for {nf}"
    );
}

#[test]
fn am2_bag_bodied_new_floats_to_a_flat_bag() {
    // A-S5.4a mandatory pin (b) — the AM-2 bag-bodied-ν subject:
    // `{ new(x, { n[{in(m,0)}] | q }) | m[0] }`. Gate-drop alone would extrude
    // the opened BAG body as ONE nested element `{ {n[{in(m,0)}] | q} | m[0] }`
    // — C-G dissolves that nesting by (Struct Par Assoc), which mettail absorbs
    // only REPRESENTATIONALLY, so nothing on the host path would ever flatten it
    // and the In-redex would stay hidden from its sibling `m[0]`. The AM-2
    // splice (the generated `insert_into_ppar` auto-flatten, the host mirror of
    // `add_flattened_bag`) makes the extrusion seam produce a FLAT bag exposing
    // the redex. Pinned structurally (term_eq + an explicit no-nested-bag scan).
    use mettail_languages::ambient::{Name, Proc};
    use mettail_runtime::{Binder, BoundTerm, FreeVar, OrdVar, Scope, Var};
    use std::sync::Arc;

    let x = FreeVar::fresh(Some("x".to_string()));
    let n = FreeVar::fresh(Some("n".to_string()));
    let m = FreeVar::fresh(Some("m".to_string()));
    let q = FreeVar::fresh(Some("q".to_string()));
    let name =
        |v: &FreeVar<String>| Arc::new(Name::NVar(OrdVar(Var::Free(v.clone()))));

    // member 1: new(x, { n[{in(m,0)}] | q }) — the ν body is ITSELF a PPar bag.
    let in_m = Proc::PIn(name(&m), Arc::new(Proc::PZero));
    let amb_n = Proc::PAmb(
        name(&n),
        Arc::new(Proc::PPar(std::iter::once(in_m).collect())),
    );
    let q_var = Proc::PVar(OrdVar(Var::Free(q.clone())));
    let nu_body = Proc::PPar([amb_n.clone(), q_var.clone()].into_iter().collect());
    let member1 = Proc::PNew(Scope::new(Binder(x.clone()), Arc::new(nu_body)));
    // member 2: m[0] — the sibling the In-redex needs.
    let member2 = Proc::PAmb(name(&m), Arc::new(Proc::PZero));
    let subject = Proc::PPar([member1, member2.clone()].into_iter().collect());

    let nf = subject.binder_congruence_nf();

    // The canonical NF: new(w, { n[{in(m,0)}] | q | m[0] }) — a FLAT 3-member
    // bag (the opened bag body SPLICED), never `{ {n[…]|q} | m[0] }`.
    let w = FreeVar::fresh(Some("w".to_string()));
    let expected = Proc::PNew(Scope::new(
        Binder(w),
        Arc::new(Proc::PPar([amb_n, q_var, member2].into_iter().collect())),
    ));
    assert!(
        BoundTerm::term_eq(&nf, &expected),
        "the bag-bodied ν must splice to the flat In-redex-exposing NF; got {nf}"
    );
    // The flatness obligation, asserted explicitly: no member of the floated bag
    // is itself a PPar (a nested bag element would hide the redex).
    let Proc::PNew(scope) = &nf else {
        panic!("the NF root must be the floated binder, got {nf}");
    };
    let (_, opened) = scope.clone().unbind();
    let Proc::PPar(bag) = opened.as_ref() else {
        panic!("the floated body must be the widened bag, got {opened}");
    };
    let mut member_count = 0usize;
    for (member, count) in bag.iter() {
        member_count += count;
        assert!(
            !matches!(member, Proc::PPar(_)),
            "AM-2 flatness violated: the extrusion seam produced a nested bag \
             element {member} inside {opened}"
        );
    }
    assert_eq!(member_count, 3, "the flat bag carries exactly the three members");
}
