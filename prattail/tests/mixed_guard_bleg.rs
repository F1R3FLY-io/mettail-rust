//! OSLF Phase 3 — the *production* mixed-guard B-leg composes.
//!
//! The `algebra_tower` unit tests exercise [`RejectSafeProduct`] with a
//! test-local `TriAlg` mock as the behavioral leg. This integration test
//! instantiates the product with the **real** behavioral algebra —
//! `BehavioralAlgebra<NoTerm>` — as the reject-safe `B`, paired with a classical
//! structural leg `Classical<IntervalAlgebra>`. It proves the production B-leg
//! type composes and that the reject-safe asymmetry (exact structural ∧
//! reject-safe behavioral) holds end-to-end. `RhoGuardedCommSoundness.v` /
//! `BehavioralNegation.v` are the Coq image of exactly this construction.

use mettail_prattail::algebra_tower::{
    Classical, MixedPred, RejectSafeAlgebra, RejectSafeProduct, Sat3,
};
use mettail_prattail::behavioral_algebra::{
    ActionPattern, Arg, BehavioralAlgebra, BehavioralFormula, BehavioralWorld, FactBase, NoTerm,
};
use mettail_prattail::symbolic::{IntervalAlgebra, IntervalPred};

type StructuralLeg = Classical<IntervalAlgebra>;
type BehavioralLeg = BehavioralAlgebra<NoTerm>;
type MixedGuard = RejectSafeProduct<StructuralLeg, BehavioralLeg>;

fn facts() -> FactBase {
    let mut f = FactBase::new();
    f.add_fact("halts", vec!["p".into()]);
    f
}

/// The production mixed guard: a classical structural interval leg × the real
/// reject-safe behavioral algebra.
fn mixed() -> MixedGuard {
    RejectSafeProduct::new(
        Classical::new(IntervalAlgebra::new(0, 100)),
        BehavioralAlgebra::<NoTerm>::new(facts()),
    )
}

fn world() -> BehavioralWorld<NoTerm> {
    BehavioralWorld::new(NoTerm)
}

#[test]
fn production_bleg_relational_is_exact() {
    let p = mixed();
    // structural [0,50) ∧ behavioral halts(p) — a relational behavioral leg is
    // exact (closed-world over the snapshot): Sat through the product.
    let halts =
        BehavioralFormula::Relation { name: "halts".into(), args: vec![Arg::Lit("p".into())] };
    let g = MixedPred(vec![(IntervalPred::Range(0, 50), halts)]);
    assert_eq!(p.is_satisfiable_3v(&g), Sat3::Sat);
    // Fires iff BOTH legs hold: 25 ∈ [0,50) ∧ halts(p) ⇒ fire; 75 ∉ [0,50) ⇒ no.
    assert!(p.evaluate(&g, &(25, world())));
    assert!(!p.evaluate(&g, &(75, world())));
    // A relational behavioral leg Unsat over the snapshot ⇒ Unsat product.
    let diverges =
        BehavioralFormula::Relation { name: "halts".into(), args: vec![Arg::Lit("q".into())] };
    let g2 = MixedPred(vec![(IntervalPred::Range(0, 50), diverges)]);
    assert_eq!(p.is_satisfiable_3v(&g2), Sat3::Unsat);
    assert!(!p.evaluate(&g2, &(25, world())));
}

#[test]
fn production_bleg_modal_is_dontknow_rejectsafe() {
    let p = mixed();
    // A MODAL behavioral leg is only semi-decidable: is_satisfiable_3v ⇒ DontKnow,
    // which propagates through the product (Kleene OR over rectangles). The guard
    // never fires on a DontKnow leg ⇒ reject-safe (never wrongly admits a Comm).
    let modal =
        BehavioralFormula::Diamond(ActionPattern::Any, Box::new(BehavioralFormula::Atom("done".into())));
    let g = MixedPred(vec![(IntervalPred::Range(0, 50), modal)]);
    assert_eq!(p.is_satisfiable_3v(&g), Sat3::DontKnow);
    // NoTerm has no transitions, so ⟨-⟩done is false there ⇒ no fire (and never a
    // wrong accept).
    assert!(!p.evaluate(&g, &(25, world())));
}

#[test]
fn production_bleg_negation_is_reject_safe() {
    // mixed_negation_soundness (BehavioralNegation.v) with the REAL behavioral
    // leg: wherever the asymmetric De Morgan complement fires, the guard
    // genuinely rejects — so a guarded receive never wrongly admits a Comm.
    let p = mixed();
    let halts =
        BehavioralFormula::Relation { name: "halts".into(), args: vec![Arg::Lit("p".into())] };
    let g = MixedPred(vec![(IntervalPred::Range(10, 60), halts)]);
    let pc = p.pseudo_complement(&g);
    for x in [0i64, 5, 10, 30, 59, 60, 80, 99] {
        let d = (x, world());
        if p.evaluate(&pc, &d) {
            assert!(
                !p.evaluate(&g, &d),
                "complement fired at x={x} but guard also accepts — NOT reject-safe"
            );
        }
    }
}
