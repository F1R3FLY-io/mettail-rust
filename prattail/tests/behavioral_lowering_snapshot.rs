//! OSLF Phase 9 `.0`-inert — the carrier→decider canonical-lowering snapshot.
//!
//! Proves the parity-safe FOUNDATION that reconciles the two behavioral-
//! predicate representations in this crate:
//!
//! - the runtime CARRIER `mettail_prattail::behavioral_pred::BehavioralPred`
//!   (produced by the WPDA walker; the `runtime` crate re-exports it and
//!   evaluates it via `evaluate_pred_with_bindings`), and
//! - the DECIDER `mettail_prattail::behavioral_algebra::BehavioralFormula`
//!   (the `algebra_tower`-backed relational classifier).
//!
//! `BehavioralPred::to_behavioral_formula` lowers the carrier into the decider's
//! RELATIONAL fragment. This test exercises a corpus covering EVERY carrier
//! variant and asserts:
//!
//! 1. **tier-equivalence** — `behavioral_tier()` is `Some(T1)` iff the pred is
//!    exactly `Top`, `None` iff the pred contains an `AcMatch` anywhere, else
//!    `Some(T2)`. The image is the relational fragment only, so `T3` is never
//!    produced (the load-bearing parity fact).
//! 2. **H1** — a `negated: true` `RelationQuery` lowers to an outer
//!    `Not(Relation)`.
//! 3. **H5** — `Top` lowers to `BehavioralFormula::Top` (NOT a relation atom).
//! 4. **H6** — `AcMatch` (and any pred containing it) lowers to `None`.
//! 5. **eval-agreement** — on the literal/relational subset (no H2 domain
//!    gaps), the decider's `BehavioralAlgebra::<NoTerm>::evaluate` of the lowered
//!    formula agrees with the runtime carrier evaluator
//!    `evaluate_pred_with_bindings`.
//!
//! The whole file is feature-gated: it contributes ZERO tests to the default
//! build (keeping `cargo nextest run -p prattail` byte-identical), and runs only
//! under `--features oslf-behavioral-lowering`.
#![cfg(feature = "oslf-behavioral-lowering")]

use std::collections::{HashMap, HashSet};

use mettail_prattail::algebra_tower::RejectSafeAlgebra;
use mettail_prattail::behavioral_algebra::{
    Arg, BehavioralAlgebra, BehavioralFormula, BehavioralWorld, FactBase, NoTerm,
};
use mettail_prattail::behavioral_pred::{BehavioralPred, PredArg, QuantifiedDomain, Quantifier};
use mettail_prattail::symbolic::DecidabilityTier;

// The runtime carrier evaluator + its thread-local fact snapshot, reached
// through the runtime re-export (dev-dependency cycle; see `prattail/Cargo.toml`).
use mettail_runtime::{
    clear_pred_fact_snapshot, evaluate_pred_with_bindings, set_pred_fact_snapshot,
};

// ── carrier constructors (terse) ──────────────────────────────────────────

fn pvar(v: &str) -> PredArg {
    PredArg::Var(v.to_string())
}
fn pint(n: i64) -> PredArg {
    PredArg::IntLit(n)
}
fn pstr(s: &str) -> PredArg {
    PredArg::StringLit(s.to_string())
}
fn rel(name: &str, args: Vec<PredArg>, negated: bool) -> BehavioralPred {
    BehavioralPred::RelationQuery {
        relation_name: name.to_string(),
        args,
        negated,
    }
}

// ══════════════════════════════════════════════════════════════════════════
// The corpus: every BehavioralPred variant.
//
// `contains_ac` is the ground truth for the H6/tier-equivalence assertions:
// the lowering returns `None` iff an `AcMatch` appears anywhere in the tree.
// ══════════════════════════════════════════════════════════════════════════

struct Case {
    name: &'static str,
    pred: BehavioralPred,
    contains_ac: bool,
}

fn corpus() -> Vec<Case> {
    use BehavioralPred::*;
    let c = |name, pred, contains_ac| Case { name, pred, contains_ac };

    let ac = || AcMatch {
        bag: pvar("bag"),
        elements: vec![pvar("e1"), pvar("e2")],
        rest: Some("rest".to_string()),
    };

    vec![
        // ── RelationQuery, both polarities, all arg kinds ──
        c("rel_pos_literal", rel("halts", vec![pstr("p")], false), false),
        c("rel_pos_int", rel("at_step", vec![pint(7)], false), false),
        c("rel_pos_var", rel("safe", vec![pvar("x")], false), false),
        c("rel_neg_literal", rel("halts", vec![pstr("q")], true), false),
        c("rel_neg_var", rel("blocked", vec![pvar("x")], true), false),
        c("rel_mixed_args", rel("edge", vec![pvar("x"), pint(3), pstr("c")], false), false),
        // ── Top ──
        c("top", Top, false),
        // ── Quantified × {ForAll, Exists} × {Named, Bounded, Enumerated, None} ──
        c(
            "forall_named",
            Quantified {
                quantifier: Quantifier::ForAll,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Named("nodes".to_string())),
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "exists_named",
            Quantified {
                quantifier: Quantifier::Exists,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Named("nodes".to_string())),
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "forall_bounded",
            Quantified {
                quantifier: Quantifier::ForAll,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Bounded(16)),
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "exists_bounded",
            Quantified {
                quantifier: Quantifier::Exists,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Bounded(16)),
                body: Box::new(rel("reaches", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "forall_enumerated",
            Quantified {
                quantifier: Quantifier::ForAll,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Enumerated(vec![pstr("a"), pstr("b")])),
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "exists_enumerated",
            Quantified {
                quantifier: Quantifier::Exists,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Enumerated(vec![pstr("a"), pstr("b")])),
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        c(
            "exists_none",
            Quantified {
                quantifier: Quantifier::Exists,
                var: "y".to_string(),
                domain: None,
                body: Box::new(rel("safe", vec![pvar("y")], false)),
            },
            false,
        ),
        // ── Boolean combinators over relational atoms ──
        c(
            "and",
            And(
                Box::new(rel("halts", vec![pvar("x")], false)),
                Box::new(rel("safe", vec![pvar("x")], false)),
            ),
            false,
        ),
        c(
            "or",
            Or(
                Box::new(rel("halts", vec![pvar("x")], false)),
                Box::new(rel("safe", vec![pvar("x")], false)),
            ),
            false,
        ),
        c("not", Not(Box::new(rel("halts", vec![pvar("x")], false))), false),
        c(
            "implies",
            Implies(
                Box::new(rel("halts", vec![pvar("x")], false)),
                Box::new(rel("safe", vec![pvar("x")], false)),
            ),
            false,
        ),
        // ── AcMatch (structural leg) and combinators that CONTAIN it ──
        c("ac_match", ac(), true),
        c(
            "and_with_ac_left",
            And(Box::new(ac()), Box::new(rel("safe", vec![pvar("x")], false))),
            true,
        ),
        c(
            "or_with_ac_right",
            Or(Box::new(rel("safe", vec![pvar("x")], false)), Box::new(ac())),
            true,
        ),
        c("not_ac", Not(Box::new(ac())), true),
        c(
            "implies_ac_consequent",
            Implies(Box::new(rel("safe", vec![pvar("x")], false)), Box::new(ac())),
            true,
        ),
        c(
            "forall_body_ac",
            Quantified {
                quantifier: Quantifier::ForAll,
                var: "y".to_string(),
                domain: Some(QuantifiedDomain::Named("nodes".to_string())),
                body: Box::new(ac()),
            },
            true,
        ),
    ]
}

// ══════════════════════════════════════════════════════════════════════════
// 1. tier-equivalence (+ implicit "never T3").
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn tier_equivalence_over_corpus() {
    for case in corpus() {
        let tier = case.pred.behavioral_tier();
        let expected = if case.contains_ac {
            None
        } else if matches!(case.pred, BehavioralPred::Top) {
            Some(DecidabilityTier::CompileTimeDecidable)
        } else {
            Some(DecidabilityTier::RuntimeDecidable)
        };
        assert_eq!(
            tier,
            expected,
            "tier mismatch for `{}`: lowered={:?}",
            case.name,
            case.pred.to_behavioral_formula()
        );
        // The load-bearing parity fact: the relational image is NEVER modal, so
        // the tier is never T3 (SemiDecidable) and never T4 (Undecidable).
        assert_ne!(
            tier,
            Some(DecidabilityTier::SemiDecidable),
            "`{}` lowered to a T3 (modal) tier — parity invariant violated",
            case.name
        );
        assert_ne!(
            tier,
            Some(DecidabilityTier::Undecidable),
            "`{}` lowered to a T4 tier — parity invariant violated",
            case.name
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 2. H1 — negated RelationQuery → outer Not(Relation).
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn h1_negated_relation_wraps_in_not() {
    let p = rel("halts", vec![pvar("x"), pint(3)], true);
    match p.to_behavioral_formula() {
        Some(BehavioralFormula::Not(inner)) => match *inner {
            BehavioralFormula::Relation { name, args } => {
                assert_eq!(name, "halts");
                assert_eq!(args, vec![Arg::Var("x".to_string()), Arg::Lit("3".to_string())]);
            },
            other => panic!("H1: inner of Not is not a Relation: {other:?}"),
        },
        other => panic!("H1: negated RelationQuery did not lower to Not(Relation): {other:?}"),
    }

    // And the positive twin lowers to a BARE Relation (no Not).
    let pos = rel("halts", vec![pvar("x"), pint(3)], false);
    assert!(matches!(pos.to_behavioral_formula(), Some(BehavioralFormula::Relation { .. })));
}

// ══════════════════════════════════════════════════════════════════════════
// 3. H5 — Top → BehavioralFormula::Top (NOT a relation atom).
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn h5_top_lowers_to_formula_top() {
    assert_eq!(BehavioralPred::Top.to_behavioral_formula(), Some(BehavioralFormula::Top));
    // Explicitly NOT the syn-twin's `"true"`/`"__top__"` relation encoding.
    assert!(!matches!(
        BehavioralPred::Top.to_behavioral_formula(),
        Some(BehavioralFormula::Relation { .. })
    ));
    // ⊤ is T1.
    assert_eq!(
        BehavioralPred::Top.behavioral_tier(),
        Some(DecidabilityTier::CompileTimeDecidable)
    );
}

// ══════════════════════════════════════════════════════════════════════════
// 4. H6 — AcMatch (and anything containing it) → None.
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn h6_ac_match_lowers_to_none() {
    for case in corpus() {
        if case.contains_ac {
            assert_eq!(
                case.pred.to_behavioral_formula(),
                None,
                "H6: `{}` contains AcMatch but did not lower to None",
                case.name
            );
            assert_eq!(
                case.pred.behavioral_tier(),
                None,
                "H6: `{}` contains AcMatch but behavioral_tier is not None",
                case.name
            );
        } else {
            assert!(
                case.pred.to_behavioral_formula().is_some(),
                "`{}` is AcMatch-free but lowered to None",
                case.name
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 5. eval-agreement on the literal/relational subset.
//
// For each case below the decider (BehavioralAlgebra over a FactBase) and the
// runtime carrier evaluator (evaluate_pred_with_bindings over the thread-local
// snapshot) are given the SAME facts and bindings, and must agree. We restrict
// to the subset with NO H2 domain gaps:
//   - relational atoms with literal/bound-var args, and
//   - Top, And, Or, Not, Implies over those, and
//   - quantifiers over a LITERAL Enumerated domain only (Named/Bounded/None
//     inference are the deferred eval-path increment, excluded here).
// ══════════════════════════════════════════════════════════════════════════

/// Seed both fact stores identically and return the decider algebra.
fn seed(facts: &[(&str, Vec<&str>)]) -> BehavioralAlgebra<NoTerm> {
    let mut fb = FactBase::new();
    let mut snap: HashMap<String, HashSet<Vec<String>>> = HashMap::new();
    for (name, tuple) in facts {
        let owned: Vec<String> = tuple.iter().map(|s| s.to_string()).collect();
        fb.add_fact(*name, owned.clone());
        snap.entry((*name).to_string()).or_default().insert(owned);
    }
    set_pred_fact_snapshot(snap);
    BehavioralAlgebra::<NoTerm>::new(fb)
}

/// Assert decider(lowered p) == runtime(p) under the given env/bindings.
fn assert_eval_agrees(
    alg: &BehavioralAlgebra<NoTerm>,
    p: &BehavioralPred,
    bindings: &[(String, String)],
    label: &str,
) {
    let lowered = p
        .to_behavioral_formula()
        .unwrap_or_else(|| panic!("eval-agreement `{label}`: pred did not lower"));
    let env = bindings.iter().cloned().collect();
    let world = BehavioralWorld::with_env(NoTerm, env);
    let decider = alg.evaluate(&lowered, &world);
    let runtime = evaluate_pred_with_bindings(p, bindings);
    assert_eq!(
        decider, runtime,
        "eval-agreement `{label}`: decider={decider} runtime={runtime}; lowered={lowered:?}"
    );
}

#[test]
fn eval_agreement_relational_subset() {
    // Facts: halts(p), safe(p); deliberately NO halts(q)/safe(q).
    let alg = seed(&[("halts", vec!["p"]), ("safe", vec!["p"])]);
    let bind = |pairs: &[(&str, &str)]| -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    };

    // Top — both true unconditionally.
    assert_eval_agrees(&alg, &BehavioralPred::Top, &[], "top");

    // Positive literal hit / miss.
    assert_eval_agrees(&alg, &rel("halts", vec![pstr("p")], false), &[], "halts(p)_hit");
    assert_eval_agrees(&alg, &rel("halts", vec![pstr("q")], false), &[], "halts(q)_miss");

    // Negated literal: miss ⇒ true, hit ⇒ false.
    assert_eval_agrees(&alg, &rel("halts", vec![pstr("q")], true), &[], "not_halts(q)");
    assert_eval_agrees(&alg, &rel("halts", vec![pstr("p")], true), &[], "not_halts(p)");

    // Bound-var relation (var resolved identically by both sides).
    let bx = bind(&[("x", "p")]);
    assert_eval_agrees(&alg, &rel("safe", vec![pvar("x")], false), &bx, "safe(x=p)_hit");
    let bx2 = bind(&[("x", "q")]);
    assert_eval_agrees(&alg, &rel("safe", vec![pvar("x")], false), &bx2, "safe(x=q)_miss");

    // And / Or / Implies / Not over bound-var atoms.
    let and = BehavioralPred::And(
        Box::new(rel("halts", vec![pvar("x")], false)),
        Box::new(rel("safe", vec![pvar("x")], false)),
    );
    assert_eval_agrees(&alg, &and, &bx, "and(x=p)_both_hit");
    assert_eval_agrees(&alg, &and, &bx2, "and(x=q)_both_miss");

    let or = BehavioralPred::Or(
        Box::new(rel("halts", vec![pvar("x")], false)),
        Box::new(rel("nope", vec![pvar("x")], false)),
    );
    assert_eval_agrees(&alg, &or, &bx, "or(x=p)_left_hit");

    let implies = BehavioralPred::Implies(
        Box::new(rel("halts", vec![pvar("x")], false)),
        Box::new(rel("safe", vec![pvar("x")], false)),
    );
    assert_eval_agrees(&alg, &implies, &bx, "implies(x=p)_true_true");
    assert_eval_agrees(&alg, &implies, &bx2, "implies(x=q)_false_antecedent");

    let not = BehavioralPred::Not(Box::new(rel("halts", vec![pvar("x")], false)));
    assert_eval_agrees(&alg, &not, &bx, "not_halts(x=p)");
    assert_eval_agrees(&alg, &not, &bx2, "not_halts(x=q)");

    clear_pred_fact_snapshot();
}

#[test]
fn eval_agreement_literal_enumerated_quantifiers() {
    // The H2-gap-free quantifier subset: a LITERAL Enumerated domain. Both
    // evaluators iterate the same ground value list {a, b}.
    let alg = seed(&[("safe", vec!["a"]), ("safe", vec!["b"])]);

    // ∀ y ∈ {a, b}. safe(y) — true (both a and b are safe).
    let forall_true = BehavioralPred::Quantified {
        quantifier: Quantifier::ForAll,
        var: "y".to_string(),
        domain: Some(QuantifiedDomain::Enumerated(vec![pstr("a"), pstr("b")])),
        body: Box::new(rel("safe", vec![pvar("y")], false)),
    };
    assert_eval_agrees(&alg, &forall_true, &[], "forall_enum_all_safe");

    // ∀ y ∈ {a, c}. safe(y) — false (c is not safe).
    let forall_false = BehavioralPred::Quantified {
        quantifier: Quantifier::ForAll,
        var: "y".to_string(),
        domain: Some(QuantifiedDomain::Enumerated(vec![pstr("a"), pstr("c")])),
        body: Box::new(rel("safe", vec![pvar("y")], false)),
    };
    assert_eval_agrees(&alg, &forall_false, &[], "forall_enum_one_unsafe");

    // ∃ y ∈ {c, b}. safe(y) — true (b is safe).
    let exists_true = BehavioralPred::Quantified {
        quantifier: Quantifier::Exists,
        var: "y".to_string(),
        domain: Some(QuantifiedDomain::Enumerated(vec![pstr("c"), pstr("b")])),
        body: Box::new(rel("safe", vec![pvar("y")], false)),
    };
    assert_eval_agrees(&alg, &exists_true, &[], "exists_enum_one_safe");

    // ∃ y ∈ {c, d}. safe(y) — false (neither safe).
    let exists_false = BehavioralPred::Quantified {
        quantifier: Quantifier::Exists,
        var: "y".to_string(),
        domain: Some(QuantifiedDomain::Enumerated(vec![pstr("c"), pstr("d")])),
        body: Box::new(rel("safe", vec![pvar("y")], false)),
    };
    assert_eval_agrees(&alg, &exists_false, &[], "exists_enum_none_safe");

    clear_pred_fact_snapshot();
}
