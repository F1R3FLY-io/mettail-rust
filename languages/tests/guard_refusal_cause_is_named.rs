//! ★ **A refusal from the SURFACE lane names what stopped it.**
//!
//! ```text
//!  ┌──────────────────────────────────────────────────────────────────────────────────────┐
//!  │ THE DEFECT THIS FILE PINS                                                            │
//!  │   `eval_guard_disposition_via_substrate` turned every `Sat3::DontKnow` into a        │
//!  │   CAUSELESS `GuardDisposition::Declines`. Its twin over the lowered `Par` —          │
//!  │   `guard_par_substrate::substrate_guard_disposition`, which that module's own docs   │
//!  │   call *"the same shape as well as the same decider"* — had carried a                │
//!  │   `GuardRefusalCause` and a `RefusalProvenance` since `0f3d298c`. Two lanes that     │
//!  │   decide the same thing must not diverge in what they can EXPLAIN.                   │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ WHAT IS ASSERTED HERE                                                                │
//!  │   Not *that* a cause exists — **which** cause, for each of the three steps the two   │
//!  │   lanes share, plus the provenance each one computes and the class that follows.     │
//!  │   A test that only asserted "some cause" would pass against a decider that answered  │
//!  │   one collapsed symbol, which is the very thing being removed.                       │
//!  └──────────────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ⚠ **What this file does NOT assert, and why.** Two of the seven causes —
//! `GuardRefusalCause::EvaluationFailed` and `GuardRefusalCause::Malformed` — are
//! **unreachable on this lane**, so there is no honest way to show an assertion about them go
//! red. The lowered lane reads them off `rho_pure_eval`'s `EvalError`; this lane's delegated
//! deciders (`formula::host_matches_verdict`, `runtime::compare_collection_equality`) answer
//! `Option<bool>`, which has no error channel. `the_causes_this_lane_cannot_reach_are_absent`
//! measures that absence rather than leaving it to prose.

use std::sync::Arc;

use mettail_languages::rholang::guard_substrate::{
    encode_guard, eval_guard_disposition_via_substrate, surface_guard_disposition,
    SurfaceGuardDisposition,
};
use mettail_languages::rholang::receive::GuardDisposition;
use mettail_languages::rholang::{Bool, Int, Proc, Str};
use mettail_prattail::algebra_tower::Sat3;
use mettail_prattail::guard_refusal::{
    GuardRefusal, GuardRefusalCause, GuardRefusalClass, RefusalProvenance,
};
use mettail_runtime::{get_or_create_var, OrdVar, Var};

// ── Term builders ───────────────────────────────────────────────────────────────────────────

fn int(n: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(n)))
}

fn boolean(b: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(b)))
}

fn string(s: &str) -> Proc {
    Proc::CastStr(Arc::new(Str::StringLit(s.to_string())))
}

fn var(name: &str) -> Proc {
    Proc::PVar(OrdVar(Var::Free(get_or_create_var(name))))
}

fn arc(p: Proc) -> Arc<Proc> {
    Arc::new(p)
}

/// `"hi" matches {"hi" | true}` — the SEPARATING CONJUNCTION, whose associative-commutative-
/// with-remainder semantics belong to the reducer's own matcher. The surface lane delegates it
/// and the delegate declines, which is the one refusal this lane raises for a fragment that
/// genuinely IS a predicate.
fn separating_conjunction_guard() -> Proc {
    Proc::Matches(arc(string("hi")), arc(Proc::PParInfix(arc(string("hi")), arc(boolean(true)))))
}

/// The refusal a guard produced, or a panic naming what it produced instead.
///
/// Deliberately *not* an `Option`: every test below is about a guard that must not be decided,
/// so a decided guard is a failure of the premise and has to say so loudly.
fn refusal_of(written: &Proc, substituted: &Proc) -> GuardRefusal {
    match surface_guard_disposition(written, substituted) {
        SurfaceGuardDisposition::Undecided(refusal) => refusal,
        decided => panic!(
            "the guard was expected to produce NO VERDICT, so that the refusal could be \
             inspected; the decider answered {decided:?} instead"
        ),
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// STEP 1 — a binder the substitution could not reach
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **THE HEADLINE.** `where y == 2` with `y` unsubstituted is refused because a binder
/// survived — and the refusal now says so, and says WHICH slot.
///
/// The clause that produces it is step 1: `encoding.vars` is non-empty. Substitution has
/// already applied every binding the receive will ever get, so a surviving slot is one no
/// payload supplies — hence `Term`, hence `DeciderGap`.
#[test]
fn step_one_a_residual_binder_names_the_slot_the_substitution_could_not_reach() {
    let guard = Proc::Eq(arc(var("y")), arc(int(2)));

    // The premise: the encoder really did intern a binder, so step 1 is the clause under test
    // and not an accident of some other step firing first.
    let encoding = encode_guard(&guard);
    assert_eq!(
        encoding.vars.names().len(),
        1,
        "premise: `y == 2` must intern exactly one binder, got {:?}",
        encoding.vars.names()
    );

    let refusal = refusal_of(&guard, &guard);
    match &refusal.cause {
        GuardRefusalCause::ResidualBinder { slots } => {
            assert_eq!(slots.len(), 1, "one unreached binder, got {slots:?}");
            assert!(
                slots[0].starts_with("y$"),
                "the slot must be the binder's own canonical key (`name$unique_id`), got {:?}",
                slots[0]
            );
        },
        other => panic!(
            "a guard with an unsubstituted binder must be refused as \
             `ResidualBinder` — the clause is step 1, `encoding.vars` is non-empty — got {other:?}"
        ),
    }
    assert_eq!(
        refusal.provenance,
        RefusalProvenance::Term,
        "a slot no payload supplies is in the TERM: substitution has already applied every \
         binding this receive gets"
    );
    assert_eq!(refusal.class, GuardRefusalClass::DeciderGap);
    assert!(
        refusal
            .to_string()
            .contains("a binder the payload does not supply"),
        "the rendering must name the cause in the author's vocabulary, got {refusal}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// STEP 2 — a set-aside fragment the delegated decider could not answer
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The separating conjunction is a PREDICATE this lane has no procedure for — a coverage
/// fact, not a sort fact, and not a false guard.
///
/// The clause is step 2 at an `OpaquePosition::Predicate` fragment: `Proc::Matches` is a
/// verdict-producing arm, so the encoder set the fragment aside knowing a verdict was required,
/// and `formula::host_matches_verdict` then declined it.
#[test]
fn step_two_a_separating_conjunction_is_unsupported_rather_than_a_false_guard() {
    let guard = separating_conjunction_guard();
    let refusal = refusal_of(&guard, &guard);
    match &refusal.cause {
        GuardRefusalCause::Unsupported { nodes } => assert_eq!(
            nodes,
            &vec!["spatial match (`matches`)".to_string()],
            "the refusal must name the construct the decider had no arm for"
        ),
        other => panic!(
            "`t matches {{φ | ψ}}` must be refused as `Unsupported` — the host delegates the \
             separating conjunction and the delegate declined — got {other:?}"
        ),
    }
    assert_eq!(
        refusal.provenance,
        RefusalProvenance::Term,
        "the `matches` is in the guard as written, so every payload hits it"
    );
    assert_eq!(refusal.class, GuardRefusalClass::DeciderGap);
}

/// ★ A process in guard position was never a predicate — a SORT fact, and a different one from
/// the coverage fact above.
///
/// The clause is step 2 at an `OpaquePosition::NotAPredicate` fragment: `Proc::PZero` reaches
/// `Encoder::formula`'s `other` catch-all, which is by construction the complement of the
/// verdict-producing arms.
#[test]
fn step_two_a_process_in_guard_position_is_not_a_boolean() {
    let guard = Proc::PZero;
    let refusal = refusal_of(&guard, &guard);
    assert_eq!(
        refusal.cause,
        GuardRefusalCause::NotABoolean,
        "`where 0` is not a predicate under any payload — that is a fact about the guard's \
         SORT, and it must not be reported as a coverage gap"
    );
    assert_eq!(refusal.provenance, RefusalProvenance::Term);
    assert_eq!(refusal.class, GuardRefusalClass::DeciderGap);
}

/// ★ The two step-2 causes are genuinely DIFFERENT objects.
///
/// Asserting each in isolation would pass against a decider that answered one of them for
/// everything, which is exactly the collapse being removed.
#[test]
fn the_two_step_two_causes_are_not_the_same_object() {
    let coverage = refusal_of(&separating_conjunction_guard(), &separating_conjunction_guard());
    let sort = refusal_of(&Proc::PZero, &Proc::PZero);
    assert_ne!(
        coverage.cause, sort.cause,
        "a predicate the decider cannot answer and a term that is not a predicate are two \
         different facts with two different remedies"
    );
    assert_ne!(
        coverage.to_string(),
        sort.to_string(),
        "…and they must still be different after rendering, which is where a reader sees them"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// PROVENANCE — computed from the written guard, not tabulated
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ An obstruction the PAYLOAD carried in is data-dependent, not a decider gap.
///
/// `where x == 1` is a perfectly good guard: it is `Linear` and decides for every integer
/// payload. Under a payload that is a *process*, its image `0 == 1` sets a fragment aside that
/// the comparison encoder cannot represent. Refusing that loudly would refuse a guard that
/// works for every other datum — so the provenance is `Datum` and the class is
/// `DataDependent`, computed by asking the written guard the same question.
#[test]
fn a_payload_carried_obstruction_is_data_dependent_not_a_decider_gap() {
    let written = Proc::Eq(arc(var("x")), arc(int(1)));
    let substituted = Proc::Eq(arc(Proc::PZero), arc(int(1)));

    let refusal = refusal_of(&written, &substituted);
    assert_eq!(
        refusal.provenance,
        RefusalProvenance::Datum,
        "`x == 1` is decidable as written; only this payload's image is not, so the \
         obstruction came in with the datum. Got refusal: {refusal}"
    );
    assert_eq!(refusal.class, GuardRefusalClass::DataDependent);

    // ★ The control that makes the row above non-vacuous: the SAME image, presented as though
    // it were also what the author wrote, is a `Term` obstruction. So the `Datum` answer is
    // produced by consulting the written guard and not by the image alone.
    let as_written = refusal_of(&substituted, &substituted);
    assert_eq!(
        as_written.provenance,
        RefusalProvenance::Term,
        "with the obstruction present in the written guard, the same image must be a decider gap"
    );
    assert_eq!(as_written.class, GuardRefusalClass::DeciderGap);
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// THE INVARIANTS — a refusal exists exactly when there is no verdict
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// A guard that was evaluated and REFUTED carries no refusal at all. This is the other half of
/// the fix: `GuardRefusal` must not become a second name for "false".
#[test]
fn a_decided_guard_carries_no_refusal() {
    for (label, guard) in [
        ("true == false", Proc::Eq(arc(boolean(true)), arc(boolean(false)))),
        ("1 == 2", Proc::Eq(arc(int(1)), arc(int(2)))),
        ("1 == 1", Proc::Eq(arc(int(1)), arc(int(1)))),
        ("true", boolean(true)),
    ] {
        let disposition = surface_guard_disposition(&guard, &guard);
        assert!(
            disposition.refusal().is_none(),
            "{label} is DECIDED, so it must carry no refusal; got {disposition:?}"
        );
        assert_ne!(disposition.verdict(), Sat3::DontKnow, "{label}");
    }
}

/// ★ **No dual runtime paths.** `eval_guard_disposition_via_substrate` is a projection of
/// `surface_guard_disposition`, so the two can never answer different COMM verdicts. Pinned
/// over every shape this file exercises plus the decided controls.
#[test]
fn the_legacy_entry_point_is_a_projection_and_cannot_disagree() {
    let corpus: Vec<(&str, Proc)> = vec![
        ("residual binder", Proc::Eq(arc(var("y")), arc(int(2)))),
        ("separating conjunction", separating_conjunction_guard()),
        ("process in guard position", Proc::PZero),
        ("never a predicate", Proc::Add(arc(int(1)), arc(int(1)))),
        ("refuted", Proc::Eq(arc(int(1)), arc(int(2)))),
        ("admitted", Proc::Eq(arc(int(1)), arc(int(1)))),
        ("admitted literal", boolean(true)),
        ("refuted literal", boolean(false)),
        ("string equality", Proc::Eq(arc(string("hi")), arc(string("hi")))),
    ];
    for (label, guard) in &corpus {
        let expected = match surface_guard_disposition(guard, guard) {
            SurfaceGuardDisposition::Admits => GuardDisposition::Fires,
            SurfaceGuardDisposition::Refutes => GuardDisposition::Blocks,
            SurfaceGuardDisposition::Undecided(_) => GuardDisposition::Declines,
        };
        assert_eq!(
            eval_guard_disposition_via_substrate(guard),
            expected,
            "{label}: the projection must agree with the decider it projects"
        );
    }
}

/// ★ **THE HONEST NEGATIVE.** Two of the seven causes cannot be reached on this lane, and this
/// measures that rather than asserting it in prose.
///
/// `EvaluationFailed` and `Malformed` are read off an evaluator's *error channel*. This lane's
/// delegated deciders answer `Option<bool>`; there is no error channel to read, so nothing on
/// this lane ever *ran and failed*. If a delegate ever grows one, this test fails and the cause
/// mapping has to be extended rather than silently left collapsed.
#[test]
fn the_causes_this_lane_cannot_reach_are_absent() {
    let corpus: Vec<Proc> = vec![
        Proc::Eq(arc(var("y")), arc(int(2))),
        separating_conjunction_guard(),
        Proc::PZero,
        Proc::Add(arc(int(1)), arc(int(1))),
        Proc::Add(arc(var("y")), arc(int(1))),
        Proc::Mul(arc(var("y")), arc(var("z"))),
        Proc::Div(arc(int(6)), arc(int(0))),
        Proc::Eq(arc(Proc::Div(arc(int(6)), arc(int(0)))), arc(int(1))),
        Proc::Matches(arc(string("hi")), arc(string("bye"))),
        Proc::Eq(arc(Proc::PZero), arc(int(1))),
        Proc::Not(arc(Proc::PZero)),
        Proc::And(arc(Proc::PZero), arc(boolean(true))),
    ];
    for guard in &corpus {
        if let Some(refusal) = surface_guard_disposition(guard, guard).refusal() {
            assert!(
                !matches!(
                    refusal.cause,
                    GuardRefusalCause::EvaluationFailed { .. } | GuardRefusalCause::Malformed
                ),
                "this lane has no evaluator error channel, so it cannot honestly report \
                 {:?}. If a delegate grew one, map it deliberately instead of leaving this \
                 assertion to fail. Guard: {guard}",
                refusal.cause
            );
        }
    }
}
