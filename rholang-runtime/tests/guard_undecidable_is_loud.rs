//! **The substrate lane: a `where` guard that cannot be DECIDED stops saying "false".**
//!
//! This is the third lane of a defect already fixed twice — the host lane (`c61995c1`, where
//! `eval_guard_bool`'s `Option<bool>` became `GuardDisposition::{Fires, Blocks, Declines}`) and
//! the machine lane (`eaa44c2f` + `6ab1c78b` in f1r3node, where an undecidable guard is refused
//! before any matcher is consulted). The residue is
//! [`mettail_rholang_runtime::guard_par_substrate`]: `Sat3::DontKnow` was mapped to `false` by
//! `dont_know_policy` **with no signal at all**.
//!
//! # The measured dose-response, before anything was written
//!
//! ```text
//!   guard                                fired  resting  error
//!   x > 0                                [5]    []       —
//!   x > 100                              []     [5]      —
//!   x + 1                                []     [5]      —        ← SILENT
//!   [1, 2]                               []     [5]      —        ← SILENT
//!   x                                    []     [5]      —        ← SILENT
//!   "nope"                               []     [5]      —        ← SILENT
//!   6 / (x - 5) > 1                      []     [5]      —        ← SILENT
//!   x.toByteArray() == x.toByteArray()   []     []       (refused by the MACHINE lane's gate)
//! ```
//!
//! The last row is the control: `6ab1c78b`'s gate is live in this tree, and it pre-empts exactly
//! the subset `rho_pure_eval` calls `UnsupportedExpression`. Every row above it is the substrate
//! lane's **own** `DontKnow`, and every one of them was silent.
//!
//! # The separation this file exists to pin
//!
//! One datum, three guards, three *observably different* outcomes:
//!
//! ```text
//!   guard TRUE        → no error, COMM FIRES
//!   guard FALSE       → no error, rests
//!   guard UNDECIDABLE → error raised, rests    ← must differ from the row above
//! ```
//!
//! Without the third row being observably different from the second, the fix has not landed.
//!
//! # ⚠ Anti-vacuity
//!
//! Every check below either drives a real reduction through
//! [`SubstrateGuardMatcher`](mettail_rholang_runtime::guard_par_substrate::SubstrateGuardMatcher)
//! or calls the classifier on a real `Par`. §1's primary assertion was watched RED against the
//! pre-fix tree and failed with
//! *"★ THE DEFECT: an UNDECIDABLE guard produced no error"* — after the two rows above it had
//! already passed, so the harness was demonstrably live when it rejected.

#![cfg(feature = "source-oracle")]

use std::collections::HashMap;

use mettail_rholang_runtime::guard_par_substrate::{
    substrate_guard_disposition, substrate_guard_passes, GuardRefusalCause, GuardRefusalClass,
    GuardRefusalLedger, RefusalProvenance, SubstrateGuardDisposition, SubstrateGuardMatcher,
};
use mettail_rholang_runtime::{
    run_rholang_source_and_read_ints_with_guard_refusals,
    run_rholang_source_sequence_for_oracle_and_read_ints,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{EPlus, Expr, Par, Send, Var};

// ════════════════════════════════════════════════════════════════════════════════════════════
// The one program, parameterised by its guard
// ════════════════════════════════════════════════════════════════════════════════════════════

/// One datum (`5` on `@"c"`), one guarded receive, one observation channel.
///
/// `OUT` non-empty ⟺ the COMM fired. `c` non-empty ⟺ the datum is still resting.
fn program(guard: &str) -> String {
    format!(r#"for (@x <- @"c" where {guard}) {{ @"OUT"!(x) }} | @"c"!(5)"#)
}

/// What the program did, as a user of the runtime observes it.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    /// The refusals the run reported — the *loudness* column.
    refusals: Vec<String>,
    /// The values left on `OUT` — non-empty ⟺ the COMM fired.
    fired: Vec<i64>,
    /// The values left on `c` — non-empty ⟺ the datum is still resting.
    resting: Vec<i64>,
}

fn take(observed: &HashMap<String, Vec<i64>>, channel: &str) -> Vec<i64> {
    let mut values = observed.get(channel).cloned().unwrap_or_default();
    values.sort_unstable();
    values
}

/// Run one guard through mettail's runtime — the one that installs `SubstrateGuardMatcher` at
/// `RSpace::create` — and report all three columns *independently*.
///
/// The tuplespace and the refusals are read separately on purpose: rows 2 and 3 of the
/// separation leave the **identical** space, so only the third column can tell them apart.
async fn run_guard(guard: &str) -> Outcome {
    let source = program(guard);
    let (observed, refusals) =
        run_rholang_source_and_read_ints_with_guard_refusals(&source, &["OUT", "c"])
            .await
            .unwrap_or_else(|error| panic!("guard {guard:?} failed to run: {error}"));
    Outcome {
        refusals,
        fired: take(&observed, "OUT"),
        resting: take(&observed, "c"),
    }
}

/// The same program through the ORDINARY entry point, which turns a decider gap into the run's
/// `Err`. `Ok(())` ⟺ nothing was refused.
async fn run_guard_plainly(guard: &str) -> Result<(), String> {
    let source = program(guard);
    run_rholang_source_sequence_for_oracle_and_read_ints(&[&source], &["OUT"])
        .await
        .map(|_| ())
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §1 — ★ THE SEPARATION. One datum, three guards, three distinguishable outcomes.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **THE PRIMARY ASSERTION OF THIS FILE**, and the one watched RED.
///
/// The third row must be *observably* different from the second. Before the fix it was not:
/// both rested silently, and a user had nothing in the program's output to tell "the guard was
/// false" from "the guard could not be decided".
#[tokio::test]
async fn a_true_a_false_and_an_undecidable_guard_are_three_different_observations() {
    let fires = run_guard("x > 0").await;
    let rests = run_guard("x > 100").await;
    let undecidable = run_guard("x + 1").await;

    println!("\n★ THE SEPARATION — one datum (5 on @\"c\"), one guarded receive\n");
    for (label, outcome) in [
        ("TRUE  x > 0", &fires),
        ("FALSE x > 100", &rests),
        ("UNDEC x + 1", &undecidable),
    ] {
        println!(
            "  {label:<14} fired={:<6} resting={:<6} refusals={}",
            format!("{:?}", outcome.fired),
            format!("{:?}", outcome.resting),
            outcome.refusals.len()
        );
    }
    println!();

    // ── Row 1: TRUE — no refusal, the COMM fires, nothing is left resting. ────────────────
    assert!(fires.refusals.is_empty(), "a TRUE guard must not be refused");
    assert_eq!(fires.fired, vec![5], "a TRUE guard must fire the COMM");
    assert_eq!(fires.resting, Vec::<i64>::new(), "a fired COMM consumes the datum");

    // ── Row 2: FALSE — no refusal, no COMM, the datum rests and stays observable. ─────────
    assert!(rests.refusals.is_empty(), "a FALSE guard must not be refused");
    assert_eq!(rests.fired, Vec::<i64>::new(), "a FALSE guard must not fire the COMM");
    assert_eq!(rests.resting, vec![5], "a FALSE guard leaves the datum resting");

    // ── Row 3: UNDECIDABLE — ★ refused, AND the datum still rests. ────────────────────────
    //
    // `x + 1` is not a predicate at all: it evaluates cleanly to an integer, so nothing in
    // `rho_pure_eval`'s undecidable class (`UnsupportedExpression`) covers it and the machine
    // lane's gate lets it through. The substrate then answers `Sat3::DontKnow` — and used to
    // spell that `false`.
    assert!(
        !undecidable.refusals.is_empty(),
        "★ THE DEFECT: an UNDECIDABLE guard produced no refusal — it is indistinguishable from \
         the FALSE row above. fired={:?} resting={:?}",
        undecidable.fired,
        undecidable.resting
    );
    assert_eq!(
        undecidable.fired,
        Vec::<i64>::new(),
        "loud is not permissive: an undecidable guard must still not fire the COMM"
    );
    assert_eq!(
        undecidable.resting,
        vec![5],
        "★ the refusal must not roll the reduction back — the datum the guard declined to \
         consume is still resting, exactly as in the FALSE row"
    );

    // ── And the three rows are pairwise distinguishable. ─────────────────────────────────
    assert_ne!(rests, undecidable, "★ FALSE and UNDECIDABLE must not be the same observation");
    assert_ne!(fires, rests, "TRUE and FALSE must not be the same observation");
    assert_ne!(fires, undecidable, "TRUE and UNDECIDABLE must not be the same observation");
}

/// The same separation through the ORDINARY entry point, where a decider gap is the run's `Err`.
///
/// This is the column an author actually reads: they do not call the refusal-reporting variant,
/// they run their program.
#[tokio::test]
async fn the_ordinary_entry_point_reports_an_undecidable_guard_as_an_error() {
    assert!(run_guard_plainly("x > 0").await.is_ok(), "a TRUE guard runs cleanly");
    assert!(run_guard_plainly("x > 100").await.is_ok(), "a FALSE guard runs cleanly");

    let refused = run_guard_plainly("x + 1")
        .await
        .expect_err("★ an UNDECIDABLE guard must not run cleanly");
    println!("\n★ WHAT THE AUTHOR READS:\n  {refused}\n");
    assert!(
        refused.contains("guard cannot be decided"),
        "the error must say what happened, not merely be an error: {refused}"
    );
    assert!(
        refused.contains("not a predicate"),
        "the error must name the CAUSE so the author can act on it: {refused}"
    );
    assert!(
        refused.contains("present in the guard term"),
        "the error must say whether the guard term or the payload is at fault: {refused}"
    );
}

/// Loud is not permissive: no refusal turns a blocked COMM into a fired one.
///
/// ⚠ This is the property `FailClosedBlock` always had, re-measured *after* the change, because
/// the one way to "fix" the silence wrongly is to stop blocking.
#[tokio::test]
async fn no_refused_guard_ever_fires_a_comm() {
    for guard in ["x + 1", "[1, 2]", "x", "\"nope\"", "6 / (x - 5) > 1"] {
        let outcome = run_guard(guard).await;
        assert_eq!(
            outcome.fired,
            Vec::<i64>::new(),
            "guard {guard:?} fired a COMM the substrate could not decide"
        );
        assert_eq!(outcome.resting, vec![5], "guard {guard:?} consumed the datum without deciding");
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §2 — ★ THE TWO-CLASS SPLIT: a data-dependent failure is NOT raised
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The boundary, pinned so it cannot be read as an oversight.
///
/// `6 / (x - 5) > 1` with `x = 5` is a division by zero. The guard is *fine* for every other
/// payload, so refusing it would refuse a working guard — the machine lane made exactly this
/// call (`a_data_dependent_failure_is_not_refused_at_compile_time`) and this lane makes it too.
/// It is still **recorded**, so it is not silent; it is simply not the run's error.
#[tokio::test]
async fn a_data_dependent_failure_is_recorded_but_does_not_fail_the_run() {
    let outcome = run_guard("6 / (x - 5) > 1").await;
    assert_eq!(
        outcome.refusals.len(),
        1,
        "the failure must be RECORDED: {:?}",
        outcome.refusals
    );
    assert!(
        outcome.refusals[0].contains("carried in by this payload"),
        "a data-dependent failure must say the PAYLOAD is at fault: {:?}",
        outcome.refusals
    );
    assert!(
        run_guard_plainly("6 / (x - 5) > 1").await.is_ok(),
        "★ a data-dependent failure must NOT fail the run — the guard works for every other \
         payload, and no compile-time gate could have decided it"
    );

    // The control: the same guard shape with a payload it CAN decide runs clean and refuses
    // nothing, so the row above is about the datum and not about the guard.
    assert!(run_guard("6 / (x - 4) > 1").await.refusals.is_empty());
}

/// `where x` under a non-boolean payload is the *other* data-dependent row: the guard term could
/// be a predicate — a boolean payload makes it one — so this payload, not the term, is at fault.
#[tokio::test]
async fn a_bare_variable_guard_is_data_dependent_not_a_decider_gap() {
    let outcome = run_guard("x").await;
    assert_eq!(outcome.refusals.len(), 1, "must be recorded: {:?}", outcome.refusals);
    assert!(
        outcome.refusals[0].contains("carried in by this payload"),
        "`where x` is decidable under a boolean payload: {:?}",
        outcome.refusals
    );
    assert!(
        run_guard_plainly("x").await.is_ok(),
        "a data-dependent refusal must not fail the run"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §3 — ★ THE COMPLETE ENUMERATION, EXECUTED. Every substrate `DontKnow` source, classified.
// ════════════════════════════════════════════════════════════════════════════════════════════

fn gint(n: i64) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::GInt(n)),
    }])
}

fn gbool(b: bool) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::GBool(b)),
    }])
}

fn var(instance: VarInstance) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EVarBody(models::rhoapi::EVar {
            v: Some(Var { var_instance: Some(instance) }),
        })),
    }])
}

fn plus(left: Par, right: Par) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EPlusBody(EPlus { p1: Some(left), p2: Some(right) })),
    }])
}

fn eq(left: Par, right: Par) -> Par {
    Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EEqBody(models::rhoapi::EEq {
            p1: Some(left),
            p2: Some(right),
        })),
    }])
}

/// A `Par` that is a *process*, not an expression — `GuardAtomKind::ProcessShaped`.
fn process_shaped() -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(gint(1)),
        data: vec![gint(2)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

/// An `Expr` carrying no `expr_instance` — the malformed shape
/// `EvalError::MissingExprInstance` reports.
fn malformed() -> Par {
    Par::default().with_exprs(vec![Expr { expr_instance: None }])
}

fn refusal_of(condition: &Par, payloads: &[Par]) -> (GuardRefusalCause, RefusalProvenance) {
    match substrate_guard_disposition(condition, payloads) {
        SubstrateGuardDisposition::Undecided(refusal) => (refusal.cause, refusal.provenance),
        other => panic!("expected a refusal, got {other:?}"),
    }
}

/// ★ **EVERY WAY the substrate can fail to reach a verdict, exercised and classified.**
///
/// The table is the enumeration in `GuardRefusalCause`'s documentation, executed. A row that
/// could not be constructed would be a row that cannot be trusted.
#[test]
fn every_substrate_refusal_cause_is_reachable_and_classified() {
    // ── 1. RESIDUAL BINDER — a de Bruijn slot past the arrived bindings. ─────────────────
    let (cause, provenance) = refusal_of(&eq(var(VarInstance::BoundVar(3)), gint(0)), &[gint(5)]);
    assert!(matches!(cause, GuardRefusalCause::ResidualBinder { .. }), "{cause:?}");
    assert_eq!(provenance, RefusalProvenance::Term);

    // ── 1b. RESIDUAL BINDER — a match-frame slot (`free$i`). ─────────────────────────────
    let (cause, provenance) = refusal_of(&eq(var(VarInstance::FreeVar(0)), gint(0)), &[gint(5)]);
    assert!(matches!(cause, GuardRefusalCause::ResidualBinder { .. }), "{cause:?}");
    assert_eq!(provenance, RefusalProvenance::Term);

    // ── 3. NOT A BOOLEAN, from the TERM — `x + 1` is never a predicate. ─────────────────
    let (cause, provenance) = refusal_of(&plus(var(VarInstance::BoundVar(0)), gint(1)), &[gint(5)]);
    assert_eq!(cause, GuardRefusalCause::NotABoolean);
    assert_eq!(provenance, RefusalProvenance::Term);

    // ── 3b. NOT A BOOLEAN, from the DATUM — `where x` is a predicate for a boolean `x`. ──
    let (cause, provenance) = refusal_of(&var(VarInstance::BoundVar(0)), &[gint(5)]);
    assert_eq!(cause, GuardRefusalCause::NotABoolean);
    assert_eq!(provenance, RefusalProvenance::Datum);

    // ── 3c. …and the control: a BOOLEAN payload decides the very same guard. ────────────
    assert_eq!(
        substrate_guard_disposition(&var(VarInstance::BoundVar(0)), &[gbool(true)]),
        SubstrateGuardDisposition::Admits,
        "the `Datum` classification above must be true: a boolean payload DECIDES `where x`"
    );

    // ── 3d. PROCESS-SHAPED — a send is not a predicate under any payload. ───────────────
    let (cause, provenance) = refusal_of(&process_shaped(), &[gint(5)]);
    assert_eq!(cause, GuardRefusalCause::NotABoolean);
    assert_eq!(provenance, RefusalProvenance::Term);

    // ── 4. MALFORMED — an `Expr` with no `expr_instance`. ───────────────────────────────
    let (cause, provenance) = refusal_of(&malformed(), &[gint(5)]);
    assert_eq!(cause, GuardRefusalCause::Malformed);
    assert_eq!(provenance, RefusalProvenance::Term);

    // ── 5. UNRESOLVED REFERENCE — a `Wildcard`, which the encoder does NOT intern as a
    //      substrate variable, so it escapes row 1 and surfaces from the delegated
    //      evaluator instead. Same fact, other route, same class. ──────────────────────
    let wildcard = var(VarInstance::Wildcard(models::rhoapi::var::WildcardMsg {}));
    let (cause, provenance) = refusal_of(&eq(wildcard, gint(0)), &[gint(5)]);
    assert_eq!(
        cause,
        GuardRefusalCause::UnresolvedReference { slot: "_".to_string() },
        "★ a WILDCARD and a headless `Expr` reach the evaluator as the SAME          `EvalError::MissingExprInstance`; reporting them as one fact would rebuild this          module's own defect one level down"
    );
    assert_eq!(
        provenance,
        RefusalProvenance::Term,
        "★ a reference that survived substitution is a slot NO payload supplies — the same \
         decider gap `ResidualBinder` reports"
    );

    // ── 6. EVALUATION FAILED — a type mismatch this payload caused. ─────────────────────
    let (cause, provenance) = refusal_of(
        &eq(plus(var(VarInstance::BoundVar(0)), gint(1)), gint(6)),
        &[Par::default().with_exprs(vec![Expr {
            expr_instance: Some(ExprInstance::GString("five".to_string())),
        }])],
    );
    assert!(matches!(cause, GuardRefusalCause::EvaluationFailed { .. }), "{cause:?}");
    assert_eq!(provenance, RefusalProvenance::Datum);
}

/// The classes are exactly the provenances — one rule, applied to every cause.
#[test]
fn the_class_is_the_provenance_for_every_cause() {
    let rows: Vec<(Par, Vec<Par>)> = vec![
        (eq(var(VarInstance::BoundVar(3)), gint(0)), vec![gint(5)]),
        (plus(var(VarInstance::BoundVar(0)), gint(1)), vec![gint(5)]),
        (var(VarInstance::BoundVar(0)), vec![gint(5)]),
        (process_shaped(), vec![gint(5)]),
        (malformed(), vec![gint(5)]),
    ];
    let mut seen_gap = 0usize;
    let mut seen_data = 0usize;
    for (condition, payloads) in &rows {
        let SubstrateGuardDisposition::Undecided(refusal) =
            substrate_guard_disposition(condition, payloads)
        else {
            panic!("row must refuse");
        };
        match refusal.provenance {
            RefusalProvenance::Term => {
                assert_eq!(refusal.class, GuardRefusalClass::DeciderGap);
                seen_gap += 1;
            },
            RefusalProvenance::Datum => {
                assert_eq!(refusal.class, GuardRefusalClass::DataDependent);
                seen_data += 1;
            },
        }
    }
    // ⚠ ANTI-VACUITY: the loop above proves nothing if every row lands in one class.
    assert!(
        seen_gap > 0,
        "no decider gap in the table — the assertion above never discriminated"
    );
    assert!(seen_data > 0, "no data-dependent row — the assertion above never discriminated");
}

/// ★ Step 3 of `substrate_guard_disposition` — [`GuardRefusalCause::FormulaUndecided`] — is
/// argued unreachable, and this MEASURES it rather than assuming it.
///
/// The argument spans three modules, so a change to any of them could revive the arm. If it ever
/// does, the arm is *loud*, and this test says so first.
///
/// ⚠ The sweep is worthless if it never reaches step 3. So it counts the guards that got **all
/// the way through** steps 1 and 2 — the ones that reached a real `ground_verdict_with` call —
/// and fails if that count is zero.
#[test]
fn step_three_stays_unreached_and_the_sweep_that_says_so_is_not_vacuous() {
    let rows: Vec<(Par, Vec<Par>)> = vec![
        // Decided by the substrate's own ground procedures: these DO reach step 3.
        (eq(gint(5), gint(5)), vec![]),
        (eq(gint(5), gint(6)), vec![]),
        (eq(var(VarInstance::BoundVar(0)), gint(5)), vec![gint(5)]),
        (eq(var(VarInstance::BoundVar(0)), gint(5)), vec![gint(6)]),
        (eq(plus(var(VarInstance::BoundVar(0)), gint(1)), gint(6)), vec![gint(5)]),
        (gbool(true), vec![]),
        (gbool(false), vec![]),
        // Refused earlier: these do NOT reach step 3, and must not be counted as if they had.
        (eq(var(VarInstance::BoundVar(3)), gint(0)), vec![gint(5)]),
        (plus(var(VarInstance::BoundVar(0)), gint(1)), vec![gint(5)]),
        (process_shaped(), vec![gint(5)]),
        (malformed(), vec![gint(5)]),
    ];
    let mut reached_step_three = 0usize;
    for (condition, payloads) in &rows {
        match substrate_guard_disposition(condition, payloads) {
            // Only steps 3's `ground_verdict_with` can produce a decided verdict, so these rows
            // are exactly the ones that got there.
            SubstrateGuardDisposition::Admits | SubstrateGuardDisposition::Refutes => {
                reached_step_three += 1
            },
            SubstrateGuardDisposition::Undecided(refusal) => assert_ne!(
                refusal.cause,
                GuardRefusalCause::FormulaUndecided,
                "★ step 3 became REACHABLE — the unreachability argument in \
                 `substrate_guard_disposition` no longer holds for {condition:?}"
            ),
        }
    }
    assert!(
        reached_step_three >= 5,
        "⚠ VACUOUS: only {reached_step_three} row(s) reached step 3, so the assertion above \
         mostly never ran"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §4 — THE PROJECTIONS AGREE: the COMM verdict did not move
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `substrate_guard_passes` is `substrate_guard_disposition(...).commits()`, and both are
/// fail-closed. This is the "did the fix change which COMMs fire?" check, done at the decider
/// rather than inferred from the program level.
#[test]
fn the_disposition_and_the_boolean_verdict_never_disagree() {
    let rows: Vec<(Par, Vec<Par>)> = vec![
        (eq(gint(5), gint(5)), vec![]),
        (eq(gint(5), gint(6)), vec![]),
        (eq(var(VarInstance::BoundVar(0)), gint(5)), vec![gint(5)]),
        (eq(var(VarInstance::BoundVar(0)), gint(5)), vec![gint(6)]),
        (eq(var(VarInstance::BoundVar(3)), gint(0)), vec![gint(5)]),
        (plus(var(VarInstance::BoundVar(0)), gint(1)), vec![gint(5)]),
        (var(VarInstance::BoundVar(0)), vec![gbool(true)]),
        (var(VarInstance::BoundVar(0)), vec![gint(5)]),
        (process_shaped(), vec![gint(5)]),
        (malformed(), vec![gint(5)]),
    ];
    let mut committed = 0usize;
    let mut blocked = 0usize;
    for (condition, payloads) in &rows {
        let disposition = substrate_guard_disposition(condition, payloads);
        assert_eq!(
            disposition.commits(),
            substrate_guard_passes(condition, payloads),
            "the disposition and the boolean projection disagree on {condition:?}"
        );
        match disposition.commits() {
            true => committed += 1,
            false => blocked += 1,
        }
    }
    // ⚠ ANTI-VACUITY: an all-`false` table would pass the loop while proving nothing.
    assert!(committed > 0 && blocked > 0, "{committed} committed / {blocked} blocked");
}

/// Every refusal blocks, and only a refusal blocks-without-deciding. The `Refutes` rows here are
/// the ones that must stay **silent**: an ordinary, correct non-commit is not an error.
#[test]
fn a_refuted_guard_is_never_recorded_as_a_refusal() {
    let ledger = GuardRefusalLedger::new();
    for (condition, payloads) in [
        (eq(gint(5), gint(6)), vec![]),
        (eq(var(VarInstance::BoundVar(0)), gint(5)), vec![gint(6)]),
    ] {
        let disposition = substrate_guard_disposition(&condition, &payloads);
        assert_eq!(disposition, SubstrateGuardDisposition::Refutes, "{condition:?}");
        assert!(!disposition.commits());
        if let SubstrateGuardDisposition::Undecided(refusal) = disposition {
            ledger.record(refusal);
        }
    }
    assert!(ledger.is_empty(), "a REFUTED guard must not be reported as undecidable");
    assert!(ledger.decider_gap_error().is_none());
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §5 — THE LEDGER IS FED BY THE MATCHER ITSELF, so no install site can forget
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Recording happens inside `Match::check_commit`, so every RSpace this crate builds records
/// without being wired. Measured through the trait object, not through the concrete type.
#[test]
fn check_commit_feeds_the_ledger() {
    use models::rhoapi::{BindPattern, ListParWithRandom, TaggedContinuation};
    use rspace_plus_plus::rspace::r#match::Match;

    fn continuation(guard: &Par) -> TaggedContinuation {
        TaggedContinuation {
            guard: Some(guard.clone()),
            tagged_cont: Some(models::rhoapi::tagged_continuation::TaggedCont::ParBody(
                models::rhoapi::ParWithRandom {
                    body: Some(Par::default()),
                    random_state: Vec::new(),
                },
            )),
        }
    }

    let matcher = SubstrateGuardMatcher::new();
    let ledger = matcher.refusals();
    assert!(ledger.is_empty(), "a fresh decider has refused nothing");

    let payload = ListParWithRandom {
        pars: vec![gint(5)],
        random_state: Vec::new(),
    };
    let decider: &dyn Match<BindPattern, ListParWithRandom, TaggedContinuation> = &matcher;

    // A DECIDED guard leaves the ledger empty — the anti-vacuity control for the row below.
    assert!(decider
        .check_commit(&continuation(&eq(var(VarInstance::BoundVar(0)), gint(5))), &[&payload]));
    assert!(ledger.is_empty(), "a guard that was DECIDED must record nothing");

    // An UNDECIDABLE guard blocks *and* records.
    assert!(!decider
        .check_commit(&continuation(&plus(var(VarInstance::BoundVar(0)), gint(1))), &[&payload]));
    let recorded = ledger.snapshot();
    assert_eq!(recorded.len(), 1, "{recorded:?}");
    assert_eq!(recorded[0].class, GuardRefusalClass::DeciderGap);

    // The driver's question, and its answer.
    let error = ledger
        .decider_gap_error()
        .expect("a decider gap must be raisable");
    assert!(error.to_string().contains("guard cannot be decided"), "{error}");

    // `take` empties it; `snapshot` did not.
    assert_eq!(ledger.take().len(), 1);
    assert!(ledger.is_empty());
}

/// The refusal message is a pure function of the guard term — no address, no `Debug` derive, no
/// dependence on which run produced it. It reaches a published `^spec-failure` datum on the
/// speculation lane, so two nodes must render the same bytes.
#[test]
fn the_refusal_message_depends_on_nothing_but_the_guard() {
    let guard = plus(var(VarInstance::BoundVar(0)), gint(1));
    let first = substrate_guard_disposition(&guard, &[gint(5)]);
    let second = substrate_guard_disposition(&guard.clone(), &[gint(7)]);
    let (Some(a), Some(b)) = (first.refusal(), second.refusal()) else {
        panic!("both must refuse");
    };
    assert_eq!(a.to_string(), b.to_string(), "the message moved with the payload");

    // …and a DIFFERENT guard renders differently, so the check above is not vacuous.
    let other = substrate_guard_disposition(&process_shaped(), &[gint(5)]);
    assert_ne!(a.to_string(), other.refusal().expect("must refuse").to_string());
}
