//! ★ **THE REDUCER IS NORMATIVE — a residual binder rests the COMM, whatever the formula says.**
//!
//! ```text
//!  ┌──────────────────────────────────────────────────────────────────────────────────────┐
//!  │ THE DEFECT THIS FILE PINS                                                            │
//!  │   The surface lane FIRED a COMM whenever short-circuit evaluation made the guard      │
//!  │   formula constant-true — even when the guard still mentioned a binder the arrived    │
//!  │   payload never supplied. The reducer, on the same guard, produces an internal `Err`  │
//!  │   and the process RESTS. Firing where the reducer rests is unsoundness in the FIRING  │
//!  │   direction: the one direction a fail-closed policy cannot excuse.                    │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ THE RULING                                                                            │
//!  │   *"The reducer is normative."* Conservative: YES — the surface lane stops firing     │
//!  │   whenever a residual binder is present. Strictly fewer COMMs than before, never      │
//!  │   more. Erroring: NO — the reducer raises nothing the author sees; the COMM simply    │
//!  │   does not happen. So the surface lane **DECLINES**, loudly, carrying                 │
//!  │   `GuardRefusalCause::ResidualBinder`. `InterpreterError::UndecidableGuard` would be  │
//!  │   a THIRD behaviour, diverging from the reducer in the opposite direction: it would   │
//!  │   turn a resting process into a failing one.                                          │
//!  └──────────────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Why the reducer rests, at source
//!
//! `f1r3node/rholang/src/rust/interpreter/reduce.rs:1970` binds **both** operands of `EAnd`/`EOr`
//! with `?` before combining them — unconditionally, with no short-circuit. Its pure twin,
//! `f1r3node-rust-mettail/rho-pure-eval/src/eval.rs:348`, does the same, and a non-`GBool`
//! operand is `Err(operator_mismatch_binary)`. An operand mentioning an unresolved binder is not
//! a `GBool`; it is an error. The error propagates out of the whole connective, `guard_passes`
//! maps it to *no COMM*, and the receive and the send both remain in the term — the process rests
//! and the datum stays available for a later match.
//!
//! `Proc::Implies` is not a third case: it lowers to `(not a) or b`
//! (`rholang-runtime/src/rholang_ast.rs`, `Kont::Implies`), so it is an `EOr` on the machine and
//! inherits exactly the same both-operands-strict discipline.
//!
//! # ★ Why a check on the FORMULA cannot work — three mechanisms, one end
//!
//! | # | guard | mechanism that discards the binder | formula after encoding |
//! |---|---|---|---|
//! | 1 | `true or (y == 2)` | `GuardFormula::or`'s **constructor-time** collapse `(True, _) ⟼ True` | literally `True` |
//! | 2 | `false implies (y == 2)` | `ground_verdict_with`'s **evaluator** short-circuit on a refuted antecedent | `Implies(False, …)` |
//! | 3 | `(1 == 1) or (y == 2)` | `ground_verdict_with`'s **evaluator** short-circuit on a satisfied left disjunct | `Or(Linear, Linear)` |
//!
//! Row 1 is the sharpest: the residual binder is **gone from the formula before any ground check
//! runs**, while `encoding.vars` still names it — so a fix inspecting `formula.atoms()` would see
//! nothing to refuse. Rows 2 and 3 show the constructor is not the only discarder: the
//! *evaluator* discards too, and it discards operands the constructor kept. The check must
//! therefore consult the **encoding** — `encoding.vars` — independently of formula shape, which
//! is exactly the reasoning `rholang-runtime/src/guard_par_substrate.rs` gives for sweeping
//! `encoding.opaque` rather than `formula.atoms()` in its own step 2.
//!
//! # ★ This is NOT divergence K, and the difference decides the SCOPE of the repair
//!
//! `rholang-runtime/tests/rho_rholang_conformance.rs`'s divergence **K** is `DontKnow ∨ Sat`: the
//! host declines `(x matches {φ|ψ}) or true` while the machine FIRES it, because K's undecided
//! operand is one the machine's spatial oracle decides **totally**. That file explicitly rejects
//! the Kleene repair `DontKnow ∨ Sat = Sat` for the general case.
//!
//! This file is the mirror, `Sat ∨ DontKnow`, and it is a different input class: here the
//! undecided operand is one the machine **errors** on. K's remedy would fire more COMMs; this one
//! fires fewer. Neither subsumes the other — which is precisely why the repair is scoped to the
//! **residual-binder** class (`encoding.vars`) and NOT extended to the opaque-fragment class
//! (`encoding.opaque`). The lowered lane may sweep `opaque` because its delegate *is*
//! `rho_pure_eval`, so "the delegate could not decide it" ⟺ "the machine errors on it". The
//! surface lane's delegates (`formula::host_matches_verdict`,
//! `runtime::compare_collection_equality`) decline things the machine decides, so the same sweep
//! here would refuse guards the machine fires — worsening K in the resting direction.

#![cfg(feature = "rholang")]

use std::sync::Arc;

use mettail_languages::rholang::guard_substrate::{
    encode_guard, eval_guard_disposition_via_substrate, surface_guard_disposition,
    SurfaceGuardDisposition,
};
use mettail_languages::rholang::receive::GuardDisposition;
use mettail_languages::rholang::{Bool, Int, Proc, Str};
use mettail_prattail::guard_formula::GuardFormula;
use mettail_prattail::guard_refusal::{GuardRefusalCause, GuardRefusalClass, RefusalProvenance};
use mettail_runtime::{get_or_create_var, OrdVar, Var};

// ── Term builders ───────────────────────────────────────────────────────────────────────────

fn arc(p: Proc) -> Arc<Proc> {
    Arc::new(p)
}

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

/// `y == 2` — the canonical residual binder: a guard the author wrote against a binder the
/// arrived payload did not supply. On the machine this is `EEq(EVar(y), GInt(2))` with `y`
/// unresolved, which is an `Err`, which rests.
fn residual() -> Proc {
    Proc::Eq(arc(var("y")), arc(int(2)))
}

/// `2 == 2` — [`residual`] with the binder RESOLVED. Identical shape, identical sort, no binder.
///
/// ★ This is the control operand. Every matrix row is built from a *hole*, so each row has a twin
/// that differs from it in exactly one respect: whether the payload supplied the binder. A change
/// that made everything decline would satisfy every "must not fire" assertion in this file; the
/// twins are what make that impossible.
fn resolved() -> Proc {
    Proc::Eq(arc(int(2)), arc(int(2)))
}

/// `1 == 1` — a satisfied comparison that the encoder emits as a `Linear` constraint rather than
/// as `GuardFormula::True`, so a disjunction with it does **not** collapse at construction time.
fn satisfied_comparison() -> Proc {
    Proc::Eq(arc(int(1)), arc(int(1)))
}

/// The disposition and the projected host verdict, together.
fn disposition_of(guard: &Proc) -> (SurfaceGuardDisposition, GuardDisposition) {
    (
        surface_guard_disposition(guard, guard),
        eval_guard_disposition_via_substrate(guard),
    )
}

/// Why a guard was not refused as a residual binder, or `None` when it was — rendered so a whole
/// matrix can be reported in one run rather than one failure at a time.
///
/// The cause is checked **by name**: a decider that answered one collapsed symbol for everything
/// would satisfy a weaker "some refusal exists" claim, and that collapse is what
/// `prattail/src/guard_refusal.rs` exists to remove.
fn residual_binder_complaint(label: &str, guard: &Proc, expected_slots: usize) -> Option<String> {
    let (disposition, host) = disposition_of(guard);
    let refusal = match &disposition {
        SurfaceGuardDisposition::Undecided(refusal) => refusal,
        SurfaceGuardDisposition::Admits => {
            return Some(format!(
                "  {label:<26} FIRES — the reducer errors on this guard and RESTS; firing it is \
                 unsoundness in the FIRING direction"
            ))
        },
        SurfaceGuardDisposition::Refutes => {
            return Some(format!(
                "  {label:<26} REFUTES — a decided `false` is a claim about a guard nobody can \
                 decide; the reducer reaches no verdict at all"
            ))
        },
    };
    match &refusal.cause {
        GuardRefusalCause::ResidualBinder { slots } => {
            if slots.len() != expected_slots {
                return Some(format!(
                    "  {label:<26} refused as ResidualBinder but named {} slots, expected \
                     {expected_slots}: {slots:?}",
                    slots.len()
                ));
            }
            if !slots[0].starts_with("y$") {
                return Some(format!(
                    "  {label:<26} must name the slot the substitution could not reach \
                     (`name$unique_id`): {slots:?}"
                ));
            }
        },
        other => {
            return Some(format!(
                "  {label:<26} refused as {other:?} — the obstruction is a RESIDUAL BINDER and \
                 the refusal must say so by name, or the author is sent looking for a decider \
                 gap that is not there"
            ))
        },
    }
    if refusal.provenance != RefusalProvenance::Term {
        return Some(format!(
            "  {label:<26} provenance {:?} — substitution has already applied every binding this \
             receive will ever get, so a surviving slot is one NO payload supplies",
            refusal.provenance
        ));
    }
    if refusal.class != GuardRefusalClass::DeciderGap {
        return Some(format!("  {label:<26} class {:?}, expected DeciderGap", refusal.class));
    }
    if host != GuardDisposition::Declines {
        return Some(format!(
            "  {label:<26} projected to {host:?} — the ruling is DECLINE, not `Blocks` and not \
             `Fires`"
        ));
    }
    None
}

/// Assert one guard rests on a residual binder, naming exactly one slot.
fn assert_rests_on_residual_binder(label: &str, guard: &Proc) {
    if let Some(complaint) = residual_binder_complaint(label, guard, 1) {
        panic!("{}\n\nguard: {guard}", complaint.trim_start());
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE PREMISE — the residual binder is invisible to a formula-shaped check
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **Why the fix cannot live in the formula.** `true or (y == 2)` encodes to the formula
/// `True` — the binder is gone before any ground procedure runs — while `encoding.vars` still
/// names it. Measured, not asserted in prose, because it is the entire reason the check consults
/// the encoding's var map instead of `formula.atoms()`.
#[test]
fn the_constructor_collapse_erases_the_binder_from_the_formula_but_not_from_the_var_map() {
    let guard = Proc::Or(arc(boolean(true)), arc(residual()));
    let encoding = encode_guard(&guard);

    assert_eq!(
        encoding.formula,
        GuardFormula::True,
        "premise: `GuardFormula::or` collapses `(True, _)` at CONSTRUCTION time, so the disjunct \
         carrying `y` is not in the formula at all. Got {:?}",
        encoding.formula
    );
    assert!(
        encoding.formula.atoms().is_empty(),
        "premise: and it leaves no atom behind either, so a sweep over `formula.atoms()` — the \
         one place a formula-shaped fix could look — finds nothing to refuse"
    );
    assert_eq!(
        encoding.vars.names().len(),
        1,
        "premise: the encoder still interned the binder, so `encoding.vars` is where the fact \
         survives. Got {:?}",
        encoding.vars.names()
    );
    assert!(encoding.vars.names()[0].starts_with("y$"), "{:?}", encoding.vars.names());
}

/// ★ The constructor collapse is not the only discarder, so a fix that defeated only the
/// constructor would still be incomplete. `(1 == 1) or (y == 2)` keeps **both** disjuncts in the
/// formula — `1 == 1` encodes as a `Linear` constraint, not as `True` — and it is
/// `ground_verdict_with`'s own left-strict short-circuit that then discards the right one.
#[test]
fn the_evaluator_short_circuits_a_disjunct_the_constructor_kept() {
    let guard = Proc::Or(arc(satisfied_comparison()), arc(residual()));
    let encoding = encode_guard(&guard);

    assert!(
        matches!(encoding.formula, GuardFormula::Or(_, _)),
        "premise: `1 == 1` encodes as a Linear constraint rather than as `GuardFormula::True`, so \
         the constructor collapse does NOT apply and both disjuncts survive into the formula. \
         Got {:?}",
        encoding.formula
    );
    assert_eq!(
        encoding.vars.names().len(),
        1,
        "premise: `y` is interned. Got {:?}",
        encoding.vars.names()
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE THREE ROWS THAT FIRED
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **ROW 1 — the constructor collapse.** `true or (y == 2)`.
///
/// The machine evaluates `y == 2`, fails to resolve `y`, and the whole `EOr` is an `Err` — the
/// process rests. The surface lane fired it, because its formula is literally `True`.
#[test]
fn row_one_true_or_residual_binder_rests_where_it_used_to_fire() {
    assert_rests_on_residual_binder(
        "row 1 (constructor collapse)",
        &Proc::Or(arc(boolean(true)), arc(residual())),
    );
}

/// ★ **ROW 2 — vacuous truth.** `false implies (y == 2)`.
///
/// `implies` lowers to `(not a) or b`, so on the machine this is `EOr(ENot(GBool(false)), …)` —
/// both operands evaluated, the second an `Err`, the guard fails, the process rests. The surface
/// lane fired it on the evaluator's refuted-antecedent short-circuit.
#[test]
fn row_two_false_implies_residual_binder_rests_where_it_used_to_fire() {
    assert_rests_on_residual_binder(
        "row 2 (vacuous truth)",
        &Proc::Implies(arc(boolean(false)), arc(residual())),
    );
}

/// ★ **ROW 3 — the evaluator short-circuit.** `(1 == 1) or (y == 2)`.
///
/// The same end as row 1 by a different route: here both disjuncts reach the formula and it is
/// `ground_verdict_with` that discards the right one after satisfying the left.
#[test]
fn row_three_satisfied_disjunct_or_residual_binder_rests_where_it_used_to_fire() {
    assert_rests_on_residual_binder(
        "row 3 (evaluator short-circuit)",
        &Proc::Or(arc(satisfied_comparison()), arc(residual())),
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE FULL MATRIX — every connective, both operand positions, both settling constants
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// One place a residual binder can hide behind a settling operand.
///
/// `build` takes the operand as a **hole** so each row has an exact control twin: the same
/// connective, the same operand position, the same settling constant, with the binder resolved.
struct MatrixRow {
    label: &'static str,
    build: fn(Proc) -> Proc,
    /// What `eval_guard_disposition_via_substrate` answered on the binder-carrying instance
    /// **before** the residual-binder refusal existed — the measured RED column.
    before: GuardDisposition,
}

const MATRIX: &[MatrixRow] = &[
    // ── `or`, binder on the RIGHT — the firing direction ───────────────────────────────────
    MatrixRow {
        label: "true or ⟨·⟩",
        build: |hole| Proc::Or(arc(boolean(true)), arc(hole)),
        before: GuardDisposition::Fires,
    },
    MatrixRow {
        label: "(1 == 1) or ⟨·⟩",
        build: |hole| Proc::Or(arc(satisfied_comparison()), arc(hole)),
        before: GuardDisposition::Fires,
    },
    MatrixRow {
        label: "false or ⟨·⟩",
        build: |hole| Proc::Or(arc(boolean(false)), arc(hole)),
        before: GuardDisposition::Declines,
    },
    // ── `or`, binder on the LEFT — already conservative (left-strict propagation) ───────────
    MatrixRow {
        label: "⟨·⟩ or true",
        build: |hole| Proc::Or(arc(hole), arc(boolean(true))),
        before: GuardDisposition::Declines,
    },
    MatrixRow {
        label: "⟨·⟩ or false",
        build: |hole| Proc::Or(arc(hole), arc(boolean(false))),
        before: GuardDisposition::Declines,
    },
    // ── `and`, binder on the RIGHT ─────────────────────────────────────────────────────────
    MatrixRow {
        label: "true and ⟨·⟩",
        build: |hole| Proc::And(arc(boolean(true)), arc(hole)),
        before: GuardDisposition::Declines,
    },
    MatrixRow {
        label: "false and ⟨·⟩",
        build: |hole| Proc::And(arc(boolean(false)), arc(hole)),
        before: GuardDisposition::Blocks,
    },
    // ── `and`, binder on the LEFT ──────────────────────────────────────────────────────────
    MatrixRow {
        label: "⟨·⟩ and true",
        build: |hole| Proc::And(arc(hole), arc(boolean(true))),
        before: GuardDisposition::Declines,
    },
    MatrixRow {
        label: "⟨·⟩ and false",
        build: |hole| Proc::And(arc(hole), arc(boolean(false))),
        before: GuardDisposition::Declines,
    },
    // ── `implies`, binder on the RIGHT — vacuous truth is the firing direction ──────────────
    MatrixRow {
        label: "false implies ⟨·⟩",
        build: |hole| Proc::Implies(arc(boolean(false)), arc(hole)),
        before: GuardDisposition::Fires,
    },
    MatrixRow {
        label: "true implies ⟨·⟩",
        build: |hole| Proc::Implies(arc(boolean(true)), arc(hole)),
        before: GuardDisposition::Declines,
    },
    // ── `implies`, binder on the LEFT ──────────────────────────────────────────────────────
    MatrixRow {
        label: "⟨·⟩ implies true",
        build: |hole| Proc::Implies(arc(hole), arc(boolean(true))),
        before: GuardDisposition::Declines,
    },
    MatrixRow {
        label: "⟨·⟩ implies false",
        build: |hole| Proc::Implies(arc(hole), arc(boolean(false))),
        before: GuardDisposition::Declines,
    },
    // ── the unary connective, and the bare guard, for a complete enumeration ────────────────
    MatrixRow {
        label: "not ⟨·⟩",
        build: |hole| Proc::Not(arc(hole)),
        before: GuardDisposition::Declines,
    },
    MatrixRow {
        label: "⟨·⟩",
        build: |hole| hole,
        before: GuardDisposition::Declines,
    },
];

/// ★ **THE MATRIX.** Every row carries a residual binder, so every row must rest — whichever
/// operand the binder sits in, and whatever the other operand settles the formula to.
///
/// All rows are reported together rather than one panic at a time, so a single run yields the
/// whole table.
#[test]
fn every_connective_and_both_operand_positions_rest_on_a_residual_binder() {
    let complaints: Vec<String> = MATRIX
        .iter()
        .filter_map(|row| residual_binder_complaint(row.label, &(row.build)(residual()), 1))
        .collect();
    assert!(
        complaints.is_empty(),
        "{} of {} residual-binder guards did not rest:\n{}",
        complaints.len(),
        MATRIX.len(),
        complaints.join("\n")
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE CONTROL — the same shapes, binder resolved, still decide. Same tree, same run.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **THE CONTROL THAT MAKES EVERY ROW ABOVE EVIDENCE.**
///
/// Each row is the matrix row above with `⟨·⟩ = 2 == 2` instead of `y == 2`: the same connective,
/// the same operand position, the same settling constant, differing in exactly one respect —
/// whether the payload supplied the binder. Every twin must reach a **verdict**, and enough of
/// them must still FIRE that "the lane stopped firing everything" is excluded.
#[test]
fn the_same_shapes_with_the_binder_resolved_still_decide_and_still_fire() {
    let mut undecided: Vec<String> = Vec::new();
    let mut fired = 0usize;
    let mut refuted = 0usize;

    for row in MATRIX {
        let twin = (row.build)(resolved());
        let (disposition, host) = disposition_of(&twin);
        match host {
            GuardDisposition::Fires => fired += 1,
            GuardDisposition::Blocks => refuted += 1,
            GuardDisposition::Declines => {
                undecided.push(format!("  {:<26} {disposition:?}  ({twin})", row.label))
            },
        }
        if host != GuardDisposition::Declines {
            assert!(
                disposition.refusal().is_none(),
                "CONTROL {}: a DECIDED guard must carry no refusal; got {disposition:?}",
                row.label
            );
        }
    }

    assert!(
        undecided.is_empty(),
        "{} control twins carry NO residual binder and must still decide:\n{}",
        undecided.len(),
        undecided.join("\n")
    );
    assert!(fired >= 8, "the control must exhibit real firing, got {fired}");
    assert!(refuted >= 3, "the control must exhibit real refuting, got {refuted}");
    println!(
        "\n★ CONTROL: with the binder resolved, {fired} of {} twins FIRE and {refuted} BLOCK — \
         the refusal is scoped to the residual-binder class, not a blanket decline.\n",
        MATRIX.len()
    );
}

/// ★ A second control, over shapes the matrix does not build at all: the lane still decides
/// guards across every sort it covers, including the delegated structural leg.
#[test]
fn ground_guards_across_the_covered_sorts_still_decide() {
    let rows: Vec<(&str, Proc, GuardDisposition)> = vec![
        ("true", boolean(true), GuardDisposition::Fires),
        ("false", boolean(false), GuardDisposition::Blocks),
        ("1 == 1", satisfied_comparison(), GuardDisposition::Fires),
        ("1 == 2", Proc::Eq(arc(int(1)), arc(int(2))), GuardDisposition::Blocks),
        ("2 > 1", Proc::Gt(arc(int(2)), arc(int(1))), GuardDisposition::Fires),
        ("1 >= 2", Proc::GtEq(arc(int(1)), arc(int(2))), GuardDisposition::Blocks),
        (
            r#""hi" == "hi""#,
            Proc::Eq(arc(string("hi")), arc(string("hi"))),
            GuardDisposition::Fires,
        ),
        (
            r#""hi" == "bye""#,
            Proc::Eq(arc(string("hi")), arc(string("bye"))),
            GuardDisposition::Blocks,
        ),
        // The DELEGATED structural leg still answers — in the POSITIVE direction only. A
        // spatial MISS (`42 matches 41`) declines, and that is deliberate:
        // `formula::host_matches_verdict`'s `FormulaShape::Term` arm reports success only,
        // because a host match implies a machine match while a host NON-match implies nothing.
        // It is a property of that delegate, unrelated to the residual-binder class.
        (
            "42 matches 42",
            Proc::Matches(arc(int(42)), arc(int(42))),
            GuardDisposition::Fires,
        ),
    ];
    for (label, guard, expected) in &rows {
        let (disposition, host) = disposition_of(guard);
        assert_eq!(
            host, *expected,
            "CONTROL {label}: no residual binder, so the residual-binder refusal must not touch \
             it. Got {disposition:?}"
        );
        assert!(
            disposition.refusal().is_none(),
            "CONTROL {label}: a DECIDED guard must carry no refusal; got {disposition:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE LEDGER — which rows were RED, stated honestly
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ **THE LEDGER, and the anti-vacuity claim it supports.**
///
/// Three of the fifteen matrix rows FIRED before the fix — those are the COMMs that now rest, and
/// they are the whole ruling. One REFUTED — no COMM changes there, but a decided `false` was
/// being claimed about a guard nobody can decide, and that claim is withdrawn. The remaining
/// eleven were already declining by the left-strict discipline, and this file says so rather than
/// counting fifteen reds.
///
/// The `before` column is a *record of a measurement*, so it cannot be re-derived from the code
/// under test; what is asserted here is that the record still describes three classes and that
/// the firing class is not empty — a fix whose firing set were empty would be vacuous.
#[test]
fn the_ledger_names_the_rows_that_were_firing_and_the_firing_set_is_not_empty() {
    let mut was_firing: Vec<&str> = Vec::new();
    let mut was_refuting: Vec<&str> = Vec::new();
    let mut was_declining: Vec<&str> = Vec::new();
    for row in MATRIX {
        match row.before {
            GuardDisposition::Fires => was_firing.push(row.label),
            GuardDisposition::Blocks => was_refuting.push(row.label),
            GuardDisposition::Declines => was_declining.push(row.label),
        }
    }

    assert_eq!(
        was_firing,
        vec!["true or ⟨·⟩", "(1 == 1) or ⟨·⟩", "false implies ⟨·⟩"],
        "the matrix rows whose binder-carrying instance used to FIRE — the three rows of the \
         divergence table"
    );
    assert_eq!(
        was_refuting,
        vec!["false and ⟨·⟩"],
        "the matrix row that used to claim a decided `false` about an undecidable guard"
    );
    assert_eq!(was_declining.len(), 11, "already conservative: {was_declining:?}");
    assert_eq!(MATRIX.len(), 15);

    println!(
        "\n★ LEDGER: of {} matrix rows, {} used to FIRE (now rest), {} used to claim a decided \
         `false` (now refuses), {} were already conservative.\n",
        MATRIX.len(),
        was_firing.len(),
        was_refuting.len(),
        was_declining.len()
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ CONSERVATIVITY — strictly fewer COMMs, never more
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The direction of the change, stated as a property rather than row by row: over the matrix,
/// its control twins, and the ground corpus, the lane fires **only** where no binder survived.
///
/// This is the invariant the ruling names — *"strictly fewer COMMs, never more"* — and it is
/// checked against `encoding.vars`, which is the one place the fact lives.
#[test]
fn the_lane_never_fires_a_guard_whose_encoding_still_has_a_binder() {
    let mut guards: Vec<Proc> = Vec::with_capacity(2 * MATRIX.len() + 8);
    for row in MATRIX {
        guards.push((row.build)(residual()));
        guards.push((row.build)(resolved()));
    }
    guards.extend([
        boolean(true),
        boolean(false),
        satisfied_comparison(),
        Proc::Matches(arc(int(42)), arc(int(42))),
        Proc::Eq(arc(string("hi")), arc(string("hi"))),
        // Two binders behind a settling `true`.
        Proc::Or(arc(boolean(true)), arc(Proc::Eq(arc(var("y")), arc(var("z"))))),
        // A binder behind a settling `true`, nested two connectives deep.
        Proc::Or(
            arc(boolean(true)),
            arc(Proc::And(
                arc(boolean(true)),
                arc(Proc::Or(arc(boolean(true)), arc(residual()))),
            )),
        ),
    ]);

    let mut fired_without_binder = 0usize;
    for guard in &guards {
        let has_binder = !encode_guard(guard).vars.is_empty();
        let host = eval_guard_disposition_via_substrate(guard);
        match has_binder {
            true => assert_ne!(
                host,
                GuardDisposition::Fires,
                "`{guard}` still mentions a binder the payload did not supply, and the reducer \
                 rests on it. Firing it is unsoundness in the FIRING direction, which no \
                 fail-closed policy excuses."
            ),
            false => {
                if host == GuardDisposition::Fires {
                    fired_without_binder += 1;
                }
            },
        }
    }
    assert!(
        fired_without_binder >= 8,
        "the invariant would hold vacuously if nothing fired at all; got {fired_without_binder}"
    );
}

/// A guard with **two** residual binders names both slots: the refusal reports the var map, not
/// the first thing the decider tripped over.
#[test]
fn a_refusal_names_every_slot_the_substitution_could_not_reach() {
    let guard = Proc::Or(arc(boolean(true)), arc(Proc::Eq(arc(var("y")), arc(var("z")))));
    let disposition = surface_guard_disposition(&guard, &guard);
    let refusal = disposition
        .refusal()
        .unwrap_or_else(|| panic!("`{guard}` carries two residual binders; got {disposition:?}"));
    match &refusal.cause {
        GuardRefusalCause::ResidualBinder { slots } => {
            assert_eq!(slots.len(), 2, "both slots, in interning order: {slots:?}");
            assert!(slots[0].starts_with("y$"), "{slots:?}");
            assert!(slots[1].starts_with("z$"), "{slots:?}");
        },
        other => panic!("expected `ResidualBinder`, got {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
// ★ THE RULING'S NEGATIVE HALF — declining is not erroring
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The reducer raises nothing the author sees: `reduce.rs`'s `?` produces an internal `Err`,
/// the COMM does not happen, and the process rests. Matching it means the surface lane
/// **declines**, and declining is a **value** — a `SurfaceGuardDisposition::Undecided` — not a
/// panic and not an `Err`.
///
/// Asserted because the third behaviour (raising `UndecidableGuard`) would diverge from the
/// reducer in the opposite direction: it would turn a resting process into a failing one. The
/// decider is also contractually total on the COMM path, so a panic here would be worse than the
/// defect being removed.
#[test]
fn declining_is_a_value_and_the_shape_is_not_poisoned() {
    for row in MATRIX {
        let refused = (row.build)(residual());
        // Total: it returns a value. A decider that raised would never reach the assertion.
        assert!(
            matches!(
                surface_guard_disposition(&refused, &refused),
                SurfaceGuardDisposition::Undecided(_)
            ),
            "{}: {refused}",
            row.label
        );

        // ★ And the SAME shape, once the binder is supplied, decides. The refusal is about this
        // guard under this payload; it does not poison the shape — which is what "the datum stays
        // available for a later match" means at the level this lane can observe it.
        let supplied = (row.build)(resolved());
        assert_ne!(
            eval_guard_disposition_via_substrate(&supplied),
            GuardDisposition::Declines,
            "{}: with the binder supplied the very same shape must decide — `{supplied}`",
            row.label
        );
    }
}
