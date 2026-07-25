//! M-0 — the `implies` connective, end-to-end on the REAL f1r3node reducer.
//!
//! `implies` is the paper's `φ ⇒ ψ` (notation delta N2: a word, because neither
//! `⇒` nor `=>` is available in this grammar). It adds **no machine surface at
//! all**: the RhoCalc lowering compiles it to the material-implication identity
//!
//! ```text
//!     ⟦a implies b⟧  =  EOrBody { p1: ENotBody ⟦a⟧ , p2: ⟦b⟧ }
//! ```
//!
//! and BOTH halves of that identity were already emitted by
//! `rhocalc_ast::lower_proc` and already decided by `rho-pure-eval`
//! (`eval.rs`'s `ENotBody` arm and its `EOrBody` → `bool_binop("||", …)` arm).
//! So there is no new `ExprInstance`, no new evaluator arm, and no
//! consensus-visible wire change to review.
//!
//! Everything here runs on the production guard path, not a host simulation:
//!
//! ```text
//!   RhoCalc source ──Proc::parse_via_wpda──▶ Proc ──lower_rhocalc_proc──▶ Par
//!        │                                                                 │
//!        │  (f1r3node's own Rholang parser is    Receive.condition ◀────────┘
//!        │   NEVER invoked on this path)                  │
//!        ▼                                                ▼
//!                        reduce.rs: substitute_and_charge(guard, depth 1)
//!                                            │
//!                                            ▼
//!                        rspace Match::check_commit ─▶ guard_passes
//!                                            │
//!                                            ▼
//!                              rho_pure_eval::eval  ──▶ commits iff GBool(true)
//! ```
//!
//! ## Two observation surfaces, and why both are needed
//!
//! 1. **Payload position** (`@"OUT"!(φ)`) — the machine's *verdict* for `φ` lands
//!    on `@"OUT"` as a `Bool`, so a truth table can be read directly. This is
//!    also the position in which a `fold` is liftable, so it is where the
//!    three-helper fold traversal is exercised.
//! 2. **Guard position** (`for(@x <- @"c" where φ)`) — the *operational*
//!    contract: commit, or fail SHUT leaving the datum resting (§18.5).
//!
//! ## Why the guard-position tests compare STRINGS, not integers
//!
//! ★ HISTORICAL as of 2026-07-25 (divergence I). A plain RhoCalc integer literal
//! used to lower to `GBigInt`, and `rho-pure-eval`'s `cmp_binop` (`eval.rs`)
//! admits only `(GInt,GInt)`, `(GString,GString)` and `(GBool,GBool)` — so a
//! `GBigInt` comparison raised `EvalError`, §18.5 collapsed that to guard-fail,
//! and EVERY numeric guard in the language failed shut. The ordered-`Str` guards
//! were chosen to route around it; they have exactly the same shape and drive
//! exactly the same machine arms, so they are kept as-is.
//!
//! A plain literal is now `GInt` (`normalize_ground`'s carrier), so numeric
//! guards work; the inverted pin is
//! `a_plain_integer_comparison_guard_now_fires_and_the_bigint_one_still_fails_shut`,
//! which also keeps the surviving `GBigInt` half so a future `cmp_binop`
//! widening cannot pass silently.
//!
//! The HOST twin of the same truth table (`eval_guard_bool`, reached through the
//! Dovetail/oracle receive path) lives in
//! `languages/tests/rhocalc_tests.rs::implies_*` — the two suites are the two
//! halves of the two-evaluator agreement obligation.

#![cfg(feature = "rhocalc-runtime")]

use std::collections::HashMap;

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::fold_contract::fold_definitions_for;
use mettail_rholang_runtime::rhocalc_ast::{clear_held_fold_sites, take_held_fold_sites};
use mettail_rholang_runtime::run::run_installed_program_with_call_definitions_and_read_runtime_values;
use mettail_rholang_runtime::{
    lower_rhocalc_proc, run_normalized_par_for_oracle_and_read_runtime_value_channels,
};
use mettail_runtime::{clear_var_cache, RuntimeObservationValue};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::Par;

/// Parse RhoCalc surface syntax with the GENERATED PraTTaIL parser and lower it
/// to a normalized `Par`. No Rholang source text is produced or reparsed.
fn parse_lower(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc parse failed for {source:?}: {err:?}"));
    lower_rhocalc_proc(&proc)
        .unwrap_or_else(|err| panic!("rhocalc lowering failed for {source:?}: {err:?}"))
}

/// Evaluate a RhoCalc program that may contain width folds, materializing every
/// held fold site into the system-process `Definition`s the production exec path
/// installs (`backend.rs`), and return the observations resting on `@"OUT"`.
///
/// Returns the fold-site count alongside the observations: a dropped fold is a
/// SILENT defect at the traversal layer, so the count is asserted, not assumed.
async fn run_with_folds(source: &str) -> (usize, Vec<RuntimeObservationValue>) {
    clear_var_cache();
    clear_held_fold_sites();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc parse failed for {source:?}: {err:?}"));
    let par = lower_rhocalc_proc(&proc)
        .unwrap_or_else(|err| panic!("rhocalc lowering failed for {source:?}: {err:?}"));
    let sites = take_held_fold_sites();
    let fold_count = sites.len();
    let observed = run_installed_program_with_call_definitions_and_read_runtime_values(
        &Par::default(),
        &par,
        fold_definitions_for(&sites),
        "OUT",
    )
    .await
    .unwrap_or_else(|err| panic!("execution failed for {source:?}: {err}"));
    (fold_count, observed)
}

/// The machine's boolean verdict for the propositional expression `formula`,
/// observed by sending it to `@"OUT"` and reading the resting value.
///
/// `lower_rhocalc_proc` does NOT normalize, so a `![…]` host constant fold never
/// runs on this path: the `EOrBody`/`ENotBody` tree really is evaluated by
/// `rho_pure_eval`.
async fn machine_verdict(formula: &str) -> bool {
    let (_folds, observed) = run_with_folds(&format!(r#"@"OUT"!({formula})"#)).await;
    match observed.as_slice() {
        [RuntimeObservationValue::Bool(verdict)] => *verdict,
        other => panic!("formula {formula:?} must reduce to exactly one Bool, got {other:?}"),
    }
}

/// Run a guarded receive against one datum and report BOTH observables of the
/// same quiescent store: what landed on `@"OUT"`, and what is still resting on
/// `@"c"`.
async fn guarded_receive(guard: &str, datum: &str) -> (Vec<String>, Vec<String>) {
    let source =
        format!(r#"{{ for(@x <- @"c" where {guard}) {{ @"OUT"!(x) }} | @"c"!({datum}) }}"#);
    let par = parse_lower(&source);
    let observed = run_normalized_par_for_oracle_and_read_runtime_value_channels(&par, &["OUT", "c"])
        .await
        .unwrap_or_else(|err| panic!("guarded receive failed for {source:?}: {err}"));
    (rendered(&observed, "OUT"), rendered(&observed, "c"))
}

fn rendered(observed: &HashMap<String, Vec<RuntimeObservationValue>>, channel: &str) -> Vec<String> {
    let mut values: Vec<String> = observed
        .get(channel)
        .map(|vs| vs.iter().map(|v| v.to_string()).collect())
        .unwrap_or_default();
    values.sort();
    values
}

/// The four rows of `⇒`, each spelled twice — once as ground `bool` literals and
/// once as `int`-width-folded comparisons — so the table is exercised both with
/// and without the fold trampoline in the operand positions.
const IMPLICATION_ROWS: [(bool, bool, bool); 4] =
    [(false, false, true), (false, true, true), (true, false, false), (true, true, true)];

fn as_bool_literal(value: bool) -> &'static str {
    if value {
        "true"
    } else {
        "false"
    }
}

/// A folded comparison whose value is `value`, in a form the machine can decide:
/// `int(a, w)` is the fixed-width `Int` ⟷ `GInt` carrier, so `cmp_binop` accepts
/// it where a plain (arbitrary-precision) literal would not.
fn as_folded_comparison(value: bool) -> &'static str {
    if value {
        "int(3,8) > int(1,8)"
    } else {
        "int(0,8) > int(1,8)"
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// 1. The truth table, decided by the MACHINE
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn implies_truth_table_on_the_reducer() {
    // `p ⇒ q` ≡ `¬p ∨ q`. The connective has exactly four ground rows and every
    // one of them is checked — no representative sampling.
    for (p, q, expected) in IMPLICATION_ROWS {
        let formula = format!("{} implies {}", as_bool_literal(p), as_bool_literal(q));
        assert_eq!(
            machine_verdict(&formula).await,
            expected,
            "reducer row {p} implies {q} must be {expected} (formula {formula:?})"
        );
    }
}

#[tokio::test]
async fn implies_truth_table_on_the_reducer_with_folded_operands() {
    // The same four rows with every operand a lifted `int(·,8)` width fold, so
    // the verdict is produced only AFTER the fold trampoline substitutes the
    // folded values back into the implication.
    for (p, q, expected) in IMPLICATION_ROWS {
        let formula = format!("{} implies {}", as_folded_comparison(p), as_folded_comparison(q));
        let (folds, observed) = run_with_folds(&format!(r#"@"OUT"!({formula})"#)).await;
        assert_eq!(folds, 4, "each operand contributes two `int(·,8)` folds (formula {formula:?})");
        assert_eq!(
            observed,
            vec![RuntimeObservationValue::Bool(expected)],
            "folded row {p} implies {q} must be {expected} (formula {formula:?})"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// 2. The lowering really is `EOr(ENot a, b)`
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn implies_lowers_to_or_of_not() {
    // The identity is the whole reason `implies` needs no machine surface, so it
    // is asserted structurally rather than inferred from behaviour.
    let par = parse_lower("true implies false");
    let expr = match par.exprs.as_slice() {
        [expr] => expr.expr_instance.as_ref().expect("a lowered expression"),
        other => panic!("`implies` must lower to exactly one Expr, got {other:?}"),
    };
    let disjunction = match expr {
        ExprInstance::EOrBody(or) => or,
        other => panic!("`implies` must lower to EOrBody, got {other:?}"),
    };
    let antecedent = disjunction.p1.as_ref().expect("EOr must carry its left operand");
    assert!(
        matches!(
            antecedent.exprs.as_slice(),
            [models::rhoapi::Expr { expr_instance: Some(ExprInstance::ENotBody(_)) }]
        ),
        "the ANTECEDENT must be negated: ⟦a implies b⟧ = EOr(ENot ⟦a⟧, ⟦b⟧), got {antecedent:?}"
    );
    let consequent = disjunction.p2.as_ref().expect("EOr must carry its right operand");
    assert!(
        matches!(
            consequent.exprs.as_slice(),
            [models::rhoapi::Expr { expr_instance: Some(ExprInstance::GBool(false)) }]
        ),
        "the CONSEQUENT must ride verbatim, got {consequent:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 3. Precedence — `implies` is the LOOSEST propositional connective
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn implies_is_looser_than_or_and_and() {
    // `Implies` is declared immediately BEFORE `Or`, and declaration order is
    // loosest → tightest, so:
    //
    //   `false or false implies false and false`
    //     must group   (false or false) implies (false and false)  = F ⇒ F = TRUE
    //     and NOT      false or ((false implies false) and false)  = F ∨ (T ∧ F) = FALSE
    //
    // The two readings DISAGREE, so this one formula pins the precedence.
    assert!(
        machine_verdict("false or false implies false and false").await,
        "`or`/`and` must bind TIGHTER than `implies`"
    );
    // The mirror image: `(true and true) implies (false or true)` = T ⇒ T = TRUE.
    assert!(
        machine_verdict("true and true implies false or true").await,
        "a true antecedent with a true disjunctive consequent must be true"
    );
    // And the falsifying grouping really falsifies: `true implies (false or false)` = T ⇒ F.
    assert!(
        !machine_verdict("true implies false or false").await,
        "a true antecedent with a false disjunctive consequent must be false"
    );
}

#[tokio::test]
async fn comparison_binds_tighter_than_implies() {
    // Comparisons are declared AFTER `implies`, so `a > b implies c > d` needs no
    // parentheses to mean `(a > b) implies (c > d)`. `int(·,8)` keeps the operands
    // in the `GInt` carrier the machine can compare.
    let (folds, observed) = run_with_folds(r#"@"OUT"!(int(3,8) > int(1,8) implies int(3,8) > int(1,8))"#).await;
    assert_eq!(folds, 4, "four `int(·,8)` folds ride the two comparisons");
    assert_eq!(
        observed,
        vec![RuntimeObservationValue::Bool(true)],
        "comparison must bind tighter than `implies`"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// 4. ★ The fold-traversal regression (all THREE helpers)
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn a_fold_nested_inside_an_implies_is_lifted_not_dropped() {
    // ★ The regression this test exists for. `implies` had to be added to ALL
    // THREE fold-traversal helpers in `rhocalc_ast.rs`:
    //
    //   `find_fold`      — finds the innermost liftable fold (miss ⇒ never lifted)
    //   `replace_fold`   — substitutes `*r` for it       (miss ⇒ never trampolined)
    //   `rebuild_binary` — rebuilds the node around `*r` (miss ⇒ substitution discarded)
    //
    // Missing any one of them drops a fold nested inside an implication. The
    // asymmetric shape below (a fold on ONE side only) pins the traversal in both
    // operand positions independently.
    let (folds, observed) = run_with_folds(r#"@"OUT"!(true implies int(3,8) > int(1,8))"#).await;
    assert_eq!(folds, 2, "a fold in the CONSEQUENT must be found and lifted");
    assert_eq!(observed, vec![RuntimeObservationValue::Bool(true)], "T ⇒ T = true");

    let (folds, observed) = run_with_folds(r#"@"OUT"!(int(0,8) > int(1,8) implies false)"#).await;
    assert_eq!(folds, 2, "a fold in the ANTECEDENT must be found and lifted");
    assert_eq!(observed, vec![RuntimeObservationValue::Bool(true)], "F ⇒ F = true");

    // Nested one level deeper, under an `and` inside the implication: the
    // traversal must recurse, not merely inspect the implication's own operands.
    let (folds, observed) =
        run_with_folds(r#"@"OUT"!(true implies true and int(3,8) > int(1,8))"#).await;
    assert_eq!(folds, 2, "a fold nested under `and` under `implies` must still lift");
    assert_eq!(observed, vec![RuntimeObservationValue::Bool(true)], "T ⇒ (T ∧ T) = true");
}

// ══════════════════════════════════════════════════════════════════════════════
// 5. Guard position — commit, and the fail-SHUT contract
// ══════════════════════════════════════════════════════════════════════════════

/// `x > "m" implies x > "s"` is the ordered analogue of the numeric
/// `x > 0 implies x > 10`: `"z"` satisfies both comparisons, `"p"` satisfies only
/// the antecedent, `"a"` satisfies neither.
const ORDERED_GUARD: &str = r#"x > "m" implies x > "s""#;

#[tokio::test]
async fn implies_guard_fires_on_a_satisfying_datum() {
    // "z" > "m" is true and "z" > "s" is true ⇒ T ⇒ T = true.
    let (fired, resting) = guarded_receive(ORDERED_GUARD, r#""z""#).await;
    assert_eq!(fired, vec![r#""z""#.to_string()], "a satisfied implication must commit the receive");
    assert!(resting.is_empty(), "a committed receive consumes its datum");
}

#[tokio::test]
async fn implies_guard_blocks_and_leaves_the_datum_resting() {
    // "p" > "m" is true but "p" > "s" is false ⇒ T ⇒ F = false.
    //
    // §18.5's fail-SHUT contract on the real reducer: a false guard consumes
    // nothing and fabricates nothing. Both halves are read from ONE quiescent
    // store, so they are asserted to hold TOGETHER.
    let (fired, resting) = guarded_receive(ORDERED_GUARD, r#""p""#).await;
    assert!(fired.is_empty(), "a falsified implication must not emit the guarded body");
    assert_eq!(
        resting,
        vec![r#""p""#.to_string()],
        "a falsified implication must leave the rejected datum resting"
    );
}

#[tokio::test]
async fn implies_guard_is_vacuously_true_on_a_false_antecedent() {
    // "a" > "m" is false ⇒ `false ⇒ anything` = true (ex falso quodlibet). This is
    // the row that distinguishes `⇒` from `∧`: a conjunctive reading would block.
    let (fired, resting) = guarded_receive(ORDERED_GUARD, r#""a""#).await;
    assert_eq!(fired, vec![r#""a""#.to_string()], "a vacuously-true implication must commit");
    assert!(resting.is_empty(), "a committed receive consumes its datum");
}

#[tokio::test]
async fn a_closed_false_implication_guard_leaves_the_datum_resting() {
    // The guard need not mention the bound variable at all: `true implies false`
    // is closed and false, so the receive never commits.
    let (fired, resting) = guarded_receive("true implies false", r#""a""#).await;
    assert!(fired.is_empty(), "a closed false implication must not commit");
    assert_eq!(resting, vec![r#""a""#.to_string()], "and must leave the datum resting");

    let (fired, resting) = guarded_receive("false implies false", r#""a""#).await;
    assert_eq!(fired, vec![r#""a""#.to_string()], "a closed true implication must commit");
    assert!(resting.is_empty(), "a committed receive consumes its datum");
}

// ══════════════════════════════════════════════════════════════════════════════
// 6. A failed operator must never invent a value
// ══════════════════════════════════════════════════════════════════════════════

#[tokio::test]
async fn implies_over_a_non_boolean_operand_fabricates_nothing() {
    // Both operands ground but not `bool` ⇒ the operator is genuinely undefined
    // at those types. The host `![…]` fold answers `error`; on the machine the
    // `ENot` of a `GBigInt` raises `EvalError`, which §18.5 collapses to
    // guard-fail. Either way the observable contract is the one that matters: no
    // commit, and the datum stays resting. Nothing is fabricated.
    let (fired, resting) = guarded_receive("1 implies 2", r#""a""#).await;
    assert!(fired.is_empty(), "a type-erroneous implication must not commit");
    assert_eq!(
        resting,
        vec![r#""a""#.to_string()],
        "a type-erroneous implication must leave the datum resting"
    );
}

/// `RuntimeObservationValue::BigIntBytes` renders as signed big-endian hex, so a
/// RhoCalc **`…n`** literal `11n` observes as `BigInt(0x0b)`. A PLAIN `11` now
/// observes as the `GInt` `11` (divergence I).
const BIGINT_ELEVEN: &str = "BigInt(0x0b)";

/// ★ INVERTED 2026-07-25 (divergence I). This test was
/// `a_bigint_comparison_guard_fails_shut_pre_existing`, and it pinned a REAL
/// defect that this suite's ordered-`Str` guards existed to route around: a plain
/// RhoCalc integer literal lowered to `GBigInt`, `rho-pure-eval`'s `cmp_binop`
/// (`eval.rs`) admits only `(GInt,GInt)`, `(GString,GString)`, `(GBool,GBool)`,
/// so a numeric guard as ordinary as `where x > 0` raised `EvalError` and §18.5
/// collapsed that to guard-FAIL. Every numeric guard in the language failed shut.
///
/// A plain literal is now `GInt` — its `normalize_ground` carrier — so numeric
/// guards WORK. The `GBigInt` half of the pin survives below, because
/// `cmp_binop` still does not admit `GBigInt`: the `…n` spelling still fails
/// shut, and a future widening of `cmp_binop` must fail this test loudly rather
/// than change consensus-visible guard behaviour silently.
#[tokio::test]
async fn a_plain_integer_comparison_guard_now_fires_and_the_bigint_one_still_fails_shut() {
    // ── the INVERTED half: a plain numeric guard fires. ──
    let (fired, resting) = guarded_receive("x > 0", "11").await;
    assert_eq!(
        fired,
        vec!["11".to_string()],
        "a plain (GInt) comparison guard now FIRES — this was the defect divergence I closed"
    );
    assert!(resting.is_empty(), "and consumes the datum");

    let (fired, _resting) = guarded_receive("x > 0 implies x > 10", "11").await;
    assert_eq!(
        fired,
        vec!["11".to_string()],
        "`implies` over plain numeric comparisons composes: `11 > 0 ⇒ 11 > 10` is true"
    );

    // …and the guard can still answer FALSE, so the firing above is not vacuous.
    let (fired, resting) = guarded_receive("x > 100", "11").await;
    assert!(fired.is_empty(), "a false numeric guard still fails shut");
    assert_eq!(resting, vec!["11".to_string()], "and leaves the datum resting");

    // ── the SURVIVING half: `cmp_binop` still has no `GBigInt` arm. ──
    let (fired, resting) = guarded_receive("x > 0n", "11n").await;
    assert!(
        fired.is_empty(),
        "a GBigInt comparison guard still fails shut — `cmp_binop` has no `(GBigInt,GBigInt)` arm"
    );
    assert_eq!(resting, vec![BIGINT_ELEVEN.to_string()], "and leaves the datum resting");
}
