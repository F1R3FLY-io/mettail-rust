//! Phase F.13 chain_10000 Plan v6 H3 correctness (2026-05-27): verify
//! the Earley chain-absorption fast path (H3) produces a parse that
//! EVALUATES correctly — not just `is_ok()`.
//!
//! Why this file exists: the `test_left_assoc_chain_*` trampoline tests
//! only assert `result.is_ok()`, and the generated `gen_calculator_op`
//! eval tests use < 4-atom expressions that never trigger H3's
//! `≥ 4 atoms` peek-ahead gate. So H3's chain-AST correctness was
//! UNVERIFIED. These tests parse chains ≥ 4 atoms (which DO trigger H3)
//! and assert the evaluated normal form, catching any degenerate /
//! atom-dropping / wrong-structure parse that `is_ok()` would miss.
//!
//! H3 mechanism (wpda_walker.rs IterativeChainAbsorb arm): when
//! peek-ahead detects ≥ 4 atoms, invoke `earley_outboard_chain` which
//! recognizes the chain + emits the SPPF subforest using the walker's
//! own AddInt rule metadata, then jump the cursor to chain_end. If the
//! emitted SPPF folds the atoms incorrectly, the sum is wrong.

use mettail_languages::calculator::*;
use mettail_runtime::Language;

/// Evaluate a Calculator source string and return the set of normal-form
/// display strings.
fn eval_calc(input: &str) -> Vec<String> {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse of {:?} should succeed: {:?}", input, e));
    let results = lang
        .run_ascent(parsed.as_ref())
        .unwrap_or_else(|e| panic!("eval of {:?} should succeed: {:?}", input, e));
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
}

#[test]
fn h3_chain_5_ones_evals_to_5() {
    // 5 atoms, 4 ops → triggers H3 (peek-ahead ≥ 4 atoms).
    let nfs = eval_calc("1 + 1 + 1 + 1 + 1");
    assert!(
        nfs.iter().any(|d| d == "5"),
        "1+1+1+1+1 should eval to 5 (H3 chain absorption correctness), got {:?}",
        nfs
    );
}

#[test]
fn h3_chain_10_ones_evals_to_10() {
    // 10 atoms → well past the H3 gate.
    let nfs = eval_calc("1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1");
    assert!(
        nfs.iter().any(|d| d == "10"),
        "ten 1s summed should eval to 10, got {:?}",
        nfs
    );
}

#[test]
fn h3_chain_mixed_values_evals_correctly() {
    // Distinct atom values + ≥ 4 atoms → triggers H3 AND detects
    // atom-dropping (a degenerate parse that drops or reorders atoms
    // would not sum to 15). 1+2+3+4+5 = 15.
    let nfs = eval_calc("1 + 2 + 3 + 4 + 5");
    assert!(
        nfs.iter().any(|d| d == "15"),
        "1+2+3+4+5 should eval to 15 (detects atom-drop/reorder), got {:?}",
        nfs
    );
}

#[test]
fn h3_chain_below_gate_control_evals_to_3() {
    // 3 atoms — BELOW the H3 ≥ 4-atom gate. Control: confirms the
    // non-H3 (pure WPDS) path still evals correctly, isolating H3 as
    // the only variable between this and the ≥ 4-atom cases.
    let nfs = eval_calc("1 + 1 + 1");
    assert!(
        nfs.iter().any(|d| d == "3"),
        "1+1+1 (below H3 gate) should eval to 3, got {:?}",
        nfs
    );
}
