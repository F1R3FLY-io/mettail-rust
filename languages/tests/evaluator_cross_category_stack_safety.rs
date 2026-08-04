//! Regression and executable-equivalence gates for native-category evaluator cycles.
//!
//! The production evaluator is generated as one typed pushdown machine per SCC of
//! the native-category dependency graph. These small recursive functions are a
//! test-only semantic oracle for the constructors that witness the two bundled
//! cycles. They are intentionally exercised only at shallow depths; the generated
//! machine is then exercised at a depth that would overflow a recursive evaluator.

use std::sync::Arc;
use std::{fs, path::PathBuf};

use mettail_languages::calculator::{Bool as CalcBool, Int as CalcInt};

#[path = "definitions/led_test.rs"]
mod led_test;

fn calculator_int_oracle(term: &CalcInt) -> Option<i32> {
    match term {
        CalcInt::NumLit(value) => Some(*value),
        CalcInt::BoolToInt(value) => {
            calculator_bool_oracle(value).map(|value| if value { 1 } else { 0 })
        },
        _ => None,
    }
}

fn calculator_bool_oracle(term: &CalcBool) -> Option<bool> {
    match term {
        CalcBool::BoolLit(value) => Some(*value),
        CalcBool::EqInt(left, right) => {
            Some(calculator_int_oracle(left)? == calculator_int_oracle(right)?)
        },
        _ => None,
    }
}

fn calculator_cycle(depth: usize) -> CalcInt {
    let mut term = CalcInt::NumLit(0);
    for _ in 0..depth {
        term = CalcInt::BoolToInt(Arc::new(CalcBool::EqInt(
            Arc::new(term),
            Arc::new(CalcInt::NumLit(0)),
        )));
    }
    term
}

#[test]
fn calculator_pda_matches_recursive_oracle_on_cycle_prefixes() {
    for depth in 0..=256 {
        let term = calculator_cycle(depth);
        assert_eq!(term.try_eval(), calculator_int_oracle(&term), "depth {depth}");
    }
}

#[test]
fn calculator_cross_category_cycle_is_stack_safe_at_20000_edges() {
    // Each layer crosses Int → Bool → Int, so this is 20,000 cyclic category
    // edges.  A deliberately small ordinary Rust stack is a stricter gate
    // than relying on the test harness default and rules out RUST_MIN_STACK,
    // stacker, or any equivalent accommodation.
    std::thread::Builder::new()
        .name("calculator-evaluator-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| assert_eq!(calculator_cycle(10_000).try_eval(), Some(0)))
        .expect("spawn Calculator small-stack regression")
        .join()
        .expect("Calculator evaluator must not overflow or panic");
}

fn led_num_oracle(term: &led_test::Num) -> Option<i32> {
    match term {
        led_test::Num::NumLit(value) => Some(*value),
        led_test::Num::PredToNum(value) => {
            led_pred_oracle(value).map(|value| if value { 1 } else { 0 })
        },
        _ => None,
    }
}

fn led_pred_oracle(term: &led_test::Pred) -> Option<bool> {
    match term {
        led_test::Pred::BoolLit(value) => Some(*value),
        led_test::Pred::EqNum(left, right) => Some(led_num_oracle(left)? == led_num_oracle(right)?),
        _ => None,
    }
}

fn led_cycle(depth: usize) -> led_test::Num {
    let mut term = led_test::Num::NumLit(0);
    for _ in 0..depth {
        term = led_test::Num::PredToNum(Arc::new(led_test::Pred::EqNum(
            Arc::new(term),
            Arc::new(led_test::Num::NumLit(0)),
        )));
    }
    term
}

#[test]
fn ledtest_pda_matches_recursive_oracle_on_cycle_prefixes() {
    for depth in 0..=256 {
        let term = led_cycle(depth);
        assert_eq!(term.try_eval(), led_num_oracle(&term), "depth {depth}");
    }
}

#[test]
fn ledtest_cross_category_cycle_is_stack_safe_at_20000_edges() {
    std::thread::Builder::new()
        .name("ledtest-evaluator-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| assert_eq!(led_cycle(10_000).try_eval(), Some(0)))
        .expect("spawn LedTest small-stack regression")
        .join()
        .expect("LedTest evaluator must not overflow or panic");
}

fn compact_generated_eval(language: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("languages crate has a workspace parent")
        .join("target/generated")
        .join(language)
        .join("eval.rs");
    fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

fn constructor_window<'a>(source: &'a str, constructor: &str) -> &'a str {
    let start = source
        .find(constructor)
        .unwrap_or_else(|| panic!("missing generated constructor arm {constructor}"));
    &source[start..source.len().min(start + 700)]
}

#[test]
fn generated_cycle_edges_are_pda_visits_not_host_calls() {
    let calculator = compact_generated_eval("calculator");
    let int_to_bool = constructor_window(&calculator, "Int::BoolToInt(");
    assert!(int_to_bool.contains("::VisitBool("), "BoolToInt must schedule Bool");
    assert!(!int_to_bool.contains(".try_eval()?"), "BoolToInt must not recurse on the host");

    let bool_to_int = constructor_window(&calculator, "Bool::EqInt(");
    assert!(bool_to_int.matches("::VisitInt(").count() >= 2, "EqInt must schedule both Ints");
    assert!(!bool_to_int.contains(".try_eval()?"), "EqInt must not recurse on the host");

    let ledtest = compact_generated_eval("ledtest");
    let num_to_pred = constructor_window(&ledtest, "Num::PredToNum(");
    assert!(num_to_pred.contains("::VisitPred("), "PredToNum must schedule Pred");
    assert!(!num_to_pred.contains(".try_eval()?"), "PredToNum must not recurse on the host");

    let pred_to_num = constructor_window(&ledtest, "Pred::EqNum(");
    assert!(pred_to_num.matches("::VisitNum(").count() >= 2, "EqNum must schedule both Nums");
    assert!(!pred_to_num.contains(".try_eval()?"), "EqNum must not recurse on the host");
}
