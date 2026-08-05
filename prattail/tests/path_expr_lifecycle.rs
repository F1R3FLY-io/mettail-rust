use mettail_prattail::algebraic::{evaluate, PathExpr};
use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn path_expression_lifecycle_and_evaluator_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("path-expression-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut expr = PathExpr::Atom(BooleanWeight::one());
            for _ in 0..DEPTH {
                expr = PathExpr::Star(Box::new(expr));
            }

            let cloned = expr.clone();
            assert_eq!(evaluate(&expr), BooleanWeight::one());
            assert_eq!(evaluate(&cloned), BooleanWeight::one());
            let debug = format!("{expr:?}");
            assert!(debug.starts_with("Star(Star("));
            assert!(debug.ends_with(&")".repeat(DEPTH)));

            drop(cloned);
            drop(expr);
        })
        .expect("spawn path-expression small-stack gate")
        .join()
        .expect("path-expression small-stack gate panicked");
}

#[test]
fn path_expression_debug_preserves_the_compact_derived_contract() {
    let expr = PathExpr::Alt(
        Box::new(PathExpr::Seq(
            Box::new(PathExpr::Atom(BooleanWeight::one())),
            Box::new(PathExpr::Zero),
        )),
        Box::new(PathExpr::Star(Box::new(PathExpr::One))),
    );
    assert_eq!(format!("{expr:?}"), "Alt(Seq(Atom(BooleanWeight(true)), Zero), Star(One))");
}
