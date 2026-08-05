use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::cra::{evaluate_stream, CostRegisterAutomaton, CraTransition, RegisterExpr};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn register_expression_lifecycle_and_evaluator_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("register-expression-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut expr = RegisterExpr::InputCost;
            for _ in 0..DEPTH {
                expr = RegisterExpr::Plus(Box::new(expr), Box::new(RegisterExpr::Zero));
            }

            let cloned = expr.clone();
            assert_eq!(expr, cloned);
            assert!(expr.to_string().starts_with(&"(".repeat(DEPTH)));
            assert!(format!("{expr:?}").starts_with("Plus(Plus("));

            let mut cra = CostRegisterAutomaton::<BooleanWeight>::new(1, 1);
            cra.set_output_register(0, 0);
            cra.add_transition(CraTransition {
                from: 0,
                to: 0,
                guard: Some("a".to_string()),
                updates: [(0, cloned)].into_iter().collect(),
            });
            let result = evaluate_stream(&cra, &[("a".to_string(), BooleanWeight::one())]);
            assert_eq!(result, BooleanWeight::one());

            drop(expr);
            drop(cra);
        })
        .expect("spawn register-expression small-stack gate")
        .join()
        .expect("register-expression small-stack gate panicked");
}

#[test]
fn register_expression_formatting_preserves_compact_contracts() {
    let expr = RegisterExpr::plus(
        RegisterExpr::reg(2),
        RegisterExpr::times(RegisterExpr::InputCost, RegisterExpr::One),
    );
    assert_eq!(expr.to_string(), "(r2 + (cost * 1))");
    assert_eq!(format!("{expr:?}"), "Plus(Reg(Register { index: 2 }), Times(InputCost, One))");
}
