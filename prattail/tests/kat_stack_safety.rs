use mettail_prattail::kat::{check_equivalence_bounded, BooleanTest, KatExpr};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("kat-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn KAT small-stack gate")
        .join()
        .expect("KAT small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn deep_test() -> BooleanTest {
    let mut test = BooleanTest::atom("ready");
    for _ in 0..DEPTH {
        test = BooleanTest::not(test);
    }
    test
}

fn deep_program() -> KatExpr {
    let mut expr = KatExpr::action("step");
    for _ in 0..DEPTH {
        expr = KatExpr::star(expr);
    }
    expr
}

#[test]
fn boolean_test_lifecycle_evaluation_and_formatting_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let test = deep_test();
        let cloned = test.clone();
        assert_eq!(test, cloned);
        assert_eq!(hash(&test), hash(&cloned));
        assert_eq!(test.atoms().into_iter().collect::<Vec<_>>(), ["ready"]);

        let display = test.to_string();
        assert_eq!(display.len(), DEPTH + "ready".len());
        assert!(display.ends_with("ready"));
        let debug = format!("{test:?}");
        assert!(debug.starts_with("Not(Not("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let expression = KatExpr::test(test.clone());
        assert!(check_equivalence_bounded(&expression, &expression, 1));

        drop(expression);
        drop(cloned);
        drop(test);
    });
}

#[test]
fn kat_lifecycle_derivative_simplifier_and_formatting_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let left = deep_program();
        let right = deep_program();
        assert_eq!(left, right);
        assert_eq!(hash(&left), hash(&right));

        let cloned = left.clone();
        assert_eq!(left, cloned);
        let display = left.to_string();
        assert_eq!(display.len(), "step".len() + DEPTH);
        assert!(display.starts_with("step"));
        let debug = format!("{left:?}");
        assert!(debug.starts_with("Star(Star("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        // One exact symbolic step reaches nullability, derivative construction,
        // bottom-up simplification, structural equality, hashing, and worklist
        // destruction without relying on the native call stack.
        assert!(check_equivalence_bounded(&left, &right, 1));

        drop(cloned);
        drop(right);
        drop(left);
    });
}

#[test]
fn kat_debug_and_display_preserve_their_compact_contracts() {
    let test = BooleanTest::and(BooleanTest::atom("a"), BooleanTest::not(BooleanTest::atom("b")));
    assert_eq!(format!("{test:?}"), "And(Atom(\"a\"), Not(Atom(\"b\")))");
    assert_eq!(test.to_string(), "(a & ~b)");

    let expr = KatExpr::seq(
        KatExpr::test(test),
        KatExpr::star(KatExpr::alt(KatExpr::action("x"), KatExpr::One)),
    );
    assert_eq!(
        format!("{expr:?}"),
        "Seq(Test(And(Atom(\"a\"), Not(Atom(\"b\")))), Star(Alt(Action(\"x\"), One)))"
    );
    assert_eq!(expr.to_string(), "([(a & ~b)] ; (x + 1)*)");
}
