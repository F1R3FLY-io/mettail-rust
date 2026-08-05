use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_simulation::semiring::FreeExpr;

#[test]
fn free_expression_lifecycle_survives_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("free-expression-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut expression = FreeExpr::gen("x");
            for _ in 0..DEPTH {
                expression = FreeExpr::Plus(Box::new(FreeExpr::Zero), Box::new(expression));
            }

            let cloned = expression.clone();
            assert_eq!(expression, cloned);
            assert_eq!(expression.generator_count(), 1);
            assert_eq!(expression.simplify(), FreeExpr::gen("x"));
            assert!(format!("{expression:?}").ends_with(&")".repeat(DEPTH)));
            assert!(expression.to_string().ends_with(&")".repeat(DEPTH)));

            let mut left_hash = DefaultHasher::new();
            expression.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());

            drop(cloned);
            drop(expression);
        })
        .expect("small-stack worker starts")
        .join()
        .expect("free-expression lifecycle must not overflow the native stack");
}
