use mettail_prattail::product_nary::{
    NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue,
};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("product-nary-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn N-ary product/sum small-stack gate")
        .join()
        .expect("N-ary product/sum small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn product_atom() -> NaryProductPred<IntervalPred> {
    NaryProductPred::Field(0, IntervalPred::Range(10, 20))
}

fn deep_product_conjunction() -> NaryProductPred<IntervalPred> {
    let mut predicate = product_atom();
    for _ in 0..DEPTH {
        predicate = NaryProductPred::And(Box::new(predicate), Box::new(product_atom()));
    }
    predicate
}

fn deep_product_negation() -> NaryProductPred<IntervalPred> {
    let mut predicate = product_atom();
    for _ in 0..DEPTH {
        predicate = NaryProductPred::Not(Box::new(predicate));
    }
    predicate
}

fn sum_atom() -> SumPred<IntervalPred> {
    SumPred::InVariant(0, IntervalPred::Range(10, 20))
}

fn deep_sum_conjunction() -> SumPred<IntervalPred> {
    let mut predicate = sum_atom();
    for _ in 0..DEPTH {
        predicate = SumPred::And(Box::new(predicate), Box::new(sum_atom()));
    }
    predicate
}

fn deep_sum_negation() -> SumPred<IntervalPred> {
    let mut predicate = sum_atom();
    for _ in 0..DEPTH {
        predicate = SumPred::Not(Box::new(predicate));
    }
    predicate
}

#[test]
fn nary_product_lifecycle_dnf_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra = NaryProductAlgebra::new(vec![IntervalAlgebra::new(0, 100)]);
        let predicate = deep_product_conjunction();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));
        assert!(algebra.evaluate(&predicate, &vec![15]));
        assert!(!algebra.evaluate(&predicate, &vec![25]));
        assert!(algebra.is_satisfiable(&predicate));
        assert_eq!(algebra.witness(&predicate), Some(vec![10]));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with("))"));
        drop(cloned);
        drop(predicate);

        let negation = deep_product_negation();
        assert!(algebra.is_satisfiable(&negation));
        assert!(algebra.evaluate(&negation, &vec![15]));
        drop(negation);
    });
}

#[test]
fn sum_lifecycle_projection_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra = SumAlgebra::new(vec![IntervalAlgebra::new(0, 100)]);
        let predicate = deep_sum_conjunction();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));
        assert!(algebra.evaluate(&predicate, &SumValue { tag: 0, payload: 15 }));
        assert!(!algebra.evaluate(&predicate, &SumValue { tag: 0, payload: 25 }));
        assert!(algebra.is_satisfiable(&predicate));
        let witness = algebra
            .witness(&predicate)
            .expect("deep sum predicate has a witness");
        assert_eq!((witness.tag, witness.payload), (0, 10));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with("))"));
        drop(cloned);
        drop(predicate);

        let negation = deep_sum_negation();
        assert!(algebra.is_satisfiable(&negation));
        assert!(algebra.evaluate(&negation, &SumValue { tag: 0, payload: 15 }));
        drop(negation);
    });
}

#[test]
fn nary_product_and_sum_debug_preserve_compact_derived_contracts() {
    let product = NaryProductPred::Not(Box::new(NaryProductPred::Or(
        Box::new(NaryProductPred::Field(0, IntervalPred::Range(1, 3))),
        Box::new(NaryProductPred::False),
    )));
    assert_eq!(format!("{product:?}"), "Not(Or(Field(0, Range(1, 3)), False))");

    let sum = SumPred::Not(Box::new(SumPred::And(
        Box::new(SumPred::TagIs(1)),
        Box::new(SumPred::InVariant(1, IntervalPred::Range(4, 6))),
    )));
    assert_eq!(format!("{sum:?}"), "Not(And(TagIs(1), InVariant(1, Range(4, 6))))");
}
