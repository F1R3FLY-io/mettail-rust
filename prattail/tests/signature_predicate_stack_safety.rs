use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_prattail::predicate_dispatch::{PredicateSignature, SignaturePred};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum RecursiveOracle {
    True,
    False,
    HasBit(u16),
    And(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Or(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Not(Box<RecursiveOracle>),
}

fn nested(depth: usize) -> SignaturePred {
    let mut pred = SignaturePred::HasBit(1);
    for index in 0..depth {
        pred = if index % 2 == 0 {
            SignaturePred::Not(Box::new(pred))
        } else {
            SignaturePred::And(Box::new(SignaturePred::True), Box::new(pred))
        };
    }
    pred
}

fn shallow_pair() -> (SignaturePred, RecursiveOracle) {
    (
        SignaturePred::And(
            Box::new(SignaturePred::HasBit(4)),
            Box::new(SignaturePred::Not(Box::new(SignaturePred::Or(
                Box::new(SignaturePred::True),
                Box::new(SignaturePred::False),
            )))),
        ),
        RecursiveOracle::And(
            Box::new(RecursiveOracle::HasBit(4)),
            Box::new(RecursiveOracle::Not(Box::new(RecursiveOracle::Or(
                Box::new(RecursiveOracle::True),
                Box::new(RecursiveOracle::False),
            )))),
        ),
    )
}

#[test]
fn signature_predicate_lifecycle_matches_the_recursive_derive_oracle() {
    let (pred, oracle) = shallow_pair();
    assert_eq!(format!("{pred:?}"), format!("{oracle:?}"));

    let mut actual_hash = DefaultHasher::new();
    pred.hash(&mut actual_hash);
    let mut oracle_hash = DefaultHasher::new();
    oracle.hash(&mut oracle_hash);
    assert_eq!(actual_hash.finish(), oracle_hash.finish());

    let cloned = pred.clone();
    assert_eq!(pred, cloned);
    assert_ne!(pred, SignaturePred::False);
}

#[test]
fn signature_predicate_lifecycle_and_evaluation_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let pred = nested(DEPTH);
            let cloned = pred.clone();
            assert_eq!(pred, cloned);

            let mut left_hash = DefaultHasher::new();
            pred.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());

            let rendered = format!("{pred:?}");
            assert!(rendered.starts_with("And(True, Not("));
            assert!(rendered.ends_with(')'));

            let signature = PredicateSignature::from_raw(1);
            assert_eq!(pred.eval(signature), cloned.eval(signature));
            drop(cloned);
            drop(pred);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("signature predicate stack-safety gate");
}
