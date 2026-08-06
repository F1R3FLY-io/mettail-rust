use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use mettail_prattail::lattice_theory::{LatticeStore, LatticeTheory};
use mettail_prattail::symbolic::BooleanAlgebra;
use mettail_prattail::type_system::{LatticeTypeSystem, TypePred, TypeSystemAlgebra};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum RecursiveOracle {
    True,
    False,
    HasType(usize),
    Subtype { sub: usize, sup: usize },
    And(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Or(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Not(Box<RecursiveOracle>),
}

fn algebra() -> TypeSystemAlgebra<LatticeTypeSystem> {
    let theory = LatticeTheory::new(vec![0, 1], HashMap::new());
    let mut store = LatticeStore::new();
    store.add_edge(0, 1);
    TypeSystemAlgebra::new(LatticeTypeSystem::with_bounds(theory, store, HashMap::new(), 1, 0))
}

fn nested_not(depth: usize) -> TypePred<LatticeTypeSystem> {
    let mut pred = TypePred::True;
    for _ in 0..depth {
        pred = TypePred::Not(Box::new(pred));
    }
    pred
}

#[test]
fn type_predicate_lifecycle_matches_the_recursive_derive_oracle() {
    let actual: TypePred<LatticeTypeSystem> = TypePred::And(
        Box::new(TypePred::HasType(1)),
        Box::new(TypePred::Not(Box::new(TypePred::Subtype { sub: 0, sup: 1 }))),
    );
    let oracle = RecursiveOracle::And(
        Box::new(RecursiveOracle::HasType(1)),
        Box::new(RecursiveOracle::Not(Box::new(RecursiveOracle::Subtype { sub: 0, sup: 1 }))),
    );

    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));
    let mut actual_hash = DefaultHasher::new();
    actual.hash(&mut actual_hash);
    let mut oracle_hash = DefaultHasher::new();
    oracle.hash(&mut oracle_hash);
    assert_eq!(actual_hash.finish(), oracle_hash.finish());
    assert_eq!(actual, actual.clone());
}

#[test]
fn type_predicate_lifecycle_and_deciders_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let algebra = algebra();
            let pred = nested_not(DEPTH);
            let cloned = pred.clone();
            assert_eq!(pred, cloned);

            let mut left_hash = DefaultHasher::new();
            pred.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            assert!(format!("{pred:?}").starts_with("Not(Not(Not("));

            assert!(algebra.evaluate_pred(&pred));
            assert!(algebra.is_satisfiable_pred(&pred));
            assert!(algebra.evaluate(&pred, &0));
            assert_eq!(algebra.witness(&pred), Some(1));

            drop(cloned);
            drop(pred);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("type-predicate stack-safety gate");
}
