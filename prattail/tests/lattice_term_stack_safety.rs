use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use mettail_prattail::lattice_theory::{LatticeStore, LatticeTheory};
use mettail_prattail::type_system::{LatticeTerm, LatticeTypeSystem, TypeSystem};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum RecursiveOracle {
    Var(String),
    Const { name: String, ty: usize },
    App { head: String, args: Vec<RecursiveOracle> },
}

fn nested(depth: usize) -> LatticeTerm {
    let mut term = LatticeTerm::Const { name: "leaf".into(), ty: 0 };
    for _ in 0..depth {
        term = LatticeTerm::App { head: "wrap".into(), args: vec![term] };
    }
    term
}

#[test]
fn lattice_term_lifecycle_matches_the_recursive_derive_oracle() {
    let actual = LatticeTerm::App {
        head: "pair".into(),
        args: vec![LatticeTerm::Var("x".into()), LatticeTerm::Const { name: "leaf".into(), ty: 7 }],
    };
    let oracle = RecursiveOracle::App {
        head: "pair".into(),
        args: vec![
            RecursiveOracle::Var("x".into()),
            RecursiveOracle::Const { name: "leaf".into(), ty: 7 },
        ],
    };
    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));

    let mut actual_hash = DefaultHasher::new();
    actual.hash(&mut actual_hash);
    let mut oracle_hash = DefaultHasher::new();
    oracle.hash(&mut oracle_hash);
    assert_eq!(actual_hash.finish(), oracle_hash.finish());
    assert_eq!(actual, actual.clone());
}

#[test]
fn lattice_term_lifecycle_and_inference_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let term = nested(DEPTH);
            let cloned = term.clone();
            assert_eq!(term, cloned);

            let mut left_hash = DefaultHasher::new();
            term.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            assert!(format!("{term:?}").starts_with("App { head: \"wrap\", args: ["));

            let theory = LatticeTheory::new(vec![0], HashMap::new());
            let store = LatticeStore::new();
            let mut constructors = HashMap::new();
            constructors.insert("wrap".into(), (vec![0], 0));
            let system = LatticeTypeSystem::new(theory, store, constructors);
            assert_eq!(system.infer(&system.empty_env(), &term), vec![0]);

            drop(cloned);
            drop(term);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("lattice term stack-safety gate");
}
