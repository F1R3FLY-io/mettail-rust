use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use mettail_prattail::type_system::{SetTheoreticTypeSystem, SetType, TypeSystem};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum RecursiveOracle {
    Atom(String),
    Union(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Intersection(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Negation(Box<RecursiveOracle>),
    Arrow(Box<RecursiveOracle>, Box<RecursiveOracle>),
    Top,
    Bottom,
}

fn nested_union(depth: usize) -> SetType {
    let mut ty = SetType::Atom("leaf".into());
    for _ in 0..depth {
        ty = SetType::Union(Box::new(SetType::Bottom), Box::new(ty));
    }
    ty
}

#[test]
fn set_type_lifecycle_matches_the_recursive_derive_and_display_oracles() {
    let actual = SetType::Arrow(
        Box::new(SetType::Intersection(
            Box::new(SetType::Atom("A".into())),
            Box::new(SetType::Negation(Box::new(SetType::Atom("B".into())))),
        )),
        Box::new(SetType::Top),
    );
    let oracle = RecursiveOracle::Arrow(
        Box::new(RecursiveOracle::Intersection(
            Box::new(RecursiveOracle::Atom("A".into())),
            Box::new(RecursiveOracle::Negation(Box::new(RecursiveOracle::Atom("B".into())))),
        )),
        Box::new(RecursiveOracle::Top),
    );

    assert_eq!(format!("{actual:?}"), format!("{oracle:?}"));
    assert_eq!(actual.to_string(), "((A & ~B) -> Top)");
    let mut actual_hash = DefaultHasher::new();
    actual.hash(&mut actual_hash);
    let mut oracle_hash = DefaultHasher::new();
    oracle.hash(&mut oracle_hash);
    assert_eq!(actual_hash.finish(), oracle_hash.finish());
    assert_eq!(actual, actual.clone());
}

#[test]
fn set_type_lifecycle_and_automaton_lowering_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let system = SetTheoreticTypeSystem::new(HashMap::new());
            let ty = nested_union(DEPTH);
            let cloned = ty.clone();
            assert_eq!(ty, cloned);

            let mut left_hash = DefaultHasher::new();
            ty.hash(&mut left_hash);
            let mut right_hash = DefaultHasher::new();
            cloned.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            assert!(format!("{ty:?}").starts_with("Union(Bottom, Union(Bottom,"));
            assert!(ty.to_string().starts_with("(Bottom | (Bottom |"));

            let automaton = system.type_to_automaton(&ty);
            assert_eq!(automaton.num_states(), 0);
            assert!(!system.is_inhabited(&system.empty_env(), &ty));

            drop(cloned);
            drop(ty);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("set-type stack-safety gate");
}
