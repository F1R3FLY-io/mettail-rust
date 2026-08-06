use mettail_prattail::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("collection-predicate-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn collection predicate small-stack gate")
        .join()
        .expect("collection predicate small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn bag_atom() -> BagPred<IntervalPred> {
    BagPred::Count {
        class: IntervalPred::Range(10, 20),
        lo: 1,
        hi: None,
    }
}

fn deep_bag_conjunction() -> BagPred<IntervalPred> {
    let mut predicate = bag_atom();
    for _ in 0..DEPTH {
        predicate = BagPred::And(Box::new(predicate), Box::new(bag_atom()));
    }
    predicate
}

fn deep_bag_negation() -> BagPred<IntervalPred> {
    let mut predicate = bag_atom();
    for _ in 0..DEPTH {
        predicate = BagPred::Not(Box::new(predicate));
    }
    predicate
}

fn map_atom() -> MapPred<IntervalPred, IntervalPred> {
    MapPred::CountEntries {
        key_class: IntervalPred::Range(10, 20),
        val_class: IntervalPred::Range(30, 40),
        lo: 1,
        hi: None,
    }
}

fn deep_map_conjunction() -> MapPred<IntervalPred, IntervalPred> {
    let mut predicate = map_atom();
    for _ in 0..DEPTH {
        predicate = MapPred::And(Box::new(predicate), Box::new(map_atom()));
    }
    predicate
}

fn deep_map_negation() -> MapPred<IntervalPred, IntervalPred> {
    let mut predicate = map_atom();
    for _ in 0..DEPTH {
        predicate = MapPred::Not(Box::new(predicate));
    }
    predicate
}

#[test]
fn bag_lifecycle_count_search_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra = BagAlgebra::new(IntervalAlgebra::new(0, 100));
        let predicate = deep_bag_conjunction();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));
        assert!(algebra.evaluate(&predicate, &vec![15]));
        assert!(!algebra.evaluate(&predicate, &vec![25]));
        assert!(algebra.is_satisfiable(&predicate));
        let witness = algebra
            .witness(&predicate)
            .expect("deep bag predicate has a witness");
        assert!(algebra.evaluate(&predicate, &witness));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with(" })"));
        drop(cloned);
        drop(predicate);

        let negation = deep_bag_negation();
        assert!(algebra.is_satisfiable(&negation));
        assert!(algebra.evaluate(&negation, &vec![15]));
        drop(negation);
    });
}

#[test]
fn map_lifecycle_count_search_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra = MapAlgebra::new(IntervalAlgebra::new(0, 100), IntervalAlgebra::new(0, 100));
        let predicate = deep_map_conjunction();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));
        assert!(algebra.evaluate(&predicate, &vec![(15, 35)]));
        assert!(!algebra.evaluate(&predicate, &vec![(15, 45)]));
        assert!(algebra.is_satisfiable(&predicate));
        let witness = algebra
            .witness(&predicate)
            .expect("deep map predicate has a witness");
        assert!(algebra.evaluate(&predicate, &witness));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with(" })"));
        drop(cloned);
        drop(predicate);

        let negation = deep_map_negation();
        assert!(algebra.is_satisfiable(&negation));
        assert!(algebra.evaluate(&negation, &vec![(15, 35)]));
        drop(negation);
    });
}

#[test]
fn bag_and_map_debug_preserve_compact_derived_contracts() {
    let bag = BagPred::Not(Box::new(BagPred::Count {
        class: IntervalPred::Range(1, 3),
        lo: 2,
        hi: Some(4),
    }));
    assert_eq!(format!("{bag:?}"), "Not(Count { class: Range(1, 3), lo: 2, hi: Some(4) })");

    let map = MapPred::Not(Box::new(MapPred::CountEntries {
        key_class: IntervalPred::Range(1, 3),
        val_class: IntervalPred::Range(4, 6),
        lo: 2,
        hi: Some(4),
    }));
    assert_eq!(
        format!("{map:?}"),
        "Not(CountEntries { key_class: Range(1, 3), val_class: Range(4, 6), lo: 2, hi: Some(4) })"
    );
}
