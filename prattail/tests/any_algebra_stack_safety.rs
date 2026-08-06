use std::collections::{hash_map::DefaultHasher, HashMap, HashSet};
use std::hash::{Hash, Hasher};

use mettail_prattail::any_algebra::{AnyAlgebra, AnyDomain, AnyPred};
use mettail_prattail::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred, Singleton};
use mettail_prattail::product_nary::{
    NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue,
};
use mettail_prattail::regex_sfa::{RegexAlgebra, RegexPred};
use mettail_prattail::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("any-algebra-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn Any* small-stack gate")
        .join()
        .expect("Any* small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn deep_domain() -> AnyDomain {
    let mut domain = AnyDomain::Int(7);
    for depth in 0..DEPTH {
        domain = match depth % 6 {
            0 => AnyDomain::Product(vec![domain]),
            1 => AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: domain })),
            2 => AnyDomain::List(vec![domain]),
            3 => AnyDomain::Bag(vec![domain]),
            4 => AnyDomain::Tree(Box::new(SymTerm {
                constructor: "node".to_string(),
                payload: Some(domain),
                children: Vec::new(),
            })),
            _ => AnyDomain::Map(vec![(AnyDomain::Int(1), domain)]),
        };
    }
    domain
}

fn deep_algebra() -> AnyAlgebra {
    let mut algebra = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
    for depth in 0..DEPTH {
        algebra = match depth % 6 {
            0 => AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![algebra]))),
            1 => AnyAlgebra::Sum(Box::new(SumAlgebra::new(vec![algebra]))),
            2 => AnyAlgebra::List(Box::new(RegexAlgebra::new(algebra))),
            3 => AnyAlgebra::Bag(Box::new(BagAlgebra::new(algebra))),
            4 => AnyAlgebra::Tree(Box::new(TreeAlgebra::new(
                algebra,
                HashMap::new(),
                HashSet::new(),
            ))),
            _ => AnyAlgebra::Map(Box::new(MapAlgebra::new(
                AnyAlgebra::Int(IntervalAlgebra::new(0, 100)),
                algebra,
            ))),
        };
    }
    algebra
}

fn deep_predicate() -> AnyPred {
    let mut predicate = AnyPred::Int(IntervalPred::Range(7, 8));
    for depth in 0..DEPTH {
        predicate = match depth % 7 {
            0 => AnyPred::Not(Box::new(predicate)),
            1 => AnyPred::Product(Box::new(NaryProductPred::Field(0, predicate))),
            2 => AnyPred::Sum(Box::new(SumPred::InVariant(0, predicate))),
            3 => AnyPred::List(Box::new(RegexPred::Elem(predicate))),
            4 => AnyPred::Bag(Box::new(BagPred::Count { class: predicate, lo: 1, hi: Some(1) })),
            5 => AnyPred::Tree(Box::new(TreePred::Node {
                constructor: "node".to_string(),
                payload_guard: Some(predicate),
                children: Vec::new(),
            })),
            _ => AnyPred::Map(Box::new(MapPred::CountEntries {
                key_class: AnyPred::Int(IntervalPred::Range(1, 2)),
                val_class: predicate,
                lo: 1,
                hi: Some(1),
            })),
        };
    }
    predicate
}

fn deep_evaluation_case() -> (AnyAlgebra, AnyPred, AnyDomain) {
    let mut algebra = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
    let mut predicate = AnyPred::Int(IntervalPred::Range(7, 8));
    let mut domain = AnyDomain::Int(7);
    for depth in 0..DEPTH {
        match depth % 6 {
            0 => {
                algebra = AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![algebra])));
                predicate = AnyPred::Product(Box::new(NaryProductPred::Field(0, predicate)));
                domain = AnyDomain::Product(vec![domain]);
            },
            1 => {
                algebra = AnyAlgebra::Sum(Box::new(SumAlgebra::new(vec![algebra])));
                predicate = AnyPred::Sum(Box::new(SumPred::InVariant(0, predicate)));
                domain = AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: domain }));
            },
            2 => {
                algebra = AnyAlgebra::List(Box::new(RegexAlgebra::new(algebra)));
                predicate = AnyPred::List(Box::new(RegexPred::Elem(predicate)));
                domain = AnyDomain::List(vec![domain]);
            },
            3 => {
                algebra = AnyAlgebra::Bag(Box::new(BagAlgebra::new(algebra)));
                predicate =
                    AnyPred::Bag(Box::new(BagPred::Count { class: predicate, lo: 1, hi: Some(1) }));
                domain = AnyDomain::Bag(vec![domain]);
            },
            4 => {
                algebra = AnyAlgebra::Tree(Box::new(TreeAlgebra::new(
                    algebra,
                    HashMap::from([("node".to_string(), 0)]),
                    HashSet::from(["node".to_string()]),
                )));
                predicate = AnyPred::Tree(Box::new(TreePred::Node {
                    constructor: "node".to_string(),
                    payload_guard: Some(predicate),
                    children: Vec::new(),
                }));
                domain = AnyDomain::Tree(Box::new(SymTerm {
                    constructor: "node".to_string(),
                    payload: Some(domain),
                    children: Vec::new(),
                }));
            },
            _ => {
                algebra = AnyAlgebra::Map(Box::new(MapAlgebra::new(
                    AnyAlgebra::Int(IntervalAlgebra::new(0, 100)),
                    algebra,
                )));
                predicate = AnyPred::Map(Box::new(MapPred::CountEntries {
                    key_class: AnyPred::Int(IntervalPred::Range(1, 2)),
                    val_class: predicate,
                    lo: 1,
                    hi: Some(1),
                }));
                domain = AnyDomain::Map(vec![(AnyDomain::Int(1), domain)]);
            },
        }
    }
    (algebra, predicate, domain)
}

#[test]
fn any_domain_lifecycle_is_stack_safe_across_alternating_wrappers() {
    on_small_stack(|| {
        let domain = deep_domain();
        let cloned = domain.clone();
        assert_eq!(domain, cloned);
        let debug = format!("{domain:?}");
        assert!(debug.contains("Int(7)"));
        drop(cloned);
        drop(domain);
    });
}

#[test]
fn any_predicate_lifecycle_is_stack_safe_across_alternating_wrappers() {
    on_small_stack(|| {
        let predicate = deep_predicate();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));
        let debug = format!("{predicate:?}");
        assert!(debug.contains("Range(7, 8)"));
        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn any_algebra_lifecycle_and_singleton_are_stack_safe_across_alternating_wrappers() {
    on_small_stack(|| {
        let algebra = deep_algebra();
        let domain = deep_domain();
        let cloned = algebra.clone();
        let debug = format!("{algebra:?}");
        assert!(debug.contains("IntervalAlgebra { min_val: 0, max_val: 100 }"));

        let singleton = algebra.point(&domain);
        assert!(!matches!(singleton, AnyPred::False));

        drop(singleton);
        drop(cloned);
        drop(domain);
        drop(algebra);
    });
}

#[test]
fn boolean_projection_is_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra = AnyAlgebra::Int(IntervalAlgebra::new(0, 100));
        let mut predicate = AnyPred::Int(IntervalPred::Range(7, 8));
        for _ in 0..DEPTH {
            predicate = AnyPred::Not(Box::new(predicate));
        }
        assert!(algebra.evaluate(&predicate, &AnyDomain::Int(7)));
        drop(predicate);
        drop(algebra);
    });
}

#[test]
fn nested_combinator_evaluation_is_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let (algebra, predicate, domain) = deep_evaluation_case();
        assert!(algebra.evaluate(&predicate, &domain));
        drop(predicate);
        drop(domain);
        drop(algebra);
    });
}

#[test]
fn nested_decision_procedures_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let (algebra, predicate, _) = deep_evaluation_case();
        assert!(algebra.is_satisfiable(&predicate));
        let witness = algebra
            .witness(&predicate)
            .expect("deep Any predicate has a witness");
        assert!(algebra.evaluate(&predicate, &witness));
        drop(predicate);
        drop(witness);
        drop(algebra);
    });
}

#[test]
fn shallow_debug_contracts_match_the_former_recursive_derives() {
    let domain = AnyDomain::Product(vec![
        AnyDomain::Int(3),
        AnyDomain::List(vec![AnyDomain::Str("x".to_string())]),
    ]);
    assert_eq!(format!("{domain:?}"), "Product([Int(3), List([Str(\"x\")])])");

    let predicate = AnyPred::Product(Box::new(NaryProductPred::Field(
        0,
        AnyPred::Not(Box::new(AnyPred::Int(IntervalPred::Range(1, 3)))),
    )));
    assert_eq!(format!("{predicate:?}"), "Product(Field(0, Not(Int(Range(1, 3)))))");

    let algebra =
        AnyAlgebra::List(Box::new(RegexAlgebra::new(AnyAlgebra::Int(IntervalAlgebra::new(0, 10)))));
    assert_eq!(
        format!("{algebra:?}"),
        "List(RegexAlgebra { elem: Int(IntervalAlgebra { min_val: 0, max_val: 10 }) })"
    );
}
