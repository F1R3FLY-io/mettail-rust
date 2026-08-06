//! Differential checks for the heap-trampolined `AnyAlgebra` decision engine.
//!
//! The shallow generic algebras are the independent reference implementation:
//! they decide the same predicates directly, without routing recursive carrier
//! queries through `AnyAlgebra`'s coroutine executor.

use std::collections::{HashMap, HashSet};

use mettail_prattail::any_algebra::{AnyAlgebra, AnyDomain, AnyPred};
use mettail_prattail::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred};
use mettail_prattail::product_nary::{NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred};
use mettail_prattail::regex_sfa::{RegexAlgebra, RegexPred};
use mettail_prattail::sym_tree::{TreeAlgebra, TreePred};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};

fn interval() -> IntervalAlgebra {
    IntervalAlgebra::new(0, 8)
}

fn any_interval() -> AnyAlgebra {
    AnyAlgebra::Int(interval())
}

fn wrap_interval(predicate: &IntervalPred) -> AnyPred {
    AnyPred::Int(predicate.clone())
}

fn wrap_product(predicate: &NaryProductPred<IntervalPred>) -> NaryProductPred<AnyPred> {
    match predicate {
        NaryProductPred::True => NaryProductPred::True,
        NaryProductPred::False => NaryProductPred::False,
        NaryProductPred::Field(index, predicate) => {
            NaryProductPred::Field(*index, wrap_interval(predicate))
        },
        NaryProductPred::And(left, right) => {
            NaryProductPred::And(Box::new(wrap_product(left)), Box::new(wrap_product(right)))
        },
        NaryProductPred::Or(left, right) => {
            NaryProductPred::Or(Box::new(wrap_product(left)), Box::new(wrap_product(right)))
        },
        NaryProductPred::Not(body) => NaryProductPred::Not(Box::new(wrap_product(body))),
    }
}

fn wrap_sum(predicate: &SumPred<IntervalPred>) -> SumPred<AnyPred> {
    match predicate {
        SumPred::True => SumPred::True,
        SumPred::False => SumPred::False,
        SumPred::TagIs(tag) => SumPred::TagIs(*tag),
        SumPred::InVariant(tag, predicate) => SumPred::InVariant(*tag, wrap_interval(predicate)),
        SumPred::And(left, right) => {
            SumPred::And(Box::new(wrap_sum(left)), Box::new(wrap_sum(right)))
        },
        SumPred::Or(left, right) => {
            SumPred::Or(Box::new(wrap_sum(left)), Box::new(wrap_sum(right)))
        },
        SumPred::Not(body) => SumPred::Not(Box::new(wrap_sum(body))),
    }
}

fn wrap_regex(predicate: &RegexPred<IntervalPred>) -> RegexPred<AnyPred> {
    match predicate {
        RegexPred::Empty => RegexPred::Empty,
        RegexPred::Epsilon => RegexPred::Epsilon,
        RegexPred::Elem(predicate) => RegexPred::Elem(wrap_interval(predicate)),
        RegexPred::Concat(left, right) => {
            RegexPred::Concat(Box::new(wrap_regex(left)), Box::new(wrap_regex(right)))
        },
        RegexPred::Alt(left, right) => {
            RegexPred::Alt(Box::new(wrap_regex(left)), Box::new(wrap_regex(right)))
        },
        RegexPred::Star(body) => RegexPred::Star(Box::new(wrap_regex(body))),
        RegexPred::Inter(left, right) => {
            RegexPred::Inter(Box::new(wrap_regex(left)), Box::new(wrap_regex(right)))
        },
        RegexPred::Compl(body) => RegexPred::Compl(Box::new(wrap_regex(body))),
        RegexPred::Length(lower, upper) => RegexPred::Length(*lower, *upper),
    }
}

fn wrap_bag(predicate: &BagPred<IntervalPred>) -> BagPred<AnyPred> {
    match predicate {
        BagPred::True => BagPred::True,
        BagPred::False => BagPred::False,
        BagPred::Count { class, lo, hi } => BagPred::Count {
            class: wrap_interval(class),
            lo: *lo,
            hi: *hi,
        },
        BagPred::And(left, right) => {
            BagPred::And(Box::new(wrap_bag(left)), Box::new(wrap_bag(right)))
        },
        BagPred::Or(left, right) => {
            BagPred::Or(Box::new(wrap_bag(left)), Box::new(wrap_bag(right)))
        },
        BagPred::Not(body) => BagPred::Not(Box::new(wrap_bag(body))),
    }
}

fn wrap_map(predicate: &MapPred<IntervalPred, IntervalPred>) -> MapPred<AnyPred, AnyPred> {
    match predicate {
        MapPred::True => MapPred::True,
        MapPred::False => MapPred::False,
        MapPred::CountEntries { key_class, val_class, lo, hi } => MapPred::CountEntries {
            key_class: wrap_interval(key_class),
            val_class: wrap_interval(val_class),
            lo: *lo,
            hi: *hi,
        },
        MapPred::And(left, right) => {
            MapPred::And(Box::new(wrap_map(left)), Box::new(wrap_map(right)))
        },
        MapPred::Or(left, right) => {
            MapPred::Or(Box::new(wrap_map(left)), Box::new(wrap_map(right)))
        },
        MapPred::Not(body) => MapPred::Not(Box::new(wrap_map(body))),
    }
}

fn wrap_tree(predicate: &TreePred<IntervalPred>) -> TreePred<AnyPred> {
    match predicate {
        TreePred::True => TreePred::True,
        TreePred::False => TreePred::False,
        TreePred::Wild => TreePred::Wild,
        TreePred::Node { constructor, payload_guard, children } => TreePred::Node {
            constructor: constructor.clone(),
            payload_guard: payload_guard.as_ref().map(wrap_interval),
            children: children.iter().map(wrap_tree).collect(),
        },
        TreePred::And(left, right) => {
            TreePred::And(Box::new(wrap_tree(left)), Box::new(wrap_tree(right)))
        },
        TreePred::Or(left, right) => {
            TreePred::Or(Box::new(wrap_tree(left)), Box::new(wrap_tree(right)))
        },
        TreePred::Not(body) => TreePred::Not(Box::new(wrap_tree(body))),
    }
}

#[test]
fn product_and_sum_decisions_match_generic_oracles() {
    let product = NaryProductAlgebra::new(vec![interval(), interval()]);
    let any_product = AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![
        any_interval(),
        any_interval(),
    ])));
    let left = NaryProductPred::Field(0, IntervalPred::Range(1, 5));
    let right = NaryProductPred::Field(1, IntervalPred::Range(4, 7));
    let product_cases = vec![
        NaryProductPred::True,
        NaryProductPred::False,
        left.clone(),
        NaryProductPred::Field(9, IntervalPred::True),
        NaryProductPred::And(Box::new(left.clone()), Box::new(right.clone())),
        NaryProductPred::Or(Box::new(NaryProductPred::False), Box::new(right)),
        NaryProductPred::Not(Box::new(left)),
    ];
    for predicate in product_cases {
        let any_predicate = AnyPred::Product(Box::new(wrap_product(&predicate)));
        let expected = product.is_satisfiable(&predicate);
        let witness = product.witness(&predicate);
        let actual = any_product.is_satisfiable(&any_predicate);
        let any_witness = any_product.witness(&any_predicate);
        assert_eq!(actual, expected, "product SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(product.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_product.evaluate(&any_predicate, &value));
        }
    }

    let sum = SumAlgebra::new(vec![interval(), interval()]);
    let any_sum = AnyAlgebra::Sum(Box::new(SumAlgebra::new(vec![any_interval(), any_interval()])));
    let tag_zero = SumPred::InVariant(0, IntervalPred::Range(1, 3));
    let tag_one = SumPred::InVariant(1, IntervalPred::Range(6, 8));
    let sum_cases = vec![
        SumPred::True,
        SumPred::False,
        SumPred::TagIs(1),
        tag_zero.clone(),
        SumPred::InVariant(9, IntervalPred::True),
        SumPred::And(Box::new(tag_zero.clone()), Box::new(tag_one.clone())),
        SumPred::Or(Box::new(tag_zero.clone()), Box::new(tag_one)),
        SumPred::Not(Box::new(tag_zero)),
    ];
    for predicate in sum_cases {
        let any_predicate = AnyPred::Sum(Box::new(wrap_sum(&predicate)));
        let expected = sum.is_satisfiable(&predicate);
        let witness = sum.witness(&predicate);
        let actual = any_sum.is_satisfiable(&any_predicate);
        let any_witness = any_sum.witness(&any_predicate);
        assert_eq!(actual, expected, "sum SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(sum.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_sum.evaluate(&any_predicate, &value));
        }
    }
}

#[test]
fn regex_decisions_match_generic_oracle() {
    let regex = RegexAlgebra::new(interval());
    let any_regex = AnyAlgebra::List(Box::new(RegexAlgebra::new(any_interval())));
    let small = RegexPred::Elem(IntervalPred::Range(1, 4));
    let large = RegexPred::Elem(IntervalPred::Range(5, 8));
    let cases = vec![
        RegexPred::Empty,
        RegexPred::Epsilon,
        small.clone(),
        RegexPred::Concat(Box::new(small.clone()), Box::new(large.clone())),
        RegexPred::Alt(Box::new(RegexPred::Empty), Box::new(large.clone())),
        RegexPred::Star(Box::new(small.clone())),
        RegexPred::Inter(
            Box::new(small.clone()),
            Box::new(RegexPred::Elem(IntervalPred::Range(3, 6))),
        ),
        RegexPred::Compl(Box::new(RegexPred::Star(Box::new(large)))),
        RegexPred::Length(2, Some(3)),
    ];
    for predicate in cases {
        let any_predicate = AnyPred::List(Box::new(wrap_regex(&predicate)));
        let expected = regex.is_satisfiable(&predicate);
        let witness = regex.witness(&predicate);
        let actual = any_regex.is_satisfiable(&any_predicate);
        let any_witness = any_regex.witness(&any_predicate);
        assert_eq!(actual, expected, "regex SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(regex.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_regex.evaluate(&any_predicate, &value));
        }
    }
}

#[test]
fn bag_and_map_decisions_match_generic_oracles() {
    let bag = BagAlgebra::new(interval());
    let any_bag = AnyAlgebra::Bag(Box::new(BagAlgebra::new(any_interval())));
    let low = BagPred::Count {
        class: IntervalPred::Range(0, 4),
        lo: 1,
        hi: Some(2),
    };
    let high = BagPred::Count {
        class: IntervalPred::Range(4, 8),
        lo: 1,
        hi: None,
    };
    let bag_cases = vec![
        BagPred::True,
        BagPred::False,
        low.clone(),
        BagPred::Count {
            class: IntervalPred::False,
            lo: 1,
            hi: None,
        },
        BagPred::And(Box::new(low.clone()), Box::new(high.clone())),
        BagPred::Or(Box::new(BagPred::False), Box::new(high)),
        BagPred::Not(Box::new(low)),
    ];
    for predicate in bag_cases {
        let any_predicate = AnyPred::Bag(Box::new(wrap_bag(&predicate)));
        let expected = bag.is_satisfiable(&predicate);
        let witness = bag.witness(&predicate);
        let actual = any_bag.is_satisfiable(&any_predicate);
        let any_witness = any_bag.witness(&any_predicate);
        assert_eq!(actual, expected, "bag SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(bag.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_bag.evaluate(&any_predicate, &value));
        }
    }

    let map = MapAlgebra::new(interval(), interval());
    let any_map = AnyAlgebra::Map(Box::new(MapAlgebra::new(any_interval(), any_interval())));
    let low = MapPred::CountEntries {
        key_class: IntervalPred::Range(0, 4),
        val_class: IntervalPred::Range(0, 4),
        lo: 1,
        hi: Some(1),
    };
    let high = MapPred::CountEntries {
        key_class: IntervalPred::Range(4, 8),
        val_class: IntervalPred::Range(4, 8),
        lo: 1,
        hi: None,
    };
    let map_cases = vec![
        MapPred::True,
        MapPred::False,
        low.clone(),
        MapPred::CountEntries {
            key_class: IntervalPred::False,
            val_class: IntervalPred::True,
            lo: 1,
            hi: None,
        },
        MapPred::And(Box::new(low.clone()), Box::new(high.clone())),
        MapPred::Or(Box::new(MapPred::False), Box::new(high)),
        MapPred::Not(Box::new(low)),
    ];
    for predicate in map_cases {
        let any_predicate = AnyPred::Map(Box::new(wrap_map(&predicate)));
        let expected = map.is_satisfiable(&predicate);
        let witness = map.witness(&predicate);
        let actual = any_map.is_satisfiable(&any_predicate);
        let any_witness = any_map.witness(&any_predicate);
        assert_eq!(actual, expected, "map SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(map.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_map.evaluate(&any_predicate, &value));
        }
    }
}

#[test]
fn tree_decisions_match_generic_oracle() {
    let arities = HashMap::from([("Lit".to_string(), 0), ("Pair".to_string(), 2)]);
    let payloaded = HashSet::from(["Lit".to_string()]);
    let tree = TreeAlgebra::new(interval(), arities.clone(), payloaded.clone());
    let any_tree = AnyAlgebra::Tree(Box::new(TreeAlgebra::new(any_interval(), arities, payloaded)));
    let small_lit = TreePred::Node {
        constructor: "Lit".to_string(),
        payload_guard: Some(IntervalPred::Range(0, 4)),
        children: Vec::new(),
    };
    let pair = TreePred::Node {
        constructor: "Pair".to_string(),
        payload_guard: None,
        children: vec![small_lit.clone(), TreePred::Wild],
    };
    let cases = vec![
        TreePred::True,
        TreePred::False,
        TreePred::Wild,
        small_lit.clone(),
        pair,
        TreePred::And(
            Box::new(small_lit.clone()),
            Box::new(TreePred::Not(Box::new(small_lit.clone()))),
        ),
        TreePred::Or(Box::new(TreePred::False), Box::new(small_lit.clone())),
        TreePred::Not(Box::new(small_lit)),
    ];
    for predicate in cases {
        let any_predicate = AnyPred::Tree(Box::new(wrap_tree(&predicate)));
        let expected = tree.is_satisfiable(&predicate);
        let witness = tree.witness(&predicate);
        let actual = any_tree.is_satisfiable(&any_predicate);
        let any_witness = any_tree.witness(&any_predicate);
        assert_eq!(actual, expected, "tree SAT disagreement for {predicate:?}");
        assert_eq!(any_witness.is_some(), witness.is_some());
        if let Some(value) = witness {
            assert!(tree.evaluate(&predicate, &value));
        }
        if let Some(value) = any_witness {
            assert!(any_tree.evaluate(&any_predicate, &value));
        }
    }
}

#[test]
fn carrier_level_boolean_projection_agrees_with_leaf_semantics() {
    let algebra = any_interval();
    let range = AnyPred::Int(IntervalPred::Range(2, 5));
    let alien = AnyPred::List(Box::new(RegexPred::Epsilon));
    let cases = [
        AnyPred::True,
        AnyPred::False,
        range.clone(),
        AnyPred::Not(Box::new(range.clone())),
        AnyPred::And(Box::new(range.clone()), Box::new(alien.clone())),
        AnyPred::Or(Box::new(range), Box::new(alien)),
    ];
    for predicate in cases {
        let satisfiable = algebra.is_satisfiable(&predicate);
        let witness = algebra.witness(&predicate);
        assert_eq!(satisfiable, witness.is_some(), "{predicate:?}");
        if let Some(AnyDomain::Int(value)) = witness {
            assert!(algebra.evaluate(&predicate, &AnyDomain::Int(value)));
        }
    }
}
