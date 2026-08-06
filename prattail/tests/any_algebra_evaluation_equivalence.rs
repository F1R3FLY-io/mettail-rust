use std::collections::{HashMap, HashSet};

use mettail_prattail::any_algebra::{AnyAlgebra, AnyDomain, AnyPred};
use mettail_prattail::collection_algebra::{BagAlgebra, BagPred, MapAlgebra, MapPred};
use mettail_prattail::product_nary::{
    NaryProductAlgebra, NaryProductPred, SumAlgebra, SumPred, SumValue,
};
use mettail_prattail::regex_sfa::{RegexAlgebra, RegexPred};
use mettail_prattail::sym_tree::{SymTerm, TreeAlgebra, TreePred};
use mettail_prattail::symbolic::{BooleanAlgebra, IntervalAlgebra, IntervalPred};

fn fold_recursive<A, F>(algebra: &A, predicate: &AnyPred, leaf: &F) -> A::Predicate
where
    A: BooleanAlgebra,
    F: Fn(&AnyPred) -> Option<A::Predicate>,
{
    match predicate {
        AnyPred::True => algebra.true_pred(),
        AnyPred::False => algebra.false_pred(),
        AnyPred::And(left, right) => {
            algebra.and(&fold_recursive(algebra, left, leaf), &fold_recursive(algebra, right, leaf))
        },
        AnyPred::Or(left, right) => {
            algebra.or(&fold_recursive(algebra, left, leaf), &fold_recursive(algebra, right, leaf))
        },
        AnyPred::Not(body) => algebra.not(&fold_recursive(algebra, body, leaf)),
        other => leaf(other).unwrap_or_else(|| algebra.false_pred()),
    }
}

fn recursive_oracle(algebra: &AnyAlgebra, predicate: &AnyPred, element: &AnyDomain) -> bool {
    match (algebra, element) {
        (AnyAlgebra::Int(inner), AnyDomain::Int(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Int(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Char(inner), AnyDomain::Char(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Char(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Bool(inner), AnyDomain::Bool(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Bool(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::BigInt(inner), AnyDomain::BigInt(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::BigInt(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::BigRat(inner), AnyDomain::BigRat(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::BigRat(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Fixed(inner), AnyDomain::Fixed(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Fixed(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Float(inner), AnyDomain::Float(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Float(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Str(inner), AnyDomain::Str(value)) => inner.evaluate(
            &fold_recursive(inner, predicate, &|node| match node {
                AnyPred::Str(predicate) => Some(predicate.clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Product(inner), AnyDomain::Product(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::Product(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Sum(inner), AnyDomain::Sum(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::Sum(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::List(inner), AnyDomain::List(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::List(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Bag(inner), AnyDomain::Bag(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::Bag(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Tree(inner), AnyDomain::Tree(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::Tree(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        (AnyAlgebra::Map(inner), AnyDomain::Map(value)) => inner.evaluate(
            &fold_recursive(inner.as_ref(), predicate, &|node| match node {
                AnyPred::Map(predicate) => Some((**predicate).clone()),
                _ => None,
            }),
            value,
        ),
        _ => false,
    }
}

fn assert_agrees(algebra: &AnyAlgebra, predicate: &AnyPred, elements: &[AnyDomain]) {
    for element in elements {
        assert_eq!(
            algebra.evaluate(predicate, element),
            recursive_oracle(algebra, predicate, element),
            "algebra={algebra:?}, predicate={predicate:?}, element={element:?}",
        );
    }
}

#[test]
fn scalar_projection_and_boolean_structure_match_the_recursive_oracle() {
    let algebra = AnyAlgebra::Int(IntervalAlgebra::new(0, 10));
    let in_range = AnyPred::Int(IntervalPred::Range(2, 5));
    let foreign = AnyPred::Char(mettail_prattail::symbolic::CharClassPred::True);
    let predicates = [
        AnyPred::True,
        AnyPred::False,
        in_range.clone(),
        AnyPred::Not(Box::new(in_range.clone())),
        AnyPred::And(Box::new(in_range.clone()), Box::new(AnyPred::True)),
        AnyPred::Or(Box::new(in_range), Box::new(foreign.clone())),
        AnyPred::Not(Box::new(foreign)),
    ];
    let elements = [AnyDomain::Int(1), AnyDomain::Int(3), AnyDomain::Char('x')];
    for predicate in &predicates {
        assert_agrees(&algebra, predicate, &elements);
    }
}

#[test]
fn product_and_sum_predicates_match_the_recursive_oracle() {
    let int = || AnyAlgebra::Int(IntervalAlgebra::new(0, 10));
    let field = AnyPred::Int(IntervalPred::Range(2, 5));
    let product = AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![int(), int()])));
    let product_predicates = [
        AnyPred::Product(Box::new(NaryProductPred::True)),
        AnyPred::Product(Box::new(NaryProductPred::False)),
        AnyPred::Product(Box::new(NaryProductPred::Field(0, field.clone()))),
        AnyPred::Product(Box::new(NaryProductPred::And(
            Box::new(NaryProductPred::Field(0, field.clone())),
            Box::new(NaryProductPred::Not(Box::new(NaryProductPred::Field(1, field.clone())))),
        ))),
        AnyPred::Product(Box::new(NaryProductPred::Or(
            Box::new(NaryProductPred::Field(8, field.clone())),
            Box::new(NaryProductPred::Field(1, field.clone())),
        ))),
    ];
    let product_elements = [
        AnyDomain::Product(vec![AnyDomain::Int(3), AnyDomain::Int(8)]),
        AnyDomain::Product(vec![AnyDomain::Int(8), AnyDomain::Int(3)]),
        AnyDomain::Product(Vec::new()),
    ];
    for predicate in &product_predicates {
        assert_agrees(&product, predicate, &product_elements);
    }

    let sum = AnyAlgebra::Sum(Box::new(SumAlgebra::new(vec![int(), int()])));
    let sum_predicates = [
        AnyPred::Sum(Box::new(SumPred::True)),
        AnyPred::Sum(Box::new(SumPred::False)),
        AnyPred::Sum(Box::new(SumPred::TagIs(1))),
        AnyPred::Sum(Box::new(SumPred::InVariant(0, field.clone()))),
        AnyPred::Sum(Box::new(SumPred::And(
            Box::new(SumPred::InVariant(0, field.clone())),
            Box::new(SumPred::Not(Box::new(SumPred::TagIs(1)))),
        ))),
        AnyPred::Sum(Box::new(SumPred::Or(
            Box::new(SumPred::TagIs(0)),
            Box::new(SumPred::TagIs(1)),
        ))),
    ];
    let sum_elements = [
        AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: AnyDomain::Int(3) })),
        AnyDomain::Sum(Box::new(SumValue { tag: 1, payload: AnyDomain::Int(8) })),
        AnyDomain::Sum(Box::new(SumValue { tag: 8, payload: AnyDomain::Int(3) })),
    ];
    for predicate in &sum_predicates {
        assert_agrees(&sum, predicate, &sum_elements);
    }
}

#[test]
fn regex_predicates_match_the_recursive_oracle() {
    let algebra =
        AnyAlgebra::List(Box::new(RegexAlgebra::new(AnyAlgebra::Int(IntervalAlgebra::new(0, 10)))));
    let elem = || AnyPred::Int(IntervalPred::Range(2, 5));
    let predicates = [
        RegexPred::Empty,
        RegexPred::Epsilon,
        RegexPred::Elem(elem()),
        RegexPred::Length(1, Some(2)),
        RegexPred::Concat(Box::new(RegexPred::Elem(elem())), Box::new(RegexPred::Elem(elem()))),
        RegexPred::Alt(Box::new(RegexPred::Epsilon), Box::new(RegexPred::Elem(elem()))),
        RegexPred::Star(Box::new(RegexPred::Elem(elem()))),
        RegexPred::Inter(
            Box::new(RegexPred::Length(1, None)),
            Box::new(RegexPred::Star(Box::new(RegexPred::Elem(elem())))),
        ),
        RegexPred::Compl(Box::new(RegexPred::Elem(elem()))),
    ];
    let elements = [
        AnyDomain::List(Vec::new()),
        AnyDomain::List(vec![AnyDomain::Int(3)]),
        AnyDomain::List(vec![AnyDomain::Int(8)]),
        AnyDomain::List(vec![AnyDomain::Int(3), AnyDomain::Int(4)]),
        AnyDomain::List(vec![AnyDomain::Char('x')]),
    ];
    for predicate in predicates {
        assert_agrees(&algebra, &AnyPred::List(Box::new(predicate)), &elements);
    }
}

#[test]
fn bag_and_map_predicates_match_the_recursive_oracle() {
    let class = AnyPred::Int(IntervalPred::Range(2, 5));
    let bag =
        AnyAlgebra::Bag(Box::new(BagAlgebra::new(AnyAlgebra::Int(IntervalAlgebra::new(0, 10)))));
    let bag_predicates = [
        BagPred::True,
        BagPred::False,
        BagPred::Count { class: class.clone(), lo: 1, hi: Some(2) },
        BagPred::Not(Box::new(BagPred::Count { class: class.clone(), lo: 0, hi: Some(0) })),
        BagPred::And(
            Box::new(BagPred::Count { class: class.clone(), lo: 1, hi: None }),
            Box::new(BagPred::Count { class: AnyPred::True, lo: 0, hi: Some(2) }),
        ),
        BagPred::Or(
            Box::new(BagPred::False),
            Box::new(BagPred::Count { class: class.clone(), lo: 2, hi: Some(2) }),
        ),
    ];
    let bag_elements = [
        AnyDomain::Bag(Vec::new()),
        AnyDomain::Bag(vec![AnyDomain::Int(3)]),
        AnyDomain::Bag(vec![AnyDomain::Int(3), AnyDomain::Int(8)]),
        AnyDomain::Bag(vec![AnyDomain::Int(3), AnyDomain::Int(4)]),
    ];
    for predicate in bag_predicates {
        assert_agrees(&bag, &AnyPred::Bag(Box::new(predicate)), &bag_elements);
    }

    let map = AnyAlgebra::Map(Box::new(MapAlgebra::new(
        AnyAlgebra::Int(IntervalAlgebra::new(0, 10)),
        AnyAlgebra::Int(IntervalAlgebra::new(0, 10)),
    )));
    let map_predicates = [
        MapPred::True,
        MapPred::False,
        MapPred::CountEntries {
            key_class: AnyPred::Int(IntervalPred::Range(1, 3)),
            val_class: class.clone(),
            lo: 1,
            hi: Some(1),
        },
        MapPred::Not(Box::new(MapPred::CountEntries {
            key_class: AnyPred::True,
            val_class: class.clone(),
            lo: 0,
            hi: Some(0),
        })),
        MapPred::And(
            Box::new(MapPred::CountEntries {
                key_class: AnyPred::True,
                val_class: AnyPred::True,
                lo: 1,
                hi: None,
            }),
            Box::new(MapPred::CountEntries {
                key_class: AnyPred::Int(IntervalPred::Range(1, 3)),
                val_class: class,
                lo: 1,
                hi: Some(1),
            }),
        ),
    ];
    let map_elements = [
        AnyDomain::Map(Vec::new()),
        AnyDomain::Map(vec![(AnyDomain::Int(1), AnyDomain::Int(3))]),
        AnyDomain::Map(vec![
            (AnyDomain::Int(1), AnyDomain::Int(8)),
            (AnyDomain::Int(4), AnyDomain::Int(3)),
        ]),
    ];
    for predicate in map_predicates {
        assert_agrees(&map, &AnyPred::Map(Box::new(predicate)), &map_elements);
    }
}

#[test]
fn tree_predicates_match_the_recursive_oracle() {
    let mut arities = HashMap::new();
    arities.insert("Leaf".to_string(), 0);
    arities.insert("Pair".to_string(), 2);
    let payloaded = HashSet::from(["Leaf".to_string()]);
    let algebra = AnyAlgebra::Tree(Box::new(TreeAlgebra::new(
        AnyAlgebra::Int(IntervalAlgebra::new(0, 10)),
        arities,
        payloaded,
    )));
    let leaf = || TreePred::Node {
        constructor: "Leaf".to_string(),
        payload_guard: Some(AnyPred::Int(IntervalPred::Range(2, 5))),
        children: Vec::new(),
    };
    let predicates = [
        TreePred::True,
        TreePred::False,
        TreePred::Wild,
        leaf(),
        TreePred::Node {
            constructor: "Pair".to_string(),
            payload_guard: None,
            children: vec![leaf(), TreePred::Wild],
        },
        TreePred::And(Box::new(TreePred::Wild), Box::new(leaf())),
        TreePred::Or(Box::new(TreePred::False), Box::new(leaf())),
        TreePred::Not(Box::new(leaf())),
    ];
    let elements = [
        AnyDomain::Tree(Box::new(SymTerm::leaf("Leaf", AnyDomain::Int(3)))),
        AnyDomain::Tree(Box::new(SymTerm::leaf("Leaf", AnyDomain::Int(8)))),
        AnyDomain::Tree(Box::new(SymTerm::node(
            "Pair",
            vec![
                SymTerm::leaf("Leaf", AnyDomain::Int(3)),
                SymTerm::leaf("Leaf", AnyDomain::Int(8)),
            ],
        ))),
        AnyDomain::Tree(Box::new(SymTerm::node("Unknown", Vec::new()))),
        AnyDomain::Tree(Box::new(SymTerm::node("Pair", Vec::new()))),
    ];
    for predicate in predicates {
        assert_agrees(&algebra, &AnyPred::Tree(Box::new(predicate)), &elements);
    }
}

#[test]
fn shallow_cross_combinator_nesting_matches_inductively() {
    let mut algebra = AnyAlgebra::Int(IntervalAlgebra::new(0, 10));
    let mut predicate = AnyPred::Int(IntervalPred::Range(2, 5));
    let mut matching = AnyDomain::Int(3);
    let mut rejected = AnyDomain::Int(8);
    for depth in 0..18 {
        assert_agrees(&algebra, &predicate, &[matching.clone(), rejected.clone()]);
        match depth % 6 {
            0 => {
                algebra = AnyAlgebra::Product(Box::new(NaryProductAlgebra::new(vec![algebra])));
                predicate = AnyPred::Product(Box::new(NaryProductPred::Field(0, predicate)));
                matching = AnyDomain::Product(vec![matching]);
                rejected = AnyDomain::Product(vec![rejected]);
            },
            1 => {
                algebra = AnyAlgebra::Sum(Box::new(SumAlgebra::new(vec![algebra])));
                predicate = AnyPred::Sum(Box::new(SumPred::InVariant(0, predicate)));
                matching = AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: matching }));
                rejected = AnyDomain::Sum(Box::new(SumValue { tag: 0, payload: rejected }));
            },
            2 => {
                algebra = AnyAlgebra::List(Box::new(RegexAlgebra::new(algebra)));
                predicate = AnyPred::List(Box::new(RegexPred::Elem(predicate)));
                matching = AnyDomain::List(vec![matching]);
                rejected = AnyDomain::List(vec![rejected]);
            },
            3 => {
                algebra = AnyAlgebra::Bag(Box::new(BagAlgebra::new(algebra)));
                predicate =
                    AnyPred::Bag(Box::new(BagPred::Count { class: predicate, lo: 1, hi: Some(1) }));
                matching = AnyDomain::Bag(vec![matching]);
                rejected = AnyDomain::Bag(vec![rejected]);
            },
            4 => {
                algebra = AnyAlgebra::Tree(Box::new(TreeAlgebra::new(
                    algebra,
                    HashMap::new(),
                    HashSet::new(),
                )));
                predicate = AnyPred::Tree(Box::new(TreePred::Node {
                    constructor: "node".to_string(),
                    payload_guard: Some(predicate),
                    children: Vec::new(),
                }));
                matching = AnyDomain::Tree(Box::new(SymTerm::leaf("node", matching)));
                rejected = AnyDomain::Tree(Box::new(SymTerm::leaf("node", rejected)));
            },
            _ => {
                algebra = AnyAlgebra::Map(Box::new(MapAlgebra::new(
                    AnyAlgebra::Int(IntervalAlgebra::new(0, 10)),
                    algebra,
                )));
                predicate = AnyPred::Map(Box::new(MapPred::CountEntries {
                    key_class: AnyPred::Int(IntervalPred::Range(1, 2)),
                    val_class: predicate,
                    lo: 1,
                    hi: Some(1),
                }));
                matching = AnyDomain::Map(vec![(AnyDomain::Int(1), matching)]);
                rejected = AnyDomain::Map(vec![(AnyDomain::Int(1), rejected)]);
            },
        }
    }
    assert_agrees(&algebra, &predicate, &[matching, rejected]);
}
