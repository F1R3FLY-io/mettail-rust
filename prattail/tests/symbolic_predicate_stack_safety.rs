use mettail_prattail::symbolic::{
    classify_decidability, BooleanAlgebra, CharClassAlgebra, CharClassPred, DecidabilityTier,
    IntervalAlgebra, IntervalPred, PredicateExpr, ProductAlgebra, ProductDomain, ProductPred,
};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("symbolic-predicate-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn symbolic predicate small-stack gate")
        .join()
        .expect("symbolic predicate small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn deep_interval_predicate() -> IntervalPred {
    let mut predicate = IntervalPred::Range(10, 20);
    for _ in 0..DEPTH {
        predicate = IntervalPred::Not(Box::new(predicate));
    }
    predicate
}

fn deep_character_predicate() -> CharClassPred {
    let mut predicate = CharClassPred::Range('a', 'z');
    for _ in 0..DEPTH {
        predicate = CharClassPred::Not(Box::new(predicate));
    }
    predicate
}

fn deep_predicate_expression() -> PredicateExpr {
    let mut expression = PredicateExpr::Relation {
        name: "edge".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    for depth in 0..DEPTH {
        expression = match depth % 5 {
            0 => PredicateExpr::Not(Box::new(expression)),
            1 => PredicateExpr::ForallFinite {
                var: "x".to_string(),
                domain: vec!["0".to_string(), "1".to_string()],
                body: Box::new(expression),
            },
            2 => PredicateExpr::ExistsFinite {
                var: "y".to_string(),
                domain: vec!["a".to_string()],
                body: Box::new(expression),
            },
            3 => PredicateExpr::ForallInfinite {
                var: "n".to_string(),
                body: Box::new(expression),
            },
            _ => PredicateExpr::ExistsInfinite {
                var: "m".to_string(),
                body: Box::new(expression),
            },
        };
    }
    PredicateExpr::Bounded { body: Box::new(expression), bound: 64 }
}

type IntervalProductPred = ProductPred<IntervalAlgebra, IntervalAlgebra>;

fn product_atom() -> IntervalProductPred {
    ProductPred::Both(IntervalPred::Range(10, 20), IntervalPred::Range(30, 40))
}

fn deep_product_conjunction() -> IntervalProductPred {
    let mut predicate = product_atom();
    for _ in 0..DEPTH {
        predicate = ProductPred::And(Box::new(predicate), Box::new(product_atom()));
    }
    predicate
}

fn deep_product_negation() -> IntervalProductPred {
    let mut predicate = product_atom();
    for _ in 0..DEPTH {
        predicate = ProductPred::Not(Box::new(predicate));
    }
    predicate
}

#[test]
fn interval_predicate_lifecycle_and_algebra_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let predicate = deep_interval_predicate();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));

        let display = predicate.to_string();
        assert_eq!(display.len(), DEPTH + "[10, 20)".len());
        assert!(display.ends_with("[10, 20)"));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("Not(Not("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let algebra = IntervalAlgebra::new(0, 100);
        assert!(algebra.is_satisfiable(&predicate));
        assert_eq!(algebra.witness(&predicate), Some(10));
        assert!(algebra.evaluate(&predicate, &15));
        assert!(!algebra.evaluate(&predicate, &25));

        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn character_predicate_lifecycle_and_algebra_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let predicate = deep_character_predicate();
        let cloned = predicate.clone();
        assert_eq!(predicate, cloned);
        assert_eq!(hash(&predicate), hash(&cloned));

        let display = predicate.to_string();
        assert_eq!(display.len(), DEPTH + "[a-z]".len());
        assert!(display.ends_with("[a-z]"));
        let debug = format!("{predicate:?}");
        assert!(debug.starts_with("Not(Not("));
        assert!(debug.ends_with(&")".repeat(DEPTH)));

        let algebra = CharClassAlgebra::new();
        assert!(algebra.is_satisfiable(&predicate));
        assert_eq!(algebra.witness(&predicate), Some('a'));
        assert!(algebra.evaluate(&predicate, &'m'));
        assert!(!algebra.evaluate(&predicate, &'0'));

        drop(cloned);
        drop(predicate);
    });
}

#[test]
fn predicate_expression_lifecycle_and_classifier_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let expression = deep_predicate_expression();
        let cloned = expression.clone();
        assert_eq!(expression, cloned);
        assert_eq!(hash(&expression), hash(&cloned));
        assert_eq!(classify_decidability(&expression), DecidabilityTier::SemiDecidable);

        let display = expression.to_string();
        assert!(display.starts_with("bounded("));
        assert!(display.contains("edge(x, y)"));
        assert!(display.ends_with(", 64)"));
        let debug = format!("{expression:?}");
        assert!(debug.starts_with("Bounded { body: "));
        assert!(debug.contains("Relation { name: \"edge\", args: [\"x\", \"y\"] }"));
        assert!(debug.ends_with(", bound: 64 }"));

        drop(cloned);
        drop(expression);
    });
}

#[test]
fn product_predicate_lifecycle_dnf_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let algebra =
            ProductAlgebra::new(IntervalAlgebra::new(0, 100), IntervalAlgebra::new(0, 100));
        let element = ProductDomain(15, 35);

        let conjunction = deep_product_conjunction();
        let cloned = conjunction.clone();
        assert_eq!(conjunction, cloned);
        assert_eq!(hash(&conjunction), hash(&cloned));
        assert!(algebra.evaluate(&conjunction, &element));
        assert!(algebra.is_satisfiable(&conjunction));
        let witness = algebra
            .witness(&conjunction)
            .expect("deep product conjunction has a witness");
        assert_eq!((witness.0, witness.1), (10, 30));

        let display = conjunction.to_string();
        assert!(display.starts_with("((("));
        assert!(display.contains("×"));
        assert!(display.ends_with("))"));
        let debug = format!("{conjunction:?}");
        assert!(debug.starts_with("And(And("));
        assert!(debug.ends_with("))"));

        let negation = deep_product_negation();
        let negation_clone = negation.clone();
        assert_eq!(negation, negation_clone);
        assert_eq!(hash(&negation), hash(&negation_clone));
        assert!(algebra.evaluate(&negation, &element));
        assert!(algebra.is_satisfiable(&negation));

        drop(negation_clone);
        drop(negation);
        drop(cloned);
        drop(conjunction);
    });
}

#[test]
fn symbolic_predicate_debug_and_display_preserve_compact_contracts() {
    let interval = IntervalPred::Not(Box::new(IntervalPred::Range(1, 3)));
    assert_eq!(interval.to_string(), "~[1, 3)");
    assert_eq!(format!("{interval:?}"), "Not(Range(1, 3))");

    let character = CharClassPred::Not(Box::new(CharClassPred::Range('a', 'z')));
    assert_eq!(character.to_string(), "~[a-z]");
    assert_eq!(format!("{character:?}"), "Not(Range('a', 'z'))");

    let expression = PredicateExpr::Bounded {
        body: Box::new(PredicateExpr::And(
            Box::new(PredicateExpr::Atom("p".to_string())),
            Box::new(PredicateExpr::ForallFinite {
                var: "x".to_string(),
                domain: vec!["a".to_string(), "b".to_string()],
                body: Box::new(PredicateExpr::Relation {
                    name: "r".to_string(),
                    args: vec!["x".to_string()],
                }),
            }),
        )),
        bound: 8,
    };
    assert_eq!(expression.to_string(), "bounded((p /\\ forall x in [\"a\", \"b\"]. r(x)), 8)");
    assert_eq!(
        format!("{expression:?}"),
        "Bounded { body: And(Atom(\"p\"), ForallFinite { var: \"x\", domain: [\"a\", \"b\"], body: Relation { name: \"r\", args: [\"x\"] } }), bound: 8 }"
    );

    let product: IntervalProductPred = ProductPred::Not(Box::new(ProductPred::And(
        Box::new(ProductPred::LeftOnly(IntervalPred::Range(1, 3))),
        Box::new(ProductPred::RightOnly(IntervalPred::Range(4, 6))),
    )));
    assert_eq!(product.to_string(), "¬((Range(1, 3) × TRUE) ∧ (TRUE × Range(4, 6)))");
    assert_eq!(
        format!("{product:?}"),
        "Not(And(LeftOnly(Range(1, 3)), RightOnly(Range(4, 6))))"
    );
}
