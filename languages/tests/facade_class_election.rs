#[path = "support/facade_class_weights.rs"]
mod facade_class_weights;
#[path = "definitions/led_test.rs"]
mod ledtest;

use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};
use mettail_prattail::wpda_walker::WpdaEngine;
use std::sync::Arc;

fn key(term: &ledtest::Expr) -> Vec<u8> {
    let erased: Arc<dyn std::any::Any + Send + Sync> = Arc::new(term.clone());
    <ledtest::LedTestWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint(
        &ledtest::LedTestWpdaEngine,
        &erased,
    )
    .unwrap()
}

fn check(source: &str, trailing: bool) {
    let single = ledtest::Expr::parse_via_wpda(source).unwrap();
    let input = if trailing {
        format!("{source} )")
    } else {
        source.to_string()
    };
    let tokens = LatticeTokenSource::new(ledtest::lex_dag(&input).unwrap());
    let mut position = 0;
    let (terms, weights) =
        ledtest::parse_Expr_via_wpda_all_with_source(&tokens, &mut position, 0).unwrap();
    if trailing {
        assert!(position < tokens.eof_node());
    } else {
        assert_eq!(position, tokens.eof_node());
    }
    let category = ledtest::WPDA_CATEGORIES
        .iter()
        .position(|name| *name == "Expr")
        .unwrap();
    let raw = facade_class_weights::enumerated_weights(
        ledtest::LedTestWpdaEngine,
        u16::try_from(category).unwrap(),
        &tokens,
    );
    let raw_keys: std::collections::BTreeSet<_> = raw.iter().map(|(key, _)| key.clone()).collect();
    let keys: std::collections::BTreeSet<_> = terms.iter().map(key).collect();
    assert_eq!(keys, raw_keys, "every raw class remains available: {input}");
    assert_eq!(terms.len(), keys.len(), "each class has one representative");
    assert_eq!(weights.len(), terms.len());
    for (term, weight) in terms.iter().zip(&weights) {
        let class = key(term);
        let minimum = raw
            .iter()
            .filter(|(candidate, _)| *candidate == class)
            .map(|(_, weight)| *weight)
            .min()
            .unwrap();
        assert_eq!(*weight, minimum, "the exact class weight is preserved: {input}");
    }
    let elected = terms.iter().find(|term| key(term) == key(&single)).unwrap();
    assert_eq!(format!("{elected:?}"), format!("{single:?}"), "{input}");
}

#[test]
fn independent_language_preserves_ambiguity_and_native_categories() {
    for source in ["false", "true and false", "1 + 2", "1 == 2", "x", "(x)"] {
        check(source, false);
        check(source, true);
    }
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn independent_language_preserves_elections_classes_and_weights(
        a in 0u8..16, b in 0u8..16, mode in 0u8..4,
        depth in 0usize..3, trailing in proptest::bool::ANY,
    ) {
        let mut source = match mode {
            0 => format!("{}", a % 2 == 0),
            1 => format!("{} and {}", a % 2 == 0, b % 2 == 0),
            2 => format!("{a} + {b}"),
            _ => format!("{a} == {b}"),
        };
        for _ in 0..depth { source = format!("({source})"); }
        check(&source, trailing);
    }
}
