#[path = "definitions/class3opt.rs"]
mod class3opt;
#[path = "support/facade_class_weights.rs"]
mod facade_class_weights;
#[path = "definitions/led_test.rs"]
mod ledtest;

use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_runtime::{CursorBoundingMode, LatticeTokenSource, WpdaTokenSource};
use mettail_prattail::wpda_walker::WpdaEngine;
use std::collections::BTreeSet;

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(128))]
    #[test]
    fn generated_digest_preserves_the_exact_selected_stream(
        number in proptest::num::i32::ANY,
        boolean in proptest::bool::ANY,
    ) {
        let engine = ledtest::LedTestWpdaEngine;
        let terms: Vec<std::sync::Arc<dyn std::any::Any + Send + Sync>> = vec![
            std::sync::Arc::new(ledtest::Num::NumLit(number)),
            std::sync::Arc::new(ledtest::Pred::BoolLit(boolean)),
            std::sync::Arc::new(ledtest::Expr::CastNum(std::sync::Arc::new(ledtest::Num::NumLit(number)))),
            std::sync::Arc::new(()),
        ];
        for term in terms {
            let bytes = <ledtest::LedTestWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint(&engine, &term);
            let expected = bytes.as_ref().map(|bytes|
                mettail_prattail::wpda_walker::SemanticFingerprintDigest::from_exact_key(bytes));
            let actual = <ledtest::LedTestWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint_digest(&engine, &term);
            proptest::prop_assert_eq!(actual, expected);
        }
    }

    #[test]
    fn generated_collection_lookup_preserves_the_declared_record(slot in 0u8..16) {
        let category = class3opt::WPDA_CATEGORIES.iter().position(|name| *name == "Proc").unwrap();
        let rule = class3opt::WPDA_RULES[category].iter()
            .find_map(|(name, index)| (*name == "PInputsOptTagged").then_some(*index)).unwrap();
        let actual = <class3opt::Class3OptWpdaEngine as WpdaEngine<LexicographicWeight>>::collection_spec(
            &class3opt::Class3OptWpdaEngine, category as u16, rule, slot,
        );
        if slot == 1 {
            let actual = actual.expect("the optional collection has one declared slot");
            proptest::prop_assert_eq!((actual.open, actual.close, actual.sep), ("", "]", "|"));
            proptest::prop_assert_eq!(actual.element_src_idx, Some(category as u16));
            proptest::prop_assert_eq!(actual.min_elements, 0);
            proptest::prop_assert_eq!(actual.kv_sep, None);
            proptest::prop_assert!(!actual.has_synth_paren && !actual.kv_value_optional);
            proptest::prop_assert!(actual.close_resumes_via_unwinding);
        } else {
            proptest::prop_assert!(actual.is_none());
        }
    }
}

fn led_key(term: &ledtest::Expr) -> Vec<u8> {
    let erased: std::sync::Arc<dyn std::any::Any + Send + Sync> = std::sync::Arc::new(term.clone());
    <ledtest::LedTestWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint(
        &ledtest::LedTestWpdaEngine,
        &erased,
    )
    .unwrap()
}

fn check_led(input: &str, trailing: bool) {
    let source = if trailing {
        format!("{input} )")
    } else {
        input.to_string()
    };
    let tokens = LatticeTokenSource::new(ledtest::lex_dag(&source).unwrap());
    let mut position = 0;
    let readings = ledtest::parse_Expr_via_wpda_ranked_prefix_with_source_and_bounding_mode(
        &tokens,
        &mut position,
        0,
        4096,
        CursorBoundingMode::Unbounded,
    )
    .unwrap();
    assert!(!readings.is_empty(), "{source}");
    if trailing {
        assert!(position < tokens.eof_node());
    } else {
        assert_eq!(position, tokens.eof_node());
    }
    let category = ledtest::WPDA_CATEGORIES
        .iter()
        .position(|category| *category == "Expr")
        .unwrap();
    let raw = facade_class_weights::enumerated_weights(
        ledtest::LedTestWpdaEngine,
        category as u16,
        &tokens,
    );
    let expected_keys: BTreeSet<_> = raw.iter().map(|(key, _)| key.clone()).collect();
    let keys: BTreeSet<_> = readings.iter().map(|(term, _, _)| led_key(term)).collect();
    assert_eq!(keys, expected_keys, "{source}");
    assert_eq!(readings.len(), keys.len(), "{source}");
    assert!(readings
        .windows(2)
        .all(|pair| (&pair[0].1, &pair[0].2) <= (&pair[1].1, &pair[1].2)));
    for (term, cost, rank) in &readings {
        let key = led_key(term);
        let minimum = raw
            .iter()
            .filter(|(candidate, _)| candidate == &key)
            .map(|(_, weight)| weight.primary.0)
            .min_by(f64::total_cmp)
            .unwrap();
        assert!((cost.to_f64() - minimum).abs() < 1e-12, "{source}: {cost:?} versus {minimum}");
        assert!(!rank.is_empty(), "{source}");
    }
    for limit in [0, 1, 2, readings.len(), readings.len() + 1] {
        let mut prefix_position = 0;
        let prefix = ledtest::parse_Expr_via_wpda_ranked_prefix_with_source_and_bounding_mode(
            &tokens,
            &mut prefix_position,
            0,
            limit,
            CursorBoundingMode::Unbounded,
        )
        .unwrap();
        assert_eq!(prefix_position, position);
        assert_eq!(prefix.len(), readings.len().min(limit));
        for (actual, expected) in prefix.iter().zip(&readings) {
            assert_eq!(led_key(&actual.0), led_key(&expected.0));
            assert_eq!((&actual.1, &actual.2), (&expected.1, &expected.2));
        }
    }
}

#[test]
fn ranked_prefix_preserves_native_values_operators_and_ambiguity() {
    for source in ["x", "(x)", "x + x", "false", "true and false", "1 + 2 * 3", "1 == 2"] {
        check_led(source, false);
        check_led(source, true);
    }
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]
    #[test]
    fn ranked_prefix_obeys_the_class_and_prefix_contract(
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
        check_led(&source, trailing);
    }
}

#[test]
fn ranked_prefix_handles_optional_collections_and_binders() {
    for source in ["0", "() . { 0 }", "() . { 0 } with []", "(@(0)?x) . { x } with [0 | 0]"] {
        let tokens = LatticeTokenSource::new(class3opt::lex_dag(source).unwrap());
        let mut position = 0;
        let ranked = class3opt::parse_Proc_via_wpda_ranked_prefix_with_source_and_bounding_mode(
            &tokens,
            &mut position,
            0,
            4096,
            CursorBoundingMode::Unbounded,
        )
        .unwrap();
        assert_eq!(position, tokens.eof_node());
        let category = class3opt::WPDA_CATEGORIES
            .iter()
            .position(|name| *name == "Proc")
            .unwrap();
        let raw = facade_class_weights::enumerated_weights(
            class3opt::Class3OptWpdaEngine,
            category as u16,
            &tokens,
        );
        let expected: BTreeSet<_> = raw.iter().map(|(key, _)| key.clone()).collect();
        let mut actual = BTreeSet::new();
        for (term, cost, rank) in ranked {
            let erased: std::sync::Arc<dyn std::any::Any + Send + Sync> = std::sync::Arc::new(term);
            let key = <class3opt::Class3OptWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint(
                &class3opt::Class3OptWpdaEngine, &erased,
            ).unwrap();
            let minimum = raw
                .iter()
                .filter(|(candidate, _)| candidate == &key)
                .map(|(_, weight)| weight.primary.0)
                .min_by(f64::total_cmp)
                .unwrap();
            assert!((cost.to_f64() - minimum).abs() < 1e-12, "{source}: {cost:?} versus {minimum}");
            assert!(!rank.is_empty());
            actual.insert(key);
        }
        assert_eq!(actual, expected, "{source}");
    }
}
