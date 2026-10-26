#![cfg(feature = "rholang")]

use mettail_languages::rholang::*;
use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_walker::WpdaEngine;
use std::sync::Arc;

#[path = "support/facade_class_weights.rs"]
mod facade_class_weights;

fn semantic_key(term: &Proc) -> Vec<u8> {
    let erased: Arc<dyn std::any::Any + Send + Sync> = Arc::new(term.clone());
    <RholangWpdaEngine as WpdaEngine<LexicographicWeight>>::semantic_fingerprint(
        &RholangWpdaEngine,
        &erased,
    )
    .expect("generated Proc semantic key")
}

#[test]
fn transparent_casts_share_a_key_but_keep_distinct_native_values() {
    for value in [false, true] {
        let boolean = Arc::new(Bool::BoolLit(value));
        let direct = Proc::CastBool(boolean.clone());
        let converted = Proc::CastUInt32(Arc::new(UInt32::BoolToUInt32(boolean)));
        assert_eq!(semantic_key(&direct), semantic_key(&converted));
        let Proc::CastBool(b) = &direct else {
            unreachable!()
        };
        let Proc::CastUInt32(n) = &converted else {
            unreachable!()
        };
        assert_eq!(b.try_eval(), Some(value));
        assert_eq!(n.try_eval(), Some(u32::from(value)));
        assert_ne!(format!("{direct:?}"), format!("{converted:?}"));
    }
    assert_eq!(WPDA_RULES[0][39], ("CastUInt32", 39));
    assert_eq!(WPDA_RULES[0][40], ("CastBool", 40));
    assert!(
        LexicographicWeight::from_cost(0.0, 0, 39) < LexicographicWeight::from_cost(0.0, 0, 40)
    );
}

fn elected_representative(source: &str) -> (String, String) {
    let single = Proc::parse_via_wpda(source).expect("single result");
    let (all, weights) = Proc::parse_via_wpda_all_with_weights(source).expect("all results");
    let key = semantic_key(&single);
    let matching: Vec<_> = all
        .iter()
        .enumerate()
        .filter(|(_, term)| semantic_key(term) == key)
        .collect();
    assert_eq!(matching.len(), 1, "one class for the elected key: {source:?}");
    let (index, representative) = matching[0];
    eprintln!("ELECTION source={source:?} single={single:?} all={representative:?} weight={:?} classes={}", weights[index], all.len());
    (format!("{single:?}"), format!("{representative:?}"))
}

#[test]
fn all_results_keep_the_existing_single_result_representative() {
    let mut mismatches = Vec::new();
    for source in ["false", "not false", "true and true", "int(false, 64)"] {
        let (single, all) = elected_representative(source);
        if single != all {
            mismatches.push((source, single, all));
        }
    }
    assert!(mismatches.is_empty(), "representative mismatches: {mismatches:#?}");
}

#[test]
fn distinct_parenthesized_name_classes_remain_available() {
    let (terms, weights) =
        Proc::parse_via_wpda_all_with_weights("@((a)!(0))!()").expect("ambiguous quoted send");
    assert_eq!(terms.len(), 4);
    assert_eq!(weights.len(), terms.len());
    let keys: std::collections::BTreeSet<_> = terms.iter().map(semantic_key).collect();
    assert_eq!(keys.len(), terms.len());
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn boolean_classes_keep_the_elected_constructor_tree(
        left in proptest::bool::ANY,
        right in proptest::bool::ANY,
        operator in 0usize..4,
        depth in 0usize..4,
    ) {
        let mut source = match operator {
            0 => format!("{left}"),
            1 => format!("{left} and {right}"),
            2 => format!("{left} or {right}"),
            _ => format!("{left} implies {right}"),
        };
        for _ in 0..depth { source = format!("not ({source})"); }
        let (single, all) = elected_representative(&source);
        proptest::prop_assert_eq!(single, all, "{}", source);
    }
}

#[test]
fn aligned_boolean_class_retains_its_minimum_weight() {
    let (terms, weights) = Proc::parse_via_wpda_all_with_weights("false").unwrap();
    assert_eq!(terms.len(), 1);
    assert!(
        matches!(&terms[0], Proc::CastBool(value) if matches!(value.as_ref(), Bool::BoolLit(false)))
    );
    assert_eq!(weights[0].rule_idx, 39);
    assert_class_minimum("false", &terms[0], weights[0]);
}

#[test]
fn trailing_input_uses_the_same_elected_representative() {
    use mettail_prattail::wpda_runtime::LatticeTokenSource;
    let source = LatticeTokenSource::new(lex_dag("false ;").unwrap());
    let mut position = 0;
    let (terms, weights) = parse_Proc_via_wpda_all_with_source(&source, &mut position, 0).unwrap();
    assert_eq!(position, 1);
    assert_eq!(terms.len(), 1);
    assert!(
        matches!(&terms[0], Proc::CastBool(value) if matches!(value.as_ref(), Bool::BoolLit(false)))
    );
    assert_eq!(weights[0].rule_idx, 39);
    assert_class_minimum("false ;", &terms[0], weights[0]);
}

fn assert_class_minimum(source: &str, term: &Proc, weight: LexicographicWeight) {
    use mettail_prattail::wpda_runtime::LatticeTokenSource;
    let tokens = LatticeTokenSource::new(lex_dag(source).unwrap());
    let category = WPDA_CATEGORIES
        .iter()
        .position(|name| *name == "Proc")
        .unwrap();
    let raw = facade_class_weights::enumerated_weights(
        RholangWpdaEngine,
        u16::try_from(category).unwrap(),
        &tokens,
    );
    let key = semantic_key(term);
    let expected = raw
        .into_iter()
        .filter(|(candidate, _)| *candidate == key)
        .map(|(_, weight)| weight)
        .min()
        .expect("the raw forest contains the class");
    eprintln!(
        "CLASS_WEIGHT source={source:?} primary={:.17e} bits={:016x} raw_minimum={:.17e}",
        weight.primary.value(),
        weight.primary.value().to_bits(),
        expected.primary.value()
    );
    assert_eq!(weight, expected, "the class keeps its exact raw minimum");
}
