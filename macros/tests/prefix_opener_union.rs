//! Grammar-declared opening tokens must not silently elect one prefix route.
//!
//! The generated parser has a structural collection route and an ordinary
//! constructor for each tested opener. Complete parses of the empty forms are
//! intentionally ambiguous, so losing either route is observable at the
//! `parse_via_wpda_all` boundary. The examples cover a conventional pair,
//! a compound pair, a mixed pair, and two distinct collections sharing one
//! opener. A separate unique route exercises deep nesting without making the
//! deliberately ambiguous examples grow exponentially.

#![allow(unused_imports, dead_code)]

use mettail_runtime::Language;
use std::collections::BTreeSet;

#[path = "../../languages/tests/definitions/prefix_opener_union.rs"]
mod fixture;
use fixture::*;

fn readings(source: &str) -> BTreeSet<String> {
    Expr::parse_via_wpda_all(source)
        .unwrap_or_else(|error| panic!("failed to parse {source:?}: {error}"))
        .iter()
        .map(|term| format!("{term:?}"))
        .collect()
}

fn assert_has_routes(source: &str, labels: &[&str]) {
    let found = readings(source);
    for label in labels {
        assert!(
            found
                .iter()
                .any(|reading| reading.split('(').next() == Some(*label)),
            "{source:?} lost {label}; complete readings: {found:?}"
        );
    }
}

#[test]
fn square_opener_keeps_two_collections_and_the_ordinary_constructor() {
    assert_has_routes("[]", &["SquareComma", "SquareSemicolon", "SquareNullary"]);
}

#[test]
fn conventional_compound_and_mixed_pairs_keep_collection_and_ordinary_routes() {
    assert_has_routes("()", &["Round", "RoundNullary"]);
    assert_has_routes("{}", &["Curly", "CurlyNullary"]);
    assert_has_routes("{||}", &["Compound", "CompoundNullary"]);
    assert_has_routes("#{}", &["HashOpen", "HashNullary"]);
    assert_has_routes("Map()", &["MapRound", "MapRoundNullary"]);
    assert_has_routes("(]", &["Mixed", "MixedNullary"]);
}

#[test]
fn secondary_collection_opener_consumes_its_own_edge() {
    assert_has_routes("{|}", &["Curly"]);
}

#[test]
fn synthetic_collection_openers_require_the_parenthesis() {
    for source in ["Map x)", "seq x)"] {
        assert!(
            Expr::parse_via_wpda_all(source).is_err(),
            "accepted malformed opener: {source:?}"
        );
    }
}

#[test]
fn unique_collection_route_is_stack_safe_under_deep_nesting() {
    let depth = 256;
    let source = format!("{}x{}", "<".repeat(depth), ">".repeat(depth));
    let found = readings(&source);
    assert_eq!(found.len(), 1, "deep collection must have one complete reading");
    assert!(found
        .iter()
        .next()
        .is_some_and(|reading| reading.starts_with("Deep")));
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(16))]

    #[test]
    fn separator_evidence_disambiguates_shared_openers_without_losing_either_route(
        count in 2usize..7,
    ) {
        let comma = format!("[{}]", vec!["x"; count].join(","));
        let semicolon = format!("[{}]", vec!["x"; count].join(";"));
        let comma_readings = readings(&comma);
        let semicolon_readings = readings(&semicolon);
        proptest::prop_assert!(comma_readings.iter().any(|reading| reading.starts_with("SquareComma")));
        proptest::prop_assert!(!comma_readings.iter().any(|reading| reading.starts_with("SquareSemicolon")));
        proptest::prop_assert!(semicolon_readings.iter().any(|reading| reading.starts_with("SquareSemicolon")));
        proptest::prop_assert!(!semicolon_readings.iter().any(|reading| reading.starts_with("SquareComma")));
    }
}

struct FixtureHost([u8; 32]);

impl mettail_grammar_core::RuntimeHost for FixtureHost {
    fn capability_manifest(
        &self,
        key: &mettail_grammar_core::RuntimeCapabilityKey,
    ) -> Option<mettail_grammar_core::RuntimeCapabilityManifest> {
        (key.language_fingerprint == self.0).then(|| {
            mettail_grammar_core::RuntimeCapabilityManifest {
                key: key.clone(),
                code_commitment: [1; 32],
                abi: "prefix-opener-parity/1".into(),
                effects: [mettail_grammar_core::RuntimeEffect::Reduce]
                    .into_iter()
                    .collect(),
                cost: mettail_grammar_core::RuntimeLogicalCost {
                    base: 1,
                    per_input_byte: 1,
                    per_value: 1,
                    maximum: 1024,
                },
            }
        })
    }

    fn decode_token(&self, _: &str, _: &str) -> Result<mettail_grammar_core::DynamicValue, String> {
        panic!("constructor-only fixture must not decode a native token")
    }

    fn evaluate(
        &self,
        _: &mettail_grammar_core::NativeEvaluation,
        _: &[mettail_grammar_core::DynamicValue],
        _: mettail_grammar_core::SourceSpan,
    ) -> Result<mettail_grammar_core::DynamicValue, String> {
        panic!("constructor-only fixture must not run native evaluation")
    }
}

#[test]
fn owned_and_generated_wpdas_preserve_the_same_weighted_collision_readings() {
    assert_owned_generated_parity(&[
        "[]", "()", "{}", "{||}", "{|}", "#{}", "Map()", "(]", "<x>", "x",
    ]);
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(24))]

    #[test]
    fn owned_collection_actions_preserve_weighted_readings(
        count in 0usize..6,
        kind in 0usize..8,
        compound_element in proptest::bool::ANY,
    ) {
        let (open, separator, close) = [
            ("[", ",", "]"), ("[", ";", "]"), ("(", ",", ")"),
            ("{", ",", "}"), ("{|", ",", "|}"), ("#{", ",", "}"),
            ("Map(", ",", ")"),
            ("seq(", ",", ")"),
        ][kind];
        let element = if compound_element { "pair(x,x)" } else { "x" };
        let source = format!("{open}{}{close}", vec![element; count].join(separator));
        assert_owned_generated_parity(&[&source, element]);
    }
}

fn assert_owned_generated_parity(source_texts: &[&str]) {
    use mettail_grammar_core as core;
    use mettail_prattail::runtime_backend::{
        compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI,
    };
    use mettail_prattail::wpda_owned::absorption::derive_absorption_rows;
    use mettail_prattail::wpda_owned::actions::{OwnedActionProvider, OwnedTerm};
    use mettail_prattail::wpda_owned::engine::OwnedWpdaEngine;
    use mettail_prattail::wpda_owned::source::{OwnedTokenSource, SourceAdapterLimits};
    use mettail_prattail::wpda_rule_analysis::authored_descriptors::{
        derive_authored_descriptors, DescriptorOptions,
    };
    use mettail_prattail::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
    use mettail_prattail::wpda_runtime::WpdaResolveResult;
    use mettail_prattail::wpda_walker::{RealizeRequestMode, WpdaWalker};
    use std::convert::Infallible;

    let metadata = PrefixOpenerUnionLanguage.metadata();
    let artifacts = metadata
        .generated_semantic_artifacts_v1()
        .unwrap_or_else(|| {
            panic!(
                "original grammar refused: {:?}",
                metadata.generated_semantic_artifact_refusal_v1()
            )
        });
    let grammar: core::GrammarCoreV1 =
        postcard::from_bytes(artifacts.grammar_core_postcard).expect("captured grammar decodes");
    let occurrences: Vec<usize> = grammar
        .wpda_original_occurrences
        .as_ref()
        .expect("macro records original authored rules")
        .iter()
        .map(|id| id.0 as usize)
        .collect();
    let synthesis = derive_authored_rules(&grammar, &occurrences, |_| Ok::<_, Infallible>(()))
        .expect("shared authored synthesis");
    let descriptors = derive_authored_descriptors(
        &grammar,
        &occurrences,
        synthesis,
        DescriptorOptions {
            crosscat_lex_compat_gate: true,
            prefix_factoring: false,
            mixfix_factoring: false,
            accept_continue: false,
            recovery_base: 0xFE00,
            max_mixfix_slice: usize::MAX,
        },
        |_, _, _, _| Ok::<_, Infallible>(()),
        |_, _| Ok::<_, Infallible>(false),
    )
    .expect("shared owned descriptors");
    assert!(
        descriptors
            .collections
            .iter()
            .any(|row| !row.spec.close_resumes_via_unwinding),
        "fixture must exercise previously rejected standalone collections"
    );
    let absorption =
        derive_absorption_rows(&grammar, &descriptors).expect("original absorption observations");
    let image = compile_parser_image(&grammar).expect("original runtime lexical image");
    let host = FixtureHost(grammar.fingerprint().expect("fixture fingerprint"));
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("fixture runtime parser admits original image");

    for &source_text in source_texts {
        let session = parser
            .lexical_session(source_text)
            .expect("shared lexical session");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 1024,
                edges: 4096,
                text_bytes: 65536,
            },
        )
        .expect("shared token observations");
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("owned actions admit fixture");
        let engine = OwnedWpdaEngine::new(
            &descriptors,
            &actions,
            0,
            &[],
            &absorption,
            |_| Ok(()),
            |_| Ok(()),
        )
        .expect("owned routing admits standalone collections");
        let mut owned = WpdaWalker::new_for_category(engine, 0, 0);
        owned
            .run_to_end_of_input(10000, &source)
            .expect("owned walk");
        let WpdaResolveResult::Accepted { roots, .. } = owned.resolve_at_end_of_input(&source)
        else {
            panic!("owned engine refused {source_text:?}");
        };
        let mut owned_readings = Vec::new();
        for root in roots {
            for (value, weight) in owned
                .realize_root_to_terms_with_weights(
                    root,
                    Some(32),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("owned complete readings")
            {
                let term = value
                    .downcast_ref::<OwnedTerm>()
                    .expect("owned term carrier");
                let core::DynamicValue::Term(node) = &term.value else {
                    panic!("owned root must be a declared constructor")
                };
                let label = grammar
                    .productions
                    .iter()
                    .find(|production| production.constructor == node.constructor)
                    .expect("owned constructor is declared")
                    .label
                    .clone();
                owned_readings.push((label, weight));
            }
        }
        owned_readings.sort();
        owned_readings.dedup();

        let mut generated = WpdaWalker::new_for_category(PrefixOpenerUnionWpdaEngine, 0, 0);
        generated
            .run_to_end_of_input(10000, &source)
            .expect("generated walk");
        let WpdaResolveResult::Accepted { roots, .. } = generated.resolve_at_end_of_input(&source)
        else {
            panic!("generated engine refused {source_text:?}");
        };
        let mut generated_readings = Vec::new();
        for root in roots {
            for (value, weight) in generated
                .realize_root_to_terms_with_weights(
                    root,
                    Some(32),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("generated complete readings")
            {
                let term = value
                    .downcast_ref::<Expr>()
                    .expect("generated term carrier");
                let debug = format!("{term:?}");
                let label = debug.split('(').next().expect("constructor debug label");
                generated_readings.push((label.to_owned(), weight));
            }
        }
        generated_readings.sort();
        generated_readings.dedup();
        assert_eq!(owned_readings, generated_readings, "weighted route parity for {source_text:?}");
    }
}
