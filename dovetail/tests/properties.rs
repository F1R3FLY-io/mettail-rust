mod support;

use std::collections::HashMap;

use dovetail::egraph::{EGraph, EGraphConfig, ENode};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome};
use dovetail::space::{Fired, InMemSpace, Match, TupleSpace};
use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};

use support::{
    build_acyclic, derivation_count_upper_bound, extractor_observations,
    extractor_observations_with_heuristic, generated_bounded_acyclic_spec, oracle_observations,
};

const MAX_PROPERTY_DERIVATIONS: usize = 2048;

#[test]
fn bounded_property_generator_respects_complete_output_cap() {
    for class_count in 1..=6 {
        for seed in 0..512u64 {
            let spec = generated_bounded_acyclic_spec(seed, class_count, MAX_PROPERTY_DERIVATIONS);
            assert!(
                derivation_count_upper_bound(&spec, MAX_PROPERTY_DERIVATIONS)
                    <= MAX_PROPERTY_DERIVATIONS,
                "bounded generator exceeded cap for seed {seed}, classes {class_count}: {spec:?}"
            );
        }
    }
}

fn env_cases(var: &str, default: u32) -> u32 {
    std::env::var(var)
        .ok()
        .and_then(|raw| raw.parse::<u32>().ok())
        .filter(|cases| *cases > 0)
        .unwrap_or(default)
}

#[test]
fn prop_extractor_matches_bruteforce_acyclic_oracle() {
    let strategy = (1usize..=6, any::<u64>());
    let mut runner = TestRunner::new(Config {
        cases: env_cases("PROPTEST_CASES", 256),
        ..Config::default()
    });

    runner
        .run(&strategy, |(class_count, seed)| {
            let spec = generated_bounded_acyclic_spec(seed, class_count, MAX_PROPERTY_DERIVATIONS);
            let (eg, roots) = build_acyclic(&spec);
            let root = roots[class_count - 1];

            let extracted = extractor_observations(&eg, root);
            let oracle = oracle_observations(&eg, root);
            prop_assert_eq!(extracted.len(), oracle.len());
            for (idx, (actual, expected)) in extracted.iter().zip(&oracle).enumerate() {
                prop_assert_eq!(
                    actual,
                    expected,
                    "mismatch at derivation {} for seed {}, classes {}",
                    idx,
                    seed,
                    class_count
                );
            }
            Ok(())
        })
        .expect("acyclic extraction property failed");
}

#[test]
fn prop_heuristic_is_result_invariant() {
    let strategy = (1usize..=6, any::<u64>());
    let mut runner = TestRunner::new(Config {
        cases: env_cases("PROPTEST_CASES", 256),
        ..Config::default()
    });

    runner
        .run(&strategy, |(class_count, seed)| {
            let spec = generated_bounded_acyclic_spec(seed, class_count, MAX_PROPERTY_DERIVATIONS);
            let (eg, roots) = build_acyclic(&spec);
            let root = roots[class_count - 1];

            prop_assert_eq!(
                extractor_observations_with_heuristic(&eg, root),
                extractor_observations(&eg, root)
            );
            Ok(())
        })
        .expect("heuristic invariance property failed");
}

#[test]
fn prop_budgeted_saturation_never_overshoots_and_reports_refusal() {
    let strategy = (3usize..=24, 1usize..=12);
    let mut runner = TestRunner::new(Config {
        cases: env_cases("PROPTEST_CASES", 128),
        ..Config::default()
    });

    runner
        .run(&strategy, |(budget, max_iters)| {
            let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: budget });
            let a = eg.add(ENode::leaf("a".into()));
            let _root = eg.add(ENode::new("f".into(), vec![a]));
            let grow = RewriteRule {
                lhs: Pattern::app("f".into(), vec![Pattern::var("x")]),
                rhs: Pattern::app(
                    "f".into(),
                    vec![Pattern::app("h".into(), vec![Pattern::var("x")])],
                ),
                label: Some("grow".into()),
            };

            let report = eg.saturate(&[grow], max_iters);

            prop_assert!(
                eg.node_count() <= budget,
                "node_count {} exceeded budget {budget}",
                eg.node_count()
            );
            let node_limited = report.outcome == SaturationOutcome::NodeLimit;
            prop_assert_eq!(node_limited, eg.node_limit_reached());
            Ok(())
        })
        .expect("budgeted saturation property failed");
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TestPat {
    Any,
    Exact(i64),
}

#[derive(Clone, Debug)]
enum SpaceOp {
    Produce { chan: u8, data: i64 },
    Consume { chan: u8, pat: TestPat, k: u16 },
}

struct TestMatch;

impl Match<TestPat, i64> for TestMatch {
    type Bindings = i64;

    fn matches(&self, pat: &TestPat, data: &i64) -> Option<Self::Bindings> {
        match pat {
            TestPat::Any => Some(*data),
            TestPat::Exact(expected) => (*expected == *data).then_some(*data),
        }
    }
}

fn pat_strategy() -> impl Strategy<Value = TestPat> {
    prop_oneof![Just(TestPat::Any), (-4i64..=4).prop_map(TestPat::Exact)]
}

fn op_strategy() -> impl Strategy<Value = SpaceOp> {
    prop_oneof![
        (0u8..=3, -4i64..=4).prop_map(|(chan, data)| SpaceOp::Produce { chan, data }),
        (0u8..=3, pat_strategy(), 0u16..=32).prop_map(|(chan, pat, k)| SpaceOp::Consume {
            chan,
            pat,
            k
        }),
    ]
}

fn model_match(pat: &TestPat, data: i64) -> Option<i64> {
    match pat {
        TestPat::Any => Some(data),
        TestPat::Exact(expected) => (*expected == data).then_some(data),
    }
}

#[test]
fn prop_in_memory_tuplespace_matches_fifo_reference_model() {
    let strategy = proptest::collection::vec(op_strategy(), 0..96);
    let mut runner = TestRunner::new(Config {
        cases: env_cases("PROPTEST_CASES", 128),
        ..Config::default()
    });

    runner
        .run(&strategy, |ops| {
            let mut actual = InMemSpace::<u8, TestPat, i64, u16, TestMatch>::new(TestMatch);
            let mut data: HashMap<u8, Vec<i64>> = HashMap::new();
            let mut conts: HashMap<u8, Vec<(TestPat, u16)>> = HashMap::new();

            for op in ops {
                match op {
                    SpaceOp::Produce { chan, data: datum } => {
                        let expected = if let Some(waiting) = conts.get_mut(&chan) {
                            if let Some(idx) = waiting
                                .iter()
                                .position(|(pat, _)| model_match(pat, datum).is_some())
                            {
                                let (pat, k) = waiting.remove(idx);
                                Some(Fired {
                                    partner: k,
                                    bindings: model_match(&pat, datum).expect("matched"),
                                })
                            } else {
                                data.entry(chan).or_default().push(datum);
                                None
                            }
                        } else {
                            data.entry(chan).or_default().push(datum);
                            None
                        };
                        prop_assert_eq!(actual.produce(chan, datum), expected);
                    },
                    SpaceOp::Consume { chan, pat, k } => {
                        let expected = if let Some(waiting) = data.get_mut(&chan) {
                            if let Some(idx) =
                                waiting.iter().position(|d| model_match(&pat, *d).is_some())
                            {
                                let datum = waiting.remove(idx);
                                Some(Fired {
                                    partner: datum,
                                    bindings: model_match(&pat, datum).expect("matched"),
                                })
                            } else {
                                conts.entry(chan).or_default().push((pat.clone(), k));
                                None
                            }
                        } else {
                            conts.entry(chan).or_default().push((pat.clone(), k));
                            None
                        };
                        prop_assert_eq!(actual.consume(chan, pat, k), expected);
                    },
                }

                for chan in 0u8..=3 {
                    prop_assert_eq!(actual.parked_data(&chan), data.get(&chan).map_or(0, Vec::len));
                    prop_assert_eq!(
                        actual.parked_conts(&chan),
                        conts.get(&chan).map_or(0, Vec::len)
                    );
                }
            }
            Ok(())
        })
        .expect("tuplespace property failed");
}
