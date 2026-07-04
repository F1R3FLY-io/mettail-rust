mod support;

use std::collections::{BTreeSet, HashMap};

use dovetail::egraph::{EGraph, EGraphConfig, ENode};
use dovetail::rules::{Pattern, RewriteRule, SaturationOutcome, Subst};
use dovetail::set_automaton::PatternId;
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

type MatchObservation = (u32, Vec<(String, u32)>);

fn normalize_match(
    eg: &EGraph<String>,
    root: dovetail::egraph::EClassId,
    subst: &Subst,
) -> MatchObservation {
    let mut bindings: Vec<(String, u32)> = subst
        .iter()
        .map(|(name, &class)| (name.clone(), eg.find(class).0))
        .collect();
    bindings.sort();
    (eg.find(root).0, bindings)
}

fn recursive_positional_matches(
    eg: &EGraph<String>,
    pattern: &Pattern<String>,
) -> BTreeSet<MatchObservation> {
    let mut out = Vec::new();
    for class in eg.classes() {
        collect_positional_matches(eg, pattern, eg.find(class), &Subst::new(), &mut out);
    }
    out.into_iter()
        .map(|(root, subst)| normalize_match(eg, root, &subst))
        .collect()
}

fn collect_positional_matches(
    eg: &EGraph<String>,
    pattern: &Pattern<String>,
    class: dovetail::egraph::EClassId,
    subst: &Subst,
    out: &mut Vec<(dovetail::egraph::EClassId, Subst)>,
) {
    let class = eg.find(class);
    match pattern {
        Pattern::Var(name) => match subst.get(name) {
            Some(&existing) if eg.find(existing) == class => out.push((class, subst.clone())),
            Some(_) => {},
            None => {
                let mut next = subst.clone();
                next.insert(name.clone(), class);
                out.push((class, next));
            },
        },
        Pattern::App { op, args } => {
            let candidates: Vec<Vec<_>> = eg
                .nodes(class)
                .iter()
                .filter(|node| node.op == *op && node.children.len() == args.len())
                .map(|node| node.children.clone())
                .collect();
            for children in candidates {
                collect_positional_children(eg, args, &children, subst, class, out);
            }
        },
        Pattern::AcApp { .. } => unreachable!("property generator only emits positional patterns"),
    }
}

fn collect_positional_children(
    eg: &EGraph<String>,
    patterns: &[Pattern<String>],
    children: &[dovetail::egraph::EClassId],
    subst: &Subst,
    root: dovetail::egraph::EClassId,
    out: &mut Vec<(dovetail::egraph::EClassId, Subst)>,
) {
    if patterns.is_empty() {
        out.push((root, subst.clone()));
        return;
    }

    let mut child_matches = Vec::new();
    collect_positional_matches(eg, &patterns[0], children[0], subst, &mut child_matches);
    for (_, child_subst) in child_matches {
        collect_positional_children(eg, &patterns[1..], &children[1..], &child_subst, root, out);
    }
}

fn matching_property_graph(seed: u64) -> EGraph<String> {
    let mut eg = EGraph::<String>::new();
    let a = eg.add(ENode::leaf("a".into()));
    let b = eg.add(ENode::leaf("b".into()));
    let c = eg.add(ENode::leaf("c".into()));
    let d = eg.add(ENode::leaf("d".into()));
    let f_a = eg.add(ENode::new("f".into(), vec![a]));
    let f_b = eg.add(ENode::new("f".into(), vec![b]));
    let g_a = eg.add(ENode::new("g".into(), vec![a]));
    let pair_ab = eg.add(ENode::new("pair".into(), vec![a, b]));
    let pair_ba = eg.add(ENode::new("pair".into(), vec![b, a]));
    let pair_cd = eg.add(ENode::new("pair".into(), vec![c, d]));
    let _wrap_pair = eg.add(ENode::new("wrap".into(), vec![pair_ab]));
    let _pair_nested = eg.add(ENode::new("pair".into(), vec![f_a, g_a]));

    if seed & 0b0001 != 0 {
        eg.merge(a, b);
    }
    if seed & 0b0010 != 0 {
        eg.merge(f_a, g_a);
    }
    if seed & 0b0100 != 0 {
        eg.merge(pair_ab, pair_ba);
    }
    if seed & 0b1000 != 0 {
        eg.merge(f_b, pair_cd);
    }
    eg.rebuild();
    eg
}

fn op_name_strategy(names: &'static [&'static str]) -> impl Strategy<Value = String> {
    prop::sample::select(names).prop_map(str::to_owned)
}

fn positional_pattern_strategy() -> impl Strategy<Value = Pattern<String>> {
    let var = prop::sample::select(&["x", "y", "z"]).prop_map(Pattern::var);
    let leaf = op_name_strategy(&["a", "b", "c", "d", "missing_leaf"]).prop_map(Pattern::leaf);
    prop_oneof![var, leaf].prop_recursive(3, 24, 3, |inner| {
        let unary = (op_name_strategy(&["f", "g", "wrap", "missing_unary"]), inner.clone())
            .prop_map(|(op, child)| Pattern::app(op, vec![child]));
        let binary = (op_name_strategy(&["pair", "missing_binary"]), inner.clone(), inner)
            .prop_map(|(op, left, right)| Pattern::app(op, vec![left, right]));
        prop_oneof![unary, binary]
    })
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

#[test]
fn prop_set_automaton_matches_recursive_positional_oracle() {
    let strategy = (positional_pattern_strategy(), any::<u64>());
    let mut runner = TestRunner::new(Config {
        cases: env_cases("PROPTEST_CASES", 256),
        ..Config::default()
    });

    runner
        .run(&strategy, |(pattern, seed)| {
            let eg = matching_property_graph(seed);
            let run = eg
                .search_many_structural([(PatternId(0), pattern.clone())])
                .expect("property generator emits only positional patterns");
            let actual: BTreeSet<_> = run
                .matches
                .iter()
                .map(|matched| normalize_match(&eg, matched.root, &matched.subst))
                .collect();
            let expected = recursive_positional_matches(&eg, &pattern);

            prop_assert_eq!(actual, expected, "pattern {:?}, seed {}", pattern, seed);
            Ok(())
        })
        .expect("set automaton positional equivalence property failed");
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
