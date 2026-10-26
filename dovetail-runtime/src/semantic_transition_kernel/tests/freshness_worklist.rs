//! The freshness primitive's completed verdict, not a second source evaluator.
//!
//! The independent oracle closes the finite FreeOccurrence relation upwards.
//! It has no pending/visited stack and does not decode the runtime graph.
//! These raw primitive fixtures do not claim typed source-input admission.

use super::*;
use proptest::prelude::*;

#[derive(Clone, Debug)]
enum GroundNode {
    Plain(Vec<usize>),
    Abstraction { binder: usize, body: usize },
}

fn free_occurrence_closure(nodes: &[GroundNode], needle: usize) -> Vec<bool> {
    let mut occurs = vec![false; nodes.len()];
    occurs[needle] = true;
    // Each strict round adds a vertex, so this also works for finite cycles.
    for _ in 0..=nodes.len() {
        let previous = occurs.clone();
        for (root, node) in nodes.iter().enumerate() {
            occurs[root] |= match node {
                GroundNode::Plain(children) => children.iter().any(|&child| previous[child]),
                GroundNode::Abstraction { binder, body } => *binder != needle && previous[*body],
            };
        }
        if previous == occurs {
            return occurs;
        }
    }
    panic!("finite occurrence closure must stabilize");
}

fn plain(
    graph: &mut EGraph<FramedSemanticOperator>,
    label: u32,
    children: Vec<EClassId>,
) -> EClassId {
    add(graph, TheoryImageOperatorV1::Constructor(TheoryConstructorId(label)), children)
}

fn abstraction(
    graph: &mut EGraph<FramedSemanticOperator>,
    sort: u32,
    binder: EClassId,
    body: EClassId,
) -> EClassId {
    add(
        graph,
        TheoryImageOperatorV1::Abstraction { sort: TheorySortId(sort) },
        vec![binder, body],
    )
}

fn build_dag(nodes: &[GroundNode], salt: u16) -> (EGraph<FramedSemanticOperator>, Vec<EClassId>) {
    let mut graph = EGraph::new();
    let mut roots = Vec::new();
    for (index, node) in nodes.iter().enumerate() {
        let label = u32::from(salt) + index as u32;
        let root = match node {
            GroundNode::Plain(children) => {
                plain(&mut graph, label, children.iter().map(|&child| roots[child]).collect())
            },
            GroundNode::Abstraction { binder, body } => {
                abstraction(&mut graph, label, roots[*binder], roots[*body])
            },
        };
        roots.push(root);
    }
    (graph, roots)
}

fn assert_completed(
    graph: &EGraph<FramedSemanticOperator>,
    needle: EClassId,
    target: EClassId,
    fresh: bool,
    prefix: u64,
) -> u64 {
    let mut work = prefix;
    assert_eq!(
        freshness_holds(graph, needle, target, &mut work, 10_000, &mut || false),
        Ok(fresh)
    );
    let used = work - prefix;
    assert!(used > 0);

    // A completed result is reproducible at its exact allowance. Every smaller
    // prefix is an explicit refusal, never evidence for the opposite verdict.
    for allowance in 0..used {
        let mut work = prefix;
        assert_eq!(
            freshness_holds(graph, needle, target, &mut work, prefix + allowance, &mut || false),
            Err(SemanticMatchUndetermined::WorkBudgetExhausted),
        );
        assert_eq!(work, prefix + allowance);
    }
    let mut exact_work = prefix;
    assert_eq!(
        freshness_holds(graph, needle, target, &mut exact_work, prefix + used, &mut || false),
        Ok(fresh),
    );
    assert_eq!(exact_work, prefix + used);

    for cancel_at in 1..=used {
        let mut calls = 0;
        let mut work = prefix;
        assert_eq!(
            freshness_holds(graph, needle, target, &mut work, prefix + used, &mut || {
                calls += 1;
                calls == cancel_at
            }),
            Err(SemanticMatchUndetermined::Cancelled),
        );
        assert_eq!(calls, cancel_at);
        assert_eq!(work, prefix + cancel_at - 1);
    }
    used
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn generated_freshness_shared_dags_match_free_occurrence_closure(
        extensions in prop::collection::vec(
            (any::<bool>(), any::<u8>(), any::<u8>(), prop::collection::vec(any::<u8>(), 0..5)),
            0..10,
        ),
        salt in any::<u16>(),
        chosen_needle in any::<u8>(),
        prefix in 0u64..8,
    ) {
        let mut nodes = vec![
            GroundNode::Plain(vec![]), // the distinguished needle
            GroundNode::Plain(vec![]),
            GroundNode::Plain(vec![0]), // a different binder containing the needle
            GroundNode::Abstraction { binder: 0, body: 2 },
            GroundNode::Abstraction { binder: 2, body: 1 },
            GroundNode::Abstraction { binder: 1, body: 2 },
            GroundNode::Plain(vec![3, 3, 4]), // shared shielded nodes, no free occurrence
            GroundNode::Plain(vec![6, 5, 6]), // shared and unshielded paths coexist
        ];
        for (is_abstraction, binder, body, children) in extensions {
            let count = nodes.len();
            nodes.push(if is_abstraction {
                GroundNode::Abstraction {
                    binder: usize::from(binder) % count,
                    body: usize::from(body) % count,
                }
            } else {
                GroundNode::Plain(children.into_iter().map(|child| usize::from(child) % count).collect())
            });
        }
        let (graph, roots) = build_dag(&nodes, salt);
        let edge_bound = 1 + nodes.iter().map(|node| match node {
            GroundNode::Plain(children) => children.len(),
            GroundNode::Abstraction { .. } => 1,
        }).sum::<usize>();
        for needle in [0, usize::from(chosen_needle) % nodes.len()] {
            let occurs = free_occurrence_closure(&nodes, needle);
            for (target, &root) in roots.iter().enumerate() {
                let used = assert_completed(&graph, roots[needle], root, !occurs[target], prefix);
                prop_assert!(used <= edge_bound as u64);
            }
        }
        // The duplicate is still charged when popped, but not expanded again.
        prop_assert_eq!(assert_completed(&graph, roots[0], roots[6], true, prefix), 5);
        // Root identity wins even when the root is itself an abstraction.
        prop_assert_eq!(assert_completed(&graph, roots[3], roots[3], false, prefix), 1);
    }

    #[test]
    fn generated_freshness_normalizes_needle_root_children_and_binders(
        salt in any::<u16>(),
        reverse_merge in any::<bool>(),
        prefix in 0u64..8,
    ) {
        let mut graph = EGraph::new();
        let label = u32::from(salt);
        let left = plain(&mut graph, label, vec![]);
        let right = plain(&mut graph, label + 1, vec![]);
        let other = plain(&mut graph, label + 2, vec![]);
        let left_child = plain(&mut graph, label + 3, vec![left]);
        let right_child = plain(&mut graph, label + 3, vec![right]);
        let left_bound = abstraction(&mut graph, label, left, right_child);
        let right_bound = abstraction(&mut graph, label + 1, right, left_child);
        let different_binder = abstraction(&mut graph, label + 2, right_child, other);
        if reverse_merge {
            graph.merge(right, left);
        } else {
            graph.merge(left, right);
        }
        // Before rebuild, stored child/binder IDs include a noncanonical alias.
        // The ambiguous needle class is never decoded: equality is tested first.
        for needle in [left, right] {
            for alias in [left, right] {
                prop_assert_eq!(assert_completed(&graph, needle, alias, false, prefix), 1);
            }
            for bound in [left_bound, right_bound] {
                prop_assert_eq!(assert_completed(&graph, needle, bound, true, prefix), 1);
            }
            for child in [left_child, right_child] {
                prop_assert_eq!(assert_completed(&graph, needle, child, false, prefix), 2);
            }
            prop_assert_eq!(assert_completed(&graph, needle, different_binder, true, prefix), 2);
        }
        graph.rebuild();
        prop_assert_ne!(left_child, right_child);
        prop_assert!(graph.equiv(left_child, right_child));
        prop_assert_eq!(graph.nodes(left_child).len(), 1);
        // Congruent root aliases now have one decoded node. Both target and
        // needle normalization must preserve their completed free-occurrence result.
        for needle in [left, right] {
            for target in [left_child, right_child] {
                prop_assert_eq!(assert_completed(&graph, needle, target, false, prefix), 2);
            }
        }
    }

    #[test]
    fn generated_freshness_refuses_reachable_malformed_and_cyclic_classes(
        salt in any::<u16>(),
        depth in 0usize..6,
        prefix in 0u64..8,
    ) {
        for malformed in 0..6 {
            let mut graph = EGraph::new();
            let label = u32::from(salt);
            let needle = plain(&mut graph, label, vec![]);
            let other = plain(&mut graph, label + 1, vec![]);
            let bad = match malformed {
                0 => graph.add(ENode::leaf(FramedSemanticOperator::new(99, vec![]))),
                1 => add(&mut graph, TheoryImageOperatorV1::Abstraction { sort: TheorySortId(label) }, vec![other]),
                2 => add(&mut graph, TheoryImageOperatorV1::Abstraction { sort: TheorySortId(label) }, vec![other, other, other]),
                3 => graph.add(ENode::new(FramedSemanticOperator::new(
                    THEORY_OPERATOR_DISCRIMINANT,
                    vec![THEORY_OPERATOR_DOMAIN.to_vec(), vec![1, 0, 0, 0]],
                ), vec![other, other])),
                4 => {
                    let first = plain(&mut graph, label + 2, vec![]);
                    let second = plain(&mut graph, label + 3, vec![]);
                    graph.merge(first, second);
                    first
                },
                5 => {
                    let leaf = plain(&mut graph, label + 2, vec![]);
                    let parent = plain(&mut graph, label + 3, vec![leaf]);
                    graph.merge(leaf, parent);
                    graph.rebuild();
                    prop_assert!(graph.nodes(leaf).iter().any(|node| node.children.iter().any(|&child| graph.equiv(child, leaf))));
                    leaf
                },
                _ => unreachable!(),
            };
            let mut target = bad;
            for index in 0..depth {
                target = plain(&mut graph, label + 10 + index as u32, vec![target]);
            }
            let mut work = prefix;
            prop_assert_eq!(
                freshness_holds(&graph, needle, target, &mut work, 10_000, &mut || false),
                Err(SemanticMatchUndetermined::InvalidImageEvidence),
            );
            prop_assert_eq!(work, prefix + depth as u64 + 1);

            let shielded = abstraction(&mut graph, label + 20, needle, target);
            let exposed = abstraction(&mut graph, label + 21, other, target);
            let private_binder = abstraction(&mut graph, label + 22, target, other);
            prop_assert_eq!(assert_completed(&graph, needle, shielded, true, prefix), 1);
            prop_assert_eq!(assert_completed(&graph, needle, private_binder, true, prefix), 2);
            let mut work = prefix;
            prop_assert_eq!(
                freshness_holds(&graph, needle, exposed, &mut work, 10_000, &mut || false),
                Err(SemanticMatchUndetermined::InvalidImageEvidence),
            );
            prop_assert_eq!(work, prefix + depth as u64 + 2);
            prop_assert_eq!(assert_completed(&graph, bad, bad, false, prefix), 1);

            if malformed == 5 {
                // Public bottom-up EGraph construction creates cycles by merging
                // distinct nodes. Such a reachable class is ambiguous and cannot
                // be admitted as a source input, even under a shielding binder.
                prop_assert!(graph.nodes(bad).len() > 1);
                prop_assert!(
                    matches!(
                        SemanticTransitionInput::admit(
                            graph,
                            shielded,
                            SemanticInputLimits { work: 10_000, nodes: 100, bytes: 100_000 },
                            || false,
                        ),
                        SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected)
                    ),
                    "shielding does not admit a cyclic multi-node source input",
                );
            }
        }
    }
}
