mod support;

use dovetail::egraph::{EGraph, ENode};
use rigail::TropicalWeight;

use support::{
    assert_observations_eq, build_acyclic, extractor_observations,
    extractor_observations_with_heuristic, generated_acyclic_spec, oracle_observations, EdgeSpec,
};

#[test]
fn small_acyclic_graphs_match_bruteforce_oracle() {
    for class_count in 1..=4 {
        for seed in 0..256u64 {
            let spec = generated_acyclic_spec(seed, class_count);
            let (eg, roots) = build_acyclic(&spec);
            let root = roots[class_count - 1];

            let oracle = oracle_observations(&eg, root);
            let extracted = extractor_observations(&eg, root);
            assert_observations_eq(
                &extracted,
                &oracle,
                &format!("seed {seed}, classes {class_count}: {spec:?}"),
            );
        }
    }
}

#[test]
fn equal_weight_alternatives_are_exhaustively_enumerated() {
    let spec = support::AcyclicSpec {
        classes: vec![
            vec![
                EdgeSpec {
                    op: "a".into(),
                    weight: 1,
                    children: vec![],
                },
                EdgeSpec {
                    op: "b".into(),
                    weight: 1,
                    children: vec![],
                },
            ],
            vec![
                EdgeSpec {
                    op: "pair_left".into(),
                    weight: 2,
                    children: vec![0, 0],
                },
                EdgeSpec {
                    op: "pair_right".into(),
                    weight: 2,
                    children: vec![0, 0],
                },
            ],
        ],
    };
    let (eg, roots) = build_acyclic(&spec);
    let extracted = extractor_observations(&eg, roots[1]);

    assert_observations_eq(&extracted, &oracle_observations(&eg, roots[1]), "equal weights");
    assert_eq!(
        extracted.len(),
        8,
        "2 parent edges times 2x2 child derivation choices must all survive"
    );
    assert!(extracted.windows(2).all(|w| w[0].weight <= w[1].weight));
    assert!(
        extracted
            .iter()
            .all(|obs| obs.weight == TropicalWeight::new(4.0)),
        "all alternatives have the same total weight"
    );
}

#[test]
fn heuristic_order_matches_plain_order_for_all_bounded_acyclic_graphs() {
    for class_count in 1..=4 {
        for seed in 256..384u64 {
            let spec = generated_acyclic_spec(seed, class_count);
            let (eg, roots) = build_acyclic(&spec);
            let root = roots[class_count - 1];

            assert_eq!(
                extractor_observations_with_heuristic(&eg, root),
                extractor_observations(&eg, root),
                "heuristic changed extraction for seed {seed}, classes {class_count}: {spec:?}"
            );
        }
    }
}

#[test]
fn exhaustive_congruence_closure_for_two_by_two_contexts() {
    for left in ["a", "b"] {
        for right in ["c", "d"] {
            for context in ["f", "g"] {
                let mut eg = EGraph::<String>::new();
                let l0 = eg.add(ENode::leaf(left.to_string()));
                let l1 = eg.add(ENode::leaf(format!("{left}'")));
                let r0 = eg.add(ENode::leaf(right.to_string()));
                let r1 = eg.add(ENode::leaf(format!("{right}'")));
                let c00 = eg.add(ENode::new(context.to_string(), vec![l0, r0]));
                let c11 = eg.add(ENode::new(context.to_string(), vec![l1, r1]));

                eg.merge(l0, l1);
                eg.merge(r0, r1);
                eg.rebuild();

                assert!(
                    eg.equiv(c00, c11),
                    "congruence did not propagate through {context}({left},{right})"
                );
                assert_eq!(
                    eg.nodes(eg.find(c00)).len(),
                    1,
                    "exact rebuild should deduplicate the now-congruent parent node"
                );
            }
        }
    }
}
