#[path = "support/delta1_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_rholang_adapter::{
    delta1_selects_index, delta1_selects_left_perfect_matching_indices,
    select_delta1_min_cost_left_perfect_matchings, select_delta1_minima, DeltaOneCandidate,
    DeltaOneMatchEdge, DeltaOneMatching,
};

fn selected_values<'a>(candidates: &'a [DeltaOneCandidate<&'a str>]) -> Vec<&'a str> {
    select_delta1_minima(candidates)
        .into_iter()
        .map(|candidate| candidate.value)
        .collect()
}

#[test]
fn delta1_selects_all_enabled_minimal_ties() {
    let candidates = vec![
        DeltaOneCandidate::enabled("slow", 7),
        DeltaOneCandidate::enabled("fast-a", 2),
        DeltaOneCandidate::enabled("fast-b", 2),
    ];
    assert_eq!(selected_values(&candidates), vec!["fast-a", "fast-b"]);
    assert!(!delta1_selects_index(&candidates, 0));
    assert!(delta1_selects_index(&candidates, 1));
    assert!(delta1_selects_index(&candidates, 2));
}

#[test]
fn delta1_refutation_and_bounds_precede_ordering() {
    let candidates = vec![
        DeltaOneCandidate::refuted("cheap-but-refuted", 0),
        DeltaOneCandidate::enabled("enabled", 5),
        DeltaOneCandidate::enabled("expensive", 8),
    ];
    assert_eq!(selected_values(&candidates), vec!["enabled"]);
    assert!(!delta1_selects_index(&candidates, 0));
    assert!(delta1_selects_index(&candidates, 1));
    assert!(!delta1_selects_index(&candidates, 2));
    assert!(!delta1_selects_index(&candidates, 3));
    assert!(select_delta1_minima(&[
        DeltaOneCandidate::refuted("a", 0),
        DeltaOneCandidate::refuted("b", 1),
    ])
    .is_empty());
}

#[test]
fn matching_selects_global_minimum_and_preserves_ties() {
    let cheapest = vec![
        DeltaOneMatchEdge::enabled(0, 0, "l0-r0", 5),
        DeltaOneMatchEdge::enabled(0, 1, "l0-r1", 1),
        DeltaOneMatchEdge::enabled(1, 0, "l1-r0", 1),
        DeltaOneMatchEdge::enabled(1, 1, "l1-r1", 5),
    ];
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&cheapest, 2, 2),
        vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 2 }]
    );
    assert!(delta1_selects_left_perfect_matching_indices(&cheapest, 2, 2, &[1, 2]));
    assert!(!delta1_selects_left_perfect_matching_indices(&cheapest, 2, 2, &[0, 3]));

    let ties = vec![
        DeltaOneMatchEdge::enabled(0, 0, "a", 1),
        DeltaOneMatchEdge::enabled(0, 1, "b", 1),
        DeltaOneMatchEdge::enabled(1, 0, "c", 1),
        DeltaOneMatchEdge::enabled(1, 1, "d", 1),
    ];
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&ties, 2, 2),
        vec![
            DeltaOneMatching { edge_indices: vec![0, 3], total_cost: 2 },
            DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 2 },
        ]
    );

    let nongreedy = vec![
        DeltaOneMatchEdge::enabled(0, 0, "locally-cheap", 1),
        DeltaOneMatchEdge::enabled(0, 1, "globally-good-left", 2),
        DeltaOneMatchEdge::enabled(1, 0, "globally-good-right", 1),
        DeltaOneMatchEdge::enabled(1, 1, "forced-expensive", 100),
    ];
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&nongreedy, 2, 2),
        vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 3 }]
    );
}

#[test]
fn matching_filters_refuted_out_of_range_and_infeasible_edges() {
    let edges = vec![
        DeltaOneMatchEdge::refuted(0, 0, "cheap-refuted", 0),
        DeltaOneMatchEdge::enabled(0, 1, "enabled-left", 4),
        DeltaOneMatchEdge::enabled(1, 0, "enabled-right", 4),
        DeltaOneMatchEdge::enabled(1, 1, "duplicate-right", 0),
        DeltaOneMatchEdge::enabled(0, 2, "right-out-of-range", 0),
        DeltaOneMatchEdge::enabled(2, 0, "left-out-of-range", 0),
    ];
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&edges, 2, 2),
        vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 8 }]
    );

    let missing_left = vec![
        DeltaOneMatchEdge::enabled(0, 0, "a", 1),
        DeltaOneMatchEdge::enabled(0, 1, "b", 1),
    ];
    let duplicate_right = vec![
        DeltaOneMatchEdge::enabled(0, 0, "a", 1),
        DeltaOneMatchEdge::enabled(1, 0, "b", 1),
    ];
    assert!(select_delta1_min_cost_left_perfect_matchings(&missing_left, 2, 2).is_empty());
    assert!(select_delta1_min_cost_left_perfect_matchings(&duplicate_right, 2, 2).is_empty());
    assert!(select_delta1_min_cost_left_perfect_matchings(&missing_left, 2, 1).is_empty());
}

#[test]
fn matching_handles_empty_left_and_unused_right_frontiers() {
    let edges = vec![
        DeltaOneMatchEdge::enabled(0, 0, "usable-but-expensive", 5),
        DeltaOneMatchEdge::enabled(0, 1, "chosen", 2),
    ];
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&edges, 1, 2),
        vec![DeltaOneMatching { edge_indices: vec![1], total_cost: 2 }]
    );
    assert_eq!(
        select_delta1_min_cost_left_perfect_matchings(&edges, 0, 2),
        vec![DeltaOneMatching { edge_indices: Vec::new(), total_cost: 0 }]
    );
}

#[test]
fn iterative_search_matches_recursive_oracle() {
    let corpora = [
        vec![
            DeltaOneMatchEdge::enabled(0, 0, 'a', 4),
            DeltaOneMatchEdge::enabled(0, 1, 'b', 1),
            DeltaOneMatchEdge::enabled(1, 0, 'c', 2),
            DeltaOneMatchEdge::enabled(1, 1, 'd', 8),
        ],
        vec![
            DeltaOneMatchEdge::enabled(0, 0, 'a', 1),
            DeltaOneMatchEdge::enabled(0, 1, 'b', 1),
            DeltaOneMatchEdge::enabled(1, 0, 'c', 1),
            DeltaOneMatchEdge::enabled(1, 1, 'd', 1),
        ],
        vec![
            DeltaOneMatchEdge::refuted(0, 0, 'a', 0),
            DeltaOneMatchEdge::enabled(0, 2, 'b', 2),
            DeltaOneMatchEdge::enabled(1, 1, 'c', 3),
            DeltaOneMatchEdge::enabled(2, 0, 'd', u64::MAX),
        ],
    ];
    for edges in corpora {
        for (left_count, right_count) in [(0, 3), (1, 3), (2, 3), (3, 3), (3, 2)] {
            assert_eq!(
                select_delta1_min_cost_left_perfect_matchings(&edges, left_count, right_count),
                recursive_oracle::select(&edges, left_count, right_count),
                "Delta-one search diverged for {left_count}x{right_count}: {edges:?}"
            );
        }
    }
}

#[test]
fn iterative_search_is_stack_safe_at_twenty_thousand_obligations() {
    std::thread::Builder::new()
        .name("delta-one-matching-pda-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let edges: Vec<_> = (0..20_000)
                .map(|index| DeltaOneMatchEdge::enabled(index, index, (), 1))
                .collect();
            assert_eq!(
                select_delta1_min_cost_left_perfect_matchings(&edges, edges.len(), edges.len()),
                vec![DeltaOneMatching {
                    edge_indices: (0..edges.len()).collect(),
                    total_cost: edges.len() as u128,
                }]
            );
        })
        .expect("spawn Delta-one stack-gate thread")
        .join()
        .expect("Delta-one matching PDA overflowed or panicked");
}
