//! Delta-one join selection for MeTTaIL's Rho backend.
//!
//! The contract has two separate axes:
//!
//! - refutation decides whether a candidate is enabled at all;
//! - ordering cost ranks enabled candidates without deleting equal-cost
//!   alternatives.
//!
//! `select_delta1_minima` therefore filters refuted candidates first and then
//! returns every enabled candidate whose ordering cost is minimal. For join
//! frontiers that still need an assignment step,
//! `select_delta1_min_cost_left_perfect_matchings` performs the corresponding
//! exact bipartite selection: each left obligation is covered once, each right
//! message or witness is used at most once, refuted edges are removed before
//! ranking, and every minimum-cost left-perfect matching is returned.
//!
//! Returning all ties is intentional in both APIs: it preserves semantic
//! ambiguity instead of letting host scheduler or iteration order choose one
//! representative.

/// A candidate n-ary join match with separated refutation and ordering axes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeltaOneCandidate<T> {
    /// Caller-owned candidate payload. This can be a join identifier, lowered
    /// continuation handle, or test witness.
    pub value: T,
    /// Rank-only cost among enabled candidates. Lower is better.
    pub ordering_cost: u64,
    /// Refuted candidates are absent from Delta-one selection regardless of
    /// their ordering cost.
    pub refuted: bool,
}

impl<T> DeltaOneCandidate<T> {
    /// Construct an enabled candidate.
    pub fn enabled(value: T, ordering_cost: u64) -> Self {
        Self { value, ordering_cost, refuted: false }
    }

    /// Construct a refuted candidate.
    pub fn refuted(value: T, ordering_cost: u64) -> Self {
        Self { value, ordering_cost, refuted: true }
    }

    /// Whether this candidate can participate in Delta-one selection.
    pub fn is_enabled(&self) -> bool {
        !self.refuted
    }
}

/// Return every enabled candidate with minimal ordering cost.
pub fn select_delta1_minima<T>(candidates: &[DeltaOneCandidate<T>]) -> Vec<&DeltaOneCandidate<T>> {
    let Some(min_cost) = candidates
        .iter()
        .filter(|candidate| candidate.is_enabled())
        .map(|candidate| candidate.ordering_cost)
        .min()
    else {
        return Vec::new();
    };

    candidates
        .iter()
        .filter(|candidate| candidate.is_enabled() && candidate.ordering_cost == min_cost)
        .collect()
}

/// Relational predicate for whether `index` is selected by Delta-one.
pub fn delta1_selects_index<T>(candidates: &[DeltaOneCandidate<T>], index: usize) -> bool {
    let Some(candidate) = candidates.get(index) else {
        return false;
    };
    candidate.is_enabled()
        && candidates
            .iter()
            .filter(|other| other.is_enabled())
            .all(|other| candidate.ordering_cost <= other.ordering_cost)
}

/// One possible assignment edge in a Delta-one bipartite join frontier.
///
/// `left` identifies the join obligation, `right` identifies the candidate
/// message or binding witness, and `value` is caller-owned metadata for the
/// edge. The selector treats duplicate `(left, right)` edges as distinct
/// semantic alternatives because their payloads may lower to different guarded
/// continuations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeltaOneMatchEdge<T> {
    /// Left-side join obligation index.
    pub left: usize,
    /// Right-side message or witness index.
    pub right: usize,
    /// Caller-owned edge payload.
    pub value: T,
    /// Rank-only edge cost among enabled left-perfect matchings. Lower is better.
    pub ordering_cost: u64,
    /// Refuted edges cannot participate in a selected matching.
    pub refuted: bool,
}

impl<T> DeltaOneMatchEdge<T> {
    /// Construct an enabled match edge.
    pub fn enabled(left: usize, right: usize, value: T, ordering_cost: u64) -> Self {
        Self {
            left,
            right,
            value,
            ordering_cost,
            refuted: false,
        }
    }

    /// Construct a refuted match edge.
    pub fn refuted(left: usize, right: usize, value: T, ordering_cost: u64) -> Self {
        Self {
            left,
            right,
            value,
            ordering_cost,
            refuted: true,
        }
    }

    /// Whether this edge can participate in Delta-one matching.
    pub fn is_enabled(&self) -> bool {
        !self.refuted
    }
}

/// A selected minimum-cost left-perfect matching.
///
/// `edge_indices` are indexes into the caller's edge slice in left-obligation
/// order. `total_cost` uses `u128`, so summing any feasible `usize`-bounded
/// number of `u64` edge costs cannot overflow the represented total.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeltaOneMatching {
    /// Edge indexes into the edge slice passed to
    /// [`select_delta1_min_cost_left_perfect_matchings`].
    pub edge_indices: Vec<usize>,
    /// Exact sum of the selected edges' ordering costs.
    pub total_cost: u128,
}

impl DeltaOneMatching {
    /// Resolve the selected edge indexes back to edge references.
    pub fn edges<'a, T>(
        &self,
        edges: &'a [DeltaOneMatchEdge<T>],
    ) -> Option<Vec<&'a DeltaOneMatchEdge<T>>> {
        self.edge_indices
            .iter()
            .map(|&index| edges.get(index))
            .collect()
    }
}

struct DeltaOneMatchingSearch<'a, T> {
    edges: &'a [DeltaOneMatchEdge<T>],
    edge_indices_by_left: Vec<Vec<usize>>,
    left_count: usize,
    used_rights: Vec<usize>,
    current_indices: Vec<usize>,
    best_cost: Option<u128>,
    best_matchings: Vec<DeltaOneMatching>,
}

impl<T> DeltaOneMatchingSearch<'_, T> {
    fn visit_left(&mut self, left: usize, current_cost: u128) {
        if self
            .best_cost
            .is_some_and(|best_cost| current_cost > best_cost)
        {
            return;
        }

        if left == self.left_count {
            self.record_matching(current_cost);
            return;
        }

        for position in 0..self.edge_indices_by_left[left].len() {
            let index = self.edge_indices_by_left[left][position];
            let edge = &self.edges[index];
            let right = edge.right;
            let ordering_cost = edge.ordering_cost;

            if self.used_rights.contains(&right) {
                continue;
            }

            let next_cost = current_cost + u128::from(ordering_cost);
            if self
                .best_cost
                .is_some_and(|best_cost| next_cost > best_cost)
            {
                continue;
            }

            self.used_rights.push(right);
            self.current_indices.push(index);
            self.visit_left(left + 1, next_cost);
            self.current_indices.pop();
            self.used_rights.pop();
        }
    }

    fn record_matching(&mut self, total_cost: u128) {
        match self.best_cost {
            Some(best_cost) if total_cost > best_cost => {},
            Some(best_cost) if total_cost == best_cost => {
                self.best_matchings.push(DeltaOneMatching {
                    edge_indices: self.current_indices.clone(),
                    total_cost,
                });
            },
            _ => {
                self.best_cost = Some(total_cost);
                self.best_matchings.clear();
                self.best_matchings.push(DeltaOneMatching {
                    edge_indices: self.current_indices.clone(),
                    total_cost,
                });
            },
        }
    }
}

/// Return every enabled left-perfect matching with minimal total ordering cost.
///
/// A left-perfect matching covers every required left obligation exactly once
/// while using each right witness at most once. Extra right witnesses may remain
/// unused; they correspond to resting/admitted messages outside the chosen join.
/// Edges outside the declared frontier bounds are ignored. The implementation
/// is an exact exhaustive search over the currently bounded adapter frontier; a
/// future Hungarian or min-cost-flow implementation can replace it if it returns
/// precisely the same set of minimum-cost matchings.
pub fn select_delta1_min_cost_left_perfect_matchings<T>(
    edges: &[DeltaOneMatchEdge<T>],
    left_count: usize,
    right_count: usize,
) -> Vec<DeltaOneMatching> {
    if left_count > right_count {
        return Vec::new();
    }

    if left_count == 0 {
        return vec![DeltaOneMatching { edge_indices: Vec::new(), total_cost: 0 }];
    }

    if edges.len() < left_count {
        return Vec::new();
    }

    let mut edge_indices_by_left = vec![Vec::new(); left_count];
    for (index, edge) in edges.iter().enumerate() {
        if edge.is_enabled() && edge.left < left_count && edge.right < right_count {
            edge_indices_by_left[edge.left].push(index);
        }
    }

    if edge_indices_by_left.iter().any(Vec::is_empty) {
        return Vec::new();
    }

    let mut search = DeltaOneMatchingSearch {
        edges,
        edge_indices_by_left,
        left_count,
        used_rights: Vec::with_capacity(left_count),
        current_indices: Vec::with_capacity(left_count),
        best_cost: None,
        best_matchings: Vec::new(),
    };
    search.visit_left(0, 0);
    search.best_matchings
}

/// Relational predicate for whether `edge_indices` name a selected matching.
pub fn delta1_selects_left_perfect_matching_indices<T>(
    edges: &[DeltaOneMatchEdge<T>],
    left_count: usize,
    right_count: usize,
    edge_indices: &[usize],
) -> bool {
    select_delta1_min_cost_left_perfect_matchings(edges, left_count, right_count)
        .iter()
        .any(|matching| matching.edge_indices == edge_indices)
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn delta1_refutation_precedes_ordering() {
        let candidates = vec![
            DeltaOneCandidate::refuted("cheap-but-refuted", 0),
            DeltaOneCandidate::enabled("enabled", 5),
            DeltaOneCandidate::enabled("expensive", 8),
        ];

        assert_eq!(selected_values(&candidates), vec!["enabled"]);
        assert!(!delta1_selects_index(&candidates, 0));
        assert!(delta1_selects_index(&candidates, 1));
        assert!(!delta1_selects_index(&candidates, 2));
    }

    #[test]
    fn delta1_returns_empty_when_no_candidate_is_enabled() {
        let candidates =
            vec![DeltaOneCandidate::refuted("a", 0), DeltaOneCandidate::refuted("b", 1)];

        assert!(select_delta1_minima(&candidates).is_empty());
        assert!(!delta1_selects_index(&candidates, 0));
        assert!(!delta1_selects_index(&candidates, 1));
    }

    #[test]
    fn delta1_out_of_range_index_is_not_selected() {
        let candidates = vec![DeltaOneCandidate::enabled("only", 0)];
        assert!(!delta1_selects_index(&candidates, 1));
    }

    fn matching_values<'a>(
        edges: &'a [DeltaOneMatchEdge<&'a str>],
        matching: &DeltaOneMatching,
    ) -> Vec<&'a str> {
        matching
            .edges(edges)
            .expect("test matchings should resolve")
            .into_iter()
            .map(|edge| edge.value)
            .collect()
    }

    #[test]
    fn delta1_matching_selects_cheapest_left_perfect_assignment() {
        let edges = vec![
            DeltaOneMatchEdge::enabled(0, 0, "l0-r0", 5),
            DeltaOneMatchEdge::enabled(0, 1, "l0-r1", 1),
            DeltaOneMatchEdge::enabled(1, 0, "l1-r0", 1),
            DeltaOneMatchEdge::enabled(1, 1, "l1-r1", 5),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 2, 2);

        assert_eq!(selected, vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 2 }]);
        assert!(delta1_selects_left_perfect_matching_indices(&edges, 2, 2, &[1, 2]));
        assert!(!delta1_selects_left_perfect_matching_indices(&edges, 2, 2, &[0, 3]));
    }

    #[test]
    fn delta1_matching_preserves_equal_cost_ambiguity() {
        let edges = vec![
            DeltaOneMatchEdge::enabled(0, 0, "a", 1),
            DeltaOneMatchEdge::enabled(0, 1, "b", 1),
            DeltaOneMatchEdge::enabled(1, 0, "c", 1),
            DeltaOneMatchEdge::enabled(1, 1, "d", 1),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 2, 2);
        let selected_values: Vec<Vec<&str>> = selected
            .iter()
            .map(|matching| matching_values(&edges, matching))
            .collect();

        assert_eq!(
            selected,
            vec![
                DeltaOneMatching { edge_indices: vec![0, 3], total_cost: 2 },
                DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 2 },
            ]
        );
        assert_eq!(selected_values, vec![vec!["a", "d"], vec!["b", "c"]]);
    }

    #[test]
    fn delta1_matching_is_globally_optimal_not_greedy() {
        let edges = vec![
            DeltaOneMatchEdge::enabled(0, 0, "locally-cheap", 1),
            DeltaOneMatchEdge::enabled(0, 1, "globally-good-left", 2),
            DeltaOneMatchEdge::enabled(1, 0, "globally-good-right", 1),
            DeltaOneMatchEdge::enabled(1, 1, "forced-expensive", 100),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 2, 2);

        assert_eq!(selected, vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 3 }]);
    }

    #[test]
    fn delta1_matching_refutation_precedes_ordering() {
        let edges = vec![
            DeltaOneMatchEdge::refuted(0, 0, "cheap-refuted", 0),
            DeltaOneMatchEdge::enabled(0, 1, "enabled-left", 4),
            DeltaOneMatchEdge::enabled(1, 0, "enabled-right", 4),
            DeltaOneMatchEdge::enabled(1, 1, "duplicate-right", 0),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 2, 2);

        assert_eq!(selected, vec![DeltaOneMatching { edge_indices: vec![1, 2], total_cost: 8 }]);
        assert!(!delta1_selects_left_perfect_matching_indices(&edges, 2, 2, &[0, 3]));
    }

    #[test]
    fn delta1_matching_returns_empty_without_left_perfect_assignment() {
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
    fn delta1_matching_allows_unused_right_witnesses() {
        let edges = vec![
            DeltaOneMatchEdge::enabled(0, 0, "usable-but-expensive", 5),
            DeltaOneMatchEdge::enabled(0, 1, "chosen", 2),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 1, 2);

        assert_eq!(selected, vec![DeltaOneMatching { edge_indices: vec![1], total_cost: 2 }]);
    }

    #[test]
    fn delta1_matching_ignores_edges_outside_declared_frontier() {
        let edges = vec![
            DeltaOneMatchEdge::enabled(0, 0, "in-left", 3),
            DeltaOneMatchEdge::enabled(0, 2, "right-out-of-range", 0),
            DeltaOneMatchEdge::enabled(2, 0, "left-out-of-range", 0),
        ];

        let selected = select_delta1_min_cost_left_perfect_matchings(&edges, 1, 1);

        assert_eq!(selected, vec![DeltaOneMatching { edge_indices: vec![0], total_cost: 3 }]);
    }

    #[test]
    fn delta1_matching_empty_frontier_has_empty_left_perfect_matching() {
        let edges: Vec<DeltaOneMatchEdge<&str>> = Vec::new();

        assert_eq!(
            select_delta1_min_cost_left_perfect_matchings(&edges, 0, 2),
            vec![DeltaOneMatching { edge_indices: Vec::new(), total_cost: 0 }]
        );
    }
}
