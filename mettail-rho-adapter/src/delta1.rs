//! Delta-one join selection for MeTTaIL's Rho backend.
//!
//! The contract has two separate axes:
//!
//! - refutation decides whether a candidate is enabled at all;
//! - ordering cost ranks enabled candidates without deleting equal-cost
//!   alternatives.
//!
//! `select_delta1_minima` therefore filters refuted candidates first and then
//! returns every enabled candidate whose ordering cost is minimal. Returning all
//! ties is intentional: it preserves semantic ambiguity instead of letting host
//! scheduler or iteration order choose one representative.

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
}
