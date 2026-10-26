//! Finite one-to-one assignment over collection occurrences.
//!
//! Used when a rewrite LHS has `#zip(first, second).#map(|a, b| body)` over a collection:
//! for each element of `first`, we find elements in a context that match `body` (with `a` bound).
//! When multiple context elements match the same `first` element, the rule should fire once per
//! valid assignment (one context element per first element, no reuse). This module enumerates
//! all such assignments.
//!
//! Input: `candidates[group]` = list of `(context_index, payload)` for the group (one group per
//! element of `first`). Output: each matching is `(payloads_in_order, set_of_used_indices)`.
//!
//! Generated first-order term matching has a different, existential contract:
//! it needs one perfect assignment or proof that none exists, not an eagerly
//! materialized list of every substitution. [`first_perfect_matching`] uses
//! iterative augmenting paths for that contract. The all-witness enumerator
//! remains the finite oracle for its tests and the API for rewrite semantics.

use std::collections::HashSet;

/// Return one perfect assignment of pattern occurrences to ground occurrences.
/// The result is indexed by pattern occurrence and contains its matched ground
/// occurrence. Equal-valued bag elements retain distinct occurrence indices.
///
/// `compatible(ground, pattern)` is a pure compatibility test. The explicit
/// BFS queue, owner arrays, and predecessor vectors use O(n) auxiliary space;
/// there is no quadratic edge cache or hidden cardinality cutoff. The outer
/// loop has n roots, each BFS visits at most n patterns and scans at most n
/// grounds per pattern, giving at most n³ compatibility evaluations. Nested
/// calls made *inside* the predicate have their own stack-safety contract.
///
/// This is an existential term matcher, not an ambiguity-pruning parser step:
/// the first-order caller exposes one `MatchBindings` witness, whereas
/// PraTTaIL's parse forest and weighted transducers are separate APIs.
/// Repeated free-variable occurrences in Rholang `matches` formulas are
/// independent Wildcards; this function does not impose rewrite-style
/// nonlinear substitution equality across different pair edges.
/// Existence is invariant under permutation of either occurrence enumeration.
/// A selected witness is deterministic for the supplied index order, but an
/// unordered container may enumerate occurrences in a different order. The
/// Rholang formula caller observes only existence; a future consumer of the
/// binding values must canonicalize the occurrence order or enumerate all
/// witnesses before using them in consensus-visible output.
pub fn first_perfect_matching(
    ground_count: usize,
    pattern_count: usize,
    mut compatible: impl FnMut(usize, usize) -> bool,
) -> Option<Vec<usize>> {
    if ground_count != pattern_count {
        return None;
    }
    let count = pattern_count;
    let mut ground_for_pattern: Vec<Option<usize>> = vec![None; count];
    let mut pattern_for_ground: Vec<Option<usize>> = vec![None; count];

    for root in 0..count {
        let mut queue = std::collections::VecDeque::new();
        let mut seen_pattern = vec![false; count];
        let mut seen_ground = vec![false; count];
        let mut predecessor: Vec<Option<usize>> = vec![None; count];
        seen_pattern[root] = true;
        queue.push_back(root);
        let mut free_ground = None;

        while let Some(pattern) = queue.pop_front() {
            for ground in 0..count {
                if seen_ground[ground] {
                    continue;
                }
                if !compatible(ground, pattern) {
                    continue;
                }
                seen_ground[ground] = true;
                predecessor[ground] = Some(pattern);
                match pattern_for_ground[ground] {
                    None => {
                        free_ground = Some(ground);
                        break;
                    },
                    Some(owner) if !seen_pattern[owner] => {
                        seen_pattern[owner] = true;
                        queue.push_back(owner);
                    },
                    Some(_) => {},
                }
            }
            if free_ground.is_some() {
                break;
            }
        }

        // With no alternating path from an unmatched pattern, the current
        // matching cannot grow; the exhausted frontier gives the Hall-deficit
        // certificate modeled in UnorderedPatternAssignment.v. Edge closure
        // follows from scanning every not-yet-seen ground for every queued
        // pattern. Debug checks verify the ownership/count invariants without
        // calling the compatibility predicate a second time.
        let Some(mut ground) = free_ground else {
            debug_assert!(ground_for_pattern[root].is_none());
            debug_assert_eq!(
                seen_pattern.iter().filter(|&&seen| seen).count(),
                seen_ground.iter().filter(|&&seen| seen).count() + 1,
            );
            debug_assert!((0..count)
                .filter(|&g| seen_ground[g])
                .all(|g| { pattern_for_ground[g].is_some_and(|p| seen_pattern[p]) }));
            return None;
        };
        loop {
            let pattern = predecessor[ground]?;
            let displaced = ground_for_pattern[pattern].replace(ground);
            pattern_for_ground[ground] = Some(pattern);
            match displaced {
                Some(previous_ground) => ground = previous_ground,
                None => break,
            }
        }
    }

    debug_assert!(ground_for_pattern
        .iter()
        .enumerate()
        .all(|(pattern, ground)| {
            ground.is_some_and(|ground| pattern_for_ground[ground] == Some(pattern))
        }));
    ground_for_pattern.into_iter().collect()
}

/// Enumerate all ways to pick one candidate per group with distinct context indices.
/// `candidates[group_idx]` = list of `(context_index, payload)` for that group.
/// Returns `(payloads_in_group_order, used_indices)` for each valid matching.
pub fn enumerate_matchings<T: Clone>(
    candidates: &[Vec<(usize, T)>],
) -> Vec<(Vec<T>, HashSet<usize>)> {
    let mut out = Vec::new();
    let n = candidates.len();
    if n == 0 {
        out.push((Vec::new(), HashSet::new()));
        return out;
    }

    // `next_candidate[group]` is the explicit return address of the recursive
    // depth-first search. Borrow payloads while exploring; clone them only for
    // completed results rather than once per speculative edge and again per result.
    let mut next_candidate = vec![0; n];
    let mut chosen: Vec<(usize, &T)> = Vec::with_capacity(n);
    let mut used = HashSet::new();
    let mut group = 0;

    loop {
        let mut selection = None;
        while next_candidate[group] < candidates[group].len() {
            let candidate = next_candidate[group];
            next_candidate[group] += 1;
            let (index, payload) = &candidates[group][candidate];
            if !used.contains(index) {
                selection = Some((*index, payload));
                break;
            }
        }

        if let Some((index, payload)) = selection {
            used.insert(index);
            chosen.push((index, payload));
            if group + 1 == n {
                out.push((
                    chosen
                        .iter()
                        .map(|(_, payload)| (*payload).clone())
                        .collect(),
                    chosen.iter().map(|(index, _)| *index).collect(),
                ));
                let (index, _) = chosen.pop().expect("matching PDA: missing leaf selection");
                used.remove(&index);
            } else {
                group += 1;
                next_candidate[group] = 0;
            }
            continue;
        }

        next_candidate[group] = 0;
        if group == 0 {
            break;
        }
        group -= 1;
        let (index, _) = chosen
            .pop()
            .expect("matching PDA: missing parent selection");
        used.remove(&index);
    }

    out
}

#[cfg(test)]
mod tests {
    use super::{enumerate_matchings, first_perfect_matching};
    use proptest::prelude::*;
    use std::collections::HashSet;

    #[test]
    fn alternating_path_repairs_a_greedy_false_rejection() {
        // Pattern 0 accepts either occurrence; pattern 1 requires ground 0.
        // Claiming ground 0 for pattern 0 would strand pattern 1.
        let assignment =
            first_perfect_matching(2, 2, |ground, pattern| pattern == 0 || ground == 0);
        assert_eq!(assignment, Some(vec![1, 0]));
    }

    #[test]
    fn multi_step_augmentation_reassigns_every_displaced_owner() {
        // The last root requires ground 0. Its path displaces pattern 0 from
        // ground 0 to ground 1, then pattern 1 from ground 1 to ground 2.
        let assignment = first_perfect_matching(3, 3, |ground, pattern| {
            matches!((pattern, ground), (0, 0 | 1) | (1, 1 | 2) | (2, 0))
        });
        assert_eq!(assignment, Some(vec![1, 2, 0]));
    }

    #[test]
    fn occurrence_multiplicity_and_cardinality_are_exact() {
        assert_eq!(first_perfect_matching(2, 2, |_, _| true), Some(vec![0, 1]));
        assert_eq!(first_perfect_matching(1, 2, |_, _| true), None);
        assert_eq!(first_perfect_matching(2, 1, |_, _| true), None);
        assert_eq!(first_perfect_matching(0, 0, |_, _| false), Some(vec![]));
    }

    #[test]
    fn assignment_search_uses_an_explicit_worklist_at_large_cardinality() {
        let count = 1024;
        let mut evaluations = 0usize;
        let assignment = first_perfect_matching(count, count, |ground, pattern| {
            evaluations += 1;
            ground == pattern
        });
        assert_eq!(assignment, Some((0..count).collect()));
        assert_eq!(evaluations, count * (count + 1) / 2);
    }

    proptest! {
        #[test]
        fn existential_search_matches_the_existing_all_witness_pda(
            size in 0usize..=6,
            edge_bits in any::<u64>(),
        ) {
            let edge = |ground: usize, pattern: usize| {
                edge_bits & (1u64 << (pattern * size + ground)) != 0
            };
            let candidates: Vec<Vec<(usize, usize)>> = (0..size)
                .map(|pattern| {
                    (0..size)
                        .filter(|&ground| edge(ground, pattern))
                        .map(|ground| (ground, ground))
                        .collect()
                })
                .collect();
            let all = enumerate_matchings(&candidates);
            let mut evaluations = 0usize;
            let found = first_perfect_matching(size, size, |ground, pattern| {
                evaluations += 1;
                edge(ground, pattern)
            });
            prop_assert!(evaluations <= size * size * size);
            prop_assert_eq!(found.is_some(), !all.is_empty());
            if let Some(assignment) = found {
                let distinct: HashSet<_> = assignment.iter().copied().collect();
                prop_assert_eq!(assignment.len(), size);
                prop_assert_eq!(distinct.len(), size);
                prop_assert!(all.iter().any(|(witness, _)| witness == &assignment));
            }
        }

        #[test]
        fn existence_is_invariant_under_independent_occurrence_permutations(
            size in 0usize..=6,
            edge_bits in any::<u64>(),
            ground_shift in any::<usize>(),
            pattern_shift in any::<usize>(),
        ) {
            let edge = |ground: usize, pattern: usize| {
                edge_bits & (1u64 << (pattern * size + ground)) != 0
            };
            let original = first_perfect_matching(size, size, edge).is_some();
            let permuted = first_perfect_matching(size, size, |ground, pattern| {
                if size == 0 {
                    false
                } else {
                    let ground_index = (size - 1 - ground + ground_shift % size) % size;
                    let pattern_index = (size - 1 - pattern + pattern_shift % size) % size;
                    edge(ground_index, pattern_index)
                }
            }).is_some();
            prop_assert_eq!(original, permuted);
        }
    }
}
