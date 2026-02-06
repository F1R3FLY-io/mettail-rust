//! Enumerate all valid matchings for correlated zip+map LHS patterns.
//!
//! Used when a rewrite LHS has `#zip(first, second).#map(|a, b| body)` over a collection:
//! for each element of `first`, we find elements in a context that match `body` (with `a` bound).
//! When multiple context elements match the same `first` element, the rule should fire once per
//! valid assignment (one context element per first element, no reuse). This module enumerates
//! all such assignments.
//!
//! Input: `candidates[group]` = list of `(context_index, payload)` for the group (one group per
//! element of `first`). Output: each matching is `(payloads_in_order, set_of_used_indices)`.

use std::collections::HashSet;

/// Enumerate all ways to pick one candidate per group with distinct context indices.
/// `candidates[group_idx]` = list of `(context_index, payload)` for that group.
/// Returns `(payloads_in_group_order, used_indices)` for each valid matching.
pub fn enumerate_matchings<T: Clone>(
    candidates: &[Vec<(usize, T)>],
) -> Vec<(Vec<T>, HashSet<usize>)> {
    let mut out = Vec::new();
    let n = candidates.len();
    let mut chosen: Vec<(usize, T)> = Vec::new();
    let mut used = HashSet::new();
    enumerate_rec(candidates, n, 0, &mut chosen, &mut used, &mut out);
    out
}

fn enumerate_rec<T: Clone>(
    candidates: &[Vec<(usize, T)>],
    n: usize,
    group: usize,
    chosen: &mut Vec<(usize, T)>,
    used: &mut HashSet<usize>,
    out: &mut Vec<(Vec<T>, HashSet<usize>)>,
) {
    if group == n {
        out.push((
            chosen.iter().map(|(_, p)| p.clone()).collect(),
            chosen.iter().map(|(i, _)| *i).collect(),
        ));
        return;
    }
    for (idx, payload) in &candidates[group] {
        if used.contains(idx) {
            continue;
        }
        used.insert(*idx);
        chosen.push((*idx, payload.clone()));
        enumerate_rec(candidates, n, group + 1, chosen, used, out);
        chosen.pop();
        used.remove(idx);
    }
}
