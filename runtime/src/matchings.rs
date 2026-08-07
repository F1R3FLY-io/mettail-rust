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
