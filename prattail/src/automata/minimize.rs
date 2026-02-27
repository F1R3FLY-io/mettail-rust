//! Hopcroft's DFA minimization.
//!
//! Merges equivalent DFA states — states that have the same accept status
//! and transition identically on all equivalence classes. This is important
//! for grammars with many operators sharing common prefixes (e.g., `$proc`,
//! `$name`, `$int` and `$$proc(`, `$$name(`, `$$int(`), where minimization
//! merges the shared `$` prefix into a single state.
//!
//! **Algorithm:** True Hopcroft's minimization using an inverse transition map.
//! For each splitter (partition class + equivalence class), only the predecessors
//! of splitter states are examined, yielding O(|transitions| × log p) complexity
//! where p is the number of partitions, instead of the naive O(n² × k) approach.
//!
//! **Complexity:** O(n × k × log n) on the number of DFA states and classes.
//!
//! ## Optimizations
//!
//! - **Inverse map pre-allocation:** A counting pass computes exact predecessor
//!   counts per (target, class) pair, then inner Vecs are allocated with exact
//!   capacity — eliminating ~n×k micro-reallocations.
//! - **Thread-local buffer pooling:** `affected_partitions`, `goes_to_splitter`,
//!   and `partition_seen` retain capacity across calls via `Cell<Vec<T>>`
//!   take/set pattern, eliminating ~100+ `Vec<bool>` allocations per call.

use std::cell::Cell;

use super::{ClassId, Dfa, DfaState, StateId, DEAD_STATE};
use std::collections::BTreeMap;

thread_local! {
    /// Reusable buffer for affected partition indices during worklist refinement.
    static AFFECTED: Cell<Vec<usize>> = const { Cell::new(Vec::new()) };
    /// Reusable buffer for states that transition to the splitter partition.
    static GOES_TO: Cell<Vec<StateId>> = const { Cell::new(Vec::new()) };
    /// Reusable boolean buffer for tracking seen partitions (avoids duplicates).
    static SEEN: Cell<Vec<bool>> = const { Cell::new(Vec::new()) };
}

/// Minimize a DFA using Hopcroft's algorithm with inverse transition map.
///
/// Returns a new DFA with equivalent states merged.
pub fn minimize_dfa(dfa: &Dfa) -> Dfa {
    let n = dfa.states.len();
    if n <= 1 {
        return dfa.clone();
    }

    let num_classes = dfa.num_classes;

    // --- Step 1: Build inverse transition map with pre-counted capacities ---
    // Count predecessors per (target, class) pair for exact inner Vec allocation
    let mut pred_counts = vec![0u32; n * num_classes];
    for state in dfa.states.iter() {
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                pred_counts[target as usize * num_classes + class_id] += 1;
            }
        }
    }
    // inverse[target_state][class_id] = list of predecessor states
    // that transition to target_state on class_id.
    let mut inverse: Vec<Vec<Vec<StateId>>> = (0..n)
        .map(|state| {
            (0..num_classes)
                .map(|class| Vec::with_capacity(pred_counts[state * num_classes + class] as usize))
                .collect()
        })
        .collect();
    for (state_idx, state) in dfa.states.iter().enumerate() {
        let state_id = state_idx as StateId;
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                inverse[target as usize][class_id].push(state_id);
            }
        }
    }

    // --- Step 2: Initial partition — group by (accept token kind, weight) ---
    // States with different accept tokens or different weights cannot be merged.
    // Weight is included in the partition key to preserve WFST weight semantics:
    // two states accepting the same token but with different tropical weights
    // represent different priority levels and must remain distinct.
    //
    // We use BTreeMap with a composite key. For weight, we use the bit
    // representation of f64 for total ordering.
    let mut accept_groups: BTreeMap<(Option<&super::TokenKind>, u64), Vec<StateId>> =
        BTreeMap::new();
    for (i, state) in dfa.states.iter().enumerate() {
        let weight_bits = state.weight.value().to_bits();
        accept_groups
            .entry((state.accept.as_ref(), weight_bits))
            .or_default()
            .push(i as StateId);
    }

    // partition_of[state] = partition index for that state
    let mut partition_of: Vec<usize> = vec![0; n];
    // partitions: each partition is a sorted Vec<StateId>
    let mut partitions: Vec<Vec<StateId>> = Vec::with_capacity(accept_groups.len());

    for (_key, states) in accept_groups {
        let part_idx = partitions.len();
        for &s in &states {
            partition_of[s as usize] = part_idx;
        }
        partitions.push(states);
    }

    // --- Step 3: Worklist initialization ---
    // Hopcroft's "distinguishing set" optimization: add the *smaller* of each
    // pair of {accepting, non-accepting} groups. For multi-group initial partitions,
    // add all groups to the worklist.
    let num_initial = partitions.len();
    // Worklist tracks (partition_index, class_id) pairs
    let mut worklist: Vec<(usize, ClassId)> = Vec::with_capacity(num_initial * num_classes);
    for part_idx in 0..num_initial {
        for class_id in 0..num_classes as ClassId {
            worklist.push((part_idx, class_id));
        }
    }

    // --- Step 4: Iterative refinement with inverse transition map ---
    // Take TLS buffers and ensure first-call pre-allocation
    let mut affected_partitions = AFFECTED.with(|cell| cell.take());
    affected_partitions.clear();
    if affected_partitions.capacity() < n {
        affected_partitions.reserve(n - affected_partitions.capacity());
    }

    let mut goes_to_splitter = GOES_TO.with(|cell| cell.take());
    goes_to_splitter.clear();
    if goes_to_splitter.capacity() < n {
        goes_to_splitter.reserve(n - goes_to_splitter.capacity());
    }

    let mut partition_seen = SEEN.with(|cell| cell.take());

    while let Some((splitter_idx, class_id)) = worklist.pop() {
        // Skip if the partition is empty (may have been emptied by a split)
        if partitions[splitter_idx].is_empty() {
            continue;
        }

        // Collect all predecessor states that transition into the splitter on class_id.
        // These are the only states that *could* cause a partition to split.
        affected_partitions.clear();
        // Track which partitions have predecessors (to avoid duplicates)
        // TLS Vec<bool>: resize to current partition count, reused across iterations
        partition_seen.clear();
        partition_seen.resize(partitions.len(), false);

        for &splitter_state in &partitions[splitter_idx] {
            for &pred in &inverse[splitter_state as usize][class_id as usize] {
                let pred_part = partition_of[pred as usize];
                if !partition_seen[pred_part] {
                    partition_seen[pred_part] = true;
                    affected_partitions.push(pred_part);
                }
            }
        }

        // For each affected partition, check if it needs splitting
        for &part_idx in &affected_partitions {
            if partitions[part_idx].len() <= 1 {
                continue;
            }

            // Determine which states in this partition have a predecessor
            // in the splitter (i.e., they transition to splitter on class_id).
            goes_to_splitter.clear();
            let splitter_part = splitter_idx;

            // A state goes_to_splitter if its transition on class_id
            // lands in the splitter partition
            let mut split_count = 0;
            let mut keep_count = 0;
            for &state in &partitions[part_idx] {
                let target = dfa.transition(state, class_id);
                if target != DEAD_STATE && partition_of[target as usize] == splitter_part {
                    goes_to_splitter.push(state);
                    split_count += 1;
                } else {
                    keep_count += 1;
                }
            }

            // If all states agree, no split needed
            if split_count == 0 || keep_count == 0 {
                continue;
            }

            // Split: keep the larger group in place, create new partition for smaller.
            // This is critical for Hopcroft's O(n log n) complexity.
            let new_part_idx = partitions.len();

            if split_count <= keep_count {
                // goes_to_splitter is the smaller group — becomes the new partition
                let mut new_partition = Vec::with_capacity(split_count);
                let mut kept = Vec::with_capacity(keep_count);
                for &state in &partitions[part_idx] {
                    let target = dfa.transition(state, class_id);
                    if target != DEAD_STATE && partition_of[target as usize] == splitter_part {
                        partition_of[state as usize] = new_part_idx;
                        new_partition.push(state);
                    } else {
                        kept.push(state);
                    }
                }
                partitions[part_idx] = kept;
                partitions.push(new_partition);
            } else {
                // not_goes_to_splitter is the smaller group — becomes the new partition
                let mut new_partition = Vec::with_capacity(keep_count);
                let mut kept = Vec::with_capacity(split_count);
                for &state in &partitions[part_idx] {
                    let target = dfa.transition(state, class_id);
                    if target != DEAD_STATE && partition_of[target as usize] == splitter_part {
                        kept.push(state);
                    } else {
                        partition_of[state as usize] = new_part_idx;
                        new_partition.push(state);
                    }
                }
                partitions[part_idx] = kept;
                partitions.push(new_partition);
            }

            // Add the NEW (smaller) partition to the worklist for all classes.
            // The existing partition is only added if it was already in the worklist.
            // Since we can't cheaply check worklist membership, we add the new
            // partition for all classes (Hopcroft's guarantee: each state moves to
            // a new partition at most O(log n) times).
            for c in 0..num_classes as ClassId {
                worklist.push((new_part_idx, c));
            }
        }
    }

    // Return TLS buffers for reuse
    AFFECTED.with(|cell| cell.set(affected_partitions));
    GOES_TO.with(|cell| cell.set(goes_to_splitter));
    SEEN.with(|cell| cell.set(partition_seen));

    // --- Step 5: Build minimized DFA ---
    let mut new_dfa = Dfa::new(num_classes);

    // Filter out empty partitions and assign new state IDs
    let non_empty: Vec<usize> = (0..partitions.len())
        .filter(|&i| !partitions[i].is_empty())
        .collect();

    let mut partition_to_new_state: Vec<StateId> = vec![DEAD_STATE; partitions.len()];

    // Find which partition contains the original start state
    let start_partition = partition_of[dfa.start as usize];

    // Assign state 0 to the start partition
    partition_to_new_state[start_partition] = 0;
    let representative = partitions[start_partition][0];
    new_dfa.states[0].accept = dfa.states[representative as usize].accept.clone();
    new_dfa.states[0].weight = dfa.states[representative as usize].weight;

    // Assign remaining states
    for &part_idx in &non_empty {
        if partition_to_new_state[part_idx] != DEAD_STATE {
            continue; // already assigned (start partition)
        }
        let rep = partitions[part_idx][0];
        let new_state = new_dfa.add_state(DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: dfa.states[rep as usize].accept.clone(),
            weight: dfa.states[rep as usize].weight,
        });
        partition_to_new_state[part_idx] = new_state;
    }

    // Build transitions for each new state
    for &part_idx in &non_empty {
        let rep = partitions[part_idx][0];
        let new_state_id = partition_to_new_state[part_idx];

        for class_id in 0..num_classes as ClassId {
            let target = dfa.transition(rep, class_id);
            if target != DEAD_STATE {
                let target_partition = partition_of[target as usize];
                let new_target = partition_to_new_state[target_partition];
                if new_target != DEAD_STATE {
                    new_dfa.set_transition(new_state_id, class_id, new_target);
                }
            }
        }
    }

    new_dfa.start = 0;

    // --- Step 6: Canonical BFS state reordering ---
    // Renumber states in BFS order from state 0 so that the generated code is
    // deterministic regardless of NFA topology (e.g., DAFSA vs prefix-only).
    // This is O(S + T) where S = states, T = transitions — negligible overhead.
    canonicalize_state_order(&mut new_dfa);

    new_dfa
}

/// Renumber DFA states in BFS order from the start state.
///
/// This ensures that generated match arms appear in a canonical order,
/// independent of the NFA construction strategy (DAFSA vs prefix-only trie).
/// Future grammars with shared `Ident` tokens could trigger DAFSA merging,
/// producing different NFA topologies; canonical ordering makes the output
/// deterministic regardless.
///
/// Complexity: O(S + T) where S = number of states, T = total transitions.
pub fn canonicalize_state_order(dfa: &mut Dfa) {
    let n = dfa.states.len();
    if n <= 1 {
        return;
    }

    let num_classes = dfa.num_classes;

    // BFS from start state (always 0 after minimize_dfa)
    let mut old_to_new: Vec<StateId> = vec![DEAD_STATE; n];
    let mut new_order: Vec<StateId> = Vec::with_capacity(n);
    let mut queue = std::collections::VecDeque::with_capacity(n);

    old_to_new[dfa.start as usize] = 0;
    new_order.push(dfa.start);
    queue.push_back(dfa.start);

    while let Some(old_id) = queue.pop_front() {
        for class_id in 0..num_classes {
            let target = dfa.states[old_id as usize].transitions[class_id];
            if target != DEAD_STATE && old_to_new[target as usize] == DEAD_STATE {
                let new_id = new_order.len() as StateId;
                old_to_new[target as usize] = new_id;
                new_order.push(target);
                queue.push_back(target);
            }
        }
    }

    // Check if already in BFS order (common case — skip reordering)
    let already_ordered = new_order
        .iter()
        .enumerate()
        .all(|(i, &old)| old == i as StateId);
    if already_ordered && new_order.len() == n {
        return;
    }

    // Build reordered states vector
    let mut new_states: Vec<DfaState> = Vec::with_capacity(new_order.len());
    for &old_id in &new_order {
        let old_state = &dfa.states[old_id as usize];
        let mut new_transitions = Vec::with_capacity(num_classes);
        for &target in &old_state.transitions {
            if target == DEAD_STATE {
                new_transitions.push(DEAD_STATE);
            } else {
                new_transitions.push(old_to_new[target as usize]);
            }
        }
        new_states.push(DfaState {
            transitions: new_transitions,
            accept: old_state.accept.clone(),
            weight: old_state.weight,
        });
    }

    dfa.states = new_states;
    dfa.start = 0;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa_default, BuiltinNeeds};
    use crate::automata::partition::compute_equivalence_classes;
    use crate::automata::subset::subset_construction;
    use crate::automata::TerminalPattern;
    use crate::automata::TokenKind;

    #[test]
    fn test_minimize_simple() {
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "-".to_string(),
                kind: TokenKind::Fixed("-".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa_default(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // Minimized DFA should have no more states than the original
        assert!(
            min_dfa.states.len() <= dfa.states.len(),
            "minimized DFA ({} states) should have no more states than original ({} states)",
            min_dfa.states.len(),
            dfa.states.len()
        );
    }

    #[test]
    fn test_canonicalize_idempotent() {
        // Canonical reordering applied twice should produce the same DFA.
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "++".to_string(),
                kind: TokenKind::Fixed("++".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "-".to_string(),
                kind: TokenKind::Fixed("-".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "->".to_string(),
                kind: TokenKind::Fixed("->".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa_default(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // Snapshot state after first canonicalization (already done in minimize_dfa)
        let first_pass_states: Vec<_> = min_dfa
            .states
            .iter()
            .map(|s| (s.transitions.clone(), s.accept.clone()))
            .collect();

        // Apply canonicalization again
        let mut dfa_copy = min_dfa.clone();
        canonicalize_state_order(&mut dfa_copy);

        let second_pass_states: Vec<_> = dfa_copy
            .states
            .iter()
            .map(|s| (s.transitions.clone(), s.accept.clone()))
            .collect();

        assert_eq!(
            first_pass_states, second_pass_states,
            "canonical BFS reordering should be idempotent"
        );
    }

    #[test]
    fn test_minimize_preserves_acceptance() {
        let terminals = vec![
            TerminalPattern {
                text: "==".to_string(),
                kind: TokenKind::Fixed("==".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "=".to_string(),
                kind: TokenKind::Fixed("=".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: false,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa_default(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // After lexing "=", should accept Fixed("=")
        let mut state = min_dfa.start;
        let class = partition.classify(b'=');
        state = min_dfa.transition(state, class);
        assert_ne!(state, DEAD_STATE);
        assert_eq!(min_dfa.states[state as usize].accept, Some(TokenKind::Fixed("=".to_string())));

        // After lexing "==", should accept Fixed("==")
        let state2 = min_dfa.transition(state, class);
        assert_ne!(state2, DEAD_STATE);
        assert_eq!(
            min_dfa.states[state2 as usize].accept,
            Some(TokenKind::Fixed("==".to_string()))
        );
    }
}
