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

use super::{ClassId, Dfa, DfaState, StateId, DEAD_STATE};
use std::collections::BTreeMap;

/// Minimize a DFA using Hopcroft's algorithm with inverse transition map.
///
/// Returns a new DFA with equivalent states merged.
pub fn minimize_dfa(dfa: &Dfa) -> Dfa {
    let n = dfa.states.len();
    if n <= 1 {
        return dfa.clone();
    }

    let num_classes = dfa.num_classes;

    // --- Step 1: Build inverse transition map ---
    // inverse[target_state][class_id] = list of predecessor states
    // that transition to target_state on class_id.
    let mut inverse: Vec<Vec<Vec<StateId>>> = vec![vec![Vec::new(); num_classes]; n];
    for (state_idx, state) in dfa.states.iter().enumerate() {
        let state_id = state_idx as StateId;
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                inverse[target as usize][class_id].push(state_id);
            }
        }
    }

    // --- Step 2: Initial partition — group by accept token kind ---
    // Use the TokenKind's discriminant for grouping instead of format!("{:?}") Strings.
    // We use BTreeMap<Option<TokenKind>, Vec<StateId>> since TokenKind derives Ord.
    let mut accept_groups: BTreeMap<Option<&super::TokenKind>, Vec<StateId>> = BTreeMap::new();
    for (i, state) in dfa.states.iter().enumerate() {
        accept_groups
            .entry(state.accept.as_ref())
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
    // Reusable buffers to avoid repeated allocation
    let mut affected_partitions: Vec<usize> = Vec::new();
    let mut goes_to_splitter: Vec<StateId> = Vec::new();

    while let Some((splitter_idx, class_id)) = worklist.pop() {
        // Skip if the partition is empty (may have been emptied by a split)
        if partitions[splitter_idx].is_empty() {
            continue;
        }

        // Collect all predecessor states that transition into the splitter on class_id.
        // These are the only states that *could* cause a partition to split.
        affected_partitions.clear();
        // Track which partitions have predecessors (to avoid duplicates)
        // Use a simple Vec<bool> since partition count is small.
        let num_partitions = partitions.len();
        let mut partition_seen = vec![false; num_partitions];

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

    // Assign remaining states
    for &part_idx in &non_empty {
        if partition_to_new_state[part_idx] != DEAD_STATE {
            continue; // already assigned (start partition)
        }
        let rep = partitions[part_idx][0];
        let new_state = new_dfa.add_state(DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: dfa.states[rep as usize].accept.clone(),
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
    new_dfa
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa, BuiltinNeeds};
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

        let nfa = build_nfa(&terminals, &needs);
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

        let nfa = build_nfa(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        // After lexing "=", should accept Fixed("=")
        let mut state = min_dfa.start;
        let class = partition.classify(b'=');
        state = min_dfa.transition(state, class);
        assert_ne!(state, DEAD_STATE);
        assert_eq!(
            min_dfa.states[state as usize].accept,
            Some(TokenKind::Fixed("=".to_string()))
        );

        // After lexing "==", should accept Fixed("==")
        let state2 = min_dfa.transition(state, class);
        assert_ne!(state2, DEAD_STATE);
        assert_eq!(
            min_dfa.states[state2 as usize].accept,
            Some(TokenKind::Fixed("==".to_string()))
        );
    }
}
