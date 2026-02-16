//! Subset construction: NFA → DFA conversion.
//!
//! Implements the standard powerset construction algorithm:
//! 1. Compute epsilon-closure of the NFA start state → DFA start state
//! 2. For each DFA state and each equivalence class, compute reachable NFA states
//! 3. DFA accept state inherits highest-priority accept token
//!
//! This inherently eliminates all epsilon transitions.

use std::collections::HashMap;

use super::{
    nfa::epsilon_closure, partition::AlphabetPartition, ClassId, Dfa, DfaState, Nfa, StateId,
    TokenKind, DEAD_STATE,
};

/// Convert an NFA to a DFA using subset construction with alphabet partitioning.
///
/// The resulting DFA uses equivalence class IDs for transitions (not raw bytes),
/// so transition tables are compact. Transitions are stored as dense arrays
/// indexed by class ID for O(1) lookup.
pub fn subset_construction(nfa: &Nfa, partition: &AlphabetPartition) -> Dfa {
    let num_classes = partition.num_classes;
    let mut dfa = Dfa::new(num_classes);

    // Map from sorted set of NFA states → DFA state ID
    let mut state_map: HashMap<Vec<StateId>, StateId> = HashMap::new();
    // Worklist of DFA states to process
    let mut worklist: Vec<Vec<StateId>> = Vec::new();

    // Start state: epsilon-closure of NFA start
    let start_set = epsilon_closure(nfa, &[nfa.start]);
    let start_accept = resolve_accept(nfa, &start_set);
    dfa.states[0].accept = start_accept;
    state_map.insert(start_set.clone(), 0);
    worklist.push(start_set);

    while let Some(current_set) = worklist.pop() {
        let current_dfa_state = *state_map
            .get(&current_set)
            .expect("current set should be in state_map");

        // For each equivalence class, compute the set of NFA states reachable
        for class_id in 0..num_classes as ClassId {
            let rep_byte = partition.class_representatives[class_id as usize];

            // Compute move(current_set, class_id): all NFA states reachable via
            // transitions on any byte in this equivalence class
            let mut target_set: Vec<StateId> = Vec::new();
            for &nfa_state in &current_set {
                for (char_class, target) in &nfa.states[nfa_state as usize].transitions {
                    if char_class.contains(rep_byte) {
                        target_set.push(*target);
                    }
                }
            }

            if target_set.is_empty() {
                continue; // Dead state — no transition for this class
            }

            // Compute epsilon-closure of the target set
            target_set = epsilon_closure(nfa, &target_set);

            // Look up or create the DFA state for this NFA state set
            let target_dfa_state = if let Some(&existing) = state_map.get(&target_set) {
                existing
            } else {
                let accept = resolve_accept(nfa, &target_set);
                let new_state = dfa.add_state(DfaState {
                    transitions: vec![DEAD_STATE; num_classes],
                    accept,
                });
                state_map.insert(target_set.clone(), new_state);
                worklist.push(target_set);
                new_state
            };

            dfa.set_transition(current_dfa_state, class_id, target_dfa_state);
        }
    }

    dfa
}

/// Resolve the accept token for a set of NFA states.
/// If multiple NFA states in the set are accepting, the one with highest
/// priority wins.
fn resolve_accept(nfa: &Nfa, states: &[StateId]) -> Option<TokenKind> {
    states
        .iter()
        .filter_map(|&s| nfa.states[s as usize].accept.as_ref())
        .max_by_key(|kind| kind.priority())
        .cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa, BuiltinNeeds};
    use crate::automata::partition::compute_equivalence_classes;
    use crate::automata::TerminalPattern;
    use crate::automata::TokenKind;

    #[test]
    fn test_subset_construction_simple() {
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "*".to_string(),
                kind: TokenKind::Fixed("*".to_string()),
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

        // DFA should have a reasonable number of states
        assert!(
            dfa.states.len() < 20,
            "DFA should have fewer than 20 states, got {}",
            dfa.states.len()
        );

        // Start state should not be accepting
        assert!(
            dfa.states[dfa.start as usize].accept.is_none(),
            "start state should not be accepting"
        );

        // There should be at least one accepting state
        let num_accepting = dfa
            .states
            .iter()
            .filter(|s| s.accept.is_some())
            .count();
        assert!(
            num_accepting > 0,
            "DFA should have at least one accepting state"
        );
    }

    #[test]
    fn test_keyword_priority() {
        // "error" as keyword should win over identifier
        let terminals = vec![TerminalPattern {
            text: "error".to_string(),
            kind: TokenKind::Fixed("error".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        // Simulate lexing "error" through the DFA
        let mut state = dfa.start;
        for &byte in b"error" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, DEAD_STATE, "should not reach dead state while lexing 'error'");
        }

        // After "error", should be in a state accepting Fixed("error"), not Ident
        let accept = &dfa.states[state as usize].accept;
        assert_eq!(
            accept,
            &Some(TokenKind::Fixed("error".to_string())),
            "keyword 'error' should have higher priority than identifier"
        );
    }
}
