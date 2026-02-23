//! Subset construction: NFA → DFA conversion.
//!
//! Implements the standard powerset construction algorithm:
//! 1. Compute epsilon-closure of the NFA start state → DFA start state
//! 2. For each DFA state and each equivalence class, compute reachable NFA states
//! 3. DFA accept state inherits highest-priority accept token
//!
//! This inherently eliminates all epsilon transitions.
//!
//! ## Optimizations
//!
//! - **Thread-local buffer pooling:** `visited`, `ec_closure`, `ec_stack`, and
//!   `target_set` retain capacity across calls via `Cell<Vec<T>>` take/set pattern.
//!   Only 1 TLS access per `subset_construction` call (vs ~300 if TLS were at
//!   the `epsilon_closure` level).
//! - **`epsilon_closure_reuse`:** Receives buffers from the caller, resetting
//!   `visited` flags in O(closure_size) instead of O(nfa.states.len()).
//! - **Pre-allocation:** `state_map` and `worklist` pre-allocated to NFA-size
//!   heuristic; `visited` exact-sized on first call.

use std::cell::Cell;
use std::collections::HashMap;

use super::{
    nfa::{epsilon_closure, epsilon_closure_reuse},
    partition::AlphabetPartition,
    semiring::{Semiring, TropicalWeight},
    ClassId, Dfa, DfaState, Nfa, StateId, TokenKind, DEAD_STATE,
};

thread_local! {
    /// Reusable visited-state bitmap for epsilon_closure_reuse.
    /// Exact size: nfa.states.len(). Reused across calls.
    static VISITED: Cell<Vec<bool>> = const { Cell::new(Vec::new()) };
    /// Reusable closure result buffer for epsilon_closure_reuse.
    static EC_CLOSURE: Cell<Vec<StateId>> = const { Cell::new(Vec::new()) };
    /// Reusable stack buffer for epsilon_closure_reuse.
    static EC_STACK: Cell<Vec<StateId>> = const { Cell::new(Vec::new()) };
    /// Reusable buffer for collecting move targets before epsilon closure.
    static TARGET_SET: Cell<Vec<StateId>> = const { Cell::new(Vec::new()) };
}

/// Convert an NFA to a DFA using subset construction with alphabet partitioning.
///
/// The resulting DFA uses equivalence class IDs for transitions (not raw bytes),
/// so transition tables are compact. Transitions are stored as dense arrays
/// indexed by class ID for O(1) lookup.
pub fn subset_construction(nfa: &Nfa, partition: &AlphabetPartition) -> Dfa {
    let num_classes = partition.num_classes;
    let n = nfa.states.len();
    let mut dfa = Dfa::new(num_classes);

    // Pre-allocate HashMap and worklist with NFA-size heuristic
    let mut state_map: HashMap<Vec<StateId>, StateId> = HashMap::with_capacity(n);
    // Worklist of DFA states to process
    let mut worklist: Vec<Vec<StateId>> = Vec::with_capacity(n);

    // Take TLS buffers and ensure first-call pre-allocation
    let mut visited = VISITED.with(|cell| cell.take());
    visited.clear();
    visited.resize(n, false); // exact size; reuses capacity on subsequent calls

    let mut ec_closure = EC_CLOSURE.with(|cell| cell.take());
    ec_closure.clear();
    if ec_closure.capacity() < n {
        ec_closure.reserve(n - ec_closure.capacity());
    }

    let mut ec_stack = EC_STACK.with(|cell| cell.take());
    ec_stack.clear();
    if ec_stack.capacity() < n {
        ec_stack.reserve(n - ec_stack.capacity());
    }

    let mut target_set = TARGET_SET.with(|cell| cell.take());
    target_set.clear();
    if target_set.capacity() < n {
        target_set.reserve(n - target_set.capacity());
    }

    // Start state: epsilon-closure of NFA start (uses original epsilon_closure
    // for the initial set since we need an owned Vec for state_map insertion)
    let start_set = epsilon_closure(nfa, &[nfa.start]);
    let (start_accept, start_weight) = resolve_accept(nfa, &start_set);
    dfa.states[0].accept = start_accept;
    dfa.states[0].weight = start_weight;
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
            target_set.clear();
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

            // Compute epsilon-closure of the target set using reusable buffers
            epsilon_closure_reuse(nfa, &target_set, &mut visited, &mut ec_closure, &mut ec_stack);

            // Look up or create the DFA state for this NFA state set
            let target_dfa_state = if let Some(&existing) = state_map.get(ec_closure.as_slice()) {
                existing
            } else {
                let (accept, weight) = resolve_accept(nfa, &ec_closure);
                let new_state = dfa.add_state(DfaState {
                    transitions: vec![DEAD_STATE; num_classes],
                    accept,
                    weight,
                });
                state_map.insert(ec_closure.clone(), new_state);
                worklist.push(ec_closure.clone());
                new_state
            };

            dfa.set_transition(current_dfa_state, class_id, target_dfa_state);
        }
    }

    // Return TLS buffers for reuse
    VISITED.with(|cell| cell.set(visited));
    EC_CLOSURE.with(|cell| cell.set(ec_closure));
    EC_STACK.with(|cell| cell.set(ec_stack));
    TARGET_SET.with(|cell| cell.set(target_set));

    dfa
}

/// Resolve the accept token and weight for a set of NFA states.
///
/// If multiple NFA states in the set are accepting, the one with highest
/// priority (lowest tropical weight) wins. Returns `(token_kind, weight)`.
fn resolve_accept(nfa: &Nfa, states: &[StateId]) -> (Option<TokenKind>, TropicalWeight) {
    let mut best_kind: Option<&TokenKind> = None;
    let mut best_weight = TropicalWeight::zero(); // infinity = unreachable

    for &s in states {
        let nfa_state = &nfa.states[s as usize];
        if let Some(ref kind) = nfa_state.accept {
            // Tropical plus = min: lower weight wins (higher priority)
            let w = nfa_state.weight;
            if best_kind.is_none() || w < best_weight {
                best_kind = Some(kind);
                best_weight = w;
            }
        }
    }

    (best_kind.cloned(), best_weight)
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
