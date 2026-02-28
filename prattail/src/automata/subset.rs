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
    let resolved = resolve_accept(nfa, &start_set);
    dfa.states[0].accept = resolved.kind;
    dfa.states[0].weight = resolved.weight;
    dfa.states[0].alt_accepts = resolved.alt_accepts;
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
                let resolved = resolve_accept(nfa, &ec_closure);
                let new_state = dfa.add_state(DfaState {
                    transitions: vec![DEAD_STATE; num_classes],
                    accept: resolved.kind,
                    weight: resolved.weight,
                    alt_accepts: resolved.alt_accepts,
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

/// Resolved accept information for a set of NFA states.
///
/// Contains the primary (highest-priority) accept token and weight, plus
/// ALL alternative accepts sorted by weight. `alt_accepts` is non-empty
/// only when 2+ distinct `TokenKind`s are valid for this DFA state.
pub(crate) struct ResolvedAccept {
    /// Primary accept (lowest weight = highest priority), or `None`.
    pub kind: Option<TokenKind>,
    /// Weight of the primary accept. `TropicalWeight::zero()` (infinity) if no accept.
    pub weight: TropicalWeight,
    /// All alternative accepts (including the primary), sorted by weight ascending.
    /// Empty if 0 or 1 accepting NFA states (unambiguous).
    pub alt_accepts: Vec<(TokenKind, TropicalWeight)>,
}

/// Resolve the accept token, weight, and ALL alternatives for a set of NFA states.
///
/// Primary: highest priority (lowest tropical weight) wins.
/// Alternatives: all distinct `TokenKind`s, deduplicated, sorted by weight.
/// `alt_accepts` is populated only when 2+ distinct token kinds exist.
fn resolve_accept(nfa: &Nfa, states: &[StateId]) -> ResolvedAccept {
    // Collect all accepting (kind, weight) pairs, keeping the best weight per kind.
    let mut by_kind: std::collections::BTreeMap<TokenKind, TropicalWeight> =
        std::collections::BTreeMap::new();

    for &s in states {
        let nfa_state = &nfa.states[s as usize];
        if let Some(ref kind) = nfa_state.accept {
            let w = nfa_state.weight;
            by_kind
                .entry(kind.clone())
                .and_modify(|existing| {
                    if w < *existing {
                        *existing = w;
                    }
                })
                .or_insert(w);
        }
    }

    if by_kind.is_empty() {
        return ResolvedAccept {
            kind: None,
            weight: TropicalWeight::zero(),
            alt_accepts: Vec::new(),
        };
    }

    // Sort alternatives by weight (ascending = best first)
    let mut alts: Vec<(TokenKind, TropicalWeight)> = by_kind.into_iter().collect();
    alts.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

    let kind = alts[0].0.clone();
    let weight = alts[0].1;

    // Only populate alt_accepts when 2+ distinct token kinds
    let alt_accepts = if alts.len() >= 2 { alts } else { Vec::new() };

    ResolvedAccept {
        kind: Some(kind),
        weight,
        alt_accepts,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::nfa::{build_nfa, BuiltinNeeds};
    use crate::LiteralPatterns;
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

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
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
        let num_accepting = dfa.states.iter().filter(|s| s.accept.is_some()).count();
        assert!(num_accepting > 0, "DFA should have at least one accepting state");
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

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
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

    #[test]
    fn test_multi_accept_keyword_ident() {
        // "error" is both a keyword and a valid identifier.
        // The DFA state after "error" should have alt_accepts with both.
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

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        // Walk "error" through the DFA
        let mut state = dfa.start;
        for &byte in b"error" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, super::DEAD_STATE);
        }

        let dfa_state = &dfa.states[state as usize];

        // Primary winner is Fixed("error") (higher priority)
        assert_eq!(
            dfa_state.accept,
            Some(TokenKind::Fixed("error".to_string())),
        );

        // alt_accepts should contain both Fixed("error") and Ident
        assert!(
            dfa_state.is_ambiguous(),
            "state after 'error' should be ambiguous (keyword + ident)"
        );
        assert_eq!(dfa_state.alt_accepts.len(), 2);

        // Verify both kinds are present
        let kinds: Vec<&TokenKind> = dfa_state.alt_accepts.iter().map(|(k, _)| k).collect();
        assert!(kinds.contains(&&TokenKind::Ident));
        assert!(kinds.contains(&&TokenKind::Fixed("error".to_string())));

        // Verify weight ordering: Fixed (priority 10) should be first (lower weight)
        assert!(
            dfa_state.alt_accepts[0].1 <= dfa_state.alt_accepts[1].1,
            "alt_accepts should be sorted by weight ascending"
        );
    }

    #[test]
    fn test_unambiguous_states_have_empty_alt_accepts() {
        // Pure operators like "+" should NOT have alt_accepts
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
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

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        // Walk "+" through the DFA
        let mut state = dfa.start;
        let class = partition.classify(b'+');
        state = dfa.transition(state, class);
        assert_ne!(state, super::DEAD_STATE);

        let dfa_state = &dfa.states[state as usize];
        assert_eq!(dfa_state.accept, Some(TokenKind::Fixed("+".to_string())));
        assert!(
            !dfa_state.is_ambiguous(),
            "'+' should not be ambiguous"
        );
        assert!(dfa_state.alt_accepts.is_empty());
    }

    #[test]
    fn test_multi_accept_boolean_ident() {
        // "true" is both a boolean keyword and a valid identifier
        let terminals = vec![TerminalPattern {
            text: "true".to_string(),
            kind: TokenKind::True,
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        // Walk "true" through the DFA
        let mut state = dfa.start;
        for &byte in b"true" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, super::DEAD_STATE);
        }

        let dfa_state = &dfa.states[state as usize];

        // Primary winner: True (priority 10) beats Ident (priority 1)
        assert_eq!(dfa_state.accept, Some(TokenKind::True));

        // Should be ambiguous (True + Ident)
        assert!(
            dfa_state.is_ambiguous(),
            "state after 'true' should be ambiguous (boolean + ident)"
        );
    }

    #[test]
    fn test_dfa_has_ambiguous_accepts() {
        // Grammar with keyword → has_ambiguous_accepts() = true
        let terminals = vec![TerminalPattern {
            text: "if".to_string(),
            kind: TokenKind::Fixed("if".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        assert!(
            dfa.has_ambiguous_accepts(),
            "DFA with keyword 'if' and ident should have ambiguous accepts"
        );

        let ambiguous = dfa.ambiguous_states();
        assert!(!ambiguous.is_empty(), "should find ambiguous states");

        // Each ambiguous state should have 2+ alternatives
        for (_, alts) in &ambiguous {
            assert!(alts.len() >= 2, "ambiguous state should have 2+ alternatives");
        }
    }

    #[test]
    fn test_dfa_no_ambiguous_accepts() {
        // Grammar with only operators → no ambiguous states
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
            ident: false,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        assert!(
            !dfa.has_ambiguous_accepts(),
            "DFA with only operators should not have ambiguous accepts"
        );
        assert!(dfa.ambiguous_states().is_empty());
    }
}
