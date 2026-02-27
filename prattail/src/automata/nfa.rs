//! NFA construction from terminal patterns.
//!
//! Fixed string terminals (keywords, operators) are built as a prefix-sharing
//! trie directly in the NFA — common prefixes like `=`/`==` or `true`/`try`
//! share NFA states, reducing state count and downstream DFA size.
//!
//! Character-class patterns (identifiers, integers, floats, strings) remain
//! Thompson fragments since they use ranges rather than single bytes.

use std::collections::HashMap;

use super::{
    regex, semiring::TropicalWeight, CharClass, Nfa, NfaFragment, NfaState, StateId,
    TerminalPattern, TokenKind,
};
use crate::LiteralPatterns;

/// Build a complete NFA from a set of terminal patterns plus built-in
/// character-class patterns (identifiers, integers, floats, strings).
///
/// Fixed string terminals are built as a prefix-sharing trie: common prefixes
/// (e.g., `=`/`==`, `true`/`try`/`type`) share NFA states, reducing the total
/// state count compared to per-terminal Thompson chains.
///
/// Character-class patterns are compiled from configurable regex patterns
/// (from `LiteralPatterns`) via the Thompson NFA construction pipeline.
pub fn build_nfa(
    terminals: &[TerminalPattern],
    needs: &BuiltinNeeds,
    patterns: &LiteralPatterns,
) -> Nfa {
    let mut nfa = Nfa::new();
    let global_start = nfa.start;

    // Build keyword/operator trie (prefix-sharing)
    if !terminals.is_empty() {
        let trie_root = build_keyword_trie(&mut nfa, terminals);
        nfa.add_epsilon(global_start, trie_root);
    }

    // Build built-in character class patterns from configurable regex patterns
    let mut fragments: Vec<NfaFragment> = Vec::new();
    if needs.ident {
        let frag = regex::compile_regex(&patterns.ident, &mut nfa, TokenKind::Ident)
            .expect("ident pattern should be a valid regex");
        fragments.push(frag);
    }
    if needs.integer {
        let frag = regex::compile_regex(&patterns.integer, &mut nfa, TokenKind::Integer)
            .expect("integer pattern should be a valid regex");
        fragments.push(frag);
    }
    if needs.float {
        let frag = regex::compile_regex(&patterns.float, &mut nfa, TokenKind::Float)
            .expect("float pattern should be a valid regex");
        fragments.push(frag);
    }
    if needs.string_lit {
        let frag = regex::compile_regex(&patterns.string, &mut nfa, TokenKind::StringLit)
            .expect("string pattern should be a valid regex");
        fragments.push(frag);
    }

    // Combine character-class fragments via alternation
    for frag in &fragments {
        nfa.add_epsilon(global_start, frag.start);
    }

    nfa
}

/// Build an NFA with default literal patterns.
///
/// Convenience wrapper for tests and callers that don't need custom patterns.
pub fn build_nfa_default(terminals: &[TerminalPattern], needs: &BuiltinNeeds) -> Nfa {
    build_nfa(terminals, needs, &LiteralPatterns::default())
}

/// What built-in character-class patterns are needed by the grammar.
#[derive(Debug, Clone, Default)]
pub struct BuiltinNeeds {
    /// Whether the grammar uses identifiers (almost always true).
    pub ident: bool,
    /// Whether any type has a native integer type.
    pub integer: bool,
    /// Whether any type has a native float type.
    pub float: bool,
    /// Whether any type has a native string type.
    pub string_lit: bool,
    /// Whether any type has a native bool type (keywords `true`/`false`).
    pub boolean: bool,
}

// ══════════════════════════════════════════════════════════════════════════════
// DAFSA (Directed Acyclic Finite State Automaton) — prefix + suffix sharing
// ══════════════════════════════════════════════════════════════════════════════

/// Signature of an NFA state for DAFSA suffix equivalence.
///
/// Two states are suffix-equivalent iff they have the same accept token and
/// identical outgoing transitions to identical targets. This is the key used
/// by the Daciuk et al. incremental algorithm's frozen-state registry.
#[derive(Clone, PartialEq, Eq, Hash)]
struct NodeSignature {
    accept: Option<TokenKind>,
    /// Sorted by byte for deterministic hashing.
    transitions: Vec<(u8, StateId)>,
}

impl NodeSignature {
    /// Extract a signature from a live NFA state. Only considers `CharClass::Single`
    /// transitions (the only kind used in the keyword trie).
    fn from_nfa_state(nfa: &Nfa, state_id: StateId) -> Self {
        let state = &nfa.states[state_id as usize];
        let mut transitions: Vec<(u8, StateId)> = state
            .transitions
            .iter()
            .filter_map(|(class, target)| {
                if let CharClass::Single(b) = class {
                    Some((*b, *target))
                } else {
                    None
                }
            })
            .collect();
        transitions.sort_unstable_by_key(|&(b, _)| b);
        NodeSignature {
            accept: state.accept.clone(),
            transitions,
        }
    }
}

/// An entry in the DAFSA construction path, tracking the current insertion path
/// from root to the deepest node of the most recently inserted terminal.
struct PathEntry {
    /// The NFA state at this position in the path.
    state: StateId,
    /// The byte label on the edge from the parent to this state.
    byte: u8,
}

/// Find the target state of a single-byte transition from `state` on `byte`.
fn find_transition(nfa: &Nfa, state: StateId, byte: u8) -> Option<StateId> {
    nfa.states[state as usize]
        .transitions
        .iter()
        .find_map(|(class, target)| {
            if let CharClass::Single(b) = class {
                if *b == byte {
                    Some(*target)
                } else {
                    None
                }
            } else {
                None
            }
        })
}

/// Set or upgrade the accept token on a state (higher priority wins).
///
/// Also updates the tropical weight to match the new token's priority.
fn set_or_upgrade_accept(nfa: &mut Nfa, state: StateId, kind: &TokenKind) {
    let nfa_state = &mut nfa.states[state as usize];
    match &nfa_state.accept {
        None => {
            nfa_state.accept = Some(kind.clone());
            nfa_state.weight = TropicalWeight::from_priority(kind.priority());
        },
        Some(existing) => {
            if kind.priority() > existing.priority() {
                nfa_state.accept = Some(kind.clone());
                nfa_state.weight = TropicalWeight::from_priority(kind.priority());
            }
        },
    }
}

/// Redirect an existing transition edge: change `parent --byte--> old_target`
/// to `parent --byte--> new_target`.
fn redirect_edge(nfa: &mut Nfa, parent: StateId, byte: u8, new_target: StateId) {
    for (class, target) in &mut nfa.states[parent as usize].transitions {
        if let CharClass::Single(b) = class {
            if *b == byte {
                *target = new_target;
                return;
            }
        }
    }
    panic!("redirect_edge: no transition on byte {} from state {}", byte, parent);
}

/// Freeze suffix states in the DAFSA construction path.
///
/// Walks backward from `path[path.len()-1]` to `path[keep_count]`, computing
/// the `NodeSignature` for each state. If an equivalent frozen state exists in
/// the registry, redirects the parent's edge to it (suffix sharing). Otherwise,
/// registers the state as a new frozen canonical representative.
///
/// `keep_count` is the number of path entries to keep unfrozen (the common
/// prefix with the next terminal). `trie_root` is needed as the parent of
/// `path[0]` (since the root itself is not part of the path).
fn freeze_suffixes(
    nfa: &mut Nfa,
    registry: &mut HashMap<NodeSignature, StateId>,
    path: &[PathEntry],
    trie_root: StateId,
    keep_count: usize,
) {
    // Walk backward from the deepest path entry to keep_count
    for i in (keep_count..path.len()).rev() {
        let state = path[i].state;
        let byte = path[i].byte;
        let sig = NodeSignature::from_nfa_state(nfa, state);

        if let Some(&canonical) = registry.get(&sig) {
            // An equivalent frozen state exists — redirect parent edge to it.
            let parent = if i > 0 { path[i - 1].state } else { trie_root };
            redirect_edge(nfa, parent, byte, canonical);
            // The old state becomes dead (unreachable) — left in nfa.states vector.
        } else {
            // Register this state as the canonical representative for its signature.
            registry.insert(sig, state);
        }
    }
}

/// Build a DAFSA (Directed Acyclic Finite State Automaton) for all fixed string
/// terminals directly in the NFA.
///
/// Extends prefix-sharing with suffix sharing using the Daciuk et al. incremental
/// algorithm. Terminals must arrive sorted (guaranteed by `BTreeSet<TerminalPattern>`
/// in the caller). Two trie nodes merge when they have identical accept tokens and
/// identical outgoing transitions to identical targets.
///
/// For grammars with suffix overlap (e.g., keywords ending in `"e"`, `"le"`, `"ile"`),
/// DAFSA merges redundant NFA states. For current small grammars the savings are
/// modest (0-3 states), but it guarantees optimality for any future grammar.
///
/// Merged states remain as unreachable dead entries in `nfa.states` — downstream
/// stages (subset construction, partition) only visit reachable states.
///
/// Returns the trie root state ID. The caller should add an epsilon transition
/// from the global NFA start to this root.
fn build_keyword_trie(nfa: &mut Nfa, terminals: &[TerminalPattern]) -> StateId {
    let trie_root = nfa.add_state(NfaState::new());

    // Registry of frozen states: NodeSignature → canonical StateId
    let mut registry: HashMap<NodeSignature, StateId> = HashMap::new();

    // Path tracks the insertion path for the previous terminal.
    // Each entry records (state, byte_from_parent).
    // path[0] is the first child of trie_root (not the root itself).
    let mut path: Vec<PathEntry> = Vec::new();

    let mut prev_bytes: Vec<u8> = Vec::new();

    for terminal in terminals {
        assert!(!terminal.text.is_empty(), "terminal string must not be empty");

        let bytes = terminal.text.as_bytes();

        // Step 1: Compute common prefix length with previous terminal
        let common_prefix_len = prev_bytes
            .iter()
            .zip(bytes.iter())
            .take_while(|(&a, &b)| a == b)
            .count();

        // Step 2: FREEZE — freeze suffix states from previous path that diverge
        if !path.is_empty() {
            freeze_suffixes(nfa, &mut registry, &path, trie_root, common_prefix_len);
            path.truncate(common_prefix_len);
        }

        // Step 3: INSERT — walk the common prefix, then add remaining chars
        let mut current = if path.is_empty() {
            trie_root
        } else {
            path.last()
                .expect("path should not be empty after truncation")
                .state
        };

        // Edge case: entire terminal is already in the common prefix (e.g., duplicate
        // text with different priority). Set/upgrade accept on the current state.
        if bytes.len() == common_prefix_len && !path.is_empty() {
            set_or_upgrade_accept(nfa, current, &terminal.kind);
            prev_bytes = bytes.to_vec();
            continue;
        }

        for (i, &byte) in bytes.iter().enumerate() {
            if i < common_prefix_len {
                // Already in the path — just advance
                continue;
            }

            let is_last = i == bytes.len() - 1;

            // Check if a transition for this byte already exists
            let existing = find_transition(nfa, current, byte);

            if let Some(target) = existing {
                current = target;
                if is_last {
                    set_or_upgrade_accept(nfa, current, &terminal.kind);
                }
                path.push(PathEntry { state: current, byte });
            } else {
                // Create new state
                let next = if is_last {
                    nfa.add_state(NfaState::accepting(terminal.kind.clone()))
                } else {
                    nfa.add_state(NfaState::new())
                };
                nfa.add_transition(current, next, CharClass::Single(byte));
                path.push(PathEntry { state: next, byte });
                current = next;
            }
        }

        prev_bytes = bytes.to_vec();
    }

    // Step 4: FINALIZE — freeze all remaining states from last path
    if !path.is_empty() {
        freeze_suffixes(nfa, &mut registry, &path, trie_root, 0);
    }

    trie_root
}

/// Build a prefix-only sharing trie for fixed string terminals (no suffix sharing).
///
/// **Preserved for testing**: used to verify DAFSA produces functionally equivalent
/// DFAs via `test_dafsa_produces_same_dfa` and `test_dafsa_vs_prefix_identical_codegen`.
#[cfg(test)]
pub(crate) fn build_keyword_trie_prefix_only(
    nfa: &mut Nfa,
    terminals: &[TerminalPattern],
) -> StateId {
    let trie_root = nfa.add_state(NfaState::new());

    for terminal in terminals {
        assert!(!terminal.text.is_empty(), "terminal string must not be empty");

        let mut current = trie_root;
        let bytes = terminal.text.as_bytes();

        for (i, &byte) in bytes.iter().enumerate() {
            let is_last = i == bytes.len() - 1;

            let existing = find_transition(nfa, current, byte);

            if let Some(target) = existing {
                current = target;
                if is_last {
                    set_or_upgrade_accept(nfa, current, &terminal.kind);
                }
            } else {
                let next = if is_last {
                    nfa.add_state(NfaState::accepting(terminal.kind.clone()))
                } else {
                    nfa.add_state(NfaState::new())
                };
                nfa.add_transition(current, next, CharClass::Single(byte));
                current = next;
            }
        }
    }

    trie_root
}

/// Build a complete NFA using prefix-only trie (no DAFSA suffix sharing).
///
/// **Preserved for testing**: allows A/B comparison of DAFSA vs prefix-only codegen
/// to verify that DAFSA does not affect generated lexer code for current grammars.
#[cfg(test)]
pub(crate) fn build_nfa_prefix_only(terminals: &[TerminalPattern], needs: &BuiltinNeeds) -> Nfa {
    let mut nfa = Nfa::new();
    let global_start = nfa.start;

    // Build keyword/operator trie (prefix-sharing only, no suffix merging)
    if !terminals.is_empty() {
        let trie_root = build_keyword_trie_prefix_only(&mut nfa, terminals);
        nfa.add_epsilon(global_start, trie_root);
    }

    // Build built-in character class patterns via regex compiler — same as build_nfa
    let patterns = crate::LiteralPatterns::default();
    let mut fragments: Vec<NfaFragment> = Vec::new();
    if needs.ident {
        fragments.push(
            regex::compile_regex(&patterns.ident, &mut nfa, TokenKind::Ident)
                .expect("default ident pattern should be valid"),
        );
    }
    if needs.integer {
        fragments.push(
            regex::compile_regex(&patterns.integer, &mut nfa, TokenKind::Integer)
                .expect("default integer pattern should be valid"),
        );
    }
    if needs.float {
        fragments.push(
            regex::compile_regex(&patterns.float, &mut nfa, TokenKind::Float)
                .expect("default float pattern should be valid"),
        );
    }
    if needs.string_lit {
        fragments.push(
            regex::compile_regex(&patterns.string, &mut nfa, TokenKind::StringLit)
                .expect("default string pattern should be valid"),
        );
    }

    // Combine character-class fragments via alternation
    for frag in &fragments {
        nfa.add_epsilon(global_start, frag.start);
    }

    nfa
}

/// Build an NFA fragment for a fixed string terminal (Thompson chain).
///
/// Creates a chain of single-character transitions ending in an accept state.
/// For example, `"=="` becomes:
/// ```text
///   start -'='-> s1 -'='-> accept(EqEq)
/// ```
///
/// **Note:** This function is preserved for testing and reference. The primary
/// `build_nfa()` uses `build_keyword_trie()` instead for prefix sharing.
#[cfg(test)]
fn build_string_fragment(nfa: &mut Nfa, text: &str, kind: TokenKind) -> NfaFragment {
    let bytes = text.as_bytes();
    assert!(!bytes.is_empty(), "terminal string must not be empty");

    let start = nfa.add_state(NfaState::new());
    let mut current = start;

    for (i, &byte) in bytes.iter().enumerate() {
        if i == bytes.len() - 1 {
            // Last character: transition to accept state
            let accept = nfa.add_state(NfaState::accepting(kind.clone()));
            nfa.add_transition(current, accept, CharClass::Single(byte));
            return NfaFragment { start, accept };
        } else {
            // Intermediate character: transition to next state
            let next = nfa.add_state(NfaState::new());
            nfa.add_transition(current, next, CharClass::Single(byte));
            current = next;
        }
    }

    unreachable!("terminal string must not be empty")
}

/// Compute the epsilon closure of a set of NFA states.
///
/// Returns all states reachable from `states` via zero or more epsilon transitions.
/// Pre-allocates `closure` and `stack` to `nfa.states.len()` to prevent
/// growth-reallocations (upper bound on closure size; n is typically 30-80).
pub fn epsilon_closure(nfa: &Nfa, states: &[StateId]) -> Vec<StateId> {
    let n = nfa.states.len();
    let mut closure: Vec<StateId> = Vec::with_capacity(n);
    closure.extend_from_slice(states);
    let mut stack: Vec<StateId> = Vec::with_capacity(n);
    stack.extend_from_slice(states);
    let mut visited = vec![false; n];

    for &s in states {
        visited[s as usize] = true;
    }

    while let Some(state) = stack.pop() {
        for &target in &nfa.states[state as usize].epsilon {
            if !visited[target as usize] {
                visited[target as usize] = true;
                closure.push(target);
                stack.push(target);
            }
        }
    }

    closure.sort_unstable();
    closure.dedup();
    closure
}

/// Compute epsilon closure reusing caller-provided buffers.
///
/// The caller must ensure `visited` is all-false on entry. This function
/// resets `visited` flags before returning (only touching set entries),
/// so the caller can reuse the same buffer across multiple calls.
/// The reset is O(closure_size), not O(nfa.states.len()).
///
/// This variant avoids per-call allocation of `visited`, `closure`, and `stack`
/// by receiving them as mutable references from the caller (typically TLS buffers
/// in `subset_construction`).
pub fn epsilon_closure_reuse(
    nfa: &Nfa,
    seeds: &[StateId],
    visited: &mut [bool],
    closure: &mut Vec<StateId>,
    stack: &mut Vec<StateId>,
) {
    closure.clear();
    stack.clear();

    closure.extend_from_slice(seeds);
    stack.extend_from_slice(seeds);
    for &s in seeds {
        visited[s as usize] = true;
    }

    while let Some(state) = stack.pop() {
        for &target in &nfa.states[state as usize].epsilon {
            if !visited[target as usize] {
                visited[target as usize] = true;
                closure.push(target);
                stack.push(target);
            }
        }
    }

    // Reset visited flags for reuse (O(closure_size), not O(nfa.states.len()))
    for &s in closure.iter() {
        visited[s as usize] = false;
    }

    closure.sort_unstable();
    closure.dedup();
}

#[cfg(test)]
mod tests {
    use super::*;

    // ══════════════════════════════════════════════════════════════════════
    // Thompson chain tests (build_string_fragment — preserved for reference)
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_build_string_fragment() {
        let mut nfa = Nfa::new();
        let frag = build_string_fragment(&mut nfa, "+", TokenKind::Fixed("+".to_string()));

        // Should have: original start (0), fragment start, accept
        assert_eq!(nfa.states.len(), 3);
        assert!(nfa.states[frag.accept as usize].accept.is_some());
    }

    #[test]
    fn test_build_multi_char_fragment() {
        let mut nfa = Nfa::new();
        let frag = build_string_fragment(&mut nfa, "==", TokenKind::Fixed("==".to_string()));

        // original start (0) + fragment start + intermediate + accept = 4
        assert_eq!(nfa.states.len(), 4);
        assert!(nfa.states[frag.accept as usize].accept.is_some());
    }

    #[test]
    fn test_compile_ident_pattern() {
        let mut nfa = Nfa::new();
        let patterns = crate::LiteralPatterns::default();
        let frag = regex::compile_regex(&patterns.ident, &mut nfa, TokenKind::Ident)
            .expect("ident pattern should compile");

        assert_eq!(nfa.states[frag.accept as usize].accept, Some(TokenKind::Ident));
    }

    #[test]
    fn test_epsilon_closure() {
        let mut nfa = Nfa::new();
        let s1 = nfa.add_state(NfaState::new());
        let s2 = nfa.add_state(NfaState::new());
        let s3 = nfa.add_state(NfaState::new());

        nfa.add_epsilon(0, s1);
        nfa.add_epsilon(s1, s2);
        nfa.add_epsilon(s2, s3);

        let closure = epsilon_closure(&nfa, &[0]);
        assert_eq!(closure, vec![0, s1, s2, s3]);
    }

    #[test]
    fn test_build_nfa() {
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

        let nfa = build_nfa_default(&terminals, &needs);
        // Check that the start state has epsilon transitions
        assert!(
            !nfa.states[nfa.start as usize].epsilon.is_empty(),
            "start state should have epsilon transitions to fragments"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Keyword trie tests (build_keyword_trie)
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_keyword_trie_single_char() {
        // Single-char terminals should produce one transition each from trie root.
        let mut nfa = Nfa::new();
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

        let trie_root = build_keyword_trie(&mut nfa, &terminals);

        // Trie root should have exactly 2 transitions ('+' and '*')
        assert_eq!(nfa.states[trie_root as usize].transitions.len(), 2);

        // Both target states should be accepting
        for (_, target) in &nfa.states[trie_root as usize].transitions {
            assert!(
                nfa.states[*target as usize].accept.is_some(),
                "single-char terminal target should be accepting"
            );
        }

        // States: nfa start(0), trie_root(1), accept_plus(2), accept_star(3) = 4
        assert_eq!(nfa.states.len(), 4);
    }

    #[test]
    fn test_keyword_trie_prefix_sharing() {
        // `=` and `==` should share the first `=` state.
        let mut nfa = Nfa::new();
        let terminals = vec![
            TerminalPattern {
                text: "=".to_string(),
                kind: TokenKind::Fixed("=".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "==".to_string(),
                kind: TokenKind::Fixed("==".to_string()),
                is_keyword: false,
            },
        ];

        let trie_root = build_keyword_trie(&mut nfa, &terminals);

        // Trie root should have exactly 1 transition ('=')
        assert_eq!(
            nfa.states[trie_root as usize].transitions.len(),
            1,
            "= and == should share the '=' transition from root"
        );

        // The '=' state should be accepting (for single `=`)
        let eq_state = nfa.states[trie_root as usize].transitions[0].1;
        assert_eq!(
            nfa.states[eq_state as usize].accept,
            Some(TokenKind::Fixed("=".to_string())),
            "shared '=' state should accept single '='"
        );

        // The '=' state should also have a transition to '==' state
        assert_eq!(
            nfa.states[eq_state as usize].transitions.len(),
            1,
            "'=' state should have one transition for second '='"
        );

        let eq_eq_state = nfa.states[eq_state as usize].transitions[0].1;
        assert_eq!(
            nfa.states[eq_eq_state as usize].accept,
            Some(TokenKind::Fixed("==".to_string())),
            "'==' state should accept '=='"
        );

        // States: nfa start(0), trie_root(1), eq_accept(2), eq_eq_accept(3) = 4
        // Chain construction would need: start(0), frag1_start, eq_accept, frag2_start, eq_inter, eq_eq_accept = 7
        assert_eq!(nfa.states.len(), 4);
    }

    #[test]
    fn test_keyword_trie_keywords_sharing_prefix() {
        // `true`, `try`, `type` share `t`→`r` prefix for true/try, `t` for all three
        let mut nfa = Nfa::new();
        let terminals = vec![
            TerminalPattern {
                text: "true".to_string(),
                kind: TokenKind::True,
                is_keyword: true,
            },
            TerminalPattern {
                text: "try".to_string(),
                kind: TokenKind::Fixed("try".to_string()),
                is_keyword: true,
            },
            TerminalPattern {
                text: "type".to_string(),
                kind: TokenKind::Fixed("type".to_string()),
                is_keyword: true,
            },
        ];

        let trie_root = build_keyword_trie(&mut nfa, &terminals);

        // Trie root should have exactly 1 transition ('t')
        assert_eq!(
            nfa.states[trie_root as usize].transitions.len(),
            1,
            "all three keywords start with 't'"
        );

        // Follow 't' to find shared state
        let t_state = nfa.states[trie_root as usize].transitions[0].1;
        // 't' state should have 2 transitions: 'r' (true/try) and 'y' (type)
        assert_eq!(
            nfa.states[t_state as usize].transitions.len(),
            2,
            "after 't': 'r' for true/try and 'y' for type"
        );

        // Follow 'r' from t_state
        let r_state = nfa.states[t_state as usize]
            .transitions
            .iter()
            .find_map(|(class, target)| {
                if let CharClass::Single(b'r') = class {
                    Some(*target)
                } else {
                    None
                }
            })
            .expect("should have 'r' transition");

        // 'r' state should have 2 transitions: 'u' (true) and 'y' (try)
        assert_eq!(
            nfa.states[r_state as usize].transitions.len(),
            2,
            "after 'tr': 'u' for true and 'y' for try"
        );

        // Verify total state count: trie construction shares prefix states
        // Chain: 3 keywords × (1 start + avg 3 intermediate + 1 accept) = ~15 + nfa_start = ~16
        // Trie: nfa_start(0), trie_root(1), t(2), r(3), u(4), e(5=accept:true),
        //       y(6=accept:try), y(7), p(8), e(9=accept:type) = 10
        assert_eq!(nfa.states.len(), 10);
    }

    #[test]
    fn test_keyword_trie_state_reduction() {
        // Quantitative comparison: trie vs chain construction
        let terminals = vec![
            TerminalPattern {
                text: "=".to_string(),
                kind: TokenKind::Fixed("=".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "==".to_string(),
                kind: TokenKind::Fixed("==".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "!=".to_string(),
                kind: TokenKind::Fixed("!=".to_string()),
                is_keyword: false,
            },
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

        // Chain construction state count
        let mut chain_nfa = Nfa::new();
        for t in &terminals {
            build_string_fragment(&mut chain_nfa, &t.text, t.kind.clone());
        }
        let chain_states = chain_nfa.states.len() - 1; // exclude global start

        // Trie construction state count
        let mut trie_nfa = Nfa::new();
        let trie_root = build_keyword_trie(&mut trie_nfa, &terminals);
        let trie_states = trie_nfa.states.len() - 1; // exclude global start

        assert!(
            trie_states < chain_states,
            "trie ({} states) should use fewer states than chains ({} states)",
            trie_states,
            chain_states,
        );

        // Verify specific counts:
        // Chain: 7 terminals produce 7 fragment_starts + sum of chars in all terminals
        //   = (1) + (2) + (2) + (1) + (2) + (1) + (2) = 11 intermediate/accept states
        //   + 7 fragment starts = 18 states (excl. global start)
        // Trie: = → ==(4), !=(3), + → ++(4), - → ->(4) = ~10 states + trie_root
        assert!(trie_states <= 11, "trie should have at most 11 states (got {})", trie_states);

        // Verify trie root exists and is reachable
        assert!(trie_root > 0, "trie root should not be global start");
    }

    #[test]
    fn test_keyword_trie_priority_resolution() {
        // When two terminals share exact same text, higher priority wins
        let mut nfa = Nfa::new();
        let terminals = vec![
            TerminalPattern {
                text: "foo".to_string(),
                kind: TokenKind::Ident, // priority 1
                is_keyword: false,
            },
            TerminalPattern {
                text: "foo".to_string(),
                kind: TokenKind::Fixed("foo".to_string()), // priority 10
                is_keyword: true,
            },
        ];

        let trie_root = build_keyword_trie(&mut nfa, &terminals);

        // Follow f→o→o
        let f_state = nfa.states[trie_root as usize].transitions[0].1;
        let o1_state = nfa.states[f_state as usize].transitions[0].1;
        let o2_state = nfa.states[o1_state as usize].transitions[0].1;

        // The final state should have the Fixed token (higher priority)
        assert_eq!(
            nfa.states[o2_state as usize].accept,
            Some(TokenKind::Fixed("foo".to_string())),
            "higher-priority token should win"
        );
    }

    #[test]
    fn test_keyword_trie_builds_correct_nfa_via_build_nfa() {
        // Verify that build_nfa uses the trie and produces a working NFA
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

        let nfa = build_nfa_default(&terminals, &needs);

        // Start state should have epsilon transitions:
        // - 1 to trie_root (all terminals share one trie)
        // - 1 to ident fragment
        // - 1 to integer fragment
        // = 3 epsilon transitions
        assert_eq!(
            nfa.states[nfa.start as usize].epsilon.len(),
            3,
            "start state should have 3 epsilon transitions (trie + ident + integer)"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // DAFSA suffix sharing tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_dafsa_no_regression_single_char() {
        // Single-char terminals should be unchanged by DAFSA (no suffixes to share).
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

        let mut dafsa_nfa = Nfa::new();
        let dafsa_root = build_keyword_trie(&mut dafsa_nfa, &terminals);

        let mut prefix_nfa = Nfa::new();
        let prefix_root = build_keyword_trie_prefix_only(&mut prefix_nfa, &terminals);

        // Both should produce same structure for single-char terminals
        assert_eq!(
            dafsa_nfa.states[dafsa_root as usize].transitions.len(),
            prefix_nfa.states[prefix_root as usize].transitions.len(),
            "root transition counts should match"
        );
    }

    #[test]
    fn test_dafsa_no_regression_prefix_sharing() {
        // `=`/`==` prefix sharing should be preserved by DAFSA.
        let terminals = vec![
            TerminalPattern {
                text: "=".to_string(),
                kind: TokenKind::Fixed("=".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "==".to_string(),
                kind: TokenKind::Fixed("==".to_string()),
                is_keyword: false,
            },
        ];

        let mut nfa = Nfa::new();
        let root = build_keyword_trie(&mut nfa, &terminals);

        // Root should have exactly 1 transition ('=')
        assert_eq!(nfa.states[root as usize].transitions.len(), 1);

        // The '=' state should accept single '='
        let eq_state = nfa.states[root as usize].transitions[0].1;
        assert_eq!(nfa.states[eq_state as usize].accept, Some(TokenKind::Fixed("=".to_string())));

        // The '=' state should have a transition to '==' state
        let eq_eq_state = nfa.states[eq_state as usize].transitions[0].1;
        assert_eq!(
            nfa.states[eq_eq_state as usize].accept,
            Some(TokenKind::Fixed("==".to_string()))
        );
    }

    #[test]
    fn test_dafsa_suffix_sharing_non_accepting() {
        // Terminals with same accept token but different prefixes can share suffixes.
        // `ab` → Ident, `cb` → Ident: the 'b'(Ident) leaf nodes can merge,
        // and then the intermediate nodes (both {None, [('b', canonical)]}) can merge too.
        let terminals = vec![
            TerminalPattern {
                text: "ab".to_string(),
                kind: TokenKind::Ident,
                is_keyword: false,
            },
            TerminalPattern {
                text: "cb".to_string(),
                kind: TokenKind::Ident,
                is_keyword: false,
            },
        ];

        let mut dafsa_nfa = Nfa::new();
        let dafsa_root = build_keyword_trie(&mut dafsa_nfa, &terminals);

        let mut prefix_nfa = Nfa::new();
        let prefix_root = build_keyword_trie_prefix_only(&mut prefix_nfa, &terminals);

        // Count reachable states from each root
        let dafsa_reachable = count_reachable_trie_states(&dafsa_nfa, dafsa_root);
        let prefix_reachable = count_reachable_trie_states(&prefix_nfa, prefix_root);

        assert!(
            dafsa_reachable <= prefix_reachable,
            "DAFSA reachable ({}) should be <= prefix-only reachable ({})",
            dafsa_reachable,
            prefix_reachable
        );

        // Specifically: DAFSA should merge 'b' leaves and intermediate states
        // prefix-only: root → a → b(Ident), root → c → b(Ident) = 5 reachable
        // DAFSA: root → a → b(Ident), root → c → (same a) → (same b) = 3 reachable
        assert_eq!(
            dafsa_reachable, 3,
            "DAFSA should have 3 reachable states (root + shared intermediate + shared accept)"
        );
        assert_eq!(
            prefix_reachable, 5,
            "prefix-only should have 5 reachable states (root + a + b_1 + c + b_2)"
        );

        // Both 'a' and 'c' transitions from root should point to the same state
        let targets: Vec<StateId> = dafsa_nfa.states[dafsa_root as usize]
            .transitions
            .iter()
            .map(|(_, t)| *t)
            .collect();
        assert_eq!(targets.len(), 2);
        assert_eq!(
            targets[0], targets[1],
            "both root transitions should point to same merged state"
        );
    }

    #[test]
    fn test_dafsa_no_merge_different_accept() {
        // Terminals with different accept tokens on leaves should NOT merge.
        // `ab` → Fixed("ab"), `cb` → Fixed("cb"): different accept tokens
        let terminals = vec![
            TerminalPattern {
                text: "ab".to_string(),
                kind: TokenKind::Fixed("ab".to_string()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "cb".to_string(),
                kind: TokenKind::Fixed("cb".to_string()),
                is_keyword: false,
            },
        ];

        let mut dafsa_nfa = Nfa::new();
        let dafsa_root = build_keyword_trie(&mut dafsa_nfa, &terminals);

        let mut prefix_nfa = Nfa::new();
        let prefix_root = build_keyword_trie_prefix_only(&mut prefix_nfa, &terminals);

        // No merging should happen — same reachable count
        let dafsa_reachable = count_reachable_trie_states(&dafsa_nfa, dafsa_root);
        let prefix_reachable = count_reachable_trie_states(&prefix_nfa, prefix_root);

        assert_eq!(
            dafsa_reachable, prefix_reachable,
            "different accept tokens should prevent DAFSA merging"
        );
    }

    #[test]
    fn test_dafsa_produces_same_dfa() {
        // End-to-end: both trie variants should produce functionally equivalent DFAs.
        use crate::automata::{
            minimize::minimize_dfa, partition::compute_equivalence_classes,
            subset::subset_construction,
        };

        let terminal_specs = vec![
            ("+", TokenKind::Fixed("+".to_string())),
            ("++", TokenKind::Fixed("++".to_string())),
            ("-", TokenKind::Fixed("-".to_string())),
            ("->", TokenKind::Fixed("->".to_string())),
            ("=", TokenKind::Fixed("=".to_string())),
            ("==", TokenKind::Fixed("==".to_string())),
            ("!=", TokenKind::Fixed("!=".to_string())),
            ("(", TokenKind::Fixed("(".to_string())),
            (")", TokenKind::Fixed(")".to_string())),
            ("error", TokenKind::Fixed("error".to_string())),
        ];

        let terminals: Vec<TerminalPattern> = terminal_specs
            .iter()
            .map(|(text, kind)| TerminalPattern {
                text: text.to_string(),
                kind: kind.clone(),
                is_keyword: text.chars().all(|c| c.is_alphanumeric()),
            })
            .collect();

        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            ..Default::default()
        };

        // Build with DAFSA (current build_keyword_trie)
        let nfa_dafsa = build_nfa_default(&terminals, &needs);
        let partition_dafsa = compute_equivalence_classes(&nfa_dafsa);
        let dfa_dafsa = minimize_dfa(&subset_construction(&nfa_dafsa, &partition_dafsa));

        // Build with prefix-only trie
        let mut nfa_prefix = Nfa::new();
        let global_start_prefix = nfa_prefix.start;
        let trie_root_prefix = build_keyword_trie_prefix_only(&mut nfa_prefix, &terminals);
        nfa_prefix.add_epsilon(global_start_prefix, trie_root_prefix);
        // Add character-class fragments via regex compiler
        let patterns = crate::LiteralPatterns::default();
        if needs.ident {
            let frag = regex::compile_regex(&patterns.ident, &mut nfa_prefix, TokenKind::Ident)
                .expect("ident pattern should be valid");
            nfa_prefix.add_epsilon(global_start_prefix, frag.start);
        }
        if needs.integer {
            let frag = regex::compile_regex(&patterns.integer, &mut nfa_prefix, TokenKind::Integer)
                .expect("integer pattern should be valid");
            nfa_prefix.add_epsilon(global_start_prefix, frag.start);
        }
        let partition_prefix = compute_equivalence_classes(&nfa_prefix);
        let dfa_prefix = minimize_dfa(&subset_construction(&nfa_prefix, &partition_prefix));

        // Verify DFA equivalence by testing all terminals + identifiers + integers
        let test_inputs = vec![
            "+", "++", "-", "->", "=", "==", "!=", "(", ")", "error", "x", "foo", "bar123", "42",
            "0", "999",
        ];

        for input in test_inputs {
            let result_dafsa = lex_through_dfa(&dfa_dafsa, &partition_dafsa, input);
            let result_prefix = lex_through_dfa(&dfa_prefix, &partition_prefix, input);
            assert_eq!(
                result_dafsa, result_prefix,
                "DFA mismatch for input {:?}: DAFSA={:?} vs prefix-only={:?}",
                input, result_dafsa, result_prefix
            );
        }
    }

    #[test]
    fn test_dafsa_state_count_report() {
        // Diagnostic: print before/after NFA state counts for visibility
        let terminals: Vec<TerminalPattern> = [
            "+", "++", "-", "->", "=", "==", "!=", "<=", ">=", "(", ")", "{", "}", "[", "]", ",",
            ";", "error", "true", "false", "if", "else", "while", "for",
        ]
        .iter()
        .enumerate()
        .map(|(_, text)| {
            let kind = match *text {
                "true" => TokenKind::True,
                "false" => TokenKind::False,
                _ => TokenKind::Fixed(text.to_string()),
            };
            TerminalPattern {
                text: text.to_string(),
                kind,
                is_keyword: text.chars().all(|c| c.is_alphanumeric()),
            }
        })
        .collect();

        let mut dafsa_nfa = Nfa::new();
        let dafsa_root = build_keyword_trie(&mut dafsa_nfa, &terminals);
        let dafsa_total = dafsa_nfa.states.len();
        let dafsa_reachable = count_reachable_trie_states(&dafsa_nfa, dafsa_root);

        let mut prefix_nfa = Nfa::new();
        let prefix_root = build_keyword_trie_prefix_only(&mut prefix_nfa, &terminals);
        let prefix_total = prefix_nfa.states.len();
        let prefix_reachable = count_reachable_trie_states(&prefix_nfa, prefix_root);

        eprintln!("DAFSA state count report:");
        eprintln!(
            "  Prefix-only: {} total, {} reachable from trie root",
            prefix_total, prefix_reachable
        );
        eprintln!(
            "  DAFSA:       {} total ({} dead), {} reachable from trie root",
            dafsa_total,
            dafsa_total - dafsa_reachable - 1, // -1 for nfa start
            dafsa_reachable
        );
        eprintln!(
            "  Reduction:   {} states saved ({:.1}%)",
            prefix_reachable.saturating_sub(dafsa_reachable),
            if prefix_reachable > 0 {
                (prefix_reachable.saturating_sub(dafsa_reachable) as f64 / prefix_reachable as f64)
                    * 100.0
            } else {
                0.0
            }
        );

        // DAFSA should never produce MORE reachable states
        assert!(
            dafsa_reachable <= prefix_reachable,
            "DAFSA ({}) should not produce more reachable states than prefix-only ({})",
            dafsa_reachable,
            prefix_reachable
        );
    }

    /// Count reachable states from a trie root via BFS (only follows Single-byte transitions).
    fn count_reachable_trie_states(nfa: &Nfa, root: StateId) -> usize {
        let mut visited = vec![false; nfa.states.len()];
        let mut queue = vec![root];
        visited[root as usize] = true;
        let mut count = 0;
        while let Some(state) = queue.pop() {
            count += 1;
            for (class, target) in &nfa.states[state as usize].transitions {
                if let CharClass::Single(_) = class {
                    if !visited[*target as usize] {
                        visited[*target as usize] = true;
                        queue.push(*target);
                    }
                }
            }
        }
        count
    }

    /// Simulate lexing through a DFA, returning the accept token (if any).
    fn lex_through_dfa(
        dfa: &crate::automata::Dfa,
        partition: &crate::automata::partition::AlphabetPartition,
        input: &str,
    ) -> Option<TokenKind> {
        let mut state = dfa.start;
        for &byte in input.as_bytes() {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            if state == crate::automata::DEAD_STATE {
                return None;
            }
        }
        dfa.states[state as usize].accept.clone()
    }

    // ══════════════════════════════════════════════════════════════════════
    // Tropical weight tests — verify weights propagate correctly through
    // NFA → DFA → minimize pipeline
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_nfa_state_weight_default() {
        let state = NfaState::new();
        assert!(state.weight.is_infinite(), "non-accepting state should have infinite weight");
        assert!(state.accept.is_none());
    }

    #[test]
    fn test_nfa_state_weight_from_priority() {
        // Fixed terminal: priority 10 → weight 0.0 (best)
        let fixed = NfaState::accepting(TokenKind::Fixed("+".to_string()));
        assert_eq!(fixed.weight.value(), 0.0, "Fixed(+) should have weight 0.0");

        // Ident: priority 1 → weight 9.0
        let ident = NfaState::accepting(TokenKind::Ident);
        assert_eq!(ident.weight.value(), 9.0, "Ident should have weight 9.0");

        // Integer: priority 2 → weight 8.0
        let integer = NfaState::accepting(TokenKind::Integer);
        assert_eq!(integer.weight.value(), 8.0, "Integer should have weight 8.0");

        // Float: priority 3 → weight 7.0
        let float = NfaState::accepting(TokenKind::Float);
        assert_eq!(float.weight.value(), 7.0, "Float should have weight 7.0");

        // Boolean: priority 10 → weight 0.0
        let boolean = NfaState::accepting(TokenKind::True);
        assert_eq!(boolean.weight.value(), 0.0, "True should have weight 0.0");
    }

    #[test]
    fn test_weight_propagation_through_pipeline() {
        use crate::automata::{
            minimize::minimize_dfa, partition::compute_equivalence_classes,
            subset::subset_construction,
        };

        let terminals = vec![TerminalPattern {
            text: "error".to_string(),
            kind: TokenKind::Fixed("error".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };

        let nfa = build_nfa_default(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = minimize_dfa(&subset_construction(&nfa, &partition));

        // Simulate lexing "error" — should get Fixed("error") with weight 0.0
        let mut state = dfa.start;
        for &byte in b"error" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, crate::automata::DEAD_STATE);
        }
        assert_eq!(dfa.states[state as usize].accept, Some(TokenKind::Fixed("error".to_string())));
        assert_eq!(
            dfa.states[state as usize].weight.value(),
            0.0,
            "keyword 'error' (priority 10) should have weight 0.0"
        );

        // Simulate lexing "foo" — should get Ident with weight 9.0
        let mut state = dfa.start;
        for &byte in b"foo" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, crate::automata::DEAD_STATE);
        }
        assert_eq!(dfa.states[state as usize].accept, Some(TokenKind::Ident),);
        assert_eq!(
            dfa.states[state as usize].weight.value(),
            9.0,
            "identifier 'foo' (priority 1) should have weight 9.0"
        );

        // Simulate lexing "42" — should get Integer with weight 8.0
        let mut state = dfa.start;
        for &byte in b"42" {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            assert_ne!(state, crate::automata::DEAD_STATE);
        }
        assert_eq!(dfa.states[state as usize].accept, Some(TokenKind::Integer),);
        assert_eq!(
            dfa.states[state as usize].weight.value(),
            8.0,
            "integer '42' (priority 2) should have weight 8.0"
        );
    }

    #[test]
    fn test_set_or_upgrade_accept_updates_weight() {
        let mut nfa = Nfa::new();
        let state = nfa.add_state(NfaState::accepting(TokenKind::Ident)); // priority 1, weight 9.0

        assert_eq!(nfa.states[state as usize].weight.value(), 9.0);

        // Upgrade to Fixed (priority 10, weight 0.0)
        set_or_upgrade_accept(&mut nfa, state, &TokenKind::Fixed("kw".to_string()));
        assert_eq!(nfa.states[state as usize].weight.value(), 0.0);
        assert_eq!(nfa.states[state as usize].accept, Some(TokenKind::Fixed("kw".to_string())));
    }

    #[test]
    fn test_set_or_upgrade_accept_no_downgrade_weight() {
        let mut nfa = Nfa::new();
        let state = nfa.add_state(NfaState::accepting(TokenKind::Fixed("kw".to_string()))); // priority 10, weight 0.0

        assert_eq!(nfa.states[state as usize].weight.value(), 0.0);

        // Attempt to downgrade to Ident (priority 1, weight 9.0) — should NOT change
        set_or_upgrade_accept(&mut nfa, state, &TokenKind::Ident);
        assert_eq!(nfa.states[state as usize].weight.value(), 0.0);
        assert_eq!(nfa.states[state as usize].accept, Some(TokenKind::Fixed("kw".to_string())));
    }

    #[test]
    fn test_weight_preserved_through_minimization() {
        use crate::automata::{
            minimize::minimize_dfa, partition::compute_equivalence_classes,
            subset::subset_construction,
        };

        // Two categories of accepting states: Fixed (weight 0.0) and Ident (weight 9.0)
        // After minimization, these must remain distinct.
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
        let dfa = minimize_dfa(&subset_construction(&nfa, &partition));

        // Verify: all accepting states have correct weights
        for state in &dfa.states {
            if let Some(ref kind) = state.accept {
                let expected_weight = TropicalWeight::from_priority(kind.priority());
                assert_eq!(
                    state.weight, expected_weight,
                    "state accepting {:?} has weight {:?} but expected {:?}",
                    kind, state.weight, expected_weight
                );
            } else {
                assert!(
                    state.weight.is_infinite(),
                    "non-accepting state should have infinite weight, got {:?}",
                    state.weight
                );
            }
        }
    }
}
