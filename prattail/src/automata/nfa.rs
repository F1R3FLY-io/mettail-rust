//! NFA construction from terminal patterns.
//!
//! Fixed string terminals (keywords, operators) are built as a prefix-sharing
//! trie directly in the NFA — common prefixes like `=`/`==` or `true`/`try`
//! share NFA states, reducing state count and downstream DFA size.
//!
//! Character-class patterns (identifiers, integers, floats, strings) remain
//! Thompson fragments since they use ranges rather than single bytes.

use super::{CharClass, Nfa, NfaFragment, NfaState, StateId, TerminalPattern, TokenKind};

/// Build a complete NFA from a set of terminal patterns plus built-in
/// character-class patterns (identifiers, integers, floats, strings).
///
/// Fixed string terminals are built as a prefix-sharing trie: common prefixes
/// (e.g., `=`/`==`, `true`/`try`/`type`) share NFA states, reducing the total
/// state count compared to per-terminal Thompson chains.
///
/// Character-class patterns (identifiers, integers, floats, strings) remain
/// independent Thompson fragments since they use ranges, not single bytes.
pub fn build_nfa(terminals: &[TerminalPattern], needs: &BuiltinNeeds) -> Nfa {
    let mut nfa = Nfa::new();
    let global_start = nfa.start;

    // Build keyword/operator trie (prefix-sharing)
    if !terminals.is_empty() {
        let trie_root = build_keyword_trie(&mut nfa, terminals);
        nfa.add_epsilon(global_start, trie_root);
    }

    // Build built-in character class patterns (Thompson fragments)
    let mut fragments: Vec<NfaFragment> = Vec::new();
    if needs.ident {
        fragments.push(build_ident_fragment(&mut nfa));
    }
    if needs.integer {
        fragments.push(build_integer_fragment(&mut nfa));
    }
    if needs.float {
        fragments.push(build_float_fragment(&mut nfa));
    }
    if needs.string_lit {
        fragments.push(build_string_lit_fragment(&mut nfa));
    }

    // Combine character-class fragments via alternation
    for frag in &fragments {
        nfa.add_epsilon(global_start, frag.start);
    }

    nfa
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

/// Build a prefix-sharing trie for all fixed string terminals directly in the NFA.
///
/// Common prefixes share NFA states by construction. For example, `=` and `==`:
/// ```text
///   trie_root -'='-> s1(accept:Eq) -'='-> s2(accept:EqEq)
/// ```
/// And `true`/`try`/`type`:
/// ```text
///   trie_root -'t'-> s1 -'r'-> s2 -'u'-> s3 -'e'-> s4(accept:True)
///                              s2 -'y'-> s5(accept:KwTry)
///                    s1 -'y'-> s6 -'p'-> s7 -'e'-> s8(accept:KwType)
/// ```
///
/// Priority resolution: when a terminal ends at an existing state that already
/// has an accept token, the higher-priority token wins (e.g., Fixed beats Ident).
///
/// Returns the trie root state ID. The caller should add an epsilon transition
/// from the global NFA start to this root.
fn build_keyword_trie(nfa: &mut Nfa, terminals: &[TerminalPattern]) -> StateId {
    let trie_root = nfa.add_state(NfaState::new());

    for terminal in terminals {
        assert!(
            !terminal.text.is_empty(),
            "terminal string must not be empty"
        );

        let mut current = trie_root;
        let bytes = terminal.text.as_bytes();

        for (i, &byte) in bytes.iter().enumerate() {
            let is_last = i == bytes.len() - 1;

            // Check if a transition for this byte already exists from current state
            let existing = nfa.states[current as usize]
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
                });

            if let Some(target) = existing {
                current = target;
                if is_last {
                    // Terminal ends at existing state — set or upgrade accept
                    let state = &mut nfa.states[current as usize];
                    match &state.accept {
                        None => {
                            state.accept = Some(terminal.kind.clone());
                        }
                        Some(existing_kind) => {
                            if terminal.kind.priority() > existing_kind.priority() {
                                state.accept = Some(terminal.kind.clone());
                            }
                        }
                    }
                }
            } else {
                // No existing transition — create new state
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
            return NfaFragment {
                start,
                accept,
            };
        } else {
            // Intermediate character: transition to next state
            let next = nfa.add_state(NfaState::new());
            nfa.add_transition(current, next, CharClass::Single(byte));
            current = next;
        }
    }

    unreachable!("terminal string must not be empty")
}

/// Build an NFA fragment for identifiers: `[a-zA-Z_][a-zA-Z0-9_]*`
///
/// ```text
///   start -[a-zA-Z_]-> s1(accept:Ident) -[a-zA-Z0-9_]-> s1(accept:Ident)
/// ```
fn build_ident_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::Ident));

    // First character: letter or underscore
    nfa.add_transition(start, accept, CharClass::Range(b'a', b'z'));
    nfa.add_transition(start, accept, CharClass::Range(b'A', b'Z'));
    nfa.add_transition(start, accept, CharClass::Single(b'_'));

    // Subsequent characters: letter, digit, or underscore (self-loop)
    nfa.add_transition(accept, accept, CharClass::Range(b'a', b'z'));
    nfa.add_transition(accept, accept, CharClass::Range(b'A', b'Z'));
    nfa.add_transition(accept, accept, CharClass::Range(b'0', b'9'));
    nfa.add_transition(accept, accept, CharClass::Single(b'_'));

    NfaFragment { start, accept }
}

/// Build an NFA fragment for integer literals: `[0-9]+`
///
/// ```text
///   start -[0-9]-> s1(accept:Integer) -[0-9]-> s1(accept:Integer)
/// ```
fn build_integer_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::Integer));

    // One or more digits
    nfa.add_transition(start, accept, CharClass::Range(b'0', b'9'));
    nfa.add_transition(accept, accept, CharClass::Range(b'0', b'9'));

    NfaFragment { start, accept }
}

/// Build an NFA fragment for float literals: `[0-9]+\.[0-9]+`
///
/// ```text
///   start -[0-9]-> s1 -[0-9]-> s1 -'.'-> s2 -[0-9]-> s3(accept:Float) -[0-9]-> s3
/// ```
fn build_float_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let integer_part = nfa.add_state(NfaState::new());
    let dot = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::Float));

    // Integer part: one or more digits
    nfa.add_transition(start, integer_part, CharClass::Range(b'0', b'9'));
    nfa.add_transition(integer_part, integer_part, CharClass::Range(b'0', b'9'));

    // Dot
    nfa.add_transition(integer_part, dot, CharClass::Single(b'.'));

    // Fractional part: one or more digits
    nfa.add_transition(dot, accept, CharClass::Range(b'0', b'9'));
    nfa.add_transition(accept, accept, CharClass::Range(b'0', b'9'));

    NfaFragment { start, accept }
}

/// Build an NFA fragment for string literals: `"[^"]*"`
///
/// ```text
///   start -'"'-> s1 -[^"]-> s1 -'"'-> accept(StringLit)
/// ```
fn build_string_lit_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let inside = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::StringLit));

    // Opening quote
    nfa.add_transition(start, inside, CharClass::Single(b'"'));

    // Any character except quote (loop)
    // We model this as explicit ranges that exclude the quote character
    for byte in 0u8..b'"' {
        nfa.add_transition(inside, inside, CharClass::Single(byte));
    }
    for byte in (b'"' + 1)..=127 {
        nfa.add_transition(inside, inside, CharClass::Single(byte));
    }

    // Closing quote
    nfa.add_transition(inside, accept, CharClass::Single(b'"'));

    NfaFragment { start, accept }
}

/// Compute the epsilon closure of a set of NFA states.
///
/// Returns all states reachable from `states` via zero or more epsilon transitions.
pub fn epsilon_closure(nfa: &Nfa, states: &[StateId]) -> Vec<StateId> {
    let mut closure: Vec<StateId> = states.to_vec();
    let mut stack: Vec<StateId> = states.to_vec();
    let mut visited = vec![false; nfa.states.len()];

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
    fn test_build_ident_fragment() {
        let mut nfa = Nfa::new();
        let frag = build_ident_fragment(&mut nfa);

        // original start (0) + fragment start + accept = 3
        assert_eq!(nfa.states.len(), 3);
        assert_eq!(
            nfa.states[frag.accept as usize].accept,
            Some(TokenKind::Ident)
        );
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

        let nfa = build_nfa(&terminals, &needs);
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
        assert!(
            trie_states <= 11,
            "trie should have at most 11 states (got {})",
            trie_states
        );

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

        let nfa = build_nfa(&terminals, &needs);

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
}
