//! Original generated prefix evidence predicates from kind_dispatch.rs at f905c1e3.
//!
//! Category routing, trigger/delimiter slices, and codegen eligibility gates remain
//! at the caller. These bodies preserve the original primary-edge scan, delimiter
//! and trigger precedence, early returns, and same-position termination check.
//! Projection membership is observed only after the original Ident token test.
//! TransitionBodyRelocation.v requires equality of the complete observations;
//! these helpers neither cache nor replay token-source observations.

use crate::wpda_runtime::WpdaTokenSource;

/// A negative-only gate for a grammar-certified one-token source atom.
/// `alt_idx` identifies the selected first edge: lattice alternatives can
/// have different successor nodes. An unknown edge or successor keeps the
/// delegate. At a known successor, every lexical interpretation is checked.
pub fn crosscat_one_token_successor_may_continue(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    alt_idx: usize,
    target_operators: &[&str],
    source_extensions: &[&str],
) -> bool {
    let Some(next) = tokens.next_pos(pos, alt_idx) else {
        return true;
    };
    if next == pos {
        return true;
    }
    let Some(primary) = tokens.peek_kind(next) else {
        return true;
    };
    let may_continue = |kind: &crate::automata::TokenKind| match kind {
        crate::automata::TokenKind::Fixed(text) => {
            target_operators.contains(&text.as_str()) || source_extensions.contains(&text.as_str())
        },
        _ => false,
    };
    may_continue(&primary)
        || tokens
            .peek_alternatives(next)
            .iter()
            .any(|alternative| may_continue(&alternative.kind))
}

pub fn prefix_crosscat_lhs_trigger_ahead(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    triggers: &[&str],
) -> bool {
    if triggers.is_empty() {
        return false;
    }
    let mut next = tokens.next_pos(pos, 0);
    while let Some(i) = next {
        if let Some(crate::automata::TokenKind::Fixed(t)) = tokens.peek_kind(i) {
            if triggers.iter().any(|trig| t == *trig) {
                return true;
            }
        }
        let following = tokens.next_pos(i, 0);
        if following == Some(i) {
            break;
        }
        next = following;
    }
    false
}

#[allow(non_snake_case)]
pub fn prefix_crosscat_lhs_trigger_ahead_scoped(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    triggers: &[&str],
    __OPENS: &[&str],
    __CLOSES: &[&str],
    __ROW_SEPS: &[&str],
) -> bool {
    if triggers.is_empty() {
        return false;
    }
    // GEN-1 GAP-2 (2026-06-28): spec-derived delimiter / row-separator
    // tables (emitted from `collect_structural_delimiters` +
    // `collect_sequence_separators` \ cross-cat-triggers), replacing the
    // formerly-hardcoded rholang alphabet. `opens`/`closes` depth-track
    // brackets; a depth-0 `row_seps` entry bounds the row.
    let mut depth: i32 = 0;
    let mut next = tokens.next_pos(pos, 0);
    while let Some(i) = next {
        if let Some(crate::automata::TokenKind::Fixed(t)) = tokens.peek_kind(i) {
            let __t = t.as_str();
            if __OPENS.contains(&__t) {
                depth += 1;
            } else if __CLOSES.contains(&__t) {
                depth -= 1;
                if depth < 0 {
                    // Exited the enclosing bracketed region (for-`)`).
                    return false;
                }
            } else if depth == 0 && __ROW_SEPS.contains(&__t) {
                // Row boundary: a trigger in a LATER row does not bind
                // THIS row's LHS.
                return false;
            } else if depth == 0 && triggers.iter().any(|trig| __t == *trig) {
                return true;
            }
        }
        let following = tokens.next_pos(i, 0);
        if following == Some(i) {
            break;
        }
        next = following;
    }
    false
}

#[allow(non_snake_case)]
pub fn prefix_at_quoted_bind_gate_evidence(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    bind_triggers: &[&str],
    polyadic_stops: &[&str],
    __OPENS: &[&str],
    __CLOSES: &[&str],
    __ROW_SEPS: &[&str],
) -> bool {
    if bind_triggers.is_empty() {
        return false;
    }
    let mut depth: i32 = 0;
    let mut next = tokens.next_pos(pos, 0);
    while let Some(i) = next {
        if let Some(crate::automata::TokenKind::Fixed(t)) = tokens.peek_kind(i) {
            let __t = t.as_str();
            if __OPENS.contains(&__t) {
                depth += 1;
            } else if __CLOSES.contains(&__t) {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            } else if depth == 0 && __ROW_SEPS.contains(&__t) {
                return false;
            } else if depth == 0 && bind_triggers.iter().any(|trig| __t == *trig) {
                // First depth-0 whole-source trigger is a bind
                // trigger with a sigil sibling ⇒ over-generation ⇒
                // SUPPRESS.
                return true;
            } else if depth == 0 && polyadic_stops.iter().any(|stop| __t == *stop) {
                // First depth-0 whole-source trigger has NO sigil
                // sibling (polyadic) ⇒ legitimate ⇒ KEEP.
                return false;
            }
        }
        let following = tokens.next_pos(i, 0);
        if following == Some(i) {
            break;
        }
        next = following;
    }
    false
}

pub fn crosscat_proj_lex_compatible(
    source_src: u16,
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    membership: impl FnOnce(u16) -> bool,
) -> bool {
    // Only `Ident` peeks can be refuted; anything else is
    // lex-compatible by fail-open.
    if !matches!(tokens.peek_kind(pos), Some(crate::automata::TokenKind::Ident)) {
        return true;
    }
    // Peek is Ident: refute iff the source is Ident-var-only.
    !(membership(source_src))
}

#[cfg(test)]
mod certified_crosscat_tests {
    use super::*;
    use crate::automata::{semiring::TropicalWeight, TokenKind};
    use crate::lexer_types::LexAlternative;
    use crate::wpda_runtime::SliceTokenSource;
    use proptest::prelude::*;

    struct AlternativeSuccessor {
        kinds: Vec<TokenKind>,
        successor_alternatives: Vec<LexAlternative>,
    }

    impl WpdaTokenSource for AlternativeSuccessor {
        fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
            self.kinds.get(pos).cloned()
        }

        fn peek_text(&self, _pos: usize) -> Option<&str> {
            None
        }

        fn len(&self) -> usize {
            self.kinds.len()
        }

        fn next_pos(&self, pos: usize, alt_idx: usize) -> Option<usize> {
            match (pos, alt_idx) {
                (0, 0) => Some(1),
                (0, 1) => Some(2),
                _ => (pos < self.len()).then_some(pos + 1),
            }
        }

        fn peek_alternatives(&self, pos: usize) -> &[LexAlternative] {
            if pos == 1 {
                &self.successor_alternatives
            } else {
                &[]
            }
        }
    }

    #[test]
    fn distant_target_operator_does_not_keep_one_token_delegate() {
        let kinds = [
            TokenKind::Ident,
            TokenKind::Fixed("unrelated".into()),
            TokenKind::Fixed("::".into()),
        ];
        let tokens = SliceTokenSource::new(&kinds);
        assert!(!crosscat_one_token_successor_may_continue(
            &tokens,
            0,
            0,
            &["::"],
            &["-o", "(*)"],
        ));
    }

    #[test]
    fn target_or_source_extension_keeps_delegate() {
        for successor in ["::", "-o", "(*)"] {
            let kinds = [TokenKind::Ident, TokenKind::Fixed(successor.into())];
            let tokens = SliceTokenSource::new(&kinds);
            assert!(crosscat_one_token_successor_may_continue(
                &tokens,
                0,
                0,
                &["::"],
                &["-o", "(*)"],
            ));
        }
    }

    #[test]
    fn selected_lattice_edge_and_successor_alternatives_are_respected() {
        let tokens = AlternativeSuccessor {
            kinds: vec![
                TokenKind::Ident,
                TokenKind::Fixed("unrelated".into()),
                TokenKind::Fixed("::".into()),
            ],
            successor_alternatives: vec![LexAlternative {
                kind: TokenKind::Fixed("-o".into()),
                text: "-o".into(),
                end_byte: 2,
                weight: TropicalWeight::from_priority(0),
            }],
        };
        assert!(crosscat_one_token_successor_may_continue(&tokens, 0, 0, &["::"], &["-o"],));
        assert!(crosscat_one_token_successor_may_continue(&tokens, 0, 1, &["::"], &["-o"],));
        assert!(!crosscat_one_token_successor_may_continue(&tokens, 0, 0, &["::"], &[],));
    }

    proptest! {
        #[test]
        fn one_token_gate_depends_only_on_immediate_successor(
            successor in 0u8..3,
            distant_target in any::<bool>(),
        ) {
            let next = match successor {
                0 => "::",
                1 => "-o",
                _ => "unrelated",
            };
            let mut kinds = vec![TokenKind::Ident, TokenKind::Fixed(next.into())];
            if distant_target {
                kinds.push(TokenKind::Fixed("::".into()));
            }
            let tokens = SliceTokenSource::new(&kinds);
            prop_assert_eq!(
                crosscat_one_token_successor_may_continue(
                    &tokens, 0, 0, &["::"], &["-o"],
                ),
                successor != 2,
            );
        }
    }
}
