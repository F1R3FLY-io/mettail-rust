//! Original generated prefix evidence predicates from kind_dispatch.rs at f905c1e3.
//!
//! Category routing, trigger/delimiter slices, and codegen eligibility gates remain
//! at the caller. These bodies preserve the original primary-edge scan, delimiter
//! and trigger precedence, early returns, and same-position termination check.
//! Projection membership is observed only after the original Ident token test.
//! TransitionBodyRelocation.v requires equality of the complete observations;
//! these helpers neither cache nor replay token-source observations.

use crate::wpda_runtime::WpdaTokenSource;

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
