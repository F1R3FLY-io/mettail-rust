//! Phase 6: walker-driven predicate parsing.
//!
//! Thin adapter that lets the WPDS walker's `WpdsStepAction::ParsePredicate`
//! handler invoke the canonical language-generic Pratt parser
//! (`predicate_pratt`) over a `WpdsTokenSource`. Returns
//! `mettail_prattail::behavioral_pred::BehavioralPred` directly — no
//! intermediate AST conversion (the prior `PrattailPred` duplicate was
//! deleted during the F.0-sibling break, 2026-04-26).
//!
//! The walker's terminator policy: stop at the first `Fixed` token in
//! a default-terminator set (`)`, `}`, `,`, `;`, `]`). Per-grammar
//! terminator sets can be threaded later via `parse_predicate` directly.

use crate::automata::TokenKind;
use crate::behavioral_pred::BehavioralPred;
use crate::parser::predicate_pratt::{
    parse_predicate_from_str, PredicateParserConfig, TerminatorToken,
};
use crate::wpds_runtime::WpdsTokenSource;

/// Phase 6: parse a predicate from `tokens` starting at `start`. Returns
/// `(predicate, new_pos)` on success.
///
/// Walks the token stream from `start` collecting tokens into a string
/// representation (whitespace-separated `peek_text` values), invokes the
/// canonical Pratt parser, and returns the parsed `BehavioralPred` plus
/// the new position (advanced past the consumed predicate tokens).
///
/// Stops at the first default-terminator token at depth 0
/// (`)`, `}`, `,`, `;`, `]`).
pub fn parse_predicate_via_token_source(
    tokens: &dyn WpdsTokenSource,
    start: usize,
) -> Result<(BehavioralPred, usize), String> {
    // Collect tokens up to the first default terminator (at depth 0)
    // and build a whitespace-separated source string for the canonical
    // parser. Track depth to avoid stopping at terminator tokens nested
    // inside parentheses/brackets.
    let mut depth: i32 = 0;
    let mut pieces: Vec<String> = Vec::new();
    let mut pos = start;
    let total = tokens.len();
    while pos < total {
        let kind = tokens.peek_kind(pos);
        let text = tokens.peek_text(pos).unwrap_or("").to_string();
        if depth == 0 && is_default_terminator(kind.as_ref(), &text) {
            break;
        }
        match kind {
            Some(TokenKind::Fixed(ref s)) if matches!(s.as_str(), "(" | "[" | "{") => {
                depth += 1;
            }
            Some(TokenKind::Fixed(ref s)) if matches!(s.as_str(), ")" | "]" | "}") => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            _ => {}
        }
        pieces.push(text);
        pos += 1;
    }
    let source = pieces.join(" ");
    let cfg = PredicateParserConfig {
        connective_map: None,
        terminators: vec![TerminatorToken::Eof],
        builtin_predicates: Vec::new(),
    };
    let pred = parse_predicate_from_str(&source, cfg)
        .map_err(|e| format!("predicate parse error: {:?}", e))?;
    Ok((pred, pos))
}

fn is_default_terminator(kind: Option<&TokenKind>, text: &str) -> bool {
    match kind {
        Some(TokenKind::Fixed(s)) => matches!(s.as_str(), ")" | "}" | "]" | "," | ";"),
        _ => matches!(text, ")" | "}" | "]" | "," | ";"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wpds_runtime::SliceTokenSource;

    fn build_tokens(words: &[&str]) -> (Vec<TokenKind>, Vec<String>) {
        let kinds: Vec<TokenKind> = words
            .iter()
            .map(|w| {
                if w.chars().all(|c| c.is_ascii_alphabetic()) {
                    TokenKind::Ident
                } else if w.parse::<i64>().is_ok() {
                    TokenKind::IntegerLit("Int".to_string())
                } else {
                    TokenKind::Fixed(w.to_string())
                }
            })
            .collect();
        let texts: Vec<String> = words.iter().map(|s| s.to_string()).collect();
        (kinds, texts)
    }

    #[test]
    fn parses_relation_query_via_token_source() {
        let (kinds, texts) = build_tokens(&["halts", "(", "x", ")"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        let (pred, new_pos) =
            parse_predicate_via_token_source(&src, 0).expect("parse should succeed");
        match pred {
            BehavioralPred::RelationQuery {
                relation_name,
                args,
                ..
            } => {
                assert_eq!(relation_name, "halts");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected RelationQuery"),
        }
        assert_eq!(new_pos, 4);
    }

    #[test]
    fn stops_at_terminator() {
        // After `halts ( x )` we have a terminator `,`. New pos points at `,`.
        let (kinds, texts) = build_tokens(&["halts", "(", "x", ")", ",", "more"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        let (_pred, new_pos) =
            parse_predicate_via_token_source(&src, 0).expect("parse should succeed");
        assert_eq!(new_pos, 4, "should stop at the comma at index 4");
    }
}
