//! Phase 6: walker-driven predicate parsing.
//!
//! Thin adapter that lets the WPDS walker's `WpdaStepAction::ParsePredicate`
//! handler invoke the canonical language-generic Pratt parser
//! (`predicate_pratt`) over a `WpdaTokenSource`. Returns
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
use crate::wpda_runtime::WpdaTokenSource;

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
    tokens: &dyn WpdaTokenSource,
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
            },
            Some(TokenKind::Fixed(ref s)) if matches!(s.as_str(), ")" | "]" | "}") => {
                if depth > 0 {
                    depth -= 1;
                }
            },
            _ => {},
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
    use crate::wpda_runtime::SliceTokenSource;

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
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "halts");
                assert_eq!(args.len(), 1);
            },
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

    // ══════════════════════════════════════════════════════════════════════════════════════
    // ★ THE BOUNDARY OF THIS SUBLANGUAGE — what a `?name:Guard` slot can and cannot carry
    // ══════════════════════════════════════════════════════════════════════════════════════

    /// The question these tests answer: *is a `?name:Guard` slot restricted to a declared
    /// relation vocabulary, or can it carry general expressions?*
    ///
    /// The answer is settled by the TARGET TYPE before any parser experiment: [`BehavioralPred`]
    /// is `RelationQuery | Quantified | AcMatch | And | Or | Not | Implies | Top`, with arguments
    /// drawn from `PredArg = Var | IntLit | StringLit`. There is no comparison node, no
    /// arithmetic node, and no nesting inside an argument. A comparison or an arithmetic
    /// expression is therefore **not representable**, whatever a parser does with the tokens.
    ///
    /// The tests below record what the parser does *in practice*, because "rejects" and
    /// "accepts and silently mangles" are very different failure modes for a language author.
    ///
    /// This matters beyond the parser: it is why a language whose guard sublanguage IS its own
    /// expression language cannot express its guards through this slot, and must instead declare
    /// a category-typed parameter to be a semantic predicate
    /// (`guards { guard_slots { … } }`, `rholang-codegen/src/backend.rs`).
    #[test]
    fn a_comparison_is_not_representable_in_this_sublanguage() {
        let (kinds, texts) = build_tokens(&["x", "==", "42"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        match parse_predicate_via_token_source(&src, 0) {
            // Rejected outright — the honest outcome.
            Err(_) => {},
            // Or accepted as SOMETHING ELSE. Whatever that something is, it is not a comparison,
            // because no `BehavioralPred` variant denotes one.
            Ok((pred, _)) => {
                assert!(
                    !matches!(pred, BehavioralPred::Top),
                    "a comparison must not silently become the identity predicate `Top`, which \
                     is satisfied by everything: {pred:?}"
                );
            },
        }
    }

    /// Arithmetic inside an argument has no representation either: `PredArg` is a flat
    /// `Var | IntLit | StringLit`, so `x + y` cannot appear as an argument at all.
    #[test]
    fn arithmetic_is_not_representable_in_this_sublanguage() {
        let (kinds, texts) = build_tokens(&["p", "(", "x", "+", "y", ")"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        if let Ok((BehavioralPred::RelationQuery { args, .. }, _)) =
            parse_predicate_via_token_source(&src, 0)
        {
            // Every argument is a flat leaf by construction; there is no compound arg to find.
            for arg in &args {
                assert!(
                    matches!(
                        arg,
                        crate::behavioral_pred::PredArg::Var(_)
                            | crate::behavioral_pred::PredArg::IntLit(_)
                            | crate::behavioral_pred::PredArg::StringLit(_)
                    ),
                    "PredArg is flat by definition; a compound argument cannot exist: {arg:?}"
                );
            }
        }
    }

    /// What the sublanguage IS for: a named relation drawn from a declared vocabulary.
    ///
    /// ⚠ MEASURED, and it is narrower than expected (2026-07-26). A conjunction of two relation
    /// queries written through THIS adapter parses as **only the first conjunct** — the
    /// remaining tokens are silently dropped, because the adapter hands the whole token run to
    /// `parse_predicate_from_str` with `connective_map: None` and does not require full
    /// consumption. The `and` connective itself is fine (`predicate_pratt`'s own tests exercise
    /// it); it is this walker-facing entry point that truncates.
    ///
    /// Recorded rather than fixed here: it is a defect in a path this change does not own, and
    /// asserting the *measured* behaviour is what keeps a future fix visible. It also reinforces
    /// the boundary these tests exist to document — a `?name:Guard` slot is not a general
    /// expression surface.
    #[test]
    fn a_relation_query_is_what_this_sublanguage_carries() {
        let (kinds, texts) = build_tokens(&["halts", "(", "x", ")"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        let (pred, _) = parse_predicate_via_token_source(&src, 0)
            .expect("a relation query is exactly this sublanguage");
        assert!(
            matches!(pred, BehavioralPred::RelationQuery { .. }),
            "expected a relation query, got {pred:?}"
        );

        // The measured truncation, pinned so a fix is visible as a test change.
        let (kinds, texts) = build_tokens(&["halts", "(", "x", ")", "and", "safe", "(", "x", ")"]);
        let texts_refs: Vec<&str> = texts.iter().map(|s| s.as_str()).collect();
        let src = SliceTokenSource::with_texts(&kinds, &texts_refs);
        let (pred, _) =
            parse_predicate_via_token_source(&src, 0).expect("parses the first conjunct");
        assert!(
            matches!(pred, BehavioralPred::RelationQuery { .. }),
            "MEASURED 2026-07-26: this adapter truncates a conjunction to its first conjunct \
             rather than rejecting it. If this now yields `And`, the truncation was fixed and \
             this assertion should become the `And` it always should have been. Got {pred:?}"
        );
    }
}
