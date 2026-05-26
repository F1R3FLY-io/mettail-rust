//! Split island bodies into literal spans and `${…}` typed holes.

use crate::error::{Result, SpecError};

/// A literal text span inside an island template.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextSpan {
    pub text: String,
}

/// An unescaped `${…}` hole (expression source, not yet type-checked).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedHole {
    pub source: String,
    pub start: usize,
}

/// Piece of an island template.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemplatePiece {
    Text(TextSpan),
    Hole(TypedHole),
}

/// Island body split into alternating text and holes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IslandTemplate {
    pub pieces: Vec<TemplatePiece>,
}

/// Split an island body (lexer raw, escapes preserved) into text spans and holes.
///
/// Escaped `\${` is literal text; unescaped `${` opens a typed hole.
pub fn split_template(body: &str) -> IslandTemplate {
    let mut pieces = Vec::new();
    let mut i = 0;
    let bytes = body.as_bytes();
    let mut text_start = 0;

    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 2 < bytes.len() && bytes[i + 1] == b'$' && bytes[i + 2] == b'{'
        {
            if i > text_start {
                pieces
                    .push(TemplatePiece::Text(TextSpan { text: body[text_start..i].to_string() }));
            }
            pieces.push(TemplatePiece::Text(TextSpan { text: "${".to_string() }));
            i += 3;
            text_start = i;
            continue;
        }
        if bytes[i] == b'$' && i + 1 < bytes.len() && bytes[i + 1] == b'{' {
            if i > text_start {
                pieces
                    .push(TemplatePiece::Text(TextSpan { text: body[text_start..i].to_string() }));
            }
            let hole_start = i;
            i += 2;
            let expr_start = i;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                match bytes[i] {
                    b'{' => depth += 1,
                    b'}' => depth -= 1,
                    _ => {},
                }
                if depth > 0 {
                    i += 1;
                }
            }
            if depth != 0 {
                pieces.push(TemplatePiece::Text(TextSpan { text: body[hole_start..].to_string() }));
                break;
            }
            let source = body[expr_start..i].trim().to_string();
            pieces.push(TemplatePiece::Hole(TypedHole { source, start: hole_start }));
            i += 1;
            text_start = i;
        } else {
            i += 1;
        }
    }
    if text_start < body.len() {
        pieces.push(TemplatePiece::Text(TextSpan { text: body[text_start..].to_string() }));
    }
    IslandTemplate { pieces }
}

/// Count unescaped `${` holes in a decoded body.
pub fn hole_count(body: &str) -> usize {
    split_template(body)
        .pieces
        .iter()
        .filter(|p| matches!(p, TemplatePiece::Hole(_)))
        .count()
}

/// Validate hole count matches expectation (for tests).
pub fn expect_hole_count(body: &str, expected: usize) -> Result<()> {
    let n = hole_count(body);
    if n != expected {
        return Err(SpecError::Island {
            lang: "?".into(),
            message: format!("expected {expected} holes, found {n}"),
        });
    }
    Ok(())
}
