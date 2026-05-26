//! Decoded island body (escapes applied; holes preserved for template pass).

use crate::error::{Result, SpecError};

/// Island body after escape decoding (same bytes the lexer stores in [`Token::Island`](crate::lexer::Token)).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBody {
    pub text: String,
}

/// Apply v1 §5.2 escape rules to a raw island body string.
///
/// The lexer already decodes escapes while scanning; this function is the shared
/// specification for tests and for re-processing stored bodies.
pub fn decode_island_body(raw: &str) -> Result<DecodedBody> {
    let mut out = String::new();
    let mut chars = raw.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('`') => out.push('`'),
                Some('$') => {
                    if chars.peek() == Some(&'{') {
                        chars.next();
                        out.push_str("${");
                    } else {
                        out.push('$');
                    }
                },
                Some('\\') => out.push('\\'),
                Some(x) => out.push(x),
                None => {
                    return Err(SpecError::Parse {
                        path: std::path::PathBuf::from("<island>"),
                        line: 0,
                        col: 0,
                        message: "unterminated escape in island".into(),
                    });
                },
            }
        } else {
            out.push(c);
        }
    }
    Ok(DecodedBody { text: out })
}
