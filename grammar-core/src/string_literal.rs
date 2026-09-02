//! Canonical encoding and decoding for MeTTaIL double-quoted string tokens.

use std::fmt;

/// Why a captured double-quoted string token could not be decoded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StringLiteralDecodeError {
    /// The token does not have one leading and one trailing double quote.
    MissingQuotes,
    /// A double quote occurs inside the framed token without an escape.
    UnescapedQuote,
    /// The final character of the token body is a backslash.
    DanglingEscape,
}

impl fmt::Display for StringLiteralDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MissingQuotes => "string-token capture is not enclosed in double quotes",
            Self::UnescapedQuote => "string-token capture contains an unescaped double quote",
            Self::DanglingEscape => "string-token capture ends in a dangling escape",
        })
    }
}

impl std::error::Error for StringLiteralDecodeError {}

/// Decode a complete MeTTaIL double-quoted string token from left to right.
///
/// Escaped quote and escaped backslash contract to one character. Every other
/// escape pair is preserved literally. The deterministic two-state transducer
/// consumes each Unicode scalar value once, so adjacent escape pairs cannot be
/// reinterpreted across a boundary produced by an earlier replacement pass.
pub fn decode_double_quoted_string_literal(raw: &str) -> Result<String, StringLiteralDecodeError> {
    let inner = raw
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .ok_or(StringLiteralDecodeError::MissingQuotes)?;
    let mut output = String::with_capacity(inner.len());
    let mut characters = inner.chars();
    while let Some(character) = characters.next() {
        match character {
            '"' => return Err(StringLiteralDecodeError::UnescapedQuote),
            '\\' => {
                let escaped = characters
                    .next()
                    .ok_or(StringLiteralDecodeError::DanglingEscape)?;
                match escaped {
                    '"' => output.push('"'),
                    '\\' => output.push('\\'),
                    other => {
                        output.push('\\');
                        output.push(other);
                    },
                }
            },
            other => output.push(other),
        }
    }
    Ok(output)
}

/// Encode a value as one canonical MeTTaIL double-quoted string token.
///
/// Quote and backslash are the only characters escaped because they are the
/// only distinguished characters in the decoder. This function is the right
/// inverse of [`decode_double_quoted_string_literal`].
pub fn encode_double_quoted_string_literal(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            other => output.push(other),
        }
    }
    output.push('"');
    output
}

#[cfg(test)]
mod tests {
    use super::{
        decode_double_quoted_string_literal, encode_double_quoted_string_literal,
        StringLiteralDecodeError,
    };

    #[test]
    fn contracts_only_quote_and_backslash_from_left_to_right() {
        for (raw, expected) in [
            (r#""plain""#, "plain"),
            (r#""a\"b\\c""#, "a\"b\\c"),
            (r#""\n\t\x""#, r"\n\t\x"),
            ("\"λ��\"", "λ��"),
        ] {
            assert_eq!(decode_double_quoted_string_literal(raw).as_deref(), Ok(expected));
        }
    }

    #[test]
    fn overlapping_escape_pairs_do_not_cross_transition_boundaries() {
        let decoded = decode_double_quoted_string_literal(r#""a\\\"b\\\\c""#)
            .expect("the framed string is valid");
        assert_eq!(decoded.chars().collect::<Vec<_>>(), ['a', '\\', '"', 'b', '\\', '\\', 'c']);
    }

    #[test]
    fn malformed_frames_fail_closed() {
        for (raw, expected) in [
            ("not-quoted", StringLiteralDecodeError::MissingQuotes),
            ("\"interior\"quote\"", StringLiteralDecodeError::UnescapedQuote),
            ("\"dangling\\\"", StringLiteralDecodeError::DanglingEscape),
        ] {
            assert_eq!(decode_double_quoted_string_literal(raw), Err(expected));
        }
    }

    #[test]
    fn canonical_encoding_round_trips_every_distinguished_character() {
        for value in ["", "plain", "a\\\"b\\\\c", r"\n\t\x", "λ��\n"] {
            let encoded = encode_double_quoted_string_literal(value);
            assert_eq!(decode_double_quoted_string_literal(&encoded).as_deref(), Ok(value));
        }
    }
}
