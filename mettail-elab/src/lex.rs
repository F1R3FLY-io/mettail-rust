//! Lexer for the frozen MeTTaIL module surface.
//!
//! Surface per plan §3, decisions D1-D10. Notable: `|-` and `:` delimit the
//! term judgement (D2/G6), `...` introduces a remainder pattern (G3), `^`
//! introduces an abstraction (G4).

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Tok {
    Ident(String),
    Str(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),

    // keywords
    KwModule,
    KwTheoryUpper, // `Theory` - declaration
    KwTheoryLower, // `theory` - instantiation
    KwImport,
    KwAs,
    KwFrom,
    KwEmpty,
    KwFree,
    KwLet,
    KwIn,
    KwIf,
    KwThen,
    KwSubst,
    KwTypes,
    KwExports,
    KwReplacements,
    KwTerms,
    KwEquations,
    KwRewrites,
    KwData,
    KwTrue,
    KwFalse,
    KwNil,

    // punctuation
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    Dot,
    Star,
    Hash,
    Caret,
    Turnstile, // |-
    FatArrow,  // =>
    Squiggle,  // ~>
    ThinArrow, // ->
    EqEq,      // ==
    Meet,      // /\
    Join,      // \/
    Diff,      // backslash
    Ellipsis,  // ...
    Eq,        // =
    Eof,
}

impl Tok {
    pub fn describe(&self) -> String {
        match self {
            Tok::Ident(s) => format!("identifier `{s}`"),
            Tok::Str(s) => format!("string {s:?}"),
            Tok::Bytes(bytes) => format!("byte array literal ({} bytes)", bytes.len()),
            Tok::Integer(value) => format!("integer `{value}`"),
            Tok::FloatBits(bits) => format!("float `{}`", f64::from_bits(*bits)),
            Tok::Eof => "end of input".into(),
            t => format!("`{}`", t.spelling()),
        }
    }

    pub fn spelling(&self) -> &str {
        match self {
            Tok::Ident(s) | Tok::Str(s) => s,
            Tok::Bytes(_) => "<bytes>",
            Tok::Integer(_) => "<integer>",
            Tok::FloatBits(_) => "<float>",
            Tok::KwModule => "Module",
            Tok::KwTheoryUpper => "Theory",
            Tok::KwTheoryLower => "theory",
            Tok::KwImport => "import",
            Tok::KwAs => "as",
            Tok::KwFrom => "from",
            Tok::KwEmpty => "Empty",
            Tok::KwFree => "free",
            Tok::KwLet => "let",
            Tok::KwIn => "in",
            Tok::KwIf => "if",
            Tok::KwThen => "then",
            Tok::KwSubst => "subst",
            Tok::KwTypes => "Types",
            Tok::KwExports => "Exports",
            Tok::KwReplacements => "Replacements",
            Tok::KwTerms => "Terms",
            Tok::KwEquations => "Equations",
            Tok::KwRewrites => "Rewrites",
            Tok::KwData => "Data",
            Tok::KwTrue => "true",
            Tok::KwFalse => "false",
            Tok::KwNil => "Nil",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::Comma => ",",
            Tok::Semi => ";",
            Tok::Colon => ":",
            Tok::Dot => ".",
            Tok::Star => "*",
            Tok::Hash => "#",
            Tok::Caret => "^",
            Tok::Turnstile => "|-",
            Tok::FatArrow => "=>",
            Tok::Squiggle => "~>",
            Tok::ThinArrow => "->",
            Tok::EqEq => "==",
            Tok::Meet => "/\\",
            Tok::Join => "\\/",
            Tok::Diff => "\\",
            Tok::Ellipsis => "...",
            Tok::Eq => "=",
            Tok::Eof => "<eof>",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lexeme {
    pub tok: Tok,
    pub span: Span,
}

/// Decode the exact string-literal semantics used by nouveau Rholang.
///
/// Only escaped quote and escaped backslash contract. Every other escape pair
/// is preserved literally, so `\n`, `\t`, and `\x` remain two characters.
/// The loop is a deterministic two-state transducer and uses no native-stack
/// recursion. Structural DDL lowering and Registry-source parsing share this
/// function so their canonical values cannot diverge on escape spelling.
pub fn decode_rholang_string_literal(raw: &str) -> Result<String, String> {
    let inner = raw
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .ok_or_else(|| "string-token capture is not enclosed in double quotes".to_string())?;
    let mut output = String::with_capacity(inner.len());
    let mut characters = inner.chars();
    while let Some(character) = characters.next() {
        match character {
            '"' => return Err("string-token capture contains an unescaped double quote".into()),
            '\\' => {
                let escaped = characters
                    .next()
                    .ok_or_else(|| "string-token capture ends in a dangling escape".to_string())?;
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

/// Decode the exact `b"…"` byte-array token emitted by nouveau Rholang.
///
/// The framing and even-length checks precede allocation.  Hex decoding is a
/// deterministic two-nibble transducer and accepts either case, matching the
/// Rholang literal language while the renderer emits canonical lowercase.
pub fn decode_rholang_byte_array_literal(raw: &str) -> Result<Vec<u8>, String> {
    let digits = raw
        .strip_prefix("b\"")
        .and_then(|value| value.strip_suffix('"'))
        .ok_or_else(|| "byte-array token is not enclosed in b\"...\"".to_string())?;
    if digits.len() % 2 != 0 {
        return Err("byte-array token contains an odd number of hexadecimal digits".into());
    }
    let mut output = Vec::new();
    output
        .try_reserve_exact(digits.len() / 2)
        .map_err(|error| format!("cannot allocate decoded byte array: {error}"))?;
    let mut pending_high_nibble = None;
    for digit in digits.bytes() {
        let nibble = match digit {
            b'0'..=b'9' => digit - b'0',
            b'a'..=b'f' => digit - b'a' + 10,
            b'A'..=b'F' => digit - b'A' + 10,
            _ => return Err("byte-array token contains a non-hexadecimal digit".into()),
        };
        match pending_high_nibble {
            None => pending_high_nibble = Some(nibble),
            Some(high) => {
                output.push((high << 4) | nibble);
                pending_high_nibble = None;
            },
        }
    }
    match pending_high_nibble {
        Some(_) => Err("byte-array token ended after one hexadecimal nibble".into()),
        None => Ok(output),
    }
}

pub fn lex(src: &str) -> Result<Vec<Lexeme>, String> {
    let b: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    let mut line = 1u32;
    let mut col = 1u32;
    let mut out = Vec::new();

    macro_rules! bump {
        ($n:expr) => {{
            for _ in 0..$n {
                if b[i] == '\n' {
                    line += 1;
                    col = 1;
                } else {
                    col += 1;
                }
                i += 1;
            }
        }};
    }

    while i < b.len() {
        let span = Span { line, col };
        let c = b[i];

        // whitespace
        if c.is_whitespace() {
            bump!(1);
            continue;
        }
        // line comments: `--` and `//`
        if (c == '-' && i + 1 < b.len() && b[i + 1] == '-')
            || (c == '/' && i + 1 < b.len() && b[i + 1] == '/')
        {
            while i < b.len() && b[i] != '\n' {
                bump!(1);
            }
            continue;
        }
        // block comment `{- ... -}` (must be tried before `{`)
        if c == '{' && i + 1 < b.len() && b[i + 1] == '-' {
            bump!(2);
            let mut depth = 1;
            while i < b.len() && depth > 0 {
                if b[i] == '{' && i + 1 < b.len() && b[i + 1] == '-' {
                    depth += 1;
                    bump!(2);
                } else if b[i] == '-' && i + 1 < b.len() && b[i + 1] == '}' {
                    depth -= 1;
                    bump!(2);
                } else {
                    bump!(1);
                }
            }
            if depth > 0 {
                return Err(format!("{span}: unterminated block comment"));
            }
            continue;
        }

        // Byte-array literal. This check precedes identifiers and strings so
        // the frame is one token rather than `Ident("b")`, `Str(...)`.
        if c == 'b' && i + 1 < b.len() && b[i + 1] == '"' {
            let start = i;
            bump!(2);
            while i < b.len() && b[i] != '"' {
                if !b[i].is_ascii_hexdigit() {
                    return Err(format!(
                        "{span}: byte-array literal contains non-hexadecimal character `{}`",
                        b[i]
                    ));
                }
                bump!(1);
            }
            if i >= b.len() {
                return Err(format!("{span}: unterminated byte-array literal"));
            }
            bump!(1);
            let raw: String = b[start..i].iter().collect();
            let value = decode_rholang_byte_array_literal(&raw)
                .map_err(|message| format!("{span}: {message}"))?;
            out.push(Lexeme { tok: Tok::Bytes(value), span });
            continue;
        }

        // string literal
        if c == '"' {
            let start = i;
            bump!(1);
            loop {
                if i >= b.len() {
                    return Err(format!("{span}: unterminated string literal"));
                }
                if b[i] == '"' {
                    bump!(1);
                    break;
                }
                if b[i] == '\\' && i + 1 < b.len() {
                    bump!(2);
                    continue;
                }
                bump!(1);
            }
            let raw: String = b[start..i].iter().collect();
            let s = decode_rholang_string_literal(&raw)
                .map_err(|message| format!("{span}: {message}"))?;
            out.push(Lexeme { tok: Tok::Str(s), span });
            continue;
        }

        // identifiers and keywords
        if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < b.len() && (b[i].is_alphanumeric() || b[i] == '_' || b[i] == '\'') {
                bump!(1);
            }
            let word: String = b[start..i].iter().collect();
            let tok = match word.as_str() {
                "Module" => Tok::KwModule,
                "Theory" => Tok::KwTheoryUpper,
                "theory" => Tok::KwTheoryLower,
                "import" => Tok::KwImport,
                "as" => Tok::KwAs,
                "from" => Tok::KwFrom,
                "Empty" => Tok::KwEmpty,
                "free" => Tok::KwFree,
                "let" => Tok::KwLet,
                "in" => Tok::KwIn,
                "if" => Tok::KwIf,
                "then" => Tok::KwThen,
                "subst" => Tok::KwSubst,
                "Types" => Tok::KwTypes,
                "Exports" => Tok::KwExports,
                "Replacements" => Tok::KwReplacements,
                "Terms" => Tok::KwTerms,
                "Equations" => Tok::KwEquations,
                "Rewrites" => Tok::KwRewrites,
                "Data" => Tok::KwData,
                "true" => Tok::KwTrue,
                "false" => Tok::KwFalse,
                "Nil" => Tok::KwNil,
                _ => Tok::Ident(word),
            };
            out.push(Lexeme { tok, span });
            continue;
        }

        // Canonical values use signed decimal integers and IEEE-754 decimal
        // floats. A leading `--` was already consumed as a comment above, so
        // `-` is unambiguous here.
        if c.is_ascii_digit() || (c == '-' && i + 1 < b.len() && b[i + 1].is_ascii_digit()) {
            let start = i;
            if c == '-' {
                bump!(1);
            }
            while i < b.len() && b[i].is_ascii_digit() {
                bump!(1);
            }
            let mut is_float = false;
            if i + 1 < b.len() && b[i] == '.' && b[i + 1].is_ascii_digit() {
                is_float = true;
                bump!(1);
                while i < b.len() && b[i].is_ascii_digit() {
                    bump!(1);
                }
            }
            if i < b.len() && matches!(b[i], 'e' | 'E') {
                is_float = true;
                bump!(1);
                if i < b.len() && matches!(b[i], '+' | '-') {
                    bump!(1);
                }
                let exponent_start = i;
                while i < b.len() && b[i].is_ascii_digit() {
                    bump!(1);
                }
                if i == exponent_start {
                    return Err(format!("{span}: float exponent has no digits"));
                }
            }
            if !is_float && i < b.len() && b[i] == 'n' {
                bump!(1);
            }
            let raw: String = b[start..i].iter().collect();
            let tok = if is_float {
                let value = raw
                    .parse::<f64>()
                    .map_err(|_| format!("{span}: invalid IEEE-754 float"))?;
                if !value.is_finite() {
                    return Err(format!("{span}: float must be finite"));
                }
                Tok::FloatBits(value.to_bits())
            } else {
                let decimal = raw.strip_suffix('n').unwrap_or(&raw);
                Tok::Integer(
                    decimal
                        .parse::<i128>()
                        .map_err(|_| format!("{span}: integer is outside the i128 range"))?,
                )
            };
            out.push(Lexeme { tok, span });
            continue;
        }

        // multi-character operators, longest first
        let two: String = b[i..(i + 2).min(b.len())].iter().collect();
        let three: String = b[i..(i + 3).min(b.len())].iter().collect();

        if three == "..." {
            bump!(3);
            out.push(Lexeme { tok: Tok::Ellipsis, span });
            continue;
        }
        let two_tok = match two.as_str() {
            "|-" => Some(Tok::Turnstile),
            "=>" => Some(Tok::FatArrow),
            "~>" => Some(Tok::Squiggle),
            "->" => Some(Tok::ThinArrow),
            "==" => Some(Tok::EqEq),
            "/\\" => Some(Tok::Meet),
            "\\/" => Some(Tok::Join),
            _ => None,
        };
        if let Some(t) = two_tok {
            bump!(2);
            out.push(Lexeme { tok: t, span });
            continue;
        }

        let one = match c {
            '{' => Tok::LBrace,
            '}' => Tok::RBrace,
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBracket,
            ']' => Tok::RBracket,
            ',' => Tok::Comma,
            ';' => Tok::Semi,
            ':' => Tok::Colon,
            '.' => Tok::Dot,
            '*' => Tok::Star,
            '#' => Tok::Hash,
            '^' => Tok::Caret,
            '\\' => Tok::Diff,
            '=' => Tok::Eq,
            other => return Err(format!("{span}: unexpected character `{other}`")),
        };
        bump!(1);
        out.push(Lexeme { tok: one, span });
    }

    out.push(Lexeme { tok: Tok::Eof, span: Span { line, col } });
    Ok(out)
}

#[cfg(test)]
mod string_literal_tests {
    use super::{decode_rholang_byte_array_literal, decode_rholang_string_literal, lex, Tok};

    #[test]
    fn decoder_contracts_only_quote_and_backslash() {
        for (raw, expected) in [
            (r#""plain""#, "plain"),
            (r#""a\"b\\c""#, "a\"b\\c"),
            (r#""\n\t\x""#, r"\n\t\x"),
            ("\"λ��\"", "λ��"),
        ] {
            assert_eq!(decode_rholang_string_literal(raw).as_deref(), Ok(expected));
            let tokens = lex(raw).expect("the shared lexer accepts the same literal");
            assert!(matches!(&tokens[0].tok, Tok::Str(value) if value == expected));
        }
    }

    #[test]
    fn malformed_literal_frames_fail_closed() {
        for raw in ["not-quoted", "\"interior\"quote\"", "\"dangling\\\""] {
            assert!(decode_rholang_string_literal(raw).is_err(), "{raw:?}");
        }
    }

    #[test]
    fn byte_array_frame_preserves_kind_and_payload() {
        for (raw, expected) in [(r#"b"""#, Vec::new()), (r#"b"00abFF""#, vec![0x00, 0xab, 0xff])] {
            assert_eq!(decode_rholang_byte_array_literal(raw), Ok(expected.clone()));
            let tokens = lex(raw).expect("byte array lexes as one framed token");
            assert_eq!(tokens[0].tok, Tok::Bytes(expected));
        }
    }

    #[test]
    fn malformed_byte_array_frames_fail_closed() {
        let unframed = r#""00""#;
        assert!(decode_rholang_byte_array_literal(unframed).is_err());
        let tokens = lex(unframed).expect("an ordinary string remains valid");
        assert!(matches!(&tokens[0].tok, Tok::Str(value) if value == "00"));

        for raw in [r#"b"0""#, r#"b"0g""#, r#"b"00"#] {
            assert!(decode_rholang_byte_array_literal(raw).is_err(), "{raw:?}");
            assert!(lex(raw).is_err(), "{raw:?}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_numbers_preserve_integer_and_float_kinds() {
        let tokens = lex("2 2.0 -1.25e2 4E-1 9223372036854775808n -1n").expect("numbers lex");
        assert_eq!(tokens[0].tok, Tok::Integer(2));
        assert_eq!(tokens[1].tok, Tok::FloatBits(2.0f64.to_bits()));
        assert_eq!(tokens[2].tok, Tok::FloatBits((-125.0f64).to_bits()));
        assert_eq!(tokens[3].tok, Tok::FloatBits(0.4f64.to_bits()));
        assert_eq!(tokens[4].tok, Tok::Integer(i64::MAX as i128 + 1));
        assert_eq!(tokens[5].tok, Tok::Integer(-1));
    }

    #[test]
    fn malformed_float_exponents_are_rejected() {
        assert!(lex("1e+").expect_err("bad exponent").contains("no digits"));
    }
}
