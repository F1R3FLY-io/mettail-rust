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
    Integer(i128),

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
            Tok::Integer(value) => format!("integer `{value}`"),
            Tok::Eof => "end of input".into(),
            t => format!("`{}`", t.spelling()),
        }
    }

    pub fn spelling(&self) -> &str {
        match self {
            Tok::Ident(s) | Tok::Str(s) => s,
            Tok::Integer(_) => "<integer>",
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

        // string literal
        if c == '"' {
            bump!(1);
            let mut s = String::new();
            loop {
                if i >= b.len() {
                    return Err(format!("{span}: unterminated string literal"));
                }
                if b[i] == '"' {
                    bump!(1);
                    break;
                }
                if b[i] == '\\' && i + 1 < b.len() {
                    let e = b[i + 1];
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        other => other,
                    });
                    bump!(2);
                    continue;
                }
                s.push(b[i]);
                bump!(1);
            }
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

        // Canonical values use signed decimal integers. A leading `--` was
        // already consumed as a comment above, so `-` is unambiguous here.
        if c.is_ascii_digit() || (c == '-' && i + 1 < b.len() && b[i + 1].is_ascii_digit()) {
            let start = i;
            if c == '-' {
                bump!(1);
            }
            while i < b.len() && b[i].is_ascii_digit() {
                bump!(1);
            }
            let raw: String = b[start..i].iter().collect();
            let value = raw
                .parse::<i128>()
                .map_err(|_| format!("{span}: integer is outside the i128 range"))?;
            out.push(Lexeme { tok: Tok::Integer(value), span });
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
