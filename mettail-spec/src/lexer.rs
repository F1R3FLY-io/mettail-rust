use crate::error::{Result, SpecError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Ident(String),
    StringLit(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    Dot,
    Colon,
    Comma,
    Equals,
    SlashBackslash, // /\
    Punct(char),
    Island { lang: String, body: String, triple: bool },
    Eof,
}

pub struct Lexer<'a> {
    _source: &'a str,
    path: std::path::PathBuf,
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, path: std::path::PathBuf) -> Self {
        Self {
            _source: source,
            path,
            chars: source.chars().peekable(),
            line: 1,
            col: 1,
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Token>> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek().is_none() {
                tokens.push(Token::Eof);
                break;
            }
            tokens.push(self.next_token()?);
        }
        Ok(tokens)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while matches!(self.peek(), Some(c) if c.is_whitespace()) {
                if self.peek() == Some('\n') {
                    self.line += 1;
                    self.col = 1;
                } else {
                    self.col += 1;
                }
                self.next_char();
            }
            if self.peek() == Some('#') {
                while self.peek().is_some_and(|c| c != '\n') {
                    self.next_char();
                }
                continue;
            }
            break;
        }
    }

    fn next_token(&mut self) -> Result<Token> {
        let c = self.peek().ok_or_else(|| self.eof_error())?;
        match c {
            '{' => {
                self.next_char();
                Ok(Token::LBrace)
            },
            '}' => {
                self.next_char();
                Ok(Token::RBrace)
            },
            '(' => {
                self.next_char();
                Ok(Token::LParen)
            },
            ')' => {
                self.next_char();
                Ok(Token::RParen)
            },
            '.' => {
                self.next_char();
                Ok(Token::Dot)
            },
            ':' => {
                self.next_char();
                Ok(Token::Colon)
            },
            ',' => {
                self.next_char();
                Ok(Token::Comma)
            },
            '=' => {
                self.next_char();
                Ok(Token::Equals)
            },
            '/' => {
                self.next_char();
                if self.peek() == Some('\\') {
                    self.next_char();
                    Ok(Token::SlashBackslash)
                } else {
                    Err(self.error("expected '\\' after '/' for union operator /\\"))
                }
            },
            '"' => Ok(Token::StringLit(self.read_string()?)),
            '`' => self.read_island(false),
            _ if c.is_ascii_alphabetic() || c == '_' => {
                let ident = self.read_ident()?;
                if self.peek() == Some('`') {
                    self.try_lex_island_after_ident(ident)
                } else {
                    Ok(Token::Ident(ident))
                }
            },
            _ if c.is_ascii_punctuation() => {
                self.next_char();
                Ok(Token::Punct(c))
            },
            _ => Err(self.error(format!("unexpected character '{c}'"))),
        }
    }

    fn read_ident(&mut self) -> Result<String> {
        let mut s = String::new();
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            s.push(self.next_char().unwrap());
        }
        Ok(s)
    }

    fn read_string(&mut self) -> Result<String> {
        self.next_char(); // opening "
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '"' {
                self.next_char();
                return Ok(s);
            }
            if c == '\\' {
                self.next_char();
                if let Some(esc) = self.next_char() {
                    s.push(esc);
                }
                continue;
            }
            s.push(self.next_char().unwrap());
        }
        Err(self.error("unterminated string literal"))
    }

    fn read_island(&mut self, triple: bool) -> Result<Token> {
        // Caller consumed opening ` or we are at Lang```
        let lang = if triple {
            // multiline: Lang```
            let lang = self.read_ident()?;
            for _ in 0..3 {
                if self.peek() != Some('`') {
                    return Err(self.error("expected ``` after island language name"));
                }
                self.next_char();
            }
            lang
        } else {
            // Could be `body` only if we mis-parsed — single-backtick islands are Lang`body`
            // Format: Ident`body` — ident already consumed before `
            return Err(self.error("island must be Lang`...` form"));
        };

        let body = self.scan_island_body('`', triple)?;
        Ok(Token::Island { lang, body, triple })
    }

    /// Parse `Lang`...` or `Lang```...```
    pub fn try_lex_island_after_ident(&mut self, lang: String) -> Result<Token> {
        if self.peek() != Some('`') {
            return Err(self.error(format!("expected backtick after island language '{lang}'")));
        }
        self.next_char();
        let triple = if self.peek() == Some('`') {
            self.next_char();
            if self.peek() == Some('`') {
                self.next_char();
                true
            } else {
                return Err(self.error("expected ``` for multiline island"));
            }
        } else {
            false
        };
        let body = self.scan_island_body('`', triple)?;
        Ok(Token::Island { lang, body, triple })
    }

    fn scan_island_body(&mut self, close: char, triple: bool) -> Result<String> {
        let mut body = String::new();
        let closes = if triple { 3 } else { 1 };
        loop {
            let Some(c) = self.peek() else {
                return Err(self.error("unterminated island"));
            };
            if c == '\\' {
                body.push('\\');
                self.next_char();
                if let Some(esc) = self.next_char() {
                    body.push(esc);
                } else {
                    return Err(self.error("unterminated escape in island"));
                }
                continue;
            }
            if c == close {
                let mut count = 0;
                while self.peek() == Some(close) && count < closes {
                    self.next_char();
                    count += 1;
                }
                if count == closes {
                    return Ok(body);
                }
                for _ in 0..count {
                    body.push(close);
                }
                continue;
            }
            body.push(self.next_char().unwrap());
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn next_char(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        if c != '\n' {
            self.col += 1;
        }
        Some(c)
    }

    fn error(&self, message: impl Into<String>) -> SpecError {
        SpecError::Parse {
            path: self.path.clone(),
            line: self.line,
            col: self.col,
            message: message.into(),
        }
    }

    fn eof_error(&self) -> SpecError {
        self.error("unexpected end of file")
    }
}
