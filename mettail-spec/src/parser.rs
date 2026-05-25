use std::path::PathBuf;

use proc_macro2::TokenStream;

use crate::error::{Result, SpecError};
use crate::lexer::{Lexer, Token};
use crate::surface::*;

pub fn parse_file(path: PathBuf, source: &str) -> Result<SurfaceFile> {
    let tokens = Lexer::new(source, path.clone()).tokenize()?;
    let mut p = ParserState::new(tokens, path.clone());
    let imports = p.parse_imports()?;
    let module = p.parse_module()?;
    if !p.check_eof() {
        return Err(p.error("expected end of file after module"));
    }
    Ok(SurfaceFile { path, imports, module })
}

struct ParserState {
    tokens: Vec<Token>,
    pos: usize,
    path: PathBuf,
}

impl ParserState {
    fn new(tokens: Vec<Token>, path: PathBuf) -> Self {
        Self { tokens, pos: 0, path }
    }

    fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(&Token::Eof)
    }

    fn advance(&mut self) -> Token {
        let t = self.peek().clone();
        if !matches!(t, Token::Eof) {
            self.pos += 1;
        }
        t
    }

    fn expect_ident(&mut self, expected: Option<&str>) -> Result<String> {
        match self.advance() {
            Token::Ident(s) => {
                if let Some(e) = expected {
                    if s != e {
                        return Err(self.error(format!("expected '{e}', found '{s}'")));
                    }
                }
                Ok(s)
            },
            other => Err(self.error(format!("expected identifier, found {other:?}"))),
        }
    }

    fn expect(&mut self, want: Token) -> Result<()> {
        let got = self.advance();
        if std::mem::discriminant(&got) != std::mem::discriminant(&want) {
            return Err(self.error(format!("expected {want:?}, found {got:?}")));
        }
        Ok(())
    }

    fn check_eof(&self) -> bool {
        matches!(self.peek(), Token::Eof)
    }

    fn error(&self, message: impl Into<String>) -> SpecError {
        SpecError::Parse {
            path: self.path.clone(),
            line: 1,
            col: 1,
            message: message.into(),
        }
    }

    fn parse_imports(&mut self) -> Result<Vec<Import>> {
        let mut imports = Vec::new();
        while matches!(self.peek(), Token::Ident(s) if s == "import") {
            self.advance();
            if matches!(self.peek(), Token::LBrace) {
                self.advance();
                while !matches!(self.peek(), Token::RBrace) {
                    imports.push(self.parse_import_descriptor()?);
                }
                self.expect(Token::RBrace)?;
            } else {
                imports.push(self.parse_import_descriptor()?);
            }
        }
        Ok(imports)
    }

    fn parse_import_descriptor(&mut self) -> Result<Import> {
        let path = match self.advance() {
            Token::StringLit(s) => s,
            other => {
                return Err(self.error(format!("expected quoted import path, found {other:?}")))
            },
        };
        let alias = if matches!(self.peek(), Token::Ident(s) if s == "as") {
            self.advance();
            Some(self.expect_ident(None)?)
        } else {
            None
        };
        Ok(Import { path, alias })
    }

    fn parse_module(&mut self) -> Result<Module> {
        self.expect_ident(Some("module"))?;
        let name = self.expect_ident(None)?;
        self.expect(Token::LBrace)?;
        let mut items = Vec::new();
        while !matches!(self.peek(), Token::RBrace) {
            items.push(self.parse_content_item()?);
        }
        self.expect(Token::RBrace)?;
        Ok(Module { name, items })
    }

    fn parse_content_item(&mut self) -> Result<ContentItem> {
        let exported = if matches!(self.peek(), Token::Ident(s) if s == "export") {
            self.advance();
            true
        } else {
            false
        };

        match self.peek() {
            Token::Ident(s) if s == "extender" => {
                self.advance();
                let name = self.expect_ident(None)?;
                self.expect(Token::LParen)?;
                let mut params = Vec::new();
                if !matches!(self.peek(), Token::RParen) {
                    params.push(self.expect_ident(None)?);
                    while matches!(self.peek(), Token::Comma) {
                        self.advance();
                        params.push(self.expect_ident(None)?);
                    }
                }
                self.expect(Token::RParen)?;
                self.expect(Token::LBrace)?;
                let body = self.parse_extender_expr()?;
                self.expect(Token::RBrace)?;
                Ok(ContentItem::Extender(ExtenderDecl { exported, name, params, body }))
            },
            Token::Ident(s) if s == "language" => {
                self.advance();
                let name = self.expect_ident(None)?;
                self.expect(Token::Equals)?;
                let expr = self.parse_language_expr()?;
                Ok(ContentItem::Language(LanguageDecl { exported, name, expr }))
            },
            Token::Ident(s) if s == "space" => {
                self.advance();
                let name = self.expect_ident(None)?;
                self.expect(Token::Colon)?;
                let lang = self.parse_language_expr()?;
                Ok(ContentItem::Space(SpaceDecl { exported, name, lang }))
            },
            Token::Ident(s) if s == "module" => Ok(ContentItem::Nested(self.parse_module()?)),
            Token::Ident(s) if s == "empty" => {
                // bare empty at content level — unusual
                self.advance();
                Err(self.error("unexpected 'empty' at module content level"))
            },
            Token::Island { .. } => {
                Err(self
                    .error("process/island content at module level is not supported in Phase 1"))
            },
            other => Err(self.error(format!("unexpected module content: {other:?}"))),
        }
    }

    fn parse_extender_expr(&mut self) -> Result<ExtenderExpr> {
        self.parse_extender_expr_bp(0)
    }

    fn parse_extender_expr_bp(&mut self, min_bp: u8) -> Result<ExtenderExpr> {
        let mut lhs = self.parse_extender_prefix()?;
        loop {
            if matches!(self.peek(), Token::SlashBackslash) {
                let bp = 1;
                if bp < min_bp {
                    break;
                }
                self.advance();
                let rhs = self.parse_extender_expr_bp(bp + 1)?;
                lhs = ExtenderExpr::Union(Box::new(lhs), Box::new(rhs));
                continue;
            }
            // suffix operators bind to lhs
            if let Some(kind) = suffix_keyword(self.peek()) {
                let bp = 2;
                if bp < min_bp {
                    break;
                }
                self.advance();
                let (tokens, raw) = self.parse_brace_fragment()?;
                lhs = ExtenderExpr::Suffix { inner: Box::new(lhs), kind, tokens, raw };
                continue;
            }
            if matches!(self.peek(), Token::Ident(s) if s == "semantics") {
                let bp = 2;
                if bp < min_bp {
                    break;
                }
                self.advance();
                let target = self.parse_language_expr()?;
                lhs = ExtenderExpr::Semantics { inner: Box::new(lhs), target };
                continue;
            }
            if matches!(self.peek(), Token::Ident(s) if s == "context") {
                let bp = 2;
                if bp < min_bp {
                    break;
                }
                self.advance();
                let template = self.parse_context_template()?;
                lhs = ExtenderExpr::Context { inner: Box::new(lhs), template };
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    fn parse_extender_prefix(&mut self) -> Result<ExtenderExpr> {
        match self.advance() {
            Token::Ident(s) if s == "empty" => Ok(ExtenderExpr::Empty),
            Token::LBrace => {
                let inner = self.parse_extender_expr()?;
                self.expect(Token::RBrace)?;
                Ok(ExtenderExpr::Group(Box::new(inner)))
            },
            Token::Island { lang, body, triple } => {
                Ok(ExtenderExpr::Island(IslandToken { lang, body, triple }))
            },
            Token::Ident(name) => {
                if matches!(self.peek(), Token::LParen) {
                    self.advance();
                    let mut args = Vec::new();
                    if !matches!(self.peek(), Token::RParen) {
                        args.push(self.parse_extender_expr()?);
                        while matches!(self.peek(), Token::Comma) {
                            self.advance();
                            args.push(self.parse_extender_expr()?);
                        }
                    }
                    self.expect(Token::RParen)?;
                    Ok(ExtenderExpr::Call { name, args })
                } else {
                    Ok(ExtenderExpr::Call { name, args: Vec::new() })
                }
            },
            other => Err(self.error(format!("expected extender expression, found {other:?}"))),
        }
    }

    fn parse_brace_fragment(&mut self) -> Result<(TokenStream, String)> {
        self.expect(Token::LBrace)?;
        let raw = self.extract_balanced_brace_raw()?;
        // Fragment parsers (mettail-ast) add their own `types { … }` / `terms { … }` wrapper.
        let tokens: TokenStream = syn::parse_str(&raw)
            .map_err(|e| self.error(format!("invalid fragment tokens: {e}")))?;
        Ok((tokens, raw))
    }

    fn extract_balanced_brace_raw(&mut self) -> Result<String> {
        // We are past the opening `{` of the fragment; collect until matching `}`.
        let mut depth = 1usize;
        let mut raw = String::new();
        while depth > 0 {
            let tok = self.advance();
            if matches!(tok, Token::RBrace) {
                depth -= 1;
                if depth > 0 {
                    push_raw_token(&mut raw, &tok);
                }
                continue;
            }
            if matches!(tok, Token::Eof) {
                return Err(self.error("unterminated fragment block"));
            }
            push_raw_token(&mut raw, &tok);
            if matches!(tok, Token::LBrace) {
                depth += 1;
            }
        }
        Ok(raw)
    }

    fn parse_context_template(&mut self) -> Result<ContextTemplate> {
        self.expect(Token::LBrace)?;
        let raw = self.extract_balanced_brace_raw()?;
        let insert_offset = raw.find("INSERT_HERE");
        Ok(ContextTemplate { raw, insert_offset })
    }

    fn parse_language_expr(&mut self) -> Result<LanguageExpr> {
        let mut segments = vec![self.expect_ident(None)?];
        while matches!(self.peek(), Token::Dot) {
            self.advance();
            segments.push(self.expect_ident(None)?);
        }
        if matches!(self.peek(), Token::LParen) {
            self.advance();
            let mut args = Vec::new();
            if !matches!(self.peek(), Token::RParen) {
                args.push(self.parse_language_expr()?);
                while matches!(self.peek(), Token::Comma) {
                    self.advance();
                    args.push(self.parse_language_expr()?);
                }
            }
            self.expect(Token::RParen)?;
            Ok(LanguageExpr { segments, args: Some(args) })
        } else {
            Ok(LanguageExpr { segments, args: None })
        }
    }
}

fn suffix_keyword(tok: &Token) -> Option<SuffixKind> {
    match tok {
        Token::Ident(s) => match s.as_str() {
            "types" => Some(SuffixKind::Types),
            "terms" => Some(SuffixKind::Terms),
            "literals" => Some(SuffixKind::Literals),
            "equations" => Some(SuffixKind::Equations),
            "relations" => Some(SuffixKind::Relations),
            "rewrites" => Some(SuffixKind::Rewrites),
            _ => None,
        },
        _ => None,
    }
}

fn needs_space_before(last: char, tok: &Token) -> bool {
    match tok {
        Token::Ident(_) => {
            last.is_alphanumeric() || matches!(last, ']' | ')' | '>' | ';' | '.' | ':' | ',' | '"')
        },
        Token::StringLit(_) => !last.is_whitespace() && last != '"',
        Token::Dot => last.is_alphanumeric(),
        Token::Colon | Token::Comma => last.is_alphanumeric(),
        Token::Punct(c) => match c {
            ':' => last.is_alphanumeric() || last == '.',
            '=' => last == ':',
            '|' => last.is_alphanumeric() || last == ':',
            '-' => last.is_alphanumeric(),
            _ => false,
        },
        _ => false,
    }
}

fn push_raw_token(raw: &mut String, tok: &Token) {
    if !raw.is_empty() {
        let last = raw.chars().last().unwrap_or(' ');
        if needs_space_before(last, tok) {
            raw.push(' ');
        }
    }
    match tok {
        Token::Ident(s) => raw.push_str(s),
        Token::StringLit(s) => {
            raw.push('"');
            raw.push_str(s);
            raw.push('"');
        },
        Token::Island { lang, body, triple } => {
            if *triple {
                raw.push_str(lang);
                raw.push_str("```");
                raw.push_str(body);
                raw.push_str("```");
            } else {
                raw.push_str(lang);
                raw.push('`');
                raw.push_str(body);
                raw.push('`');
            }
        },
        other => raw.push(token_char(other)),
    }
}

fn token_char(tok: &Token) -> char {
    match tok {
        Token::LParen => '(',
        Token::RParen => ')',
        Token::Dot => '.',
        Token::Colon => ':',
        Token::Comma => ',',
        Token::Equals => '=',
        Token::SlashBackslash => '/',
        Token::Punct(c) => *c,
        _ => ' ',
    }
}
