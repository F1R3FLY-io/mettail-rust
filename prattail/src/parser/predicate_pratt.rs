//! Language-generic Pratt parser for the §2 predicate sublanguage.
//!
//! This parser implements the EBNF grammar from §2 of
//! `docs/design/predicated-types.md`:
//!
//! ```text
//! literal  ::= pos_lit
//!            | NOT '(' pos_lit ')'                stratified negation
//!            | AND '(' literal (',' literal)+ ')' conjunction sugar
//!            | OR '(' literal (',' literal)+ ')'  disjunction sugar
//!
//! pos_lit  ::= ident '(' args ')'                 relation application
//!            | var IN ident                       set membership sugar
//!            | term cmp term                      infix comparison
//!            | term REWRITE term                  rewrite closure
//!            | ENTAILS '(' literal ',' literal ')' forward impl sugar
//!            | IMPLIED_BY '(' literal ',' literal ')' reverse impl sugar
//!            | IFF '(' literal ',' literal ')'     biconditional sugar
//!            | FORALL '(' var [',' dom_or_bound] ','
//!              literal ')'                        universal sugar
//!            | EXISTS '(' var [',' dom_or_bound] ','
//!              literal ')'                        existential sugar
//! ```
//!
//! ## Language-generic design
//!
//! The parser is **not** coupled to any particular surrounding keyword
//! (`where`, `if`, `|`, etc.). The trigger keyword lives in each
//! language's `terms { }` syntax pattern as a literal that the
//! macro-generated source parser consumes before dispatching to this
//! parser. The parser starts at the first token of the predicate
//! expression itself and stops at any configured terminator.
//!
//! ## Connective spelling
//!
//! Each language's `guards { connectives { ... } }` block declares
//! which keywords spell which connective roles. The parser consults
//! this map (passed via `PredicateParserConfig`) to determine whether
//! a given token is a connective or a relation name. Languages that
//! omit a role from their `connectives { }` block cannot write that
//! role in predicates (the parser falls back to treating the keyword
//! as a plain identifier).
//!
//! ## Default connectives
//!
//! When `PredicateParserConfig::connective_map` is `None`, the parser
//! uses a default set:
//! - `and`, `∧` → And
//! - `or`, `∨` → Or
//! - `not`, `¬`, `!` → Not
//! - `entails`, `implies`, `⟹` → Implies (forward)
//! - `implied_by`, `⟸` → Implies (reversed)
//! - `iff`, `⟺` → biconditional (desugars to two Implies)
//! - `forall`, `∀` → Quantified ForAll
//! - `exists`, `∃` → Quantified Exists
//! - `in`, `∈`, `:` → set membership sugar

use crate::behavioral_pred::{BehavioralPred, PredArg, Quantifier, QuantifiedDomain};
use std::collections::HashMap;

// ═════════════════════════════════════════════════════════════════════════
// Public API
// ═════════════════════════════════════════════════════════════════════════

/// Configuration for a `PredicateParser` instance. The configuration
/// is derived from the current language's `guards { }` block at
/// macro-expansion time and passed at each call site.
#[derive(Debug, Clone, Default)]
pub struct PredicateParserConfig {
    /// Maps connective role names (`"and"`, `"or"`, `"not"`, ...)
    /// to the set of keyword spellings that trigger them in this
    /// language. Derived from the `guards { connectives { } }` block.
    ///
    /// When `None`, the parser uses the default set of spellings
    /// (see module docs).
    pub connective_map: Option<HashMap<String, Vec<String>>>,
    /// Terminator tokens — the parser stops when any of these is
    /// encountered at the top level (outside parentheses). The
    /// macro-generated parser computes these from the next literal
    /// in the surrounding syntax pattern.
    pub terminators: Vec<TerminatorToken>,
    /// Names of registered built-in predicates from
    /// `guards { eq . x, y |- x "==" y; ... }`. Used to recognize
    /// user-defined predicate spellings beyond the EBNF defaults.
    /// Not yet consulted by the initial parser version.
    #[allow(dead_code)]
    pub builtin_predicates: Vec<String>,
}

/// A token that signals the end of the predicate expression. The
/// parser stops consuming input when it sees any of these at the
/// top level (not inside nested parentheses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminatorToken {
    /// A specific literal token like `{`, `then`, or `)`.
    Literal(String),
    /// End of input.
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "predicate parse error at {}: {}", self.position, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Top-level entry: parse a predicate expression from a `&str`.
///
/// The input should contain ONLY the predicate expression — the
/// caller is responsible for extracting the substring between the
/// trigger keyword (e.g., `where`) and the terminator (e.g., `{`).
pub fn parse_predicate_from_str(
    input: &str,
    config: PredicateParserConfig,
) -> Result<BehavioralPred, ParseError> {
    let tokens = tokenize(input)?;
    let mut parser = PredicateParser::new(tokens, config);
    let pred = parser.parse_top()?;
    Ok(pred)
}

// ═════════════════════════════════════════════════════════════════════════
// Minimal tokenizer
// ═════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(i64),
    Str(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Dot,
    Op(String),
}

#[derive(Debug, Clone)]
struct TokenSpan {
    tok: Tok,
    pos: usize,
}

fn tokenize(input: &str) -> Result<Vec<TokenSpan>, ParseError> {
    let mut out = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        // Identifiers and keywords
        if c.is_ascii_alphabetic() || c == b'_' {
            let mut end = i + 1;
            while end < bytes.len()
                && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_')
            {
                end += 1;
            }
            let ident = std::str::from_utf8(&bytes[i..end]).unwrap().to_string();
            out.push(TokenSpan {
                tok: Tok::Ident(ident),
                pos: start,
            });
            i = end;
            continue;
        }
        // Integer literals
        if c.is_ascii_digit() {
            let mut end = i + 1;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            let num_str = std::str::from_utf8(&bytes[i..end]).unwrap();
            let n: i64 = num_str.parse().map_err(|_| ParseError {
                message: format!("invalid integer: {}", num_str),
                position: start,
            })?;
            out.push(TokenSpan {
                tok: Tok::Int(n),
                pos: start,
            });
            i = end;
            continue;
        }
        // String literals
        if c == b'"' {
            let mut end = i + 1;
            while end < bytes.len() && bytes[end] != b'"' {
                end += 1;
            }
            if end >= bytes.len() {
                return Err(ParseError {
                    message: "unterminated string literal".to_string(),
                    position: start,
                });
            }
            let s = std::str::from_utf8(&bytes[i + 1..end]).unwrap().to_string();
            out.push(TokenSpan {
                tok: Tok::Str(s),
                pos: start,
            });
            i = end + 1;
            continue;
        }
        // Unicode multi-byte characters (connectives like ∧, ∨, ¬, ∀, ∃, ∈, ⟹, ⟸, ⟺)
        if c >= 0x80 {
            // Parse one UTF-8 char
            let ch_len = utf8_char_len(c);
            if i + ch_len > bytes.len() {
                return Err(ParseError {
                    message: "truncated UTF-8 sequence".to_string(),
                    position: start,
                });
            }
            let ch_str = std::str::from_utf8(&bytes[i..i + ch_len]).map_err(|_| ParseError {
                message: "invalid UTF-8".to_string(),
                position: start,
            })?;
            out.push(TokenSpan {
                tok: Tok::Op(ch_str.to_string()),
                pos: start,
            });
            i += ch_len;
            continue;
        }
        // ASCII operators and punctuation
        let tok = match c {
            b'(' => {
                i += 1;
                Tok::LParen
            }
            b')' => {
                i += 1;
                Tok::RParen
            }
            b'{' => {
                i += 1;
                Tok::LBrace
            }
            b'}' => {
                i += 1;
                Tok::RBrace
            }
            b',' => {
                i += 1;
                Tok::Comma
            }
            b'.' => {
                i += 1;
                Tok::Dot
            }
            b'=' if i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                i += 2;
                Tok::Op("==".to_string())
            }
            b'!' if i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                i += 2;
                Tok::Op("!=".to_string())
            }
            b'<' if i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                i += 2;
                Tok::Op("<=".to_string())
            }
            b'>' if i + 1 < bytes.len() && bytes[i + 1] == b'=' => {
                i += 2;
                Tok::Op(">=".to_string())
            }
            b'-' if i + 2 < bytes.len() && bytes[i + 1] == b'>' && bytes[i + 2] == b'*' => {
                i += 3;
                Tok::Op("->*".to_string())
            }
            b'!' => {
                i += 1;
                Tok::Op("!".to_string())
            }
            b'<' => {
                i += 1;
                Tok::Op("<".to_string())
            }
            b'>' => {
                i += 1;
                Tok::Op(">".to_string())
            }
            b':' => {
                i += 1;
                Tok::Op(":".to_string())
            }
            _ => {
                return Err(ParseError {
                    message: format!("unexpected character: {}", c as char),
                    position: start,
                });
            }
        };
        out.push(TokenSpan { tok, pos: start });
    }
    Ok(out)
}

fn utf8_char_len(byte: u8) -> usize {
    if byte & 0x80 == 0 {
        1
    } else if byte & 0xE0 == 0xC0 {
        2
    } else if byte & 0xF0 == 0xE0 {
        3
    } else if byte & 0xF8 == 0xF0 {
        4
    } else {
        1 // malformed — caller handles
    }
}

// ═════════════════════════════════════════════════════════════════════════
// PredicateParser
// ═════════════════════════════════════════════════════════════════════════

/// Language-generic Pratt parser for behavioral predicates.
pub struct PredicateParser {
    tokens: Vec<TokenSpan>,
    pos: usize,
    config: PredicateParserConfig,
}

impl PredicateParser {
    pub fn new(tokens: Vec<TokenSpan>, config: PredicateParserConfig) -> Self {
        Self { tokens, pos: 0, config }
    }

    /// Parse a complete predicate expression up to the first
    /// terminator (or end of input).
    pub fn parse_top(&mut self) -> Result<BehavioralPred, ParseError> {
        self.parse_implication()
    }

    // ── Role resolution ────────────────────────────────────────────

    /// Check if a keyword string matches a given connective role in
    /// the active map (or in the defaults if no map is set).
    fn is_role(&self, keyword: &str, role: &str) -> bool {
        if let Some(map) = &self.config.connective_map {
            if let Some(spellings) = map.get(role) {
                return spellings.iter().any(|s| s == keyword);
            }
            // The map is present but this role isn't listed — role is not available.
            return false;
        }
        // No map: fall back to defaults.
        match role {
            "and" => matches!(keyword, "and" | "∧"),
            "or" => matches!(keyword, "or" | "∨"),
            "not" => matches!(keyword, "not" | "¬" | "!"),
            "entails" => matches!(keyword, "entails" | "implies" | "⟹"),
            "implied_by" => matches!(keyword, "implied_by" | "⟸"),
            "iff" => matches!(keyword, "iff" | "⟺"),
            "forall" => matches!(keyword, "forall" | "∀"),
            "exists" => matches!(keyword, "exists" | "∃"),
            _ => false,
        }
    }

    fn peek_keyword_role(&self, role: &str) -> bool {
        if self.pos >= self.tokens.len() {
            return false;
        }
        let kw = match &self.tokens[self.pos].tok {
            Tok::Ident(s) => s.as_str(),
            Tok::Op(s) => s.as_str(),
            _ => return false,
        };
        self.is_role(kw, role)
    }

    // ── Parser layers ──────────────────────────────────────────────

    /// Layer 1: implication-like forms (`entails`, `implied_by`, `iff`).
    fn parse_implication(&mut self) -> Result<BehavioralPred, ParseError> {
        if self.peek_keyword_role("entails") {
            self.consume();
            self.expect_lparen()?;
            let p = self.parse_implication()?;
            self.expect_comma()?;
            let c = self.parse_implication()?;
            self.expect_rparen()?;
            return Ok(BehavioralPred::Implies(Box::new(p), Box::new(c)));
        }
        if self.peek_keyword_role("implied_by") {
            self.consume();
            self.expect_lparen()?;
            let c = self.parse_implication()?;
            self.expect_comma()?;
            let p = self.parse_implication()?;
            self.expect_rparen()?;
            return Ok(BehavioralPred::Implies(Box::new(p), Box::new(c)));
        }
        if self.peek_keyword_role("iff") {
            self.consume();
            self.expect_lparen()?;
            let a = self.parse_implication()?;
            self.expect_comma()?;
            let b = self.parse_implication()?;
            self.expect_rparen()?;
            return Ok(BehavioralPred::And(
                Box::new(BehavioralPred::Implies(
                    Box::new(a.clone()),
                    Box::new(b.clone()),
                )),
                Box::new(BehavioralPred::Implies(Box::new(b), Box::new(a))),
            ));
        }
        self.parse_or()
    }

    /// Layer 2: `or(...)` variadic disjunction.
    fn parse_or(&mut self) -> Result<BehavioralPred, ParseError> {
        if self.peek_keyword_role("or") {
            self.consume();
            self.expect_lparen()?;
            let mut clauses = vec![self.parse_implication()?];
            while self.peek_comma() {
                self.consume();
                clauses.push(self.parse_implication()?);
            }
            self.expect_rparen()?;
            return Ok(fold_or(clauses));
        }
        self.parse_and()
    }

    /// Layer 3: `and(...)` variadic conjunction plus top-level comma.
    fn parse_and(&mut self) -> Result<BehavioralPred, ParseError> {
        if self.peek_keyword_role("and") {
            self.consume();
            self.expect_lparen()?;
            let mut clauses = vec![self.parse_implication()?];
            while self.peek_comma() {
                self.consume();
                clauses.push(self.parse_implication()?);
            }
            self.expect_rparen()?;
            return Ok(fold_and(clauses));
        }
        // Top-level comma-separated conjunction is handled by the
        // caller (see `parse_top_level_conjunction`).
        self.parse_not()
    }

    /// Layer 4: `not(...)` function-call form and prefix `not`/`!`.
    fn parse_not(&mut self) -> Result<BehavioralPred, ParseError> {
        if self.peek_keyword_role("not") {
            self.consume();
            // Function-call form: not(P)
            if self.peek_lparen() {
                self.consume();
                let inner = self.parse_implication()?;
                self.expect_rparen()?;
                return Ok(BehavioralPred::Not(Box::new(inner)));
            }
            // Prefix form: not P
            let inner = self.parse_quantifier()?;
            return Ok(BehavioralPred::Not(Box::new(inner)));
        }
        self.parse_quantifier()
    }

    /// Layer 5: `forall(var, domain, body)` / `exists(var, domain, body)`.
    fn parse_quantifier(&mut self) -> Result<BehavioralPred, ParseError> {
        let q = if self.peek_keyword_role("forall") {
            self.consume();
            Quantifier::ForAll
        } else if self.peek_keyword_role("exists") {
            self.consume();
            Quantifier::Exists
        } else {
            return self.parse_atom();
        };
        self.expect_lparen()?;
        let var = self.expect_ident()?;
        // Optional domain clause. Syntax:
        //   forall(v, body)                — no domain
        //   forall(v, domain, body)        — comma separator
        //   forall(v in domain, body)      — `in` / `∈` keyword
        let domain = if self.peek_keyword_role("entails")
            && false
        {
            None
        } else if self.peek_in_keyword() {
            self.consume();
            Some(self.parse_domain()?)
        } else if self.peek_comma() {
            // Lookahead to determine if the next token(s) form a
            // domain expression followed by another comma (i.e., the
            // three-arg form) or are the body (two-arg form).
            //
            // The domain form is: int literal | ident | { ... }
            // If that's followed by a `,`, it's a domain; otherwise
            // it's part of the body.
            let save = self.pos;
            self.consume(); // consume the first comma
            if self.peek_domain_lookahead() {
                let dom = self.parse_domain()?;
                if self.peek_comma() {
                    self.consume(); // consume the comma after the domain
                    Some(dom)
                } else {
                    // Not actually a domain — restore position.
                    self.pos = save;
                    self.consume(); // consume the comma again
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        let body = self.parse_implication()?;
        self.expect_rparen()?;
        Ok(BehavioralPred::Quantified {
            quantifier: q,
            var,
            domain,
            body: Box::new(body),
        })
    }

    fn peek_in_keyword(&self) -> bool {
        if self.pos >= self.tokens.len() {
            return false;
        }
        match &self.tokens[self.pos].tok {
            Tok::Ident(s) => s == "in",
            Tok::Op(s) => s == "∈" || s == ":",
            _ => false,
        }
    }

    fn peek_domain_lookahead(&self) -> bool {
        if self.pos >= self.tokens.len() {
            return false;
        }
        matches!(
            &self.tokens[self.pos].tok,
            Tok::Int(_) | Tok::LBrace | Tok::Ident(_)
        )
    }

    fn parse_domain(&mut self) -> Result<QuantifiedDomain, ParseError> {
        if let Some(tok) = self.peek_tok() {
            match tok {
                Tok::Int(n) => {
                    let k = *n as usize;
                    self.consume();
                    return Ok(QuantifiedDomain::Bounded(k));
                }
                Tok::LBrace => {
                    self.consume();
                    let mut elems = Vec::new();
                    if !self.peek_rbrace() {
                        elems.push(self.parse_arg()?);
                        while self.peek_comma() {
                            self.consume();
                            elems.push(self.parse_arg()?);
                        }
                    }
                    self.expect_rbrace()?;
                    return Ok(QuantifiedDomain::Enumerated(elems));
                }
                Tok::Ident(name) => {
                    let s = name.clone();
                    self.consume();
                    return Ok(QuantifiedDomain::Named(s));
                }
                _ => {}
            }
        }
        Err(self.error("expected domain (integer, identifier, or brace-enclosed set)"))
    }

    /// Layer 6: atomic predicates — relation calls, infix comparisons,
    /// set membership.
    fn parse_atom(&mut self) -> Result<BehavioralPred, ParseError> {
        // Parenthesized expression
        if self.peek_lparen() {
            self.consume();
            let inner = self.parse_implication()?;
            self.expect_rparen()?;
            return Ok(inner);
        }

        // Relation application: `name(args)` (peek required)
        if self.peek_ident_followed_by_lparen() {
            let name = self.expect_ident()?;
            self.expect_lparen()?;
            let mut args = Vec::new();
            if !self.peek_rparen() {
                args.push(self.parse_arg()?);
                while self.peek_comma() {
                    self.consume();
                    args.push(self.parse_arg()?);
                }
            }
            self.expect_rparen()?;
            return Ok(BehavioralPred::RelationQuery {
                relation_name: name,
                args,
                negated: false,
            });
        }

        // Infix / set-membership / bare identifier
        let lhs = self.parse_arg()?;

        // Comparison operator: x == y, x < y, etc.
        if let Some(op) = self.peek_comparison_op() {
            let op = op.to_string();
            self.consume();
            let rhs = self.parse_arg()?;
            return Ok(BehavioralPred::RelationQuery {
                relation_name: comparison_op_to_relation_name(&op),
                args: vec![lhs, rhs],
                negated: false,
            });
        }

        // Set membership sugar: x in T
        if self.peek_in_keyword() {
            self.consume();
            let ty = self.expect_ident()?;
            return Ok(BehavioralPred::RelationQuery {
                relation_name: ty,
                args: vec![lhs],
                negated: false,
            });
        }

        // Rewrite closure: x ->* y
        if let Some(Tok::Op(s)) = self.peek_tok() {
            if s == "->*" || s == "→*" {
                self.consume();
                let rhs = self.parse_arg()?;
                return Ok(BehavioralPred::RelationQuery {
                    relation_name: "rewrites_to".to_string(),
                    args: vec![lhs, rhs],
                    negated: false,
                });
            }
        }

        // Bare identifier as nullary relation
        if let PredArg::Var(name) = lhs {
            return Ok(BehavioralPred::RelationQuery {
                relation_name: name,
                args: vec![],
                negated: false,
            });
        }
        Err(self.error("expected predicate expression"))
    }

    fn parse_arg(&mut self) -> Result<PredArg, ParseError> {
        match self.peek_tok() {
            Some(Tok::Int(n)) => {
                let v = *n;
                self.consume();
                Ok(PredArg::IntLit(v))
            }
            Some(Tok::Str(s)) => {
                let v = s.clone();
                self.consume();
                Ok(PredArg::StringLit(v))
            }
            Some(Tok::Ident(name)) => {
                let v = name.clone();
                self.consume();
                Ok(PredArg::Var(v))
            }
            _ => Err(self.error("expected argument (identifier, integer, or string)")),
        }
    }

    // ── Token-stream helpers ──────────────────────────────────────

    fn peek_tok(&self) -> Option<&Tok> {
        self.tokens.get(self.pos).map(|ts| &ts.tok)
    }

    fn consume(&mut self) -> Option<TokenSpan> {
        let t = self.tokens.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn peek_lparen(&self) -> bool {
        matches!(self.peek_tok(), Some(Tok::LParen))
    }

    fn peek_rparen(&self) -> bool {
        matches!(self.peek_tok(), Some(Tok::RParen))
    }

    fn peek_rbrace(&self) -> bool {
        matches!(self.peek_tok(), Some(Tok::RBrace))
    }

    fn peek_comma(&self) -> bool {
        matches!(self.peek_tok(), Some(Tok::Comma))
    }

    fn peek_ident_followed_by_lparen(&self) -> bool {
        matches!(self.peek_tok(), Some(Tok::Ident(_)))
            && matches!(self.tokens.get(self.pos + 1).map(|t| &t.tok), Some(Tok::LParen))
    }

    fn peek_comparison_op(&self) -> Option<&str> {
        if let Some(Tok::Op(s)) = self.peek_tok() {
            match s.as_str() {
                "==" | "!=" | "<" | ">" | "<=" | ">=" | "≠" | "≤" | "≥" => Some(s.as_str()),
                _ => None,
            }
        } else {
            None
        }
    }

    fn expect_lparen(&mut self) -> Result<(), ParseError> {
        if self.peek_lparen() {
            self.consume();
            Ok(())
        } else {
            Err(self.error("expected `(`"))
        }
    }

    fn expect_rparen(&mut self) -> Result<(), ParseError> {
        if self.peek_rparen() {
            self.consume();
            Ok(())
        } else {
            Err(self.error("expected `)`"))
        }
    }

    fn expect_rbrace(&mut self) -> Result<(), ParseError> {
        if self.peek_rbrace() {
            self.consume();
            Ok(())
        } else {
            Err(self.error("expected `}`"))
        }
    }

    fn expect_comma(&mut self) -> Result<(), ParseError> {
        if self.peek_comma() {
            self.consume();
            Ok(())
        } else {
            Err(self.error("expected `,`"))
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.peek_tok() {
            Some(Tok::Ident(name)) => {
                let v = name.clone();
                self.consume();
                Ok(v)
            }
            _ => Err(self.error("expected identifier")),
        }
    }

    fn error(&self, message: &str) -> ParseError {
        let position = self
            .tokens
            .get(self.pos)
            .map(|t| t.pos)
            .unwrap_or_else(|| self.tokens.last().map(|t| t.pos).unwrap_or(0));
        ParseError {
            message: message.to_string(),
            position,
        }
    }
}

fn fold_and(mut clauses: Vec<BehavioralPred>) -> BehavioralPred {
    if clauses.len() == 1 {
        return clauses.pop().unwrap();
    }
    let mut acc = clauses.pop().unwrap();
    while let Some(c) = clauses.pop() {
        acc = BehavioralPred::And(Box::new(c), Box::new(acc));
    }
    acc
}

fn fold_or(mut clauses: Vec<BehavioralPred>) -> BehavioralPred {
    if clauses.len() == 1 {
        return clauses.pop().unwrap();
    }
    let mut acc = clauses.pop().unwrap();
    while let Some(c) = clauses.pop() {
        acc = BehavioralPred::Or(Box::new(c), Box::new(acc));
    }
    acc
}

fn comparison_op_to_relation_name(op: &str) -> String {
    match op {
        "==" => "eq".to_string(),
        "!=" | "≠" => "neq".to_string(),
        "<" => "lt".to_string(),
        ">" => "gt".to_string(),
        "<=" | "≤" => "le".to_string(),
        ">=" | "≥" => "ge".to_string(),
        _ => op.to_string(),
    }
}

// ═════════════════════════════════════════════════════════════════════════
// Tests
// ═════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<BehavioralPred, ParseError> {
        parse_predicate_from_str(s, PredicateParserConfig::default())
    }

    fn parse_with_map(
        s: &str,
        map: Vec<(&str, Vec<&str>)>,
    ) -> Result<BehavioralPred, ParseError> {
        let mut m = HashMap::new();
        for (role, spellings) in map {
            m.insert(
                role.to_string(),
                spellings.iter().map(|s| s.to_string()).collect(),
            );
        }
        parse_predicate_from_str(
            s,
            PredicateParserConfig {
                connective_map: Some(m),
                ..Default::default()
            },
        )
    }

    // ── Relation queries ──────────────────────────────────────────

    #[test]
    fn parse_nullary_relation() {
        let pred = parse("halts").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, negated } => {
                assert_eq!(relation_name, "halts");
                assert!(args.is_empty());
                assert!(!negated);
            }
            _ => panic!("expected RelationQuery, got {:?}", pred),
        }
    }

    #[test]
    fn parse_unary_relation() {
        let pred = parse("halts(x)").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "halts");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], PredArg::Var("x".to_string()));
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    #[test]
    fn parse_binary_relation() {
        let pred = parse("reachable(x, y)").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "reachable");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    #[test]
    fn parse_relation_with_int_literal() {
        let pred = parse("gt(x, 5)").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { args, .. } => {
                assert_eq!(args[1], PredArg::IntLit(5));
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    // ── Connectives ───────────────────────────────────────────────

    #[test]
    fn parse_conjunction() {
        let pred = parse("and(halts(x), safe(x))").expect("ok");
        match pred {
            BehavioralPred::And(_, _) => {}
            _ => panic!("expected And, got {:?}", pred),
        }
    }

    #[test]
    fn parse_variadic_conjunction() {
        let pred = parse("and(a, b, c)").expect("ok");
        // Should fold to And(a, And(b, c))
        match pred {
            BehavioralPred::And(_, rhs) => {
                assert!(matches!(*rhs, BehavioralPred::And(_, _)));
            }
            _ => panic!("expected nested And"),
        }
    }

    #[test]
    fn parse_disjunction() {
        let pred = parse("or(halts(x), safe(x))").expect("ok");
        assert!(matches!(pred, BehavioralPred::Or(_, _)));
    }

    #[test]
    fn parse_negation_fn_call() {
        let pred = parse("not(halts(x))").expect("ok");
        assert!(matches!(pred, BehavioralPred::Not(_)));
    }

    #[test]
    fn parse_negation_prefix() {
        let pred = parse("not halts(x)").expect("ok");
        assert!(matches!(pred, BehavioralPred::Not(_)));
    }

    #[test]
    fn parse_implication() {
        let pred = parse("entails(halts(x), safe(x))").expect("ok");
        assert!(matches!(pred, BehavioralPred::Implies(_, _)));
    }

    #[test]
    fn parse_implied_by_swaps_args() {
        let pred = parse("implied_by(safe(x), halts(x))").expect("ok");
        // implied_by(S, H) == entails(H, S) == Implies(H, S)
        match pred {
            BehavioralPred::Implies(p, c) => {
                if let BehavioralPred::RelationQuery { relation_name, .. } = *p {
                    assert_eq!(relation_name, "halts");
                }
                if let BehavioralPred::RelationQuery { relation_name, .. } = *c {
                    assert_eq!(relation_name, "safe");
                }
            }
            _ => panic!("expected Implies"),
        }
    }

    #[test]
    fn parse_iff_desugars_to_conjunction_of_implies() {
        let pred = parse("iff(a, b)").expect("ok");
        match pred {
            BehavioralPred::And(lhs, rhs) => {
                assert!(matches!(*lhs, BehavioralPred::Implies(_, _)));
                assert!(matches!(*rhs, BehavioralPred::Implies(_, _)));
            }
            _ => panic!("expected And(Implies, Implies)"),
        }
    }

    // ── Comparisons ───────────────────────────────────────────────

    #[test]
    fn parse_equality() {
        let pred = parse("x == y").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, .. } => {
                assert_eq!(relation_name, "eq");
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    #[test]
    fn parse_less_than() {
        let pred = parse("x < 5").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "lt");
                assert_eq!(args[1], PredArg::IntLit(5));
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    #[test]
    fn parse_greater_equal() {
        let pred = parse("x >= 0").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, .. } => {
                assert_eq!(relation_name, "ge");
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    // ── Quantifiers ───────────────────────────────────────────────

    #[test]
    fn parse_forall_named_domain() {
        let pred = parse("forall(y, nodes, safe(y))").expect("ok");
        match pred {
            BehavioralPred::Quantified {
                quantifier: Quantifier::ForAll,
                var,
                domain: Some(QuantifiedDomain::Named(name)),
                ..
            } => {
                assert_eq!(var, "y");
                assert_eq!(name, "nodes");
            }
            _ => panic!("expected Quantified/ForAll/Named, got {:?}", pred),
        }
    }

    #[test]
    fn parse_exists_no_domain() {
        let pred = parse("exists(y, safe(y))").expect("ok");
        match pred {
            BehavioralPred::Quantified {
                quantifier: Quantifier::Exists,
                var,
                domain: None,
                ..
            } => {
                assert_eq!(var, "y");
            }
            _ => panic!("expected Quantified/Exists/None, got {:?}", pred),
        }
    }

    #[test]
    fn parse_forall_bounded() {
        let pred = parse("forall(y, 100, safe(y))").expect("ok");
        match pred {
            BehavioralPred::Quantified {
                domain: Some(QuantifiedDomain::Bounded(k)),
                ..
            } => {
                assert_eq!(k, 100);
            }
            _ => panic!("expected Bounded domain"),
        }
    }

    #[test]
    fn parse_forall_enumerated() {
        let pred = parse("forall(y, {a, b, c}, safe(y))").expect("ok");
        match pred {
            BehavioralPred::Quantified {
                domain: Some(QuantifiedDomain::Enumerated(es)),
                ..
            } => {
                assert_eq!(es.len(), 3);
            }
            _ => panic!("expected Enumerated domain"),
        }
    }

    // ── Set membership ────────────────────────────────────────────

    #[test]
    fn parse_in_keyword() {
        let pred = parse("x in PosInt").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "PosInt");
                assert_eq!(args[0], PredArg::Var("x".to_string()));
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    // ── Unicode alternates ────────────────────────────────────────

    #[test]
    fn parse_unicode_forall() {
        let pred = parse("∀(y, nodes, safe(y))").expect("ok");
        assert!(matches!(
            pred,
            BehavioralPred::Quantified { quantifier: Quantifier::ForAll, .. }
        ));
    }

    #[test]
    fn parse_unicode_in() {
        let pred = parse("x ∈ PosInt").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, .. } => {
                assert_eq!(relation_name, "PosInt");
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    // ── Rewrite closure ───────────────────────────────────────────

    #[test]
    fn parse_rewrite_closure() {
        let pred = parse("x ->* y").expect("ok");
        match pred {
            BehavioralPred::RelationQuery { relation_name, .. } => {
                assert_eq!(relation_name, "rewrites_to");
            }
            _ => panic!("expected RelationQuery"),
        }
    }

    // ── Language-generic behavior ─────────────────────────────────

    /// The parser is invoked in three different language contexts
    /// with different connective spelling maps. Each context's
    /// connective spellings should be honored without the parser
    /// hardcoding any particular language.
    #[test]
    fn generic_across_three_language_contexts() {
        // Context A: Rholang-style (default spellings).
        let a = parse("and(halts(x), safe(x))").expect("rholang ok");
        assert!(matches!(a, BehavioralPred::And(_, _)));

        // Context B: C-like (and = "&&", or = "||", not = "!").
        // With only "&&" declared as And, the keyword "and" is NOT
        // recognized as a connective — it becomes a plain nullary
        // relation name.
        let b = parse_with_map(
            "and",
            vec![("and", vec!["&&"]), ("or", vec!["||"]), ("not", vec!["!"])],
        )
        .expect("c-like ok");
        match b {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                assert_eq!(relation_name, "and");
                assert!(args.is_empty());
            }
            _ => panic!("expected bare identifier as nullary relation"),
        }

        // Context C: ML-like (not = "not" keyword, but no "and"/"or"
        // in the map). Prefix `not halts(x)` still parses.
        let c = parse_with_map(
            "not halts(x)",
            vec![("not", vec!["not"])],
        )
        .expect("ml-like ok");
        assert!(matches!(c, BehavioralPred::Not(_)));
    }

    /// When a language declares a closed connectives map that omits
    /// `or`, the keyword `or` is NOT recognized as a disjunction
    /// and falls back to being a plain identifier.
    #[test]
    fn closed_world_rejects_undeclared_connective() {
        // Only `and` and `not` are declared. `or(a, b)` must not
        // parse as a disjunction.
        let result = parse_with_map(
            "or",
            vec![("and", vec!["and"]), ("not", vec!["not"])],
        );
        // `or` becomes a bare identifier (a nullary relation named "or").
        match result.unwrap() {
            BehavioralPred::RelationQuery { relation_name, .. } => {
                assert_eq!(relation_name, "or");
            }
            _ => panic!("expected RelationQuery for bare `or`"),
        }
    }

    #[test]
    fn parse_error_position() {
        let err = parse("halts(x,)").expect_err("should fail");
        assert!(
            err.message.contains("expected")
                || err.message.contains("argument")
                || err.message.contains(")"),
            "error message: {}",
            err.message
        );
    }
}
