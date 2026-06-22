//! OSLF Phase 5 — a CUSTOM TEST-ONLY letprop language, end-to-end.
//!
//! The *official* letprop surface syntax is undecided (a tracked follow-up). For
//! integration testing, this defines a small, self-contained letprop
//! semantic-predicate syntax + a recursive-descent parser into the prattail
//! [`RecursivePredicate`], then drives it through the live decision wired in
//! Phase 5 (`parity_tree::decide_recursive_predicate`):
//!
//!   source string → parse → RecursivePredicate → μ/ν → PATA → emptiness verdict
//!
//! This proves the downstream pipeline is **ready** for whatever official surface
//! is later chosen: the official parser only has to produce the SAME
//! `RecursivePredicate`, and everything below (lowering, PATA, decision, the
//! `LetpropPataWiringSound.v` soundness) applies unchanged. It is TEST-ONLY, so
//! production `ast/` and the grammar are untouched (no parser drift).
//!
//! Test grammar (one definition per call):
//! ```text
//!   letprop  ::= "letprop" NAME "(" params? ")" "=" expr
//!   expr     ::= implies
//!   implies  ::= or ( "=>" or )*          (right-associative)
//!   or       ::= and ( "|" and )*
//!   and      ::= not ( "&" not )*
//!   not      ::= "~" not | atom
//!   atom     ::= "true" | "false" | NAME "(" args? ")" | "(" expr ")"
//! ```
//! An applied name equal to the enclosing predicate name becomes a
//! [`LetPropExpr::Recursive`]; any other becomes a [`LetPropExpr::Atom`].
#![cfg(feature = "oslf-letprop")]

use mettail_prattail::letprop::{LetPropExpr, RecursivePredicate};
use mettail_prattail::parity_tree::decide_recursive_predicate;

// ── Tokenizer ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    Comma,
    Eq,
    Arrow, // =>
    Or,    // |
    And,   // &
    Not,   // ~
}

fn tokenize(src: &str) -> Vec<Tok> {
    let mut toks = Vec::with_capacity(src.len() / 2 + 1);
    let bytes = src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        match c {
            c if c.is_whitespace() => i += 1,
            '(' => {
                toks.push(Tok::LParen);
                i += 1;
            },
            ')' => {
                toks.push(Tok::RParen);
                i += 1;
            },
            ',' => {
                toks.push(Tok::Comma);
                i += 1;
            },
            '|' => {
                toks.push(Tok::Or);
                i += 1;
            },
            '&' => {
                toks.push(Tok::And);
                i += 1;
            },
            '~' => {
                toks.push(Tok::Not);
                i += 1;
            },
            '=' => {
                if i + 1 < bytes.len() && bytes[i + 1] as char == '>' {
                    toks.push(Tok::Arrow);
                    i += 2;
                } else {
                    toks.push(Tok::Eq);
                    i += 1;
                }
            },
            c if c.is_alphanumeric() || c == '_' => {
                let start = i;
                while i < bytes.len()
                    && ((bytes[i] as char).is_alphanumeric() || bytes[i] as char == '_')
                {
                    i += 1;
                }
                toks.push(Tok::Ident(src[start..i].to_string()));
            },
            other => panic!("letprop test lexer: unexpected character {other:?}"),
        }
    }
    toks
}

// ── Recursive-descent parser ─────────────────────────────────────────────────

struct Parser<'a> {
    toks: &'a [Tok],
    pos: usize,
    /// The enclosing predicate name, so an applied `name(args)` is recognized as
    /// a recursive self-reference rather than a relation atom.
    self_name: String,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        self.pos += 1;
        t
    }

    fn expect(&mut self, want: &Tok) {
        let got = self.bump();
        assert_eq!(&got, want, "letprop test parser: expected {want:?}, got {got:?}");
    }

    fn ident(&mut self) -> String {
        match self.bump() {
            Tok::Ident(s) => s,
            other => panic!("letprop test parser: expected identifier, got {other:?}"),
        }
    }

    /// `NAME ("," NAME)*` inside parens (possibly empty).
    fn name_list(&mut self) -> Vec<String> {
        let mut names = Vec::new();
        if matches!(self.peek(), Some(Tok::RParen)) {
            return names;
        }
        names.push(self.ident());
        while matches!(self.peek(), Some(Tok::Comma)) {
            self.bump();
            names.push(self.ident());
        }
        names
    }

    fn expr(&mut self) -> LetPropExpr {
        self.implies()
    }

    fn implies(&mut self) -> LetPropExpr {
        let lhs = self.or();
        if matches!(self.peek(), Some(Tok::Arrow)) {
            self.bump();
            let rhs = self.implies(); // right-associative
            LetPropExpr::Implies(Box::new(lhs), Box::new(rhs))
        } else {
            lhs
        }
    }

    fn or(&mut self) -> LetPropExpr {
        let mut acc = self.and();
        while matches!(self.peek(), Some(Tok::Or)) {
            self.bump();
            let rhs = self.and();
            acc = LetPropExpr::Or(Box::new(acc), Box::new(rhs));
        }
        acc
    }

    fn and(&mut self) -> LetPropExpr {
        let mut acc = self.not();
        while matches!(self.peek(), Some(Tok::And)) {
            self.bump();
            let rhs = self.not();
            acc = LetPropExpr::And(Box::new(acc), Box::new(rhs));
        }
        acc
    }

    fn not(&mut self) -> LetPropExpr {
        if matches!(self.peek(), Some(Tok::Not)) {
            self.bump();
            LetPropExpr::Not(Box::new(self.not()))
        } else {
            self.atom()
        }
    }

    fn atom(&mut self) -> LetPropExpr {
        match self.peek() {
            Some(Tok::LParen) => {
                self.bump();
                let inner = self.expr();
                self.expect(&Tok::RParen);
                inner
            },
            Some(Tok::Ident(_)) => {
                let name = self.ident();
                match name.as_str() {
                    "true" => LetPropExpr::True,
                    "false" => LetPropExpr::False,
                    _ => {
                        self.expect(&Tok::LParen);
                        let args = self.name_list();
                        self.expect(&Tok::RParen);
                        if name == self.self_name {
                            LetPropExpr::Recursive { args }
                        } else {
                            LetPropExpr::Atom { relation: name, args }
                        }
                    },
                }
            },
            other => panic!("letprop test parser: expected atom, got {other:?}"),
        }
    }
}

/// Parse one `letprop NAME(params) = body` definition into a [`RecursivePredicate`].
fn parse_letprop(src: &str) -> RecursivePredicate {
    let toks = tokenize(src);
    // `letprop` NAME `(` params `)` `=` expr
    let mut p = Parser { toks: &toks, pos: 0, self_name: String::new() };
    let kw = p.ident();
    assert_eq!(kw, "letprop", "letprop test parser: definitions must start with `letprop`");
    let name = p.ident();
    p.expect(&Tok::LParen);
    let params = p.name_list();
    p.expect(&Tok::RParen);
    p.expect(&Tok::Eq);
    p.self_name = name.clone();
    let body = p.expr();
    assert!(p.peek().is_none(), "letprop test parser: trailing tokens after body");
    RecursivePredicate { name, params, body }
}

// ── End-to-end tests: source → parse → RecursivePredicate → PATA → verdict ────

#[test]
fn parser_produces_the_expected_recursive_predicate() {
    // The CONTRACT the official surface must satisfy: this exact source parses to
    // this exact RecursivePredicate (the input to the proven downstream).
    let rp = parse_letprop("letprop reachable(x) = edge(x) | reachable(x)");
    assert_eq!(
        rp,
        RecursivePredicate {
            name: "reachable".to_string(),
            params: vec!["x".to_string()],
            body: LetPropExpr::Or(
                Box::new(LetPropExpr::Atom {
                    relation: "edge".to_string(),
                    args: vec!["x".to_string()],
                }),
                Box::new(LetPropExpr::Recursive { args: vec!["x".to_string()] }),
            ),
        }
    );
}

#[test]
fn reachable_is_satisfiable_end_to_end() {
    // μX. edge(x) ∨ X — a least fixpoint WITH a base case (`edge`): the PATA is
    // non-empty, so the behavioral type is satisfiable.
    let rp = parse_letprop("letprop reachable(x) = edge(x) | reachable(x)");
    assert!(
        decide_recursive_predicate(&rp),
        "reachable has a base case (edge) — its PATA must be non-empty (satisfiable)"
    );
}

#[test]
fn spin_is_unsatisfiable_end_to_end() {
    // μX. X — a least fixpoint with NO base case: the least solution is ∅, the
    // PATA is empty, so the behavioral type is a dead/unsatisfiable type.
    let rp = parse_letprop("letprop spin(x) = spin(x)");
    assert!(
        !decide_recursive_predicate(&rp),
        "spin is a baseless fixpoint — its PATA must be empty (unsatisfiable / dead type)"
    );
}

#[test]
fn nested_connectives_and_precedence_parse_and_decide() {
    // Exercises precedence (`~` > `&` > `|` > `=>`), parens, and a guarded
    // recursion `terminates(x) = done(x) | (step(x) & terminates(x))`.
    let rp = parse_letprop("letprop terminates(x) = done(x) | ( step(x) & terminates(x) )");
    // `|` binds looser than `&`, so the body is Or(done, And(step, Recursive)).
    assert_eq!(
        rp.body,
        LetPropExpr::Or(
            Box::new(LetPropExpr::Atom {
                relation: "done".to_string(),
                args: vec!["x".to_string()],
            }),
            Box::new(LetPropExpr::And(
                Box::new(LetPropExpr::Atom {
                    relation: "step".to_string(),
                    args: vec!["x".to_string()],
                }),
                Box::new(LetPropExpr::Recursive { args: vec!["x".to_string()] }),
            )),
        )
    );
    // It has a base case (`done`), so it is satisfiable.
    assert!(decide_recursive_predicate(&rp));
}
