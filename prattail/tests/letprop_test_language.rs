//! OSLF Phase 5 — a CUSTOM TEST-ONLY letprop language, end-to-end.
//!
//! The *official* letprop surface syntax is undecided (a tracked follow-up). This
//! test exercises the **proposed** syntax from
//! `docs/design/predicated-types.md` §"Recursive Predicates (letprop)":
//!
//! ```text
//!   letprop safe(x) = base(x) ∨ (step(x) ∧ safe(x))
//! ```
//!
//! i.e. `letprop NAME "(" params ")" "=" body`, where the body is built from
//! relation atoms `R(args)`, the connectives `∨` / `∧` / `¬` / `⇒`, and recursive
//! self-references `NAME(args)`. A test-scoped recursive-descent parser turns that
//! surface into the prattail [`RecursivePredicate`] and drives it through the live
//! Phase-5 decision (`parity_tree::decide_recursive_predicate`):
//!
//!   source string → parse → RecursivePredicate → μ/ν → PATA → emptiness verdict
//!
//! This pins the `surface → RecursivePredicate` contract the official syntax must
//! satisfy: the official parser only has to produce the SAME `RecursivePredicate`,
//! and everything below (lowering, PATA, decision, `LetpropPataWiringSound.v`)
//! applies unchanged. It is TEST-ONLY, so production `ast/` is untouched.
//!
//! ⚠ GAP for the official-surface phase (task #26): the proposed syntax also
//! admits a quantified form — `letprop halt x = forall(x', ¬rewrites_to(x, x'))`
//! (predicated-types.md:5784) — but `LetPropExpr` has **no** `Forall`/`Exists`
//! variant, so that fragment is not yet representable. This test exercises only
//! the connective + recursive fragment that `LetPropExpr` supports today; the
//! official surface will need `LetPropExpr` extended with quantifiers (or the
//! quantifiers lowered separately) to cover the `halt`-style proposal.
//!
//! The lenient tokenizer accepts the proposed Unicode connectives (`∨`/`∧`/`¬`/`⇒`)
//! as well as their ASCII spellings (`|`/`&`/`~`/`=>`), and `'` in identifiers.
#![cfg(feature = "oslf-letprop")]

use mettail_prattail::letprop::{LetPropExpr, RecursivePredicate};
use mettail_prattail::parity_tree::decide_recursive_predicate;

// ── Tokenizer (char-based: the proposed connectives are multi-byte Unicode) ───

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    Comma,
    Eq,
    Arrow, // ⇒ / =>
    Or,    // ∨ / |
    And,   // ∧ / &
    Not,   // ¬ / ~
}

fn tokenize(src: &str) -> Vec<Tok> {
    let chars: Vec<char> = src.chars().collect();
    let mut toks = Vec::with_capacity(chars.len() / 2 + 1);
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
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
            '∨' | '|' => {
                toks.push(Tok::Or);
                i += 1;
            },
            '∧' | '&' => {
                toks.push(Tok::And);
                i += 1;
            },
            '¬' | '~' => {
                toks.push(Tok::Not);
                i += 1;
            },
            '⇒' => {
                toks.push(Tok::Arrow);
                i += 1;
            },
            '=' => {
                if i + 1 < chars.len() && chars[i + 1] == '>' {
                    toks.push(Tok::Arrow);
                    i += 2;
                } else {
                    toks.push(Tok::Eq);
                    i += 1;
                }
            },
            c if c.is_alphanumeric() || c == '_' || c == '\'' => {
                let start = i;
                while i < chars.len()
                    && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '\'')
                {
                    i += 1;
                }
                toks.push(Tok::Ident(chars[start..i].iter().collect()));
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

/// Parse one `letprop NAME(params) = body` definition (the proposed
/// `predicated-types.md` surface) into a [`RecursivePredicate`].
fn parse_letprop(src: &str) -> RecursivePredicate {
    let toks = tokenize(src);
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
    // The CONTRACT the official surface must satisfy: this exact proposed source
    // parses to this exact RecursivePredicate (the input to the proven downstream).
    let rp = parse_letprop("letprop reachable(x) = edge(x) ∨ reachable(x)");
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
    let rp = parse_letprop("letprop reachable(x) = edge(x) ∨ reachable(x)");
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
    // The proposed `safe(x) = base(x) ∨ (step(x) ∧ safe(x))` shape: exercises
    // precedence (`¬` > `∧` > `∨` > `⇒`), parens, and a guarded recursion.
    let rp = parse_letprop("letprop terminates(x) = done(x) ∨ ( step(x) ∧ terminates(x) )");
    // `∨` binds looser than `∧`, so the body is Or(done, And(step, Recursive)).
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

#[test]
fn ascii_connectives_are_accepted_too() {
    // The tokenizer is lenient: the ASCII spellings parse to the same AST as the
    // proposed Unicode connectives (so the test does not depend on the final
    // glyph choice the official surface will fix).
    let unicode = parse_letprop("letprop reachable(x) = edge(x) ∨ reachable(x)");
    let ascii = parse_letprop("letprop reachable(x) = edge(x) | reachable(x)");
    assert_eq!(unicode, ascii);
}
