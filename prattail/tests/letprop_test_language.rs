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
//! GAP STATUS (task #26): the two formerly-open gaps are now CLOSED.
//!
//! - **Quantifiers.** The proposed quantified form
//!   `letprop halt(x) = forall(x', ¬rewrites_to(x, x'))`
//!   (predicated-types.md:5823) is now representable: `LetPropExpr` carries
//!   `Forall`/`Exists`, lowered to the PATA tree engine's `Box`/`Diamond`
//!   modal operators (`νX. □_{→*}(¬X)`, predicated-types.md:5836). A
//!   quantifier-only (non-recursive) body lowers via §4-(B) as the modal body
//!   wrapped in `Nu` instead of erroring `NotRecursive`.
//! - **Argument substitution.** The proposed fixpoint
//!   `letprop safe(x) = base(x) ∨ (step(x) ∧ safe(child(x)))`
//!   (predicated-types.md:8202) is now representable: relation/recursive
//!   arguments are structured `LetPropArg`s (`Var` | `App`), so `safe(child(x))`
//!   and `rewrites_to(x, x')` parse. The μ-calculus lowering still DROPS
//!   arguments (propositional, decision-invariant); they are retained on the AST
//!   for the runtime-dispatch contract.
//!
//! This test now exercises the FULL proposed fragment — connectives, recursion,
//! quantifiers, AND argument substitution — end-to-end through
//! `LetPropExpr → μ-calculus → PATA → decide`.
//!
//! The lenient tokenizer accepts the proposed Unicode connectives (`∨`/`∧`/`¬`/`⇒`)
//! as well as their ASCII spellings (`|`/`&`/`~`/`=>`), and `'` in identifiers.
#![cfg(feature = "oslf-letprop")]

use mettail_prattail::letprop::{LetPropArg, LetPropExpr, RecursivePredicate};
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

    /// `NAME ("," NAME)*` inside parens (possibly empty). Used for the
    /// predicate's formal PARAMETER list, which is bare names.
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

    /// One argument: `IDENT` optionally followed by `( arg_list )`.
    /// `child(x)` → `App{func:"child", args:[Var("x")]}`; a bare `x` →
    /// `Var("x")`. This is what makes argument substitution parse.
    fn arg(&mut self) -> LetPropArg {
        let name = self.ident();
        if matches!(self.peek(), Some(Tok::LParen)) {
            self.bump();
            let args = self.arg_list();
            self.expect(&Tok::RParen);
            LetPropArg::App { func: name, args }
        } else {
            LetPropArg::Var(name)
        }
    }

    /// `ARG ("," ARG)*` inside parens (possibly empty). Used for relation
    /// and recursive-call ARGUMENT lists, which may be structured terms.
    fn arg_list(&mut self) -> Vec<LetPropArg> {
        let mut args = Vec::new();
        if matches!(self.peek(), Some(Tok::RParen)) {
            return args;
        }
        args.push(self.arg());
        while matches!(self.peek(), Some(Tok::Comma)) {
            self.bump();
            args.push(self.arg());
        }
        args
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
                    // Quantifiers: `forall(VAR, BODY)` / `exists(VAR, BODY)`.
                    // The first slot is the bound VARIABLE (a bare ident), the
                    // second slot is a full sub-expression.
                    "forall" | "exists" => {
                        self.expect(&Tok::LParen);
                        let var = self.ident();
                        self.expect(&Tok::Comma);
                        let body = Box::new(self.expr());
                        self.expect(&Tok::RParen);
                        if name == "forall" {
                            LetPropExpr::Forall { var, body }
                        } else {
                            LetPropExpr::Exists { var, body }
                        }
                    },
                    // Applied `not(BODY)` form (in addition to the prefix `¬`).
                    "not" => {
                        self.expect(&Tok::LParen);
                        let body = Box::new(self.expr());
                        self.expect(&Tok::RParen);
                        LetPropExpr::Not(body)
                    },
                    _ => {
                        self.expect(&Tok::LParen);
                        let args = self.arg_list();
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
    let mut p = Parser {
        toks: &toks,
        pos: 0,
        self_name: String::new(),
    };
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
                    args: vec![LetPropArg::Var("x".to_string())],
                }),
                Box::new(LetPropExpr::Recursive {
                    args: vec![LetPropArg::Var("x".to_string())]
                }),
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
                args: vec![LetPropArg::Var("x".to_string())],
            }),
            Box::new(LetPropExpr::And(
                Box::new(LetPropExpr::Atom {
                    relation: "step".to_string(),
                    args: vec![LetPropArg::Var("x".to_string())],
                }),
                Box::new(LetPropExpr::Recursive {
                    args: vec![LetPropArg::Var("x".to_string())]
                }),
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

// ══════════════════════════════════════════════════════════════════════════════
// QUANTIFIERS — the formerly-open gap, now closed (predicated-types.md:5823)
// ══════════════════════════════════════════════════════════════════════════════

/// Helper: `App{func, args:[Var…]}` for assertion literals.
fn app(func: &str, vars: &[&str]) -> LetPropArg {
    LetPropArg::App {
        func: func.to_string(),
        args: vars
            .iter()
            .map(|v| LetPropArg::Var(v.to_string()))
            .collect(),
    }
}

#[test]
fn quantifier_only_halt_parses_and_decides_via_section_4b() {
    // The proposed `halt` form (predicated-types.md:5823):
    //   letprop halt(x) = forall(x', not(rewrites_to(x, x')))
    // Quantifier-only (NO recursive self-reference). The CONTRACT: it parses to
    // the exact `Forall { Not(Atom rewrites_to) }` shape.
    let rp = parse_letprop("letprop halt(x) = forall(x', not(rewrites_to(x, x')))");
    assert_eq!(
        rp,
        RecursivePredicate {
            name: "halt".to_string(),
            params: vec!["x".to_string()],
            body: LetPropExpr::Forall {
                var: "x'".to_string(),
                body: Box::new(LetPropExpr::Not(Box::new(LetPropExpr::Atom {
                    relation: "rewrites_to".to_string(),
                    args: vec![LetPropArg::Var("x".to_string()), LetPropArg::Var("x'".to_string())],
                }))),
            },
        }
    );

    // HAND COMPUTATION of the verdict (§4-(B) lowering + `check_emptiness`):
    //
    // - `analyze_polarity` finds NO recursive reference ⇒ `None`, but
    //   `has_quantifier` is true ⇒ §4-(B) lowers it as the greatest-fixpoint
    //   safety formula `νX. □_{→*}(¬ rewrites_to)` (predicated-types.md:5836),
    //   NOT the `NotRecursive → false` error path.
    // - `compile_formula`: the `Nu` state is allocated FIRST with EVEN priority
    //   0 (greatest-fixpoint = safety invariant). `check_emptiness` seeds every
    //   even-priority state accepting, so the initial `Nu` state is accepting
    //   from the start ⇒ L ≠ ∅.
    //
    // ⇒ SATISFIABLE (`decide_recursive_predicate == true`). The point of this
    // assertion is that the quantifier-only body LOWERS AND DECIDES through the
    // §4-(B) path rather than collapsing to the `NotRecursive` false verdict.
    assert!(
        decide_recursive_predicate(&rp),
        "halt(x) = forall(x', ¬rewrites_to(x,x')) must lower via §4-(B) as νX.□(¬…) (even-priority \
         Nu, seeded accepting) and decide SATISFIABLE — NOT the NotRecursive→false path"
    );
}

#[test]
fn exists_quantifier_parses() {
    // The `exists` keyword parses to `Exists` (lowered to a Diamond downstream).
    let rp = parse_letprop("letprop live(x) = exists(y, rewrites_to(x, y))");
    assert_eq!(
        rp.body,
        LetPropExpr::Exists {
            var: "y".to_string(),
            body: Box::new(LetPropExpr::Atom {
                relation: "rewrites_to".to_string(),
                args: vec![LetPropArg::Var("x".to_string()), LetPropArg::Var("y".to_string())],
            }),
        }
    );
    // `exists` body is quantified (non-recursive) ⇒ §4-(B) lowers it as
    // `νX. ◇(…)`. The `Nu` state is even-priority ⇒ satisfiable.
    assert!(decide_recursive_predicate(&rp));
}

// ══════════════════════════════════════════════════════════════════════════════
// ARGUMENT SUBSTITUTION — the formerly-open gap, now closed (…md:8202)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn recursive_quantifier_argsubst_safe_parses_and_is_satisfiable() {
    // The proposed `safe` form WITH a quantifier AND argument substitution:
    //   letprop safe(x) = base(x) ∨ (step(x) ∧ forall(x', safe(child(x))))
    // Exercises recursion + a `forall` + the substituted arg `child(x)` all at
    // once. The CONTRACT: the recursive call carries `args:[App{child,[Var x]}]`.
    let rp = parse_letprop("letprop safe(x) = base(x) ∨ ( step(x) ∧ forall(x', safe(child(x))) )");
    assert_eq!(
        rp.body,
        LetPropExpr::Or(
            Box::new(LetPropExpr::Atom {
                relation: "base".to_string(),
                args: vec![LetPropArg::Var("x".to_string())],
            }),
            Box::new(LetPropExpr::And(
                Box::new(LetPropExpr::Atom {
                    relation: "step".to_string(),
                    args: vec![LetPropArg::Var("x".to_string())],
                }),
                Box::new(LetPropExpr::Forall {
                    var: "x'".to_string(),
                    // Argument substitution: `safe(child(x))`, NOT `safe(x)`.
                    body: Box::new(LetPropExpr::Recursive { args: vec![app("child", &["x"])] }),
                }),
            )),
        )
    );

    // HAND COMPUTATION:
    //
    // - Polarity: the recursive call sits under `forall`/`∧`/`∨` — none is a
    //   `Not` — so polarity is POSITIVE ⇒ least fixpoint `μ safe. …`.
    // - Scope: `child(x)` references only `x` (the formal parameter), which is
    //   in scope ⇒ `validate_arguments` passes (args are dropped by the μ-calc
    //   lowering, so the verdict is the same as the plain `safe(x)` shape).
    // - `μ safe. ( base ∨ (step ∧ □_0 safe) )` HAS a base case (`base`): the
    //   existential `Or` reaches the even-priority `Atom("base")` state, so the
    //   odd-priority `Mu` state becomes accepting ⇒ L ≠ ∅.
    //
    // ⇒ SATISFIABLE (`decide_recursive_predicate == true`).
    assert!(
        decide_recursive_predicate(&rp),
        "safe has a base case (`base`); the μ-fixpoint PATA is non-empty ⇒ satisfiable"
    );
}

#[test]
fn recursive_argsubst_only_safe_parses_and_is_satisfiable() {
    // The proposed `safe` form with ONLY argument substitution, no quantifier
    // (predicated-types.md:8202 verbatim):
    //   letprop safe(x) = base(x) ∨ (step(x) ∧ safe(child(x)))
    let rp = parse_letprop("letprop safe(x) = base(x) ∨ ( step(x) ∧ safe(child(x)) )");
    assert_eq!(
        rp.body,
        LetPropExpr::Or(
            Box::new(LetPropExpr::Atom {
                relation: "base".to_string(),
                args: vec![LetPropArg::Var("x".to_string())],
            }),
            Box::new(LetPropExpr::And(
                Box::new(LetPropExpr::Atom {
                    relation: "step".to_string(),
                    args: vec![LetPropArg::Var("x".to_string())],
                }),
                Box::new(LetPropExpr::Recursive { args: vec![app("child", &["x"])] }),
            )),
        )
    );
    // Positive recursion (μ) with a base case (`base`) ⇒ satisfiable. The
    // substituted arg `child(x)` is in scope and dropped by lowering.
    assert!(
        decide_recursive_predicate(&rp),
        "safe(x) = base(x) ∨ (step(x) ∧ safe(child(x))) has a base case ⇒ satisfiable"
    );
}

#[test]
fn argsubst_out_of_scope_var_is_rejected_so_decide_is_false() {
    // A recursive call whose substituted argument references a variable that is
    // neither a formal parameter (`x`) nor a quantifier-bound variable (`z` is
    // free) is OUT OF SCOPE. `lower_to_mu_calculus` then returns
    // `ArgumentMismatch`, and `decide_recursive_predicate` maps a non-lowerable
    // predicate to `false` (the documented "no decided inhabitant" path that
    // LP01 flags) — NOT a panic.
    let rp = parse_letprop("letprop safe(x) = base(x) ∨ safe(child(z))");
    assert_eq!(
        rp.body,
        LetPropExpr::Or(
            Box::new(LetPropExpr::Atom {
                relation: "base".to_string(),
                args: vec![LetPropArg::Var("x".to_string())],
            }),
            Box::new(LetPropExpr::Recursive { args: vec![app("child", &["z"])] }),
        )
    );
    assert!(
        !decide_recursive_predicate(&rp),
        "safe(child(z)) references out-of-scope `z` ⇒ ArgumentMismatch ⇒ decide returns false"
    );
}

#[test]
fn quantifier_bound_var_is_in_scope_for_argsubst() {
    // The bound variable of a `forall` IS in scope inside its body, so a
    // substituted argument built from it (`child(x')`) is well-scoped and the
    // predicate decides (rather than being rejected as out-of-scope).
    let rp = parse_letprop("letprop safe(x) = base(x) ∨ forall(x', safe(child(x')))");
    // The recursive arg uses the bound `x'`, which is in scope.
    assert_eq!(
        rp.body,
        LetPropExpr::Or(
            Box::new(LetPropExpr::Atom {
                relation: "base".to_string(),
                args: vec![LetPropArg::Var("x".to_string())],
            }),
            Box::new(LetPropExpr::Forall {
                var: "x'".to_string(),
                body: Box::new(LetPropExpr::Recursive { args: vec![app("child", &["x'"])] }),
            }),
        )
    );
    // Positive recursion (the call is under forall/or, not Not) with base case
    // `base` ⇒ satisfiable; the in-scope `x'` passes the scope check.
    assert!(
        decide_recursive_predicate(&rp),
        "child(x') uses the in-scope forall-bound `x'`; with a base case ⇒ satisfiable"
    );
}
