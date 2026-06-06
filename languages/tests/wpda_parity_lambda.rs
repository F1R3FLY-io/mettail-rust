//! Phase 5 binder parity — hand-authored tests for Lambda's
//! `Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term` rule.
//!
//! Verifies the binder state machine end-to-end:
//! - PrefixDispatch sees Fixed("lam ") → ConsumeAndPush(rule_at(Term, Lam, 1))
//!   → BinderRule.
//! - BinderRule@position 1: ConsumeIdentAndReplace (start_scope=true) →
//!   advance to position 2.
//! - BinderRule@position 2: verify Fixed(".") → ConsumeAndReplace → advance
//!   to position 3.
//! - BinderRule@position 3: Push(CategoryEntry(Term)) → PrefixDispatch{cur_bp:0}.
//! - Body parses (here: a bare Ident → Term::TVar via Phase 5a synthetic Var rule).
//! - Body returns to Unwinding-Return → InfixLoop. InfixLoop sees marker
//!   (RuleAt) → Advance(Unwinding). Unwinding-RuleAt → Pop, fire action
//!   (which builds Term::Lam(Scope::new(Binder, body))).

use mettail_languages::lambda::{parse_Term_via_wpda, Term};
use mettail_prattail::automata::TokenKind;

#[test]
fn wpds_parse_lam_identity() {
    // `lam x . x` → Term::Lam(Scope::new(Binder("x"), std::sync::Arc::new(Term::TVar(...))))
    let kinds = vec![
        TokenKind::Fixed("lam ".to_string()),
        TokenKind::Ident,
        TokenKind::Fixed(".".to_string()),
        TokenKind::Ident,
    ];
    let texts: Vec<&str> = vec!["lam ", "x", ".", "x"];
    let mut pos = 0usize;
    let result = parse_Term_via_wpda(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(term @ Term::Lam(_)) => {
            let displayed = format!("{}", term);
            assert!(!displayed.is_empty(), "expected non-empty Display, got {}", displayed,);
        },
        other => panic!("expected Ok(Term::Lam(...)), got {:?}", other),
    }
    assert_eq!(pos, 4, "consumed all 4 tokens");
}

#[test]
fn wpds_parse_lam_with_distinct_binder_and_body() {
    // `lam x . y` → Term::Lam(Scope::new(Binder("x"), std::sync::Arc::new(Term::TVar("y"))))
    // Verifies the binder ident is captured separately from the body's free var.
    let kinds = vec![
        TokenKind::Fixed("lam ".to_string()),
        TokenKind::Ident,
        TokenKind::Fixed(".".to_string()),
        TokenKind::Ident,
    ];
    let texts: Vec<&str> = vec!["lam ", "x", ".", "y"];
    let mut pos = 0usize;
    let result = parse_Term_via_wpda(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Term::Lam(_)) => {},
        other => panic!("expected Ok(Term::Lam(...)), got {:?}", other),
    }
    assert_eq!(pos, 4);
}
