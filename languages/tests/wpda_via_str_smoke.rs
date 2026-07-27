//! Stage 3 smoke tests: invoke `Cat::parse_via_wpda(&str)` end-to-end
//! to verify the lex → token_to_kind → WPDS facade pipeline works for
//! at least one fixture per supported grammar.

use mettail_languages::calculator::{Bool, Int, Proc};
use mettail_languages::lambda::Term;
use mettail_languages::rholang;

#[test]
fn calculator_int_lit_via_wpds() {
    let result = Int::parse_via_wpda("42").expect("int parses");
    assert!(matches!(result, Int::NumLit(42)));
}

#[test]
fn calculator_proc_int_cross_cat_via_wpds() {
    // ProcInt . i:Int |- i : Proc; — bare integer in Proc context.
    let result = Proc::parse_via_wpda("42").expect("Proc::ProcInt parses");
    match &result {
        Proc::ProcInt(boxed) => match boxed.as_ref() {
            Int::NumLit(42) => {},
            other => panic!("expected NumLit(42), got {:?}", other),
        },
        other => panic!("expected Proc::ProcInt(...), got {:?}", other),
    }
}

#[test]
fn calculator_bool_eq_int_cross_cat_infix_via_wpds() {
    // EqInt . a:Int, b:Int |- a "==" b : Bool — cross-cat infix.
    let result = Bool::parse_via_wpda("1 == 2").expect("Bool::EqInt parses");
    match &result {
        Bool::EqInt(a, b) => {
            assert!(matches!(a.as_ref(), Int::NumLit(1)));
            assert!(matches!(b.as_ref(), Int::NumLit(2)));
        },
        other => panic!("expected Bool::EqInt(1, 2), got {:?}", other),
    }
}

#[test]
fn lambda_lam_identity_via_wpds() {
    // `lam x . x` → Term::Lam(Scope::new(Binder("x"), std::sync::Arc::new(Term::TVar(...))))
    let result = Term::parse_via_wpda("lam x . x").expect("Term::Lam parses");
    match &result {
        Term::Lam(_) => {},
        other => panic!("expected Term::Lam(...), got {:?}", other),
    }
}

#[test]
fn rholang_proc_par_via_wpds() {
    // `{ error | error }` → Proc::PPar(HashBag::from([Err, Err])).
    let result = rholang::Proc::parse_via_wpda("{ error | error }").expect("Proc::PPar parses");
    match &result {
        rholang::Proc::PPar(bag) => {
            assert_eq!(bag.len(), 2);
        },
        other => panic!("expected Proc::PPar(...), got {:?}", other),
    }
}

// Rholang-1.4 receive grammar (`PForUser` / `for (...) { ... }`) parses end-to-end
// via parse_via_wpda. (Replaces the obsolete `PInputs` `(c?x).{...}` smoke tests —
// main removed that receive syntax in favor of `for`.)

#[test]
fn rholang_for_empty_bind_via_wpds() {
    // Empty bind: `for(<- c){0}` — one row, no bound variable.
    let result = rholang::Proc::parse_via_wpda("for(<- c){0}").expect("empty-bind for parses");
    match &result {
        rholang::Proc::PForUser(rows, _body) => {
            assert_eq!(rows.len(), 1, "one receive row expected");
        },
        other => panic!("expected Proc::PForUser(_, _), got {:?}", other),
    }
}

#[test]
fn rholang_for_single_bind_via_wpds() {
    // Single ephemeral bind: `for(x <- c){*(x)}` — one row binding `x`.
    let result =
        rholang::Proc::parse_via_wpda("for(x <- c){*(x)}").expect("single-bind for parses");
    match &result {
        rholang::Proc::PForUser(rows, _body) => {
            assert_eq!(rows.len(), 1, "one receive row expected");
        },
        other => panic!("expected Proc::PForUser(_, _), got {:?}", other),
    }
}

#[test]
fn rholang_for_join_bind_via_wpds() {
    // Join (`&`): `for(x <- c1 & y <- c2){*(x)}` — one row joining two binds.
    let result = rholang::Proc::parse_via_wpda("for(x <- c1 & y <- c2){*(x)}")
        .expect("join-bind for parses");
    match &result {
        rholang::Proc::PForUser(rows, _body) => {
            assert_eq!(rows.len(), 1, "one (joined) receive row expected");
        },
        other => panic!("expected Proc::PForUser(_, _), got {:?}", other),
    }
}

#[test]
fn rholang_pnew_single_binder_via_wpds() {
    // PNew . ^[xs].p:[Name* -> Proc] |- "new" xs.*sep(",") "in" "{" p "}" : Proc;
    // Single: `new x in {*(x)}`.
    let result =
        rholang::Proc::parse_via_wpda("new x in {*(x)}").expect("single-binder PNew parses");
    match &result {
        rholang::Proc::PNew(_scope) => {},
        other => panic!("expected Proc::PNew(_), got {:?}", other),
    }
}

#[test]
fn rholang_pnew_multi_binder_via_wpds() {
    // Multi-binder: `new x, y in {*(x)}`.
    let result =
        rholang::Proc::parse_via_wpda("new x, y in {*(x)}").expect("multi-binder PNew parses");
    match &result {
        rholang::Proc::PNew(_scope) => {},
        other => panic!("expected Proc::PNew(_), got {:?}", other),
    }
}
