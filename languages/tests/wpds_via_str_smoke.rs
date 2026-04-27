//! Stage 3 smoke tests: invoke `Cat::parse_via_wpds(&str)` end-to-end
//! to verify the lex → token_to_kind → WPDS facade pipeline works for
//! at least one fixture per supported grammar.

use mettail_languages::calculator::{Bool, Int, Proc};
use mettail_languages::lambda::Term;
use mettail_languages::rhocalc;

#[test]
fn calculator_int_lit_via_wpds() {
    let result = Int::parse_via_wpds("42").expect("int parses");
    assert!(matches!(result, Int::NumLit(42)));
}

#[test]
fn calculator_proc_int_cross_cat_via_wpds() {
    // ProcInt . i:Int |- i : Proc; — bare integer in Proc context.
    let result = Proc::parse_via_wpds("42").expect("Proc::ProcInt parses");
    match &result {
        Proc::ProcInt(boxed) => match boxed.as_ref() {
            Int::NumLit(42) => {}
            other => panic!("expected NumLit(42), got {:?}", other),
        },
        other => panic!("expected Proc::ProcInt(...), got {:?}", other),
    }
}

#[test]
fn calculator_bool_eq_int_cross_cat_infix_via_wpds() {
    // EqInt . a:Int, b:Int |- a "==" b : Bool — cross-cat infix.
    let result = Bool::parse_via_wpds("1 == 2").expect("Bool::EqInt parses");
    match &result {
        Bool::EqInt(a, b) => {
            assert!(matches!(a.as_ref(), Int::NumLit(1)));
            assert!(matches!(b.as_ref(), Int::NumLit(2)));
        }
        other => panic!("expected Bool::EqInt(1, 2), got {:?}", other),
    }
}

#[test]
fn lambda_lam_identity_via_wpds() {
    // `lam x . x` → Term::Lam(Scope::new(Binder("x"), Box::new(Term::TVar(...))))
    let result = Term::parse_via_wpds("lam x . x").expect("Term::Lam parses");
    match &result {
        Term::Lam(_) => {}
        other => panic!("expected Term::Lam(...), got {:?}", other),
    }
}

#[test]
fn rhocalc_proc_par_via_wpds() {
    // `{ error | error }` → Proc::PPar(HashBag::from([Err, Err])).
    let result = rhocalc::Proc::parse_via_wpds("{ error | error }")
        .expect("Proc::PPar parses");
    match &result {
        rhocalc::Proc::PPar(bag) => {
            assert_eq!(bag.len(), 2);
        }
        other => panic!("expected Proc::PPar(...), got {:?}", other),
    }
}
