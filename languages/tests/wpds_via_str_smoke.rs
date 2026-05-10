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

// B8 / Issues 1+2+3 fix verification (2026-05-10):
// Class 3 ZIP-MAP-SEP and PNew-style multi-binder rules parse end-to-end
// via parse_via_wpds.

#[test]
fn rhocalc_pinputs_empty_via_wpds() {
    // PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
    // |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
    // Empty list: ns = [], xs = [], body = 0 (PZero / CastBigInt(0)).
    let result = rhocalc::Proc::parse_via_wpds("().{0}")
        .expect("empty PInputs parses");
    match &result {
        rhocalc::Proc::PInputs(ns, _scope) => {
            assert_eq!(ns.len(), 0, "empty list expected");
        }
        other => panic!("expected Proc::PInputs(_, _), got {:?}", other),
    }
}

#[test]
fn rhocalc_pinputs_single_binder_via_wpds() {
    // Single binder: `(c1?x).{*(x)}` — ns = [NVar("c1")], xs = [Binder("x")],
    // body = PDrop(NVar("x") bound).
    let result = rhocalc::Proc::parse_via_wpds("(c1?x).{*(x)}")
        .expect("single-binder PInputs parses");
    match &result {
        rhocalc::Proc::PInputs(ns, _scope) => {
            assert_eq!(ns.len(), 1, "one channel name expected");
        }
        other => panic!("expected Proc::PInputs(_, _), got {:?}", other),
    }
}

#[test]
fn rhocalc_pinputs_multi_binder_via_wpds() {
    // Multi-binder: `(c1?x, c2?y).{*(x)}` — ns = [c1, c2], xs = [x, y].
    let result = rhocalc::Proc::parse_via_wpds("(c1?x, c2?y).{*(x)}")
        .expect("multi-binder PInputs parses");
    match &result {
        rhocalc::Proc::PInputs(ns, _scope) => {
            assert_eq!(ns.len(), 2, "two channel names expected");
        }
        other => panic!("expected Proc::PInputs(_, _), got {:?}", other),
    }
}

#[test]
fn rhocalc_pnew_single_binder_via_wpds() {
    // PNew . ^[xs].p:[Name* -> Proc] |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
    // Single: `new(x) in {*(x)}`.
    let result = rhocalc::Proc::parse_via_wpds("new(x) in {*(x)}")
        .expect("single-binder PNew parses");
    match &result {
        rhocalc::Proc::PNew(_scope) => {}
        other => panic!("expected Proc::PNew(_), got {:?}", other),
    }
}

#[test]
fn rhocalc_pnew_multi_binder_via_wpds() {
    // Multi-binder: `new(x, y) in {*(x)}`.
    let result = rhocalc::Proc::parse_via_wpds("new(x, y) in {*(x)}")
        .expect("multi-binder PNew parses");
    match &result {
        rhocalc::Proc::PNew(_scope) => {}
        other => panic!("expected Proc::PNew(_), got {:?}", other),
    }
}
