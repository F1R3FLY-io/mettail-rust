//! Opt-Group smoke tests (2026-04-29).
//!
//! Validates the WPDS Opt-Group runtime end-to-end via a synthetic
//! grammar (`mettail_languages::optsmoke`) that exercises:
//!   - The take path: `if true then 1 else 2` — Optional present.
//!   - The skip path: `if true then 1` — Optional absent.
//!   - Both branches of the `if` with each Optional state.
//!
//! The grammar's IfElse rule has term context
//!   `cond:Bool, t:Int, #opt(e:Int)`
//! and syntax pattern
//!   `"if" cond "then" t #opt("else" e)`.
//! Codegen emits `Int::IfElse(Box<Bool>, Box<Int>, Option<Box<Int>>)` and
//! the user-action body `if cond { t } else { e.unwrap_or(0) }`.

use mettail_languages::optsmoke::{Bool, Int};

fn parse_int(input: &str) -> Result<Int, String> {
    Int::parse(input).map_err(|e| format!("{}", e))
}

#[test]
fn if_true_with_else_returns_then_branch() {
    let term = parse_int("if true then 1 else 2").expect("parse should succeed");
    // Action returns t when cond is true → 1.
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 1,
        "if true then 1 else 2 should evaluate to 1, got {}",
        evaluated
    );
}

#[test]
fn if_true_without_else_returns_then_branch() {
    let term = parse_int("if true then 1").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 1,
        "if true then 1 should evaluate to 1, got {}",
        evaluated
    );
}

#[test]
fn if_false_with_else_returns_else_branch() {
    let term = parse_int("if false then 1 else 2").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 2,
        "if false then 1 else 2 should evaluate to 2, got {}",
        evaluated
    );
}

#[test]
fn if_false_without_else_returns_default_zero() {
    let term = parse_int("if false then 1").expect("parse should succeed");
    let evaluated: i32 = term.eval();
    assert_eq!(
        evaluated, 0,
        "if false then 1 should evaluate to 0 (e.unwrap_or(0)), got {}",
        evaluated
    );
}

#[test]
fn ast_shape_present_carries_some_inner_int() {
    // Direct AST-shape verification: the IfElse variant has Option<Box<Int>>
    // for the optional `e:Int` field. Parse the take-path input and check
    // that the third field is Some.
    let term = parse_int("if false then 1 else 99").expect("parse should succeed");
    match term {
        Int::IfElse(ref _cond, ref _t, ref maybe_e) => {
            assert!(
                maybe_e.is_some(),
                "IfElse with else clause should have Some(_) third field, got None"
            );
            let inner = maybe_e.as_ref().unwrap();
            // Inner should be IntLit(99).
            match inner.as_ref() {
                Int::NumLit(n) => assert_eq!(*n, 99, "inner Int should be 99"),
                other => panic!("expected IntLit(99), got {:?}", other),
            }
        }
        other => panic!("expected IfElse variant, got {:?}", other),
    }
}

#[test]
fn ast_shape_absent_carries_none() {
    let term = parse_int("if true then 42").expect("parse should succeed");
    match term {
        Int::IfElse(ref _cond, ref _t, ref maybe_e) => {
            assert!(
                maybe_e.is_none(),
                "IfElse without else clause should have None third field, got Some(_)"
            );
        }
        other => panic!("expected IfElse variant, got {:?}", other),
    }
}

#[test]
fn bool_atoms_parse_directly() {
    // Independence sanity-check: parsing a Bool literal should still work.
    let t = Bool::parse("true").expect("bool true");
    let f = Bool::parse("false").expect("bool false");
    let _ = (t, f);
}

#[test]
fn int_atom_parses_directly() {
    let n = parse_int("42").expect("int literal");
    match n {
        Int::NumLit(v) => assert_eq!(v, 42),
        other => panic!("expected IntLit(42), got {:?}", other),
    }
}
