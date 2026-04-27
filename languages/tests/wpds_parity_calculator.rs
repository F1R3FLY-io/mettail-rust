//! Phase 2 parity checkpoint — hand-authored parity tests for Calculator's
//! leaf atomic-literal categories (Int, Bool, Str, BigInt, UInt32, BigRat,
//! Fixed, Float) + TerminalKeyword rules (Err, CastErrInt, etc.).
//!
//! These tests drive `parse_<Cat>_via_wpds` directly on pre-constructed
//! `&[TokenKind]` inputs. Phase 9 will rewrite `test_gen/parity.rs` to
//! emit parity tests driven from the trampoline lexer's output.
//!
//! Per `feedback_parity_drift_ok_if_better.md`, divergences where the new
//! backend is semantically better are ACCEPTED — not driven out. These
//! tests assert correct WPDS behavior; they don't gate on trampoline
//! equivalence.

use mettail_languages::calculator::{Int, Bool, Str, UInt32, BigInt, BigRat, Fixed, Float};
use mettail_languages::calculator::{
    parse_Int_via_wpds, parse_Bool_via_wpds, parse_Str_via_wpds,
    parse_UInt32_via_wpds, parse_BigInt_via_wpds, parse_BigRat_via_wpds,
    parse_Fixed_via_wpds, parse_Float_via_wpds,
};
use mettail_prattail::automata::TokenKind;

/// Drive `parse_Int_via_wpds` with an IntegerLit("Int") token; expect NumLit(i32).
#[test]
fn wpds_parse_int_lit_42() {
    let kinds = vec![TokenKind::IntegerLit("Int".to_string())];
    let texts = vec!["42"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Int::NumLit(42)) => {}
        other => panic!("expected Int::NumLit(42), got {:?}", other),
    }
    assert_eq!(pos, 1);
}

#[test]
fn wpds_parse_int_lit_negative() {
    let kinds = vec![TokenKind::IntegerLit("Int".to_string())];
    let texts = vec!["-7"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Int::NumLit(-7)) => {}
        other => panic!("expected Int::NumLit(-7), got {:?}", other),
    }
}

#[test]
fn wpds_parse_err_keyword() {
    let kinds = vec![TokenKind::Fixed("error".to_string())];
    let texts = vec!["error"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Int::Err) => {}
        other => panic!("expected Int::Err, got {:?}", other),
    }
}

#[test]
fn wpds_parse_cast_err_int_keyword() {
    let kinds = vec![TokenKind::Fixed("cast_error_int".to_string())];
    let texts = vec!["cast_error_int"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Int::CastErrInt) => {}
        other => panic!("expected Int::CastErrInt, got {:?}", other),
    }
}

#[test]
fn wpds_parse_uint32_lit() {
    let kinds = vec![TokenKind::IntegerLit("UInt32".to_string())];
    let texts = vec!["42u32"];
    let mut pos = 0usize;
    let result = parse_UInt32_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(UInt32::NumLit(42)) => {}
        other => panic!("expected UInt32::NumLit(42), got {:?}", other),
    }
}

#[test]
fn wpds_parse_bigint_lit() {
    let kinds = vec![TokenKind::IntegerLit("BigInt".to_string())];
    let texts = vec!["34n"];
    let mut pos = 0usize;
    let result = parse_BigInt_via_wpds(&kinds, &texts, &mut pos, 0);
    assert!(
        matches!(result, Ok(BigInt::NumLit(_))),
        "expected BigInt::NumLit(_), got {:?}",
        result
    );
}

#[test]
fn wpds_parse_bool_lit_true() {
    let kinds = vec![TokenKind::BooleanLit];
    let texts = vec!["true"];
    let mut pos = 0usize;
    let result = parse_Bool_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Bool::BoolLit(true)) => {}
        other => panic!("expected Bool::BoolLit(true), got {:?}", other),
    }
}

#[test]
fn wpds_parse_bool_lit_yeap() {
    let kinds = vec![TokenKind::BooleanLit];
    let texts = vec!["yeap"];
    let mut pos = 0usize;
    let result = parse_Bool_via_wpds(&kinds, &texts, &mut pos, 0);
    match result {
        Ok(Bool::BoolLit(true)) => {}
        other => panic!("expected Bool::BoolLit(true), got {:?}", other),
    }
}

#[test]
fn wpds_parse_str_lit() {
    let kinds = vec![TokenKind::StringLit];
    let texts = vec!["\"hello\""];
    let mut pos = 0usize;
    let result = parse_Str_via_wpds(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Str::StringLit(s)) if s == "hello" => {}
        _ => panic!("expected Str::StringLit(\"hello\"), got {:?}", result),
    }
}

#[test]
fn wpds_parse_bigrat_lit() {
    let kinds = vec![TokenKind::RationalLit("BigRat".to_string())];
    let texts = vec!["1r"];
    let mut pos = 0usize;
    let result = parse_BigRat_via_wpds(&kinds, &texts, &mut pos, 0);
    assert!(
        matches!(result, Ok(BigRat::RatLit(_))),
        "expected BigRat::RatLit(_), got {:?}",
        result
    );
}

#[test]
fn wpds_parse_fixed_lit() {
    let kinds = vec![TokenKind::FixedPointLit("Fixed".to_string())];
    let texts = vec!["1.5p2"];
    let mut pos = 0usize;
    let result = parse_Fixed_via_wpds(&kinds, &texts, &mut pos, 0);
    assert!(
        matches!(result, Ok(Fixed::FixedLit(_))),
        "expected Fixed::FixedLit(_), got {:?}",
        result
    );
}

#[test]
fn wpds_parse_float_lit() {
    let kinds = vec![TokenKind::Float];
    let texts = vec!["3.14"];
    let mut pos = 0usize;
    let result = parse_Float_via_wpds(&kinds, &texts, &mut pos, 0);
    assert!(
        matches!(result, Ok(Float::FloatLit(_))),
        "expected Float::FloatLit(_), got {:?}",
        result
    );
}

#[test]
fn wpds_parse_rejects_non_integer_in_int_slot() {
    let kinds = vec![TokenKind::BooleanLit];
    let texts = vec!["true"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    assert!(result.is_err(), "expected error, got {:?}", result);
}

// ──────────────────────────────────────────────────────────────────────
// Phase 3 — Pratt infix integration tests
// ──────────────────────────────────────────────────────────────────────

#[test]
fn wpds_parse_int_add_simple() {
    let kinds = vec![
        TokenKind::IntegerLit("Int".into()),
        TokenKind::Fixed("+".into()),
        TokenKind::IntegerLit("Int".into()),
    ];
    let texts = vec!["1", "+", "2"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Int::AddInt(a, b)) => match (a.as_ref(), b.as_ref()) {
            (Int::NumLit(1), Int::NumLit(2)) => {}
            _ => panic!("inner shape wrong: {:?}", result),
        },
        _ => panic!("expected Int::AddInt(NumLit(1), NumLit(2)), got {:?}", result),
    }
    assert_eq!(pos, 3, "should consume all 3 tokens");
}

#[test]
fn wpds_parse_int_mul_left_assoc() {
    // 1 + 2 * 3 → AddInt(NumLit(1), MulInt(NumLit(2), NumLit(3)))
    let kinds = vec![
        TokenKind::IntegerLit("Int".into()),
        TokenKind::Fixed("+".into()),
        TokenKind::IntegerLit("Int".into()),
        TokenKind::Fixed("*".into()),
        TokenKind::IntegerLit("Int".into()),
    ];
    let texts = vec!["1", "+", "2", "*", "3"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Int::AddInt(a, b)) => match (a.as_ref(), b.as_ref()) {
            (Int::NumLit(1), Int::MulInt(c, d)) => match (c.as_ref(), d.as_ref()) {
                (Int::NumLit(2), Int::NumLit(3)) => {}
                _ => panic!("inner mul shape wrong: {:?}", result),
            },
            _ => panic!("inner shape wrong: {:?}", result),
        },
        _ => panic!("expected AddInt(1, MulInt(2, 3)), got {:?}", result),
    }
}

#[test]
fn wpds_parse_int_left_assoc_chain() {
    // 1 + 2 + 3 → AddInt(AddInt(NumLit(1), NumLit(2)), NumLit(3))
    // Same precedence, left-associative.
    let kinds = vec![
        TokenKind::IntegerLit("Int".into()),
        TokenKind::Fixed("+".into()),
        TokenKind::IntegerLit("Int".into()),
        TokenKind::Fixed("+".into()),
        TokenKind::IntegerLit("Int".into()),
    ];
    let texts = vec!["1", "+", "2", "+", "3"];
    let mut pos = 0usize;
    let result = parse_Int_via_wpds(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Int::AddInt(outer_l, outer_r)) => match (outer_l.as_ref(), outer_r.as_ref()) {
            (Int::AddInt(a, b), Int::NumLit(3)) => match (a.as_ref(), b.as_ref()) {
                (Int::NumLit(1), Int::NumLit(2)) => {}
                _ => panic!("inner shape wrong: {:?}", result),
            },
            _ => panic!("expected AddInt(AddInt(1, 2), 3), got {:?}", result),
        },
        _ => panic!("expected AddInt(AddInt(1, 2), 3), got {:?}", result),
    }
}
