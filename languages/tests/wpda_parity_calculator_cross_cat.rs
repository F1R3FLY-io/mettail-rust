//! Stage 1.1 cross-category projection parity — verifies Calculator's
//! `ProcInt . i:Int |- i : Proc` rule routes through CrossCatDelegate.
//!
//! When parsing as Proc and the next token is an Int-token (e.g.,
//! `IntegerLit("Int")`), the engine should:
//! 1. Push a Return marker for ProcInt with cat=Proc, rule_idx=ProcInt's idx.
//! 2. Transition to CrossCatDelegate{source=Int}.
//! 3. CrossCatDelegate pushes CategoryEntry(Int).
//! 4. PrefixDispatch on Int matches IntegerLit → ConsumeAndPush(Int's NumLit Return).
//! 5. Unwinding pops Int's Return, fires NumLit action, pushes Int::NumLit(42).
//! 6. Unwinding pops the cross-cat ProcInt Return, fires wrap-action,
//!    pushes Proc::ProcInt(Box::new(Int::NumLit(42))).

use mettail_languages::calculator::{parse_Bool_via_wpda, parse_Proc_via_wpda, Bool, Int, Proc};
use mettail_prattail::automata::TokenKind;

#[test]
fn wpds_parse_procint_from_int_literal() {
    let kinds = vec![TokenKind::IntegerLit("Int".to_string())];
    let texts = vec!["42"];
    let mut pos = 0usize;
    let result = parse_Proc_via_wpda(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Proc::ProcInt(boxed_int)) => {
            match boxed_int.as_ref() {
                Int::NumLit(42) => {}
                other => panic!("expected Int::NumLit(42), got {:?}", other),
            }
        }
        other => panic!("expected Proc::ProcInt(Int::NumLit(42)), got {:?}", other),
    }
    assert_eq!(pos, 1);
}

/// Stage 1.2 cross-category infix: `EqInt . a:Int, b:Int |- a "==" b : Bool`.
/// Parsing as Bool with input `1 == 2` should produce `Bool::EqInt(...)`.
#[test]
fn wpds_parse_eqint_cross_cat_infix() {
    let kinds = vec![
        TokenKind::IntegerLit("Int".to_string()),
        TokenKind::Fixed("==".to_string()),
        TokenKind::IntegerLit("Int".to_string()),
    ];
    let texts = vec!["1", "==", "2"];
    let mut pos = 0usize;
    let result = parse_Bool_via_wpda(&kinds, &texts, &mut pos, 0);
    match &result {
        Ok(Bool::EqInt(a, b)) => {
            assert!(matches!(a.as_ref(), Int::NumLit(1)));
            assert!(matches!(b.as_ref(), Int::NumLit(2)));
        }
        other => panic!("expected Bool::EqInt(NumLit(1), NumLit(2)), got {:?}", other),
    }
    assert_eq!(pos, 3);
}
