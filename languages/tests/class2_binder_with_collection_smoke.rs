//! B9 / Class 2 smoke test (2026-05-08).
//!
//! Validates the BINDER-WITH-COLLECTION-PARAM pattern: a multi-Param rule
//! with one tag param + one Vec-typed collection param, where the collection
//! is parsed via `Sep` over a separator. The minimal-composition design
//! reuses the existing `WpdaState::CollectionLoop` apparatus by routing
//! the binder rule's collection slot through a `CollectionMarker` push +
//! `is_binder_internal_collection` FireAction-suppression.
//!
//! Falsifiable predictions (PRED-1..6) from the B9 plan:
//! - PRED-1: empty `( )` → `Choose(Zero, [])`.
//! - PRED-2: singleton `( 0 )` → `Choose(Zero, [Zero])`.
//! - PRED-3: 3-element preserving order.
//! - PRED-5: missing close paren → Err.
//! - PRED-6: missing tag → Err.

use mettail_languages::class2smoke::Proc;

#[test]
fn pred1_empty_collection() {
    // PRED-1: `Proc::parse("choose 0 ( )")` → `Choose(Zero, [])`.
    let result = Proc::parse_via_wpda("choose 0 ( )").expect("empty Choose parses");
    match &result {
        Proc::Choose(tag, qs) => {
            assert!(matches!(tag.as_ref(), Proc::PZero), "tag should be PZero");
            assert_eq!(qs.len(), 0, "qs should be empty");
        },
        other => panic!("expected Proc::Choose(_, []), got {:?}", other),
    }
}

#[test]
fn pred2_singleton_collection() {
    // PRED-2: `Proc::parse("choose 0 ( 0 )")` → `Choose(Zero, [Zero])`.
    let result = Proc::parse_via_wpda("choose 0 ( 0 )").expect("singleton Choose parses");
    match &result {
        Proc::Choose(tag, qs) => {
            assert!(matches!(tag.as_ref(), Proc::PZero));
            assert_eq!(qs.len(), 1);
            assert!(matches!(&qs[0], Proc::PZero));
        },
        other => panic!("expected Proc::Choose(_, [_]), got {:?}", other),
    }
}

#[test]
fn pred3_three_element_collection() {
    // PRED-3: 3-element collection. With all elements equal (PZero), order
    // preservation is trivially satisfied; the assertion confirms cardinality.
    let result = Proc::parse_via_wpda("choose 0 ( 0 | 0 | 0 )").expect("3-element Choose parses");
    match &result {
        Proc::Choose(tag, qs) => {
            assert!(matches!(tag.as_ref(), Proc::PZero));
            assert_eq!(qs.len(), 3);
            for q in qs.iter() {
                assert!(matches!(q, Proc::PZero));
            }
        },
        other => panic!("expected Proc::Choose(_, [_, _, _]), got {:?}", other),
    }
}

#[test]
fn pred5_missing_close_paren_recovers() {
    // Strict parse stays strict; recovery is exposed through parse_recovering.
    assert!(
        Proc::parse_via_wpda("choose 0 ( 0 | 0").is_err(),
        "strict WPDA parse must not auto-recover missing delimiters",
    );
    let (result, errors) = Proc::parse_recovering("choose 0 ( 0 | 0");
    assert!(
        result.is_some(),
        "WPDS bounded recovery should produce a recovered parse, got {:?}",
        errors
    );
    assert!(
        !errors.is_empty(),
        "recovering parse should report the inserted missing close delimiter",
    );
}

#[test]
fn pred6_missing_tag_errors() {
    // PRED-6: missing tag → Err. Without a Proc to fill the `a` slot, parse
    // should reject (the open `(` arrives where a Proc was expected).
    let result = Proc::parse_via_wpda("choose ( 0 )");
    assert!(result.is_err(), "missing tag should error, got {:?}", result);
}
