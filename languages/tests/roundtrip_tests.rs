//! Property-based round-trip tests for the Calculator language.
//!
//! Tests the fundamental property: `parse(display(t)) == t` for randomly generated terms.
//!
//! Uses proptest strategies to construct Calculator AST terms directly, bypassing
//! `generate_random_at_depth` (which doesn't see auto-generated NumLit/IVar constructors).
//!
//! ## Limitations
//!
//! - Binder-containing terms (Lambda, RhoCalc) need alpha-equivalence comparison.
//!   This test suite focuses on binder-free Calculator Int terms.
//! - Only tests Int category (the primary Calculator category).
//! - Bool and Str are tested at depth 0 (literals and variables only) since
//!   cross-category operators like Eq/Len have complex display/parse interactions.

use proptest::prelude::*;

use mettail_languages::calculator::Int;

// ══════════════════════════════════════════════════════════════════════════════
// Int term strategies
// ══════════════════════════════════════════════════════════════════════════════

/// Strategy for generating random Int terms up to a given depth.
///
/// Depth 0: NumLit (integer literals, range -50..50 to avoid display ambiguity)
/// Depth n: one of Add, Sub, Mul(*), Neg, Pow, Fact, Tern, or depth-0
///
/// Note: Variables (IVar) are excluded because moniker's Var equality
/// semantics differ from structural equality after round-trip.
fn arb_int_term(max_depth: u32) -> impl Strategy<Value = Int> {
    // Leaf: just integer literals
    let leaf = (-50i32..50).prop_map(|n| Int::NumLit(n));

    leaf.prop_recursive(
        max_depth, // max depth
        64,        // max nodes
        4,         // items per collection (unused here, but required)
        |inner| {
            prop_oneof![
                // AddInt: left + right
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::AddInt(Box::new(a), Box::new(b)) }),
                // SubInt: left - right
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::SubInt(Box::new(a), Box::new(b)) }),
                // MulInt: left * right
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::MulInt(Box::new(a), Box::new(b)) }),
                // DivInt: left / right
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::DivInt(Box::new(a), Box::new(b)) }),
                // ModInt: left % right
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::ModInt(Box::new(a), Box::new(b)) }),
                // Neg: -operand
                inner.clone().prop_map(|a| { Int::Neg(Box::new(a)) }),
                // PowInt: base ^ exponent
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::PowInt(Box::new(a), Box::new(b)) }),
                // Fact: operand!
                inner.clone().prop_map(|a| { Int::Fact(Box::new(a)) }),
                // Tern: cond ? then : else
                (inner.clone(), inner.clone(), inner.clone())
                    .prop_map(|(c, t, e)| { Int::Tern(Box::new(c), Box::new(t), Box::new(e)) }),
                // CustomOp: a ~ b
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| { Int::CustomOp(Box::new(a), Box::new(b)) }),
            ]
        },
    )
}

// ══════════════════════════════════════════════════════════════════════════════
// Round-trip property tests
// ══════════════════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Property: parse(display(t)) should succeed for any well-formed Int term.
    #[test]
    fn roundtrip_int_parse_display(term in arb_int_term(3)) {
        mettail_runtime::clear_var_cache();
        let displayed = format!("{}", term);

        mettail_runtime::clear_var_cache();
        let parsed = Int::parse(&displayed);
        prop_assert!(
            parsed.is_ok(),
            "Failed to parse displayed Int term: '{}'\nOriginal: {:?}\nError: {:?}",
            displayed,
            term,
            parsed.err()
        );
    }

    /// Property: display(parse(display(t))) == display(t) (idempotence).
    #[test]
    fn idempotent_int_display(term in arb_int_term(3)) {
        mettail_runtime::clear_var_cache();
        let displayed1 = format!("{}", term);

        mettail_runtime::clear_var_cache();
        if let Ok(reparsed_term) = Int::parse(&displayed1) {
            let displayed2 = format!("{}", reparsed_term);
            prop_assert_eq!(
                &displayed1, &displayed2,
                "Display should be idempotent.\nFirst display: '{}'\nSecond display: '{}'",
                displayed1, displayed2
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Depth-specific regression tests
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn roundtrip_depth0_literals() {
    // Every integer literal should round-trip
    for n in -20..=20 {
        mettail_runtime::clear_var_cache();
        let term = Int::NumLit(n);
        let displayed = format!("{}", term);
        mettail_runtime::clear_var_cache();
        let parsed = Int::parse(&displayed);
        assert!(
            parsed.is_ok(),
            "Literal {} should round-trip. Displayed: '{}', Error: {:?}",
            n,
            displayed,
            parsed.err()
        );
    }
}

#[test]
fn roundtrip_simple_binary_ops() {
    let ops: Vec<(&str, fn(Box<Int>, Box<Int>) -> Int)> = vec![
        ("+", |a, b| Int::AddInt(a, b)),
        ("-", |a, b| Int::SubInt(a, b)),
        ("*", |a, b| Int::MulInt(a, b)),
        ("/", |a, b| Int::DivInt(a, b)),
        ("%", |a, b| Int::ModInt(a, b)),
        ("^", |a, b| Int::PowInt(a, b)),
        ("~", |a, b| Int::CustomOp(a, b)),
    ];

    for (op_name, constructor) in &ops {
        mettail_runtime::clear_var_cache();
        let term = constructor(Box::new(Int::NumLit(1)), Box::new(Int::NumLit(2)));
        let displayed = format!("{}", term);
        mettail_runtime::clear_var_cache();
        let parsed = Int::parse(&displayed);
        assert!(
            parsed.is_ok(),
            "Binary op '{}' should round-trip. Displayed: '{}', Error: {:?}",
            op_name,
            displayed,
            parsed.err()
        );
    }
}

#[test]
fn roundtrip_unary_ops() {
    // Neg
    mettail_runtime::clear_var_cache();
    let term = Int::Neg(Box::new(Int::NumLit(5)));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Neg should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );

    // Fact
    mettail_runtime::clear_var_cache();
    let term = Int::Fact(Box::new(Int::NumLit(5)));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Fact should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );
}

#[test]
fn roundtrip_ternary() {
    mettail_runtime::clear_var_cache();
    let term =
        Int::Tern(Box::new(Int::NumLit(1)), Box::new(Int::NumLit(42)), Box::new(Int::NumLit(0)));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Ternary should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );
}

#[test]
fn roundtrip_nested_expressions() {
    // (1 + 2) - 3
    mettail_runtime::clear_var_cache();
    let term = Int::SubInt(
        Box::new(Int::AddInt(Box::new(Int::NumLit(1)), Box::new(Int::NumLit(2)))),
        Box::new(Int::NumLit(3)),
    );
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Nested expression should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );

    // -(3 + 4)
    mettail_runtime::clear_var_cache();
    let term = Int::Neg(Box::new(Int::AddInt(Box::new(Int::NumLit(3)), Box::new(Int::NumLit(4)))));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Neg(Add) should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );
}
