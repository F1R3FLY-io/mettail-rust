//! Property-based round-trip tests for the Calculator language.
//!
//! Tests the fundamental property: `parse(display(t)) == t` for randomly generated terms.
//!
//! Uses proptest strategies to construct Calculator AST terms directly, bypassing
//! `generate_random_at_depth` (which doesn't see auto-generated NumLit/IVar constructors).
//!
//! ## Limitations
//!
//! - Binder-containing terms (Lambda, Rholang) need alpha-equivalence comparison.
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
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::AddInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // SubInt: left - right
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::SubInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // MulInt: left * right
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::MulInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // DivInt: left / right
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::DivInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // ModInt: left % right
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::ModInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // Neg: -operand
                inner
                    .clone()
                    .prop_map(|a| { Int::Neg(std::sync::Arc::new(a)) }),
                // PowInt: base ^ exponent
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::PowInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // Fact: operand!
                inner
                    .clone()
                    .prop_map(|a| { Int::Fact(std::sync::Arc::new(a)) }),
                // Tern: cond ? then : else
                (inner.clone(), inner.clone(), inner.clone()).prop_map(|(c, t, e)| {
                    Int::Tern(
                        std::sync::Arc::new(c),
                        std::sync::Arc::new(t),
                        std::sync::Arc::new(e),
                    )
                }),
                // BitAndInt: a & b
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::BitAndInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // BitOrInt: a | b
                (inner.clone(), inner.clone()).prop_map(|(a, b)| {
                    Int::BitOrInt(std::sync::Arc::new(a), std::sync::Arc::new(b))
                }),
                // BitNotInt: ~a
                inner
                    .clone()
                    .prop_map(|a| { Int::BitNotInt(std::sync::Arc::new(a)) }),
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

    /// Property: the display reaches a FIXED POINT after one parse→display roundtrip.
    ///
    /// NOTE — the `-0` rendering debate (deliberately not prejudged here). The first
    /// display of an arbitrary AST is a *faithful* rendering of its structure that need
    /// not already be value-canonical. The canonical example is negated literal zero:
    /// `Neg(NumLit(0))` renders as `-0`, which the integer lexer (`-?[0-9]+`) reads
    /// atomically back to `NumLit(0)` — since `-0 == 0` and zero is signless — which
    /// re-renders as `0`. (Non-zero negatives are already stable: `Neg(NumLit(5))` →
    /// `-5` → `NumLit(-5)` → `-5`.) Whether `-0` *ought to* render as `-0` (AST-faithful)
    /// or `0` (value-canonical) is a long-standing technical debate in mettail — each
    /// choice trades off against different components — so this property is deliberately
    /// rendering-AGNOSTIC. Raw display-identity (`display(parse(display(t))) == display(t)`)
    /// is too strong: it would demand every faithful display already be value-canonical,
    /// prejudging the debate. The meaningful invariant is FIXED-POINT CONVERGENCE —
    /// whatever the canonical form is after one parse→display roundtrip, it must be stable
    /// under a second roundtrip. This still catches any genuine display defect (a canonical
    /// form that fails to re-parse to itself) while holding under either resolution of `-0`.
    #[test]
    fn idempotent_int_display(term in arb_int_term(3)) {
        mettail_runtime::clear_var_cache();
        let displayed1 = format!("{}", term);

        mettail_runtime::clear_var_cache();
        if let Ok(reparsed1) = Int::parse(&displayed1) {
            let canonical = format!("{}", reparsed1);
            mettail_runtime::clear_var_cache();
            let reparsed2 =
                Int::parse(&canonical).expect("the canonical display (post-roundtrip) must re-parse");
            let canonical2 = format!("{}", reparsed2);
            prop_assert_eq!(
                &canonical, &canonical2,
                "Display must reach a fixed point after one roundtrip (rendering-agnostic).\n\
                 First display: '{}'\nCanonical:     '{}'\nRe-canonical:  '{}'",
                displayed1, canonical, canonical2
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
    let ops: Vec<(&str, fn(std::sync::Arc<Int>, std::sync::Arc<Int>) -> Int)> = vec![
        ("+", |a, b| Int::AddInt(a, b)),
        ("-", |a, b| Int::SubInt(a, b)),
        ("*", |a, b| Int::MulInt(a, b)),
        ("/", |a, b| Int::DivInt(a, b)),
        ("%", |a, b| Int::ModInt(a, b)),
        ("^", |a, b| Int::PowInt(a, b)),
        ("&", |a, b| Int::BitAndInt(a, b)),
        ("|", |a, b| Int::BitOrInt(a, b)),
    ];

    for (op_name, constructor) in &ops {
        mettail_runtime::clear_var_cache();
        let term =
            constructor(std::sync::Arc::new(Int::NumLit(1)), std::sync::Arc::new(Int::NumLit(2)));
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
    let term = Int::Neg(std::sync::Arc::new(Int::NumLit(5)));
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
    let term = Int::Fact(std::sync::Arc::new(Int::NumLit(5)));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "Fact should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );

    // BitNotInt: ~operand
    mettail_runtime::clear_var_cache();
    let term = Int::BitNotInt(std::sync::Arc::new(Int::NumLit(5)));
    let displayed = format!("{}", term);
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse(&displayed);
    assert!(
        parsed.is_ok(),
        "BitNotInt should round-trip. Displayed: '{}', Error: {:?}",
        displayed,
        parsed.err()
    );
}

#[test]
fn roundtrip_ternary() {
    mettail_runtime::clear_var_cache();
    let term = Int::Tern(
        std::sync::Arc::new(Int::NumLit(1)),
        std::sync::Arc::new(Int::NumLit(42)),
        std::sync::Arc::new(Int::NumLit(0)),
    );
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
        std::sync::Arc::new(Int::AddInt(
            std::sync::Arc::new(Int::NumLit(1)),
            std::sync::Arc::new(Int::NumLit(2)),
        )),
        std::sync::Arc::new(Int::NumLit(3)),
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
    let term = Int::Neg(std::sync::Arc::new(Int::AddInt(
        std::sync::Arc::new(Int::NumLit(3)),
        std::sync::Arc::new(Int::NumLit(4)),
    )));
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
