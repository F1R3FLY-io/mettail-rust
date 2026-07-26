//! Grouping is inert: `( E )` parses iff `E` parses.
//!
//! ## Why this file exists
//!
//! `gen_calculator_prop::bigrat_display_parse_roundtrip` failed with
//!
//! ```text
//! arb_bigrat produced unparseable surface term "-(592107620 + bigrat(cast_error_bigint))"
//! ```
//!
//! and was dismissed as a proptest flake. It is deterministic. Shrinking the
//! counterexample by hand isolates the defect to a **redundant pair of
//! parentheses**: `0 + bigrat(a)` parses, `(0 + bigrat(a))` does not.
//!
//! ## The shape IS in the language
//!
//! Every node of the counterexample is a declared Calculator production
//! (`languages/src/calculator.rs`):
//!
//! | surface | rule |
//! |---|---|
//! | `cast_error_bigint` | `CastErrBigInt . \|- "cast_error_bigint" : BigInt` |
//! | `bigrat( … )`       | `BigratCast . a:Proc \|- "bigrat" "(" a ")" : BigRat` |
//! | `592107620`         | `IntToBigRat . i:Int \|- i : BigRat` (transparent injection) |
//! | `… + …`             | `AddBigRat . a:BigRat, b:BigRat \|- a "+" b : BigRat` |
//! | `- …`               | `NegBigRat . a:BigRat \|- "-" a : BigRat` |
//!
//! So `<Int> + bigrat(<Proc>)` is legitimate cross-category Calculator
//! arithmetic, and the generator was right to emit it. The parser was wrong to
//! reject it.
//!
//! ## The invariant these tests pin
//!
//! `(` … `)` is Calculator's pure grouping form — it carries no rule of its
//! own. Therefore, for every `E` in a category `C`:
//!
//! ```text
//!     C::parse(E).is_ok()  ⟺  C::parse("(" ++ E ++ ")").is_ok()
//! ```
//!
//! A `both fail` pair is fine (`0 - 1r` has no `SubBigRat`); a
//! `bare ok / grouped fail` pair is the defect.

#![cfg(feature = "calculator")]

use mettail_languages::calculator::*;

/// Every string here is legal Calculator whose LHS reaches `BigRat` through a
/// cross-category promotion. Each must parse BOTH bare and parenthesized.
const GROUPING_INERT_BIGRAT: &[&str] = &[
    // The minimal witness: an `Int` LHS promoted into `BigRat`.
    "0 + bigrat(a)",
    // A `BigRat` literal on the right — no cast rule involved at all.
    "0 + 1r",
    // Each foreign literal carrier that Calculator declares an injection for.
    "1n + bigrat(a)",
    "0u32 + bigrat(a)",
    "0.5 + bigrat(a)",
    // A `step`-bodied BigRat producer on the right.
    "0 + fraction(1n,2n)",
    // The same promotion under the other BigRat infix operators.
    "0 bitand bigrat(a)",
    "0 bitor bigrat(a)",
    "0 * bigrat(a)",
    "0 / bigrat(a)",
    // Controls: LHS already native `BigRat` (these never regressed).
    "bigrat(0) + bigrat(a)",
    "error + bigrat(a)",
    "1r + bigrat(a)",
    "bigrat(a) + 0",
];

#[test]
fn grouping_is_inert_for_bigrat() {
    let mut broken: Vec<String> = Vec::with_capacity(GROUPING_INERT_BIGRAT.len());
    for bare in GROUPING_INERT_BIGRAT {
        mettail_runtime::clear_var_cache();
        let bare_ok = BigRat::parse(bare).is_ok();
        let grouped = format!("({})", bare);
        mettail_runtime::clear_var_cache();
        let grouped_res = BigRat::parse(&grouped);
        assert!(
            bare_ok,
            "precondition: the bare form {bare:?} must parse (it is declared Calculator)"
        );
        if let Err(e) = grouped_res {
            broken.push(format!("  {grouped:?} -> {e:?}"));
        }
    }
    assert!(
        broken.is_empty(),
        "grouping is not inert — these parse bare but not parenthesized:\n{}",
        broken.join("\n")
    );
}

/// A `both fail` pair stays a `both fail` pair: `BigRat` has no `-` infix
/// (`SubBigRat` is not declared), so this must be rejected in BOTH forms.
/// Without this the test above could be satisfied by making the parser
/// accept everything.
#[test]
fn grouping_inertness_does_not_mean_accept_everything() {
    mettail_runtime::clear_var_cache();
    assert!(
        BigRat::parse("0 - 1r").is_err(),
        "BigRat declares no `-` infix rule; `0 - 1r` must not parse"
    );
    mettail_runtime::clear_var_cache();
    assert!(
        BigRat::parse("(0 - 1r)").is_err(),
        "grouping must not create a derivation the grammar does not have"
    );
}

/// The literal counterexamples the proptest shrank to, pinned verbatim so a
/// regression is reported as itself rather than as a random seed.
#[test]
fn proptest_counterexamples_parse() {
    for src in [
        "-(592107620 + bigrat(cast_error_bigint))",
        "(0 + bigrat(a)) * error",
    ] {
        mettail_runtime::clear_var_cache();
        let parsed = BigRat::parse(src)
            .unwrap_or_else(|e| panic!("counterexample {src:?} must parse: {e:?}"));
        // The round-trip contract the property asserts: the canonical form is
        // a fixpoint of parse∘display.
        let canonical = format!("{}", parsed);
        mettail_runtime::clear_var_cache();
        let reparsed = BigRat::parse(&canonical).unwrap_or_else(|e| {
            panic!("canonical form {canonical:?} of {src:?} must re-parse: {e:?}")
        });
        assert_eq!(
            canonical,
            format!("{}", reparsed),
            "display must be idempotent after canonicalization"
        );
    }
}
