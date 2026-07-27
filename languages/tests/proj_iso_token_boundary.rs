//! THE PARSE-LEVEL PIN for the projection helper's TOKEN-BOUNDARY rule
//! (`macros/src/gen/runtime/wpda_codegen/lit_boundary.rs`).
//!
//! # What this file is for, and why it is separate from the artifact suite
//!
//! `rholang-runtime/tests/rhocalc_ground_literal_conformance.rs` is the CONFORMANCE criterion: it
//! compares the emitted `Par` against f1r3node's own normalizer. That is the right criterion and it
//! is not this file's job. This file pins the layer BELOW it — the elected parse tree and the
//! ambiguity-preserving alternative SET — for two reasons the artifact comparison cannot serve:
//!
//! 1. **A `Par` is lossy about tree shape.** `ENeg(GInt(7))` and `GInt(-7)` differ visibly, but
//!    `Add(CastInt(-7), 1)` and `Add(NegProc(CastInt(7)), 1)` do not once the reducer has evaluated
//!    the negation. The parse tree is where the distinction is still observable.
//! 2. **The alt SET is invisible at the artifact layer.** The governing project rule is
//!    *never disambiguate early*: a repair that makes the ELECTION right by DELETING the losing
//!    reading is a regression, not a fix. Only `parse_via_wpda_all` shows that.
//!
//! # The rule being pinned
//!
//! A fixed literal in a projection skeleton is a TOKEN, so it may only match where the lexer would
//! end that token. The helper enforced that for IDENT-shaped literals only (the rule that stops
//! `Nil` matching inside `Nilish`); a punctuation sigil got no test, and RhoCalc's numerals carry
//! their sign (`Int = -?…`, mirroring consensus Rholang's `long_literal /-?\d+/`). So in `-7n` the
//! maximal munch at byte 0 is `BigInt("-7n")` and the `NegProc` skeleton's one-byte `-` is a PROPER
//! PREFIX of it. Matching there framed the whole span as `- ⟨7n⟩`.
//!
//! ★ ADJACENCY IS THE DISCRIMINATOR, in both directions, and both directions are pinned here:
//! `-7n` is one token and must NOT become a negation; `- 7n` and `-(7n)` are two and MUST stay one.
//!
//! # The A/B this file records
//!
//! Measured by flipping `lit_boundary::TOKEN_BOUNDARY_ALPHABET` (a compile-time const, so the leg
//! cannot be changed in a shipped binary), everything else held fixed:
//!
//! ```text
//!   input        OFF (pre-fix)                       ON (this build)
//!   -7           NegProc(CastInt(7))                 CastInt(-7)
//!   -7n          NegProc(CastBigInt(7))              CastBigInt(-7)
//!   -1.5f64      NegProc(CastFloat(1.5))             CastFloat(-1.5)
//!   -3r/2r       NegProc(Div(3r, 2r))                Div(CastBigRat(-3), CastBigRat(2))
//!   -7 + 1       NegProc(Add(7, 1))          = −8    Add(CastInt(-7), 1)          = −6
//!   - 7          NegProc(CastInt(7))                 NegProc(CastInt(7))          unchanged
//!   1-7          Sub(1, 7)                           Sub(1, 7)                    unchanged
//!   @Nil!(0)     POutputNil(CastInt(0))              POutputNil(CastInt(0))       unchanged
//! ```
//!
//! The unchanged rows are not luck: the derived byte sets for `@`, `(`, `*`, `[`, `{`, `,`, `<-`,
//! `<=` are all EMPTY (nothing in RhoCalc's token alphabet extends them or runs into them), so
//! those literals' matching is byte-identical. That is the mechanical reason the two goldens
//! `43ef99aa` protected when it declined to touch the `Single` seam cannot move.

#![cfg(feature = "rhocalc")]

use mettail_languages::rhocalc::{Name, Proc};

/// The elected single-winner reading, as a structural `Debug` string.
fn one(source: &str) -> String {
    format!("{:?}", Proc::parse_via_wpda(source).expect("RhoCalc parses the source"))
}

/// The ambiguity-preserving alternative set, as structural `Debug` strings.
fn all(source: &str) -> Vec<String> {
    Proc::parse_via_wpda_all(source)
        .expect("RhoCalc parses the source")
        .iter()
        .map(|t| format!("{t:?}"))
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — THE REPAIR: a sign-abutted numeral elects the SIGNED LITERAL, not a negation.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Each spelling and the constructor its elected reading must carry the sign INSIDE.
const ABUTTED: [(&str, &str); 7] = [
    ("-7", "CastInt(NumLit(-7))"),
    ("-7i32", "CastInt(NumLit(-7))"),
    ("-7i64", "CastInt(NumLit(-7))"),
    ("-7n", "CastBigInt(NumLit(-7))"),
    ("-7r", "CastBigRat(RatLit(Ratio { numer: -7, denom: 1 }))"),
    ("-1.5f64", "CastFloat(FloatLit(-1.5))"),
    ("-1.5p2", "CastFixed(FixedLit(Fixed(-150/100)))"),
];

#[test]
fn a_sign_abutted_numeral_elects_the_signed_literal() {
    for (source, expected) in ABUTTED {
        assert_eq!(
            one(source),
            expected,
            "★ `{source}` is ONE signed literal token. Electing a negation here means the \
             projection helper matched `-` inside the numeral again — check the `ext` set derived \
             for `-` in `lit_boundary.rs` (it must contain the digits and `.`)."
        );
    }
}

/// `-0` is the row where the sign is invisible in the VALUE, so only the constructor tells the two
/// readings apart. It is kept separate because `NumLit(-0) == NumLit(0)`.
#[test]
fn negative_zero_elects_the_literal_carrier_not_a_negation() {
    assert_eq!(one("-0"), "CastInt(NumLit(0))");
}

/// ★ THE PRECEDENCE CONSEQUENCE. The `- ⟨operand⟩` framing swallowed the WHOLE remaining span with
/// no precedence awareness, so `-7 + 1` elected `-(7 + 1)` = −8 where the grammar's own declaration
/// order says `-` binds tighter than `+` and the answer is −6. `rhocalc.rs` states this intent
/// verbatim for division: *"`NegProc` is declared after `/` and `%` so `-` binds tighter than
/// division (e.g. `-3r/2r` is `(-3r)/2r`)"*.
#[test]
fn a_signed_numeral_is_the_operator_s_operand_not_its_argument() {
    assert_eq!(one("-7 + 1"), "Add(CastInt(NumLit(-7)), CastInt(NumLit(1)))");
    assert_eq!(one("-7 * 2"), "Mul(CastInt(NumLit(-7)), CastInt(NumLit(2)))");
    assert_eq!(
        one("-3r/2r"),
        "Div(CastBigRat(RatLit(Ratio { numer: -3, denom: 1 })), \
         CastBigRat(RatLit(Ratio { numer: 2, denom: 1 })))"
    );
}

/// The `@`-quoted Name position composes: `Name`'s own `@ ⟨p⟩` skeleton still matches (its `@` has
/// an EMPTY boundary alphabet), and the Proc operand it sub-parses now elects the signed literal.
#[test]
fn a_quoted_name_carries_the_signed_literal_through() {
    let name = Name::parse_via_wpda("@-7").expect("RhoCalc parses `@-7`");
    assert_eq!(format!("{name:?}"), "NQuoteShort(CastInt(NumLit(-7)))");
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — THE CONTRAST THAT PROVES THE REPAIR IS LEXICAL. ⚠ DO NOT WEAKEN.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// With the sign detached — by whitespace or by a parenthesis — there is no signed token to be a
/// prefix of, so the helper matches `-` exactly as it always did and a REAL negation is built.
///
/// ⚠ A repair applied after parsing (a fold in the lowering, say) would collapse these into the
/// abutted readings and this test is what makes that fail loudly. Its artifact-level twin is
/// `rholang-runtime/tests/rhocalc_ground_literal_conformance.rs::adjacency_is_honoured`.
#[test]
fn a_detached_sign_still_builds_a_negation() {
    for (source, expected) in [
        ("- 7", "NegProc(CastInt(NumLit(7)))"),
        ("-(7)", "NegProc(CastInt(NumLit(7)))"),
        ("- 7n", "NegProc(CastBigInt(NumLit(7)))"),
        ("-(7n)", "NegProc(CastBigInt(NumLit(7)))"),
        ("- 1.5f64", "NegProc(CastFloat(FloatLit(1.5)))"),
        ("- 1.5p2", "NegProc(CastFixed(FixedLit(Fixed(150/100))))"),
    ] {
        assert_eq!(
            one(source),
            expected,
            "★ `{source}` has a DETACHED sign, so it must still be a negation node. If this row \
             changed, the repair stopped being lexical and started folding."
        );
    }
}

/// Unspaced subtraction is unaffected: its one-token reading (`1`, `-7`) is two adjacent processes,
/// infeasible for a single `Proc`, so the lexer's fork dies on feasibility and `Minus` wins. This is
/// also the row where MeTTaIL is deliberately MORE permissive than f1r3node, whose maximal-munch
/// lexer commits before feasibility is known and cannot compile `1-7` at all (pinned in
/// `rhocalc_ground_literal_conformance.rs::f1r3node_rejects_unspaced_subtraction_and_negated_unsigned`).
#[test]
fn unspaced_subtraction_is_still_subtraction() {
    for source in ["1-7", "1 -7", "5-3"] {
        assert_eq!(all(source).len(), 1, "`{source}` must have exactly one reading");
    }
    assert_eq!(one("1-7"), "Sub(CastInt(NumLit(1)), CastInt(NumLit(7)))");
    assert_eq!(one("5-3"), "Sub(CastInt(NumLit(5)), CastInt(NumLit(3)))");
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  3 — AMBIGUITY IS PRESERVED, NOT RESOLVED. The helper may only DECLINE, never prune.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE DISAMBIGUATION-PRESERVATION GATE. Declining is safe precisely because the fall-through is
/// the monolithic walker, which is authoritative and ambiguity-preserving. So the negation reading
/// of `-7n` must STILL be enumerable — the repair changes which reading is ELECTED, not which
/// readings EXIST.
#[test]
fn the_negation_reading_is_still_enumerable() {
    let alts = all("-7n");
    assert!(
        alts.iter().any(|t| t == "CastBigInt(NumLit(-7))"),
        "the signed-literal reading must be in the set: {alts:?}"
    );
    assert!(
        alts.iter().any(|t| t == "NegProc(CastBigInt(NumLit(7)))"),
        "★ the NEGATION reading was PRUNED. The lexer forks at a sign-abutted numeral and both \
         readings are legitimate; the repair may only change the ELECTION. {alts:?}"
    );
}

/// ⚠ A READING THAT LEFT THE SET, and why that is a repair rather than a loss.
///
/// `NegProc(Add(7, 1))` used to be enumerable for `-7 + 1`. It was never a legitimate reading of
/// that string: it requires `-` to bind LOOSER than `+`, and `NegProc` is declared after `/` and
/// `%` precisely so that it binds TIGHTER. It existed only because the projection helper framed
/// `- ⟨whole remaining span⟩` with no precedence awareness and the `_all` seam unioned that framing
/// in. Removing a reading the grammar does not license is not early disambiguation — it is the
/// facade no longer manufacturing one.
#[test]
fn the_facade_no_longer_manufactures_a_precedence_violating_reading() {
    for (source, forbidden) in [
        ("-7 + 1", "NegProc(Add(CastInt(NumLit(7)), CastInt(NumLit(1))))"),
        ("-7 * 2", "NegProc(Mul(CastInt(NumLit(7)), CastInt(NumLit(2))))"),
    ] {
        let alts = all(source);
        assert!(
            !alts.iter().any(|t| t == forbidden),
            "★ `{source}` enumerates `{forbidden}`, which requires `-` to bind looser than the \
             operator. The grammar declares the opposite. {alts:?}"
        );
        // …and the readings the grammar DOES license are all still there.
        assert!(
            alts.iter()
                .any(|t| t.starts_with("Add(") || t.starts_with("Mul(")),
            "the operator-rooted readings must survive: {alts:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  4 — THE GOLDENS `43ef99aa` PROTECTED. Byte-identical, and pinned so they stay that way.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// `43ef99aa` (#28 / G3) unioned the `_all` seam with the walker and deliberately left the `Single`
/// election seam alone, recording that unioning there *"would flip `Name::parse("(@Nil)")` to the
/// transparent twin and `@Nil!(0)` from the specific `POutputNil` to the generic `POutputShort`"*.
/// This repair is not a union — it is a token-boundary condition whose derived byte sets are EMPTY
/// for `@`, `(`, `*` and the brackets — so those elections are untouched by construction. This test
/// is the measurement that says so rather than the argument that claims it.
#[test]
fn the_g3_election_goldens_are_untouched() {
    let paren_name = Name::parse_via_wpda("(@Nil)").expect("RhoCalc parses `(@Nil)` as a Name");
    assert_eq!(
        format!("{paren_name:?}"),
        "NParen(NQuoteShort(PZero))",
        "★ `Name::parse(\"(@Nil)\")` moved to the transparent twin — exactly the flip `43ef99aa` \
         declined to make"
    );

    assert_eq!(
        one("@Nil!(0)"),
        "POutputNil(CastInt(NumLit(0)))",
        "★ `@Nil!(0)` moved off the specific `POutputNil` rule — the other flip `43ef99aa` declined"
    );

    // The `_all` seam's own G3 rows, including the reading the facade contributes that the walker
    // does not (`NParen(NQuote(1))` under the drop).
    assert_eq!(all("*(@(1)) + 2").len(), 2, "the `_all` union's G3 row must keep both readings");
    assert_eq!(all("@(a)!(0)").len(), 3, "the grouped-channel row must keep all three readings");
}

/// The persistent-send sigil is the one multi-byte punctuation literal whose boundary alphabet is
/// NON-empty (`ext("!") = {'!', '='}` from the `!!` and `!=` terminals, `pre("!") = {'!'}`), so it
/// is the row that proves a non-empty set does not disturb a correct frame: `@Nil!(0)`'s `!` is
/// followed by `(`, and `@Nil!!(0)`'s `!!` is preceded by `l`.
#[test]
fn the_send_sigils_still_frame_their_own_shapes() {
    assert_eq!(one("@Nil!(0)"), "POutputNil(CastInt(NumLit(0)))");
    assert_eq!(one("@Nil!!(0)"), "PPersistOutputNil(CastInt(NumLit(0)))");
}
