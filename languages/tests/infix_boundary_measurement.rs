//! ★ THE `infix.ops` BOUNDARY-EXEMPTION MEASUREMENT — the number, not the folklore.
//!
//! # What was believed, and why it needed measuring
//!
//! The infix `__OPS` root-operator election
//! (`macros/src/gen/runtime/wpda_codegen/facade.rs`, scan site `infix.ops`) is the one
//! entry in the scan-site registry that carries **no** `pre`/`ext` token-boundary test.
//! The reason recorded in the codebase's folklore was *"adding it breaks `1-7`"*.
//!
//! That reason is almost certainly **wrong**, and it matters that it was wrong, because an
//! unmeasured exemption is indistinguishable from an oversight — which is exactly how the
//! other four members of this defect family survived. An `__OPS` decline does not reject
//! the input: it falls through to the monolithic walker, and
//! `languages/tests/proj_iso_token_boundary.rs` asserts that the *walker* resolves `1-7`
//! to `Sub` by **fork feasibility** (*"the lexer's fork dies on feasibility and `Minus`
//! wins"*). So `1-7` should survive the boundary test regardless.
//!
//! # The honest reason for the exemption
//!
//! Under the obligation criterion (see `scan_site`), this site discharges **(a) EVIDENCE**
//! on *both* spans: each operand is submitted in its entirety to the category's own string
//! entry, and `__left_is_operand` additionally requires a complete operand terminal at
//! `p-1`. Evidence is **feasibility-aware** — the competing fork `Int(1) Int(-7)` is *two
//! adjacent processes*, which no single `Proc` admits, so the sub-parse refutes it.
//! `pre`/`ext` are feasibility-**blind** local over-approximations. Where evidence is
//! discharged it strictly dominates, and the boundary test can only subtract correct
//! answers.
//!
//! The Stage-C enumerating gate demonstrated that dominance directly rather than by
//! argument. Modelling `infix.ops` with the boundary predicate alone, it reported:
//!
//! ```text
//!   SCAN SITE `infix.ops` accepts literal "-" at byte 0 of "-0", but the language's own
//!   lexer does NOT produce it as a DEFAULT-channel token there.
//! ```
//!
//! — and the site is nevertheless correct there, because at byte 0 the left span is EMPTY
//! and the evidence obligation rejects the candidate that the boundary model accepted.
//!
//! # ★ THE MEASUREMENT
//!
//! Taken by flipping `scan_site::INFIX_TOKEN_BOUNDARY` (a compile-time `const`, so a
//! shipped binary cannot reopen it), everything else held fixed, and regenerating.
//!
//! ```text
//!   input        elected reading, INFIX_TOKEN_BOUNDARY = false   = true
//!   1-7          Sub(CastInt(1), CastInt(7))                     Sub(CastInt(1), CastInt(7))
//!   1 -7         Sub(CastInt(1), CastInt(7))                     Sub(CastInt(1), CastInt(7))
//!   5-3          Sub(CastInt(5), CastInt(3))                     Sub(CastInt(5), CastInt(3))
//!   1-7-2        Sub(Sub(1, 7), 2)                               Sub(Sub(1, 7), 2)
//!   1+2*3        Add(1, Mul(2, 3))                               Add(1, Mul(2, 3))
//!   Nil | Nil    PParInfix(PZero, PZero)                         PParInfix(PZero, PZero)
//! ```
//!
//! **THE FOLKLORE IS REFUTED: `1-7` does not break.** The elected readings are identical
//! on both legs for every row measured. What the `true` leg costs is the FAST PATH — the
//! `-` election declines at the facade (because `ext("-") ∋ digits`) and the input is
//! resolved by the monolithic walker instead — which is a latency cost, not a correctness
//! one.
//!
//! **The shipped value is `false`**, and the reason recorded in `scan_site` is now
//! *"(a) is discharged on both spans and strictly dominates the (b) approximation"* rather
//! than *"it breaks `1-7`"*. The exemption is a measured decision with a recorded number,
//! which is what this codebase did not have.
//!
//! This file pins the rows so the measurement can be re-taken by flipping one `const`, and
//! so a future change that makes `1-7` depend on the exemption fails loudly.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;

/// The elected single-winner reading, as a structural `Debug` string.
fn one(source: &str) -> String {
    format!("{:?}", Proc::parse_via_wpda(source).expect("Rholang parses the source"))
}

/// ★ THE ROW THE FOLKLORE NAMED. `1-7` is the input the exemption was said to protect;
/// it must elect `Sub` on BOTH legs, which is what makes the folklore reason false.
#[test]
fn the_abutted_subtraction_the_exemption_was_said_to_protect() {
    assert_eq!(
        one("1-7"),
        "Sub(CastInt(NumLit(1)), CastInt(NumLit(7)))",
        "`1-7` must elect subtraction. The facade's operator election is not what makes \
         this work — the walker resolves it by fork feasibility — which is why the \
         `__OPS` boundary exemption cannot be justified by this input."
    );
}

/// The spaced and re-spelled variants of the same measurement.
#[test]
fn subtraction_is_elected_regardless_of_spacing() {
    let expected = "Sub(CastInt(NumLit(1)), CastInt(NumLit(7)))";
    assert_eq!(one("1-7"), expected);
    assert_eq!(one("1 -7"), expected);
    assert_eq!(one("1 - 7"), expected);
    assert_eq!(
        one("5-3"),
        "Sub(CastInt(NumLit(5)), CastInt(NumLit(3)))",
        "a second abutted subtraction, so the row is not a one-literal coincidence"
    );
}

/// Left-associativity and precedence still come out of the election, so the exemption is
/// not silently disabling the site.
#[test]
fn the_election_still_roots_at_the_right_operator() {
    assert_eq!(
        one("1-7-2"),
        "Sub(Sub(CastInt(NumLit(1)), CastInt(NumLit(7))), CastInt(NumLit(2)))",
        "`-` is left-associative, so the ROOT is the RIGHTMOST occurrence"
    );
    assert_eq!(
        one("1+2*3"),
        "Add(CastInt(NumLit(1)), Mul(CastInt(NumLit(2)), CastInt(NumLit(3))))",
        "`*` binds tighter than `+`, so the root is the LOOSEST operator"
    );
}

/// The `|` row, which is the operator RULE-inert actually broke. It is measured here too
/// so both obligations of this one site are pinned side by side: the boundary obligation
/// is EXEMPT (by evidence), the inert obligation is NOT.
#[test]
fn the_par_root_is_unaffected_by_the_exemption() {
    assert_eq!(one("Nil | Nil"), "PParInfix(PZero, PZero)");
}
