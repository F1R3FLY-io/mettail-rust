//! D1 probe — a COLLECTION FIELD in Binder / MultiBinder PRE-SCOPE position was
//! compared by LENGTH ONLY.
//!
//! `macros/src/gen/term_ops/match_pattern.rs` emitted, for such a field:
//!
//! ```text
//! if (**g0).len() != (**p0).len() { return None; }
//! ```
//!
//! so two collections of equal length but entirely different contents MATCHED,
//! and no element of the collection could ever bind a pattern variable.
//!
//! `class3multi::TaggedInputs(Vec<Proc>, Vec<Name>, Scope<..>)` is one of only
//! three live sites in the whole generated tree (the others are the sibling
//! `Vec<Name>` slot and `class3opt::PInputsOptTagged`), which is why this
//! language is the witness.

#![cfg(feature = "class3multi")]

use mettail_languages::class3multi::Proc;

fn parse(input: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse_via_wpda(input).unwrap_or_else(|e| panic!("parse failed for `{input}`: {e:?}"))
}

/// The CARDINALITY direction, which the length-only comparison already got
/// right. Kept as a control so a regression that broke cardinality would be
/// distinguishable from one that broke element comparison.
#[test]
fn different_tag_counts_still_do_not_match() {
    let ground = parse("with [ 0 ] ( ) . { 0 }");
    let pattern = parse("with [ 0 ; 0 ] ( ) . { 0 }");
    assert!(
        ground.match_pattern(&pattern).is_none(),
        "different tag counts must not match"
    );
}

/// ★ Same length, different CONTENT — the case length-only could not see.
///
/// The `tags` slot is `Vec(Proc)` and the Class3Multi grammar admits exactly two
/// closed `Proc` shapes at that position: `0` (`PZero`) and the auto-generated
/// parseable `PVar`. The witness therefore puts a VARIABLE in the GROUND and
/// `0` in the PATTERN — `PVar(x).match_pattern(&PZero)` is a constructor clash,
/// so the correct verdict is "no match".
///
/// (The opposite orientation would be useless: a free variable in PATTERN
/// position is a binder and matches anything, so it would be green either way.
/// The orientation is the whole point of the test.)
#[test]
fn same_length_different_content_must_not_match() {
    let ground = parse("with [ 0 ; x ] ( ) . { 0 }");
    let pattern = parse("with [ 0 ; 0 ] ( ) . { 0 }");
    assert!(
        ground.match_pattern(&pattern).is_none(),
        "★D1: `tags` has length 2 on BOTH sides, but the second elements differ \
         (ground `x` is a PVar, pattern `0` is PZero). A length-only comparison \
         sees only `2 == 2` and accepts this as a match"
    );
}

/// The satisfied companion — the fix must not degenerate into "reject all".
#[test]
fn identical_tagged_inputs_still_match() {
    let ground = parse("with [ 0 ; 0 ] ( ) . { 0 }");
    let pattern = parse("with [ 0 ; 0 ] ( ) . { 0 }");
    assert!(
        ground.match_pattern(&pattern).is_some(),
        "identical terms must still match"
    );
}
