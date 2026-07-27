//! THE PARSE-LEVEL PIN for **RULE-inert** — *a raw-source scan may only inspect bytes the
//! lexer would place on the DEFAULT channel.*
//!
//! # The defect this file pins, and how it was found
//!
//! `macros/src/gen/runtime/wpda_codegen/scan_site.rs` registers every raw-source byte scan
//! the WPDA facade emits and requires each to declare how both neighbouring spans discharge
//! their obligation. RULE-inert is the third, *orthogonal* obligation: `pre`/`ext` answer
//! *"can a longer token cover this position?"*, while RULE-inert answers *"is this position
//! **code** at all?"*.
//!
//! Before the registry, that rule was stated in exactly one place — the infix facade's
//! hand-written `__in_str` string-literal state — and implemented nowhere else. It knew
//! about string literals and **nothing about comments**. Rholang's comments are
//! **LEXED, NOT STRIPPED** (`languages/src/rholang.rs`:
//! `LineComment = "//[^\n]*" -> COMMENTS`), so raw comment bytes reach every string facade.
//!
//! The consequence was measured on the shipped `rholang` binary before any code changed,
//! with the presence of a depth-0 `|` **inside the comment** as the single controlled
//! variable:
//!
//! ```text
//!   @"OUT"!(1) // z|@"OUT"!(2)     ⇒  @"OUT" observations (2):  Int(1), Int(2)
//!   | Nil                              ↑ the COMMENTED-OUT send RAN
//!
//!   @"OUT"!(1) // z@"OUT"!(2)      ⇒  @"OUT" observations (1):  Int(1)
//!   | Nil                              ↑ same comment, no depth-0 `|` in it
//! ```
//!
//! The infix `__OPS` scan saw the `|` at depth 0 inside the comment, elected it as the
//! `Par` root, and split the source there — handing text the lexer had already routed to
//! the `COMMENTS` channel to a sub-parser **as code**. Commented-out code executed.
//!
//! ⚠ Note that this is *not* gated by `PRATTAIL_NO_PROJ_ISOLATION`: that kill switch
//! disables the `@`-projection helper only, and the defect is in the *infix* helper. Both
//! legs of that switch produced the wrong answer, which is why the discriminating control
//! is the comment's content and not the switch.
//!
//! # The A/B this file records
//!
//! Measured by flipping `scan_site::INERT_SPAN_SKIP` (a compile-time const, so a shipped
//! binary cannot reopen it), everything else held fixed:
//!
//! ```text
//!   source                              OFF (pre-fix)                    ON (this build)
//!   Nil // a|b ⏎ | Nil                  3-way Par (the comment split)    PParInfix(PZero, PZero)
//!   @"OUT"!(1) // z|@"OUT"!(2) ⏎ | Nil  the commented send is a term     PParInfix(POutputShort(…1…), PZero)
//!   @"OUT"!(1) // z@"OUT"!(2)  ⏎ | Nil  PParInfix(POutputShort(…1…), …)  unchanged  ← the control
//!   "a|b"                               unchanged (`__in_str` covered it) unchanged
//! ```
//!
//! The last two rows are the point: the **control** (same comment, no depth-0 separator in
//! it) was already right and stays right, and the string-literal row shows the derived
//! skipper SUBSUMES the hand-written `__in_str` it replaces rather than merely coexisting
//! with it.
//!
//! # Why the fix cannot lose a reading
//!
//! Skipping inert spans can only make a scan see *fewer* candidate positions ⇒ more
//! declines ⇒ fall-through to the monolithic walker, which lexes correctly. That is the
//! same safety argument `ProjectionIsolation.v` `T7_fallthrough_is_monolithic` makes for
//! `combine_run = None`.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;

/// The elected single-winner reading, as a structural `Debug` string.
fn one(source: &str) -> String {
    format!("{:?}", Proc::parse_via_wpda(source).expect("Rholang parses the source"))
}

/// ★ THE HEADLINE PIN — a depth-0 separator inside a line comment is not a split.
///
/// The source has TWO parallel components. Before RULE-inert the infix scan found the `|`
/// inside `// a|b`, split there, and produced a THREE-way `Par` whose middle component was
/// the comment text `b`.
#[test]
fn a_depth0_separator_inside_a_line_comment_is_not_a_par_root() {
    assert_eq!(
        one("Nil // a|b\n| Nil"),
        "PParInfix(PZero, PZero)",
        "the `|` inside the comment must not split the source; the program has two \
         parallel components, not three"
    );
    // The same source with the comment removed — the shape the reading must agree with.
    assert_eq!(one("Nil // a|b\n| Nil"), one("Nil | Nil"));
}

/// ★ THE SEMANTIC PIN — commented-out code must not become a term.
///
/// This is the row that ran on the shipped binary: the send inside the comment was
/// resurrected as a live process and published `Int(2)` on `@"OUT"`.
#[test]
fn a_send_inside_a_comment_does_not_become_a_term() {
    let with_pipe = one("@\"OUT\"!(1) // z|@\"OUT\"!(2)\n| Nil");
    let without_pipe = one("@\"OUT\"!(1) // z@\"OUT\"!(2)\n| Nil");
    assert_eq!(
        with_pipe, without_pipe,
        "whether the comment happens to contain a depth-0 `|` cannot change the parse — \
         a comment is not code"
    );
    assert_eq!(
        with_pipe,
        "PParInfix(POutputShort(CastStr(StringLit(\"OUT\")), CastInt(NumLit(1))), PZero)",
        "only the send OUTSIDE the comment is a term"
    );
}

/// The derived skipper SUBSUMES the hand-written `__in_str` state it replaces: an operator
/// inside a string literal is still content, not a split.
#[test]
fn an_operator_inside_a_string_literal_is_still_content() {
    // The `|` is inside the string, so the only `Par` root is the real one.
    assert_eq!(
        one("@\"a|b\"!(1) | Nil"),
        "PParInfix(POutputShort(CastStr(StringLit(\"a|b\")), CastInt(NumLit(1))), PZero)",
        "a `|` inside a string literal is content; the derived inert skipper must cover \
         the case the hand-written `__in_str` toggle used to cover alone"
    );
}

/// A BLOCK comment is inert too. `__in_str` never had a notion of one; the skipper derives
/// it from the same `BlockComment = "/\*([^*]|\*+[^*/])*\*+/" -> COMMENTS` token def.
#[test]
fn a_depth0_separator_inside_a_block_comment_is_not_a_par_root() {
    assert_eq!(
        one("Nil /* a|b */ | Nil"),
        "PParInfix(PZero, PZero)",
        "the `|` inside a block comment must not split the source"
    );
}

/// A bracket inside a comment must not corrupt the bracket-depth counter for the rest of
/// the scan — the S2/S4 half of RULE-inert, distinct from the separator half.
#[test]
fn an_unbalanced_bracket_inside_a_comment_does_not_corrupt_depth() {
    // The `(` in the comment would push depth to 1 and keep the REAL `|` from ever being
    // seen at depth 0, so the whole source would decline to the walker.
    assert_eq!(
        one("Nil // (((\n| Nil"),
        "PParInfix(PZero, PZero)",
        "brackets inside a comment are not code and must not move the depth counter"
    );
}

/// The comment is still LEXED — this pins that RULE-inert did not silently become
/// comment *stripping*, which would lose the `COMMENTS` channel the tooling depends on.
#[test]
fn comments_are_still_retained_on_their_channel() {
    let lexed = mettail_languages::rholang::lex_with_streams("Nil // a|b\n| Nil")
        .expect("the source lexes");
    let comments: Vec<_> = lexed.tokens_on_channel("COMMENTS").iter().collect();
    assert_eq!(
        comments.len(),
        1,
        "the comment must still be retained on the COMMENTS channel: RULE-inert makes the \
         facade SKIP those bytes, it does not strip them from the source"
    );
}
