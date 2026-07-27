//! X4 — the two lookahead productions **in the real RhoCalc grammar**.
//!
//! `x2_lookahead_bracket_probe.rs` established over 17 inputs that
//!
//! ```text
//! PLookahead    . p:Proc, n:Proc |- p "[" n "]"   : Proc
//! PLookaheadAll . p:Proc         |- p "[" "*" "]" : Proc
//! ```
//!
//! are unambiguous **in a miniature grammar**. That is the right first experiment — it isolates
//! the bracket question from RhoCalc's ~700 other productions — but it is not evidence about
//! RhoCalc itself, whose `List` type owns `[`/`]` as its `open_parts`/`close_parts` and whose
//! mixfix cohorts are far richer. This file is the corresponding measurement on the production
//! grammar, through the PRODUCTION parse entry (`parse_via_wpda`, not `Proc::parse` — see the
//! long note in `rholang-runtime/src/bin/rhocalc.rs` on why the latter is not term-preserving).
//!
//! Three things are asserted, and they are the three ways this could have gone wrong:
//!
//! 1. the lookahead surfaces PARSE, and parse to the intended constructors;
//! 2. list literals are UNDISTURBED — `[1]`, `[*x]`, `[[1],[2]]` still read as lists;
//! 3. the surface is attached to the send forms the demo actually uses, including the
//!    quoted-string channel (`@"results"!(…)[*]`) and the `new`-bound channel.
#![cfg(feature = "rhocalc")]

use mettail_languages::rhocalc::Proc;
use mettail_runtime::clear_var_cache;

/// Parse through the production entry, returning the debug rendering of the term.
fn read(source: &str) -> Result<String, String> {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .map(|p| format!("{p:?}"))
        .map_err(|e| e.to_string())
}

fn read_ok(source: &str) -> String {
    read(source).unwrap_or_else(|err| panic!("RhoCalc must parse {source:?}: {err}"))
}

// ── 1. the lookahead surfaces parse, to the intended constructors ───────────────────────────

#[test]
fn t1_lookahead_all_over_a_quoted_string_channel_send() {
    let term = read_ok(r#"@"results"!(Nil)[*]"#);
    println!("X4 `@\"results\"!(Nil)[*]` → {term}");
    assert!(
        term.contains("PLookaheadAll"),
        "`@\"results\"!(Nil)[*]` must read as PLookaheadAll, got: {term}"
    );
}

#[test]
fn t2_lookahead_all_over_an_flt_payload() {
    let term = read_ok(r#"@"results"!(lambda`(lam x. x, lam a. lam b. a)`)[*]"#);
    println!("X4 FLT[*] → {term}");
    assert!(
        term.contains("PLookaheadAll"),
        "an FLT-payload send with `[*]` must read as PLookaheadAll, got: {term}"
    );
    assert!(
        term.contains("PFlt"),
        "the payload must still reflect as an FLT node, got: {term}"
    );
}

#[test]
fn t3_bounded_lookahead_parses_with_an_integer_bound() {
    let term = read_ok(r#"@"results"!(Nil)[3]"#);
    println!("X4 `@\"results\"!(Nil)[3]` → {term}");
    assert!(
        term.contains("PLookahead("),
        "`@\"results\"!(Nil)[3]` must read as the bounded PLookahead, got: {term}"
    );
}

#[test]
fn t4_lookahead_on_a_new_bound_channel() {
    let term = read_ok("new r in { r!(Nil)[*] }");
    println!("X4 new-bound `[*]` → {term}");
    assert!(
        term.contains("PLookaheadAll"),
        "a `new`-bound channel must accept `[*]`, got: {term}"
    );
}

#[test]
fn t5_two_lookahead_sends_in_one_program_parse() {
    // The collision question at the SURFACE level; the runtime half is measured by
    // `rholang-runtime/tests/x3_inprocess_lookahead_probe.rs`.
    let term = read_ok(r#"@"results"!(Nil)[*] | @"results"!(Nil)[*]"#);
    println!("X4 two `[*]` sends → {term}");
    assert!(
        term.matches("PLookaheadAll").count() >= 2,
        "both sends must carry their own lookahead, got: {term}"
    );
}

// ── 2. list literals are undisturbed (the regression that matters) ──────────────────────────

#[test]
fn t6_list_literals_still_read_as_lists_not_lookaheads() {
    for source in ["[1]", "[[1],[2]]", "[*x]", "[1, 2, 3]"] {
        let term = read_ok(source);
        println!("X4 list {source:?} → {term}");
        assert!(
            !term.contains("PLookahead"),
            "{source:?} must still read as a LIST, not a lookahead: {term}"
        );
    }
}

#[test]
fn t7_a_send_of_a_list_is_still_a_send_of_a_list() {
    let term = read_ok(r#"@"c"!([1, 2])"#);
    println!("X4 send-of-list → {term}");
    assert!(
        !term.contains("PLookahead"),
        "`@\"c\"!([1, 2])` must not acquire a lookahead reading: {term}"
    );
}

// ── 3. the shapes the grammar must still REJECT ─────────────────────────────────────────────

#[test]
fn t8_unattached_and_unterminated_brackets_are_rejected() {
    for source in [r#"@"c"!(Nil)[*"#, r#"@"c"!(Nil)*]"#] {
        let outcome = read(source);
        println!("X4 reject {source:?} → {outcome:?}");
        assert!(outcome.is_err(), "{source:?} must be rejected, got: {outcome:?}");
    }
}
