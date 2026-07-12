//! P3.d / F1 amendment A-11 (2026-07-11): the SITE-2 ParsePredicate smoke —
//! a `?g:Guard` slot INSIDE `*opt(...)` (`check(p)` / `check(p where g)`).
//! Site 1 (guard directly in a binder rule) is covered by the 14 GuardedRho
//! tests; this pair covers the optional-group flow: the predicate leaf must
//! fold into the GROUP frame's spine and flatten through the
//! `OPTIONAL_PRESENT` packing into `ActionArg::Optional(Some([Predicate]))`
//! (guard present), while the skip path yields `Optional(None)` (absent).

//! ⚠ BLOCKED-BY-PREEXISTING (2026-07-11): the whole file is cfg-gated on
//! the non-default `guardoptsmoke` feature because the grammar cannot
//! COMPILE today — two engine-independent term-ops codegen gaps (see
//! languages/Cargo.toml's feature note). The moment those are fixed,
//! adding the feature to `all-languages` turns this pair into the live
//! site-2 gate. Nothing here is parser-blocked: binder.rs:836-839 emits
//! the GuardSlot for optional-group inner positions, and the pure arm is
//! payload-driven (plan §4 placement 2).
#![cfg(feature = "guardoptsmoke")]

use mettail_languages::guardoptsmoke::Int;

#[test]
fn guardopt_present_parses_predicate_in_group() {
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_via_wpda("check ( 1 where ok ( Nil ) )")
        .expect("guard inside #opt(...) should parse when present (site-2 dispatch)");
    let rendered = format!("{parsed:?}");
    assert!(
        rendered.starts_with("PCheck("),
        "expected PCheck(..) with a present guard, got {rendered}"
    );
    assert!(
        rendered.contains("Some("),
        "the optional guard slot should be Some(predicate), got {rendered}"
    );
    assert!(
        rendered.contains("ok"),
        "the parsed predicate should carry the `ok` relation query, got {rendered}"
    );
}

#[test]
fn guardopt_absent_parses_without_guard() {
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_via_wpda("check ( 1 )")
        .expect("omitting the optional guard group should parse (OptGroupAbsent path)");
    let rendered = format!("{parsed:?}");
    assert!(
        rendered.starts_with("PCheck("),
        "expected PCheck(..) with an absent guard, got {rendered}"
    );
    assert!(
        rendered.contains("None"),
        "the optional guard slot should be None when omitted, got {rendered}"
    );
}
