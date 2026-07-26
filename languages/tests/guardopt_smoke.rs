//! P3.d / F1 amendment A-11 (2026-07-11): the SITE-2 ParsePredicate smoke —
//! a `?g:Guard` slot INSIDE `*opt(...)` (`check(p)` / `check(p where g)`).
//! Site 1 (guard directly in a binder rule) is covered by the 14 GuardedRho
//! tests; this pair covers the optional-group flow: the predicate leaf must
//! fold into the GROUP frame's spine and flatten through the
//! `OPTIONAL_PRESENT` packing into `ActionArg::Optional(Some([Predicate]))`
//! (guard present), while the skip path yields `Optional(None)` (absent).

//! UNBLOCKED by task #14 (Option<Guard> term-ops codegen, 2026-07-13): the
//! historical blocker was 15 pre-existing, engine-independent term-ops
//! codegen errors across 8 generated files (normalize/subst/match_pattern/
//! display/hashes/term_gen/test_gen — receipt:
//! scratchpad/zz_probes/logs_s2burn/f1_a11_check.log) plus the eval
//! classify `compile_error!` for the committed Int shape; all closed by
//! the task-#14 emitter fixes. This pair is now the LIVE site-2 gate,
//! still cfg-gated on the non-default `guardoptsmoke` feature (promotion
//! into `all-languages` is a separate decision). Nothing here was ever
//! parser-blocked: binder.rs emits the GuardSlot for optional-group inner
//! positions at both sites, and the pure arm is payload-driven.
// Task #11 (extended 2026-07-26): the `guardoptsmoke` LIBRARY FEATURE is gone (the
// definition is test-hosted now), so this file-level gate would evaluate FALSE and
// silently delete the LIVE site-2 gate. The definition is `#[path]`-included
// unconditionally below instead, which makes the site-2 pair unconditional.
// #![cfg(feature = "guardoptsmoke")]

// Task #11 (extended 2026-07-26): `GuardOptSmoke` is a site-2 ParsePredicate FIXTURE, not a production language, so its
// definition lives in `languages/tests/definitions/guardoptsmoke.rs` rather than in the `languages`
// library (`languages/src/` is production-only).
//
// This file is its DESIGNATED HOST: it declares the definition module and is the one and only
// invoker of the opt-in `guardoptsmoke_generated_tests!` wrapper, which materializes the
// macro-generated sections that used to be written to `languages/tests/gen_guardoptsmoke_*.rs`.
// Other consumers `#[path]`-include the same definition WITHOUT invoking the wrapper, so the
// generated tests exist exactly once across the whole suite.
#[path = "definitions/guardoptsmoke.rs"]
mod guardoptsmoke;

guardoptsmoke::guardoptsmoke_generated_tests!(crate::guardoptsmoke);

use guardoptsmoke::Int;

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
