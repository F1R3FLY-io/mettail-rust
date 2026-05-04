//! Stage 3.13d (2026-05-01) — Bug B regression test.
//!
//! Verifies that `run_ascent` returns no duplicate `term_id`s in
//! `all_terms`. Pre-3.13d, `run_ascent_typed` double-seeded the input
//! term: a direct `prog.<cat>.push((initial.clone(),))` AND a carry-over
//! loop from `pre.<cat>.iter()`. Ascent's `relation foo(T)` is
//! `Vec`-backed at push time (no dedup until rule application), so two
//! byte-identical tuples survived. Result: `all_terms` had 2 entries
//! with identical `term_id`.
//!
//! Post-3.13d: when pre-stratum is present, the direct match is
//! suppressed and the carry-over loop is the single seed source.
//! When pre-stratum is absent, the direct match remains the only seed.

use std::collections::HashSet;

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::Language;

#[test]
fn all_terms_unique_term_ids() {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang.parse_term("2.0 + 2.5").expect("parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval");

    let ids: HashSet<u64> = results.all_terms.iter().map(|t| t.term_id).collect();
    assert_eq!(
        ids.len(),
        results.all_terms.len(),
        "all_terms must contain unique term_ids; got {} entries with {} unique ids: {:?}",
        results.all_terms.len(),
        ids.len(),
        results
            .all_terms
            .iter()
            .map(|t| (t.term_id, t.display.clone()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn no_duplicate_initial_in_relations() {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang.parse_term("2.0 + 2.5").expect("parse");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval");

    // Find entries displaying as the original input. There must be at
    // most one — pre-3.13d there were two (the dedup bug); post-3.13d
    // exactly one (the input's representation in its own category).
    let initial_count = results
        .all_terms
        .iter()
        .filter(|t| t.display == "2.0 + 2.5")
        .count();
    assert!(
        initial_count <= 1,
        "input must appear at most once in all_terms; got {} copies: {:?}",
        initial_count,
        results
            .all_terms
            .iter()
            .filter(|t| t.display == "2.0 + 2.5")
            .map(|t| (t.term_id, t.display.clone()))
            .collect::<Vec<_>>()
    );
}
