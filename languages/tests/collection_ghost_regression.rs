//! Regression guard for #307 TR: collection sub-multiset "ghost" alternatives.
//!
//! Before the element-category splice gate (commit 36353578), the language-trait
//! all-alternatives parse path surfaced spurious sub-multiset alternatives for
//! collections whose elements are cross-category (e.g. `{0 | 1}` also yielding
//! `{0}`), because a competing cursor lineage spliced an element's RAW
//! source-category Symbol PRE-WRAP and the finalize action silently dropped it.
//! The fix refutes such cursors at the source. These tests assert the ghosts
//! never return: each multi-element collection has EXACTLY one surviving
//! all-alternatives parse, and legitimate single/cross-cat collections still parse.

use mettail_languages::rhocalc;
use mettail_prattail::wpda_runtime::{LatticeTokenSource, WpdaTokenSource};

/// Parse `input` via the language-trait all-alternatives path; return the
/// realized-term Display strings (the surface where the ghost appeared).
fn all_alts_displays(input: &str) -> Vec<String> {
    let dag = rhocalc::lex_dag(input).unwrap_or_else(|e| panic!("lex `{input}`: {e}"));
    let source = LatticeTokenSource::new(dag);
    let mut pos = 0usize;
    let (terms, _weights) = rhocalc::parse_Proc_via_wpda_all_with_source(&source, &mut pos, 0)
        .unwrap_or_else(|e| panic!("all_alts parse `{input}`: {e}"));
    assert_eq!(pos, source.eof_node(), "`{input}` must consume to EOI");
    terms.iter().map(|t| format!("{t}")).collect()
}

#[test]
fn no_sub_multiset_ghost_two_elements() {
    let alts = all_alts_displays("{0 | 1}");
    assert_eq!(alts, vec!["{0 | 1}".to_string()], "exactly the full bag, no `{{0}}` ghost");
}

#[test]
fn no_sub_multiset_ghost_three_elements() {
    let alts = all_alts_displays("{0 | 1 | 2}");
    assert_eq!(
        alts,
        vec!["{0 | 1 | 2}".to_string()],
        "no `{{0 | 1}}` / `{{0 | 2}}` sub-multiset ghosts"
    );
}

#[test]
fn no_sub_multiset_ghost_grouped_element() {
    let alts = all_alts_displays("{(1) | 2}");
    assert_eq!(alts, vec!["{1 | 2}".to_string()], "grouped element, no `{{1}}` ghost");
}

#[test]
fn single_element_collection_preserved() {
    // A genuine single-element collection must still parse (not a ghost).
    let alts = all_alts_displays("{0}");
    assert_eq!(alts, vec!["{0}".to_string()]);
}

#[test]
fn cross_category_elements_preserved() {
    // `error` (cross-cat: Int/BigInt/BigRat/Proc) and `a` (cross-cat var) are both
    // legitimate Proc elements via their wraps — the gate must NOT refute them.
    // (HashBag display order is canonical, hence `{a | error}`.)
    let alts = all_alts_displays("{error | a}");
    assert_eq!(alts, vec!["{a | error}".to_string()], "cross-cat elements preserved, no ghost");
}
