//! ★D11 probe — is the missing cardinality check in the generated `HashBag`
//! COLLECTION arm a LIVE wrong answer, or is it masked upstream?
//!
//! Read of `macros/src/gen/term_ops/match_pattern.rs:600-660` (HashBag/Map/
//! PathMap) and `:679-702` (HashSet): both build `g_elems`/`p_elems`, then claim
//! one ground element per PATTERN element, and NEVER compare cardinalities. The
//! sibling `Vec` arm (`:663-677`) does check (`g_vec.len() != p_vec.len()`), so
//! the omission is an asymmetry.
//!
//! The predicted consequence is that a pattern which is a strict SUB-multiset of
//! the ground MATCHES. This file tests that prediction directly against the
//! generated matcher, rather than through `host_matches_verdict` — the
//! differential MATRIX rows for the same shapes are all green, which shows the
//! host DECLINES that route and therefore cannot witness the defect.
//!
//! In Rholang `PPar` is a `HashBag<Proc>` collection FIELD (not a collection
//! literal), so `p | q` is the shape that reaches the arm.

#![cfg(feature = "rholang")]

use mettail_languages::rholang::*;

fn parse(input: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{}`: {}", input, e))
}

/// A par pattern must account for EVERY element of the ground par.
/// `1 | 2 | 3` must NOT match the pattern `1 | 2`.
#[test]
fn par_pattern_must_account_for_every_ground_element() {
    let ground = parse("1 | 2 | 3");
    let pattern = parse("1 | 2");
    assert!(
        ground.match_pattern(&pattern).is_none(),
        "a par is a MULTISET: the pattern `1 | 2` leaves the ground element `3` \
         unaccounted for, so `1 | 2 | 3` must not match it"
    );
}

/// The satisfied companion — the guard must not degenerate into "reject all".
#[test]
fn par_pattern_still_matches_an_equal_par() {
    let ground = parse("1 | 2");
    let pattern = parse("1 | 2");
    assert!(ground.match_pattern(&pattern).is_some(), "an identical par must still match");
}

/// The converse direction: a pattern LARGER than the ground must also fail.
/// This already held (the claim loop runs out of unclaimed ground elements).
#[test]
fn par_pattern_larger_than_ground_does_not_match() {
    let ground = parse("1 | 2");
    let pattern = parse("1 | 2 | 3");
    assert!(
        ground.match_pattern(&pattern).is_none(),
        "a pattern with more elements than the ground must not match"
    );
}

/// ★ THE REACHABILITY FACT, pinned.
///
/// This is why the three tests above pass even though the `(PPar, PPar)` arm has
/// no cardinality check, and why the `rho_matches_differential` MATRIX cannot
/// witness ★D11: surface `|` does NOT build a `PPar(HashBag)`. It builds a
/// LEFT-NESTED BINARY INFIX TREE, `PParInfix(PParInfix(1, 2), 3)`, which is a
/// `Regular` variant — so cardinality is enforced by the tree SHAPE and the
/// unordered arm is never entered.
///
/// The canonical `PPar(HashBag)` form is produced by NORMALIZATION, not by
/// parsing, which is the route
/// `canonical_ppar_pattern_must_account_for_every_ground_element` takes.
///
/// Pinned as an assertion rather than left as a comment because the whole point
/// of this campaign is that unpinned reachability claims decay into folklore: a
/// future change that makes `|` parse directly to canonical `PPar` would
/// silently change which arm every par match takes, and this test is what would
/// say so.
#[test]
fn surface_par_syntax_builds_an_infix_tree_not_a_canonical_bag() {
    let ground = parse("1 | 2 | 3");
    assert!(
        matches!(ground, Proc::PParInfix(..)),
        "surface `|` must build the binary infix tree `PParInfix`, not a \
         canonical `PPar(HashBag)`; got {ground:?}"
    );
    assert!(
        !matches!(ground, Proc::PPar(_)),
        "if surface `|` ever starts building a canonical `PPar` directly, every \
         par match changes which generated arm it takes — re-derive the \
         reachability argument in this file before updating this assertion"
    );
}

/// ★ THE DECISIVE D11 TEST — build the CANONICAL `PPar(HashBag)` form directly.
///
/// Surface `|` parses to the binary infix tree `PParInfix`, which is a `Regular`
/// variant and therefore matches structurally (cardinality is enforced by the
/// tree shape). The `(PPar, PPar)` HashBag arm — the one missing the cardinality
/// check — is reached only by the CANONICAL par form that normalization
/// produces. This constructs that form directly, so the arm is definitely
/// exercised.
#[test]
fn canonical_ppar_pattern_must_account_for_every_ground_element() {
    let mut g = mettail_runtime::HashBag::new();
    g.insert(parse("1"));
    g.insert(parse("2"));
    g.insert(parse("3"));
    let ground = Proc::PPar(g);

    let mut p = mettail_runtime::HashBag::new();
    p.insert(parse("1"));
    p.insert(parse("2"));
    let pattern = Proc::PPar(p);

    let verdict = ground.match_pattern(&pattern).is_some();
    println!("CANONICAL PPar sub-multiset match = {verdict}  (must be false)");
    assert!(
        !verdict,
        "★D11: the canonical `PPar` HashBag arm has no cardinality check, so the \
         pattern {{1,2}} claims two of the three ground elements and the leftover \
         `3` is silently ignored — pattern ⊆ ground MATCHES when it must not"
    );
}
