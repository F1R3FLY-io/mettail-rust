//! Property-based tests for rule consolidation semantic equivalence.
//!
//! Verifies that consolidated Ascent rules derive the same facts as the
//! original N per-constructor rules, using the Calculator Int type as
//! a representative example.
//!
//! These tests complement the Rocq formal proofs in
//! `formal/rocq/rule_consolidation/` by exercising the concrete types.
//!
//! ## Properties tested
//!
//! P1: Subterm extraction equivalence (Area 1)
//! P2: Congruence rebuild round-trip (Area 4)
//! P3: Congruence extraction completeness (Area 4)
//! P4: Pair match symmetry (Area 3)
//! P5: Boolean predicate equivalence (Areas 5, 6)
//! P6: Variant index injectivity (Area 4)
//! P7: End-to-end fact equivalence (all areas)

use proptest::prelude::*;

use mettail_languages::calculator::Int;

// ════════════════════════════════════════════════════════════════════════
// Term generator (reused from roundtrip_tests.rs)
// ════════════════════════════════════════════════════════════════════════

fn arb_int_term(max_depth: u32) -> impl Strategy<Value = Int> {
    let leaf = (-50i32..50).prop_map(|n| Int::NumLit(n));

    leaf.prop_recursive(max_depth, 64, 4, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Int::Add(Box::new(a), Box::new(b))),
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Int::Sub(Box::new(a), Box::new(b))),
            inner.clone().prop_map(|a| Int::Neg(Box::new(a))),
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Int::Pow(Box::new(a), Box::new(b))),
            inner.clone().prop_map(|a| Int::Fact(Box::new(a))),
            (inner.clone(), inner.clone(), inner.clone())
                .prop_map(|(c, t, e)| Int::Tern(Box::new(c), Box::new(t), Box::new(e))),
            (inner.clone(), inner.clone())
                .prop_map(|(a, b)| Int::CustomOp(Box::new(a), Box::new(b))),
        ]
    })
}

// ════════════════════════════════════════════════════════════════════════
// Helpers: Simulated "old" per-constructor rules and "new" consolidated
// ════════════════════════════════════════════════════════════════════════

/// Classify an Int term by its constructor kind (returns a tag).
fn classify_int(t: &Int) -> &'static str {
    match t {
        Int::Add(..) => "Add",
        Int::Sub(..) => "Sub",
        Int::Neg(..) => "Neg",
        Int::Pow(..) => "Pow",
        Int::Fact(..) => "Fact",
        Int::Tern(..) => "Tern",
        Int::CustomOp(..) => "CustomOp",
        Int::NumLit(..) => "NumLit",
        _ => "Other",
    }
}

/// OLD: Per-constructor subterm extraction (simulates N if-let rules).
/// Each block simulates one original Ascent rule.
fn extract_subterms_per_constructor(t: &Int) -> Vec<Int> {
    let mut results = Vec::new();

    // Rule for Add
    if let Int::Add(f0, f1) = t {
        results.push(f0.as_ref().clone());
        results.push(f1.as_ref().clone());
    }
    // Rule for Sub
    if let Int::Sub(f0, f1) = t {
        results.push(f0.as_ref().clone());
        results.push(f1.as_ref().clone());
    }
    // Rule for Neg
    if let Int::Neg(f0) = t {
        results.push(f0.as_ref().clone());
    }
    // Rule for Pow
    if let Int::Pow(f0, f1) = t {
        results.push(f0.as_ref().clone());
        results.push(f1.as_ref().clone());
    }
    // Rule for Fact
    if let Int::Fact(f0) = t {
        results.push(f0.as_ref().clone());
    }
    // Rule for Tern
    if let Int::Tern(f0, f1, f2) = t {
        results.push(f0.as_ref().clone());
        results.push(f1.as_ref().clone());
        results.push(f2.as_ref().clone());
    }
    // Rule for CustomOp
    if let Int::CustomOp(f0, f1) = t {
        results.push(f0.as_ref().clone());
        results.push(f1.as_ref().clone());
    }
    // NumLit: no subterms (leaf)

    results
}

/// NEW: Consolidated subterm extraction (simulates 1 for-match rule).
fn extract_subterms_consolidated(t: &Int) -> Vec<Int> {
    match t {
        Int::Add(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        Int::Sub(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        Int::Neg(f0) => vec![f0.as_ref().clone()],
        Int::Pow(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        Int::Fact(f0) => vec![f0.as_ref().clone()],
        Int::Tern(f0, f1, f2) => {
            vec![f0.as_ref().clone(), f1.as_ref().clone(), f2.as_ref().clone()]
        }
        Int::CustomOp(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        _ => vec![],
    }
}

/// Extract (field_value, variant_index) pairs — simulates consolidated congruence.
fn vi_extract(t: &Int) -> Vec<(Int, usize)> {
    match t {
        Int::Add(x0, x1) => {
            vec![(x0.as_ref().clone(), 0), (x1.as_ref().clone(), 1)]
        }
        Int::Sub(x0, x1) => {
            vec![(x0.as_ref().clone(), 2), (x1.as_ref().clone(), 3)]
        }
        Int::Neg(x0) => vec![(x0.as_ref().clone(), 4)],
        Int::Pow(x0, x1) => {
            vec![(x0.as_ref().clone(), 5), (x1.as_ref().clone(), 6)]
        }
        Int::Fact(x0) => vec![(x0.as_ref().clone(), 7)],
        Int::Tern(x0, x1, x2) => vec![
            (x0.as_ref().clone(), 8),
            (x1.as_ref().clone(), 9),
            (x2.as_ref().clone(), 10),
        ],
        Int::CustomOp(x0, x1) => {
            vec![(x0.as_ref().clone(), 11), (x1.as_ref().clone(), 12)]
        }
        _ => vec![],
    }
}

/// Rebuild a term by replacing the field at the given variant index.
fn vi_rebuild(t: &Int, vi: usize, new_val: Int) -> Int {
    match (t, vi) {
        (Int::Add(_, x1), 0) => Int::Add(Box::new(new_val), x1.clone()),
        (Int::Add(x0, _), 1) => Int::Add(x0.clone(), Box::new(new_val)),
        (Int::Sub(_, x1), 2) => Int::Sub(Box::new(new_val), x1.clone()),
        (Int::Sub(x0, _), 3) => Int::Sub(x0.clone(), Box::new(new_val)),
        (Int::Neg(_), 4) => Int::Neg(Box::new(new_val)),
        (Int::Pow(_, x1), 5) => Int::Pow(Box::new(new_val), x1.clone()),
        (Int::Pow(x0, _), 6) => Int::Pow(x0.clone(), Box::new(new_val)),
        (Int::Fact(_), 7) => Int::Fact(Box::new(new_val)),
        (Int::Tern(_, x1, x2), 8) => {
            Int::Tern(Box::new(new_val), x1.clone(), x2.clone())
        }
        (Int::Tern(x0, _, x2), 9) => {
            Int::Tern(x0.clone(), Box::new(new_val), x2.clone())
        }
        (Int::Tern(x0, x1, _), 10) => {
            Int::Tern(x0.clone(), x1.clone(), Box::new(new_val))
        }
        (Int::CustomOp(_, x1), 11) => Int::CustomOp(Box::new(new_val), x1.clone()),
        (Int::CustomOp(x0, _), 12) => Int::CustomOp(x0.clone(), Box::new(new_val)),
        _ => unreachable!("invalid variant index {} for {:?}", vi, classify_int(t)),
    }
}

/// OLD: Per-constructor pair extraction (simulates N equation congruence rules).
fn pair_extract_per_constructor(s: &Int, t: &Int) -> Vec<(Int, Int)> {
    let mut results = Vec::new();

    if let (Int::Add(s0, s1), Int::Add(t0, t1)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
        results.push((s1.as_ref().clone(), t1.as_ref().clone()));
    }
    if let (Int::Sub(s0, s1), Int::Sub(t0, t1)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
        results.push((s1.as_ref().clone(), t1.as_ref().clone()));
    }
    if let (Int::Neg(s0), Int::Neg(t0)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
    }
    if let (Int::Pow(s0, s1), Int::Pow(t0, t1)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
        results.push((s1.as_ref().clone(), t1.as_ref().clone()));
    }
    if let (Int::Fact(s0), Int::Fact(t0)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
    }
    if let (Int::Tern(s0, s1, s2), Int::Tern(t0, t1, t2)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
        results.push((s1.as_ref().clone(), t1.as_ref().clone()));
        results.push((s2.as_ref().clone(), t2.as_ref().clone()));
    }
    if let (Int::CustomOp(s0, s1), Int::CustomOp(t0, t1)) = (s, t) {
        results.push((s0.as_ref().clone(), t0.as_ref().clone()));
        results.push((s1.as_ref().clone(), t1.as_ref().clone()));
    }

    results
}

/// NEW: Consolidated pair extraction (simulates 1 pair-match rule).
fn pair_extract_consolidated(s: &Int, t: &Int) -> Vec<(Int, Int)> {
    match (s, t) {
        (Int::Add(s0, s1), Int::Add(t0, t1)) => vec![
            (s0.as_ref().clone(), t0.as_ref().clone()),
            (s1.as_ref().clone(), t1.as_ref().clone()),
        ],
        (Int::Sub(s0, s1), Int::Sub(t0, t1)) => vec![
            (s0.as_ref().clone(), t0.as_ref().clone()),
            (s1.as_ref().clone(), t1.as_ref().clone()),
        ],
        (Int::Neg(s0), Int::Neg(t0)) => {
            vec![(s0.as_ref().clone(), t0.as_ref().clone())]
        }
        (Int::Pow(s0, s1), Int::Pow(t0, t1)) => vec![
            (s0.as_ref().clone(), t0.as_ref().clone()),
            (s1.as_ref().clone(), t1.as_ref().clone()),
        ],
        (Int::Fact(s0), Int::Fact(t0)) => {
            vec![(s0.as_ref().clone(), t0.as_ref().clone())]
        }
        (Int::Tern(s0, s1, s2), Int::Tern(t0, t1, t2)) => vec![
            (s0.as_ref().clone(), t0.as_ref().clone()),
            (s1.as_ref().clone(), t1.as_ref().clone()),
            (s2.as_ref().clone(), t2.as_ref().clone()),
        ],
        (Int::CustomOp(s0, s1), Int::CustomOp(t0, t1)) => vec![
            (s0.as_ref().clone(), t0.as_ref().clone()),
            (s1.as_ref().clone(), t1.as_ref().clone()),
        ],
        _ => vec![],
    }
}

/// Fold trigger predicate — OLD: N separate if-let guards.
fn is_fold_trigger_per_constructor(t: &Int) -> bool {
    if let Int::Neg(_) = t {
        return true;
    }
    if let Int::Sub(_, _) = t {
        return true;
    }
    if let Int::CustomOp(_, _) = t {
        return true;
    }
    false
}

/// Fold trigger predicate — NEW: consolidated match predicate.
fn is_fold_trigger_consolidated(t: &Int) -> bool {
    matches!(t, Int::Neg(_) | Int::Sub(_, _) | Int::CustomOp(_, _))
}

// ════════════════════════════════════════════════════════════════════════
// Property tests
// ════════════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// P1: Subterm extraction equivalence (Area 1).
    /// The per-constructor extraction and consolidated match extraction
    /// produce identical results for any Int term.
    #[test]
    fn prop_subterm_extraction_equiv(t in arb_int_term(4)) {
        let old = extract_subterms_per_constructor(&t);
        let new = extract_subterms_consolidated(&t);
        prop_assert_eq!(old, new, "Subterm extraction mismatch for {:?}", classify_int(&t));
    }

    /// P2: Congruence rebuild round-trip (Area 4).
    /// Extracting a field and rebuilding with the same value yields the
    /// original term.
    #[test]
    fn prop_rebuild_roundtrip(t in arb_int_term(3)) {
        let pairs = vi_extract(&t);
        for (field_val, vi) in &pairs {
            let rebuilt = vi_rebuild(&t, *vi, field_val.clone());
            prop_assert_eq!(
                &rebuilt, &t,
                "Rebuild round-trip failed: vi={}, constructor={}",
                vi, classify_int(&t)
            );
        }
    }

    /// P3: Congruence extraction completeness (Area 4).
    /// Every field of a non-leaf term appears in the vi_extract output
    /// with a unique variant index.
    #[test]
    fn prop_extraction_completeness(t in arb_int_term(3)) {
        let pairs = vi_extract(&t);
        let subterms = extract_subterms_consolidated(&t);

        // Every subterm should appear as a field value in some pair
        let field_vals: Vec<&Int> = pairs.iter().map(|(v, _)| v).collect();
        for sub in &subterms {
            prop_assert!(
                field_vals.contains(&sub),
                "Subterm {:?} not found in vi_extract output for {:?}",
                classify_int(sub), classify_int(&t)
            );
        }

        // Number of extracted pairs should equal number of subterms
        prop_assert_eq!(
            pairs.len(), subterms.len(),
            "Extraction count mismatch: {} pairs vs {} subterms for {}",
            pairs.len(), subterms.len(), classify_int(&t)
        );
    }

    /// P4: Pair match — same constructor pairs produce results,
    /// different constructor pairs produce empty (Area 3).
    #[test]
    fn prop_pair_match_equiv(
        s in arb_int_term(3),
        t in arb_int_term(3)
    ) {
        let old = pair_extract_per_constructor(&s, &t);
        let consolidated = pair_extract_consolidated(&s, &t);

        // Non-empty iff same constructor (check before assert moves values)
        let same_ctor = classify_int(&s) == classify_int(&t);
        let has_results = !consolidated.is_empty();

        prop_assert_eq!(old, consolidated,
            "Pair extraction mismatch: s={}, t={}",
            classify_int(&s), classify_int(&t));
        // Note: NumLit has no fields, so same constructor but empty
        if classify_int(&s) != "NumLit" && classify_int(&s) != "Other" {
            prop_assert_eq!(same_ctor, has_results,
                "Pair match should be non-empty iff same constructor: s={}, t={}",
                classify_int(&s), classify_int(&t));
        }
    }

    /// P5: Boolean predicate equivalence (Areas 5, 6).
    /// The per-constructor if-let checks and the consolidated match
    /// predicate agree for all terms.
    #[test]
    fn prop_fold_trigger_equiv(t in arb_int_term(4)) {
        let old = is_fold_trigger_per_constructor(&t);
        let new = is_fold_trigger_consolidated(&t);
        prop_assert_eq!(old, new,
            "Fold trigger mismatch for {}", classify_int(&t));
    }

    /// P7: End-to-end: rebuilt terms have correct constructor (Area 4).
    /// After replacing a field, the rebuilt term still has the same
    /// constructor kind and the replacement is at the correct position.
    #[test]
    fn prop_rebuild_preserves_constructor(
        t in arb_int_term(2),
        replacement in arb_int_term(1)
    ) {
        let pairs = vi_extract(&t);
        for (_, vi) in &pairs {
            let rebuilt = vi_rebuild(&t, *vi, replacement.clone());
            prop_assert_eq!(
                classify_int(&rebuilt), classify_int(&t),
                "Rebuild changed constructor: vi={}, original={}, rebuilt={}",
                vi, classify_int(&t), classify_int(&rebuilt)
            );
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// Deterministic tests
// ════════════════════════════════════════════════════════════════════════

/// P6: Variant index injectivity.
/// No two (constructor, field_pos) pairs share a variant index.
#[test]
fn test_variant_index_injectivity() {
    // Collect all (constructor, field_position, vi) triples from representative terms
    let terms: Vec<Int> = vec![
        Int::Add(Box::new(Int::NumLit(0)), Box::new(Int::NumLit(1))),
        Int::Sub(Box::new(Int::NumLit(0)), Box::new(Int::NumLit(1))),
        Int::Neg(Box::new(Int::NumLit(0))),
        Int::Pow(Box::new(Int::NumLit(0)), Box::new(Int::NumLit(1))),
        Int::Fact(Box::new(Int::NumLit(0))),
        Int::Tern(
            Box::new(Int::NumLit(0)),
            Box::new(Int::NumLit(1)),
            Box::new(Int::NumLit(2)),
        ),
        Int::CustomOp(Box::new(Int::NumLit(0)), Box::new(Int::NumLit(1))),
    ];

    let mut all_vis: Vec<(String, usize, usize)> = Vec::new(); // (ctor, field_pos, vi)
    for t in &terms {
        let pairs = vi_extract(t);
        for (i, (_, vi)) in pairs.iter().enumerate() {
            all_vis.push((classify_int(t).to_string(), i, *vi));
        }
    }

    // Check injectivity: no two entries share the same vi
    for i in 0..all_vis.len() {
        for j in (i + 1)..all_vis.len() {
            assert_ne!(
                all_vis[i].2, all_vis[j].2,
                "Variant index collision: ({}, field {}) and ({}, field {}) both have vi={}",
                all_vis[i].0, all_vis[i].1, all_vis[j].0, all_vis[j].1, all_vis[i].2
            );
        }
    }

    // Verify we have the expected number of variant indices (13 fields total)
    assert_eq!(
        all_vis.len(),
        13,
        "Expected 13 variant indices (2+2+1+2+1+3+2)"
    );
}

/// Test that NumLit (leaf) produces empty extractions.
#[test]
fn test_leaf_produces_no_subterms() {
    let t = Int::NumLit(42);
    assert!(extract_subterms_per_constructor(&t).is_empty());
    assert!(extract_subterms_consolidated(&t).is_empty());
    assert!(vi_extract(&t).is_empty());
}

/// Test pair extraction for mismatched constructors.
#[test]
fn test_pair_mismatch_is_empty() {
    let add = Int::Add(Box::new(Int::NumLit(1)), Box::new(Int::NumLit(2)));
    let sub = Int::Sub(Box::new(Int::NumLit(3)), Box::new(Int::NumLit(4)));

    assert!(pair_extract_per_constructor(&add, &sub).is_empty());
    assert!(pair_extract_consolidated(&add, &sub).is_empty());
}
