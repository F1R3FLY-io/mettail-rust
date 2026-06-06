//! Tests for `weighted_mso::compile`.
//!
//! Phase 5 (predicated types): exercise every constructive rule of
//! the MSO → SFA compilation. Each test fixes a small label alphabet,
//! constructs a formula, calls `to_weighted_automaton`, and checks
//! the resulting `SymbolicAutomaton<KatBooleanAlgebra>` accepts/rejects
//! the words it should.
//!
//! Words are encoded as `Vec<HashMap<String, bool>>` because that is
//! what `KatBooleanAlgebra::Domain` is. Each map fixes the truth value
//! of every atom (`label_a`, `is_x`, `in_X`) at one position.

use crate::symbolic::KatBooleanAlgebra;
use crate::weighted_mso::{
    compile::{atom, build_algebra, build_unique_var_automaton, compile_formula, MsoCompileError},
    WeightedMsoFormula,
};
use std::collections::HashMap;

// ────────────────────────────────────────────────────────────────────
// Test helpers
// ────────────────────────────────────────────────────────────────────

/// A position in the encoded word: a closed-world map of every atom
/// in `algebra.atoms` to true/false.
fn position(algebra: &KatBooleanAlgebra, truths: &[(&str, bool)]) -> HashMap<String, bool> {
    let mut m = HashMap::new();
    for atom_name in &algebra.atoms {
        m.insert(atom_name.clone(), false);
    }
    for (k, v) in truths {
        m.insert((*k).to_string(), *v);
    }
    m
}

fn labels(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| s.to_string()).collect()
}

// ────────────────────────────────────────────────────────────────────
// Atomic compilations
// ────────────────────────────────────────────────────────────────────

#[test]
fn atomic_pos_accepts_word_with_correct_label_at_witness() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "a".to_string(),
        var: "x".to_string(),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a", "b"])).unwrap();

    // Word: position 0 is x AND has label_a → should accept
    let w = vec![position(&alg, &[(&atom::label("a"), true), (&atom::is_var("x"), true)])];
    assert!(sfa.accepts(&w), "expected acceptance: position 0 is x with label a");
}

#[test]
fn atomic_pos_rejects_word_with_wrong_label_at_witness() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "a".to_string(),
        var: "x".to_string(),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a", "b"])).unwrap();

    // Word: position 0 is x AND has label_b → should reject
    let w = vec![position(&alg, &[(&atom::label("b"), true), (&atom::is_var("x"), true)])];
    assert!(!sfa.accepts(&w), "expected rejection: position 0 is x with label b");
}

#[test]
fn neg_atomic_pos_accepts_when_witness_label_differs() {
    let formula = WeightedMsoFormula::NegAtomicPos {
        label: "a".to_string(),
        var: "x".to_string(),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a", "b"])).unwrap();

    let w = vec![position(&alg, &[(&atom::label("b"), true), (&atom::is_var("x"), true)])];
    assert!(sfa.accepts(&w));
}

#[test]
fn in_set_accepts_when_witness_in_set() {
    let formula = WeightedMsoFormula::InSet {
        var: "x".to_string(),
        set_var: "X".to_string(),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();

    let w = vec![position(
        &alg,
        &[
            (&atom::label("a"), true),
            (&atom::is_var("x"), true),
            (&atom::in_set("X"), true),
        ],
    )];
    assert!(sfa.accepts(&w));
}

#[test]
fn in_set_rejects_when_witness_not_in_set() {
    let formula = WeightedMsoFormula::InSet {
        var: "x".to_string(),
        set_var: "X".to_string(),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();

    let w = vec![position(
        &alg,
        &[
            (&atom::label("a"), true),
            (&atom::is_var("x"), true),
            (&atom::in_set("X"), false),
        ],
    )];
    assert!(!sfa.accepts(&w));
}

// ────────────────────────────────────────────────────────────────────
// Boolean closures
// ────────────────────────────────────────────────────────────────────

#[test]
fn and_requires_both_subformulas() {
    let formula = WeightedMsoFormula::And(
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        }),
        Box::new(WeightedMsoFormula::InSet {
            var: "x".to_string(),
            set_var: "X".to_string(),
        }),
    );
    let (alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();

    // Both: label_a + is_x + in_X
    let w_both = vec![position(
        &alg,
        &[
            (&atom::label("a"), true),
            (&atom::is_var("x"), true),
            (&atom::in_set("X"), true),
        ],
    )];
    assert!(sfa.accepts(&w_both));

    // Missing in_X
    let w_missing_set = vec![position(
        &alg,
        &[
            (&atom::label("a"), true),
            (&atom::is_var("x"), true),
            (&atom::in_set("X"), false),
        ],
    )];
    assert!(!sfa.accepts(&w_missing_set));
}

#[test]
fn or_accepts_either_subformula() {
    let formula = WeightedMsoFormula::Or(
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        }),
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "b".to_string(),
            var: "x".to_string(),
        }),
    );
    let (alg, sfa) = compile_formula(&formula, &labels(&["a", "b"])).unwrap();

    let w_a = vec![position(&alg, &[(&atom::label("a"), true), (&atom::is_var("x"), true)])];
    assert!(sfa.accepts(&w_a));

    let w_b = vec![position(&alg, &[(&atom::label("b"), true), (&atom::is_var("x"), true)])];
    assert!(sfa.accepts(&w_b));
}

// ────────────────────────────────────────────────────────────────────
// First-order existential
// ────────────────────────────────────────────────────────────────────

#[test]
fn exists_first_accepts_when_some_position_satisfies_body() {
    // ∃x. label_a(x) — accepts any word containing at least one
    // position labeled `a`.
    let formula = WeightedMsoFormula::ExistsFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        }),
    };
    let (alg, sfa) = compile_formula(&formula, &labels(&["a", "b"])).unwrap();

    // Word: just one position labeled a
    let w_a = vec![position(&alg, &[(&atom::label("a"), true)])];
    assert!(sfa.accepts(&w_a), "∃x. label_a(x) should accept [a]");

    // Word: just one position labeled b
    let w_b = vec![position(&alg, &[(&atom::label("b"), true)])];
    assert!(!sfa.accepts(&w_b), "∃x. label_a(x) should reject [b]");

    // Word: a then b
    let w_ab = vec![
        position(&alg, &[(&atom::label("a"), true)]),
        position(&alg, &[(&atom::label("b"), true)]),
    ];
    assert!(sfa.accepts(&w_ab), "∃x. label_a(x) should accept [a, b]");
}

#[test]
fn exists_first_rejects_empty_word() {
    let formula = WeightedMsoFormula::ExistsFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        }),
    };
    let (_alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();
    assert!(!sfa.accepts(&[]));
}

// ────────────────────────────────────────────────────────────────────
// Uniqueness automaton
// ────────────────────────────────────────────────────────────────────

#[test]
fn unique_var_automaton_accepts_exactly_one_witness() {
    let alg = KatBooleanAlgebra::new(vec![atom::is_var("x")]);
    let sfa = build_unique_var_automaton("x", &alg);

    // Empty: no witness — reject
    assert!(!sfa.accepts(&[]));

    // One position with is_x: accept
    let w_one = vec![position(&alg, &[(&atom::is_var("x"), true)])];
    assert!(sfa.accepts(&w_one));

    // Two positions with is_x: reject
    let w_two = vec![
        position(&alg, &[(&atom::is_var("x"), true)]),
        position(&alg, &[(&atom::is_var("x"), true)]),
    ];
    assert!(!sfa.accepts(&w_two));

    // Three positions, only middle is x: accept
    let w_middle = vec![
        position(&alg, &[(&atom::is_var("x"), false)]),
        position(&alg, &[(&atom::is_var("x"), true)]),
        position(&alg, &[(&atom::is_var("x"), false)]),
    ];
    assert!(sfa.accepts(&w_middle));
}

// ────────────────────────────────────────────────────────────────────
// Constants
// ────────────────────────────────────────────────────────────────────

#[test]
fn constant_true_accepts_everything() {
    let formula = WeightedMsoFormula::Constant("true".to_string());
    let (alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();
    assert!(sfa.accepts(&[]));
    assert!(sfa.accepts(&[position(&alg, &[(&atom::label("a"), true)])]));
}

#[test]
fn constant_false_accepts_nothing() {
    let formula = WeightedMsoFormula::Constant("false".to_string());
    let (alg, sfa) = compile_formula(&formula, &labels(&["a"])).unwrap();
    assert!(!sfa.accepts(&[]));
    assert!(!sfa.accepts(&[position(&alg, &[(&atom::label("a"), true)])]));
}

#[test]
fn non_boolean_constant_returns_error() {
    let formula = WeightedMsoFormula::Constant("3.14".to_string());
    let result = compile_formula(&formula, &labels(&["a"]));
    assert!(matches!(result, Err(MsoCompileError::NonBooleanConstant { .. })));
}

// ────────────────────────────────────────────────────────────────────
// Full MSO rejection
// ────────────────────────────────────────────────────────────────────

#[test]
fn forall_second_returns_full_mso_error() {
    let formula = WeightedMsoFormula::ForallSecond {
        var: "X".to_string(),
        body: Box::new(WeightedMsoFormula::Constant("true".to_string())),
    };
    let result = compile_formula(&formula, &labels(&["a"]));
    assert!(matches!(result, Err(MsoCompileError::FullMsoUnsupported { .. })));
}

// ────────────────────────────────────────────────────────────────────
// Algebra construction
// ────────────────────────────────────────────────────────────────────

#[test]
fn build_algebra_includes_all_required_atoms() {
    let formula = WeightedMsoFormula::And(
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        }),
        Box::new(WeightedMsoFormula::InSet {
            var: "x".to_string(),
            set_var: "X".to_string(),
        }),
    );
    let alg = build_algebra(&formula, &labels(&["a", "b"]));
    assert!(alg.atoms.contains(&atom::label("a")));
    assert!(alg.atoms.contains(&atom::label("b")));
    assert!(alg.atoms.contains(&atom::is_var("x")));
    assert!(alg.atoms.contains(&atom::in_set("X")));
}

#[test]
fn to_weighted_automaton_canonical_entry_point() {
    // Test the public WeightedMsoFormula::to_weighted_automaton
    // method exposed by the impl block in mod.rs.
    let formula = WeightedMsoFormula::AtomicPos {
        label: "a".to_string(),
        var: "x".to_string(),
    };
    let result = formula.to_weighted_automaton(&labels(&["a", "b"]));
    assert!(result.is_ok());
    let (alg, sfa) = result.unwrap();
    assert!(
        sfa.accepts(&[position(&alg, &[(&atom::label("a"), true), (&atom::is_var("x"), true)],)])
    );
}
