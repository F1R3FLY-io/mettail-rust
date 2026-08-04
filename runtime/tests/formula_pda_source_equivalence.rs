//! Executable recursive-oracle equivalence for the production Rholang formula PDA source.
//!
//! The production `languages` crate expands a multi-megabyte generated Rholang module whose LLVM
//! codegen exceeds the local 4 GiB validation envelope. This test avoids weakening that envelope:
//! it includes the exact production `languages/src/rholang/formula.rs` source into a minimal
//! test-only syntax carrier containing every constructor the classifier reads. The PDA code under
//! test is therefore not copied or reimplemented; only its generated-AST adapter is minimized.

#[path = "support/formula_pda_carrier.rs"]
mod rholang;

use rholang::{
    formula::{
        bool_formula, classify, host_matches_verdict, is_statically_false, is_statically_true,
        FormulaShape,
    },
    Parts, Proc,
};
use std::sync::Arc;

fn recursive_false(formula: &Proc) -> bool {
    match classify(formula) {
        FormulaShape::Falsum => true,
        FormulaShape::Conjunction(left, right) => recursive_false(left) || recursive_false(right),
        FormulaShape::Disjunction(left, right) => recursive_false(left) && recursive_false(right),
        FormulaShape::Negation(inner) => recursive_true(inner),
        FormulaShape::Implication(antecedent, consequent) => {
            recursive_true(antecedent) && recursive_false(consequent)
        },
        FormulaShape::Separation(parts) => parts.into_iter().any(recursive_false),
        FormulaShape::Verum | FormulaShape::Term => false,
    }
}

fn recursive_true(formula: &Proc) -> bool {
    match classify(formula) {
        FormulaShape::Verum => true,
        FormulaShape::Conjunction(left, right) => recursive_true(left) && recursive_true(right),
        FormulaShape::Disjunction(left, right) => recursive_true(left) || recursive_true(right),
        FormulaShape::Negation(inner) => recursive_false(inner),
        FormulaShape::Implication(antecedent, consequent) => {
            recursive_false(antecedent) || recursive_true(consequent)
        },
        FormulaShape::Falsum | FormulaShape::Separation(_) | FormulaShape::Term => false,
    }
}

fn recursive_host(target: &Proc, formula: &Proc) -> Option<bool> {
    if recursive_false(formula) {
        return Some(false);
    }
    if recursive_true(formula) {
        return Some(true);
    }

    let and = |left, right| match (left, right) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    };
    let or = |left, right| match (left, right) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    };

    match classify(formula) {
        FormulaShape::Verum => Some(true),
        FormulaShape::Falsum => Some(false),
        FormulaShape::Conjunction(left, right) => {
            and(recursive_host(target, left), recursive_host(target, right))
        },
        FormulaShape::Disjunction(left, right) => {
            or(recursive_host(target, left), recursive_host(target, right))
        },
        FormulaShape::Negation(inner) => recursive_host(target, inner).map(|value| !value),
        FormulaShape::Implication(antecedent, consequent) => or(
            recursive_host(target, antecedent).map(|value| !value),
            recursive_host(target, consequent),
        ),
        FormulaShape::Separation(_) => None,
        FormulaShape::Term => target.match_pattern(formula).map(|_| true),
    }
}

fn bounded_corpus() -> Vec<Proc> {
    let mut corpus = vec![bool_formula(true), bool_formula(false), Proc::PZero, Proc::Term(1)];
    for depth in 0..12 {
        let left = corpus[(depth * 3) % corpus.len()].clone();
        let right = corpus[(depth * 5 + 1) % corpus.len()].clone();
        corpus.extend([
            Proc::Not(Arc::new(left.clone())),
            Proc::And(Arc::new(left.clone()), Arc::new(right.clone())),
            Proc::Or(Arc::new(left.clone()), Arc::new(right.clone())),
            Proc::Implies(Arc::new(left.clone()), Arc::new(right.clone())),
            Proc::SpatialPPar(Arc::new(left.clone()), Arc::new(right.clone())),
            Proc::PParInfix(Arc::new(left.clone()), Arc::new(right.clone())),
            Proc::PPar(Parts::new([left, right])),
        ]);
    }
    corpus
}

#[test]
fn production_formula_pda_source_matches_the_recursive_oracle() {
    let corpus = bounded_corpus();
    assert!(corpus.len() >= 80);
    for (row, formula) in corpus.iter().enumerate() {
        assert_eq!(is_statically_false(formula), recursive_false(formula), "false row {row}");
        assert_eq!(is_statically_true(formula), recursive_true(formula), "true row {row}");
        for target in [Proc::PZero, Proc::Term(1), Proc::Term(2)] {
            assert_eq!(
                host_matches_verdict(&target, formula),
                recursive_host(&target, formula),
                "host row {row}, target {target:?}"
            );
        }
    }
}

#[test]
fn production_formula_pda_source_survives_deep_mutual_recursion_shape() {
    const DEPTH: usize = 32_768;
    let mut formula = bool_formula(true);
    for _ in 0..DEPTH {
        formula = Proc::Not(Arc::new(formula));
    }

    assert!(!is_statically_false(&formula));
    assert!(is_statically_true(&formula));
    assert_eq!(host_matches_verdict(&Proc::PZero, &formula), Some(true));

    // This minimal carrier intentionally retains derived recursive Drop. The production generated
    // AST has its own iterative destructor, so forgetting here isolates the exact included PDA.
    std::mem::forget(formula);
}
