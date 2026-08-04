//! Differential oracle and deep-shape witness for the formula-analysis PDA.
//!
//! The recursive functions below are deliberately test-only. They preserve the pre-conversion
//! equations as an executable oracle over a bounded corpus; production source contains only the
//! explicit pushdown machine.

use std::sync::Arc;

use mettail_languages::rholang::{
    formula::{
        bool_formula, classify, host_matches_verdict, is_statically_false, is_statically_true,
        FormulaShape,
    },
    Proc,
};
use mettail_runtime::HashBag;

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

fn recursive_host_verdict(target: &Proc, formula: &Proc) -> Option<bool> {
    if recursive_false(formula) {
        return Some(false);
    }
    if recursive_true(formula) {
        return Some(true);
    }

    let kleene_and = |left: Option<bool>, right: Option<bool>| match (left, right) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    };
    let kleene_or = |left: Option<bool>, right: Option<bool>| match (left, right) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    };

    match classify(formula) {
        FormulaShape::Verum => Some(true),
        FormulaShape::Falsum => Some(false),
        FormulaShape::Conjunction(left, right) => {
            kleene_and(recursive_host_verdict(target, left), recursive_host_verdict(target, right))
        },
        FormulaShape::Disjunction(left, right) => {
            kleene_or(recursive_host_verdict(target, left), recursive_host_verdict(target, right))
        },
        FormulaShape::Negation(inner) => recursive_host_verdict(target, inner).map(|value| !value),
        FormulaShape::Implication(antecedent, consequent) => kleene_or(
            recursive_host_verdict(target, antecedent).map(|value| !value),
            recursive_host_verdict(target, consequent),
        ),
        FormulaShape::Separation(_) => None,
        // The bounded corpus contains no send-sugar spellings, so the production canonicalization
        // is the identity and this is the exact pre-conversion positive-only term arm.
        FormulaShape::Term => target.match_pattern(formula).map(|_| true),
    }
}

fn bounded_formula_corpus() -> Vec<Proc> {
    let mut corpus = vec![bool_formula(true), bool_formula(false), Proc::PZero];
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
            Proc::PPar(HashBag::from_iter([left, right])),
        ]);
    }
    corpus
}

#[test]
fn generated_pda_matches_the_recursive_truth_oracle() {
    let corpus = bounded_formula_corpus();
    assert!(corpus.len() >= 80, "anti-vacuity: the corpus must exercise every connective");

    for (index, formula) in corpus.iter().enumerate() {
        assert_eq!(
            is_statically_false(formula),
            recursive_false(formula),
            "static-false mismatch at corpus row {index}: {formula}"
        );
        assert_eq!(
            is_statically_true(formula),
            recursive_true(formula),
            "static-true mismatch at corpus row {index}: {formula}"
        );
        assert_eq!(
            host_matches_verdict(&Proc::PZero, formula),
            recursive_host_verdict(&Proc::PZero, formula),
            "host-verdict mismatch at corpus row {index}: {formula}"
        );
    }
}

#[test]
fn formula_truth_and_host_verdict_survive_a_deep_mutual_recursion_shape() {
    const DEPTH: usize = 32_768;

    let mut formula = bool_formula(true);
    for _ in 0..DEPTH {
        formula = Proc::Not(Arc::new(formula));
    }

    assert!(!is_statically_false(&formula));
    assert!(is_statically_true(&formula));
    assert_eq!(host_matches_verdict(&Proc::PZero, &formula), Some(true));
}
