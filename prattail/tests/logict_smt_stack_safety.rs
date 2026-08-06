#![cfg(feature = "smt")]

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_prattail::algebra_tower::Sat3;
use mettail_prattail::logict_smt::{
    eval_constraint, is_satisfiable_3v, SmtConstraint, SmtModel, SmtTerm, Z3Theory,
};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum TermOracle {
    IntLit(i64),
    IntVar(String),
    BvLit(u64, u32),
    BvVar(String, u32),
    Add(Box<TermOracle>, Box<TermOracle>),
    Sub(Box<TermOracle>, Box<TermOracle>),
    Scale(i64, Box<TermOracle>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum ConstraintOracle {
    True,
    False,
    BoolVar(String),
    Eq(TermOracle, TermOracle),
    Le(TermOracle, TermOracle),
    Lt(TermOracle, TermOracle),
    Ge(TermOracle, TermOracle),
    Gt(TermOracle, TermOracle),
    Not(Box<ConstraintOracle>),
    And(Box<ConstraintOracle>, Box<ConstraintOracle>),
    Or(Box<ConstraintOracle>, Box<ConstraintOracle>),
}

fn hash(value: &impl Hash) -> u64 {
    let mut state = DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn deep_term(depth: usize) -> SmtTerm {
    let mut term = SmtTerm::IntLit(7);
    for _ in 0..depth {
        term = SmtTerm::Scale(1, Box::new(term));
    }
    term
}

fn term_depth(term: &SmtTerm) -> usize {
    let mut depth = 0;
    let mut current = term;
    while let SmtTerm::Scale(1, inner) = current {
        depth += 1;
        current = inner;
    }
    assert_eq!(current, &SmtTerm::IntLit(7));
    depth
}

fn deep_constraint(depth: usize) -> SmtConstraint {
    let mut constraint = SmtConstraint::True;
    for _ in 0..depth {
        constraint = SmtConstraint::Not(Box::new(constraint));
    }
    constraint
}

fn constraint_depth(constraint: &SmtConstraint) -> usize {
    let mut depth = 0;
    let mut current = constraint;
    while let SmtConstraint::Not(inner) = current {
        depth += 1;
        current = inner;
    }
    assert_eq!(current, &SmtConstraint::True);
    depth
}

#[test]
fn smt_lifecycle_and_evaluation_match_recursive_oracles() {
    let term = SmtTerm::Sub(
        Box::new(SmtTerm::Add(
            Box::new(SmtTerm::IntVar("x".into())),
            Box::new(SmtTerm::IntLit(2)),
        )),
        Box::new(SmtTerm::Scale(3, Box::new(SmtTerm::IntLit(4)))),
    );
    let term_oracle = TermOracle::Sub(
        Box::new(TermOracle::Add(
            Box::new(TermOracle::IntVar("x".into())),
            Box::new(TermOracle::IntLit(2)),
        )),
        Box::new(TermOracle::Scale(3, Box::new(TermOracle::IntLit(4)))),
    );
    assert_eq!(format!("{term:?}"), format!("{term_oracle:?}"));
    assert_eq!(format!("{:?}", term.clone()), format!("{term_oracle:?}"));
    assert_eq!(hash(&term), hash(&term_oracle));

    let constraint = SmtConstraint::Or(
        Box::new(SmtConstraint::And(
            Box::new(SmtConstraint::BoolVar("ready".into())),
            Box::new(SmtConstraint::Gt(term, SmtTerm::IntLit(0))),
        )),
        Box::new(SmtConstraint::Not(Box::new(SmtConstraint::Eq(
            SmtTerm::BvVar("byte".into(), 8),
            SmtTerm::BvLit(0, 8),
        )))),
    );
    let constraint_oracle = ConstraintOracle::Or(
        Box::new(ConstraintOracle::And(
            Box::new(ConstraintOracle::BoolVar("ready".into())),
            Box::new(ConstraintOracle::Gt(term_oracle, TermOracle::IntLit(0))),
        )),
        Box::new(ConstraintOracle::Not(Box::new(ConstraintOracle::Eq(
            TermOracle::BvVar("byte".into(), 8),
            TermOracle::BvLit(0, 8),
        )))),
    );
    assert_eq!(format!("{constraint:?}"), format!("{constraint_oracle:?}"));
    assert_eq!(hash(&constraint), hash(&constraint_oracle));
    assert_eq!(constraint, constraint.clone());

    let mut model = SmtModel::default();
    model.ints.insert("x".into(), 20);
    model.bvs.insert("byte".into(), 0);
    model.bools.insert("ready".into(), true);
    assert!(eval_constraint(&constraint, &model));
}

#[test]
fn smt_terms_constraints_and_translations_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let term = deep_term(DEPTH);
            let cloned_term = term.clone();
            assert_eq!(term, cloned_term);
            assert_eq!(term_depth(&cloned_term), DEPTH);
            assert!(format!("{term:?}").starts_with("Scale(1, Scale(1, "));
            let _ = hash(&term);

            let term_constraint = SmtConstraint::Eq(term, SmtTerm::IntLit(7));
            assert!(eval_constraint(&term_constraint, &SmtModel::default()));
            let theory = Z3Theory { timeout_ms: 5_000 };
            assert_eq!(is_satisfiable_3v(&theory, &term_constraint), Sat3::Sat);

            let constraint = deep_constraint(DEPTH);
            let cloned_constraint = constraint.clone();
            assert_eq!(constraint, cloned_constraint);
            assert_eq!(constraint_depth(&cloned_constraint), DEPTH);
            assert!(format!("{constraint:?}").starts_with("Not(Not(Not("));
            let _ = hash(&constraint);
            assert!(eval_constraint(&constraint, &SmtModel::default()));

            // Exercise the private iterative Z3 translators through the public
            // three-valued boundary. An even number of negations preserves `true`.
            assert_eq!(is_satisfiable_3v(&theory, &constraint), Sat3::Sat);

            drop(cloned_constraint);
            drop(constraint);
            drop(term_constraint);
            drop(cloned_term);
        })
        .expect("spawn SMT depth-gate thread")
        .join()
        .expect("SMT stack-safety gate");
}
