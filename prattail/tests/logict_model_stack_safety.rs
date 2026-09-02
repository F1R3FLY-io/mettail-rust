use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use mettail_prattail::algebra_tower::RejectSafeAlgebra;
use mettail_prattail::logict::{
    evaluate_quantified, evaluate_quantified_with_theory, ConstraintTheory, LogicStream,
    QuantifiedArg, QuantifiedDomain, QuantifiedFormula, TheoryAlgebra, TheoryPred, TriState,
};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum FormulaOracle {
    Atom {
        relation: String,
        args: Vec<QuantifiedArg>,
    },
    And(Box<FormulaOracle>, Box<FormulaOracle>),
    Or(Box<FormulaOracle>, Box<FormulaOracle>),
    Not(Box<FormulaOracle>),
    Implies(Box<FormulaOracle>, Box<FormulaOracle>),
    ForAll {
        var: String,
        domain: QuantifiedDomain,
        body: Box<FormulaOracle>,
    },
    Exists {
        var: String,
        domain: QuantifiedDomain,
        body: Box<FormulaOracle>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum PredicateOracle {
    True,
    False,
    Atom(bool),
    And(Box<PredicateOracle>, Box<PredicateOracle>),
    Or(Box<PredicateOracle>, Box<PredicateOracle>),
    Not(Box<PredicateOracle>),
}

#[derive(Clone, Debug)]
struct UnitTheory;

impl ConstraintTheory for UnitTheory {
    type Constraint = bool;
    type Assignment = bool;
    type Store = bool;

    fn empty_store(&self) -> Self::Store {
        true
    }

    fn propagate(&self, store: &Self::Store, constraint: &Self::Constraint) -> Option<Self::Store> {
        (*constraint && *store).then_some(true)
    }

    fn is_consistent(&self, store: &Self::Store) -> bool {
        *store
    }

    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment> {
        (*store).then_some(true)
    }

    fn label(&self, _store: &Self::Store) -> LogicStream<Self::Constraint> {
        LogicStream::empty()
    }

    fn evaluate(&self, constraint: &Self::Constraint, assignment: &Self::Assignment) -> bool {
        *constraint && *assignment
    }
}

fn hash(value: &impl Hash) -> u64 {
    let mut state = DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn nested_quantifiers(depth: usize) -> QuantifiedFormula {
    let mut formula = QuantifiedFormula::atom("is_one", vec![QuantifiedArg::var("x")]);
    for _ in 0..depth {
        formula = QuantifiedFormula::forall("x", QuantifiedDomain::Relation("one".into()), formula);
    }
    formula
}

fn quantifier_depth(formula: &QuantifiedFormula) -> usize {
    let mut depth = 0;
    let mut current = formula;
    while let QuantifiedFormula::ForAll { body, .. } = current {
        depth += 1;
        current = body;
    }
    assert!(matches!(current, QuantifiedFormula::Atom { .. }));
    depth
}

fn nested_predicate(depth: usize) -> TheoryPred<UnitTheory> {
    let mut predicate = TheoryPred::Atom(true);
    for _ in 0..depth {
        predicate = TheoryPred::And(Box::new(TheoryPred::Atom(true)), Box::new(predicate));
    }
    predicate
}

fn predicate_depth(predicate: &TheoryPred<UnitTheory>) -> usize {
    let mut depth = 0;
    let mut current = predicate;
    while let TheoryPred::And(_, right) = current {
        depth += 1;
        current = right;
    }
    assert_eq!(current, &TheoryPred::Atom(true));
    depth
}

#[test]
fn logict_model_lifecycle_matches_recursive_derive_oracles() {
    let formula = QuantifiedFormula::ForAll {
        var: "x".into(),
        domain: QuantifiedDomain::Bounded { relation: "items".into(), limit: 4 },
        body: Box::new(QuantifiedFormula::Implies(
            Box::new(QuantifiedFormula::Atom {
                relation: "live".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
            Box::new(QuantifiedFormula::Not(Box::new(QuantifiedFormula::Atom {
                relation: "blocked".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }))),
        )),
    };
    let formula_oracle = FormulaOracle::ForAll {
        var: "x".into(),
        domain: QuantifiedDomain::Bounded { relation: "items".into(), limit: 4 },
        body: Box::new(FormulaOracle::Implies(
            Box::new(FormulaOracle::Atom {
                relation: "live".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }),
            Box::new(FormulaOracle::Not(Box::new(FormulaOracle::Atom {
                relation: "blocked".into(),
                args: vec![QuantifiedArg::Var("x".into())],
            }))),
        )),
    };
    assert_eq!(format!("{formula:?}"), format!("{formula_oracle:?}"));
    assert_eq!(format!("{:?}", formula.clone()), format!("{formula_oracle:?}"));
    assert_eq!(formula, formula.clone());
    assert_eq!(formula.to_string(), "∀x ∈ items[≤4]. (live(x) ⇒ ¬blocked(x))");

    let predicate = TheoryPred::<UnitTheory>::Or(
        Box::new(TheoryPred::And(Box::new(TheoryPred::Atom(true)), Box::new(TheoryPred::False))),
        Box::new(TheoryPred::Not(Box::new(TheoryPred::Atom(false)))),
    );
    let predicate_oracle = PredicateOracle::Or(
        Box::new(PredicateOracle::And(
            Box::new(PredicateOracle::Atom(true)),
            Box::new(PredicateOracle::False),
        )),
        Box::new(PredicateOracle::Not(Box::new(PredicateOracle::Atom(false)))),
    );
    assert_eq!(format!("{predicate:?}"), format!("{predicate_oracle:?}"));
    assert_eq!(hash(&predicate), hash(&predicate_oracle));
    assert_eq!(predicate, predicate.clone());
}

#[test]
fn quantified_formula_and_theory_predicate_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let formula = nested_quantifiers(DEPTH);
            let cloned_formula = formula.clone();
            assert_eq!(formula, cloned_formula);
            assert_eq!(quantifier_depth(&cloned_formula), DEPTH);
            assert!(formula.free_vars().is_empty());
            assert!(format!("{formula:?}").starts_with("ForAll { var: \"x\""));
            assert!(formula.to_string().starts_with("∀x ∈ one. ∀x ∈ one. "));

            let env = HashMap::new();
            let relation_query =
                |relation: &str, args: &[String]| relation == "is_one" && args == ["1"];
            let domain_enumerate = |relation: &str| match relation {
                "one" => vec![vec!["1".into()]],
                _ => Vec::new(),
            };
            assert!(evaluate_quantified(&formula, &env, &relation_query, &domain_enumerate, 1,));
            assert_eq!(
                evaluate_quantified_with_theory(
                    &formula,
                    &UnitTheory,
                    &relation_query,
                    &domain_enumerate,
                    &env,
                    1,
                ),
                TriState::True
            );

            let predicate = nested_predicate(DEPTH);
            let cloned_predicate = predicate.clone();
            assert_eq!(predicate, cloned_predicate);
            assert_eq!(predicate_depth(&cloned_predicate), DEPTH);
            assert!(format!("{predicate:?}").starts_with("And(Atom(true), And("));
            let _ = hash(&predicate);

            let algebra = TheoryAlgebra::new(UnitTheory, 1);
            assert!(algebra.evaluate(&predicate, &true));
            assert_eq!(algebra.witness(&predicate), Some(true));

            drop(cloned_predicate);
            drop(predicate);
            drop(cloned_formula);
            drop(formula);
        })
        .expect("spawn LogicT model depth-gate thread")
        .join()
        .expect("LogicT model stack-safety gate");
}
