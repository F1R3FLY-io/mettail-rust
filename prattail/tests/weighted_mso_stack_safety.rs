use std::collections::{hash_map::DefaultHasher, HashSet};
use std::hash::{Hash, Hasher};

use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::weighted_mso::compile::MsoCompileError;
use mettail_prattail::weighted_mso::{
    analyze_formula, classify_formula, evaluate_formula_bool, free_set_variables, free_variables,
    Assignment, MsoFormulaClass, WeightedMsoFormula,
};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("weighted-mso-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn weighted-MSO small-stack gate")
        .join()
        .expect("weighted-MSO small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn recursive_evaluate(
    formula: &WeightedMsoFormula,
    word: &[String],
    assignment: &Assignment,
) -> BooleanWeight {
    match formula {
        WeightedMsoFormula::Constant(value) => match value.as_str() {
            "false" | "0" => BooleanWeight::zero(),
            _ => BooleanWeight::one(),
        },
        WeightedMsoFormula::AtomicPos { label, var } => {
            let position = assignment.first_order[var];
            bool_weight(position < word.len() && word[position] == *label)
        },
        WeightedMsoFormula::NegAtomicPos { label, var } => {
            let position = assignment.first_order[var];
            bool_weight(!(position < word.len() && word[position] == *label))
        },
        WeightedMsoFormula::Order { x, y } => {
            bool_weight(assignment.first_order[x] <= assignment.first_order[y])
        },
        WeightedMsoFormula::NegOrder { x, y } => {
            bool_weight(assignment.first_order[x] > assignment.first_order[y])
        },
        WeightedMsoFormula::InSet { var, set_var } => {
            bool_weight(assignment.second_order[set_var].contains(&assignment.first_order[var]))
        },
        WeightedMsoFormula::NotInSet { var, set_var } => {
            bool_weight(!assignment.second_order[set_var].contains(&assignment.first_order[var]))
        },
        WeightedMsoFormula::Or(left, right) => recursive_evaluate(left, word, assignment)
            .plus(&recursive_evaluate(right, word, assignment)),
        WeightedMsoFormula::And(left, right) => recursive_evaluate(left, word, assignment)
            .times(&recursive_evaluate(right, word, assignment)),
        WeightedMsoFormula::ExistsFirst { var, body } => {
            let mut environment = assignment.clone();
            let mut result = BooleanWeight::zero();
            for position in 0..word.len() {
                environment.first_order.insert(var.clone(), position);
                result = result.plus(&recursive_evaluate(body, word, &environment));
                if result.is_one() {
                    break;
                }
            }
            result
        },
        WeightedMsoFormula::ForallFirst { var, body } => {
            let mut environment = assignment.clone();
            let mut result = BooleanWeight::one();
            for position in 0..word.len() {
                environment.first_order.insert(var.clone(), position);
                result = result.times(&recursive_evaluate(body, word, &environment));
                if result.is_zero() {
                    break;
                }
            }
            result
        },
        WeightedMsoFormula::ExistsSecond { var, body }
        | WeightedMsoFormula::ForallSecond { var, body } => {
            assert!(word.len() < 64, "the shallow oracle only accepts short words");
            let existential = matches!(formula, WeightedMsoFormula::ExistsSecond { .. });
            let mut environment = assignment.clone();
            let mut result = bool_weight(!existential);
            for mask in 0..(1u64 << word.len()) {
                let subset = (0..word.len())
                    .filter(|bit| mask & (1u64 << bit) != 0)
                    .collect::<HashSet<_>>();
                environment.second_order.insert(var.clone(), subset);
                let value = recursive_evaluate(body, word, &environment);
                result = if existential {
                    result.plus(&value)
                } else {
                    result.times(&value)
                };
                if (existential && result.is_one()) || (!existential && result.is_zero()) {
                    break;
                }
            }
            result
        },
    }
}

fn bool_weight(value: bool) -> BooleanWeight {
    if value {
        BooleanWeight::one()
    } else {
        BooleanWeight::zero()
    }
}

#[test]
fn lifecycle_analysis_and_evaluation_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = WeightedMsoFormula::AtomicPos {
            label: "a".to_string(),
            var: "x".to_string(),
        };
        for _ in 0..DEPTH {
            formula = WeightedMsoFormula::ExistsFirst {
                var: "x".to_string(),
                body: Box::new(formula),
            };
        }

        let cloned = formula.clone();
        assert_eq!(formula, cloned);
        assert_eq!(hash(&formula), hash(&cloned));
        assert_eq!(classify_formula(&formula), MsoFormulaClass::FirstOrder);
        assert!(free_variables(&formula).is_empty());
        assert!(free_set_variables(&formula).is_empty());
        assert!(analyze_formula(&formula).is_sentence);
        assert_eq!(
            evaluate_formula_bool(&formula, &["a".to_string()], &Assignment::new()),
            BooleanWeight::one()
        );
        let debug = format!("{formula:?}");
        assert!(debug.starts_with("ExistsFirst { var: \"x\", body: ExistsFirst"));
        assert!(debug.ends_with(" }"));
        drop(cloned);
        drop(formula);
    });
}

#[test]
fn binary_evaluation_and_lifecycle_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = WeightedMsoFormula::Constant("true".to_string());
        for _ in 0..DEPTH {
            formula = WeightedMsoFormula::And(
                Box::new(formula),
                Box::new(WeightedMsoFormula::Constant("true".to_string())),
            );
        }
        assert_eq!(evaluate_formula_bool(&formula, &[], &Assignment::new()), BooleanWeight::one());
        let cloned = formula.clone();
        assert_eq!(formula, cloned);
        assert_eq!(hash(&formula), hash(&cloned));
        drop(cloned);
        drop(formula);
    });
}

#[test]
fn compilation_descent_is_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = WeightedMsoFormula::Constant("non-boolean".to_string());
        for _ in 0..DEPTH {
            formula = WeightedMsoFormula::ExistsFirst {
                var: "x".to_string(),
                body: Box::new(formula),
            };
        }
        assert!(matches!(
            formula.to_weighted_automaton(&[]),
            Err(MsoCompileError::NonBooleanConstant { value }) if value == "non-boolean"
        ));
        drop(formula);
    });
}

#[test]
fn second_order_enumeration_has_no_machine_word_depth_ceiling() {
    on_small_stack(|| {
        let formula = WeightedMsoFormula::ExistsSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("true".to_string())),
        };
        let word = vec!["a".to_string(); 65];
        assert_eq!(
            evaluate_formula_bool(&formula, &word, &Assignment::new()),
            BooleanWeight::one()
        );
    });
}

#[test]
fn iterative_evaluator_matches_the_recursive_oracle() {
    let word = vec!["a".to_string(), "b".to_string()];
    let mut assignment = Assignment::new();
    assignment.first_order.insert("x".to_string(), 0);
    assignment.first_order.insert("y".to_string(), 1);
    assignment
        .second_order
        .insert("X".to_string(), HashSet::from([0]));

    let atom = WeightedMsoFormula::AtomicPos {
        label: "a".to_string(),
        var: "x".to_string(),
    };
    let corpus = [
        WeightedMsoFormula::Constant("7".to_string()),
        WeightedMsoFormula::Or(
            Box::new(atom.clone()),
            Box::new(WeightedMsoFormula::NegAtomicPos {
                label: "b".to_string(),
                var: "x".to_string(),
            }),
        ),
        WeightedMsoFormula::And(
            Box::new(WeightedMsoFormula::Order { x: "x".to_string(), y: "y".to_string() }),
            Box::new(WeightedMsoFormula::InSet {
                var: "x".to_string(),
                set_var: "X".to_string(),
            }),
        ),
        WeightedMsoFormula::ExistsFirst {
            var: "x".to_string(),
            body: Box::new(atom.clone()),
        },
        WeightedMsoFormula::ForallFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::Or(
                Box::new(atom),
                Box::new(WeightedMsoFormula::NegAtomicPos {
                    label: "a".to_string(),
                    var: "x".to_string(),
                }),
            )),
        },
        WeightedMsoFormula::ExistsSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::InSet {
                var: "x".to_string(),
                set_var: "X".to_string(),
            }),
        },
        WeightedMsoFormula::ForallSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::Or(
                Box::new(WeightedMsoFormula::InSet {
                    var: "x".to_string(),
                    set_var: "X".to_string(),
                }),
                Box::new(WeightedMsoFormula::NotInSet {
                    var: "x".to_string(),
                    set_var: "X".to_string(),
                }),
            )),
        },
    ];

    for formula in corpus {
        assert_eq!(
            evaluate_formula_bool(&formula, &word, &assignment),
            recursive_evaluate(&formula, &word, &assignment),
            "iterative evaluation diverged for {formula:?}"
        );
    }
}

#[test]
fn shallow_debug_contract_matches_the_former_recursive_derive() {
    let formula = WeightedMsoFormula::ExistsFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::Or(
            Box::new(WeightedMsoFormula::Constant("true".to_string())),
            Box::new(WeightedMsoFormula::AtomicPos {
                label: "a".to_string(),
                var: "x".to_string(),
            }),
        )),
    };
    assert_eq!(
        format!("{formula:?}"),
        "ExistsFirst { var: \"x\", body: Or(Constant(\"true\"), AtomicPos { label: \"a\", var: \"x\" }) }"
    );
}
