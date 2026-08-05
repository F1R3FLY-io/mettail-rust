#[path = "support/behavioral_pred_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_prattail::behavioral_algebra::BehavioralFormula;
use mettail_prattail::behavioral_pred::{BehavioralPred, PredArg};
use recursive_oracle::representative_cases;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn iterative_behavioral_operations_match_the_recursive_oracle() {
    let cases = representative_cases();
    for oracle in &cases {
        let production = oracle.to_production();
        assert_eq!(format!("{production:?}"), format!("{oracle:?}"));
        assert_eq!(production.to_string(), oracle.to_string());
        assert_eq!(hash(&production), hash(oracle));
        assert_eq!(production.free_vars(), oracle.free_vars());

        let expected_substitution = oracle.substitute_var("x", "renamed").to_production();
        assert_eq!(production.substitute_var("x", "renamed"), expected_substitution);
        assert_eq!(production.to_behavioral_formula(), oracle.to_behavioral_formula());
    }

    for left in &cases {
        for right in &cases {
            let production_left = left.to_production();
            let production_right = right.to_production();
            assert_eq!(production_left == production_right, left == right);
            assert_eq!(production_left.cmp(&production_right), left.cmp(right));
        }
    }
}

#[test]
fn behavioral_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("behavioral-lifecycle-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut predicate = BehavioralPred::RelationQuery {
                relation_name: "ready".into(),
                args: vec![PredArg::Var("x".into())],
                negated: false,
            };
            for _ in 0..DEPTH {
                predicate = BehavioralPred::Not(Box::new(predicate));
            }

            let cloned = predicate.clone();
            assert_eq!(predicate, cloned);
            assert_eq!(predicate.cmp(&cloned), Ordering::Equal);
            assert_eq!(hash(&predicate), hash(&cloned));
            assert!(format!("{predicate:?}").ends_with(&")".repeat(DEPTH)));
            assert!(predicate.to_string().ends_with(&")".repeat(DEPTH + 1)));
            assert_eq!(predicate.free_vars(), ["x".to_owned()].into_iter().collect());

            let substituted = predicate.substitute_var("x", "renamed");
            assert_eq!(substituted.free_vars(), ["renamed".to_owned()].into_iter().collect());

            let formula = predicate.to_behavioral_formula().expect("Not spine lowers");
            dismantle_not_formula(formula, DEPTH);
            drop(substituted);
            drop(cloned);
            drop(predicate);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("behavioral lifecycle must not overflow the native stack");
}

fn dismantle_not_formula(formula: BehavioralFormula, expected_depth: usize) {
    let mut depth = 0;
    let mut cursor = &formula;
    loop {
        match cursor {
            BehavioralFormula::Not(inner) => {
                cursor = inner;
                depth += 1;
            },
            BehavioralFormula::Relation { name, args } => {
                assert_eq!(name, "ready");
                assert_eq!(args.len(), 1);
                break;
            },
            _ => panic!("expected a Not formula spine ending in ready(x)"),
        }
    }
    assert_eq!(depth, expected_depth);
}
