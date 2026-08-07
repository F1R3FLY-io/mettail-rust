use std::collections::HashMap;

use mettail_prattail::predicate_dispatch::{
    estimate_predicate_cost, estimate_predicate_selectivity, extract_features,
    extract_features_mso, resolve_cost, resolve_selectivity, ChannelContext, PredicateSignature,
};
use mettail_prattail::symbolic::PredicateExpr;
use mettail_prattail::weighted_mso::WeightedMsoFormula;
use mettail_prattail::GuardConfigSpec;

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[test]
fn predicate_folds_and_feature_walk_fit_a_small_stack() {
    let mut quantified = PredicateExpr::Atom("leaf".into());
    for index in 0..DEPTH {
        quantified = PredicateExpr::ForallFinite {
            var: format!("x{index}"),
            domain: vec!["only".into()],
            body: Box::new(quantified),
        };
    }

    std::thread::Builder::new()
        .name("predicate-dispatch-stack-gate".into())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            assert_eq!(estimate_predicate_cost(&quantified), 1);
            assert_eq!(resolve_cost(&quantified, None), 1);
            assert_eq!(estimate_predicate_selectivity(&quantified), 0.5);
            assert_eq!(resolve_selectivity(&quantified, None), 0.5);

            let profile = extract_features(&quantified, &ChannelContext::new());
            assert_eq!(profile.quantifier_depth, DEPTH as u32);
            assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        })
        .expect("spawn predicate dispatch stack gate")
        .join()
        .expect("predicate dispatch stack gate overflowed or panicked");
}

#[test]
fn configured_boolean_fold_propagates_a_deep_leaf_override() {
    let mut predicate = PredicateExpr::Relation {
        name: "configured".into(),
        args: vec!["x".into()],
    };
    for _ in 0..DEPTH {
        predicate = PredicateExpr::Not(Box::new(predicate));
    }
    let config = GuardConfigSpec {
        selectivity_overrides: HashMap::from([("configured".into(), 0.25)]),
        cost_overrides: HashMap::from([("configured".into(), 7)]),
        ..Default::default()
    };

    std::thread::Builder::new()
        .name("predicate-override-stack-gate".into())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            assert_eq!(resolve_selectivity(&predicate, Some(&config)), 0.25);
            assert_eq!(resolve_cost(&predicate, Some(&config)), DEPTH as u32 + 7);
        })
        .expect("spawn configured predicate stack gate")
        .join()
        .expect("configured predicate stack gate overflowed or panicked");
}

#[test]
fn weighted_mso_feature_walk_fits_a_small_stack() {
    let mut formula = WeightedMsoFormula::Constant("true".into());
    for index in 0..DEPTH {
        formula = WeightedMsoFormula::ForallFirst {
            var: format!("x{index}"),
            body: Box::new(formula),
        };
    }

    std::thread::Builder::new()
        .name("weighted-mso-dispatch-stack-gate".into())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let profile = extract_features_mso(&formula, &ChannelContext::new());
            assert_eq!(profile.quantifier_depth, DEPTH as u32);
            assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        })
        .expect("spawn weighted MSO dispatch stack gate")
        .join()
        .expect("weighted MSO dispatch stack gate overflowed or panicked");
}
