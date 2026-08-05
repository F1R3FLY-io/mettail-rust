use std::collections::{HashMap, HashSet};

use mettail_runtime::{
    clear_pred_fact_snapshot, evaluate_pred_with_bindings, set_pred_fact_snapshot, BehavioralPred,
    PredArg, Quantifier,
};

#[test]
fn evaluator_and_domain_inference_handle_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("behavioral-evaluator-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut tuples = HashSet::new();
            tuples.insert(vec!["1".to_string()]);
            set_pred_fact_snapshot(HashMap::from([("seen".to_string(), tuples)]));

            let mut body = BehavioralPred::RelationQuery {
                relation_name: "seen".to_string(),
                args: vec![PredArg::Var("x".to_string())],
                negated: false,
            };
            for _ in 0..DEPTH {
                body = BehavioralPred::Not(Box::new(body));
            }
            let mut predicate = BehavioralPred::Quantified {
                quantifier: Quantifier::ForAll,
                var: "x".to_string(),
                domain: None,
                body: Box::new(body),
            };

            assert!(evaluate_pred_with_bindings(&predicate, &[]));
            clear_pred_fact_snapshot();

            predicate = match predicate {
                BehavioralPred::Quantified { body, .. } => *body,
                _ => unreachable!(),
            };
            let mut depth = 0;
            loop {
                match predicate {
                    BehavioralPred::Not(inner) => {
                        predicate = *inner;
                        depth += 1;
                    },
                    BehavioralPred::RelationQuery { .. } => break,
                    _ => panic!("expected a Not spine ending in a relation query"),
                }
            }
            assert_eq!(depth, DEPTH);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("behavioral evaluator must not overflow the native stack");
}
