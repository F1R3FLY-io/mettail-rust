//! Runtime behavioral predicate evaluation surface.
//!
//! Phase 6 / F.0-sibling (2026-04-26): the type definitions
//! (`BehavioralPred`, `Quantifier`, `QuantifiedDomain`, `PredArg`) were
//! moved to `mettail_prattail::behavioral_pred` to break the
//! `prattail → runtime` dependency cycle. This module re-exports them
//! for backward compatibility, and retains the runtime-policy concerns
//! that don't belong in the parser library:
//!
//! - **Thread-local fact snapshot** (`set_pred_fact_snapshot`,
//!   `clear_pred_fact_snapshot`) — populated by the generated
//!   `run_ascent_typed_with_facts` before `prog.run()`.
//! - **`evaluate_pred_with_bindings`** — runtime-time evaluator the
//!   Comm rule's `if { }` guard calls.
//!
//! The type re-export means every `use mettail_runtime::BehavioralPred`
//! call site continues to compile.

pub use mettail_prattail::behavioral_pred::{
    BehavioralPred, PredArg, QuantifiedDomain, Quantifier,
};

// ═════════════════════════════════════════════════════════════════════════
// Thread-local fact snapshot for runtime predicate evaluation
// ═════════════════════════════════════════════════════════════════════════
//
// Step 1.2 (guard-gated Comm): the Comm rule's `if { }` guard calls
// `evaluate_pred_with_bindings` which reads this thread-local snapshot
// to check whether a relation tuple exists. The snapshot is populated
// by the generated `run_ascent_typed_with_facts` BEFORE `prog.run()`.
//
// This is NOT the rejected Phase 4 RelationView — that was a broad
// relation-mirroring mechanism. This is a narrow, user-controlled,
// externally-populated fact store that the generated Comm rule
// consults. BehavioralPred remains passive: the evaluation function
// is freestanding, not a method on the type.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

thread_local! {
    static PRED_FACT_SNAPSHOT: RefCell<HashMap<String, HashSet<Vec<String>>>> =
        RefCell::new(HashMap::new());
}

/// Install a fact snapshot for the current thread. Called by generated
/// `run_ascent_typed_with_facts` before `prog.run()`.
pub fn set_pred_fact_snapshot(facts: HashMap<String, HashSet<Vec<String>>>) {
    PRED_FACT_SNAPSHOT.with(|snap| *snap.borrow_mut() = facts);
}

/// Clear the fact snapshot. Called after `prog.run()` returns.
pub fn clear_pred_fact_snapshot() {
    PRED_FACT_SNAPSHOT.with(|snap| snap.borrow_mut().clear());
}

/// Evaluate a per-instance `BehavioralPred` against the thread-local
/// fact snapshot, resolving `PredArg::Var` arguments via the provided
/// bindings.
///
/// `bindings` maps variable names (e.g., `"x"`) to their resolved
/// string values (e.g., `"0"` — the Display form of the received
/// term). The Comm rule codegen supplies bindings derived from the
/// continuation binder: `[(binder_pretty_name, format!("{}", received))]`.
///
/// This function is freestanding (not a method on BehavioralPred) so
/// the type remains passive per the design decision.
pub fn evaluate_pred_with_bindings(pred: &BehavioralPred, bindings: &[(String, String)]) -> bool {
    let mut env: HashMap<String, String> = bindings.iter().cloned().collect();
    eval_pred_iterative(pred, &mut env)
}

enum EvalTask<'pred> {
    Eval(&'pred BehavioralPred),
    Not,
    AndRight(&'pred BehavioralPred),
    OrRight(&'pred BehavioralPred),
    ImpliesRight(&'pred BehavioralPred),
    QuantifiedBody {
        quantifier: Quantifier,
        var: &'pred str,
        body: &'pred BehavioralPred,
        remaining: std::vec::IntoIter<String>,
        previous: Option<String>,
    },
}

/// Heap-backed evaluator preserving the recursive evaluator's left-to-right
/// short-circuit and quantifier-binding semantics.
fn eval_pred_iterative(pred: &BehavioralPred, env: &mut HashMap<String, String>) -> bool {
    let mut tasks = vec![EvalTask::Eval(pred)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            EvalTask::Eval(BehavioralPred::Top) => values.push(true),
            EvalTask::Eval(BehavioralPred::RelationQuery { relation_name, args, negated }) => {
                let resolved: Vec<String> = args.iter().map(|arg| resolve_arg(arg, env)).collect();
                let hit = PRED_FACT_SNAPSHOT.with(|snap| {
                    snap.borrow()
                        .get(relation_name)
                        .is_some_and(|tuples| tuples.contains(&resolved))
                });
                values.push(if *negated { !hit } else { hit });
            },
            EvalTask::Eval(BehavioralPred::And(left, right)) => {
                tasks.push(EvalTask::AndRight(right));
                tasks.push(EvalTask::Eval(left));
            },
            EvalTask::Eval(BehavioralPred::Or(left, right)) => {
                tasks.push(EvalTask::OrRight(right));
                tasks.push(EvalTask::Eval(left));
            },
            EvalTask::Eval(BehavioralPred::Not(inner)) => {
                tasks.push(EvalTask::Not);
                tasks.push(EvalTask::Eval(inner));
            },
            EvalTask::Eval(BehavioralPred::Implies(premise, conclusion)) => {
                tasks.push(EvalTask::ImpliesRight(conclusion));
                tasks.push(EvalTask::Eval(premise));
            },
            EvalTask::Eval(BehavioralPred::Quantified { quantifier, var, domain, body }) => {
                let mut remaining =
                    enumerate_quantified_domain(var, domain.as_ref(), body, env).into_iter();
                if let Some(value) = remaining.next() {
                    let previous = env.insert(var.clone(), value);
                    tasks.push(EvalTask::QuantifiedBody {
                        quantifier: *quantifier,
                        var,
                        body,
                        remaining,
                        previous,
                    });
                    tasks.push(EvalTask::Eval(body));
                } else {
                    values.push(matches!(quantifier, Quantifier::ForAll));
                }
            },
            // Runtime AC matching needs structural multiset values, while this
            // evaluator only has string-valued fact snapshots. Fail closed.
            EvalTask::Eval(BehavioralPred::AcMatch { .. }) => values.push(false),
            EvalTask::Not => {
                let value = values.pop().expect("Not continuation requires one value");
                values.push(!value);
            },
            EvalTask::AndRight(right) => {
                let left = values
                    .pop()
                    .expect("And continuation requires its left value");
                if left {
                    tasks.push(EvalTask::Eval(right));
                } else {
                    values.push(false);
                }
            },
            EvalTask::OrRight(right) => {
                let left = values
                    .pop()
                    .expect("Or continuation requires its left value");
                if left {
                    values.push(true);
                } else {
                    tasks.push(EvalTask::Eval(right));
                }
            },
            EvalTask::ImpliesRight(conclusion) => {
                let premise = values
                    .pop()
                    .expect("Implies continuation requires its premise value");
                if premise {
                    tasks.push(EvalTask::Eval(conclusion));
                } else {
                    values.push(true);
                }
            },
            EvalTask::QuantifiedBody {
                quantifier,
                var,
                body,
                mut remaining,
                previous,
            } => {
                let value = values
                    .pop()
                    .expect("quantifier continuation requires its body value");
                let short_circuit = match quantifier {
                    Quantifier::ForAll => !value,
                    Quantifier::Exists => value,
                };
                if short_circuit {
                    restore_binding(env, var, previous);
                    values.push(value);
                } else if let Some(next) = remaining.next() {
                    env.insert(var.to_string(), next);
                    tasks.push(EvalTask::QuantifiedBody {
                        quantifier,
                        var,
                        body,
                        remaining,
                        previous,
                    });
                    tasks.push(EvalTask::Eval(body));
                } else {
                    restore_binding(env, var, previous);
                    values.push(matches!(quantifier, Quantifier::ForAll));
                }
            },
        }
    }
    debug_assert!(tasks.is_empty());
    debug_assert_eq!(values.len(), 1);
    values.pop().unwrap_or(false)
}

fn restore_binding(env: &mut HashMap<String, String>, var: &str, previous: Option<String>) {
    if let Some(value) = previous {
        env.insert(var.to_string(), value);
    } else {
        env.remove(var);
    }
}

fn enumerate_quantified_domain(
    var: &str,
    domain: Option<&QuantifiedDomain>,
    body: &BehavioralPred,
    env: &HashMap<String, String>,
) -> Vec<String> {
    match domain {
        Some(QuantifiedDomain::Named(name)) => relation_first_column(name),
        Some(QuantifiedDomain::Bounded(limit)) => {
            let mut values = infer_domain_values(var, body, env);
            values.truncate(*limit);
            values
        },
        Some(QuantifiedDomain::Enumerated(elements)) => {
            elements.iter().map(|arg| resolve_arg(arg, env)).collect()
        },
        None => infer_domain_values(var, body, env),
    }
}

fn relation_first_column(relation_name: &str) -> Vec<String> {
    PRED_FACT_SNAPSHOT.with(|snap| {
        snap.borrow()
            .get(relation_name)
            .map(|tuples| {
                tuples
                    .iter()
                    .filter_map(|tuple| tuple.first().cloned())
                    .collect()
            })
            .unwrap_or_default()
    })
}

fn infer_domain_values(
    var: &str,
    pred: &BehavioralPred,
    env: &HashMap<String, String>,
) -> Vec<String> {
    let mut values = BTreeSet::new();
    collect_domain_values_iterative(var, pred, env, &mut values);
    values.into_iter().collect()
}

fn collect_domain_values_iterative(
    var: &str,
    pred: &BehavioralPred,
    env: &HashMap<String, String>,
    values: &mut BTreeSet<String>,
) {
    let mut work = vec![pred];
    while let Some(pred) = work.pop() {
        match pred {
            BehavioralPred::RelationQuery { relation_name, args, .. } => {
                let positions: Vec<usize> = args
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, arg)| match arg {
                        PredArg::Var(v) if v == var => Some(idx),
                        _ => None,
                    })
                    .collect();
                if positions.is_empty() {
                    continue;
                }
                PRED_FACT_SNAPSHOT.with(|snap| {
                    if let Some(tuples) = snap.borrow().get(relation_name) {
                        for tuple in tuples {
                            if tuple_matches_bound_args(tuple, args, var, env) {
                                for idx in &positions {
                                    if let Some(value) = tuple.get(*idx) {
                                        values.insert(value.clone());
                                    }
                                }
                            }
                        }
                    }
                });
            },
            BehavioralPred::Quantified { var: inner_var, domain, body, .. } => {
                if let Some(QuantifiedDomain::Enumerated(elements)) = domain {
                    for arg in elements {
                        if let PredArg::Var(v) = arg {
                            if v == var {
                                values.insert(resolve_arg(arg, env));
                            }
                        }
                    }
                }
                if inner_var != var {
                    work.push(body);
                }
            },
            BehavioralPred::And(a, b)
            | BehavioralPred::Or(a, b)
            | BehavioralPred::Implies(a, b) => {
                work.push(b);
                work.push(a);
            },
            BehavioralPred::Not(inner) => work.push(inner),
            BehavioralPred::AcMatch { bag, elements, .. } => {
                for arg in std::iter::once(bag).chain(elements.iter()) {
                    if let PredArg::Var(v) = arg {
                        if v == var {
                            values.insert(resolve_arg(arg, env));
                        }
                    }
                }
            },
            BehavioralPred::Top => {},
        }
    }
}

fn tuple_matches_bound_args(
    tuple: &[String],
    args: &[PredArg],
    quantified_var: &str,
    env: &HashMap<String, String>,
) -> bool {
    args.iter().enumerate().all(|(idx, arg)| {
        let Some(tuple_value) = tuple.get(idx) else {
            return false;
        };
        match arg {
            PredArg::Var(v) if v == quantified_var => true,
            PredArg::Var(v) => env.get(v).map_or(true, |bound| bound == tuple_value),
            PredArg::IntLit(n) => tuple_value == &n.to_string(),
            PredArg::StringLit(s) => tuple_value == s,
        }
    })
}

fn resolve_arg(arg: &PredArg, env: &HashMap<String, String>) -> String {
    match arg {
        PredArg::Var(v) => env.get(v).cloned().unwrap_or_else(|| v.clone()),
        PredArg::IntLit(n) => n.to_string(),
        PredArg::StringLit(s) => s.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> PredArg {
        PredArg::Var(name.to_string())
    }

    fn rel(name: &str, args: Vec<PredArg>) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: name.to_string(),
            args,
            negated: false,
        }
    }

    // ── Type-level structural tests now live in
    //    `prattail/src/behavioral_pred.rs` (free_vars, substitute_var,
    //    Display, Hash). This module's tests focus on the runtime-only
    //    `evaluate_pred_with_bindings` thread-local-snapshot semantics. ──

    #[test]
    fn eval_top_is_always_true() {
        clear_pred_fact_snapshot();
        assert!(evaluate_pred_with_bindings(&BehavioralPred::Top, &[]));
    }

    #[test]
    fn eval_relation_query_hits_snapshot() {
        let mut facts = std::collections::HashMap::new();
        let mut tuples = std::collections::HashSet::new();
        tuples.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), tuples);
        set_pred_fact_snapshot(facts);

        let pred = rel("halts", vec![var("x")]);
        assert!(evaluate_pred_with_bindings(&pred, &[("x".to_string(), "0".to_string())],));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_relation_query_misses_snapshot() {
        clear_pred_fact_snapshot();
        let pred = rel("halts", vec![var("x")]);
        assert!(!evaluate_pred_with_bindings(&pred, &[("x".to_string(), "0".to_string())],));
    }

    #[test]
    fn eval_negated_relation_inverts() {
        clear_pred_fact_snapshot();
        let pred = BehavioralPred::RelationQuery {
            relation_name: "halts".to_string(),
            args: vec![PredArg::Var("x".to_string())],
            negated: true,
        };
        // Empty snapshot → query returns false → negation returns true
        assert!(evaluate_pred_with_bindings(&pred, &[("x".to_string(), "0".to_string())],));
    }

    #[test]
    fn eval_and_both_must_hold() {
        let mut facts = std::collections::HashMap::new();
        let mut h = std::collections::HashSet::new();
        h.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), h);
        // safe is NOT seeded
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::And(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        assert!(!evaluate_pred_with_bindings(&pred, &[("x".to_string(), "0".to_string())],));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_or_either_suffices() {
        let mut facts = std::collections::HashMap::new();
        let mut h = std::collections::HashSet::new();
        h.insert(vec!["0".to_string()]);
        facts.insert("halts".to_string(), h);
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::Or(
            Box::new(rel("halts", vec![var("x")])),
            Box::new(rel("safe", vec![var("x")])),
        );
        assert!(evaluate_pred_with_bindings(&pred, &[("x".to_string(), "0".to_string())],));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_forall_named_domain_checks_each_fact() {
        let mut facts = std::collections::HashMap::new();
        facts.insert(
            "nodes".to_string(),
            [vec!["a".to_string()], vec!["b".to_string()]]
                .into_iter()
                .collect(),
        );
        facts.insert("safe".to_string(), [vec!["a".to_string()]].into_iter().collect());
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: "y".to_string(),
            domain: Some(QuantifiedDomain::Named("nodes".to_string())),
            body: Box::new(rel("safe", vec![var("y")])),
        };
        assert!(!evaluate_pred_with_bindings(&pred, &[]));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_exists_infers_domain_from_body_relation() {
        let mut facts = std::collections::HashMap::new();
        facts.insert(
            "safe".to_string(),
            [vec!["a".to_string()], vec!["b".to_string()]]
                .into_iter()
                .collect(),
        );
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: "y".to_string(),
            domain: None,
            body: Box::new(rel("safe", vec![var("y")])),
        };
        assert!(evaluate_pred_with_bindings(&pred, &[]));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_quantified_restores_shadowed_binding() {
        let mut facts = std::collections::HashMap::new();
        facts.insert("safe".to_string(), [vec!["inner".to_string()]].into_iter().collect());
        set_pred_fact_snapshot(facts);

        let pred = BehavioralPred::And(
            Box::new(BehavioralPred::Quantified {
                quantifier: Quantifier::Exists,
                var: "x".to_string(),
                domain: None,
                body: Box::new(rel("safe", vec![var("x")])),
            }),
            Box::new(BehavioralPred::RelationQuery {
                relation_name: "safe".to_string(),
                args: vec![PredArg::Var("x".to_string())],
                negated: true,
            }),
        );
        assert!(evaluate_pred_with_bindings(&pred, &[("x".to_string(), "outer".to_string())],));
        clear_pred_fact_snapshot();
    }
}
