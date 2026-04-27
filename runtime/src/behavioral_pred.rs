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
use std::collections::{HashMap, HashSet};

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
pub fn evaluate_pred_with_bindings(
    pred: &BehavioralPred,
    bindings: &[(String, String)],
) -> bool {
    match pred {
        BehavioralPred::Top => true,
        BehavioralPred::RelationQuery {
            relation_name,
            args,
            negated,
        } => {
            let resolved: Vec<String> = args
                .iter()
                .map(|a| match a {
                    PredArg::Var(v) => bindings
                        .iter()
                        .find(|(k, _)| k == v)
                        .map(|(_, val)| val.clone())
                        .unwrap_or_else(|| v.clone()),
                    PredArg::IntLit(n) => n.to_string(),
                    PredArg::StringLit(s) => s.clone(),
                })
                .collect();
            let hit = PRED_FACT_SNAPSHOT.with(|snap| {
                snap.borrow()
                    .get(relation_name)
                    .map(|tuples| tuples.contains(&resolved))
                    .unwrap_or(false)
            });
            if *negated {
                !hit
            } else {
                hit
            }
        }
        BehavioralPred::And(a, b) => {
            evaluate_pred_with_bindings(a, bindings) && evaluate_pred_with_bindings(b, bindings)
        }
        BehavioralPred::Or(a, b) => {
            evaluate_pred_with_bindings(a, bindings) || evaluate_pred_with_bindings(b, bindings)
        }
        BehavioralPred::Not(inner) => !evaluate_pred_with_bindings(inner, bindings),
        BehavioralPred::Implies(p, c) => {
            !evaluate_pred_with_bindings(p, bindings) || evaluate_pred_with_bindings(c, bindings)
        }
        // Quantified/AcMatch: conservatively true (Phase 6 follow-up)
        _ => true,
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
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
        clear_pred_fact_snapshot();
    }

    #[test]
    fn eval_relation_query_misses_snapshot() {
        clear_pred_fact_snapshot();
        let pred = rel("halts", vec![var("x")]);
        assert!(!evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
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
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
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
        assert!(!evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
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
        assert!(evaluate_pred_with_bindings(
            &pred,
            &[("x".to_string(), "0".to_string())],
        ));
        clear_pred_fact_snapshot();
    }
}
