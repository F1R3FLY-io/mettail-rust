//! Abstract CESK machine coverage analysis for generated language tests.
//!
//! Wraps `mettail_prattail::abstract_cesk` and provides a higher-level
//! interface that works with `LanguageMetadata`. Constructs a Dyck State Graph
//! (DSG) from the language's rewrite rules to enumerate reachable abstract
//! evaluation states and report coverage metrics.
//!
//! The abstract CESK machine models evaluation as a pushdown system where
//! control states are (expression, environment, store) triples and the stack
//! encodes the evaluation context. The DSG compactly represents all reachable
//! configurations.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_prattail::abstract_cesk::{DyckStateGraph, EvalControlState, EvalStackSymbol};
use mettail_runtime::LanguageMetadata;

/// Result of abstract CESK coverage analysis on a language.
#[derive(Debug)]
pub struct CeskCoverageResult {
    /// Number of reachable abstract states in the DSG.
    pub reachable_state_count: usize,
    /// Number of edges (transitions) in the DSG.
    pub transition_count: usize,
    /// Number of distinct expression forms that appear in reachable states.
    pub distinct_expression_count: usize,
    /// Number of distinct stack symbol types observed.
    pub distinct_stack_symbol_count: usize,
    /// Human-readable summary.
    pub summary: String,
}

/// Check abstract CESK machine coverage for a language.
///
/// Constructs a Dyck State Graph from the language's rewrite rules and term
/// constructors. Each rewrite rule generates an evaluation transition (from the
/// LHS expression to the RHS expression). Term constructors with multiple fields
/// generate evaluation contexts (stack symbols representing pending sub-evaluations).
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite and term definitions
///
/// # Returns
/// A `CeskCoverageResult` summarizing the abstract state space coverage.
pub fn check_cesk_coverage(metadata: &dyn LanguageMetadata) -> CeskCoverageResult {
    let rewrites = metadata.rewrites();
    let terms = metadata.terms();

    if rewrites.is_empty() && terms.is_empty() {
        return CeskCoverageResult {
            reachable_state_count: 0,
            transition_count: 0,
            distinct_expression_count: 0,
            distinct_stack_symbol_count: 0,
            summary: format!(
                "{}: no rewrites or terms, CESK coverage trivially empty",
                metadata.name()
            ),
        };
    }

    let mut dsg = DyckStateGraph::new();
    let mut stack_symbol_kinds = std::collections::HashSet::new();

    // For each rewrite rule, create source and target control states
    // connected by an edge. This models the abstract evaluation step
    // where the LHS expression rewrites to the RHS expression.
    for rw in rewrites.iter().filter(|rw| rw.is_base()) {
        let source_state = EvalControlState {
            expr: rw.lhs.to_string(),
            env_fingerprint: fingerprint(rw.lhs),
            store_fingerprint: 0,
        };
        let target_state = EvalControlState {
            expr: rw.rhs.to_string(),
            env_fingerprint: fingerprint(rw.rhs),
            store_fingerprint: 0,
        };

        let src_idx = dsg.add_node(source_state);
        let tgt_idx = dsg.add_node(target_state);

        // The rewrite itself is modeled as a push/pop of a RewriteCont frame.
        let symbol = EvalStackSymbol::RewriteCont {
            rule_name: rw.name.unwrap_or("anonymous").to_string(),
        };
        stack_symbol_kinds.insert("RewriteCont");
        dsg.add_edge(src_idx, tgt_idx, symbol, true);
    }

    // For each term constructor with multiple fields, model sub-expression
    // evaluation contexts. A constructor like BinOp(lhs, op, rhs) creates
    // evaluation contexts for evaluating each operand.
    for term_def in terms {
        if term_def.fields.len() >= 2 {
            // Model binary operator contexts.
            let eval_state = EvalControlState {
                expr: format!("{}(...)", term_def.name),
                env_fingerprint: fingerprint(term_def.name),
                store_fingerprint: 0,
            };
            let sub_eval_state = EvalControlState {
                expr: format!("{}_sub_eval", term_def.name),
                env_fingerprint: fingerprint(term_def.name),
                store_fingerprint: 1,
            };

            let eval_idx = dsg.add_node(eval_state);
            let sub_idx = dsg.add_node(sub_eval_state);

            let symbol = EvalStackSymbol::BinOp { operator: term_def.name.to_string() };
            stack_symbol_kinds.insert("BinOp");
            dsg.add_edge(eval_idx, sub_idx, symbol, true);
        }

        if term_def.fields.iter().any(|f| f.is_binder) {
            // Model let-binding contexts for binder fields.
            let let_state = EvalControlState {
                expr: format!("{}(binder)", term_def.name),
                env_fingerprint: fingerprint(term_def.name),
                store_fingerprint: 2,
            };
            let body_state = EvalControlState {
                expr: format!("{}_body", term_def.name),
                env_fingerprint: fingerprint(term_def.name),
                store_fingerprint: 3,
            };

            let let_idx = dsg.add_node(let_state);
            let body_idx = dsg.add_node(body_state);

            let binder_name = term_def
                .fields
                .iter()
                .find(|f| f.is_binder)
                .map(|f| f.name)
                .unwrap_or("x");
            let symbol = EvalStackSymbol::LetBody { var_name: binder_name.to_string() };
            stack_symbol_kinds.insert("LetBody");
            dsg.add_edge(let_idx, body_idx, symbol, true);
        }
    }

    // Collect distinct expressions from all nodes.
    let distinct_expressions: std::collections::HashSet<&str> =
        dsg.nodes.iter().map(|n| n.state.expr.as_str()).collect();

    CeskCoverageResult {
        reachable_state_count: dsg.node_count(),
        transition_count: dsg.edge_count(),
        distinct_expression_count: distinct_expressions.len(),
        distinct_stack_symbol_count: stack_symbol_kinds.len(),
        summary: format!(
            "{}: CESK coverage (states: {}, transitions: {}, expressions: {}, \
             stack symbols: {})",
            metadata.name(),
            dsg.node_count(),
            dsg.edge_count(),
            distinct_expressions.len(),
            stack_symbol_kinds.len(),
        ),
    }
}

/// Compute a u64 fingerprint of a string via the default hasher.
fn fingerprint(s: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}
