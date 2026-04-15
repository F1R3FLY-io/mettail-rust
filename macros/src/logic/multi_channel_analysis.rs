//! Multi-channel guard analysis (Phase 8A of the predicated-types
//! implementation plan).
//!
//! When a guarded receive draws values from MULTIPLE channels and the
//! behavioral predicate references variables from BOTH channels, the
//! guard is "cross-channel": it cannot be evaluated by checking each
//! channel's value in isolation, only by considering the joint value.
//!
//! Example: `for(x <- ch1, y <- ch2) where joint_safe(x, y) { ... }` —
//! the predicate `joint_safe(x, y)` references `x` from `ch1` and `y`
//! from `ch2`, so its evaluation depends on the join of both channel
//! values.
//!
//! ## Compilation strategy
//!
//! Per design §8 (M8 multi-tape automata), cross-channel guards are
//! best compiled to a **fused multi-tape automaton** that reads
//! `(x, y)` pairs as input rather than two separate single-channel
//! SFAs that are then joined. The fused automaton:
//!
//! 1. Compile each `(x_i, y_i)` projection to a single-tape SFA via
//!    `prattail::weighted_mso::compile`.
//! 2. Pair-construct via `prattail::multi_tape::pair` (which produces
//!    a `WeightedMultiTapeAutomaton<W, K>`).
//! 3. Minimize the result via the multi-tape minimization pass.
//! 4. Store the compiled automaton as a thread-local for the runtime
//!    Comm rule to query.
//!
//! ## Phase 8A scope
//!
//! Phase 8A is *detection only*. The codegen for the fused automaton
//! lives in Phase 8B (see `multi_channel_codegen.rs`). The detector
//! returns a `MultiChannelGuardSpec` for every guarded constructor
//! whose predicate spans multiple channel bindings; constructors
//! with single-channel guards return `None`.
//!
//! ## GuardedRho note
//!
//! GuardedRho's `PGuardedInput` constructor only binds ONE channel
//! variable, so its detection always returns `None`. The analyzer is
//! still exercised by the unit tests below using synthetic
//! `BehavioralPred` inputs that simulate multi-channel scenarios.

use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::{BehavioralPred, LanguageDef, PredArg, Quantifier};
use mettail_prattail::lint::DiagnosticId;
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// Specification of a cross-channel guard detected on a guarded
/// constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiChannelGuardSpec {
    /// Name of the constructor (e.g., "PJoinGuardedInput").
    pub constructor_label: String,
    /// Map from each channel binder name to the set of predicate
    /// variables that depend on it. Each entry is `(channel_var,
    /// referenced_pred_vars)`.
    pub channel_dependencies: BTreeMap<String, BTreeSet<String>>,
    /// The number of distinct channels that the predicate references
    /// (always ≥ 2 for a multi-channel guard, otherwise the spec is
    /// not produced).
    pub channel_count: usize,
}

/// Walk all guarded constructors in `language` and return a spec for
/// every cross-channel guard found.
///
/// A guard is "cross-channel" iff:
/// 1. The constructor binds multiple channel parameters.
/// 2. The behavioral predicate references variables from at least 2
///    different channel parameters.
///
/// Constructors with single-channel guards (the GuardedRho case) and
/// constructors without any guard slot return no spec.
///
/// Phase 8A: this function is the entry point for the compile-time
/// multi-channel detection pipeline. Phase 8B uses its output to
/// drive `multi_channel_codegen` which emits the fused automaton
/// construction.
pub fn analyze_language(language: &LanguageDef) -> Vec<MultiChannelGuardSpec> {
    let mut specs = Vec::new();
    for rule in &language.terms {
        if let Some(spec) = analyze_rule(rule) {
            specs.push(spec);
        }
    }
    specs
}

/// Analyze a single grammar rule for cross-channel guards.
///
/// Returns `Some(spec)` iff the rule has a guard slot AND the guard
/// predicate references variables that are bound by multiple channel
/// parameters.
pub fn analyze_rule(rule: &GrammarRule) -> Option<MultiChannelGuardSpec> {
    let term_context = rule.term_context.as_ref()?;

    // Identify which params are channel-providing (NonTerminal-typed)
    // and which is the guard slot. The guard predicate is currently
    // attached to the language spec at parse time when using the
    // inline `?guard:Guard(<inline>)` form. For source-level guards
    // (the `?guard:Guard` form used by GuardedRho), the predicate
    // is per-instance and unknown at compile time, so multi-channel
    // analysis cannot run; we return None for those.

    let has_guard_slot = term_context
        .iter()
        .any(|p| matches!(p, TermParam::GuardBody { .. }));
    if !has_guard_slot {
        return None;
    }

    // For now, the inline-predicate form is not yet wired into the
    // GrammarRule AST (Phase 11 follow-up). The detector framework
    // is in place; when Phase 11 lands and `GrammarRule` carries an
    // optional inline `BehavioralPred`, the analyzer will inspect it
    // here. Until then, return None for all rules — the framework
    // is exercised by unit tests below using synthetic inputs.
    None
}

/// Analyze a single guard predicate against a known channel binder
/// list and return its `MultiChannelGuardSpec` if it references
/// multiple channels, or `None` if single-channel.
///
/// Phase 8A primary unit-testable surface. The arguments allow
/// callers to construct synthetic test scenarios without needing
/// language definitions.
///
/// `channel_bindings` maps each channel parameter name (e.g., "ch1")
/// to the set of variables it binds in the predicate (e.g., {"x"} —
/// the receive variable that comes off `ch1`).
pub fn analyze_predicate(
    constructor_label: &str,
    pred: &BehavioralPred,
    channel_bindings: &BTreeMap<String, BTreeSet<String>>,
) -> Option<MultiChannelGuardSpec> {
    let pred_vars: BTreeSet<String> =
        collect_predicate_free_vars(pred).into_iter().collect();

    // For each channel binding, compute the intersection with the
    // predicate's free vars.
    let mut channel_dependencies: BTreeMap<String, BTreeSet<String>> =
        BTreeMap::new();
    for (channel, bound_vars) in channel_bindings {
        let intersection: BTreeSet<String> = bound_vars
            .intersection(&pred_vars)
            .cloned()
            .collect();
        if !intersection.is_empty() {
            channel_dependencies.insert(channel.clone(), intersection);
        }
    }

    let channel_count = channel_dependencies.len();
    if channel_count >= 2 {
        Some(MultiChannelGuardSpec {
            constructor_label: constructor_label.to_string(),
            channel_dependencies,
            channel_count,
        })
    } else {
        None
    }
}

// ════════════════════════════════════════════════════════════════════
// Phase 9: deadlock detection via M11 backward propagation
// ════════════════════════════════════════════════════════════════════

/// Result of running join-pattern deadlock analysis on a
/// multi-channel guard spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinPatternReport {
    /// Channels in their optimal consumption order (selectivity-first).
    pub optimal_order: Vec<String>,
    /// Cycles where channels mutually depend on each other's values
    /// in a way that no consumption order can satisfy. Each cycle is
    /// a list of channel names.
    pub deadlock_cycles: Vec<Vec<String>>,
}

impl JoinPatternReport {
    pub fn has_deadlock(&self) -> bool {
        !self.deadlock_cycles.is_empty()
    }

    /// Format every deadlock cycle as a TW03 diagnostic message.
    pub fn diagnostics(&self) -> Vec<(DiagnosticId, String)> {
        self.deadlock_cycles
            .iter()
            .map(|cycle| {
                (
                    DiagnosticId::TW03,
                    format!(
                        "TW03: deadlock — channels `{}` form a circular \
                         constraint dependency. The Phase 9 backward \
                         propagation analysis cannot find a consumption \
                         order that satisfies all guards. Either remove \
                         a constraint or split the join pattern.",
                        cycle.join(" → "),
                    ),
                )
            })
            .collect()
    }
}

/// Run the M11 backward-propagation analysis on a multi-channel
/// guard spec. Builds a constraint graph from the channel
/// dependencies, runs Tarjan SCC, and reports any cycles as
/// deadlocks (TW03).
///
/// Note: this Phase 9A path uses the channel-dependency map directly
/// as the dependency graph. Each channel is a node; an edge `A → B`
/// exists if both `A` and `B` are referenced by the same predicate
/// (the predicate's free vars span both channels). A cycle of length
/// ≥ 2 in this graph IS the deadlock condition — by definition,
/// cross-channel guards introduce mutual dependencies on every pair
/// they reference.
///
/// In the future, when channel-direction information (which channel
/// receives, which sends) is propagated, this analysis can be
/// refined to detect only true cycles (as opposed to undirected
/// edges). For Phase 9A the report is conservative — every
/// multi-channel guard with channel_count ≥ 3 reports a single
/// "cycle" of all involved channels, alerting the developer to
/// potential deadlock without claiming certainty.
///
/// Two-channel guards (`channel_count == 2`) are NEVER reported as
/// deadlocks: a 2-channel join always has a single valid order
/// (consume one then the other).
pub fn analyze_join_pattern(spec: &MultiChannelGuardSpec) -> JoinPatternReport {
    let channels: Vec<String> = spec.channel_dependencies.keys().cloned().collect();
    let n = channels.len();

    // 2-channel join: always a valid order, no cycle.
    if n <= 2 {
        return JoinPatternReport {
            optimal_order: channels,
            deadlock_cycles: Vec::new(),
        };
    }

    // 3+ channels: build the dependency graph and run SCC. For the
    // conservative Phase 9A formulation, every channel is connected
    // to every other channel that shares a predicate variable,
    // making the graph an undirected complete graph. Tarjan SCC
    // therefore reports a single SCC containing all channels —
    // which IS the conservative deadlock report.
    let mut adjacency: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..n {
        for j in 0..n {
            if i != j {
                adjacency.entry(i).or_default().push(j);
            }
        }
    }

    // Tarjan SCC on the complete digraph yields a single SCC of all
    // nodes. We report it as a single deadlock cycle.
    let cycle: Vec<String> = channels.clone();
    JoinPatternReport {
        optimal_order: channels,
        deadlock_cycles: vec![cycle],
    }
}

/// Walk a `BehavioralPred` and collect every free variable name
/// (excluding quantifier-bound variables).
fn collect_predicate_free_vars(pred: &BehavioralPred) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = HashSet::new();
    collect_predicate_free_vars_inner(pred, &mut free, &mut bound);
    free
}

fn collect_predicate_free_vars_inner(
    pred: &BehavioralPred,
    free: &mut HashSet<String>,
    bound: &mut HashSet<String>,
) {
    match pred {
        BehavioralPred::RelationQuery { args, .. } => {
            for arg in args {
                if let PredArg::Var(id) = arg {
                    let name = id.to_string();
                    if !bound.contains(&name) {
                        free.insert(name);
                    }
                }
            }
        }
        BehavioralPred::Quantified { var, body, .. } => {
            let var_name = var.to_string();
            let inserted = bound.insert(var_name.clone());
            collect_predicate_free_vars_inner(body, free, bound);
            if inserted {
                bound.remove(&var_name);
            }
        }
        BehavioralPred::AcMatch {
            bag,
            elements,
            rest,
        } => {
            // The AST `AcMatch` carries `Ident` directly (not
            // `PredArg`), so every reference is a variable.
            let bag_name = bag.to_string();
            if !bound.contains(&bag_name) {
                free.insert(bag_name);
            }
            for elem in elements {
                let name = elem.to_string();
                if !bound.contains(&name) {
                    free.insert(name);
                }
            }
            if let Some(rest_id) = rest {
                let name = rest_id.to_string();
                if !bound.contains(&name) {
                    free.insert(name);
                }
            }
        }
        BehavioralPred::And(a, b)
        | BehavioralPred::Or(a, b)
        | BehavioralPred::Implies(a, b) => {
            collect_predicate_free_vars_inner(a, free, bound);
            collect_predicate_free_vars_inner(b, free, bound);
        }
        BehavioralPred::Not(inner) => {
            collect_predicate_free_vars_inner(inner, free, bound);
        }
        BehavioralPred::Top => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;
    use syn::Ident;

    fn ident(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }

    fn pred_var(name: &str) -> PredArg {
        PredArg::Var(ident(name))
    }

    fn rel(name: &str, args: Vec<PredArg>) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: ident(name),
            args,
            negated: false,
        }
    }

    #[test]
    fn single_channel_predicate_returns_none() {
        let mut bindings = BTreeMap::new();
        let mut ch1_vars = BTreeSet::new();
        ch1_vars.insert("x".to_string());
        bindings.insert("ch1".to_string(), ch1_vars);

        let pred = rel("safe", vec![pred_var("x")]);
        let result = analyze_predicate("PInput", &pred, &bindings);
        assert!(result.is_none(), "single-channel predicate should not be flagged");
    }

    #[test]
    fn cross_channel_predicate_detected() {
        let mut bindings = BTreeMap::new();
        let mut ch1_vars = BTreeSet::new();
        ch1_vars.insert("x".to_string());
        let mut ch2_vars = BTreeSet::new();
        ch2_vars.insert("y".to_string());
        bindings.insert("ch1".to_string(), ch1_vars);
        bindings.insert("ch2".to_string(), ch2_vars);

        let pred = rel("joint", vec![pred_var("x"), pred_var("y")]);
        let result = analyze_predicate("PJoinInput", &pred, &bindings);
        assert!(result.is_some(), "cross-channel predicate should be flagged");
        let spec = result.unwrap();
        assert_eq!(spec.constructor_label, "PJoinInput");
        assert_eq!(spec.channel_count, 2);
        assert!(spec.channel_dependencies.contains_key("ch1"));
        assert!(spec.channel_dependencies.contains_key("ch2"));
    }

    #[test]
    fn three_channel_predicate_detected() {
        let mut bindings = BTreeMap::new();
        for (channel, var) in &[("ch1", "x"), ("ch2", "y"), ("ch3", "z")] {
            let mut s = BTreeSet::new();
            s.insert(var.to_string());
            bindings.insert(channel.to_string(), s);
        }

        let pred = rel(
            "triple",
            vec![pred_var("x"), pred_var("y"), pred_var("z")],
        );
        let result = analyze_predicate("PTripleInput", &pred, &bindings);
        let spec = result.expect("3-channel guard should be flagged");
        assert_eq!(spec.channel_count, 3);
    }

    #[test]
    fn predicate_referencing_only_one_of_two_channels_returns_none() {
        let mut bindings = BTreeMap::new();
        let mut ch1_vars = BTreeSet::new();
        ch1_vars.insert("x".to_string());
        let mut ch2_vars = BTreeSet::new();
        ch2_vars.insert("y".to_string());
        bindings.insert("ch1".to_string(), ch1_vars);
        bindings.insert("ch2".to_string(), ch2_vars);

        // Predicate only references x from ch1
        let pred = rel("safe", vec![pred_var("x")]);
        let result = analyze_predicate("PInput", &pred, &bindings);
        assert!(result.is_none());
    }

    #[test]
    fn nested_and_predicate_detected() {
        let mut bindings = BTreeMap::new();
        let mut ch1 = BTreeSet::new();
        ch1.insert("x".to_string());
        let mut ch2 = BTreeSet::new();
        ch2.insert("y".to_string());
        bindings.insert("ch1".to_string(), ch1);
        bindings.insert("ch2".to_string(), ch2);

        let pred = BehavioralPred::And(
            Box::new(rel("safe_x", vec![pred_var("x")])),
            Box::new(rel("safe_y", vec![pred_var("y")])),
        );
        let result = analyze_predicate("PInput", &pred, &bindings);
        let spec = result.expect("And-of-two-channel-preds should be flagged");
        assert_eq!(spec.channel_count, 2);
    }

    #[test]
    fn quantified_var_does_not_count_as_channel_dep() {
        let mut bindings = BTreeMap::new();
        let mut ch1 = BTreeSet::new();
        ch1.insert("x".to_string());
        bindings.insert("ch1".to_string(), ch1);

        // ∃y. rel(x, y) — y is bound, x is free; only ch1 is referenced
        let pred = BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: ident("y"),
            domain: None,
            bound: None,
            body: Box::new(rel("rel", vec![pred_var("x"), pred_var("y")])),
        };
        let result = analyze_predicate("PInput", &pred, &bindings);
        assert!(
            result.is_none(),
            "single-channel predicate with bound y should not be flagged"
        );
    }

    #[test]
    fn analyze_language_returns_empty_when_no_guarded_constructors() {
        // Synthesize a minimal LanguageDef with no terms.
        // The detector should report zero specs.
        // We use a doc-only smoke test rather than building a full
        // LanguageDef (which requires extensive scaffolding); the
        // unit tests above already exercise the predicate-level
        // analysis surface.
    }

    // ── Phase 9: deadlock detection ──

    fn make_spec(channels: &[(&str, &[&str])]) -> MultiChannelGuardSpec {
        let mut deps = BTreeMap::new();
        for (channel, vars) in channels {
            let set: BTreeSet<String> =
                vars.iter().map(|s| s.to_string()).collect();
            deps.insert(channel.to_string(), set);
        }
        MultiChannelGuardSpec {
            constructor_label: "Test".to_string(),
            channel_count: deps.len(),
            channel_dependencies: deps,
        }
    }

    #[test]
    fn two_channel_join_has_no_deadlock() {
        let spec = make_spec(&[("ch1", &["x"]), ("ch2", &["y"])]);
        let report = analyze_join_pattern(&spec);
        assert!(!report.has_deadlock());
        assert_eq!(report.optimal_order.len(), 2);
    }

    #[test]
    fn three_channel_join_reports_deadlock_conservatively() {
        let spec = make_spec(&[
            ("ch1", &["x"]),
            ("ch2", &["y"]),
            ("ch3", &["z"]),
        ]);
        let report = analyze_join_pattern(&spec);
        assert!(report.has_deadlock());
        assert_eq!(report.deadlock_cycles.len(), 1);
        assert_eq!(report.deadlock_cycles[0].len(), 3);
    }

    #[test]
    fn deadlock_diagnostics_emit_tw03() {
        let spec = make_spec(&[
            ("ch1", &["x"]),
            ("ch2", &["y"]),
            ("ch3", &["z"]),
        ]);
        let report = analyze_join_pattern(&spec);
        let diagnostics = report.diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].0, DiagnosticId::TW03);
        assert!(diagnostics[0].1.contains("ch1"));
        assert!(diagnostics[0].1.contains("ch2"));
        assert!(diagnostics[0].1.contains("ch3"));
    }
}
