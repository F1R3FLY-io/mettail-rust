//! Stratification analysis for negated relation references.
//!
//! Phase 3F (predicated types): the Phase 3E negation lowering emits
//! Ascent's `! rel(args)` operator. Ascent's type system requires that a
//! negated relation be in a strictly earlier stratum than the rule that
//! references it; otherwise, the program is non-stratifiable and the
//! semantics of the fixpoint become undefined.
//!
//! This module walks the language's logic relations + behavioral
//! predicates and detects strata that contain a relation `R` defined by
//! a rule whose body negates `R` (directly or transitively). When a
//! cycle is found, it emits the `STRAT01` lint diagnostic with a
//! descriptive cycle path.
//!
//! ## Algorithm
//!
//! 1. Build a directed dependency graph:
//!    - Node = relation name
//!    - Edge `A → B` if relation `A` is defined by a rule that
//!      references `B` (positively OR negatively).
//!    - Edge `A ⤳ B` (marked) if relation `A` is defined by a rule that
//!      references `B` **negatively**.
//! 2. Compute strongly connected components (SCCs) via Tarjan's
//!    algorithm.
//! 3. For each SCC, walk every edge inside the SCC. If any negative edge
//!    `A ⤳ B` exists with both `A` and `B` in the same SCC, the program
//!    is non-stratifiable — emit `STRAT01` with the cycle path.
//!
//! ## When this runs
//!
//! At macro expansion time, after `language!` has parsed the
//! `logic { }` block but before generating the Ascent program. The
//! validator is invoked from
//! `mettail-macros::logic::generate_logic_block`.

use mettail_ast::language::{BehavioralPred, LanguageDef, Premise};
use mettail_prattail::lint::DiagnosticId;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Result of stratification analysis.
#[derive(Debug, Clone, Default)]
pub struct StratificationReport {
    /// Cycles where a relation depends negatively on itself
    /// (transitively). Each entry is the cycle's relation path.
    pub negative_cycles: Vec<Vec<String>>,
}

impl StratificationReport {
    /// True if the analysis found at least one stratification violation.
    pub fn has_violations(&self) -> bool {
        !self.negative_cycles.is_empty()
    }

    /// Format every violation as a `STRAT01` diagnostic message.
    pub fn diagnostics(&self) -> Vec<(DiagnosticId, String)> {
        self.negative_cycles
            .iter()
            .map(|cycle| {
                (
                    DiagnosticId::STRAT01,
                    format!(
                        "STRAT01: stratification violation — relation `{}` depends \
                         negatively on itself through the cycle `{}`. Ascent rejects \
                         non-stratifiable programs because their fixpoint semantics \
                         are undefined.",
                        cycle.first().cloned().unwrap_or_default(),
                        cycle.join(" → "),
                    ),
                )
            })
            .collect()
    }
}

/// Edge classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EdgeKind {
    Positive,
    Negative,
}

/// Build the relation dependency graph and detect negative cycles.
///
/// The graph is built from the language's `logic { }` block:
/// - Each `relation R(...)` declaration produces a node `R`.
/// - Each `Premise::BehavioralGuard` whose enclosing rule defines
///   relation `A` produces an edge `A → B` for every relation `B`
///   referenced by the guard predicate, with the edge classified as
///   `Negative` iff the reference is wrapped in a `Not(...)`.
///
/// Equation and rewrite premises can carry behavioral guards. We use the
/// equation/rewrite name as the defining node and add an edge to each
/// referenced relation. Positive `rel(args)` premises are included too,
/// so Tarjan sees the full premise dependency graph.
pub fn analyze(language: &LanguageDef) -> StratificationReport {
    let mut graph: BTreeMap<String, Vec<(String, EdgeKind)>> = BTreeMap::new();
    let mut node_set: BTreeSet<String> = BTreeSet::new();

    // Seed the node set with every declared relation.
    if let Some(logic_block) = &language.logic {
        for rel in &logic_block.relations {
            node_set.insert(rel.name.to_string());
        }
    }

    // Walk every grammar rule's `?guard:Guard(<inline>)` declarations.
    // For each one, the slot's syntax already declares which constructor
    // it belongs to; the predicate defines which relations the slot
    // references. We add an edge from the constructor's "logical
    // relation name" to each predicate-referenced relation. Since
    // constructors don't directly correspond to relations in the
    // current schema, we use the constructor label itself as the
    // virtual node — this catches the cycle case where two guards on
    // the same constructor mutually negate each other.
    for rule in &language.terms {
        let label = rule.label.to_string();
        let term_context = match &rule.term_context {
            Some(ctx) => ctx,
            None => continue,
        };
        for param in term_context {
            // The current `?guard:Guard` syntax (Phase 2C) carries no
            // inline predicate, so this loop short-circuits for
            // GuardedRho. The framework is in place for Phase 11's
            // `#[tier(...)]` and the future inline-predicate variant.
            // We still build the node so the graph is complete for
            // languages that use spec-time predicates.
            if let mettail_ast::grammar::TermParam::GuardBody { name } = param {
                let _ = name;
                node_set.insert(label.clone());
                graph.entry(label.clone()).or_default();
            }
        }
    }

    for eq in &language.equations {
        add_premise_edges(&eq.name.to_string(), &eq.premises, &mut graph, &mut node_set);
    }

    for rw in &language.rewrites {
        add_premise_edges(&rw.name.to_string(), &rw.premises, &mut graph, &mut node_set);
    }

    // Ensure every node has an (empty) entry in the adjacency map.
    for node in &node_set {
        graph.entry(node.clone()).or_default();
    }

    // Tarjan's SCC algorithm.
    let sccs = tarjan_scc(&graph);

    // For each SCC, check whether any in-SCC edge is negative.
    let mut negative_cycles: Vec<Vec<String>> = Vec::new();
    for scc in &sccs {
        if scc.len() < 2 {
            // A single-node SCC is only a cycle if it has a self-edge.
            let node = &scc[0];
            if let Some(edges) = graph.get(node) {
                for (target, kind) in edges {
                    if target == node && *kind == EdgeKind::Negative {
                        negative_cycles.push(vec![node.clone(), node.clone()]);
                    }
                }
            }
            continue;
        }
        let scc_set: HashSet<&String> = scc.iter().collect();
        for src in scc {
            if let Some(edges) = graph.get(src) {
                for (dst, kind) in edges {
                    if *kind == EdgeKind::Negative && scc_set.contains(dst) {
                        // Found a negative back-edge inside the SCC.
                        negative_cycles.push(scc.clone());
                        break;
                    }
                }
            }
        }
    }

    StratificationReport { negative_cycles }
}

/// Walk a `BehavioralPred` and collect every referenced relation name
/// along with whether the reference is negated.
///
/// Used by callers that build the graph from inline guard predicates.
fn collect_relation_refs(pred: &BehavioralPred) -> Vec<(String, EdgeKind)> {
    let mut acc = Vec::new();
    collect_relation_refs_inner(pred, false, &mut acc);
    acc
}

fn add_premise_edges(
    source: &str,
    premises: &[Premise],
    graph: &mut BTreeMap<String, Vec<(String, EdgeKind)>>,
    node_set: &mut BTreeSet<String>,
) {
    node_set.insert(source.to_string());
    graph.entry(source.to_string()).or_default();

    for premise in premises {
        add_premise_edge(source, premise, graph, node_set);
    }
}

fn add_premise_edge(
    source: &str,
    premise: &Premise,
    graph: &mut BTreeMap<String, Vec<(String, EdgeKind)>>,
    node_set: &mut BTreeSet<String>,
) {
    match premise {
        Premise::RelationQuery { relation, .. } => {
            add_edge(source, relation.to_string(), EdgeKind::Positive, graph, node_set);
        },
        Premise::BehavioralGuard(pred) => {
            for (target, kind) in collect_relation_refs(pred) {
                add_edge(source, target, kind, graph, node_set);
            }
        },
        Premise::ForAll { body, .. } => {
            add_premise_edge(source, body, graph, node_set);
        },
        Premise::Freshness(_) | Premise::Congruence { .. } | Premise::SyntheticInjGuard { .. } => {
        },
    }
}

fn add_edge(
    source: &str,
    target: String,
    kind: EdgeKind,
    graph: &mut BTreeMap<String, Vec<(String, EdgeKind)>>,
    node_set: &mut BTreeSet<String>,
) {
    node_set.insert(source.to_string());
    node_set.insert(target.clone());
    graph
        .entry(source.to_string())
        .or_default()
        .push((target, kind));
}

fn collect_relation_refs_inner(
    pred: &BehavioralPred,
    inside_negation: bool,
    acc: &mut Vec<(String, EdgeKind)>,
) {
    match pred {
        BehavioralPred::RelationQuery { relation_name, negated, .. } => {
            let effective_negated = inside_negation ^ negated;
            let kind = if effective_negated {
                EdgeKind::Negative
            } else {
                EdgeKind::Positive
            };
            acc.push((relation_name.to_string(), kind));
        },
        BehavioralPred::Not(inner) => {
            collect_relation_refs_inner(inner, !inside_negation, acc);
        },
        BehavioralPred::And(a, b) | BehavioralPred::Or(a, b) => {
            collect_relation_refs_inner(a, inside_negation, acc);
            collect_relation_refs_inner(b, inside_negation, acc);
        },
        BehavioralPred::Implies(a, b) => {
            // P ⟹ Q ≡ ¬P ∨ Q : the antecedent is negated.
            collect_relation_refs_inner(a, !inside_negation, acc);
            collect_relation_refs_inner(b, inside_negation, acc);
        },
        BehavioralPred::Quantified { body, .. } => {
            collect_relation_refs_inner(body, inside_negation, acc);
        },
        BehavioralPred::AcMatch { .. } | BehavioralPred::Top => {},
    }
}

/// Tarjan's strongly connected components algorithm.
///
/// Returns SCCs in reverse topological order. Each SCC is a vector of
/// node names; single-node SCCs are included.
fn tarjan_scc(graph: &BTreeMap<String, Vec<(String, EdgeKind)>>) -> Vec<Vec<String>> {
    struct State<'a> {
        graph: &'a BTreeMap<String, Vec<(String, EdgeKind)>>,
        index: usize,
        index_of: HashMap<&'a str, usize>,
        lowlink: HashMap<&'a str, usize>,
        on_stack: HashSet<&'a str>,
        stack: Vec<&'a str>,
        sccs: Vec<Vec<String>>,
    }

    fn strong_connect<'a>(state: &mut State<'a>, v: &'a str) {
        state.index_of.insert(v, state.index);
        state.lowlink.insert(v, state.index);
        state.index += 1;
        state.stack.push(v);
        state.on_stack.insert(v);

        if let Some(edges) = state.graph.get(v) {
            for (w, _) in edges {
                let w_str: &str = w.as_str();
                if !state.index_of.contains_key(w_str) {
                    strong_connect(state, w_str);
                    let w_low = state.lowlink[w_str];
                    let v_low = state.lowlink[v];
                    state.lowlink.insert(v, v_low.min(w_low));
                } else if state.on_stack.contains(w_str) {
                    let w_idx = state.index_of[w_str];
                    let v_low = state.lowlink[v];
                    state.lowlink.insert(v, v_low.min(w_idx));
                }
            }
        }

        if state.lowlink[v] == state.index_of[v] {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().expect("non-empty stack inside SCC");
                state.on_stack.remove(w);
                scc.push(w.to_string());
                if w == v {
                    break;
                }
            }
            state.sccs.push(scc);
        }
    }

    let mut state = State {
        graph,
        index: 0,
        index_of: HashMap::new(),
        lowlink: HashMap::new(),
        on_stack: HashSet::new(),
        stack: Vec::new(),
        sccs: Vec::new(),
    };

    for v in graph.keys() {
        let v_str: &str = v.as_str();
        if !state.index_of.contains_key(v_str) {
            strong_connect(&mut state, v_str);
        }
    }

    state.sccs
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::{
        language::{AttributeValue, Equation, GuardConfig, LangType, PredArg, RewriteRule},
        pattern::{Pattern, PatternTerm},
    };
    use std::collections::HashMap;

    fn pred_var(name: &str) -> PredArg {
        PredArg::Var(syn::Ident::new(name, proc_macro2::Span::call_site()))
    }

    fn ident(name: &str) -> syn::Ident {
        syn::Ident::new(name, proc_macro2::Span::call_site())
    }

    fn var_pattern(name: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(ident(name)))
    }

    fn rel(name: &str, args: Vec<PredArg>, negated: bool) -> BehavioralPred {
        BehavioralPred::RelationQuery {
            relation_name: ident(name),
            args,
            negated,
        }
    }

    fn minimal_lang() -> LanguageDef {
        LanguageDef {
            name: ident("TestLang"),
            options: HashMap::<String, AttributeValue>::new(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::<LangType>::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None::<GuardConfig>,
        }
    }

    #[test]
    fn collect_relation_refs_positive() {
        let p = rel("halts", vec![pred_var("x")], false);
        let refs = collect_relation_refs(&p);
        assert_eq!(refs, vec![("halts".to_string(), EdgeKind::Positive)]);
    }

    #[test]
    fn collect_relation_refs_negated_via_flag() {
        let p = rel("halts", vec![pred_var("x")], true);
        let refs = collect_relation_refs(&p);
        assert_eq!(refs, vec![("halts".to_string(), EdgeKind::Negative)]);
    }

    #[test]
    fn collect_relation_refs_negated_via_not_wrapper() {
        let inner = rel("halts", vec![pred_var("x")], false);
        let p = BehavioralPred::Not(Box::new(inner));
        let refs = collect_relation_refs(&p);
        assert_eq!(refs, vec![("halts".to_string(), EdgeKind::Negative)]);
    }

    #[test]
    fn collect_relation_refs_double_negation_cancels() {
        let inner = rel("halts", vec![pred_var("x")], true);
        let p = BehavioralPred::Not(Box::new(inner));
        let refs = collect_relation_refs(&p);
        assert_eq!(refs, vec![("halts".to_string(), EdgeKind::Positive)]);
    }

    #[test]
    fn collect_relation_refs_implies_antecedent_negated() {
        let p = BehavioralPred::Implies(
            Box::new(rel("halts", vec![pred_var("x")], false)),
            Box::new(rel("safe", vec![pred_var("x")], false)),
        );
        let refs = collect_relation_refs(&p);
        assert!(refs.contains(&("halts".to_string(), EdgeKind::Negative)));
        assert!(refs.contains(&("safe".to_string(), EdgeKind::Positive)));
    }

    #[test]
    fn analyze_detects_negative_behavioral_guard_self_cycle_in_rewrite() {
        let mut lang = minimal_lang();
        lang.rewrites.push(RewriteRule {
            name: ident("halts"),
            type_context: Vec::new(),
            premises: vec![Premise::BehavioralGuard(BehavioralPred::Not(Box::new(rel(
                "halts",
                vec![pred_var("x")],
                false,
            ))))],
            left: var_pattern("x"),
            right: var_pattern("x"),
            is_auto_injected: false,
        });

        let report = analyze(&lang);
        assert!(report.has_violations());
        assert_eq!(report.negative_cycles, vec![vec!["halts".to_string(), "halts".to_string()]]);
    }

    #[test]
    fn analyze_keeps_positive_self_reference_stratified() {
        let mut lang = minimal_lang();
        lang.equations.push(Equation {
            name: ident("safe"),
            type_context: Vec::new(),
            premises: vec![Premise::RelationQuery {
                relation: ident("safe"),
                args: vec![ident("x")],
            }],
            left: var_pattern("x"),
            right: var_pattern("x"),
        });

        let report = analyze(&lang);
        assert!(!report.has_violations(), "{:?}", report);
    }

    #[test]
    fn tarjan_self_cycle_detected() {
        let mut graph = BTreeMap::new();
        graph.insert("A".to_string(), vec![("A".to_string(), EdgeKind::Negative)]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec!["A".to_string()]);
    }

    #[test]
    fn tarjan_two_cycle_detected() {
        let mut graph = BTreeMap::new();
        graph.insert("A".to_string(), vec![("B".to_string(), EdgeKind::Positive)]);
        graph.insert("B".to_string(), vec![("A".to_string(), EdgeKind::Negative)]);
        let sccs = tarjan_scc(&graph);
        // Both nodes should land in the same SCC.
        let two_cycle = sccs.iter().find(|s| s.len() == 2);
        assert!(two_cycle.is_some(), "expected a 2-node SCC: {:?}", sccs);
    }

    #[test]
    fn tarjan_acyclic_returns_singletons() {
        let mut graph = BTreeMap::new();
        graph.insert("A".to_string(), vec![("B".to_string(), EdgeKind::Positive)]);
        graph.insert("B".to_string(), vec![]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 2);
        assert!(sccs.iter().all(|s| s.len() == 1));
    }
}
