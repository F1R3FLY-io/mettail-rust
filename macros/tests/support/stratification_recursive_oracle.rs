use super::*;
use mettail_ast::language::{PredArg, Quantifier};
use proc_macro2::Span;

fn ident(name: &str) -> syn::Ident {
    syn::Ident::new(name, Span::call_site())
}

fn relation(name: &str, negated: bool) -> BehavioralPred {
    BehavioralPred::RelationQuery {
        relation_name: ident(name),
        args: vec![PredArg::Var(ident("x"))],
        negated,
    }
}

fn collect_relation_refs_recursive(
    pred: &BehavioralPred,
    inside_negation: bool,
    refs: &mut Vec<(String, EdgeKind)>,
) {
    match pred {
        BehavioralPred::RelationQuery { relation_name, negated, .. } => refs.push((
            relation_name.to_string(),
            if inside_negation ^ negated {
                EdgeKind::Negative
            } else {
                EdgeKind::Positive
            },
        )),
        BehavioralPred::Not(inner) => {
            collect_relation_refs_recursive(inner, !inside_negation, refs);
        },
        BehavioralPred::And(left, right) | BehavioralPred::Or(left, right) => {
            collect_relation_refs_recursive(left, inside_negation, refs);
            collect_relation_refs_recursive(right, inside_negation, refs);
        },
        BehavioralPred::Implies(antecedent, consequent) => {
            collect_relation_refs_recursive(antecedent, !inside_negation, refs);
            collect_relation_refs_recursive(consequent, inside_negation, refs);
        },
        BehavioralPred::Quantified { body, .. } => {
            collect_relation_refs_recursive(body, inside_negation, refs);
        },
        BehavioralPred::AcMatch { .. } | BehavioralPred::Top => {},
    }
}

fn add_premise_edge_recursive(
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
            let mut refs = Vec::new();
            collect_relation_refs_recursive(pred, false, &mut refs);
            for (target, kind) in refs {
                add_edge(source, target, kind, graph, node_set);
            }
        },
        Premise::ForAll { body, .. } => {
            add_premise_edge_recursive(source, body, graph, node_set);
        },
        Premise::Freshness(_)
        | Premise::Congruence { .. }
        | Premise::CongruenceWithheld { .. }
        | Premise::SyntheticInjGuard { .. } => {},
    }
}

fn tarjan_scc_recursive(graph: &BTreeMap<String, Vec<(String, EdgeKind)>>) -> Vec<Vec<String>> {
    struct State<'a> {
        graph: &'a BTreeMap<String, Vec<(String, EdgeKind)>>,
        index: usize,
        index_of: HashMap<&'a str, usize>,
        lowlink: HashMap<&'a str, usize>,
        on_stack: HashSet<&'a str>,
        stack: Vec<&'a str>,
        sccs: Vec<Vec<String>>,
    }

    fn strong_connect<'a>(state: &mut State<'a>, node: &'a str) {
        state.index_of.insert(node, state.index);
        state.lowlink.insert(node, state.index);
        state.index += 1;
        state.stack.push(node);
        state.on_stack.insert(node);

        if let Some(edges) = state.graph.get(node) {
            for (target, _) in edges {
                let target = target.as_str();
                if !state.index_of.contains_key(target) {
                    strong_connect(state, target);
                    let child_lowlink = state.lowlink[target];
                    let node_lowlink = state.lowlink[node];
                    state.lowlink.insert(node, node_lowlink.min(child_lowlink));
                } else if state.on_stack.contains(target) {
                    let target_index = state.index_of[target];
                    let node_lowlink = state.lowlink[node];
                    state.lowlink.insert(node, node_lowlink.min(target_index));
                }
            }
        }

        if state.lowlink[node] == state.index_of[node] {
            let mut scc = Vec::new();
            loop {
                let member = state.stack.pop().expect("recursive oracle SCC stack");
                state.on_stack.remove(member);
                scc.push(member.to_string());
                if member == node {
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
    for node in graph.keys() {
        let node = node.as_str();
        if !state.index_of.contains_key(node) {
            strong_connect(&mut state, node);
        }
    }
    state.sccs
}

fn run_on_small_stack(test_name: &str, test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(256 * 1024)
        .spawn(test)
        .expect("spawn stratification small-stack test")
        .join()
        .expect("stratification small-stack test panicked");
}

#[test]
fn stratification_recursive_oracle_predicate_order_and_polarity_are_exact() {
    let fixture = BehavioralPred::Implies(
        Box::new(BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: ident("x"),
            domain: Some(ident("nodes")),
            bound: Some(7),
            body: Box::new(BehavioralPred::Not(Box::new(relation("antecedent", true)))),
        }),
        Box::new(BehavioralPred::Or(
            Box::new(relation("left", false)),
            Box::new(BehavioralPred::And(
                Box::new(relation("middle", true)),
                Box::new(relation("right", false)),
            )),
        )),
    );
    let mut expected = Vec::new();
    collect_relation_refs_recursive(&fixture, false, &mut expected);
    assert_eq!(collect_relation_refs(&fixture), expected);
}

#[test]
fn stratification_recursive_oracle_forall_edge_order_is_exact() {
    let predicate = BehavioralPred::And(
        Box::new(relation("negative", true)),
        Box::new(relation("positive", false)),
    );
    let premise = Premise::ForAll {
        collection: ident("outer"),
        param: ident("x"),
        body: Box::new(Premise::ForAll {
            collection: ident("inner"),
            param: ident("y"),
            body: Box::new(Premise::BehavioralGuard(predicate)),
        }),
    };
    let mut expected_graph = BTreeMap::new();
    let mut expected_nodes = BTreeSet::new();
    add_premise_edge_recursive("source", &premise, &mut expected_graph, &mut expected_nodes);
    let mut actual_graph = BTreeMap::new();
    let mut actual_nodes = BTreeSet::new();
    add_premise_edge("source", &premise, &mut actual_graph, &mut actual_nodes);
    assert_eq!(actual_graph, expected_graph);
    assert_eq!(actual_nodes, expected_nodes);
}

#[test]
fn stratification_recursive_oracle_tarjan_order_is_exact() {
    let mut graph = BTreeMap::new();
    graph.insert(
        "A".to_string(),
        vec![("B".to_string(), EdgeKind::Positive), ("D".to_string(), EdgeKind::Negative)],
    );
    graph.insert("B".to_string(), vec![("C".to_string(), EdgeKind::Positive)]);
    graph.insert("C".to_string(), vec![("A".to_string(), EdgeKind::Negative)]);
    graph.insert("D".to_string(), vec![("E".to_string(), EdgeKind::Positive)]);
    graph.insert("E".to_string(), vec![("D".to_string(), EdgeKind::Negative)]);
    graph.insert("F".to_string(), Vec::new());
    assert_eq!(tarjan_scc(&graph), tarjan_scc_recursive(&graph));
}

#[test]
fn stratification_recursive_oracle_deep_predicate_survives_small_stack() {
    run_on_small_stack("stratification-deep-predicate", || {
        let mut predicate = relation("leaf", false);
        for _ in 0..20_001 {
            predicate = BehavioralPred::Not(Box::new(predicate));
        }
        assert_eq!(
            collect_relation_refs(&predicate),
            vec![("leaf".to_string(), EdgeKind::Negative)]
        );
    });
}

#[test]
fn stratification_recursive_oracle_deep_forall_survives_small_stack() {
    run_on_small_stack("stratification-deep-forall", || {
        let mut premise = Premise::RelationQuery {
            relation: ident("target"),
            args: Vec::new(),
        };
        for depth in 0..20_000 {
            premise = Premise::ForAll {
                collection: ident(&format!("c{depth}")),
                param: ident(&format!("p{depth}")),
                body: Box::new(premise),
            };
        }
        let mut graph = BTreeMap::new();
        let mut nodes = BTreeSet::new();
        add_premise_edge("source", &premise, &mut graph, &mut nodes);
        assert_eq!(graph["source"], vec![("target".to_string(), EdgeKind::Positive)]);
    });
}

#[test]
fn stratification_recursive_oracle_deep_tarjan_survives_small_stack() {
    run_on_small_stack("stratification-deep-tarjan", || {
        const NODE_COUNT: usize = 20_000;
        let mut graph = BTreeMap::new();
        for index in 0..NODE_COUNT {
            let node = format!("n{index:05}");
            let edges = (index + 1 < NODE_COUNT)
                .then(|| vec![(format!("n{:05}", index + 1), EdgeKind::Positive)])
                .unwrap_or_default();
            graph.insert(node, edges);
        }
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), NODE_COUNT);
        assert_eq!(sccs.first(), Some(&vec![format!("n{:05}", NODE_COUNT - 1)]));
        assert_eq!(sccs.last(), Some(&vec!["n00000".to_string()]));
    });
}
