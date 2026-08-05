use super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OracleTerm {
    Var(String),
    App { symbol: String, args: Vec<OracleTerm> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OraclePattern {
    Var(String),
    App { symbol: String, args: Vec<OraclePattern> },
}

fn oracle_term(term: &Term) -> OracleTerm {
    match term {
        Term::Var(name) => OracleTerm::Var(name.clone()),
        Term::App { symbol, args } => OracleTerm::App {
            symbol: symbol.clone(),
            args: args.iter().map(oracle_term).collect(),
        },
    }
}

fn oracle_pattern(pattern: &Pattern) -> OraclePattern {
    match pattern {
        Pattern::Var(name) => OraclePattern::Var(name.clone()),
        Pattern::App { symbol, args } => OraclePattern::App {
            symbol: symbol.clone(),
            args: args.iter().map(oracle_pattern).collect(),
        },
    }
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn recursive_add_term(graph: &mut EGraph, term: &Term) -> EClassId {
    match term {
        Term::Var(name) => graph.add(ENode::leaf(format!("__var_{name}"))),
        Term::App { symbol, args } => {
            let children = args
                .iter()
                .map(|arg| recursive_add_term(graph, arg))
                .collect();
            graph.add(ENode::with_children(symbol, children))
        },
    }
}

fn recursive_from_term(term: &Term) -> Pattern {
    match term {
        Term::Var(name) => Pattern::Var(name.clone()),
        Term::App { symbol, args } => Pattern::App {
            symbol: symbol.clone(),
            args: args.iter().map(recursive_from_term).collect(),
        },
    }
}

fn recursive_to_term(pattern: &Pattern) -> Term {
    match pattern {
        Pattern::Var(name) => Term::Var(name.clone()),
        Pattern::App { symbol, args } => Term::App {
            symbol: symbol.clone(),
            args: args.iter().map(recursive_to_term).collect(),
        },
    }
}

fn recursive_collect_matches(
    graph: &EGraph,
    pattern: &Pattern,
    class_id: EClassId,
    subst: &Subst,
    results: &mut Vec<(EClassId, Subst)>,
) {
    let class_id = graph.find(class_id);
    match pattern {
        Pattern::Var(name) => match subst.get(name) {
            Some(&existing) if graph.find(existing) == class_id => {
                results.push((class_id, subst.clone()));
            },
            Some(_) => {},
            None => {
                let mut subst = subst.clone();
                subst.insert(name.clone(), class_id);
                results.push((class_id, subst));
            },
        },
        Pattern::App { symbol, args } => {
            let Some(class) = graph.classes.get(&class_id) else {
                return;
            };
            for node in &class.nodes {
                if node.symbol == *symbol && node.children.len() == args.len() {
                    recursive_match_children(graph, args, &node.children, subst, class_id, results);
                }
            }
        },
    }
}

fn recursive_match_children(
    graph: &EGraph,
    patterns: &[Pattern],
    children: &[EClassId],
    subst: &Subst,
    root: EClassId,
    results: &mut Vec<(EClassId, Subst)>,
) {
    if patterns.is_empty() {
        results.push((root, subst.clone()));
        return;
    }
    let mut child_matches = Vec::new();
    recursive_collect_matches(graph, &patterns[0], children[0], subst, &mut child_matches);
    for (_, subst) in child_matches {
        recursive_match_children(graph, &patterns[1..], &children[1..], &subst, root, results);
    }
}

fn recursive_instantiate(graph: &mut EGraph, pattern: &Pattern, subst: &Subst) -> Option<EClassId> {
    match pattern {
        Pattern::Var(name) => match subst.get(name) {
            Some(&id) => Some(id),
            None => graph.try_add_with_budget(ENode::leaf(format!("__var_{name}"))),
        },
        Pattern::App { symbol, args } => {
            let mut children = Vec::with_capacity(args.len());
            for arg in args {
                children.push(recursive_instantiate(graph, arg, subst)?);
            }
            graph.try_add_with_budget(ENode::with_children(symbol, children))
        },
    }
}

fn recursive_reconstruct(
    graph: &EGraph,
    id: EClassId,
    best: &HashMap<EClassId, (u64, usize)>,
) -> Term {
    let id = graph.find(id);
    let (_, node_index) = best[&id];
    let node = &graph.classes[&id].nodes[node_index];
    if node.children.is_empty() && node.symbol.starts_with("__var_") {
        return Term::Var(node.symbol[6..].to_string());
    }
    let args = node
        .children
        .iter()
        .map(|&child| recursive_reconstruct(graph, child, best))
        .collect();
    if node.children.is_empty() {
        Term::constant(&node.symbol)
    } else {
        Term::app(&node.symbol, args)
    }
}

fn fixture() -> Term {
    Term::app(
        "Pair",
        vec![
            Term::app("Wrap", vec![Term::var("x")]),
            Term::app("Wrap", vec![Term::constant("A")]),
        ],
    )
}

#[test]
fn iterative_term_pattern_and_egraph_operations_match_recursive_oracles() {
    let term = fixture();
    let oracle_term = oracle_term(&term);
    assert_eq!(format!("{term:?}"), format!("{oracle_term:?}"));
    assert_eq!(hash(&term), hash(&oracle_term));
    assert_eq!(term.clone(), term);

    let pattern = Pattern::from_term(&term);
    let expected_pattern = recursive_from_term(&term);
    assert_eq!(pattern, expected_pattern);
    assert_eq!(format!("{pattern:?}"), format!("{:?}", oracle_pattern(&pattern)));
    assert_eq!(hash(&pattern), hash(&oracle_pattern(&pattern)));
    assert_eq!(pattern.to_term(), recursive_to_term(&pattern));

    let mut actual_graph = EGraph::new();
    let mut expected_graph = EGraph::new();
    let actual_root = actual_graph.add_term(&term);
    let expected_root = recursive_add_term(&mut expected_graph, &term);
    assert_eq!(actual_root, expected_root);
    assert_eq!(actual_graph.node_count(), expected_graph.node_count());

    let mut actual_matches = Vec::new();
    let mut expected_matches = Vec::new();
    actual_graph.collect_matches(&pattern, actual_root, &Subst::default(), &mut actual_matches);
    recursive_collect_matches(
        &expected_graph,
        &pattern,
        expected_root,
        &Subst::default(),
        &mut expected_matches,
    );
    assert_eq!(actual_matches, expected_matches);

    let actual_instantiated = actual_graph.try_instantiate_pattern(&pattern, &Subst::default());
    let expected_instantiated =
        recursive_instantiate(&mut expected_graph, &pattern, &Subst::default());
    assert_eq!(actual_instantiated, expected_instantiated);
    assert_eq!(actual_graph.node_count(), expected_graph.node_count());

    let actual_best: HashMap<_, _> = actual_graph
        .classes
        .keys()
        .copied()
        .map(|id| (id, (0, 0)))
        .collect();
    let expected_best: HashMap<_, _> = expected_graph
        .classes
        .keys()
        .copied()
        .map(|id| (id, (0, 0)))
        .collect();
    assert_eq!(
        actual_graph.reconstruct_term(actual_root, &actual_best),
        recursive_reconstruct(&expected_graph, expected_root, &expected_best)
    );
}

#[test]
fn term_pattern_and_egraph_pdas_handle_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("prattail-egraph-term-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut term = Term::var("x");
            for _ in 0..DEPTH {
                term = Term::app("N", vec![term]);
            }

            let cloned = term.clone();
            assert_eq!(cloned, term);
            assert_eq!(hash(&cloned), hash(&term));
            assert!(format!("{term:?}").starts_with("App { symbol: \"N\""));
            assert!(term.to_string().starts_with("N(N(N("));
            assert_eq!(term.variables(), vec!["x"]);

            let pattern = Pattern::from_term(&term);
            assert_eq!(pattern.clone(), pattern);
            assert_eq!(pattern.to_term(), term);

            let mut graph = EGraph::new();
            let root = graph.add_term(&term);
            let mut matches = Vec::new();
            graph.collect_matches(&pattern, root, &Subst::default(), &mut matches);
            assert_eq!(matches.len(), 1);

            let instantiated = graph
                .try_instantiate_pattern(&pattern, &Subst::default())
                .expect("deep pattern instantiates within the default budget only if deduplicated");
            assert_eq!(graph.find(instantiated), graph.find(root));

            let best: HashMap<_, _> = graph
                .classes
                .keys()
                .copied()
                .map(|id| (id, (0u64, 0usize)))
                .collect();
            assert_eq!(graph.reconstruct_term(root, &best), term);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("term, pattern, and e-graph PDAs do not overflow a 256 KiB stack");
}
