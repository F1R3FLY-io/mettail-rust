use super::*;

fn recursive_rhs_vars_bound(pattern: &Pattern<String>, subst: &Subst) -> bool {
    match pattern {
        Pattern::Var(name) => subst.contains_key(name),
        Pattern::App { args, .. } => args.iter().all(|arg| recursive_rhs_vars_bound(arg, subst)),
        Pattern::AcApp { fixed, rest, .. } => {
            fixed.iter().all(|arg| recursive_rhs_vars_bound(arg, subst))
                && rest.as_ref().is_none_or(|name| subst.contains_key(name))
        },
    }
}

fn recursive_instantiate(
    graph: &mut EGraph<String>,
    pattern: &Pattern<String>,
    subst: &Subst,
) -> Option<EClassId> {
    match pattern {
        Pattern::Var(name) => subst.get(name).map(|&id| graph.find(id)),
        Pattern::App { op, args } => {
            let mut children = Vec::with_capacity(args.len());
            for arg in args {
                children.push(recursive_instantiate(graph, arg, subst)?);
            }
            graph.try_add_with_budget(ENode::new(op.clone(), children))
        },
        Pattern::AcApp { op, fixed, rest } => {
            let mut children = Vec::with_capacity(fixed.len() + 1);
            for pattern in fixed {
                children.push(recursive_instantiate(graph, pattern, subst)?);
            }
            if let Some(name) = rest {
                children.push(graph.find(*subst.get(name)?));
            }
            graph.add_flattened_bag(op.clone(), &children)
        },
    }
}

fn seeded_graph() -> (EGraph<String>, Subst) {
    let mut graph = EGraph::new();
    let x = graph.add(ENode::leaf("X".to_string()));
    let a = graph.add(ENode::leaf("A".to_string()));
    let b = graph.add(ENode::leaf("B".to_string()));
    let rest = graph.add(ENode::new("Par".to_string(), vec![a, b]));
    let subst = Subst::from_iter([("x".to_string(), x), ("rest".to_string(), rest)]);
    (graph, subst)
}

#[test]
fn iterative_rhs_validation_and_instantiation_match_recursive_oracles() {
    let pattern = Pattern::ac(
        "Par".to_string(),
        vec![Pattern::app("Wrap".to_string(), vec![Pattern::var("x")])],
        Some("rest".to_string()),
    );
    let (mut actual_graph, actual_subst) = seeded_graph();
    let (mut expected_graph, expected_subst) = seeded_graph();
    assert_eq!(
        EGraph::<String>::rhs_vars_bound(&pattern, &actual_subst),
        recursive_rhs_vars_bound(&pattern, &actual_subst)
    );
    let actual = actual_graph.instantiate(&pattern, &actual_subst);
    let expected = recursive_instantiate(&mut expected_graph, &pattern, &expected_subst);
    assert_eq!(actual, expected);
    assert_eq!(actual_graph.node_count(), expected_graph.node_count());
    assert_eq!(
        actual.map(|root| actual_graph.canonical_class_key(root)),
        expected.map(|root| expected_graph.canonical_class_key(root))
    );

    let dangling =
        Pattern::app("Pair".to_string(), vec![Pattern::var("x"), Pattern::var("missing")]);
    assert_eq!(
        EGraph::<String>::rhs_vars_bound(&dangling, &actual_subst),
        recursive_rhs_vars_bound(&dangling, &actual_subst)
    );
}

#[test]
fn rhs_validation_and_instantiation_handle_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("dovetail-instantiation-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut pattern = Pattern::var("x");
            for _ in 0..DEPTH {
                pattern = Pattern::app("N".to_string(), vec![pattern]);
            }
            let mut graph = EGraph::new();
            let x = graph.add(ENode::leaf("X".to_string()));
            let subst = Subst::from_iter([("x".to_string(), x)]);
            assert!(EGraph::<String>::rhs_vars_bound(&pattern, &subst));
            let root = graph
                .instantiate(&pattern, &subst)
                .expect("deep RHS instantiates");
            assert_eq!(graph.node_count(), DEPTH + 1);
            assert_eq!(graph.find(root), root);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("RHS validation/instantiation PDAs do not overflow a 256 KiB stack");
}
