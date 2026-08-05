use super::*;

fn recursive_collect_matches(
    graph: &mut EGraph<String>,
    pattern: &Pattern<String>,
    class: EClassId,
    subst: &Subst,
    out: &mut Vec<(EClassId, Subst)>,
) {
    let class = graph.find(class);
    match pattern {
        Pattern::Var(name) => match subst.get(name) {
            Some(&existing) if graph.find(existing) == class => out.push((class, subst.clone())),
            Some(_) => {},
            None => {
                let mut subst = subst.clone();
                subst.insert(name.clone(), class);
                out.push((class, subst));
            },
        },
        Pattern::App { op, args } => {
            let candidates: Vec<Vec<EClassId>> = graph
                .nodes(class)
                .iter()
                .filter(|node| node.op == *op && node.children.len() == args.len())
                .map(|node| node.children.clone())
                .collect();
            for children in candidates {
                recursive_match_children(graph, args, &children, subst, class, out);
            }
        },
        Pattern::AcApp { op, fixed, rest } => {
            recursive_collect_ac_matches(graph, op, fixed, rest, class, subst, out);
        },
    }
}

fn recursive_match_children(
    graph: &mut EGraph<String>,
    patterns: &[Pattern<String>],
    children: &[EClassId],
    subst: &Subst,
    root: EClassId,
    out: &mut Vec<(EClassId, Subst)>,
) {
    if patterns.is_empty() {
        out.push((root, subst.clone()));
        return;
    }
    let mut child_matches = Vec::new();
    recursive_collect_matches(graph, &patterns[0], children[0], subst, &mut child_matches);
    for (_, child_subst) in child_matches {
        recursive_match_children(graph, &patterns[1..], &children[1..], &child_subst, root, out);
    }
}

fn recursive_collect_ac_matches(
    graph: &mut EGraph<String>,
    op: &String,
    fixed: &[Pattern<String>],
    rest: &Option<String>,
    class: EClassId,
    subst: &Subst,
    out: &mut Vec<(EClassId, Subst)>,
) {
    let bags: Vec<Vec<EClassId>> = graph
        .nodes(class)
        .iter()
        .filter(|node| node.op == *op && node.children.len() >= fixed.len())
        .map(|node| {
            node.children
                .iter()
                .map(|&child| graph.find(child))
                .collect()
        })
        .collect();
    for bag in bags {
        for (selection, complement) in lazy_ac_select(&bag, fixed.len()) {
            let mut paired = Vec::new();
            recursive_pair_fixed(graph, fixed, &selection, subst, &mut paired);
            if paired.is_empty() {
                continue;
            }
            let rest_binding = match rest {
                Some(_) => match graph.add_canonical_bag(op.clone(), &complement) {
                    Some(id) => Some(id),
                    None => continue,
                },
                None => None,
            };
            for mut subst in paired {
                if let (Some(name), Some(id)) = (rest.as_ref(), rest_binding) {
                    subst.insert(name.clone(), id);
                }
                out.push((class, subst));
            }
        }
    }
}

fn recursive_pair_fixed(
    graph: &mut EGraph<String>,
    fixed: &[Pattern<String>],
    selection: &[EClassId],
    subst: &Subst,
    out: &mut Vec<Subst>,
) {
    let mut used = vec![false; selection.len()];
    recursive_pair_fixed_inner(graph, fixed, selection, &mut used, subst, out);
}

fn recursive_pair_fixed_inner(
    graph: &mut EGraph<String>,
    fixed: &[Pattern<String>],
    selection: &[EClassId],
    used: &mut [bool],
    subst: &Subst,
    out: &mut Vec<Subst>,
) {
    if fixed.is_empty() {
        out.push(subst.clone());
        return;
    }
    for index in 0..selection.len() {
        if used[index] {
            continue;
        }
        let mut child_matches = Vec::new();
        recursive_collect_matches(graph, &fixed[0], selection[index], subst, &mut child_matches);
        if child_matches.is_empty() {
            continue;
        }
        used[index] = true;
        for (_, child_subst) in child_matches {
            recursive_pair_fixed_inner(graph, &fixed[1..], selection, used, &child_subst, out);
        }
        used[index] = false;
    }
}

fn nonlinear_fixture() -> (EGraph<String>, EClassId) {
    let mut graph = EGraph::new();
    let channel = graph.add(ENode::leaf("N".to_string()));
    let send_body = graph.add(ENode::leaf("P".to_string()));
    let receive_body = graph.add(ENode::leaf("Q".to_string()));
    let residual = graph.add(ENode::leaf("R".to_string()));
    let open = graph.add(ENode::new("Open".to_string(), vec![channel, send_body]));
    let amb = graph.add(ENode::new("Amb".to_string(), vec![channel, receive_body]));
    let mut children = vec![open, amb, residual];
    children.sort_by_cached_key(|&child| graph.canonical_class_key(child));
    let root = graph.add(ENode::new("Par".to_string(), children));
    (graph, root)
}

#[test]
fn iterative_matcher_preserves_recursive_order_substitutions_and_materialization() {
    let pattern = Pattern::ac(
        "Par".to_string(),
        vec![
            Pattern::app("Open".to_string(), vec![Pattern::var("N"), Pattern::var("P")]),
            Pattern::app("Amb".to_string(), vec![Pattern::var("N"), Pattern::var("Q")]),
        ],
        Some("rest".to_string()),
    );
    let (mut actual_graph, actual_root) = nonlinear_fixture();
    let (mut expected_graph, expected_root) = nonlinear_fixture();
    let mut actual = Vec::new();
    let mut expected = Vec::new();
    actual_graph.collect_matches(&pattern, actual_root, &Subst::default(), &mut actual);
    recursive_collect_matches(
        &mut expected_graph,
        &pattern,
        expected_root,
        &Subst::default(),
        &mut expected,
    );

    assert_eq!(actual, expected);
    assert_eq!(actual_graph.node_count(), expected_graph.node_count());
    for ((actual_root, actual_subst), (expected_root, expected_subst)) in
        actual.iter().zip(&expected)
    {
        assert_eq!(
            actual_graph.canonical_class_key(*actual_root),
            expected_graph.canonical_class_key(*expected_root)
        );
        for name in ["N", "P", "Q", "rest"] {
            assert_eq!(
                actual_graph.canonical_class_key(actual_subst[name]),
                expected_graph.canonical_class_key(expected_subst[name])
            );
        }
    }
}

#[test]
fn positional_matcher_handles_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("dovetail-positional-matcher-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut graph = EGraph::new();
            let leaf = graph.add(ENode::leaf("X".to_string()));
            let mut root = leaf;
            let mut pattern = Pattern::var("x");
            for _ in 0..DEPTH {
                root = graph.add(ENode::new("N".to_string(), vec![root]));
                pattern = Pattern::app("N".to_string(), vec![pattern]);
            }
            let mut matches = Vec::new();
            graph.collect_matches(&pattern, root, &Subst::default(), &mut matches);
            assert_eq!(matches.len(), 1);
            assert_eq!(graph.find(matches[0].1["x"]), graph.find(leaf));
        })
        .expect("small-stack thread starts")
        .join()
        .expect("the positional matcher PDA does not overflow a 256 KiB stack");
}

#[test]
fn ac_pairing_handles_one_thousand_fixed_patterns_without_eager_permutations() {
    std::thread::Builder::new()
        .name("dovetail-ac-pairing-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const WIDTH: usize = 1_000;
            let mut graph = EGraph::new();
            let mut children = Vec::with_capacity(WIDTH);
            let mut fixed = Vec::with_capacity(WIDTH);
            for index in 0..WIDTH {
                let label = format!("L{index:04}");
                children.push(graph.add(ENode::leaf(label.clone())));
                fixed.push(Pattern::app(label, Vec::new()));
            }
            children.sort_by_cached_key(|&child| graph.canonical_class_key(child));
            let root = graph.add(ENode::new("Par".to_string(), children));
            let pattern = Pattern::ac("Par".to_string(), fixed, None);
            let mut matches = Vec::new();
            graph.collect_matches(&pattern, root, &Subst::default(), &mut matches);
            assert_eq!(matches.len(), 1);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("the AC pairing PDA does not overflow a 256 KiB stack");
}
