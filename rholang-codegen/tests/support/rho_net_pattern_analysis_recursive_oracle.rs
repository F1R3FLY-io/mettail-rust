use super::*;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn recursive_contextual_source_path(
    pattern: &Pattern,
    source: &str,
) -> Option<Vec<(String, usize)>> {
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) if id == source => Some(Vec::new()),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            for (index, arg) in args.iter().enumerate() {
                if let Some(mut suffix) = recursive_contextual_source_path(arg, source) {
                    let mut path = Vec::with_capacity(suffix.len() + 1);
                    path.push((constructor.to_string(), index));
                    path.append(&mut suffix);
                    return Some(path);
                }
            }
            None
        },
        _ => None,
    }
}

fn recursive_collect_pattern_var_counts(pattern: &Pattern, counts: &mut HashMap<String, usize>) {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            *counts.entry(name.to_string()).or_insert(0) += 1;
        },
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            for arg in args {
                recursive_collect_pattern_var_counts(arg, counts);
            }
        },
        Pattern::Collection { elements, .. } => {
            for element in elements {
                recursive_collect_pattern_var_counts(element, counts);
            }
        },
        _ => {},
    }
}

fn recursive_collect_pattern_lhs_vars(pattern: &Pattern, out: &mut HashSet<String>) {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            out.insert(name.to_string());
        },
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            for arg in args {
                recursive_collect_pattern_lhs_vars(arg, out);
            }
        },
        Pattern::Collection { elements, rest, .. } => {
            for element in elements {
                recursive_collect_pattern_lhs_vars(element, out);
            }
            if let Some(rest) = rest {
                out.insert(rest.to_string());
            }
        },
        _ => {},
    }
}

fn recursive_find_var_ident(pattern: &Pattern, name: &str) -> Option<Ident> {
    match pattern {
        Pattern::Term(PatternTerm::Var(ident)) => (ident == name).then(|| ident.clone()),
        Pattern::Term(PatternTerm::Apply { args, .. }) => args
            .iter()
            .find_map(|arg| recursive_find_var_ident(arg, name)),
        Pattern::Collection { elements, .. } => elements
            .iter()
            .find_map(|element| recursive_find_var_ident(element, name)),
        _ => None,
    }
}

fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn deep_apply(depth: usize, mut leaf: Pattern) -> Pattern {
    for _ in 0..depth {
        leaf = apply("Node", vec![leaf]);
    }
    leaf
}

#[test]
fn iterative_pattern_analyses_match_recursive_oracles() {
    let pattern = apply(
        "Root",
        vec![
            apply("Left", vec![variable("x"), variable("y")]),
            Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![variable("x"), apply("Right", vec![variable("z")])],
                rest: Some(ident("rest")),
            },
            apply("Later", vec![variable("x")]),
        ],
    );

    for name in ["x", "y", "z", "missing"] {
        assert_eq!(
            contextual_source_path(&pattern, name),
            recursive_contextual_source_path(&pattern, name)
        );
        assert_eq!(
            find_var_ident(&pattern, name).map(|id| id.to_string()),
            recursive_find_var_ident(&pattern, name).map(|id| id.to_string())
        );
    }

    let mut actual_counts = HashMap::new();
    let mut expected_counts = HashMap::new();
    collect_pattern_var_counts(&pattern, &mut actual_counts);
    recursive_collect_pattern_var_counts(&pattern, &mut expected_counts);
    assert_eq!(actual_counts, expected_counts);

    let mut actual_vars = HashSet::new();
    let mut expected_vars = HashSet::new();
    collect_pattern_lhs_vars(&pattern, &mut actual_vars);
    recursive_collect_pattern_lhs_vars(&pattern, &mut expected_vars);
    assert_eq!(actual_vars, expected_vars);
}

#[test]
fn deep_pattern_analyses_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("rho-net-pattern-analysis-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let pattern = deep_apply(DEPTH, variable("needle"));
            assert_eq!(contextual_source_path(&pattern, "needle").unwrap().len(), DEPTH);
            let mut counts = HashMap::new();
            collect_pattern_var_counts(&pattern, &mut counts);
            assert_eq!(counts.get("needle"), Some(&1));
            let mut vars = HashSet::new();
            collect_pattern_lhs_vars(&pattern, &mut vars);
            assert_eq!(vars, HashSet::from(["needle".to_owned()]));
            assert_eq!(find_var_ident(&pattern, "needle").unwrap(), "needle");
            drop(pattern);
        })
        .expect("small-stack RhoNet pattern analysis thread must spawn");
    handle
        .join()
        .expect("RhoNet pattern analysis PDAs must not overflow the native stack");
}
