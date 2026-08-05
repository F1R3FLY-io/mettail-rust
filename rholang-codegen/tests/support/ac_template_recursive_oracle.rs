use super::*;

const BINDER_FRAGMENT: &str = r#"
    name: BinderTemplate,
    types {
        Proc
        Name
    }
    terms {
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
    }
"#;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
}

fn recursive_from_pattern(pattern: &Pattern, def: &LanguageDef) -> Option<AcReconstructTemplate> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => Some(AcReconstructTemplate::Var(name.to_string())),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { coll_type, elements, rest }] = args.as_slice() {
                if !matches!(coll_type, None | Some(CollectionType::HashBag)) {
                    return None;
                }
                let mut templates = Vec::with_capacity(elements.len());
                for element in elements {
                    templates.push(recursive_from_pattern(element, def)?);
                }
                Some(AcReconstructTemplate::Bag {
                    op: constructor.to_string(),
                    elements: templates,
                    rest: rest.as_ref().map(ToString::to_string),
                })
            } else if let [Pattern::Term(PatternTerm::Lambda { body, .. })] = args.as_slice() {
                let label = constructor.to_string();
                let is_single_binder = def.terms.iter().any(|term| {
                    term.label == label
                        && crate::rho_net_subst_trs::is_binder_term(term)
                        && !term.term_context.as_ref().is_some_and(|params| {
                            params
                                .iter()
                                .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
                        })
                });
                is_single_binder.then(|| {
                    recursive_from_pattern(body, def)
                        .map(|body| AcReconstructTemplate::Binder { body: Box::new(body) })
                })?
            } else {
                let mut children = Vec::with_capacity(args.len());
                for arg in args {
                    children.push(recursive_from_pattern(arg, def)?);
                }
                Some(AcReconstructTemplate::Node {
                    constructor: constructor.to_string(),
                    children,
                })
            }
        },
        _ => None,
    }
}

fn recursive_clone(template: &AcReconstructTemplate) -> AcReconstructTemplate {
    match template {
        AcReconstructTemplate::Var(name) => AcReconstructTemplate::Var(name.clone()),
        AcReconstructTemplate::Node { constructor, children } => AcReconstructTemplate::Node {
            constructor: constructor.clone(),
            children: children.iter().map(recursive_clone).collect(),
        },
        AcReconstructTemplate::Bag { op, elements, rest } => AcReconstructTemplate::Bag {
            op: op.clone(),
            elements: elements.iter().map(recursive_clone).collect(),
            rest: rest.clone(),
        },
        AcReconstructTemplate::Binder { body } => {
            AcReconstructTemplate::Binder { body: Box::new(recursive_clone(body)) }
        },
    }
}

fn recursive_debug(template: &AcReconstructTemplate) -> String {
    match template {
        AcReconstructTemplate::Var(name) => format!("Var({name:?})"),
        AcReconstructTemplate::Node { constructor, children } => format!(
            "Node {{ constructor: {constructor:?}, children: [{}] }}",
            children
                .iter()
                .map(recursive_debug)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        AcReconstructTemplate::Bag { op, elements, rest } => format!(
            "Bag {{ op: {op:?}, elements: [{}], rest: {rest:?} }}",
            elements
                .iter()
                .map(recursive_debug)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        AcReconstructTemplate::Binder { body } => {
            format!("Binder {{ body: {} }}", recursive_debug(body))
        },
    }
}

fn recursive_eq(left: &AcReconstructTemplate, right: &AcReconstructTemplate) -> bool {
    match (left, right) {
        (AcReconstructTemplate::Var(left), AcReconstructTemplate::Var(right)) => left == right,
        (
            AcReconstructTemplate::Node {
                constructor: left_constructor,
                children: left_children,
            },
            AcReconstructTemplate::Node {
                constructor: right_constructor,
                children: right_children,
            },
        ) => {
            left_constructor == right_constructor
                && left_children.len() == right_children.len()
                && left_children
                    .iter()
                    .zip(right_children)
                    .all(|(left, right)| recursive_eq(left, right))
        },
        (
            AcReconstructTemplate::Bag {
                op: left_op,
                elements: left_elements,
                rest: left_rest,
            },
            AcReconstructTemplate::Bag {
                op: right_op,
                elements: right_elements,
                rest: right_rest,
            },
        ) => {
            left_op == right_op
                && left_rest == right_rest
                && left_elements.len() == right_elements.len()
                && left_elements
                    .iter()
                    .zip(right_elements)
                    .all(|(left, right)| recursive_eq(left, right))
        },
        (
            AcReconstructTemplate::Binder { body: left },
            AcReconstructTemplate::Binder { body: right },
        ) => recursive_eq(left, right),
        _ => false,
    }
}

fn recursive_collect_vars(template: &AcReconstructTemplate, out: &mut HashSet<String>) {
    match template {
        AcReconstructTemplate::Var(name) => {
            out.insert(name.clone());
        },
        AcReconstructTemplate::Node { children, .. } => {
            for child in children {
                recursive_collect_vars(child, out);
            }
        },
        AcReconstructTemplate::Bag { elements, rest, .. } => {
            for element in elements {
                recursive_collect_vars(element, out);
            }
            if let Some(rest) = rest {
                out.insert(rest.clone());
            }
        },
        AcReconstructTemplate::Binder { body } => recursive_collect_vars(body, out),
    }
}

fn recursive_contains_binder(template: &AcReconstructTemplate) -> bool {
    match template {
        AcReconstructTemplate::Var(_) => false,
        AcReconstructTemplate::Node { children, .. } => {
            children.iter().any(recursive_contains_binder)
        },
        AcReconstructTemplate::Bag { elements, .. } => {
            elements.iter().any(recursive_contains_binder)
        },
        AcReconstructTemplate::Binder { .. } => true,
    }
}

fn recursive_count(template: &AcReconstructTemplate, name: &str) -> usize {
    match template {
        AcReconstructTemplate::Var(var) => usize::from(var == name),
        AcReconstructTemplate::Node { children, .. } => children
            .iter()
            .map(|child| recursive_count(child, name))
            .sum(),
        AcReconstructTemplate::Bag { elements, rest, .. } => {
            usize::from(rest.as_deref() == Some(name))
                + elements
                    .iter()
                    .map(|element| recursive_count(element, name))
                    .sum::<usize>()
        },
        AcReconstructTemplate::Binder { body } => recursive_count(body, name),
    }
}

fn recursive_shift(term: &GroundTerm, cutoff: usize) -> Option<GroundTerm> {
    if let Some(kind) = &term.coll_type {
        if *kind != CollectionType::HashBag {
            return None;
        }
        let children = term
            .children
            .iter()
            .map(|child| recursive_shift(child, cutoff))
            .collect::<Option<Vec<_>>>()?;
        return Some(GroundTerm::collection(
            CollectionType::HashBag,
            term.constructor.clone(),
            children,
        ));
    }
    match term.constructor.as_str() {
        BOUND_VAR_REFLECT_LABEL => {
            let [numeral] = term.children.as_slice() else {
                return None;
            };
            let n = decode_peano_ground(numeral)?;
            Some(if n >= cutoff {
                GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(n + 1)])
            } else {
                term.clone()
            })
        },
        LAMBDA_REFLECT_LABEL => {
            let [body] = term.children.as_slice() else {
                return None;
            };
            Some(GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![recursive_shift(body, cutoff + 1)?]))
        },
        FREE_VAR_REFLECT_LABEL => Some(term.clone()),
        MULTILAMBDA_REFLECT_LABEL
        | SUBST_RESERVED_LABEL
        | SHIFT_RESERVED_LABEL
        | SHIFTK_RESERVED_LABEL
        | CMP_RESERVED_LABEL
        | PRED_RESERVED_LABEL
        | PEANO_ZERO_REFLECT_LABEL
        | PEANO_SUCC_REFLECT_LABEL => None,
        _ => Some(GroundTerm::new(
            term.constructor.clone(),
            term.children
                .iter()
                .map(|child| recursive_shift(child, cutoff))
                .collect::<Option<Vec<_>>>()?,
        )),
    }
}

fn recursive_shift_by(term: &GroundTerm, cutoff: usize, amount: usize) -> Option<GroundTerm> {
    let mut value = term.clone();
    for _ in 0..amount {
        value = recursive_shift(&value, cutoff)?;
    }
    Some(value)
}

fn recursive_instantiate(
    template: &AcReconstructTemplate,
    find_sigma: &impl Fn(&str) -> Option<GroundTerm>,
    binder_depth: usize,
) -> Option<GroundTerm> {
    let shifted = |name: &str| {
        let value = find_sigma(name)?;
        recursive_shift_by(&value, 0, binder_depth)
    };
    match template {
        AcReconstructTemplate::Var(name) => shifted(name),
        AcReconstructTemplate::Node { constructor, children } => Some(GroundTerm::new(
            constructor.clone(),
            children
                .iter()
                .map(|child| recursive_instantiate(child, find_sigma, binder_depth))
                .collect::<Option<Vec<_>>>()?,
        )),
        AcReconstructTemplate::Bag { op, elements, rest } => {
            let mut children = elements
                .iter()
                .map(|element| recursive_instantiate(element, find_sigma, binder_depth))
                .collect::<Option<Vec<_>>>()?;
            if let Some(rest) = rest {
                children.extend(shifted(rest)?.children.iter().cloned());
            }
            Some(GroundTerm::collection(CollectionType::HashBag, op.clone(), children))
        },
        AcReconstructTemplate::Binder { body } => Some(GroundTerm::new(
            LAMBDA_REFLECT_LABEL,
            vec![recursive_instantiate(body, find_sigma, binder_depth + 1)?],
        )),
    }
}

fn branching_template() -> AcReconstructTemplate {
    AcReconstructTemplate::Node {
        constructor: "Root".to_owned(),
        children: vec![
            AcReconstructTemplate::Bag {
                op: "PPar".to_owned(),
                elements: vec![
                    AcReconstructTemplate::Var("x".to_owned()),
                    AcReconstructTemplate::Binder {
                        body: Box::new(AcReconstructTemplate::Var("y".to_owned())),
                    },
                ],
                rest: Some("rest".to_owned()),
            },
            AcReconstructTemplate::Var("x".to_owned()),
        ],
    }
}

#[test]
fn ac_template_pdas_match_recursive_oracles() {
    let def = syn::parse_str::<LanguageDef>(BINDER_FRAGMENT).expect("binder fragment must parse");
    let patterns = [
        apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![variable("x"), apply("Leaf", Vec::new())],
                rest: Some(ident("rest")),
            }],
        ),
        apply(
            "PNew",
            vec![Pattern::Term(PatternTerm::Lambda {
                binder: ident("x"),
                body: Box::new(variable("body")),
            })],
        ),
        apply("Node", vec![variable("x"), apply("Leaf", Vec::new())]),
    ];
    for pattern in &patterns {
        assert_eq!(
            AcReconstructTemplate::from_pattern(pattern, &def),
            recursive_from_pattern(pattern, &def)
        );
    }

    let template = branching_template();
    let clone = template.clone();
    let oracle_clone = recursive_clone(&template);
    assert!(recursive_eq(&clone, &oracle_clone));
    assert_eq!(clone, oracle_clone);
    assert_eq!(format!("{template:?}"), recursive_debug(&template));

    let mut actual_vars = HashSet::new();
    let mut expected_vars = HashSet::new();
    template.collect_vars(&mut actual_vars);
    recursive_collect_vars(&template, &mut expected_vars);
    assert_eq!(actual_vars, expected_vars);
    assert_eq!(template.contains_binder(), recursive_contains_binder(&template));
    for name in ["x", "y", "rest", "missing"] {
        assert_eq!(
            count_template_name_occurrences(&template, name),
            recursive_count(&template, name)
        );
    }

    let sigma = |name: &str| match name {
        "x" => Some(GroundTerm::new(
            "Pair",
            vec![GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(0)])],
        )),
        "y" => Some(GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(1)])),
        "rest" => Some(GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("Residual")],
        )),
        _ => None,
    };
    assert_eq!(
        instantiate_ac_reconstruct_template(&template, &sigma),
        recursive_instantiate(&template, &sigma, 0)
    );

    let ground = GroundTerm::new(
        "Root",
        vec![
            GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(2)]),
            GroundTerm::new(
                LAMBDA_REFLECT_LABEL,
                vec![GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(0)])],
            ),
        ],
    );
    for amount in 1..8 {
        assert_eq!(
            shift_reflected_ground_term_by(&ground, 0, amount),
            recursive_shift_by(&ground, 0, amount)
        );
    }
}

#[test]
fn deep_ac_template_lifecycle_and_instantiation_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("ac-template-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = variable("x");
            for _ in 0..DEPTH {
                pattern = apply("Node", vec![pattern]);
            }
            let def =
                syn::parse_str::<LanguageDef>(BINDER_FRAGMENT).expect("binder fragment must parse");
            let template = AcReconstructTemplate::from_pattern(&pattern, &def)
                .expect("deep node pattern must be representable");
            let clone = template.clone();
            assert_eq!(template, clone);
            assert_eq!(
                format!("{template:?}")
                    .matches("Node { constructor")
                    .count(),
                DEPTH
            );
            let mut vars = HashSet::new();
            template.collect_vars(&mut vars);
            assert_eq!(vars, HashSet::from(["x".to_owned()]));
            assert!(!template.contains_binder());
            assert_eq!(count_template_name_occurrences(&template, "x"), 1);
            let ground = instantiate_ac_reconstruct_template(&template, &|name| {
                (name == "x").then(|| GroundTerm::nullary("Leaf"))
            })
            .expect("deep template must instantiate");
            assert_eq!(ground.constructor, "Node");
            drop(ground);
            drop(clone);
            drop(template);
            drop(pattern);

            let mut binders = AcReconstructTemplate::Var("x".to_owned());
            for _ in 0..DEPTH {
                binders = AcReconstructTemplate::Binder { body: Box::new(binders) };
            }
            assert!(binders.contains_binder());
            let shifted = instantiate_ac_reconstruct_template(&binders, &|name| {
                (name == "x")
                    .then(|| GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![encode_peano_ground(0)]))
            })
            .expect("deep binder template must shift and instantiate");
            drop(shifted);
            drop(binders);
        })
        .expect("small-stack AC template thread must spawn");
    handle
        .join()
        .expect("AC template PDAs must not overflow the native stack");
}
