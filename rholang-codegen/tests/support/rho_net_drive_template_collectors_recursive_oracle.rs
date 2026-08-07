use super::*;

fn bag_vars_recursive(
    template: &AcReconstructTemplate,
    at_bag_element: bool,
    depth: usize,
    out: &mut Vec<(String, usize)>,
) {
    match template {
        AcReconstructTemplate::Var(name) => {
            if at_bag_element && !out.iter().any(|(seen, d)| seen == name && *d == depth) {
                out.push((name.clone(), depth));
            }
        },
        AcReconstructTemplate::Node { children, .. } => {
            for child in children {
                bag_vars_recursive(child, false, depth, out);
            }
        },
        AcReconstructTemplate::Bag { elements, .. } => {
            for element in elements {
                bag_vars_recursive(element, true, depth, out);
            }
        },
        AcReconstructTemplate::Binder { body } => {
            bag_vars_recursive(body, false, depth + 1, out);
        },
    }
}

fn shifts_recursive(
    template: &AcReconstructTemplate,
    depth: usize,
    out: &mut Vec<(String, usize)>,
) {
    let push = |name: &str, depth: usize, out: &mut Vec<(String, usize)>| {
        if depth >= 1 && !out.iter().any(|(seen, d)| seen == name && *d == depth) {
            out.push((name.to_owned(), depth));
        }
    };
    match template {
        AcReconstructTemplate::Var(name) => push(name, depth, out),
        AcReconstructTemplate::Node { children, .. } => {
            for child in children {
                shifts_recursive(child, depth, out);
            }
        },
        AcReconstructTemplate::Bag { elements, rest, .. } => {
            for element in elements {
                shifts_recursive(element, depth, out);
            }
            if let Some(rest) = rest {
                push(rest, depth, out);
            }
        },
        AcReconstructTemplate::Binder { body } => shifts_recursive(body, depth + 1, out),
    }
}

fn corpus() -> AcReconstructTemplate {
    AcReconstructTemplate::Bag {
        op: "PPar".to_owned(),
        elements: vec![
            AcReconstructTemplate::Var("x".to_owned()),
            AcReconstructTemplate::Node {
                constructor: "C".to_owned(),
                children: vec![AcReconstructTemplate::Var("node-child".to_owned())],
            },
            AcReconstructTemplate::Binder {
                body: Box::new(AcReconstructTemplate::Bag {
                    op: "PPar".to_owned(),
                    elements: vec![
                        AcReconstructTemplate::Var("z".to_owned()),
                        AcReconstructTemplate::Var("x".to_owned()),
                    ],
                    rest: Some("inner-rest".to_owned()),
                }),
            },
        ],
        rest: Some("outer-rest".to_owned()),
    }
}

#[test]
fn template_collectors_match_recursive_order_and_depth() {
    let template = corpus();
    let mut actual_bag = vec![("seed".to_owned(), 9)];
    let mut expected_bag = actual_bag.clone();
    collect_bag_element_vars(&template, true, 2, &mut actual_bag);
    bag_vars_recursive(&template, true, 2, &mut expected_bag);
    assert_eq!(actual_bag, expected_bag);

    let mut actual_shifts = vec![("seed".to_owned(), 9)];
    let mut expected_shifts = actual_shifts.clone();
    collect_shift_requirements(&template, 2, &mut actual_shifts);
    shifts_recursive(&template, 2, &mut expected_shifts);
    assert_eq!(actual_shifts, expected_shifts);
}

#[test]
fn template_collectors_are_stack_safe_at_twenty_thousand_binders() {
    std::thread::Builder::new()
        .name("template-collector-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut template = AcReconstructTemplate::Bag {
                op: "PPar".to_owned(),
                elements: vec![AcReconstructTemplate::Var("x".to_owned())],
                rest: Some("tail".to_owned()),
            };
            for _ in 0..20_000 {
                template = AcReconstructTemplate::Binder { body: Box::new(template) };
            }
            let mut bag_vars = Vec::new();
            collect_bag_element_vars(&template, true, 0, &mut bag_vars);
            assert_eq!(bag_vars, [("x".to_owned(), 20_000)]);

            let mut shifts = Vec::new();
            collect_shift_requirements(&template, 0, &mut shifts);
            assert_eq!(shifts, [("x".to_owned(), 20_000), ("tail".to_owned(), 20_000)]);
        })
        .expect("spawn template-collector stack-gate thread")
        .join()
        .expect("template collector overflowed or panicked");
}
