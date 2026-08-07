use super::*;

fn shift_recursive(
    fingerprint: &str,
    env: &Env,
    value_name: &str,
    dest_name: &str,
    k: usize,
) -> Node {
    let zero = || ground(nullary_term(fingerprint, crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL));
    if k == 1 {
        return send(
            ground(tag_par(fingerprint, crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
            vec![zero(), env.var(value_name), env.var(dest_name)],
        );
    }
    new_scope(1, {
        let env = env.push(&["__t"]);
        let first = send(
            ground(tag_par(fingerprint, crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
            vec![zero(), env.var(value_name), env.var("__t")],
        );
        let rest = for1(env.var("__t"), {
            let env = env.push(&["__w"]);
            shift_recursive(fingerprint, &env, "__w", dest_name, k - 1)
        });
        par2(first, rest)
    })
}

fn rebuild_recursive(
    template: &AcReconstructTemplate,
    env: &Env,
    fingerprint: &str,
    depth: usize,
) -> Node {
    match template {
        AcReconstructTemplate::Var(name) => env.var(&slot_value_name(name, depth)),
        AcReconstructTemplate::Node { constructor, children } => tagged(
            fingerprint,
            constructor,
            children
                .iter()
                .map(|child| rebuild_recursive(child, env, fingerprint, depth))
                .collect(),
        ),
        AcReconstructTemplate::Binder { body } => tagged(
            fingerprint,
            LAMBDA_REFLECT_LABEL,
            vec![rebuild_recursive(body, env, fingerprint, depth + 1)],
        ),
        AcReconstructTemplate::Bag { op, elements, rest } => {
            let mut soup = Vec::with_capacity(elements.len() + usize::from(rest.is_some()));
            for element in elements {
                soup.push(match element {
                    AcReconstructTemplate::Var(name) => env.var(&fragment_value_name(name, depth)),
                    AcReconstructTemplate::Node { .. } | AcReconstructTemplate::Binder { .. } => {
                        wrap_element_send(
                            fingerprint,
                            op,
                            rebuild_recursive(element, env, fingerprint, depth),
                        )
                    },
                    AcReconstructTemplate::Bag { op: inner_op, .. } => {
                        let rebuilt = rebuild_recursive(element, env, fingerprint, depth);
                        if inner_op == op {
                            rebuilt
                        } else {
                            wrap_element_send(fingerprint, op, rebuilt)
                        }
                    },
                });
            }
            if let Some(rest) = rest {
                soup.push(env.var(&slot_value_name(rest, depth)));
            }
            parallel(soup)
        },
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
            AcReconstructTemplate::Bag {
                op: "PPar".to_owned(),
                elements: vec![AcReconstructTemplate::Var("same".to_owned())],
                rest: None,
            },
            AcReconstructTemplate::Bag {
                op: "Other".to_owned(),
                elements: vec![AcReconstructTemplate::Var("other".to_owned())],
                rest: None,
            },
            AcReconstructTemplate::Binder {
                body: Box::new(AcReconstructTemplate::Node {
                    constructor: "D".to_owned(),
                    children: vec![AcReconstructTemplate::Var("under".to_owned())],
                }),
            },
        ],
        rest: Some("tail".to_owned()),
    }
}

#[test]
fn iterative_shift_and_template_rebuild_match_recursive_bytes() {
    use prost::Message;

    let shift_env = Env::root(&["value", "dest"]);
    for depth in 1..=8 {
        let actual = chained_shift_node("shift-oracle", &shift_env, "value", "dest", depth);
        let expected = shift_recursive("shift-oracle", &shift_env, "value", "dest", depth);
        assert_eq!(actual.free, expected.free);
        assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
    }

    let template = corpus();
    let rebuild_env = Env::root(&[
        "__frag_x",
        "node-child",
        "__frag_same",
        "__frag_other",
        "__sh1_under",
        "tail",
    ]);
    let actual = rebuild_template_node(&template, &rebuild_env, "template-oracle", 0);
    let expected = rebuild_recursive(&template, &rebuild_env, "template-oracle", 0);
    assert_eq!(actual.free, expected.free);
    assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
}

#[test]
fn shift_builder_does_not_shadow_a_sigma_slot_named_like_its_private_frame() {
    use prost::Message;

    let env = Env::root(&["__t", "dest"]);
    let actual = chained_shift_node("shift-shadow", &env, "__t", "dest", 2);
    let expected = new_scope(
        1,
        par2(
            send(
                ground(tag_par("shift-shadow", crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
                vec![
                    ground(nullary_term(
                        "shift-shadow",
                        crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL,
                    )),
                    bv(2),
                    bv(0),
                ],
            ),
            for1(
                bv(0),
                send(
                    ground(tag_par("shift-shadow", crate::rho_net_lower::SHIFT_RESERVED_LABEL)),
                    vec![
                        ground(nullary_term(
                            "shift-shadow",
                            crate::rho_net_lower::PEANO_ZERO_REFLECT_LABEL,
                        )),
                        bv(0),
                        bv(2),
                    ],
                ),
            ),
        ),
    );
    assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
}

#[test]
fn shift_and_template_rebuild_are_stack_safe_at_twenty_thousand_levels() {
    std::thread::Builder::new()
        .name("template-rebuild-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;

            let shift_env = Env::root(&["value", "dest"]);
            let shift = chained_shift_node("deep-shift", &shift_env, "value", "dest", DEPTH);
            assert_eq!(shift.free, [0, 1]);
            drop(shift);

            let mut template = AcReconstructTemplate::Var("x".to_owned());
            for _ in 0..DEPTH {
                template = AcReconstructTemplate::Binder { body: Box::new(template) };
            }
            let shifted = slot_value_name("x", DEPTH);
            let env = Env::root(&[&shifted]);
            let rebuilt = rebuild_template_node(&template, &env, "deep-template", 0);
            assert_eq!(rebuilt.free, [0]);
        })
        .expect("spawn template rebuild stack-gate thread")
        .join()
        .expect("shift or template rebuild overflowed or panicked");
}
