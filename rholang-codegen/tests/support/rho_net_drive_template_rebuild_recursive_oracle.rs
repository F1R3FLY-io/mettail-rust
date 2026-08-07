use super::*;

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
fn iterative_template_rebuild_matches_recursive_bytes() {
    use prost::Message;

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
fn shift_builder_is_one_constant_size_call_in_the_caller_frame() {
    use prost::Message;

    let env = Env::root(&["value", "dest"]);
    let shallow = chained_shift_node("shift-compact", &env, "value", "dest", 1);
    let deep = chained_shift_node("shift-compact", &env, "value", "dest", 20_000);
    assert_eq!(shallow.free, [0, 1]);
    assert_eq!(deep.free, [0, 1]);
    assert_eq!(shallow.par.sends.len(), 1);
    assert_eq!(deep.par.sends.len(), 1);
    assert!(shallow.par.news.is_empty() && shallow.par.receives.is_empty());
    assert!(deep.par.news.is_empty() && deep.par.receives.is_empty());
    let shallow_send = &shallow.par.sends[0];
    let deep_send = &deep.par.sends[0];
    assert_eq!(
        shallow_send.chan.as_ref(),
        Some(&crate::native_shift::native_shift_channel("shift-compact"))
    );
    assert_eq!(deep_send.chan, shallow_send.chan);
    assert_eq!(crate::native_shift::decode_native_shift_amount(&shallow_send.data[0]), Ok(1));
    assert_eq!(crate::native_shift::decode_native_shift_amount(&deep_send.data[0]), Ok(20_000));
    assert_eq!(
        shallow.par.encode_to_vec().len(),
        deep.par.encode_to_vec().len(),
        "binder depth changes only the fixed-width amount bytes"
    );
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
            assert_eq!(shift.par.sends.len(), 1);
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
