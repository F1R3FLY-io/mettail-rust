use super::*;

const LIMITS: ConstructionLimits = ConstructionLimits {
    nodes: 50_000,
    edges: 100_000,
    payload_bytes: 1_000_000,
    work: 200_000,
};

#[test]
fn append_fold_checks_empty_seed_and_stops_at_first_failed_append() {
    use crate::construction::append_fold;
    with_neutral_target(
        ConstructionLimits { nodes: 0, ..LIMITS },
        || false,
        |mut target| {
            assert_eq!(
                append_fold(&mut target, []),
                Err(ConstructionError::LimitExceeded(LimitKind::Nodes))
            );
            assert_eq!(target.usage().nodes, 0);
        },
    );
    with_neutral_target(
        ConstructionLimits { nodes: 2, ..LIMITS },
        || false,
        |mut target| {
            let leaf = target.construct(ValueOp::Empty, vec![]).expect("leaf");
            let pulled = std::cell::Cell::new(0);
            let children = [leaf, leaf, leaf]
                .into_iter()
                .inspect(|_| pulled.set(pulled.get() + 1));
            assert_eq!(
                append_fold(&mut target, children),
                Err(ConstructionError::LimitExceeded(LimitKind::Nodes))
            );
            assert_eq!(pulled.get(), 1, "no subsequent child processed after failure");
            assert_eq!(target.usage().nodes, 2, "seed retained, failed append not inserted");
        },
    );
}

#[test]
fn primitive_values_have_exact_owned_payloads_and_observations() {
    let graph = with_neutral_target(
        LIMITS,
        || false,
        |mut target| {
            let empty = target.construct(ValueOp::Empty, vec![]).expect("empty");
            let low = target
                .construct(ValueOp::Integer(i64::MIN), vec![])
                .expect("minimum");
            let high = target
                .construct(ValueOp::Integer(i64::MAX), vec![])
                .expect("maximum");
            let boolean = target
                .construct(ValueOp::Boolean(true), vec![])
                .expect("Boolean");
            let text = target
                .construct(ValueOp::Text("a\0é\\n".into()), vec![])
                .expect("decoded text");
            for value in [empty, low, high, boolean] {
                assert_eq!(
                    target.observe(&value),
                    Ok(StructuralObservation {
                        single_string: false,
                        locally_free: &[],
                        connective_used: false,
                    })
                );
            }
            assert!(
                target
                    .observe(&text)
                    .expect("text observation")
                    .single_string
            );
            target.finish_graph(text).expect("owned graph")
        },
    );
    assert_eq!(graph.node_count(), 5);
    assert_eq!(graph.node(1).expect("minimum").operation, &ValueOp::Integer(i64::MIN));
    assert_eq!(graph.node(2).expect("maximum").operation, &ValueOp::Integer(i64::MAX));
    assert_eq!(
        graph.node(graph.root()).expect("root").operation,
        &ValueOp::Text("a\0é\\n".into())
    );
    assert!(graph.node(99).is_none());
}

#[test]
fn append_observes_constructed_heads_and_retains_order_and_repetition() {
    let graph = with_neutral_target(
        LIMITS,
        || false,
        |mut target| {
            let nil = target.construct(ValueOp::Empty, vec![]).expect("nil");
            let text = target
                .construct(ValueOp::Text("text".into()), vec![])
                .expect("text");
            let left = target.append(nil, text).expect("empty then text");
            let right = target.append(text, nil).expect("text then empty");
            assert!(target.observe(&left).expect("left").single_string);
            assert!(target.observe(&right).expect("right").single_string);
            let double = target.append(text, text).expect("repeated reference");
            assert!(!target.observe(&double).expect("two heads").single_string);
            target.finish_graph(double).expect("finish")
        },
    );
    assert_eq!(graph.node(2).expect("left").children, &[0, 1]);
    assert_eq!(graph.node(3).expect("right").children, &[1, 0]);
    assert_eq!(graph.node(4).expect("double").children, &[1, 1]);
}

#[test]
fn identity_forwarding_checks_without_allocating_a_node() {
    with_neutral_target(
        LIMITS,
        || false,
        |mut target| {
            let value = target
                .construct(ValueOp::Text("value".into()), vec![])
                .expect("value");
            let before = target.usage();
            assert_eq!(target.forward(value), Ok(value));
            assert_eq!(target.usage().nodes, before.nodes);
            assert_eq!(target.usage().edges, before.edges);
            assert_eq!(target.usage().work, before.work + 1);
            let observed = target.observe(&value).expect("borrowed observation");
            assert!(observed.single_string);
            // The observation borrows the target, not its longer phantom brand.
            target
                .construct(ValueOp::Empty, vec![])
                .expect("borrow has ended");
        },
    );
}

#[test]
fn invalid_references_precede_arity_and_do_not_mutate_graph() {
    with_neutral_target(
        LIMITS,
        || false,
        |mut target| {
            let value = target.construct(ValueOp::Empty, vec![]).expect("initial");
            // Internal malformed-state witnesses; public callers cannot forge refs.
            let missing = ValueRef { index: 9, brand: PhantomData };
            let later = ValueRef { index: 8, brand: PhantomData };
            let before = target.usage();
            assert_eq!(
                target.construct(ValueOp::Empty, vec![value, missing, later]),
                Err(ConstructionError::MissingReference { index: 9 })
            );
            assert_eq!(
                target.construct(ValueOp::Append, vec![value]),
                Err(ConstructionError::ChildArity { expected: 2, actual: 1 })
            );
            assert_eq!(
                target.forward(missing),
                Err(ConstructionError::MissingReference { index: 9 })
            );
            assert_eq!(
                target.observe(&missing),
                Err(ConstructionError::MissingReference { index: 9 })
            );
            assert_eq!(target.usage().nodes, before.nodes);
            assert_eq!(target.usage().edges, before.edges);
            assert_eq!(target.usage().payload_bytes, before.payload_bytes);
            assert!(target.usage().work > before.work);
            assert_eq!(target.forward(value), Ok(value));
        },
    );
}

#[test]
fn every_size_limit_rejects_before_graph_growth() {
    for (limits, kind) in [
        (ConstructionLimits { nodes: 0, ..LIMITS }, LimitKind::Nodes),
        (ConstructionLimits { payload_bytes: 0, ..LIMITS }, LimitKind::PayloadBytes),
        (ConstructionLimits { work: 0, ..LIMITS }, LimitKind::Work),
    ] {
        with_neutral_target(
            limits,
            || false,
            |mut target| {
                assert_eq!(
                    target.construct(ValueOp::Text("x".into()), vec![]),
                    Err(ConstructionError::LimitExceeded(kind))
                );
                assert_eq!(target.usage().nodes, 0);
            },
        );
    }
    with_neutral_target(
        ConstructionLimits { edges: 1, ..LIMITS },
        || false,
        |mut target| {
            let value = target.construct(ValueOp::Empty, vec![]).expect("leaf");
            assert_eq!(
                target.append(value, value),
                Err(ConstructionError::LimitExceeded(LimitKind::Edges))
            );
            assert_eq!(target.usage().nodes, 1);
            assert_eq!(target.usage().edges, 0);
        },
    );
    assert_eq!(
        bounded_add(usize::MAX, 1, usize::MAX, LimitKind::Nodes),
        Err(ConstructionError::LimitExceeded(LimitKind::Nodes))
    );
}

#[test]
fn payload_limit_counts_utf8_bytes_and_cumulative_retained_values() {
    with_neutral_target(
        ConstructionLimits { payload_bytes: 3, ..LIMITS },
        || false,
        |mut target| {
            target
                .construct(ValueOp::Text("é".into()), vec![])
                .expect("two bytes");
            assert_eq!(target.usage().payload_bytes, 2);
            assert_eq!(
                target.construct(ValueOp::Text("é".into()), vec![]),
                Err(ConstructionError::LimitExceeded(LimitKind::PayloadBytes))
            );
            target
                .construct(ValueOp::Text("x".into()), vec![])
                .expect("last byte");
            assert_eq!(target.usage().payload_bytes, 3);
        },
    );
}

#[test]
fn cancellation_preserves_private_graph_and_never_fabricates_root() {
    let cancelled = std::cell::Cell::new(false);
    with_neutral_target(
        LIMITS,
        || cancelled.get(),
        |mut target| {
            let value = target
                .construct(ValueOp::Empty, vec![])
                .expect("before cancellation");
            cancelled.set(true);
            assert_eq!(target.append(value, value), Err(ConstructionError::Cancelled));
            assert_eq!(target.usage().nodes, 1);
            assert!(matches!(target.finish_graph(value), Err(ConstructionError::Cancelled)));
        },
    );
}

#[test]
fn diamond_graph_does_not_expand_shared_subtrees_and_drops_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let graph = with_neutral_target(
                LIMITS,
                || false,
                |mut target| {
                    let mut value = target
                        .construct(ValueOp::Text("x".into()), vec![])
                        .expect("leaf");
                    for _ in 0..20_000 {
                        value = target.append(value, value).expect("shared diamond");
                    }
                    target.finish_graph(value).expect("finish")
                },
            );
            assert_eq!(graph.node_count(), 20_001);
            assert_eq!(graph.usage().edges, 40_000);
            assert_eq!(graph.usage().payload_bytes, 1);
            assert_eq!(graph.node(graph.root()).expect("root").children, &[19_999, 19_999]);
            // Normal destruction of flat owned nodes is itself depth-independent.
            drop(graph);
        })
        .expect("small-stack worker")
        .join()
        .expect("flat construction and destruction");
}

#[test]
fn brand_has_no_runtime_identity_storage_and_independent_nested_targets_work() {
    assert_eq!(std::mem::size_of::<ValueRef<'_>>(), std::mem::size_of::<u32>());
    with_neutral_target(
        LIMITS,
        || false,
        |mut outer| {
            let outer_value = outer.construct(ValueOp::Empty, vec![]).expect("outer");
            let inner_graph = with_neutral_target(
                LIMITS,
                || false,
                |mut inner| {
                    let inner_value = inner.construct(ValueOp::Integer(7), vec![]).expect("inner");
                    inner.finish_graph(inner_value).expect("inner owned graph")
                },
            );
            assert_eq!(inner_graph.node_count(), 1);
            assert_eq!(outer.forward(outer_value), Ok(outer_value));
        },
    );
}
