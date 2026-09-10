use super::*;
use mettail_rholang_frontend::arena::{with_neutral_target, ConstructionLimits};
use mettail_rholang_frontend::construction::{CheckedFreshDescriptor, FreshShape};
use mettail_runtime::worklist::Worklist;
use prost::Message;

#[test]
fn fresh_target_moves_every_injection_and_uses_only_body_metadata() {
    let body = new_boundvar_par(3, vec![], true);
    let injections = vec![new_gstring_par("empty-key".into(), vec![1; 9], false), Par::default()];
    let descriptor = CheckedFreshDescriptor::new(
        FreshShape::Uri {
            binder_count: 2,
            uris: vec!["a".into(), "z".into()],
        },
        vec!["".into(), "unused".into()],
    )
    .expect("descriptor");
    let expected = new_new_par(
        2,
        body.clone(),
        vec!["a".into(), "z".into()],
        [("".into(), injections[0].clone()), ("unused".into(), injections[1].clone())].into(),
        vec![0, 1],
        vec![0, 1],
        true,
    );
    let actual = DirectNodeTarget::fresh(descriptor, body, injections).expect("fresh target");
    same_bytes(&actual, &expected);
    assert_eq!(actual.locally_free, [0, 1]);
    assert_eq!(actual.news[0].injections.len(), 2);
    assert!(actual.connective_used);

    // The converse flag case detects an accidental OR of injection metadata.
    let closed_body = DirectNodeTarget::fresh(
        CheckedFreshDescriptor::new(FreshShape::Plain { binder_count: 0 }, vec!["unused".into()])
            .expect("unused injection"),
        Par::default(),
        vec![new_gbool_par(true, vec![1; 9], true)],
    )
    .expect("body-only summary");
    assert!(closed_body.locally_free.is_empty());
    assert!(closed_body.news[0].locally_free.is_empty());
    assert!(!closed_body.connective_used);
    assert!(closed_body.news[0].injections["unused"].connective_used);

    // RhoTypes.proto: Par.news=4, New.p=2. A present empty body is encoded.
    let empty = DirectNodeTarget::fresh(
        CheckedFreshDescriptor::new(FreshShape::Plain { binder_count: 0 }, vec![]).expect("zero"),
        Par::default(),
        vec![],
    )
    .expect("empty fresh");
    assert_eq!(empty.encode_to_vec(), [0x22, 2, 0x12, 0]);
    // bindCount=1 is sint32 zigzag 2, URI field 3 retains its literal bytes.
    let uri = DirectNodeTarget::fresh(
        CheckedFreshDescriptor::new(
            FreshShape::Uri { binder_count: 1, uris: vec!["u".into()] },
            vec![],
        )
        .expect("uri"),
        Par::default(),
        vec![],
    )
    .expect("URI fresh");
    assert_eq!(uri.encode_to_vec(), [0x22, 7, 0x08, 2, 0x12, 0, 0x1a, 1, b'u']);
}

#[test]
fn fresh_target_rejects_missing_or_extra_injections_before_zip() {
    for count in [0, 2] {
        let descriptor =
            CheckedFreshDescriptor::new(FreshShape::Plain { binder_count: 0 }, vec!["key".into()])
                .expect("one injection");
        assert_eq!(
            DirectNodeTarget::fresh(descriptor, Par::default(), vec![Par::default(); count]),
            Err(ConstructionError::ChildArity { expected: 2, actual: count + 1 }),
        );
    }
}

#[test]
fn fresh_nested_node_clone_and_error_cleanup_reuse_stack_safe_node_lifecycle() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut value = Par::default();
            for _ in 0..20_000 {
                let descriptor =
                    CheckedFreshDescriptor::new(FreshShape::Plain { binder_count: 0 }, vec![])
                        .expect("zero-binder layout");
                value = DirectNodeTarget::fresh(descriptor, value, vec![]).expect("nested fresh");
            }
            // Existing generated clone and drop traverse the node graph iteratively.
            drop(value.clone());
            let descriptor = CheckedFreshDescriptor::new(
                FreshShape::Plain { binder_count: 0 },
                vec!["missing".into()],
            )
            .expect("one injection");
            assert!(matches!(
                DirectNodeTarget::fresh(descriptor, value, vec![]),
                Err(ConstructionError::ChildArity { expected: 2, actual: 1 }),
            ));
        })
        .expect("small-stack worker")
        .join()
        .expect("node lifecycle is stack safe");
}

fn parallel_transition<T: ValueTarget>(target: &mut T, texts: &[&str], pair: bool) -> T::Value {
    use mettail_rholang_frontend::construction::append_fold;
    let mut work = Worklist::with_capacity(1, texts.len());
    work.push(texts.len(), |arity| Some(*arity))
        .expect("continuation");
    for text in texts {
        work.value(
            target
                .construct(ValueOp::Text((*text).into()), vec![])
                .expect("leaf"),
        );
    }
    work.check().expect("ready continuation");
    work.pop(|arity| Some(*arity)).expect("pop continuation");
    match pair {
        true => work.reduce_pair(|left, right| ValueTarget::append(target, left, right)),
        false => work.reduce_values(texts.len(), |parts| append_fold(target, parts)),
    }
    .expect("same transition as production");
    work.check().expect("one constructed result");
    work.finish().expect("complete transition")
}

#[test]
fn shared_production_parallel_transitions_accept_both_real_targets() {
    for (texts, pair) in [
        (&[][..], false),
        (&["a"][..], false),
        (&["a", "b", "a", "c"][..], false),
        (&["left", "right"][..], true),
    ] {
        let direct = parallel_transition(&mut DirectNodeTarget, texts, pair);
        let expected = texts.iter().fold(Par::default(), |left, text| {
            left.append(new_gstring_par((*text).into(), Vec::new(), false))
        });
        same_bytes(&direct, &expected);
        let graph = with_neutral_target(
            ConstructionLimits {
                nodes: 20,
                edges: 40,
                payload_bytes: 100,
                work: 100,
            },
            || false,
            |mut target| {
                let root = parallel_transition(&mut target, texts, pair);
                assert_eq!(
                    target.observe(&root).expect("observe"),
                    DirectNodeTarget::observation(&direct)
                );
                target.finish_graph(root).expect("graph")
            },
        );
        assert_eq!(graph.node_count(), if pair { 3 } else { 2 * texts.len() + 1 });
        same_graph_interpretation(&graph, &direct);
    }
}

#[test]
fn shared_pair_retains_repeated_neutral_reference_without_clone_requirement() {
    with_neutral_target(
        ConstructionLimits {
            nodes: 2,
            edges: 2,
            payload_bytes: 1,
            work: 16,
        },
        || false,
        |mut target| {
            let value = target
                .construct(ValueOp::Text("a".into()), vec![])
                .expect("leaf");
            let mut work: Worklist<(), _> = Worklist::with_capacity(0, 2);
            work.value(value);
            work.value(value);
            work.reduce_pair(|left, right| ValueTarget::append(&mut target, left, right))
                .expect("pair");
            let graph = target
                .finish_graph(work.finish().expect("root"))
                .expect("graph");
            assert_eq!(graph.node(graph.root()).expect("root").children, [0, 0]);
        },
    );
}

fn same_bytes(actual: &Par, expected: &Par) {
    assert_eq!(actual, expected);
    assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
}

fn same_graph_interpretation(
    graph: &mettail_rholang_frontend::arena::ConstructionGraph,
    expected: &Par,
) {
    let mut work = 0;
    let mut cancelled = || false;
    let mut budget = mettail_rholang_codegen::ReflectedCodecBudget::new(
        &mut work,
        100_000,
        100_000,
        &mut cancelled,
    );
    let actual = crate::rholang_ast::interpret_construction_graph(graph, &mut budget)
        .expect("same program through graph interpretation");
    same_bytes(&actual, expected);
    assert_eq!(DirectNodeTarget::observation(&actual), DirectNodeTarget::observation(expected));
}

#[test]
fn primitive_target_reuses_exact_node_constructors() {
    let mut target = DirectNodeTarget;
    same_bytes(&target.construct(ValueOp::Empty, vec![]).expect("empty"), &Par::default());
    for value in [i64::MIN, -1, 0, 1, i64::MAX] {
        same_bytes(
            &target
                .construct(ValueOp::Integer(value), vec![])
                .expect("integer"),
            &new_gint_par(value, Vec::new(), false),
        );
    }
    for value in [false, true] {
        same_bytes(
            &target
                .construct(ValueOp::Boolean(value), vec![])
                .expect("boolean"),
            &new_gbool_par(value, Vec::new(), false),
        );
    }
    for value in ["", "a\0é\\n", "left|right"] {
        same_bytes(
            &target
                .construct(ValueOp::Text(value.into()), vec![])
                .expect("text"),
            &new_gstring_par(value.into(), Vec::new(), false),
        );
    }
}

#[test]
fn direct_append_preserves_order_metadata_and_forwarding() {
    let mut target = DirectNodeTarget;
    let left = new_gstring_par("left".into(), vec![1, 0, 0], true);
    let right = new_gint_par(7, vec![2, 4], false);
    let expected = left.append(right.clone());
    let actual = target
        .construct(ValueOp::Append, vec![left, right])
        .expect("append");
    same_bytes(&actual, &expected);
    let observation = target.observe(&actual).expect("observation");
    assert_eq!(observation.locally_free, [3, 4, 0]);
    assert!(observation.connective_used);
    assert!(!observation.single_string);
    let exprs = actual.exprs.as_ptr();
    let forwarded = target.forward(actual).expect("identity");
    assert_eq!(forwarded.exprs.as_ptr(), exprs, "forwarding does not clone the value");
    same_bytes(&forwarded, &expected);
}

#[test]
fn direct_bound_validation_rejects_before_index_sized_construction() {
    let mut target = DirectNodeTarget;
    for (scope, index) in [(0, 0), (2, 2), (1, 31)] {
        assert_eq!(
            target.construct(ValueOp::Bound { scope, index }, vec![]),
            Err(ConstructionError::IndexOutOfScope { scope, index })
        );
    }
    let index = i32::MAX as usize + 1;
    for scope in [0, usize::MAX] {
        assert_eq!(
            target.construct(ValueOp::Bound { scope, index }, vec![]),
            Err(ConstructionError::TargetIndexOutOfRange { index })
        );
    }
    // A large enclosing width does not imply a large emitted reference.
    same_bytes(
        &target
            .construct(ValueOp::Bound { scope: usize::MAX, index: 0 }, vec![])
            .expect("small reference"),
        &new_boundvar_par(0, vec![], false),
    );
}

#[test]
fn direct_target_rejects_every_wrong_arity_in_initial_family() {
    let mut target = DirectNodeTarget;
    for operation in [
        ValueOp::Empty,
        ValueOp::Integer(0),
        ValueOp::Boolean(false),
        ValueOp::Text("".into()),
        ValueOp::Bound { scope: 1, index: 0 },
        ValueOp::Wildcard { connective: true },
    ] {
        assert_eq!(
            target.construct(operation, vec![Par::default()]),
            Err(ConstructionError::ChildArity { expected: 0, actual: 1 })
        );
    }
    for actual in [0, 1, 3] {
        assert_eq!(
            target.construct(ValueOp::Append, vec![Par::default(); actual]),
            Err(ConstructionError::ChildArity { expected: 2, actual })
        );
    }
}

#[test]
fn checked_bound_and_wildcard_targets_match_independent_wire_and_actual_worker() {
    for index in [0usize, 1, 7, 8, 15, 31] {
        let mut expected =
            vec![0x2a, 7, 0x9a, 1, 4, 0x0a, 2, 0x08, (index * 2) as u8, 0x4a, (index + 1) as u8];
        expected.extend(std::iter::repeat_n(0, index));
        expected.push(1);
        let direct = DirectNodeTarget
            .construct(ValueOp::Bound { scope: index + 1, index }, vec![])
            .expect("bound target");
        assert_eq!(direct.encode_to_vec(), expected);
        let variable = super::super::FreeVar::fresh_named("bound".to_owned());
        let env = super::super::extend_env(
            &super::super::BoundEnv::new(),
            &(0..=index)
                .map(|_| super::super::Binder(variable.clone()))
                .collect::<Vec<_>>(),
        )
        .expect("declared scope");
        // Last insertion selects zero; outer shifting then reaches index.
        let env = super::super::extend_env(
            &env,
            &(0..index)
                .map(|_| {
                    super::super::Binder(super::super::FreeVar::fresh_named("unused".to_owned()))
                })
                .collect::<Vec<_>>(),
        )
        .expect("shift");
        let actual = super::super::lower_proc_in_env(
            &super::super::Proc::PVar(super::super::OrdVar(super::super::Var::Free(variable))),
            &env,
        )
        .expect("same source worker");
        same_bytes(&direct, &actual);
        let graph = with_neutral_target(
            ConstructionLimits {
                nodes: 1,
                edges: 0,
                payload_bytes: index + 1,
                work: index + 3,
            },
            || false,
            |mut target| {
                let root = target
                    .construct(ValueOp::Bound { scope: index + 1, index }, vec![])
                    .expect("neutral bound");
                target.finish_graph(root).expect("graph")
            },
        );
        same_graph_interpretation(&graph, &direct);
    }
    for connective in [false, true] {
        let direct = DirectNodeTarget
            .construct(ValueOp::Wildcard { connective }, vec![])
            .expect("wildcard");
        let mut expected = vec![0x2a, 7, 0x9a, 1, 4, 0x0a, 2, 0x1a, 0];
        if connective {
            expected.extend([0x50, 1]);
        }
        assert_eq!(direct.encode_to_vec(), expected);
        let graph = with_neutral_target(
            ConstructionLimits {
                nodes: 1,
                edges: 0,
                payload_bytes: 0,
                work: 2,
            },
            || false,
            |mut target| {
                let root = target
                    .construct(ValueOp::Wildcard { connective }, vec![])
                    .expect("neutral wildcard");
                target.finish_graph(root).expect("graph")
            },
        );
        same_graph_interpretation(&graph, &direct);
    }
}

// A finite algebra program, not a new syntax traversal. Both carriers execute
// the same operations through the already-shared worklist, without a Clone
// bound. Compare every observation, including intermediate empty/string cases.
fn execute<T: ValueTarget>(target: &mut T) -> (T::Value, Vec<bool>) {
    let program = [
        ValueOp::Empty,
        ValueOp::Text("left".into()),
        ValueOp::Append,
        ValueOp::Integer(7),
        ValueOp::Append,
        ValueOp::Text("right".into()),
        ValueOp::Append,
    ];
    let mut work = Worklist::with_capacity(program.len(), program.len());
    for operation in program.into_iter().rev() {
        work.push(operation, |op| Some(op.arity()))
            .expect("checked arity");
    }
    let mut observations = Vec::with_capacity(7);
    work.check().expect("whole algebra program owes one result");
    while let Some(operation) = work.pop(|op| Some(op.arity())).expect("operation") {
        let children = work
            .pop_values(operation.arity())
            .expect("source-ordered children");
        let value = target.construct(operation, children).expect("construct");
        let observation = target.observe(&value).expect("observe");
        assert!(observation.locally_free.is_empty());
        assert!(!observation.connective_used);
        observations.push(observation.single_string);
        work.value(target.forward(value).expect("forward"));
        work.check().expect("complete transition");
    }
    (work.finish().expect("one result"), observations)
}

#[test]
fn neutral_and_direct_targets_commute_on_shared_worklist_observations() {
    let (direct, observations) = execute(&mut DirectNodeTarget);
    assert_eq!(observations, [false, true, true, false, false, true, false]);
    let graph = with_neutral_target(
        ConstructionLimits {
            nodes: 7,
            edges: 6,
            payload_bytes: 9,
            work: 100,
        },
        || false,
        |mut target| {
            let (root, neutral_observations) = execute(&mut target);
            assert_eq!(neutral_observations, observations);
            target.finish_graph(root).expect("owned graph")
        },
    );
    assert_eq!(graph.node_count(), 7);
    assert_eq!(graph.node(graph.root()).expect("root").children, [4, 5]);
    same_graph_interpretation(&graph, &direct);
    let expected = Par::default()
        .append(new_gstring_par("left".into(), Vec::new(), false))
        .append(new_gint_par(7, Vec::new(), false))
        .append(new_gstring_par("right".into(), Vec::new(), false));
    same_bytes(&direct, &expected);
}
