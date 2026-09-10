use super::*;
use mettail_rholang_frontend::arena::{with_neutral_target, ConstructionLimits};
use mettail_runtime::worklist::Worklist;
use prost::Message;

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
fn direct_target_rejects_every_wrong_arity_in_initial_family() {
    let mut target = DirectNodeTarget;
    for operation in [
        ValueOp::Empty,
        ValueOp::Integer(0),
        ValueOp::Boolean(false),
        ValueOp::Text("".into()),
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
    let expected = Par::default()
        .append(new_gstring_par("left".into(), Vec::new(), false))
        .append(new_gint_par(7, Vec::new(), false))
        .append(new_gstring_par("right".into(), Vec::new(), false));
    same_bytes(&direct, &expected);
}
