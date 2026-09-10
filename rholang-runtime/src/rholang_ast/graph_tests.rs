use super::*;
use mettail_rholang_frontend::arena::{with_neutral_target, ConstructionLimits};
use prost::Message;

#[test]
fn bound_graph_charges_both_metadata_allocations_and_observation_before_building() {
    for index in [0, 1, 7, 8, 31, 65_535] {
        let graph = graph(vec![(ValueOp::Bound { scope: index + 1, index }, vec![])], 0);
        let bytes = index + 1;
        let work = 7 + 3 * bytes as u64;
        let units = 24 + 2 * bytes;
        let (result, used, remaining) = run(&graph, work, units, || false);
        let result = result.expect("exact bound budget");
        assert_eq!(result.locally_free.len(), bytes);
        assert_eq!(result.locally_free[index], 1);
        assert_eq!((used, remaining), (work, 0));
        let (result, used, remaining) = run(&graph, work - 1, units, || false);
        assert_eq!(
            result,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::WorkLimit))
        );
        assert_eq!((used, remaining), (6, units - 20));
        let (result, used, remaining) = run(&graph, work, units - 1, || false);
        assert_eq!(
            result,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::PayloadByteLimit))
        );
        assert_eq!((used, remaining), (6, units - 21));
    }
}

#[test]
fn append_metadata_debits_use_left_copy_and_maximum_length_not_additive_lengths() {
    for (left_bytes, right_bytes) in [(2, 9), (9, 2), (1, 1)] {
        let graph = graph(
            vec![
                (ValueOp::Bound { scope: left_bytes, index: left_bytes - 1 }, vec![]),
                (
                    ValueOp::Bound {
                        scope: right_bytes,
                        index: right_bytes - 1,
                    },
                    vec![],
                ),
                (ValueOp::Append, vec![0, 1]),
            ],
            2,
        );
        let maximum = left_bytes.max(right_bytes);
        let work = (20 + 4 * left_bytes + 3 * right_bytes + 3 * maximum) as u64;
        let units = 64 + 3 * left_bytes + 2 * right_bytes + maximum;
        let (result, used, remaining) = run(&graph, work, units, || false);
        let result = result.expect("exact append budget");
        assert_eq!(result.locally_free.len(), maximum);
        assert_eq!(result.locally_free[left_bytes - 1], 1);
        assert_eq!(result.locally_free[right_bytes - 1], 1);
        assert_eq!((used, remaining), (work, 0));
        assert!(matches!(
            run(&graph, work - 1, units, || false).0,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::WorkLimit))
        ));
        assert!(matches!(
            run(&graph, work, units - 1, || false).0,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::PayloadByteLimit))
        ));
    }
    let shared = graph(
        vec![(ValueOp::Bound { scope: 3, index: 2 }, vec![]), (ValueOp::Append, vec![0, 0])],
        1,
    );
    let (result, used, remaining) = run(&shared, 47, 70, || false);
    assert_eq!(result.expect("both occurrences").locally_free, [0, 0, 1]);
    assert_eq!((used, remaining), (47, 0));
}

#[test]
fn metadata_cost_overflow_and_failed_reservation_never_call_the_constructor() {
    assert_eq!(MetadataCharge::bound(usize::MAX), Err(GraphInterpretationError::SizeOverflow));
    assert_eq!(
        MetadataCharge::append(usize::MAX, 0),
        Err(GraphInterpretationError::SizeOverflow)
    );
    let mut used = 0;
    let mut cancelled = || false;
    let mut budget = ReflectedCodecBudget::new(&mut used, 100, 5, &mut cancelled);
    let mut calls = 0;
    let result = precharged(
        &mut budget,
        Footprint { entries: 1, text_bytes: 0 },
        MetadataCharge::bound(1).expect("cost"),
        || {
            calls += 1;
            Ok(())
        },
    );
    assert_eq!(
        result,
        Err(GraphInterpretationError::Resource(DynamicReflectionError::PayloadByteLimit))
    );
    assert_eq!((calls, budget.work_used(), budget.remaining_bytes()), (0, 0, 5));
}

#[test]
fn bound_metadata_cancellation_preserves_exact_paid_prefix_without_partial_output() {
    let graph = graph(
        vec![(ValueOp::Bound { scope: 3, index: 2 }, vec![]), (ValueOp::Append, vec![0, 0])],
        1,
    );
    // Stack reservation, root/left visits, left construction, right visit/
    // construction, append visit/construction. A refused reservation is atomic.
    let paid_prefixes =
        [(0, 70), (8, 38), (9, 38), (10, 38), (20, 28), (21, 28), (31, 18), (32, 18)];
    for (stop, expected) in paid_prefixes.into_iter().enumerate() {
        let mut calls = 0;
        let (result, spent, remaining) = run(&graph, 47, 70, || {
            calls += 1;
            calls == stop + 1
        });
        assert_eq!(
            result,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::Cancelled))
        );
        assert_eq!(calls, stop + 1);
        assert_eq!((spent, remaining), expected);
    }
}

#[test]
fn exact_metadata_observation_rejects_wrong_reference_and_wildcard_flag() {
    let bound = graph(vec![(ValueOp::Bound { scope: 2, index: 1 }, vec![])], 0);
    assert!(matches!(
        checked_value(
            &bound,
            0,
            models::rust::utils::new_boundvar_par(0, vec![], false),
            Footprint { entries: 1, text_bytes: 0 }
        ),
        Err(GraphInterpretationError::ObservationMismatch { index: 0 })
    ));
    let wildcard = graph(vec![(ValueOp::Wildcard { connective: true }, vec![])], 0);
    assert!(matches!(
        checked_value(
            &wildcard,
            0,
            DirectNodeTarget::wildcard(false),
            Footprint { entries: 1, text_bytes: 0 }
        ),
        Err(GraphInterpretationError::ObservationMismatch { index: 0 })
    ));
}

fn graph(steps: Vec<(ValueOp, Vec<usize>)>, root: usize) -> ConstructionGraph {
    with_neutral_target(
        ConstructionLimits {
            nodes: steps.len(),
            edges: steps.len() * 2,
            payload_bytes: 1_000_000,
            work: 1_000_000 + steps.len() * 4 + 1,
        },
        || false,
        |mut target| {
            let mut values = Vec::with_capacity(steps.len());
            for (operation, children) in steps {
                let children = children.into_iter().map(|index| values[index]).collect();
                values.push(
                    target
                        .construct(operation, children)
                        .expect("valid graph node"),
                );
            }
            target.finish_graph(values[root]).expect("owned root")
        },
    )
}

fn run(
    graph: &ConstructionGraph,
    work_limit: u64,
    units: usize,
    mut cancelled: impl FnMut() -> bool,
) -> (Result<Par, GraphInterpretationError>, u64, usize) {
    let mut work = 0;
    let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, units, &mut cancelled);
    let result = interpret_construction_graph(graph, &mut budget);
    let remaining = budget.finish();
    (result, work, remaining)
}

fn same_bytes(actual: &Par, expected: &Par) {
    assert_eq!(actual, expected);
    assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
    assert_eq!(DirectNodeTarget::observation(actual), DirectNodeTarget::observation(expected));
}

#[test]
fn primitive_graphs_match_node_constructors_and_independent_wire_examples() {
    // RhoTypes.proto: Par.exprs field 5; Expr oneof bool=1, sint64=2, string=3.
    let mut minimum = vec![0x2a, 11, 0x10];
    minimum.extend([0xff; 9]);
    minimum.push(1);
    let mut maximum = vec![0x2a, 11, 0x10, 0xfe];
    maximum.extend([0xff; 8]);
    maximum.push(1);
    for (operation, expected_wire, work, units) in [
        (ValueOp::Empty, vec![], 6, 20),
        (ValueOp::Boolean(false), vec![0x2a, 2, 8, 0], 7, 24),
        (ValueOp::Boolean(true), vec![0x2a, 2, 8, 1], 7, 24),
        (ValueOp::Integer(i64::MIN), minimum, 7, 24),
        (ValueOp::Integer(i64::MAX), maximum, 7, 24),
        (ValueOp::Text(String::new()), vec![0x2a, 2, 0x1a, 0], 7, 24),
        (ValueOp::Text("é".into()), vec![0x2a, 4, 0x1a, 2, 0xc3, 0xa9], 9, 26),
    ] {
        let graph = graph(vec![(operation, vec![])], 0);
        let (result, spent, remaining) = run(&graph, work, units, || false);
        let actual = result.expect("exact primitive allowance");
        assert_eq!(actual.encode_to_vec(), expected_wire);
        assert_eq!((spent, remaining), (work, 0));
        assert_eq!(
            DirectNodeTarget::observation(&actual),
            graph.node(0).expect("root").observation
        );
    }
}

#[test]
fn ordered_diamond_and_empty_identity_match_direct_construction() {
    let graph = graph(
        vec![
            (ValueOp::Empty, vec![]),
            (ValueOp::Text("left".into()), vec![]),
            (ValueOp::Text("right".into()), vec![]),
            (ValueOp::Append, vec![0, 1]),
            (ValueOp::Append, vec![2, 0]),
            (ValueOp::Append, vec![3, 4]),
            (ValueOp::Append, vec![5, 3]),
        ],
        6,
    );
    let actual = run(&graph, 1000, 1000, || false).0.expect("diamond");
    let expected = DirectNodeTarget::text("left".into())
        .append(DirectNodeTarget::text("right".into()))
        .append(DirectNodeTarget::text("left".into()));
    same_bytes(&actual, &expected);
}

#[test]
fn unreachable_suffix_does_not_affect_root_or_debits() {
    let plain = graph(vec![(ValueOp::Text("a".into()), vec![])], 0);
    let with_suffix = graph(
        vec![
            (ValueOp::Text("a".into()), vec![]),
            (ValueOp::Text("unreachable".into()), vec![]),
            (ValueOp::Append, vec![1, 1]),
        ],
        0,
    );
    assert_eq!(run(&plain, 8, 25, || false), run(&with_suffix, 8, 25, || false));
}

#[test]
fn repeated_edges_are_charged_per_occurrence_in_both_dimensions() {
    let graph = graph(vec![(ValueOp::Text("a".into()), vec![]), (ValueOp::Append, vec![0, 0])], 1);
    // Setup: 8 slots. Four jobs; two leaf copies; append copies three entries
    // and three bytes. Work = 8 + 4 + 4 + 6. Units = 32 + 10 + 15.
    let (result, work, remaining) = run(&graph, 22, 57, || false);
    same_bytes(
        &result.expect("exact shared-edge allowance"),
        &DirectNodeTarget::text("a".into()).append(DirectNodeTarget::text("a".into())),
    );
    assert_eq!((work, remaining), (22, 0));
    let (result, spent, remaining) = run(&graph, 21, 57, || false);
    assert_eq!(
        result,
        Err(GraphInterpretationError::Resource(DynamicReflectionError::WorkLimit))
    );
    assert_eq!((spent, remaining), (16, 15), "failed append charge is atomic");
    let (result, spent, remaining) = run(&graph, 22, 56, || false);
    assert_eq!(
        result,
        Err(GraphInterpretationError::Resource(DynamicReflectionError::PayloadByteLimit))
    );
    assert_eq!((spent, remaining), (16, 14), "byte refusal cannot spend work");
}

#[test]
fn left_associated_append_pays_for_each_growing_prefix() {
    let graph = graph(
        vec![
            (ValueOp::Text("a".into()), vec![]),
            (ValueOp::Text("b".into()), vec![]),
            (ValueOp::Append, vec![0, 1]),
            (ValueOp::Text("c".into()), vec![]),
            (ValueOp::Append, vec![2, 3]),
        ],
        4,
    );
    // 17 setup slots, 7 jobs, 3 scalar copies, then 3 and 5 append copies.
    let (result, work, remaining) = run(&graph, 46, 123, || false);
    let expected = DirectNodeTarget::text("a".into())
        .append(DirectNodeTarget::text("b".into()))
        .append(DirectNodeTarget::text("c".into()));
    same_bytes(&result.expect("every prefix paid"), &expected);
    assert_eq!((work, remaining), (46, 0));
    assert!(run(&graph, 45, 123, || false).0.is_err());
}

#[test]
fn borrowed_budget_preserves_incoming_work_and_checks_setup_atomically() {
    let graph = graph(vec![(ValueOp::Empty, vec![])], 0);
    for (initial, limit, units, expected) in [
        (4, 9, 20, DynamicReflectionError::WorkLimit),
        (0, 6, 19, DynamicReflectionError::PayloadByteLimit),
        (u64::MAX, u64::MAX, 20, DynamicReflectionError::WorkLimit),
    ] {
        let mut work = initial;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, limit, units, &mut cancelled);
        assert_eq!(
            interpret_construction_graph(&graph, &mut budget),
            Err(GraphInterpretationError::Resource(expected))
        );
        if initial == 4 {
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (9, 0));
        } else {
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (initial, units));
        }
    }
    let mut work = 4;
    let mut cancelled = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 10, 20, &mut cancelled);
    assert_eq!(
        interpret_construction_graph(&graph, &mut budget).expect("cumulative work"),
        Par::default()
    );
    assert_eq!((budget.work_used(), budget.remaining_bytes()), (10, 0));
}

#[test]
fn doubling_graph_cannot_hide_expansion_behind_unique_node_count() {
    let depth = 10usize;
    let mut steps = vec![(ValueOp::Text("a".into()), vec![])];
    let (mut work, mut units, mut heads) = (3u64, 5usize, 1usize);
    for index in 0..depth {
        steps.push((ValueOp::Append, vec![index, index]));
        work = 2 * work + 2 + 6 * heads as u64;
        units = 2 * units + 15 * heads;
        heads *= 2;
    }
    let slots = 3 * (depth + 1) + 2;
    work += slots as u64;
    units += 4 * slots;
    let graph = graph(steps, depth);
    let (result, spent, remaining) = run(&graph, work, units, || false);
    assert_eq!(result.expect("all occurrences paid").exprs.len(), heads);
    assert_eq!((spent, remaining), (work, 0));
    assert!(matches!(
        run(&graph, work - 1, units, || false).0,
        Err(GraphInterpretationError::Resource(DynamicReflectionError::WorkLimit))
    ));
}

#[test]
fn cancellation_at_each_reservation_returns_no_partial_root() {
    let graph = graph(vec![(ValueOp::Text("a".into()), vec![]), (ValueOp::Append, vec![0, 0])], 1);
    for stop in 1..=8 {
        let mut calls = 0;
        let (result, spent, _) = run(&graph, 22, 57, || {
            calls += 1;
            calls == stop
        });
        assert_eq!(
            result,
            Err(GraphInterpretationError::Resource(DynamicReflectionError::Cancelled))
        );
        assert_eq!(calls, stop);
        assert!(spent < 22);
    }
}

#[test]
fn precharge_rejects_before_callback_and_retains_paid_failed_callback_cost() {
    let mut work = 0;
    let mut cancelled = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 10, 4, &mut cancelled);
    let mut calls = 0;
    let error = precharged(
        &mut budget,
        Footprint { entries: 1, text_bytes: 1 },
        MetadataCharge::default(),
        || {
            calls += 1;
            Ok(())
        },
    );
    assert_eq!(
        error,
        Err(GraphInterpretationError::Resource(DynamicReflectionError::PayloadByteLimit))
    );
    assert_eq!((calls, budget.work_used(), budget.remaining_bytes()), (0, 0, 4));
    let error: Result<(), _> = precharged(
        &mut budget,
        Footprint { entries: 1, text_bytes: 0 },
        MetadataCharge::default(),
        || {
            calls += 1;
            Err(GraphInterpretationError::ObservationMismatch { index: 0 })
        },
    );
    assert_eq!(error, Err(GraphInterpretationError::ObservationMismatch { index: 0 }));
    assert_eq!((calls, budget.work_used(), budget.remaining_bytes()), (1, 1, 0));
}

#[test]
fn checked_footprint_arithmetic_never_allocates_or_calls_constructor() {
    let mut work = 0;
    let mut cancelled = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, u64::MAX, usize::MAX, &mut cancelled);
    for size in [
        Footprint { entries: usize::MAX, text_bytes: 1 },
        Footprint {
            entries: usize::MAX / 4 + 1,
            text_bytes: 0,
        },
        Footprint { entries: 1, text_bytes: usize::MAX - 2 },
    ] {
        assert_eq!(
            precharged(&mut budget, size, MetadataCharge::default(), || -> Result<(), _> {
                panic!("overflow must reject before helper")
            }),
            Err(GraphInterpretationError::SizeOverflow)
        );
    }
    assert_eq!(
        Footprint { entries: usize::MAX, text_bytes: 0 }
            .plus(Footprint { entries: 1, text_bytes: 0 }),
        Err(GraphInterpretationError::SizeOverflow)
    );
    assert_eq!(
        Footprint { entries: 0, text_bytes: usize::MAX }
            .plus(Footprint { entries: 0, text_bytes: 1 }),
        Err(GraphInterpretationError::SizeOverflow)
    );
    assert_eq!((budget.work_used(), budget.remaining_bytes()), (0, usize::MAX));
}

#[test]
fn deep_graph_success_and_mid_expansion_refusal_use_small_native_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 20_000usize;
            let mut steps = Vec::with_capacity(depth + 1);
            steps.push((ValueOp::Empty, vec![]));
            for index in 0..depth {
                steps.push((ValueOp::Append, vec![index, 0]));
            }
            let graph = graph(steps, depth);
            let slots = 3 * (depth + 1) + 2;
            let work = (slots + 3 * depth + 1) as u64;
            let units = 4 * slots;
            let (result, spent, remaining) = run(&graph, work, units, || false);
            assert_eq!(result.expect("deep iterative construction"), Par::default());
            assert_eq!((spent, remaining), (work, 0));
            assert!(matches!(
                run(&graph, slots as u64 + 1000, units, || false).0,
                Err(GraphInterpretationError::Resource(DynamicReflectionError::WorkLimit))
            ));
        })
        .expect("small-stack worker")
        .join()
        .expect("stack-safe success and teardown");
}
