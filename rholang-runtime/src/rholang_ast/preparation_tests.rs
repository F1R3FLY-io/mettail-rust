//! Storage reservations count logical index slots, not payload nodes or RSS.

use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use mettail_runtime::worklist::WorklistError;
use prost::Message;
use std::cell::Cell;

#[test]
fn initial_storage_reservation_checks_both_dimensions_and_retains_paid_prefix() {
    let source = Proc::PZero;
    // Initial capacities reserve 128 four-byte slots, then the seed reserves
    // one more slot. A rejected seed does not refund the capacity reservation.
    for (work_limit, bytes, expected, used, remaining) in [
        (0, 516, Some(DynamicReflectionError::WorkLimit), 0, 516),
        (1, 516, Some(DynamicReflectionError::WorkLimit), 1, 4),
        (2, 0, Some(DynamicReflectionError::PayloadByteLimit), 0, 0),
        (2, 511, Some(DynamicReflectionError::PayloadByteLimit), 0, 511),
        (2, 515, Some(DynamicReflectionError::PayloadByteLimit), 1, 3),
        (2, 516, None, 2, 0),
    ] {
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, bytes, &mut cancel);
        let result = {
            let mut reserve = |units, bytes| {
                budget
                    .charge(units, bytes)
                    .map_err(RholangAstLowerError::Preparation)
            };
            Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).map(|_| ())
        };
        assert_eq!(
            result,
            expected.map_or(Ok(()), |error| Err(RholangAstLowerError::Preparation(error)))
        );
        assert_eq!(budget.work_used(), used);
        assert_eq!(budget.remaining_bytes(), remaining);
    }
}

#[test]
fn cancellation_precedes_initial_storage_reservation() {
    let mut work = 7;
    let mut cancel = || true;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
    let result = {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        Stacks::new(Job::Proc(&Proc::PZero, ROOT_ENV), &mut reserve).map(|_| ())
    };
    assert_eq!(
        result,
        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
    );
    assert_eq!(budget.work_used(), 7);
    assert_eq!(budget.remaining_bytes(), 4096);
}

#[test]
fn cancelled_storage_operations_preserve_pending_job_and_ordered_values() {
    let cancelled = Cell::new(false);
    let mut cancel = || cancelled.get();
    let mut work = 0;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        for value in [10, 20, 30] {
            stacks
                .value(new_gint_par(value, vec![], false))
                .expect("paid value");
        }
        cancelled.set(true);
        assert!(matches!(
            stacks.push(Job::Combine(Kont::FormulaNot)),
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert!(matches!(
            stacks.pop(),
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert!(matches!(
            stacks.value(Par::default()),
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert!(matches!(
            stacks.pop_value(),
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert!(matches!(
            stacks.pop_values(2),
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert_eq!(stacks.value_count(), 3);
        cancelled.set(false);
        assert!(matches!(
            stacks.pop().expect("original seed retained"),
            Some(Job::Proc(Proc::PZero, _))
        ));
        assert!(stacks.pop().expect("empty pop is also charged").is_none());
        assert_eq!(
            stacks.pop_values(2).expect("ordered suffix"),
            vec![new_gint_par(20, vec![], false), new_gint_par(30, vec![], false)]
        );
        assert_eq!(stacks.value_count(), 1);
        assert_eq!(stacks.pop_value().expect("unchanged prefix"), new_gint_par(10, vec![], false));
    }
    assert_eq!(budget.work_used(), 11);
    assert_eq!(budget.remaining_bytes(), 4096 - 134 * 4);
}

#[test]
fn suffix_underflow_retains_charge_and_preserves_prefix_and_source_order() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        for value in [10, 20, 20] {
            stacks
                .value(new_gint_par(value, vec![], false))
                .expect("paid value");
        }
        assert_eq!(
            stacks.pop_values(4),
            Err(RholangAstLowerError::Storage(WorklistError::ValueUnderflow {
                requested: 4,
                available: 3,
            }))
        );
        assert_eq!(stacks.value_count(), 3);
        assert_eq!(
            stacks
                .pop_values(2)
                .expect("repeated values retain multiplicity"),
            vec![new_gint_par(20, vec![], false), new_gint_par(20, vec![], false)]
        );
        assert_eq!(stacks.pop_value().expect("unchanged prefix"), new_gint_par(10, vec![], false));
    }
    assert_eq!(budget.work_used(), 14);
    assert_eq!(budget.remaining_bytes(), 4096 - 138 * 4);
}

#[test]
fn arity_work_sum_and_slot_product_overflow_reject_before_reservation() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        assert_eq!(
            stacks.push(Job::Combine(Kont::Method { name: "overflow", argc: usize::MAX })),
            Err(RholangAstLowerError::PreparationSizeOverflow)
        );
        assert_eq!(
            stacks.pop_values(usize::MAX),
            Err(RholangAstLowerError::PreparationSizeOverflow)
        );
        assert_eq!(
            stacks.pop_values(usize::MAX / 4 + 1),
            Err(RholangAstLowerError::PreparationSizeOverflow)
        );
        assert_eq!(stacks.value_count(), 0);
        // Inspect the existing storage directly so the observation adds no
        // reservation and distinguishes a rejected push from a changed stack.
        assert!(matches!(
            stacks.inner.pop(Stacks::classify).expect("seed"),
            Some(Job::Proc(Proc::PZero, _))
        ));
        assert!(stacks
            .inner
            .pop(Stacks::classify)
            .expect("no overflow job")
            .is_none());
    }
    assert_eq!(budget.work_used(), 2);
    assert_eq!(budget.remaining_bytes(), 4096 - 129 * 4);
}

#[test]
fn worklist_counter_overflow_is_typed_and_does_not_refund_the_push() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        stacks
            .push(Job::Combine(Kont::ListLit(usize::MAX)))
            .expect("representable arity");
        assert_eq!(
            stacks.push(Job::Combine(Kont::FormulaNot)),
            Err(RholangAstLowerError::Storage(WorklistError::CounterOverflow))
        );
        assert!(matches!(
            stacks.pop().expect("previous continuation retained"),
            Some(Job::Combine(Kont::ListLit(usize::MAX)))
        ));
        assert!(matches!(stacks.pop().expect("seed retained"), Some(Job::Proc(Proc::PZero, _))));
        assert!(stacks
            .pop()
            .expect("overflow job was not recorded")
            .is_none());
    }
    assert_eq!(budget.work_used(), 7);
    assert_eq!(budget.remaining_bytes(), 4096 - 131 * 4);
}

#[test]
fn consuming_reductions_gate_callbacks_and_retain_charges_on_constructor_failure() {
    for pair in [true, false] {
        let cancelled = Cell::new(false);
        let calls = Cell::new(0);
        let mut cancel = || cancelled.get();
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, 4096, &mut cancel);
        {
            let mut reserve = |units, bytes| {
                budget
                    .charge(units, bytes)
                    .map_err(RholangAstLowerError::Preparation)
            };
            let source = Proc::PZero;
            let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
            for value in [10, 20, 30] {
                stacks
                    .value(new_gint_par(value, vec![], false))
                    .expect("paid value");
            }
            for stop in [true, false] {
                cancelled.set(stop);
                let mut fail = |children: Vec<Par>| -> Result<Par, RholangAstLowerError> {
                    calls.set(calls.get() + 1);
                    assert_eq!(
                        children,
                        vec![new_gint_par(20, vec![], false), new_gint_par(30, vec![], false)]
                    );
                    Err(RholangAstLowerError::UnsupportedProc("synthetic constructor failure"))
                };
                let result = if pair {
                    stacks.reduce_pair(|left, right| fail(vec![left, right]))
                } else {
                    stacks.reduce_values(2, &mut fail)
                };
                if stop {
                    assert_eq!(
                        result,
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    );
                    assert_eq!(calls.get(), 0);
                    assert_eq!(stacks.value_count(), 3);
                } else {
                    assert_eq!(
                        result,
                        Err(RholangAstLowerError::UnsupportedProc("synthetic constructor failure"))
                    );
                    assert_eq!(calls.get(), 1);
                    assert_eq!(
                        stacks.value_count(),
                        1,
                        "failed construction publishes no substitute"
                    );
                }
            }
            assert_eq!(
                stacks.pop_value().expect("retained prefix"),
                new_gint_par(10, vec![], false)
            );
        }
        assert_eq!(budget.work_used(), if pair { 9 } else { 10 });
        assert_eq!(budget.remaining_bytes(), 4096 - if pair { 133 * 4 } else { 135 * 4 });
    }
}

#[test]
fn deep_pending_storage_retains_lifo_order_with_exact_logical_allowance() {
    const DEPTH: usize = 4096;
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(
        &mut work,
        (2 * DEPTH + 4) as u64,
        (129 + DEPTH) * 4,
        &mut cancel,
    );
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        for arity in 0..DEPTH {
            stacks
                .push(Job::Combine(Kont::ListLit(arity)))
                .expect("paid pending job");
        }
        for expected in (0..DEPTH).rev() {
            match stacks.pop().expect("paid job removal") {
                Some(Job::Combine(Kont::ListLit(actual))) => assert_eq!(actual, expected),
                _ => panic!("pending continuations must retain LIFO order"),
            }
        }
        assert!(matches!(stacks.pop().expect("seed"), Some(Job::Proc(Proc::PZero, _))));
        assert!(stacks.pop().expect("empty pop").is_none());
    }
    assert_eq!(budget.work_used(), (2 * DEPTH + 4) as u64);
    assert_eq!(budget.remaining_bytes(), 0);
}

fn held_integer_fold() -> Proc {
    Proc::IntBinProc(Arc::new(Proc::CastInt(Arc::new(Int::NumLit(5)))), Arc::new(Int::NumLit(8)))
}

// These driver-storage tests also cover families outside the public source
// profile. Exercise that internal boundary explicitly, not public admission.
fn lower_storage_test_body<C: FnMut() -> bool>(
    source: &Proc,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<session::DirectLoweringOutput, RholangAstLowerError> {
    session::with_owned_outputs(|_| {
        let mut context = BoundEnv::new();
        context.admission = SourceAdmissionMode::Public;
        drive_machine_with_reservation(Seed::Body(source), &context, &mut |work, bytes| {
            budget
                .charge(work, bytes)
                .map_err(RholangAstLowerError::Preparation)
        })
    })
}

#[test]
fn storage_bounded_whole_body_preserves_existing_bytes_and_owned_fold_outputs() {
    let source = held_integer_fold();
    let reference =
        session::lower_public_body(&source, BoundEnv::new()).expect("existing whole body");
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    let bounded = lower_storage_test_body(&source, &mut budget)
        .expect("bounded storage uses the same body driver");
    assert_eq!(bounded.par.encode_to_vec(), reference.par.encode_to_vec());
    assert_eq!(bounded.folds.len(), 1);
    assert_eq!(bounded.folds[0].channel(), reference.folds[0].channel());
    assert_eq!(bounded.guard_report, reference.guard_report);
    assert!(budget.work_used() > 2);
    assert!(take_held_fold_sites().is_empty());
    assert_eq!(take_guard_discharge_report(), GuardDischargeReport::default());
}

#[test]
fn cancellation_after_fold_recording_discards_outputs_and_releases_session() {
    let source = held_integer_fold();
    let mut work = 0;
    let mut cancel = || HELD_FOLD_SITES.with(|sites| !sites.borrow().is_empty());
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    let result = lower_storage_test_body(&source, &mut budget);
    assert!(matches!(
        result,
        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
    ));
    assert!(budget.work_used() > 2, "successful earlier reservations remain charged");
    assert!(take_held_fold_sites().is_empty());
    assert_eq!(take_guard_discharge_report(), GuardDischargeReport::default());
    let mut next_work = 0;
    let mut never_cancel = || false;
    let mut next_budget =
        ReflectedCodecBudget::new(&mut next_work, 100_000, 1_000_000, &mut never_cancel);
    let next = lower_storage_test_body(&source, &mut next_budget)
        .expect("next request is admitted after cancellation");
    assert_eq!(next.folds.len(), 1);
    assert_eq!(next.folds[0].site_index, 0);
    assert!(take_held_fold_sites().is_empty());
}

#[test]
fn roster_reservation_refuses_before_advancing_and_polls_between_items() {
    for limit_first in [true, false] {
        let advances = Cell::new(0);
        let mut cancel = || !limit_first && advances.get() == 1;
        let mut work = 0;
        let bytes = if limit_first { 516 } else { 4096 };
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, bytes, &mut cancel);
        {
            let mut reserve = |units, bytes| {
                budget
                    .charge(units, bytes)
                    .map_err(RholangAstLowerError::Preparation)
            };
            let source = Proc::PZero;
            let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
            let items = (0..3).inspect(|_| advances.set(advances.get() + 1));
            assert_eq!(
                stacks.collect_roster(3, items),
                Err(RholangAstLowerError::Preparation(if limit_first {
                    DynamicReflectionError::PayloadByteLimit
                } else {
                    DynamicReflectionError::Cancelled
                }))
            );
            assert_eq!(advances.get(), if limit_first { 0 } else { 1 });
            assert_eq!(stacks.value_count(), 0);
            assert!(matches!(
                stacks.inner.pop(Stacks::classify).expect("unchanged job"),
                Some(Job::Proc(Proc::PZero, _))
            ));
        }
        assert_eq!(budget.work_used(), if limit_first { 2 } else { 5 });
        assert_eq!(budget.remaining_bytes(), bytes - if limit_first { 516 } else { 528 });
    }
}

#[test]
fn roster_exact_bound_keeps_order_and_excess_never_grows_storage() {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 9, 544, &mut cancel);
    {
        let mut reserve = |units, bytes| {
            budget
                .charge(units, bytes)
                .map_err(RholangAstLowerError::Preparation)
        };
        let source = Proc::PZero;
        let mut stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
        assert_eq!(stacks.collect_roster(4, [7, 9, 7, 11]), Ok(vec![7, 9, 7, 11]));
        assert_eq!(stacks.collect_roster(0, std::iter::empty::<u8>()), Ok(vec![]));
        assert!(matches!(
            stacks.collect_roster(3, [1, 2, 3, 4]),
            Err(RholangAstLowerError::UnsupportedProc(
                "lowering roster exceeds its reserved source bound"
            ))
        ));
    }
    assert_eq!(budget.work_used(), 9);
    assert_eq!(budget.remaining_bytes(), 0);
}

#[test]
fn bounded_roster_families_preserve_existing_construction_bytes() {
    fn integer(n: i64) -> Proc {
        Proc::CastInt(Arc::new(Int::NumLit(n)))
    }
    let mut bag = mettail_runtime::HashBag::new();
    for n in [3, 1, 3] {
        bag.insert(integer(n));
    }
    let mut set = mettail_runtime::HashSetLit::new();
    for n in [3, 1] {
        set.insert(integer(n));
    }
    let mut map = mettail_runtime::HashMapLit::new();
    map.insert(integer(3), integer(1));
    map.insert(integer(2), integer(4));
    let sources = [
        Proc::PPar(bag.clone()),
        Proc::CastBag(Arc::new(Bag::BagLit(bag))),
        Proc::CastSet(Arc::new(Set::SetLit(set))),
        Proc::CastMap(Arc::new(Map::MapLit(map))),
        Proc::Matches(
            Arc::new(integer(1)),
            Arc::new(Proc::SpatialPPar(Arc::new(integer(1)), Arc::new(integer(2)))),
        ),
    ];
    for source in sources {
        let reference =
            session::lower_public_body(&source, BoundEnv::new()).expect("existing family");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
        let bounded = lower_storage_test_body(&source, &mut budget).expect("same paid family");
        assert_eq!(bounded.par.encode_to_vec(), reference.par.encode_to_vec());
        assert!(bounded.folds.is_empty());
        assert_eq!(bounded.guard_report, reference.guard_report);
    }
}

#[test]
fn empty_context_is_paid_once_and_cached_only_after_success() {
    for admission in [SourceAdmissionMode::Public, SourceAdmissionMode::Harness] {
        let mut root = BoundEnv::with_options(LoweringOptions::NO_DISCHARGE);
        root.admission = admission;
        root.scope_width = 1;
        root.hole_binders.insert("outer".into(), 0);
        root.free_vars_are_patterns = true;
        let nodes = Arena::new();
        let source = Proc::PZero;
        let cancelled = Cell::new(false);
        let mut cancel = || cancelled.get();
        let mut work = 0;
        // Exactly the initial stacks/seed plus one empty environment record.
        let mut budget = ReflectedCodecBudget::new(&mut work, 3, 520, &mut cancel);
        {
            let mut reserve = |work, units| {
                budget
                    .charge(work, units)
                    .map_err(RholangAstLowerError::Preparation)
            };
            let stacks = Stacks::new(Job::Proc(&source, ROOT_ENV), &mut reserve).expect("seed");
            let mut drive = Drive {
                arena: &nodes,
                envs: EnvArena::new(&root),
                stacks,
                pattern_states: Vec::new(),
                empty_env: None,
                source_preparation: SourcePreparation::Original,
            };
            cancelled.set(true);
            assert_eq!(
                drive.empty_env(),
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            );
            assert!(drive.empty_env.is_none());
            assert!(drive.envs.derived.is_empty());
            cancelled.set(false);
            let id = drive.empty_env().expect("paid empty context");
            let empty = drive.env(id);
            assert_eq!(empty.scope_width, 0);
            assert!(empty.binders.is_empty());
            assert!(empty.hole_binders.is_empty());
            assert_eq!(empty.admission, admission);
            match admission {
                SourceAdmissionMode::Public => {
                    assert_eq!(empty.options, root.options);
                    assert!(empty.free_vars_are_patterns);
                    assert!(Arc::ptr_eq(&empty.resolver, &root.resolver));
                    assert!(Arc::ptr_eq(&empty.caller_imports, &root.caller_imports));
                },
                SourceAdmissionMode::Harness => {
                    assert_eq!(empty.options, LoweringOptions::PRODUCTION);
                    assert!(!empty.free_vars_are_patterns);
                },
            }
            // Reusing a cached identifier performs no new helper or allocation.
            cancelled.set(true);
            assert_eq!(drive.empty_env().expect("existing context"), id);
            assert_eq!(drive.envs.derived.len(), 1);
            assert_eq!(root.hole_binders.get("outer"), Some(&0));
        }
        assert_eq!(budget.work_used(), 3);
        assert_eq!(budget.remaining_bytes(), 0);
    }
}
