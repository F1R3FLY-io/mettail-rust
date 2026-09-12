use super::*;
use crate::{BindingFailure, NativeComparisonFailure};
use proptest::prelude::*;
use std::cell::RefCell;

type Failure = NativeComparisonFailure<()>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Reserve(usize, usize),
    Compare(CollectionCmpRole, *const (), *const ()),
}

fn compare(role: CollectionCmpRole, left: *const (), right: *const ()) -> Ordering {
    // Every caller retains its i32/String source arena through both executions.
    unsafe {
        match role {
            CollectionCmpRole::Primary => (&*left.cast::<i32>()).cmp(&*right.cast::<i32>()),
            CollectionCmpRole::Secondary => (&*left.cast::<String>()).cmp(&*right.cast::<String>()),
        }
    }
}

fn ordinary(
    lead: Ordering,
    left: &[CollectionCmpItem],
    right: &[CollectionCmpItem],
) -> (Ordering, Vec<Event>) {
    let mut machine = CollectionCmpPda::new(lead, left.to_vec(), right.to_vec());
    let mut result = None;
    let mut trace = Vec::new();
    loop {
        match machine.resume(result.take()) {
            CollectionCmpStep::Compare { role, left, right } => {
                trace.push(Event::Compare(role, left, right));
                result = Some(compare(role, left, right));
            },
            CollectionCmpStep::Done(ordering) => return (ordering, trace),
        }
    }
}

fn roster(
    items: &[CollectionCmpItem],
    reserve: &mut impl FnMut(usize, usize) -> Result<(), ()>,
) -> Result<CheckedCmpRoster, Failure> {
    let mut result = CheckedCmpRoster::try_with_capacity(items.len(), reserve)?;
    for item in items {
        // The same live source addresses are supplied to ordinary().
        unsafe {
            let primary = &*item.primary.cast::<i32>();
            match item.secondary {
                Some(secondary) => {
                    result.try_push_pair(primary, &*secondary.cast::<String>(), reserve)?
                },
                None if item.repetitions == 1 => result.try_push_unary(primary, reserve)?,
                None => result.try_push_repeated(primary, item.repetitions, reserve)?,
            }
        }
    }
    Ok(result)
}

fn checked(
    lead: Ordering,
    left: &[CollectionCmpItem],
    right: &[CollectionCmpItem],
    events: &RefCell<Vec<Event>>,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), ()>,
) -> Result<Ordering, Failure> {
    let left = roster(left, reserve)?;
    let right = roster(right, reserve)?;
    let mut machine = CheckedCollectionCmpPda::try_new(lead, left, right, reserve)?;
    let mut result = None;
    loop {
        match machine.try_resume(result.take(), reserve)? {
            CheckedCollectionCmpStep::Compare { machine: next, role, left, right } => {
                events.borrow_mut().push(Event::Compare(role, left, right));
                result = Some(compare(role, left, right));
                machine = next;
            },
            CheckedCollectionCmpStep::Done(ordering) => return Ok(ordering),
        }
    }
}

fn parity(
    lead: Ordering,
    left: &[CollectionCmpItem],
    right: &[CollectionCmpItem],
    all_cutpoints: bool,
) -> Ordering {
    let (expected, requests) = ordinary(lead, left, right);
    let events = RefCell::new(Vec::new());
    let result = checked(lead, left, right, &events, &mut |w, u| {
        events.borrow_mut().push(Event::Reserve(w, u));
        Ok(())
    });
    assert_eq!(result, Ok(expected));
    let baseline = events.into_inner();
    assert_eq!(
        baseline
            .iter()
            .filter(|e| matches!(e, Event::Compare(..)))
            .cloned()
            .collect::<Vec<_>>(),
        requests
    );
    if all_cutpoints {
        for (end, event) in baseline.iter().enumerate() {
            if !matches!(event, Event::Reserve(..)) {
                continue;
            }
            let events = RefCell::new(Vec::new());
            let result = checked(lead, left, right, &events, &mut |w, u| {
                let mut trace = events.borrow_mut();
                trace.push(Event::Reserve(w, u));
                if trace.len() == end + 1 {
                    Err(())
                } else {
                    Ok(())
                }
            });
            assert_eq!(result, Err(Failure::Admission(BindingFailure::Reservation(()))));
            assert_eq!(&*events.borrow(), &baseline[..=end], "refusal at event {end}");
        }
        let (work, units) = baseline.iter().fold((0, 0), |(w, u), event| match event {
            Event::Reserve(dw, du) => (w + dw, u + du),
            _ => (w, u),
        });
        for (work_limit, unit_limit, succeeds) in
            [(work, units, true), (work - 1, units, false), (work, units - 1, false)]
        {
            let (mut remaining_work, mut remaining_units) = (work_limit, unit_limit);
            let events = RefCell::new(Vec::new());
            let result = checked(lead, left, right, &events, &mut |w, u| {
                if w > remaining_work || u > remaining_units {
                    return Err(());
                }
                remaining_work -= w;
                remaining_units -= u;
                Ok(())
            });
            if succeeds {
                assert_eq!(result, Ok(expected));
                assert_eq!((remaining_work, remaining_units), (0, 0));
            } else {
                assert_eq!(result, Err(Failure::Admission(BindingFailure::Reservation(()))));
            }
        }
    }
    expected
}

fn unary(values: &[i32]) -> Vec<CollectionCmpItem> {
    values.iter().map(CollectionCmpItem::unary).collect()
}

#[test]
fn map_producer_preserves_pairs_without_key_operations_at_every_budget_boundary() {
    use std::hash::{Hash, Hasher};
    use std::sync::atomic::{AtomicBool, Ordering as MemoryOrder};
    use std::sync::Arc;
    struct Key {
        id: usize,
        frozen: Arc<AtomicBool>,
    }
    impl PartialEq for Key {
        fn eq(&self, other: &Self) -> bool {
            assert!(!self.frozen.load(MemoryOrder::Relaxed), "producer invoked key equality");
            self.id == other.id
        }
    }
    impl Eq for Key {}
    impl Hash for Key {
        fn hash<H: Hasher>(&self, state: &mut H) {
            assert!(!self.frozen.load(MemoryOrder::Relaxed), "producer invoked key hashing");
            self.id.hash(state);
        }
    }
    // Neither key nor value implements Clone/Ord; value has no Eq/Hash either.
    struct Value(String);
    for width in 0..8 {
        let frozen = Arc::new(AtomicBool::new(false));
        let mut map = crate::HashMapLit::new();
        for id in (0..width).rev() {
            map.insert(Key { id, frozen: Arc::clone(&frozen) }, Value(format!("value-{id}")));
        }
        frozen.store(true, MemoryOrder::Relaxed);
        let mut trace = Vec::new();
        let roster = map
            .try_comparison_roster(&mut |w, u| {
                trace.push((w, u));
                Ok::<_, ()>(())
            })
            .expect("unlimited map roster");
        assert_eq!(
            (roster.items.len(), roster.reserved_width, roster.total),
            (width, width, width)
        );
        for (item, (key, value)) in roster.items.iter().zip(map.iter()) {
            assert_eq!(item.primary, key as *const Key as *const ());
            assert_eq!(item.secondary, Some(value as *const Value as *const ()));
            assert_eq!(item.repetitions, 1);
            assert_eq!(value.0, format!("value-{}", key.id));
        }
        assert_eq!(trace.len(), 2 * width + 5);
        let total = trace
            .iter()
            .fold((0, 0), |(w, u), (dw, du)| (w + dw, u + du));
        assert_eq!(total, (4 * width + 6, 4 * (width + 1)));
        for stop in 0..trace.len() {
            let mut actual = Vec::new();
            let result = map.try_comparison_roster(&mut |w, u| {
                actual.push((w, u));
                if actual.len() == stop + 1 {
                    Err(())
                } else {
                    Ok(())
                }
            });
            assert_eq!(result.err(), Some(Failure::Admission(BindingFailure::Reservation(()))));
            assert_eq!(actual, trace[..=stop]);
        }
        for (work, units, succeeds) in [
            (total.0, total.1, true),
            (total.0 - 1, total.1, false),
            (total.0, total.1 - 1, false),
        ] {
            let (mut remaining_work, mut remaining_units) = (work, units);
            let result = map.try_comparison_roster(&mut |w, u| {
                if w > remaining_work || u > remaining_units {
                    return Err(());
                }
                remaining_work -= w;
                remaining_units -= u;
                Ok(())
            });
            if succeeds {
                assert_eq!(result.expect("exact map allowance").total, width);
                assert_eq!((remaining_work, remaining_units), (0, 0));
            } else {
                assert_eq!(result.err(), Some(Failure::Admission(BindingFailure::Reservation(()))));
            }
        }
        assert_eq!(
            map.iter().map(|(key, _)| key.id).collect::<Vec<_>>(),
            (0..width).rev().collect::<Vec<_>>()
        );
    }
}

fn charges(
    lead: Ordering,
    left: &[CollectionCmpItem],
    right: &[CollectionCmpItem],
) -> Vec<(usize, usize)> {
    let events = RefCell::new(Vec::new());
    checked(lead, left, right, &events, &mut |w, u| {
        events.borrow_mut().push(Event::Reserve(w, u));
        Ok(())
    })
    .expect("unlimited checked fixture succeeds");
    events
        .into_inner()
        .into_iter()
        .filter_map(|event| match event {
            Event::Reserve(w, u) => Some((w, u)),
            _ => None,
        })
        .collect()
}

#[test]
fn empty_and_multirun_paths_pin_independent_reservation_totals() {
    assert!(crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let empty = charges(Ordering::Equal, &[], &[]);
    assert_eq!(empty.len(), 25);
    assert_eq!(
        empty
            .iter()
            .copied()
            .fold((0, 0), |(w, u), (dw, du)| (w + dw, u + du)),
        (29, 12)
    );
    assert_eq!(
        &empty[..10],
        &[(1, 0), (2, 4), (1, 0), (2, 4), (2, 4), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0)]
    );
    assert_eq!(parity(Ordering::Equal, &[], &[], true), Ordering::Equal);
    for lead in [Ordering::Less, Ordering::Greater] {
        let trace = charges(lead, &[], &[]);
        assert_eq!(trace.len(), 12);
        assert_eq!(
            trace
                .iter()
                .copied()
                .fold((0, 0), |(w, u), (dw, du)| (w + dw, u + du)),
            (15, 12)
        );
        assert_eq!(parity(lead, &[], &[], true), lead);
    }
    // Five records force three merge passes and odd tails. Opposite orders
    // exercise both chosen-copy routes and both tail-copy loops.
    let left = [5, 4, 3, 2, 1];
    let right = [1, 2, 3, 4, 5];
    let (left, right) = (unary(&left), unary(&right));
    assert_eq!(parity(Ordering::Equal, &left, &right, true), Ordering::Equal);
    let allocations: Vec<_> = charges(Ordering::Equal, &left, &right)
        .into_iter()
        .filter(|(_, units)| *units != 0)
        .collect();
    // Input rosters, owner header, then the two lazy scratch buffers.
    assert_eq!(allocations, vec![(12, 24), (12, 24), (2, 4), (12, 24), (12, 24)]);
}

#[test]
fn alias_secondary_and_repeated_run_paths_preserve_the_original_request_trace() {
    let keys = [1, 1, 2, 3, 0];
    let values = [String::from("a"), String::from("b"), String::from("a")];
    let same = CollectionCmpItem::pair(&keys[0], &values[0]);
    let alias = [same; 5];
    assert!(ordinary(Ordering::Equal, &alias, &alias).1.is_empty());
    assert_eq!(parity(Ordering::Equal, &alias, &alias, true), Ordering::Equal);
    let left = [CollectionCmpItem::pair(&keys[0], &values[0])];
    let right = [CollectionCmpItem::pair(&keys[0], &values[1])];
    let trace = ordinary(Ordering::Equal, &left, &right).1;
    assert_eq!(trace.len(), 1);
    assert!(matches!(trace[0], Event::Compare(CollectionCmpRole::Secondary, ..)));
    assert_eq!(parity(Ordering::Equal, &left, &right, true), Ordering::Less);
    let right = [CollectionCmpItem::pair(&keys[1], &values[2])];
    assert_eq!(ordinary(Ordering::Equal, &left, &right).1.len(), 2);
    assert_eq!(parity(Ordering::Equal, &left, &right, true), Ordering::Equal);
    let mixed = [CollectionCmpItem::unary(&keys[0]), same];
    assert_eq!(parity(Ordering::Equal, &mixed, &[same, mixed[0]], true), Ordering::Equal);
    let left = [
        CollectionCmpItem::repeated(&keys[0], 3),
        CollectionCmpItem::repeated(&keys[2], 2),
    ];
    let right = [
        CollectionCmpItem::repeated(&keys[2], 2),
        CollectionCmpItem::unary(&keys[1]),
        CollectionCmpItem::repeated(&keys[0], 2),
    ];
    assert_eq!(parity(Ordering::Equal, &left, &right, true), Ordering::Equal);
    assert_eq!(parity(Ordering::Less, &left, &[], true), Ordering::Less);
    assert_eq!(parity(Ordering::Greater, &[], &right, true), Ordering::Greater);
    assert_eq!(
        parity(
            Ordering::Equal,
            &[CollectionCmpItem::unary(&keys[3])],
            &[CollectionCmpItem::repeated(&keys[4], 10)],
            true
        ),
        Ordering::Greater
    );
    assert!(!std::mem::needs_drop::<CollectionCmpItem>());
    assert_eq!(
        values,
        ["a", "b", "a"].map(String::from),
        "source values survive refused owner cleanup"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]
    #[test]
    fn unary_permutations_keep_exact_requests_and_sorted_results(left in prop::collection::vec(-5i32..6, 0..16), right in prop::collection::vec(-5i32..6, 0..16)) {
        let (left_items, right_items) = (unary(&left), unary(&right));
        let (mut sorted_left, mut sorted_right) = (left.clone(), right.clone());
        sorted_left.sort(); sorted_right.sort();
        prop_assert_eq!(parity(Ordering::Equal, &left_items, &right_items, false), sorted_left.cmp(&sorted_right));
        let reversed: Vec<_> = left_items.iter().rev().copied().collect();
        prop_assert_eq!(parity(Ordering::Equal, &left_items, &reversed, false), Ordering::Equal);
    }
    #[test]
    fn heterogeneous_map_permutations_keep_exact_roles(left in prop::collection::vec((-3i32..4, "[a-c]{0,3}"), 0..12), right in prop::collection::vec((-3i32..4, "[a-c]{0,3}"), 0..12)) {
        let items = |values: &[(i32, String)]| values.iter().map(|(k, v)| CollectionCmpItem::pair(k, v)).collect::<Vec<_>>();
        let (left_items, right_items) = (items(&left), items(&right));
        let (mut sorted_left, mut sorted_right) = (left.clone(), right.clone());
        sorted_left.sort(); sorted_right.sort();
        prop_assert_eq!(parity(Ordering::Equal, &left_items, &right_items, false), sorted_left.cmp(&sorted_right));
        let reversed: Vec<_> = left_items.iter().rev().copied().collect();
        prop_assert_eq!(parity(Ordering::Equal, &left_items, &reversed, false), Ordering::Equal);
    }
    #[test]
    fn repeated_records_keep_exact_requests_and_expanded_results(left in prop::collection::vec((-3i32..4, 1usize..5), 0..12), right in prop::collection::vec((-3i32..4, 1usize..5), 0..12)) {
        let items = |values: &[(i32, usize)]| values.iter().map(|(v, n)| CollectionCmpItem::repeated(v, *n)).collect::<Vec<_>>();
        let expand = |values: &[(i32, usize)]| {
            let mut result: Vec<_> = values.iter().flat_map(|(v, n)| std::iter::repeat_n(*v, *n)).collect();
            result.sort(); result
        };
        prop_assert_eq!(parity(Ordering::Equal, &items(&left), &items(&right), false), expand(&left).cmp(&expand(&right)));
    }
}

#[test]
fn roster_errors_are_paid_atomic_and_never_allocate_overflowing_widths() {
    let value = 7_i32;
    let mut trace = Vec::new();
    let mut reserve = |w, u| {
        trace.push((w, u));
        Ok::<_, ()>(())
    };
    let mut zero = CheckedCmpRoster::try_with_capacity(0, &mut reserve).expect("paid empty roster");
    assert_eq!(
        zero.try_push_repeated(&value, 0, &mut reserve),
        Err(Failure::InvalidCollectionInput("collection comparison items must be present"))
    );
    assert_eq!(
        zero.try_push_unary(&value, &mut reserve),
        Err(Failure::InvalidCollectionInput(
            "collection comparison roster exceeds its reserved width"
        ))
    );
    assert!(zero.items.is_empty());
    assert_eq!(zero.total, 0);
    assert_eq!(trace, vec![(1, 0), (2, 4), (1, 0), (1, 0)]);
    let mut accept = |_, _| Ok::<_, ()>(());
    let mut full = CheckedCmpRoster::try_with_capacity(1, &mut accept).expect("paid unary roster");
    full.try_push_unary(&value, &mut accept)
        .expect("first slot admitted");
    let pointer = full.items[0].primary;
    assert_eq!(
        full.try_push_pair(&value, &String::from("not retained"), &mut accept),
        Err(Failure::InvalidCollectionInput(
            "collection comparison roster exceeds its reserved width"
        ))
    );
    assert_eq!((full.items.len(), full.total, full.items[0].primary), (1, 1, pointer));
    let mut sum =
        CheckedCmpRoster::try_with_capacity(2, &mut accept).expect("paid two-slot roster");
    sum.try_push_repeated(&value, usize::MAX, &mut accept)
        .expect("one compressed maximal run");
    assert_eq!(
        sum.try_push_unary(&value, &mut accept),
        Err(Failure::Admission(BindingFailure::SizeOverflow))
    );
    assert_eq!((sum.items.len(), sum.total), (1, usize::MAX));
    for width in [usize::MAX, usize::MAX / 2, usize::MAX / 4] {
        let mut trace = Vec::new();
        let result = CheckedCmpRoster::try_with_capacity(width, &mut |w, u| {
            trace.push((w, u));
            Ok::<_, ()>(())
        });
        assert_eq!(result.err(), Some(Failure::Admission(BindingFailure::SizeOverflow)));
        assert_eq!(trace, vec![(1, 0)], "arithmetic precedes allocation");
    }
    let slots = usize::MAX / 4;
    let mut trace = Vec::new();
    let result = CheckedCmpRoster::try_with_capacity(slots - 1, &mut |w, u| {
        trace.push((w, u));
        if trace.len() == 2 {
            Err(())
        } else {
            Ok(())
        }
    });
    assert_eq!(result.err(), Some(Failure::Admission(BindingFailure::Reservation(()))));
    assert_eq!(trace, vec![(1, 0), (2 * slots, 4 * slots)]);
    // Multiplicity is a run, not expanded into slots.
    let repeated = [CollectionCmpItem::repeated(&value, usize::MAX)];
    assert_eq!(parity(Ordering::Equal, &repeated, &repeated, true), Ordering::Equal);
}

#[test]
fn consuming_protocol_errors_do_not_publish_results_or_touch_source_values() {
    let values = [1_i32, 2];
    let mut accept = |_, _| Ok::<_, ()>(());
    let fresh = || {
        let mut reserve = |_, _| Ok::<_, ()>(());
        let left = roster(&unary(&values[..1]), &mut reserve).expect("left roster");
        let right = roster(&unary(&values[1..]), &mut reserve).expect("right roster");
        CheckedCollectionCmpPda::try_new(Ordering::Equal, left, right, &mut reserve)
            .expect("paid owner")
    };
    let mut trace = Vec::new();
    let result = fresh().try_resume(Some(Ordering::Equal), &mut |w, u| {
        trace.push((w, u));
        Ok::<_, ()>(())
    });
    assert_eq!(
        result.err(),
        Some(Failure::InvalidCollectionInput(
            "collection comparison PDA received an unrequested result"
        ))
    );
    assert_eq!(trace, vec![(1, 0)]);
    let requested = match fresh()
        .try_resume(None, &mut accept)
        .expect("first request")
    {
        CheckedCollectionCmpStep::Compare { machine, role, left, right } => {
            assert_eq!(role, CollectionCmpRole::Primary);
            assert_eq!(left, &values[0] as *const i32 as *const ());
            assert_eq!(right, &values[1] as *const i32 as *const ());
            machine
        },
        CheckedCollectionCmpStep::Done(_) => panic!("distinct singleton sources require a result"),
    };
    let mut trace = Vec::new();
    let result = requested.try_resume(None, &mut |w, u| {
        trace.push((w, u));
        Ok::<_, ()>(())
    });
    assert_eq!(
        result.err(),
        Some(Failure::InvalidCollectionInput(
            "collection comparison PDA resumed without its requested result"
        ))
    );
    assert_eq!(trace, vec![(1, 0)]);
    assert_eq!(values, [1, 2]);
    // Partial filling is valid ownership, not source-iteration completeness.
    let left = CheckedCmpRoster::try_with_capacity(3, &mut accept).expect("partial left roster");
    let right = CheckedCmpRoster::try_with_capacity(2, &mut accept).expect("partial right roster");
    let machine = CheckedCollectionCmpPda::try_new(Ordering::Equal, left, right, &mut accept)
        .expect("partial owner");
    assert!(matches!(
        machine.try_resume(None, &mut accept),
        Ok(CheckedCollectionCmpStep::Done(Ordering::Equal))
    ));
    // Done carries no machine: resuming it is unrepresentable through this API.
}

#[test]
fn wide_collection_sort_and_refusal_cleanup_fit_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let left: Vec<i32> = (0..20_000).rev().collect();
            let right: Vec<i32> = (0..20_000).collect();
            let run = |stop: Option<usize>| {
                let mut calls = 0;
                let mut reserve = |_, _| {
                    let current = calls;
                    calls += 1;
                    if Some(current) == stop {
                        Err(())
                    } else {
                        Ok(())
                    }
                };
                let outcome = (|| -> Result<Ordering, Failure> {
                    let mut lhs = CheckedCmpRoster::try_with_capacity(left.len(), &mut reserve)?;
                    let mut rhs = CheckedCmpRoster::try_with_capacity(right.len(), &mut reserve)?;
                    for value in &left {
                        lhs.try_push_unary(value, &mut reserve)?;
                    }
                    for value in &right {
                        rhs.try_push_unary(value, &mut reserve)?;
                    }
                    let mut machine =
                        CheckedCollectionCmpPda::try_new(Ordering::Equal, lhs, rhs, &mut reserve)?;
                    let mut result = None;
                    loop {
                        match machine.try_resume(result.take(), &mut reserve)? {
                            CheckedCollectionCmpStep::Compare {
                                machine: next,
                                role,
                                left,
                                right,
                            } => {
                                assert_eq!(role, CollectionCmpRole::Primary);
                                result = Some(compare(role, left, right));
                                machine = next;
                            },
                            CheckedCollectionCmpStep::Done(ordering) => return Ok(ordering),
                        }
                    }
                })();
                (outcome, calls)
            };
            let (result, calls) = run(None);
            assert_eq!(result, Ok(Ordering::Equal));
            for stop in [0, calls / 2, calls - 1] {
                assert_eq!(
                    run(Some(stop)),
                    (Err(Failure::Admission(BindingFailure::Reservation(()))), stop + 1)
                );
            }
            assert_eq!(left.first(), Some(&19_999));
            assert_eq!(right.last(), Some(&19_999));
        })
        .expect("spawn small-stack collection check")
        .join()
        .expect("wide checked sort and normal error cleanup remain stack-safe");
}
