use super::*;
use crate::{BindingFailure, CheckedCmpRoster, NativeComparisonFailure};
use std::cell::Cell;
use std::rc::Rc;

#[derive(Debug)]
struct CountedKey {
    id: usize,
    calls: Rc<Cell<(usize, usize, usize)>>,
}

impl Clone for CountedKey {
    fn clone(&self) -> Self {
        let (hash, eq, clone) = self.calls.get();
        self.calls.set((hash, eq, clone + 1));
        Self {
            id: self.id,
            calls: Rc::clone(&self.calls),
        }
    }
}

impl Hash for CountedKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let (hash, eq, clone) = self.calls.get();
        self.calls.set((hash + 1, eq, clone));
        0usize.hash(state);
    }
}

impl PartialEq for CountedKey {
    fn eq(&self, other: &Self) -> bool {
        let (hash, eq, clone) = self.calls.get();
        self.calls.set((hash, eq + 1, clone));
        self.id == other.id
    }
}
impl Eq for CountedKey {}

fn allow(_: usize, _: usize) -> Result<(), &'static str> {
    Ok(())
}

fn original_roster<T: Clone + Hash + Eq>(bag: &HashBag<T>) -> CheckedCmpRoster {
    let mut roster = CheckedCmpRoster::try_with_capacity(bag.distinct_len(), &mut allow)
        .expect("supported-profile oracle roster");
    for (key, count) in bag.iter() {
        roster
            .try_push_repeated(key, count, &mut allow)
            .expect("positive native count");
    }
    roster
}

#[test]
fn borrowed_roster_keeps_sparse_native_order_counts_and_original_pointers_without_key_calls() {
    let calls = Rc::new(Cell::new((0, 0, 0)));
    let mut bag = HashBag::new();
    for id in 0..128 {
        bag.insert_n(CountedKey { id, calls: Rc::clone(&calls) }, id % 3 + 1);
    }
    for id in 0..120 {
        let key = CountedKey { id, calls: Rc::clone(&calls) };
        for _ in 0..id % 3 + 1 {
            assert!(bag.remove(&key));
        }
    }
    assert!(bag.historical_capacity() > bag.counts.capacity());
    let before: Vec<_> = bag
        .iter()
        .map(|(key, count)| (key as *const _, count))
        .collect();
    calls.set((0, 0, 0));
    let actual = bag.try_comparison_roster(&mut allow);
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        assert!(matches!(actual, Err(NativeComparisonFailure::UnsupportedProfile)));
        assert_eq!(calls.get(), (0, 0, 0));
        return;
    }
    let actual = actual.expect("paid original borrowed roster");
    let expected = original_roster(&bag);
    // Derived Debug includes every ordered pointer/count record and stored roster total.
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(calls.get(), (0, 0, 0));
    assert_eq!(
        before,
        bag.iter()
            .map(|(key, count)| (key as *const _, count))
            .collect::<Vec<_>>()
    );
}

#[test]
fn borrowed_roster_reserves_every_stage_and_stops_at_each_refusal() {
    let mut bag = HashBag::new();
    bag.insert_n(1usize, 2);
    bag.insert_n(2, 3);
    let mut requests = Vec::new();
    let result = bag.try_comparison_roster(&mut |work, units| {
        requests.push((work, units));
        Ok::<_, &'static str>(())
    });
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        assert!(matches!(result, Err(NativeComparisonFailure::UnsupportedProfile)));
        assert!(requests.is_empty());
        return;
    }
    result.expect("unlimited roster baseline");
    let width = bag.distinct_len();
    let extent = (2 * bag.historical_capacity()).max(1);
    let groups = 1 + (extent - 1) / 16;
    let mut expected =
        vec![(1, 0), (1, 0), (2 * (width + 1), 4 * (width + 1)), (4 * width + 19 * groups, 0)];
    for _ in 0..width {
        expected.extend([(1, 0), (1, 0)]);
    }
    expected.push((1, 0));
    assert_eq!(requests, expected);
    for rejected in 0..requests.len() {
        let mut seen = Vec::new();
        let result = bag.try_comparison_roster(&mut |work, units| {
            seen.push((work, units));
            if seen.len() == rejected + 1 {
                Err("cut")
            } else {
                Ok(())
            }
        });
        assert!(matches!(
            result,
            Err(NativeComparisonFailure::Admission(BindingFailure::Reservation("cut")))
        ));
        assert_eq!(seen, requests[..=rejected]);
        assert_eq!(bag.len(), 5);
        assert_eq!(bag.count(&1), 2);
        assert_eq!(bag.count(&2), 3);
    }
}

#[test]
fn borrowed_roster_accepts_exact_work_and_retention_but_rejects_one_under() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    for width in [0usize, 1, 17] {
        let bag: HashBag<_> = (0..width).collect();
        let mut total = (0usize, 0usize);
        bag.try_comparison_roster(&mut |work, units| {
            total.0 += work;
            total.1 += units;
            Ok::<_, &'static str>(())
        })
        .expect("collect exact reservation census");
        for (work_limit, units_limit, succeeds) in [
            (total.0, total.1, true),
            (total.0 - 1, total.1, false),
            (total.0, total.1 - 1, false),
        ] {
            let mut remaining = (work_limit, units_limit);
            let result = bag.try_comparison_roster(&mut |work, units| {
                if work > remaining.0 || units > remaining.1 {
                    return Err("limit");
                }
                remaining.0 -= work;
                remaining.1 -= units;
                Ok(())
            });
            if succeeds {
                result.expect("exact allowance succeeds");
                assert_eq!(remaining, (0, 0));
            } else {
                assert!(matches!(
                    result,
                    Err(NativeComparisonFailure::Admission(BindingFailure::Reservation("limit")))
                ));
            }
            assert_eq!(bag.distinct_len(), width);
        }
    }
}

#[test]
fn borrowed_roster_handles_empty_allocated_history_and_refuses_stored_zero_counts() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    let mut source: HashBag<_> = (0usize..64).collect();
    for key in 0..64 {
        assert!(source.remove(&key));
    }
    assert!(source.historical_capacity() > 0);
    let actual = source
        .try_comparison_roster(&mut allow)
        .expect("allocated empty roster");
    assert_eq!(format!("{actual:?}"), format!("{:?}", original_roster(&source)));
    source.insert_n(7, 9);
    let zero = source.rebuild_binding_entries([(7, 0)]);
    assert_eq!(zero.len(), 9);
    assert_eq!(zero.distinct_len(), 1);
    assert!(matches!(
        zero.try_comparison_roster(&mut allow),
        Err(NativeComparisonFailure::InvalidCollectionInput(_))
    ));
    assert_eq!(zero.iter().next(), Some((&7, 0)));
    let overflowing = source.rebuild_binding_entries([(7, usize::MAX), (8, 1)]);
    assert!(matches!(
        overflowing.try_comparison_roster(&mut allow),
        Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))
    ));
    assert_eq!(overflowing.len(), 9);
    assert_eq!(overflowing.distinct_len(), 2);
}

#[test]
fn borrowed_roster_does_not_substitute_transported_total_for_repetitions() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    let mut source = HashBag::new();
    source.insert_n(1usize, 9);
    let rebuilt = source.rebuild_binding_entries([(1, 2), (1, 3)]);
    assert_eq!(rebuilt.len(), 9);
    assert_eq!(rebuilt.iter().map(|(_, count)| count).sum::<usize>(), 3);
    let actual = rebuilt
        .try_comparison_roster(&mut allow)
        .expect("anomalous total is separate");
    assert_eq!(format!("{actual:?}"), format!("{:?}", original_roster(&rebuilt)));
    assert_eq!(rebuilt.len(), 9);
}

#[test]
fn borrowed_scan_allowance_checks_each_arithmetic_boundary() {
    assert_eq!(borrowed_scan_work_allowance::<()>(0, 0), Ok(19));
    assert_eq!(borrowed_scan_work_allowance::<()>(1, 0), Ok(23));
    assert_eq!(borrowed_scan_work_allowance::<()>(0, 8), Ok(19));
    assert_eq!(borrowed_scan_work_allowance::<()>(0, 9), Ok(38));
    for (width, history) in [(usize::MAX, 0), (0, usize::MAX), (0, usize::MAX / 2)] {
        assert!(matches!(
            borrowed_scan_work_allowance::<()>(width, history),
            Err(BindingFailure::SizeOverflow)
        ));
    }
    let safe_width = (usize::MAX - 19) / 4;
    assert!(borrowed_scan_work_allowance::<()>(safe_width, 0).is_ok());
    assert!(matches!(
        borrowed_scan_work_allowance::<()>(safe_width + 1, 0),
        Err(BindingFailure::SizeOverflow)
    ));
}

#[test]
fn entry_visitor_preserves_sparse_original_borrows_without_key_operations() {
    let calls = Rc::new(Cell::new((0, 0, 0)));
    let mut bag = HashBag::new();
    for id in 0..128 {
        bag.insert(CountedKey { id, calls: Rc::clone(&calls) });
    }
    for id in 0..120 {
        assert!(bag.remove(&CountedKey { id, calls: Rc::clone(&calls) }));
    }
    assert!(bag.historical_capacity() > bag.counts.capacity());
    let original: Vec<_> = bag
        .iter()
        .map(|(key, count)| (key as *const _, count))
        .collect();
    let mut borrowed = Vec::with_capacity(bag.distinct_len());
    calls.set((0, 0, 0));
    let result = bag.try_for_each_entry(&mut allow, |key, count, _| {
        // This test records observations; production visitors admit their
        // independently owned task/storage effects through the given callback.
        borrowed.push((key, count));
        Ok(())
    });
    if crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        result.expect("paid source scan");
        assert_eq!(
            borrowed
                .iter()
                .map(|(key, count)| (*key as *const _, *count))
                .collect::<Vec<_>>(),
            original
        );
    } else {
        assert_eq!(result, Err(BindingFailure::UnsupportedProfile));
        assert!(borrowed.is_empty());
    }
    assert_eq!(calls.get(), (0, 0, 0));
    assert_eq!(
        bag.iter()
            .map(|(key, count)| (key as *const _, count))
            .collect::<Vec<_>>(),
        original
    );
}

#[test]
fn entry_visitor_keeps_zero_counts_and_overflowing_sums_without_normalization() {
    let mut source = HashBag::new();
    source.insert_n(1usize, 9);
    let bag = source.rebuild_binding_entries([(1, 0), (2, usize::MAX), (3, 1)]);
    let expected: Vec<_> = bag.iter().collect();
    let mut visited = Vec::with_capacity(bag.distinct_len());
    let result = bag.try_for_each_entry(&mut allow, |key, count, _| {
        visited.push((key, count));
        Ok(())
    });
    if crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        result.expect("entry scan does not validate comparison repetitions");
        assert_eq!(visited, expected);
    } else {
        assert_eq!(result, Err(BindingFailure::UnsupportedProfile));
        assert!(visited.is_empty());
    }
    assert_eq!(bag.len(), 9);
    assert_eq!(bag.distinct_len(), 3);
    assert_eq!(bag.count(&1), 0);
    assert_eq!(bag.count(&2), usize::MAX);
    assert_eq!(bag.count(&3), 1);
}

#[test]
fn entry_visitor_shares_admission_and_stops_at_every_scan_or_visitor_refusal() {
    for width in [0usize, 1, 17] {
        let bag: HashBag<_> = (0..width).collect();
        let mut requests = Vec::new();
        let mut visited = 0;
        let result = bag.try_for_each_entry(
            &mut |work, units| {
                requests.push((work, units));
                Ok::<_, &'static str>(())
            },
            |_, _, reserve| {
                crate::reserve_binding_parts(2, 0, 0, reserve)?;
                visited += 1;
                Ok(())
            },
        );
        if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
            assert_eq!(result, Err(BindingFailure::UnsupportedProfile));
            assert!(requests.is_empty());
            assert_eq!(visited, 0);
            continue;
        }
        result.expect("entry visitor baseline");
        let groups = 1 + ((2 * bag.historical_capacity()).max(1) - 1) / 16;
        let mut expected = vec![(1, 0), (4 * width + 19 * groups, 0)];
        for _ in 0..width {
            expected.extend([(1, 0), (2, 0)]);
        }
        expected.push((1, 0));
        assert_eq!(requests, expected);
        assert_eq!(visited, width);
        for stop in 0..requests.len() {
            let mut seen = Vec::new();
            let mut successful_visits = 0;
            let mut attempted_visits = 0;
            let result = bag.try_for_each_entry(
                &mut |work, units| {
                    seen.push((work, units));
                    if seen.len() == stop + 1 {
                        Err("cut")
                    } else {
                        Ok(())
                    }
                },
                |_, _, reserve| {
                    attempted_visits += 1;
                    crate::reserve_binding_parts(2, 0, 0, reserve)?;
                    successful_visits += 1;
                    Ok(())
                },
            );
            assert_eq!(result, Err(BindingFailure::Reservation("cut")));
            assert_eq!(seen, requests[..=stop]);
            assert_eq!(
                successful_visits,
                requests[..stop]
                    .iter()
                    .filter(|(work, _)| *work == 2)
                    .count()
            );
            assert_eq!(
                attempted_visits,
                requests[..=stop]
                    .iter()
                    .filter(|(work, _)| *work == 2)
                    .count()
            );
        }
        let exact: usize = requests.iter().map(|(work, _)| work).sum();
        for limit in [0, exact - 1, exact] {
            let mut remaining = limit;
            let result = bag.try_for_each_entry(
                &mut |work, units| {
                    assert_eq!(units, 0);
                    remaining = remaining.checked_sub(work).ok_or("limit")?;
                    Ok(())
                },
                |_, _, reserve| crate::reserve_binding_parts(2, 0, 0, reserve),
            );
            if limit == exact {
                result.expect("exact work allowance");
                assert_eq!(remaining, 0);
            } else {
                assert_eq!(result, Err(BindingFailure::Reservation("limit")));
            }
        }
        assert_eq!(bag.distinct_len(), width);
    }
}
