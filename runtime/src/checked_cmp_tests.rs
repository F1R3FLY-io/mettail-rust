use super::*;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Debug;

type TestFailure = NativeComparisonFailure<usize>;
type Reservation<'a> = dyn FnMut(usize, usize) -> Result<(), usize> + 'a;

fn check_operation<R: Copy + Debug + Eq>(
    expected: R,
    execution_work: usize,
    mut run: impl FnMut(&mut Reservation<'_>) -> Result<R, TestFailure>,
) {
    let expected_trace = [(1, 0), (execution_work, 0)];
    let mut trace = Vec::new();
    assert_eq!(
        run(&mut |work, units| {
            trace.push((work, units));
            Ok(())
        }),
        Ok(expected)
    );
    assert_eq!(trace, expected_trace);
    for stop in 0..2 {
        let mut seen = Vec::new();
        let mut spent = 0usize;
        let result = run(&mut |work, units| {
            let index = seen.len();
            seen.push((work, units));
            if index == stop {
                Err(stop)
            } else {
                spent = spent.checked_add(work).expect("fixture work fits usize");
                Ok(())
            }
        });
        assert_eq!(
            result,
            Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(stop)))
        );
        assert_eq!(seen, expected_trace[..=stop]);
        assert_eq!(spent, stop);
    }
    let exact = execution_work
        .checked_add(1)
        .expect("fixture total fits usize");
    for limit in [0, 1, exact - 1, exact] {
        let mut remaining = limit;
        let mut calls = 0;
        let result = run(&mut |work, units| {
            calls += 1;
            assert_eq!(units, 0, "comparison creates no retained payload");
            remaining = remaining.checked_sub(work).ok_or(limit)?;
            Ok(())
        });
        if limit == exact {
            assert_eq!(result, Ok(expected));
            assert_eq!(remaining, 0);
            assert_eq!(calls, 2);
        } else {
            assert_eq!(
                result,
                Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(limit)))
            );
            assert_eq!(remaining, limit.saturating_sub(1));
            assert_eq!(calls, if limit == 0 { 1 } else { 2 });
        }
    }
}

fn check_pair<T: CheckedNativeEqualityLeaf + CheckedNativeOrderingLeaf>(
    left: &T,
    right: &T,
    eq_work: usize,
    ne_work: usize,
    cmp_work: usize,
) {
    check_operation(PartialEq::eq(left, right), eq_work, |reserve| {
        left.try_native_eq(right, &mut |work, units| reserve(work, units))
    });
    check_operation(PartialEq::ne(left, right), ne_work, |reserve| {
        left.try_native_ne(right, &mut |work, units| reserve(work, units))
    });
    check_operation(Ord::cmp(left, right), cmp_work, |reserve| {
        left.try_native_cmp(right, &mut |work, units| reserve(work, units))
    });
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn fixed_native_operations_preserve_results_and_all_admission_boundaries() {
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    for left in [i64::MIN, -1, 0, 1, i64::MAX] {
        for right in [i64::MIN, -1, 0, 1, i64::MAX] {
            check_pair(&left, &right, 2, 2, 2);
        }
    }
    for left in [false, true] {
        for right in [false, true] {
            check_pair(&left, &right, 2, 2, 2);
        }
    }
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn string_native_operations_cover_byte_lengths_prefixes_and_mismatch_positions() {
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let large = "x".repeat(100_000);
    let late = format!("{}y", "x".repeat(99_999));
    let early = format!("y{}", "x".repeat(99_999));
    let cases = [
        ("", ""),
        ("", "a"),
        ("a", "a"),
        ("a", "ab"),
        ("ab", "ac"),
        ("ab", "cb"),
        ("λ", "λ"),
        ("λ", "μ"),
        ("λ", "aa"),
        ("λ", "a"),
        ("é", "e\u{301}"),
        ("🙂", "🙃"),
        ("a\0b", "a\0c"),
        (large.as_str(), large.as_str()),
        (large.as_str(), late.as_str()),
        (large.as_str(), early.as_str()),
        (large.as_str(), "x"),
    ];
    for (left, right) in cases {
        for (left, right) in [(left, right), (right, left)] {
            let eq_bytes = if left.len() == right.len() {
                left.len()
            } else {
                0
            };
            let eq_work = 6 + 2 * eq_bytes;
            let cmp_work = 9 + 2 * left.len().min(right.len());
            check_pair(&left.to_owned(), &right.to_owned(), eq_work, eq_work + 1, cmp_work);
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Event {
    Reserve(usize, usize),
    Inspect(&'static str),
    Action(&'static str),
}

fn operation_name(operation: &ComparisonOperation) -> &'static str {
    match operation {
        ComparisonOperation::Eq => "eq",
        ComparisonOperation::Ne => "ne",
        ComparisonOperation::Cmp => "cmp",
    }
}

// This private probe is deliberately NOT a public equality/ordering leaf and
// does not implement PartialEq or Ord. It tests only the private admission
// runner's effect boundary, without introducing an arbitrary public cost API.
struct Probe<'a> {
    events: &'a RefCell<Vec<Event>>,
    work: Option<usize>,
}

impl sealed::Leaf for Probe<'_> {
    fn execution_work(&self, _other: &Self, operation: ComparisonOperation) -> Option<usize> {
        self.events
            .borrow_mut()
            .push(Event::Inspect(operation_name(&operation)));
        self.work
    }
}

impl Probe<'_> {
    fn native_eq(&self, _other: &Self) -> bool {
        self.events.borrow_mut().push(Event::Action("eq"));
        true
    }
    fn native_ne(&self, _other: &Self) -> bool {
        self.events.borrow_mut().push(Event::Action("ne"));
        true
    }
    fn native_cmp(&self, _other: &Self) -> Ordering {
        self.events.borrow_mut().push(Event::Action("cmp"));
        Ordering::Less
    }
}

#[test]
fn private_runner_admits_metadata_then_exactly_one_selected_native_action() {
    for operation in [ComparisonOperation::Eq, ComparisonOperation::Ne, ComparisonOperation::Cmp] {
        let name = operation_name(&operation);
        let events = RefCell::new(Vec::new());
        let left = Probe { events: &events, work: Some(23) };
        let right = Probe { events: &events, work: Some(99) };
        let result = admit_comparison(
            &left,
            &right,
            operation,
            &mut |work, units| {
                events.borrow_mut().push(Event::Reserve(work, units));
                Ok::<_, usize>(())
            },
            true,
            |left, right| match name {
                "eq" => left.native_eq(right),
                "ne" => left.native_ne(right),
                "cmp" => left.native_cmp(right) == Ordering::Less,
                _ => unreachable!("closed operation names"),
            },
        );
        assert_eq!(result, Ok(true));
        assert_eq!(
            *events.borrow(),
            [
                Event::Reserve(1, 0),
                Event::Inspect(name),
                Event::Reserve(23, 0),
                Event::Action(name)
            ]
        );
    }
}

#[test]
fn private_runner_refuses_before_unpaid_metadata_or_native_action() {
    for stop in 0..2 {
        let events = RefCell::new(Vec::new());
        let left = Probe { events: &events, work: Some(23) };
        let right = Probe { events: &events, work: Some(99) };
        let mut calls = 0;
        let result = admit_comparison(
            &left,
            &right,
            ComparisonOperation::Ne,
            &mut |work, units| {
                events.borrow_mut().push(Event::Reserve(work, units));
                let index = calls;
                calls += 1;
                if index == stop {
                    Err(stop)
                } else {
                    Ok(())
                }
            },
            true,
            Probe::native_ne,
        );
        assert_eq!(
            result,
            Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(stop)))
        );
        let expected = if stop == 0 {
            vec![Event::Reserve(1, 0)]
        } else {
            vec![Event::Reserve(1, 0), Event::Inspect("ne"), Event::Reserve(23, 0)]
        };
        assert_eq!(*events.borrow(), expected);
    }
}

#[test]
fn unsupported_profile_has_no_reservation_inspection_or_native_action() {
    let events = RefCell::new(Vec::new());
    let left = Probe { events: &events, work: Some(23) };
    let right = Probe { events: &events, work: Some(99) };
    let result = admit_comparison(
        &left,
        &right,
        ComparisonOperation::Cmp,
        &mut |work, units| {
            events.borrow_mut().push(Event::Reserve(work, units));
            Ok::<_, usize>(())
        },
        false,
        Probe::native_cmp,
    );
    assert_eq!(result, Err(NativeComparisonFailure::UnsupportedProfile));
    assert!(events.borrow().is_empty());
}

#[test]
fn overflow_retains_only_paid_metadata_and_never_executes() {
    let events = RefCell::new(Vec::new());
    let left = Probe { events: &events, work: None };
    let right = Probe { events: &events, work: Some(99) };
    let result = admit_comparison(
        &left,
        &right,
        ComparisonOperation::Eq,
        &mut |work, units| {
            events.borrow_mut().push(Event::Reserve(work, units));
            Ok::<_, usize>(())
        },
        true,
        Probe::native_eq,
    );
    assert_eq!(result, Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow)));
    assert_eq!(*events.borrow(), [Event::Reserve(1, 0), Event::Inspect("eq")]);
}

#[test]
fn string_allowances_check_multiplication_and_addition_without_wrapping() {
    for (operation, base) in [
        (ComparisonOperation::Eq, 6),
        (ComparisonOperation::Ne, 7),
        (ComparisonOperation::Cmp, 9),
    ] {
        let last = (usize::MAX - base) / 2;
        assert_eq!(string_execution_work(last, last, operation), Some(base + 2 * last));
    }
    for operation in [ComparisonOperation::Eq, ComparisonOperation::Ne, ComparisonOperation::Cmp] {
        assert_eq!(string_execution_work(usize::MAX, usize::MAX, operation), None);
    }
    assert_eq!(
        string_execution_work(
            (usize::MAX - 6) / 2 + 1,
            (usize::MAX - 6) / 2 + 1,
            ComparisonOperation::Eq
        ),
        None
    );
    assert_eq!(
        string_execution_work(
            (usize::MAX - 7) / 2 + 1,
            (usize::MAX - 7) / 2 + 1,
            ComparisonOperation::Ne
        ),
        None
    );
    assert_eq!(
        string_execution_work(
            (usize::MAX - 9) / 2 + 1,
            (usize::MAX - 9) / 2 + 1,
            ComparisonOperation::Cmp
        ),
        None
    );
    for (left, right) in [(usize::MAX, 0), (0, usize::MAX), (usize::MAX, 1), (1, usize::MAX)] {
        assert_eq!(string_execution_work(left, right, ComparisonOperation::Eq), Some(6));
        assert_eq!(string_execution_work(left, right, ComparisonOperation::Ne), Some(7));
        assert_eq!(
            string_execution_work(left, right, ComparisonOperation::Cmp),
            Some(9 + 2 * left.min(right))
        );
    }
}
