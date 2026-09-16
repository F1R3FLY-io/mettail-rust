use super::*;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Debug;

fn check_equality_pair<T: CheckedNativeEqualityLeaf>(
    left: &T,
    right: &T,
    eq_work: usize,
    ne_work: usize,
) {
    check_inspection(eq_work, |reserve| {
        left.try_inspect_native_eq_work(right, &mut |work, units| reserve(work, units))
    });
    check_inspection(ne_work, |reserve| {
        left.try_inspect_native_ne_work(right, &mut |work, units| reserve(work, units))
    });
    check_operation(PartialEq::eq(left, right), eq_work, |reserve| {
        left.try_native_eq(right, &mut |work, units| reserve(work, units))
    });
    check_operation(PartialEq::ne(left, right), ne_work, |reserve| {
        left.try_native_ne(right, &mut |work, units| reserve(work, units))
    });
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn ordvar_comparisons_preserve_identity_fields_and_ignore_pretty_hints() {
    use crate::{BoundVar, FreeVar, OrdVar, Var};
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let free = FreeVar::fresh_named("same spelling".to_owned());
    let other = FreeVar::fresh_named("same spelling".to_owned());
    let mut renamed = free.clone();
    renamed.pretty_name = Some("λ".repeat(50_000));
    let mut unnamed = free.clone();
    unnamed.pretty_name = None;
    let bound = |scope, binder, pretty_name| {
        OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(scope),
            binder: moniker::BinderIndex(binder),
            pretty_name,
        }))
    };
    let values = [
        OrdVar(Var::Free(free.clone())),
        OrdVar(Var::Free(renamed)),
        OrdVar(Var::Free(unnamed)),
        OrdVar(Var::Free(other)),
        bound(0, 0, None),
        bound(0, 0, Some("different bound hint".repeat(1_000))),
        bound(0, 1, None),
        bound(1, 0, None),
        bound(0, u32::MAX, None),
        bound(u32::MAX, 0, None),
        bound(u32::MAX, u32::MAX, None),
    ];
    assert_eq!(values[0], values[1]);
    assert_eq!(values[0], values[2]);
    assert_ne!(values[0], values[3], "matching hints do not establish identity");
    assert_eq!(values[4], values[5]);
    assert_eq!(values[8].cmp(&values[7]), Ordering::Less, "scope precedes binder");
    for left in &values {
        for right in &values {
            let (eq, ne, cmp) = match (&left.0, &right.0) {
                (Var::Free(_), Var::Free(_)) => (14, 15, 68),
                (Var::Bound(_), Var::Bound(_)) => (19, 20, 14),
                _ => (7, 8, 5),
            };
            check_pair(left, right, eq, ne, cmp);
        }
    }
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn binder_and_binder_vector_admission_requires_equality_only() {
    use crate::{Binder, FreeVar};
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let binder = Binder(FreeVar::fresh_named("x".to_owned()));
    let other = Binder(FreeVar::fresh_named("x".to_owned()));
    let mut renamed = binder.clone();
    renamed.0.pretty_name = Some("hint".repeat(50_000));
    let mut unnamed = binder.clone();
    unnamed.0.pretty_name = None;
    assert_eq!(binder, renamed);
    assert_eq!(binder, unnamed);
    assert_ne!(binder, other);
    for left in [&binder, &other, &renamed, &unnamed] {
        for right in [&binder, &other, &renamed, &unnamed] {
            check_equality_pair(left, right, 8, 9);
        }
    }
    for width in [0, 1, 2, 1_000] {
        let left = vec![binder.clone(); width];
        let mut right = left.clone();
        check_equality_pair(&left, &right, 7 + 11 * width, 8 + 11 * width);
        if width != 0 {
            right[0] = other.clone();
            check_equality_pair(&left, &right, 7 + 11 * width, 8 + 11 * width);
            right[0] = binder.clone();
            right[width - 1] = other.clone();
            check_equality_pair(&left, &right, 7 + 11 * width, 8 + 11 * width);
        }
        right.push(other.clone());
        check_equality_pair(&left, &right, 7, 8);
        check_equality_pair(&right, &left, 7, 8);
    }
    check_equality_pair(&vec![binder.clone(), other.clone()], &vec![other, binder], 29, 30);
}

// Preserve the expressions in generate_cmp_binder_arm and
// generate_cmp_multi_binder_arm: no substitute hasher or Binder::cmp.
fn original_single_pattern_order(
    left: &crate::Binder<String>,
    right: &crate::Binder<String>,
) -> Ordering {
    let hash_pat = |p: &crate::Binder<String>| -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(p, &mut h);
        std::hash::Hasher::finish(&h)
    };
    hash_pat(left).cmp(&hash_pat(right))
}

fn original_multi_pattern_order(
    l_pats: &Vec<crate::Binder<String>>,
    r_pats: &Vec<crate::Binder<String>>,
) -> Ordering {
    let hash_pat = |p: &crate::Binder<String>| -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(p, &mut h);
        std::hash::Hasher::finish(&h)
    };
    l_pats.len().cmp(&r_pats.len()).then_with(|| {
        l_pats
            .iter()
            .zip(r_pats.iter())
            .map(|(lp, rp)| hash_pat(lp).cmp(&hash_pat(rp)))
            .find(|o| *o != std::cmp::Ordering::Equal)
            .unwrap_or(std::cmp::Ordering::Equal)
    })
}

#[test]
#[cfg(mettail_checked_native_comparison_profile)]
fn generated_pattern_order_precharge_preserves_original_hash_expressions() {
    use crate::{Binder, FreeVar};
    assert!(CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE);
    let binder = Binder(FreeVar::fresh_named("x".to_owned()));
    let other = Binder(FreeVar::fresh_named("x".to_owned()));
    let mut renamed = binder.clone();
    renamed.0.pretty_name = Some("ignored hint".repeat(10_000));
    let mut unnamed = binder.clone();
    unnamed.0.pretty_name = None;
    for left in [&binder, &other, &renamed, &unnamed] {
        for right in [&binder, &other, &renamed, &unnamed] {
            check_inspection(71, |reserve| {
                inspect_generated_single_pattern_order_work(left, right, &mut |work, units| {
                    reserve(work, units)
                })
            });
            let expected = original_single_pattern_order(left, right);
            let mut executions = 0;
            check_operation(expected, 71, |reserve| {
                precharge_generated_single_pattern_order(left, right, &mut |work, units| {
                    reserve(work, units)
                })?;
                executions += 1;
                Ok(original_single_pattern_order(left, right))
            });
            assert_eq!(executions, 2, "only initial and exact-limit successes execute");
        }
    }
    let check_multi = |left: &Vec<Binder<String>>, right: &Vec<Binder<String>>| {
        let work = if left.len() == right.len() {
            27 + 80 * left.len()
        } else {
            5
        };
        let expected = original_multi_pattern_order(left, right);
        check_inspection(work, |reserve| {
            inspect_generated_multi_pattern_order_work(left, right, &mut |work, units| {
                reserve(work, units)
            })
        });
        let mut executions = 0;
        check_operation(expected, work, |reserve| {
            precharge_generated_multi_pattern_order(left, right, &mut |work, units| {
                reserve(work, units)
            })?;
            executions += 1;
            Ok(original_multi_pattern_order(left, right))
        });
        assert_eq!(executions, 2, "refused precharges never reach the original expression");
    };
    check_multi(&vec![binder.clone()], &vec![renamed]);
    check_multi(&vec![binder.clone()], &vec![unnamed]);
    for width in [0, 1, 2, 1_000] {
        let left = vec![binder.clone(); width];
        let mut right = left.clone();
        check_multi(&left, &right);
        if width != 0 {
            right[0] = other.clone();
            check_multi(&left, &right);
            right[0] = binder.clone();
            right[width - 1] = other.clone();
            check_multi(&left, &right);
        }
        right.push(other.clone());
        assert_eq!(original_multi_pattern_order(&left, &right), Ordering::Less);
        check_multi(&left, &right);
        check_multi(&right, &left);
    }
    check_multi(&vec![binder.clone(), other.clone()], &vec![other, binder]);
}

#[test]
fn identity_vector_allowances_reject_equal_width_overflow_but_skip_unvisited_width() {
    for (negated, base) in [(false, 7usize), (true, 8usize)] {
        assert_eq!(binder_vector_equality_work(0, 0, negated), Some(base));
        let last = (usize::MAX - base) / 11;
        assert_eq!(binder_vector_equality_work(last, last, negated), Some(base + 11 * last));
        assert_eq!(binder_vector_equality_work(last + 1, last + 1, negated), None);
        assert_eq!(binder_vector_equality_work(usize::MAX, usize::MAX, negated), None);
    }
    let last = (usize::MAX - 27) / 80;
    assert_eq!(multi_pattern_order_work(0, 0), Some(27));
    assert_eq!(multi_pattern_order_work(last, last), Some(27 + 80 * last));
    assert_eq!(multi_pattern_order_work(last + 1, last + 1), None);
    assert_eq!(multi_pattern_order_work(usize::MAX, usize::MAX), None);
    for (left, right) in [
        (usize::MAX, 0),
        (0, usize::MAX),
        (usize::MAX, 1),
        (1, usize::MAX),
        (usize::MAX, usize::MAX - 1),
        (usize::MAX - 1, usize::MAX),
    ] {
        assert_eq!(binder_vector_equality_work(left, right, false), Some(7));
        assert_eq!(binder_vector_equality_work(left, right, true), Some(8));
        assert_eq!(multi_pattern_order_work(left, right), Some(5));
    }
}

type TestFailure = NativeComparisonFailure<usize>;
type Reservation<'a> = dyn FnMut(usize, usize) -> Result<(), usize> + 'a;

fn check_inspection(
    expected_work: usize,
    mut inspect: impl FnMut(&mut Reservation<'_>) -> Result<usize, TestFailure>,
) {
    for limit in [0usize, 1] {
        let mut remaining = limit;
        let mut trace = Vec::new();
        let result = inspect(&mut |work, units| {
            trace.push((work, units));
            remaining = remaining.checked_sub(work).ok_or(limit)?;
            Ok(())
        });
        assert_eq!(trace, [(1, 0)], "inspection never reserves native execution");
        assert_eq!(remaining, 0);
        match limit {
            0 => assert_eq!(
                result,
                Err(NativeComparisonFailure::Admission(BindingFailure::Reservation(0)))
            ),
            _ => assert_eq!(result, Ok(expected_work)),
        }
    }
}

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
    check_inspection(eq_work, |reserve| {
        left.try_inspect_native_eq_work(right, &mut |work, units| reserve(work, units))
    });
    check_inspection(ne_work, |reserve| {
        left.try_inspect_native_ne_work(right, &mut |work, units| reserve(work, units))
    });
    check_inspection(cmp_work, |reserve| {
        left.try_inspect_native_cmp_work(right, &mut |work, units| reserve(work, units))
    });
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
    fn execution_work<E>(
        &self,
        _other: &Self,
        operation: ComparisonOperation,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        self.events
            .borrow_mut()
            .push(Event::Inspect(operation_name(&operation)));
        self.work.ok_or(BindingFailure::SizeOverflow)
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
fn inspection_only_runner_preserves_operation_and_refuses_before_unpaid_work() {
    for operation in [ComparisonOperation::Eq, ComparisonOperation::Ne, ComparisonOperation::Cmp] {
        for (supported, allowed, work) in [
            (false, true, Some(23)),
            (true, false, Some(23)),
            (true, true, None),
            (true, true, Some(23)),
        ] {
            let name = operation_name(&operation);
            let events = RefCell::new(Vec::new());
            let left = Probe { events: &events, work };
            let right = Probe { events: &events, work: Some(99) };
            // The error owns its payload; no Clone bound is needed to return it.
            #[derive(Debug, PartialEq, Eq)]
            struct Refusal(Box<str>);
            let result = inspect_native_work(
                &mut |work, units| {
                    events.borrow_mut().push(Event::Reserve(work, units));
                    match allowed {
                        true => Ok(()),
                        false => Err(Refusal("inspection refused".into())),
                    }
                },
                supported,
                |reserve| sealed::Leaf::execution_work(&left, &right, operation, reserve),
            );
            let expected = match (supported, allowed, work) {
                (false, _, _) => Err(NativeComparisonFailure::UnsupportedProfile),
                (true, false, _) => Err(NativeComparisonFailure::Admission(
                    BindingFailure::Reservation(Refusal("inspection refused".into())),
                )),
                (true, true, None) => {
                    Err(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))
                },
                (true, true, Some(work)) => Ok(work),
            };
            assert_eq!(result, expected);
            let expected_events = match (supported, allowed) {
                (false, _) => vec![],
                (true, false) => vec![Event::Reserve(1, 0)],
                (true, true) => vec![Event::Reserve(1, 0), Event::Inspect(name)],
            };
            assert_eq!(*events.borrow(), expected_events);
        }
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
