//! Compare actual Moniker coordinates and hints, not hint-insensitive equality.
use mettail_runtime::{
    reserve_binding_copy, BindingFailure, BindingOperation, CheckedBindingLeaf, OrdVar,
};
use moniker::{Binder, BinderIndex, BoundTerm, BoundVar, FreeVar, ScopeOffset, ScopeState, Var};

fn bound(depth: u32, index: u32, hint: &str) -> OrdVar {
    OrdVar(Var::Bound(BoundVar {
        scope: ScopeOffset(depth),
        binder: BinderIndex(index),
        pretty_name: Some(hint.to_owned()),
    }))
}

fn assert_exact(actual: &OrdVar, expected: &OrdVar) {
    match (&actual.0, &expected.0) {
        (Var::Free(a), Var::Free(b)) => {
            assert_eq!(a.unique_id, b.unique_id);
            assert_eq!(a.pretty_name, b.pretty_name);
        },
        (Var::Bound(a), Var::Bound(b)) => {
            assert_eq!(a.scope, b.scope);
            assert_eq!(a.binder, b.binder);
            assert_eq!(a.pretty_name, b.pretty_name);
        },
        _ => panic!("different variable variants: {actual:?}, {expected:?}"),
    }
}

type TestResult<T> = (Result<T, BindingFailure<&'static str>>, (usize, usize), usize);

// Test callback only; each successful reservation is retained atomically.
fn copy_with_limits<T: CheckedBindingLeaf>(
    source: &T,
    operation: BindingOperation<'_>,
    limits: (usize, usize),
    cancel_call: Option<usize>,
) -> TestResult<T> {
    let mut used = (0usize, 0usize);
    let mut calls = 0;
    let result = source.try_copy_binding(operation, &mut |work, units| {
        calls += 1;
        if cancel_call == Some(calls) {
            return Err("cancelled");
        }
        if work > limits.0 - used.0 || units > limits.1 - used.1 {
            return Err("limit");
        }
        used.0 += work;
        used.1 += units;
        Ok(())
    });
    (result, used, calls)
}

#[test]
fn checked_variables_match_moniker_fields_at_zero_and_two() {
    let chosen: FreeVar<String> = FreeVar::fresh_named("λ");
    let same_hint = FreeVar::fresh_named("λ");
    assert_ne!(chosen.unique_id, same_hint.unique_id);
    let mut selected = chosen.clone();
    selected.pretty_name = Some("selected roster hint".to_owned());
    let mut duplicate = chosen.clone();
    duplicate.pretty_name = Some("later duplicate".to_owned());
    let roster = vec![Binder(same_hint), Binder(selected), Binder(duplicate)];
    for state in [ScopeState::new(), ScopeState::new().incr().incr()] {
        for variable in [chosen.clone(), FreeVar::fresh_named("λ"), FreeVar::fresh_unnamed()] {
            let source = OrdVar(Var::Free(variable));
            let original = source.clone();
            let mut expected = source.clone();
            expected.close_term(state, &roster);
            let (closed, _, _) = copy_with_limits(
                &source,
                BindingOperation::Close { state, binders: &roster },
                (usize::MAX, usize::MAX),
                None,
            );
            let closed = closed.expect("valid closing");
            assert_exact(&closed, &expected);
            assert_exact(&source, &original);
            let mut expected_open = closed.clone();
            expected_open.open_term(state, &roster);
            let (opened, _, _) = copy_with_limits(
                &closed,
                BindingOperation::Open { state, binders: &roster },
                (usize::MAX, usize::MAX),
                None,
            );
            assert_exact(&opened.expect("valid opening"), &expected_open);
            assert_exact(&closed, &expected);
        }
    }
}

#[test]
fn close_reservations_are_exact_and_cancellable_inside_identity_scan() {
    let chosen: FreeVar<String> = FreeVar::fresh_named("λ");
    let roster = vec![
        Binder(FreeVar::fresh_named("λ")),
        Binder(chosen.clone()),
        Binder(chosen.clone()),
    ];
    let source = OrdVar(Var::Free(chosen));
    let operation = BindingOperation::Close {
        state: ScopeState::new(),
        binders: &roster,
    };
    let (result, used, calls) = copy_with_limits(&source, operation, (6, 6), None);
    assert_exact(&result.expect("exact budget"), &bound(0, 1, "λ"));
    assert_eq!((used, calls), ((6, 6), 4));
    for limits in [(5, 6), (6, 5)] {
        let (result, used, calls) = copy_with_limits(&source, operation, limits, None);
        assert_eq!(result, Err(BindingFailure::Reservation("limit")));
        assert_eq!((used, calls), ((3, 0), 4));
    }
    let original = source.clone();
    for cancelled in 1..=4 {
        let (result, used, calls) = copy_with_limits(&source, operation, (6, 6), Some(cancelled));
        assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
        assert_eq!((used, calls), ((cancelled - 1, 0), cancelled));
        assert_exact(&source, &original);
    }
    assert!(copy_with_limits(&source, operation, (6, 6), None).0.is_ok());
}

#[test]
fn open_copies_selected_hint_and_rejects_missing_index_only_at_matching_depth() {
    let selected: FreeVar<String> = FreeVar::fresh_named("雪");
    let roster = vec![Binder(selected.clone())];
    let source = bound(0, 0, "old, much longer hint");
    let operation = BindingOperation::Open {
        state: ScopeState::new(),
        binders: &roster,
    };
    let (result, used, calls) = copy_with_limits(&source, operation, (5, 7), None);
    assert_exact(&result.expect("exact budget"), &OrdVar(Var::Free(selected)));
    assert_eq!((used, calls), ((5, 7), 2));
    for limits in [(4, 7), (5, 6)] {
        let (result, used, calls) = copy_with_limits(&source, operation, limits, None);
        assert_eq!(result, Err(BindingFailure::Reservation("limit")));
        assert_eq!((used, calls), ((1, 0), 2));
    }
    let missing = bound(2, 99, "x");
    let (result, used, calls) = copy_with_limits(
        &missing,
        BindingOperation::Open {
            state: ScopeState::new().incr().incr(),
            binders: &roster,
        },
        (100, 100),
        None,
    );
    assert_eq!(result, Err(BindingFailure::MissingBinder { index: 99 }));
    assert_eq!((used, calls), ((1, 0), 1));
    let (result, used, calls) = copy_with_limits(&missing, operation, (3, 5), None);
    let mut expected = missing.clone();
    expected.open_term(ScopeState::new(), &roster);
    assert_exact(&result.expect("different depth preserves index"), &expected);
    assert_exact(&missing, &bound(2, 99, "x"));
    assert_eq!((used, calls), ((3, 5), 2));
}

#[test]
fn freevar_binding_is_a_paid_noop_and_clone_preserves_variable_fields() {
    let source: FreeVar<String> = FreeVar::fresh_named("λ");
    let roster = vec![Binder(source.clone())];
    for operation in [
        BindingOperation::Clone,
        BindingOperation::Open {
            state: ScopeState::new(),
            binders: &roster,
        },
        BindingOperation::Close {
            state: ScopeState::new(),
            binders: &roster,
        },
    ] {
        let (result, used, calls) = copy_with_limits(&source, operation, (3, 6), None);
        assert_exact(
            &OrdVar(Var::Free(result.expect("direct FreeVar copy"))),
            &OrdVar(Var::Free(source.clone())),
        );
        assert_eq!((used, calls), ((3, 6), 1));
    }
    for source in [OrdVar(Var::Free(source)), bound(2, 3, "λ")] {
        let (result, used, calls) =
            copy_with_limits(&source, BindingOperation::Clone, (4, 6), None);
        assert_exact(&result.expect("variable clone"), &source);
        assert_eq!((used, calls), ((4, 6), 2));
    }
}

#[test]
fn strings_and_bytes_charge_owned_bytes_before_copying() {
    let text = "λ雪🙂".to_owned();
    let bytes = vec![0, 255, 128, 1];
    let (copied, used, calls) = copy_with_limits(&text, BindingOperation::Clone, (10, 13), None);
    assert_eq!(copied.expect("text copy"), text);
    assert_eq!((used, calls), ((10, 13), 1));
    let (copied, used, calls) = copy_with_limits(&bytes, BindingOperation::Clone, (5, 8), None);
    assert_eq!(copied.expect("byte copy"), bytes);
    assert_eq!((used, calls), ((5, 8), 1));
    let (result, used, _) = copy_with_limits(&text, BindingOperation::Clone, (10, 12), None);
    assert_eq!(result, Err(BindingFailure::Reservation("limit")));
    assert_eq!(used, (0, 0));
    assert_eq!(text, "λ雪🙂");
}

#[test]
fn copy_size_overflow_refuses_before_reservation() {
    for size in [usize::MAX, usize::MAX - 3] {
        let mut calls = 0;
        let result = reserve_binding_copy(size, &mut |_, _| {
            calls += 1;
            Ok::<(), &'static str>(())
        });
        assert_eq!(result, Err(BindingFailure::SizeOverflow));
        assert_eq!(calls, 0);
    }
}

#[test]
fn scalar_copy_is_admitted_before_return_and_empty_values_have_one_record() {
    let (result, used, calls) = copy_with_limits(&42i64, BindingOperation::Clone, (1, 4), None);
    assert_eq!(result, Ok(42));
    assert_eq!((used, calls), ((1, 4), 1));
    assert_eq!(
        copy_with_limits(&42i64, BindingOperation::Clone, (1, 3), None).0,
        Err(BindingFailure::Reservation("limit"))
    );
    for operation in [
        BindingOperation::Clone,
        BindingOperation::Close { state: ScopeState::new(), binders: &[] },
    ] {
        assert_eq!(copy_with_limits(&String::new(), operation, (1, 4), None).1, (1, 4));
        assert_eq!(copy_with_limits(&Vec::<u8>::new(), operation, (1, 4), None).1, (1, 4));
    }
}
