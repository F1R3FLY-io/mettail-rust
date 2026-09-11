//! Compare actual Moniker coordinates and hints, not hint-insensitive equality.
use mettail_runtime::{
    reserve_binding_copy, BindingFailure, BindingOperation, CheckedBindingLeaf,
    CheckedIterativeBinding, OrdVar,
};
use moniker::{
    Binder, BinderIndex, BoundPattern, BoundTerm, BoundVar, FreeVar, ScopeOffset, ScopeState, Var,
};
use std::sync::Arc;

#[test]
fn operation_state_is_inherited_without_changing_roster_or_siblings() {
    let roster = vec![Binder(FreeVar::fresh_named("x"))];
    let parent_state = ScopeState::new().incr().incr();
    for parent in [
        BindingOperation::Open { state: parent_state, binders: &roster },
        BindingOperation::Close { state: parent_state, binders: &roster },
    ] {
        let body = parent
            .under_scope::<()>()
            .expect("scope depth is representable");
        let nested = body
            .under_scope::<()>()
            .expect("nested scope depth is representable");
        assert_eq!(parent.state().depth(), ScopeOffset(2));
        assert_eq!(body.state().depth(), ScopeOffset(3));
        assert_eq!(nested.state().depth(), ScopeOffset(4));
        let sibling = parent.with_state(parent_state);
        let nested_sibling = parent.under_scope::<()>().expect("independent sibling");
        assert_eq!(sibling.state().depth(), ScopeOffset(2));
        assert_eq!(nested_sibling.state().depth(), ScopeOffset(3));
        for operation in [body, nested, sibling, nested_sibling] {
            match (parent, operation) {
                (BindingOperation::Open { .. }, BindingOperation::Open { binders, .. })
                | (BindingOperation::Close { .. }, BindingOperation::Close { binders, .. }) => {
                    assert!(std::ptr::eq(binders, roster.as_slice()));
                },
                _ => panic!("inherited operation changed kind"),
            }
        }
    }
    let cloned = BindingOperation::Clone.with_state(parent_state);
    assert!(matches!(cloned, BindingOperation::Clone));
    assert!(matches!(cloned.under_scope::<()>(), Ok(BindingOperation::Clone)));
    assert_eq!(cloned.state().depth(), ScopeOffset(0));
}

#[test]
fn checked_arc_boundary_preserves_clone_sharing_and_admits_binding() {
    let chosen: FreeVar<String> = FreeVar::fresh_named("x");
    let roster = vec![Binder(chosen.clone())];
    let original = OrdVar(Var::Free(chosen));
    let source = Arc::new(original.clone());
    let mut charges = Vec::new();
    let cloned = source
        .try_copy_iterative(BindingOperation::Clone, &mut |work, units| {
            charges.push((work, units));
            Ok::<(), &'static str>(())
        })
        .expect("paid shallow clone");
    assert!(Arc::ptr_eq(&source, &cloned));
    assert_eq!(charges, [(3, 4)]);
    drop(cloned);

    let close = BindingOperation::Close {
        state: ScopeState::new(),
        binders: &roster,
    };
    charges.clear();
    let closed = source
        .try_copy_iterative(close, &mut |work, units| {
            charges.push((work, units));
            Ok::<(), &'static str>(())
        })
        .expect("paid binding");
    assert!(!Arc::ptr_eq(&source, &closed));
    assert_exact(&closed, &bound(0, 0, "x"));
    assert_exact(&source, &original);
    assert_eq!(charges, [(3, 4), (1, 0), (1, 0), (3, 5)]);
    let mut expected = closed.as_ref().clone();
    expected.open_term(ScopeState::new(), &roster);
    let opened = closed
        .try_copy_iterative(
            BindingOperation::Open {
                state: ScopeState::new(),
                binders: &roster,
            },
            &mut |_, _| Ok::<(), ()>(()),
        )
        .expect("opening uses the same checked boundary");
    assert!(!Arc::ptr_eq(&closed, &opened));
    assert_exact(&opened, &expected);

    for cancelled in 1..=4 {
        let mut calls = 0;
        let result = source.try_copy_iterative(close, &mut |_, _| {
            calls += 1;
            if calls == cancelled {
                Err("cancelled")
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
        assert_eq!(calls, cancelled);
        assert_eq!(Arc::strong_count(&source), 1);
        assert_exact(&source, &original);
    }
    for limit in [(7usize, 9usize), (8, 8), (8, 9)] {
        let mut used = (0, 0);
        let result = source.try_copy_iterative(close, &mut |work, units| {
            if work > limit.0 - used.0 || units > limit.1 - used.1 {
                return Err("limit");
            }
            used.0 += work;
            used.1 += units;
            Ok(())
        });
        if limit == (8, 9) {
            assert_exact(&result.expect("exact limit succeeds after refusals"), &closed);
            assert_eq!(used, limit);
        } else {
            assert_eq!(result, Err(BindingFailure::Reservation("limit")));
            assert_eq!(used, (5, 4));
        }
    }
}

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

fn assert_binders_exact(actual: &[Binder<String>], expected: &[Binder<String>]) {
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        assert_eq!(actual.0.unique_id, expected.0.unique_id);
        assert_eq!(actual.0.pretty_name, expected.0.pretty_name);
    }
}

#[test]
fn checked_binder_patterns_preserve_roster_occurrences_and_prepaid_storage() {
    let first = FreeVar::fresh_named("λ");
    let same_hint = FreeVar::fresh_named("λ");
    assert_ne!(first.unique_id, same_hint.unique_id);
    let mut duplicate = first.clone();
    duplicate.pretty_name = Some("later hint".to_owned());
    let roster = vec![Binder(first.clone()), Binder(duplicate.clone())];
    let source = vec![
        Binder(first),
        Binder(same_hint),
        Binder(duplicate),
        Binder(FreeVar::fresh_unnamed()),
        Binder(FreeVar::fresh_named("")),
    ];
    for state in [ScopeState::new(), ScopeState::new().incr().incr()] {
        for operation in [
            BindingOperation::Clone,
            BindingOperation::Open { state, binders: &roster },
            BindingOperation::Close { state, binders: &roster },
        ] {
            for pattern in [&Vec::new(), &source] {
                let mut expected = pattern.clone();
                match operation {
                    BindingOperation::Clone => {},
                    BindingOperation::Open { .. } => expected.open_pattern(state, &roster),
                    BindingOperation::Close { .. } => expected.close_pattern(state, &roster),
                }
                assert_binders_exact(&expected, pattern);
                let bytes: usize = pattern
                    .iter()
                    .map(|binder| binder.0.pretty_name.as_ref().map_or(0, String::len))
                    .sum();
                let present = pattern
                    .iter()
                    .filter(|binder| binder.0.pretty_name.is_some())
                    .count();
                let total =
                    (2 + 5 * pattern.len() + present + bytes, 4 * (1 + pattern.len()) + bytes);
                let (copied, used, callbacks) = copy_with_limits(pattern, operation, total, None);
                let copied = copied.expect("exact binder-vector allowance");
                assert_binders_exact(&copied, &expected);
                assert_eq!(used, total);
                assert_eq!(callbacks, 1 + 3 * pattern.len());

                for cancelled in 1..=callbacks {
                    let (result, _, calls) =
                        copy_with_limits(pattern, operation, total, Some(cancelled));
                    assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
                    assert_eq!(calls, cancelled);
                    assert_binders_exact(pattern, &expected);
                }
                for limit in [(total.0 - 1, total.1), (total.0, total.1 - 1)] {
                    let (result, _, _) = copy_with_limits(pattern, operation, limit, None);
                    assert_eq!(result, Err(BindingFailure::Reservation("limit")));
                    assert_binders_exact(pattern, &expected);
                }
                let (retry, _, _) = copy_with_limits(pattern, operation, total, None);
                assert_binders_exact(&retry.expect("retry after partial refusal"), &expected);
            }

            for binder in &source {
                let name_bytes = binder.0.pretty_name.as_ref().map_or(0, String::len);
                let total =
                    (3 + usize::from(binder.0.pretty_name.is_some()) + name_bytes, 4 + name_bytes);
                let (result, used, calls) = copy_with_limits(binder, operation, total, None);
                assert_binders_exact(
                    &[result.expect("exact single-binder allowance")],
                    std::slice::from_ref(binder),
                );
                assert_eq!(used, total);
                assert_eq!(calls, 2);
                for cancelled in 1..=calls {
                    let (result, _, calls) =
                        copy_with_limits(binder, operation, total, Some(cancelled));
                    assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
                    assert_eq!(calls, cancelled);
                }
                for limit in [(total.0 - 1, total.1), (total.0, total.1 - 1)] {
                    let (result, _, _) = copy_with_limits(binder, operation, limit, None);
                    assert_eq!(result, Err(BindingFailure::Reservation("limit")));
                }
            }
        }
    }

    let mut charges = Vec::new();
    let one = vec![Binder(FreeVar::fresh_named("λ"))];
    one.try_copy_binding(BindingOperation::Clone, &mut |work, units| {
        charges.push((work, units));
        Ok::<(), ()>(())
    })
    .expect("observe exact preallocation and entry schedule");
    // The sole FreeVar record is paid before allocation, not again at copy.
    assert_eq!(charges, [(2, 8), (2, 0), (2, 0), (4, 2)]);
}

#[test]
fn checked_binder_pattern_copy_and_partial_cleanup_use_bounded_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let source: Vec<_> = (0..20_000)
                .map(|_| Binder(FreeVar::fresh_unnamed()))
                .collect();
            let total = (2 + 5 * source.len(), 4 * (1 + source.len()));
            let (result, used, calls) =
                copy_with_limits(&source, BindingOperation::Clone, total, None);
            let copied = result.expect("large flat pattern copy");
            assert_binders_exact(&copied, &source);
            assert_eq!(used, total);
            drop(copied);
            let (result, _, stopped) =
                copy_with_limits(&source, BindingOperation::Clone, total, Some(calls));
            assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
            assert_eq!(stopped, calls);
            let (retry, _, _) = copy_with_limits(&source, BindingOperation::Clone, total, None);
            assert_binders_exact(&retry.expect("retry after large partial cleanup"), &source);
        })
        .expect("small-stack binder-pattern thread")
        .join()
        .expect("binder-pattern copy and cleanup must not overflow");
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
    let (result, used, calls) = copy_with_limits(&source, operation, (7, 6), None);
    assert_exact(&result.expect("exact budget"), &bound(0, 1, "λ"));
    assert_eq!((used, calls), ((7, 6), 4));
    for limits in [(6, 6), (7, 5)] {
        let (result, used, calls) = copy_with_limits(&source, operation, limits, None);
        assert_eq!(result, Err(BindingFailure::Reservation("limit")));
        assert_eq!((used, calls), ((3, 0), 4));
    }
    let original = source.clone();
    for cancelled in 1..=4 {
        let (result, used, calls) = copy_with_limits(&source, operation, (7, 6), Some(cancelled));
        assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
        assert_eq!((used, calls), ((cancelled - 1, 0), cancelled));
        assert_exact(&source, &original);
    }
    assert!(copy_with_limits(&source, operation, (7, 6), None).0.is_ok());
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
    let (result, used, calls) = copy_with_limits(&source, operation, (6, 7), None);
    assert_exact(&result.expect("exact budget"), &OrdVar(Var::Free(selected)));
    assert_eq!((used, calls), ((6, 7), 2));
    for limits in [(5, 7), (6, 6)] {
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
    let (result, used, calls) = copy_with_limits(&missing, operation, (4, 5), None);
    let mut expected = missing.clone();
    expected.open_term(ScopeState::new(), &roster);
    assert_exact(&result.expect("different depth preserves index"), &expected);
    assert_exact(&missing, &bound(2, 99, "x"));
    assert_eq!((used, calls), ((4, 5), 2));
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
        let (result, used, calls) = copy_with_limits(&source, operation, (4, 6), None);
        assert_exact(
            &OrdVar(Var::Free(result.expect("direct FreeVar copy"))),
            &OrdVar(Var::Free(source.clone())),
        );
        assert_eq!((used, calls), ((4, 6), 1));
    }
    for source in [OrdVar(Var::Free(source)), bound(2, 3, "λ")] {
        let (result, used, calls) =
            copy_with_limits(&source, BindingOperation::Clone, (5, 6), None);
        assert_exact(&result.expect("variable clone"), &source);
        assert_eq!((used, calls), ((5, 6), 2));
    }
}

#[test]
fn variable_cleanup_tracks_the_selected_optional_name_not_its_spelling() {
    let unnamed: FreeVar<String> = FreeVar::fresh_unnamed();
    let mut empty_name = unnamed.clone();
    empty_name.pretty_name = Some(String::new());
    for (name, work) in [(unnamed.clone(), 1), (empty_name.clone(), 2)] {
        let (result, used, calls) =
            copy_with_limits(&name, BindingOperation::Clone, (work, 4), None);
        assert_eq!(result.expect("exact optional-name credit").pretty_name, name.pretty_name);
        assert_eq!((used, calls), ((work, 4), 1));
        let (result, used, _) =
            copy_with_limits(&name, BindingOperation::Clone, (work - 1, 4), None);
        assert_eq!(result, Err(BindingFailure::Reservation("limit")));
        assert_eq!(used, (0, 0));
    }
    let source = bound(0, 0, "this old hint must not be copied or charged");
    for (name, work) in [(unnamed, 2), (empty_name, 3)] {
        let roster = [Binder(name.clone())];
        let (result, used, calls) = copy_with_limits(
            &source,
            BindingOperation::Open {
                state: ScopeState::new(),
                binders: &roster,
            },
            (work, 4),
            None,
        );
        assert_exact(
            &result.expect("selected binder owns the output hint"),
            &OrdVar(Var::Free(name)),
        );
        assert_eq!((used, calls), ((work, 4), 2));
    }
}

#[test]
fn strings_and_bytes_charge_owned_bytes_before_copying() {
    let text = "λ雪🙂".to_owned();
    let bytes = vec![0, 255, 128, 1];
    let (copied, used, calls) = copy_with_limits(&text, BindingOperation::Clone, (11, 13), None);
    assert_eq!(copied.expect("text copy"), text);
    assert_eq!((used, calls), ((11, 13), 1));
    let (copied, used, calls) = copy_with_limits(&bytes, BindingOperation::Clone, (6, 8), None);
    assert_eq!(copied.expect("byte copy"), bytes);
    assert_eq!((used, calls), ((6, 8), 1));
    let (result, used, _) = copy_with_limits(&text, BindingOperation::Clone, (11, 12), None);
    assert_eq!(result, Err(BindingFailure::Reservation("limit")));
    assert_eq!(used, (0, 0));
    for limits in [(10, 13), (11, 12)] {
        let (result, used, _) = copy_with_limits(&text, BindingOperation::Clone, limits, None);
        assert_eq!(result, Err(BindingFailure::Reservation("limit")));
        assert_eq!(used, (0, 0));
    }
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
        let (text, used, _) = copy_with_limits(&String::new(), operation, (2, 4), None);
        assert_eq!(text.expect("empty text copy and cleanup admitted"), "");
        assert_eq!(used, (2, 4));
        let (bytes, used, _) = copy_with_limits(&Vec::<u8>::new(), operation, (2, 4), None);
        assert!(bytes
            .expect("empty byte copy and cleanup admitted")
            .is_empty());
        assert_eq!(used, (2, 4));
    }
}

fn flt_binding_fixture(selector: FreeVar<String>) -> mettail_runtime::FltNode {
    use mettail_runtime::{
        FltHole, FltHoleId, FltNode, FltSourceRange as Range, FltTemplateBounds,
        FltTemplatePiece as Piece,
    };
    FltNode {
        selector: OrdVar(Var::Free(selector)),
        selector_name: "guest".into(),
        category: "Term".into(),
        open_src: "guest:Term`".into(),
        body_src: "rho:id/*x*/${x}//雪${雪}".into(),
        close_src: "`".into(),
        holes: vec![
            FltHole {
                id: FltHoleId(0),
                name: "x".into(),
                category: Some("Term".into()),
                first_occurrence: Range::new(11, 15),
            },
            FltHole {
                id: FltHoleId(1),
                name: "雪".into(),
                category: None,
                first_occurrence: Range::new(20, 26),
            },
        ],
        pieces: vec![
            Piece::Text {
                text: "rho:id/*x*/".into(),
                range: Range::new(0, 11),
            },
            Piece::Hole {
                id: FltHoleId(0),
                range: Range::new(11, 15),
            },
            Piece::Text {
                text: "//雪".into(),
                range: Range::new(15, 20),
            },
            Piece::Hole {
                id: FltHoleId(1),
                range: Range::new(20, 26),
            },
        ],
        // Deliberately false provenance: copying is not template validation.
        bounds: FltTemplateBounds {
            source_bytes: usize::MAX,
            body_bytes: usize::MAX,
            piece_count: usize::MAX,
            hole_declarations: usize::MAX,
            hole_occurrences: usize::MAX,
        },
        position: usize::MAX,
    }
}

fn assert_exact_flt(actual: &mettail_runtime::FltNode, expected: &mettail_runtime::FltNode) {
    assert_eq!(actual, expected);
    assert_exact(&actual.selector, &expected.selector);
}

#[test]
fn captured_flt_arc_shares_clone_and_checks_selector_binding_without_reparsing() {
    let name = FreeVar::fresh_named("λ");
    let source = Arc::new(flt_binding_fixture(name.clone()));
    let roster = vec![Binder(name)];
    let state = ScopeState::new().incr().incr();
    let (cloned, used, calls) = copy_with_limits(&source, BindingOperation::Clone, (3, 4), None);
    let cloned = cloned.expect("paid captured FLT sharing");
    assert!(Arc::ptr_eq(&source, &cloned));
    assert_eq!((used, calls), ((3, 4), 1));
    drop(cloned);
    for operation in [
        BindingOperation::Close { state, binders: &roster },
        BindingOperation::Open { state, binders: &roster },
    ] {
        let mut input = source.as_ref().clone();
        if matches!(operation, BindingOperation::Open { .. }) {
            input.selector = bound(2, 0, "old");
        }
        let mut expected = input.clone();
        match operation {
            BindingOperation::Close { .. } => expected.close_term(state, &roster),
            BindingOperation::Open { .. } => expected.open_term(state, &roster),
            _ => unreachable!(),
        }
        let (_, leaf_used, leaf_calls) =
            copy_with_limits(&input, operation, (usize::MAX, usize::MAX), None);
        let input = Arc::new(input);
        let total = (leaf_used.0 + 3, leaf_used.1 + 4);
        let (result, used, calls) = copy_with_limits(&input, operation, total, None);
        let copied = result.expect("paid captured FLT binding");
        assert!(!Arc::ptr_eq(&input, &copied));
        assert_exact_flt(&copied, &expected);
        assert_eq!((used, calls), (total, leaf_calls + 1));
        for stop in 1..=calls {
            let (result, _, observed) = copy_with_limits(&input, operation, total, Some(stop));
            assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
            assert_eq!(observed, stop);
            assert_eq!(Arc::strong_count(&input), 1);
        }
        for limits in [(total.0 - 1, total.1), (total.0, total.1 - 1)] {
            assert_eq!(
                copy_with_limits(&input, operation, limits, None).0,
                Err(BindingFailure::Reservation("limit"))
            );
        }
        assert_exact_flt(
            &copy_with_limits(&input, operation, total, None)
                .0
                .expect("retry"),
            &expected,
        );
    }
    for limits in [(2, 4), (3, 3)] {
        assert_eq!(
            copy_with_limits(&source, BindingOperation::Clone, limits, None).0,
            Err(BindingFailure::Reservation("limit"))
        );
        assert_eq!(Arc::strong_count(&source), 1);
    }
}

#[test]
fn flt_copy_binding_preserves_payload_and_admits_every_copy_and_inspection() {
    let variable: FreeVar<String> = FreeVar::fresh_named("λ");
    let source = flt_binding_fixture(variable.clone());
    let mut selected = variable;
    selected.pretty_name = Some("selected".into());
    let roster = vec![Binder(selected)];
    let state = ScopeState::new().incr().incr();
    let mut closed_source = source.clone();
    closed_source.selector = bound(2, 0, "oldhint");
    // Independently counted: five strings=47 bytes, holes=8, text pieces=16.
    // Records=8+(3+2)+(2+1+2+1)=19. Copy+cleanup work=2*19+71;
    // payload charge=(109,147); inspection=7. Selector cleanup is separate.
    for (input, operation, selector_trace, totals) in [
        (source.clone(), BindingOperation::Clone, vec![(1, 0), (4, 6)], (121, 153)),
        (
            source.clone(),
            BindingOperation::Close { state, binders: &roster },
            vec![(1, 0), (1, 0), (4, 6)],
            (122, 153),
        ),
        (
            closed_source,
            BindingOperation::Open { state, binders: &roster },
            vec![(1, 0), (10, 12)],
            (127, 159),
        ),
    ] {
        let original = input.clone();
        let mut expected = input.clone();
        match operation {
            BindingOperation::Clone => {},
            BindingOperation::Close { .. } => expected.close_term(state, &roster),
            BindingOperation::Open { .. } => expected.open_term(state, &roster),
        }
        let mut trace = vec![(7usize, 0usize)];
        trace.extend(std::iter::repeat_n((0, 0), 6));
        trace.extend(selector_trace);
        trace.push((109, 147));
        let sum = |parts: &[(usize, usize)]| {
            parts
                .iter()
                .fold((0, 0), |(w, u), &(dw, du)| (w + dw, u + du))
        };
        assert_eq!(sum(&trace), totals);
        let mut observed = Vec::new();
        let copied = input
            .try_copy_binding(operation, &mut |work, units| {
                observed.push((work, units));
                Ok::<(), &'static str>(())
            })
            .expect("FLT copy");
        assert_eq!(observed, trace);
        assert_exact_flt(&copied, &expected);
        assert_exact_flt(&input, &original);
        let (result, used, calls) = copy_with_limits(&input, operation, totals, None);
        assert_exact_flt(&result.expect("exact FLT budget"), &expected);
        assert_eq!((used, calls), (totals, trace.len()));
        let paid_prefix = sum(&trace[..trace.len() - 1]);
        for limits in [(totals.0 - 1, totals.1), (totals.0, totals.1 - 1)] {
            let (result, used, calls) = copy_with_limits(&input, operation, limits, None);
            assert_eq!(result, Err(BindingFailure::Reservation("limit")));
            assert_eq!((used, calls), (paid_prefix, trace.len()));
            assert_exact_flt(&input, &original);
        }
        for cancelled in 1..=trace.len() {
            let (result, used, calls) =
                copy_with_limits(&input, operation, totals, Some(cancelled));
            assert_eq!(result, Err(BindingFailure::Reservation("cancelled")));
            assert_eq!((used, calls), (sum(&trace[..cancelled - 1]), cancelled));
            assert_exact_flt(&input, &original);
        }
        assert_exact_flt(
            &copy_with_limits(&input, operation, totals, None)
                .0
                .expect("retry"),
            &expected,
        );
        let mut other_bounds = input.clone();
        other_bounds.bounds = Default::default();
        let (_, other_used, _) = copy_with_limits(&other_bounds, operation, totals, None);
        assert_eq!(other_used, totals, "declared bounds never reduce copy cost");
    }
}

#[test]
fn binding_parts_checks_every_arithmetic_boundary_before_callback() {
    for (work, records, bytes) in
        [(usize::MAX, 0, 1), (0, usize::MAX / 4 + 1, 0), (0, usize::MAX / 4, 4)]
    {
        let mut calls = 0;
        let result = mettail_runtime::reserve_binding_parts(work, records, bytes, &mut |_, _| {
            calls += 1;
            Ok::<(), &'static str>(())
        });
        assert_eq!(result, Err(BindingFailure::SizeOverflow));
        assert_eq!(calls, 0);
    }
}

#[test]
fn flt_copy_preserves_repeated_hole_ids_and_optional_empty_category() {
    let mut source = flt_binding_fixture(FreeVar::fresh_unnamed());
    source.holes[1].category = Some(String::new());
    source.pieces.push(source.pieces[1].clone());
    let original = source.clone();
    let (result, used, _) =
        copy_with_limits(&source, BindingOperation::Clone, (usize::MAX, usize::MAX), None);
    assert_exact_flt(&result.expect("structural copy"), &original);
    // An empty category still has a string header; a repeated hole occurrence
    // still has its own piece record. Neither changes the payload bytes.
    source.holes[1].category = None;
    let (_, without_header, _) =
        copy_with_limits(&source, BindingOperation::Clone, (usize::MAX, usize::MAX), None);
    assert_eq!(used, (without_header.0 + 2, without_header.1 + 4));
    source.selector = bound(0, 4, "unresolved");
    let (result, _, _) = copy_with_limits(
        &source,
        BindingOperation::Open { state: ScopeState::new(), binders: &[] },
        (usize::MAX, usize::MAX),
        None,
    );
    assert_eq!(result, Err(BindingFailure::MissingBinder { index: 4 }));
    assert_exact(&source.selector, &bound(0, 4, "unresolved"));
}

#[test]
fn behavioral_leaf_uses_shared_meter_and_keeps_host_binding_inert() {
    use mettail_runtime::{BehavioralPred, PredArg};
    let source = BehavioralPred::RelationQuery {
        relation_name: "r".into(),
        args: vec![PredArg::Var("x".into())],
        negated: false,
    };
    let roster = vec![Binder(FreeVar::fresh_named("x"))];
    // Existing worker: 12 logical work, 8 records, 2 owned bytes.
    // Runtime projection: work14, retention34. The matching textual name is
    // a predicate argument, not a Moniker variable to close/open here.
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
        let (result, used, calls) = copy_with_limits(&source, operation, (14, 34), None);
        assert_eq!(result.expect("predicate leaf copy"), source);
        assert_eq!(used, (14, 34));
        for limits in [(13, 34), (14, 33)] {
            assert_eq!(
                copy_with_limits(&source, operation, limits, None).0,
                Err(BindingFailure::Reservation("limit"))
            );
        }
        for cancel in 1..=calls {
            assert_eq!(
                copy_with_limits(&source, operation, (14, 34), Some(cancel)).0,
                Err(BindingFailure::Reservation("cancelled"))
            );
        }
        assert_eq!(
            copy_with_limits(&source, operation, (14, 34), None)
                .0
                .expect("retry"),
            source
        );
    }
}
