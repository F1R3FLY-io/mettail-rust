//! Real leaf/Arc coverage for the shared iterative scope constructor.
//! Compare stored identities and coordinates, not cached alpha equivalence.

use std::sync::Arc;

use mettail_runtime::{IterativeBinding, OrdVar, Scope};
use moniker::{Binder, BinderIndex, BoundTerm, BoundVar, FreeVar, ScopeOffset, ScopeState, Var};

fn free(name: &str) -> FreeVar<String> {
    FreeVar::fresh_named(name.to_owned())
}

fn bound(depth: u32, index: u32, pretty: Option<&str>) -> OrdVar {
    OrdVar(Var::Bound(BoundVar {
        scope: ScopeOffset(depth),
        binder: BinderIndex(index),
        pretty_name: pretty.map(str::to_owned),
    }))
}

fn assert_same_var(actual: &OrdVar, expected: &OrdVar) {
    match (&actual.0, &expected.0) {
        (Var::Free(actual), Var::Free(expected)) => {
            assert_eq!(actual.unique_id, expected.unique_id);
            assert_eq!(actual.pretty_name, expected.pretty_name);
        },
        (Var::Bound(actual), Var::Bound(expected)) => {
            assert_eq!(actual.scope, expected.scope);
            assert_eq!(actual.binder, expected.binder);
            assert_eq!(actual.pretty_name, expected.pretty_name);
        },
        _ => panic!("variable variants differ: {actual:?} versus {expected:?}"),
    }
}

fn assert_same_pattern(actual: &[Binder<String>], expected: &[Binder<String>]) {
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        assert_eq!(actual.0.unique_id, expected.0.unique_id);
        assert_eq!(actual.0.pretty_name, expected.0.pretty_name);
    }
}

fn compare_constructors(
    pattern: Vec<Binder<String>>,
    body: OrdVar,
) -> Scope<Vec<Binder<String>>, OrdVar> {
    let ordinary = Scope::new::<String>(pattern.clone(), body.clone());
    let iterative = Scope::new_iterative(pattern.clone(), body.clone());
    let moniker = moniker::Scope::new::<String>(pattern.clone(), body);
    assert_same_pattern(ordinary.unsafe_pattern(), &pattern);
    assert_same_pattern(iterative.unsafe_pattern(), &pattern);
    assert_same_pattern(&moniker.unsafe_pattern, &pattern);
    assert_same_var(ordinary.unsafe_body(), &moniker.unsafe_body);
    assert_same_var(iterative.unsafe_body(), &moniker.unsafe_body);
    iterative
}

#[test]
fn constructors_preserve_order_and_close_at_zero() {
    let first = free("first");
    let second = free("second");
    let pattern = vec![Binder(first.clone()), Binder(second.clone())];
    let first_scope = compare_constructors(pattern.clone(), OrdVar(Var::Free(first.clone())));
    assert_same_var(first_scope.unsafe_body(), &bound(0, 0, Some("first")));
    let second_scope = compare_constructors(pattern, OrdVar(Var::Free(second.clone())));
    assert_same_var(second_scope.unsafe_body(), &bound(0, 1, Some("second")));
    let reversed =
        compare_constructors(vec![Binder(second), Binder(first.clone())], OrdVar(Var::Free(first)));
    assert_same_var(reversed.unsafe_body(), &bound(0, 1, Some("first")));
}

#[test]
fn duplicate_binders_keep_all_positions_and_first_match_wins() {
    let repeated = free("repeated");
    let other = free("other");
    let pattern = vec![Binder(repeated.clone()), Binder(other.clone()), Binder(repeated.clone())];
    let repeated_scope = compare_constructors(pattern.clone(), OrdVar(Var::Free(repeated)));
    assert_eq!(repeated_scope.unsafe_pattern().len(), 3);
    assert_same_var(repeated_scope.unsafe_body(), &bound(0, 0, Some("repeated")));
    let other_scope = compare_constructors(pattern, OrdVar(Var::Free(other)));
    assert_same_var(other_scope.unsafe_body(), &bound(0, 1, Some("other")));
}

#[test]
fn equal_pretty_names_do_not_replace_identity_matching() {
    let first = free("same");
    let second = free("same");
    let outside = free("same");
    assert_ne!(first.unique_id, second.unique_id);
    assert_ne!(second.unique_id, outside.unique_id);
    let pattern = vec![Binder(first), Binder(second.clone())];
    let selected = compare_constructors(pattern.clone(), OrdVar(Var::Free(second)));
    assert_same_var(selected.unsafe_body(), &bound(0, 1, Some("same")));
    let untouched = OrdVar(Var::Free(outside));
    let scope = compare_constructors(pattern, untouched.clone());
    assert_same_var(scope.unsafe_body(), &untouched);
}

#[test]
fn empty_unnamed_and_utf8_binders_match_existing_constructor() {
    let unbound = OrdVar(Var::Free(free("outside")));
    let empty = compare_constructors(Vec::new(), unbound.clone());
    assert_same_var(empty.unsafe_body(), &unbound);
    let variables: Vec<FreeVar<String>> = vec![FreeVar::fresh_unnamed(), free(""), free("λ雪🙂")];
    let pattern: Vec<_> = variables.iter().cloned().map(Binder).collect();
    for (index, variable) in variables.iter().enumerate() {
        let scope = compare_constructors(pattern.clone(), OrdVar(Var::Free(variable.clone())));
        assert_same_var(
            scope.unsafe_body(),
            &bound(
                0,
                u32::try_from(index).expect("three test binders fit u32"),
                variable.pretty_name.as_deref(),
            ),
        );
    }
}

#[test]
fn nonzero_state_close_and_open_match_real_moniker_leaf_operations() {
    let variable = free("深さ");
    let roster = vec![Binder(variable.clone())];
    let state = ScopeState::new().incr().incr();
    assert_eq!(state.depth(), ScopeOffset(2));
    let source = OrdVar(Var::Free(variable.clone()));
    let mut expected_closed = source.clone();
    expected_closed.close_term(state, &roster);
    let closed = source.close_iterative(state, &roster);
    assert_same_var(&source, &OrdVar(Var::Free(variable)));
    assert_same_var(&closed, &expected_closed);
    assert_same_var(&closed, &bound(2, 0, Some("深さ")));
    let mut expected_opened = closed.clone();
    expected_opened.open_term(state, &roster);
    let opened = closed.open_iterative(state, &roster);
    assert_same_var(&opened, &expected_opened);
    assert_same_var(&opened, &source);
    assert_same_var(&closed, &bound(2, 0, Some("深さ")));
}

#[test]
fn opening_uses_selected_binder_pretty_name_not_bound_hint() {
    let selected = free("selected");
    let roster = vec![Binder(free("unused")), Binder(selected.clone())];
    let source = bound(0, 1, Some("old diagnostic hint"));
    let opened = source.open_iterative(ScopeState::new(), &roster);
    assert_same_var(&opened, &OrdVar(Var::Free(selected)));
    assert_same_var(&source, &bound(0, 1, Some("old diagnostic hint")));
}

#[test]
fn different_depth_bound_variable_is_unchanged_even_with_missing_index() {
    let roster = vec![Binder(free("available"))];
    let state = ScopeState::new().incr();
    let source = bound(2, 99, Some("preserved"));
    let mut expected_opened = source.clone();
    expected_opened.open_term(state, &roster);
    let opened = source.open_iterative(state, &roster);
    assert_same_var(&opened, &expected_opened);
    assert_same_var(&opened, &source);
    let mut expected_closed = source.clone();
    expected_closed.close_term(state, &roster);
    let closed = source.close_iterative(state, &roster);
    assert_same_var(&closed, &expected_closed);
    assert_same_var(&closed, &source);
}

#[test]
fn free_open_and_unmatched_free_close_are_unchanged() {
    let source = OrdVar(Var::Free(free("outside")));
    let roster = vec![Binder(free("outside"))];
    let opened = source.open_iterative(ScopeState::new(), &roster);
    let closed = source.close_iterative(ScopeState::new(), &roster);
    assert_same_var(&opened, &source);
    assert_same_var(&closed, &source);
}

#[test]
fn arc_close_and_open_leave_inputs_unchanged_and_return_distinct_arcs() {
    let variable = free("arc");
    let roster = vec![Binder(variable.clone())];
    let source = Arc::new(OrdVar(Var::Free(variable.clone())));
    let source_alias = Arc::clone(&source);
    let closed = source.close_iterative(ScopeState::new(), &roster);
    assert!(Arc::ptr_eq(&source, &source_alias));
    assert!(!Arc::ptr_eq(&source, &closed));
    assert_same_var(source.as_ref(), &OrdVar(Var::Free(variable.clone())));
    assert_same_var(closed.as_ref(), &bound(0, 0, Some("arc")));
    let closed_alias = Arc::clone(&closed);
    let opened = closed.open_iterative(ScopeState::new(), &roster);
    assert!(Arc::ptr_eq(&closed, &closed_alias));
    assert!(!Arc::ptr_eq(&closed, &opened));
    assert_same_var(closed.as_ref(), &bound(0, 0, Some("arc")));
    assert_same_var(opened.as_ref(), &OrdVar(Var::Free(variable)));
}

#[test]
fn arc_scope_constructors_match_without_mutating_shared_input() {
    let variable = free("shared");
    let pattern = vec![Binder(variable.clone())];
    let source = Arc::new(OrdVar(Var::Free(variable.clone())));
    let ordinary = Scope::new::<String>(pattern.clone(), Arc::clone(&source));
    let iterative = Scope::new_iterative(pattern.clone(), Arc::clone(&source));
    let moniker = moniker::Scope::new::<String>(pattern.clone(), Arc::clone(&source));
    assert_same_pattern(ordinary.unsafe_pattern(), &pattern);
    assert_same_pattern(iterative.unsafe_pattern(), &pattern);
    assert_same_pattern(&moniker.unsafe_pattern, &pattern);
    assert_same_var(ordinary.unsafe_body().as_ref(), &bound(0, 0, Some("shared")));
    assert_same_var(iterative.unsafe_body().as_ref(), &bound(0, 0, Some("shared")));
    assert_same_var(moniker.unsafe_body.as_ref(), &bound(0, 0, Some("shared")));
    assert_same_var(source.as_ref(), &OrdVar(Var::Free(variable)));
    assert!(!Arc::ptr_eq(&source, iterative.unsafe_body()));
}

#[test]
#[should_panic(expected = "too few variables in pattern")]
fn invalid_iterative_opening_roster_preserves_existing_panic() {
    let roster = vec![Binder(free("only"))];
    let _ = bound(0, 1, None).open_iterative(ScopeState::new(), &roster);
}

#[test]
#[should_panic(expected = "too few variables in pattern")]
fn invalid_moniker_opening_roster_has_the_same_panic() {
    let roster = vec![Binder(free("only"))];
    let mut source = bound(0, 1, None);
    source.open_term(ScopeState::new(), &roster);
}
