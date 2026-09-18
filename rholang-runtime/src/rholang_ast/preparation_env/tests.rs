use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use std::cell::Cell;

fn run(
    root: &BoundEnv,
    derivation: EnvironmentDerivation<'_>,
    work_limit: u64,
    bytes: usize,
) -> (Result<BoundEnv, RholangAstLowerError>, u64, usize, usize) {
    let mut arena = EnvArena::new(root);
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, bytes, &mut cancel);
    let result = arena.derive(ROOT_ENV, derivation, &mut |work, bytes| {
        budget
            .charge(work, bytes)
            .map_err(RholangAstLowerError::Preparation)
    });
    let count = arena.derived.len();
    let result = result.map(|_| arena.derived.pop().expect("successful derivation appended"));
    (result, budget.work_used(), budget.remaining_bytes(), count)
}

fn two_occurrences() -> (BoundEnv, [ReceiveSlot; 1]) {
    let mut root = BoundEnv::with_options(LoweringOptions::NO_DISCHARGE);
    root.admission = SourceAdmissionMode::Public;
    root.scope_width = 1;
    root.hole_binders.insert("aa".into(), 0);
    (root, [ReceiveSlot::Hole("bbb".into())])
}

fn same_context(actual: &BoundEnv, expected: &BoundEnv) {
    assert_eq!(actual.scope_width, expected.scope_width);
    assert_eq!(actual.binders, expected.binders);
    assert_eq!(actual.hole_binders, expected.hole_binders);
    assert_eq!(actual.construction_holes, expected.construction_holes);
    assert_eq!(actual.options, expected.options);
    assert_eq!(actual.admission, expected.admission);
    assert_eq!(actual.free_vars_are_patterns, expected.free_vars_are_patterns);
    assert!(Arc::ptr_eq(&actual.resolver, &expected.resolver));
    assert!(Arc::ptr_eq(&actual.caller_imports, &expected.caller_imports));
}

#[test]
fn exact_and_under_environment_limits_preserve_paid_prefix_and_input() {
    let (root, slots) = two_occurrences();
    // n=3, s=1, b=8: old FLT capture plus both new capture namespaces.
    // Inspection 3; copy 13 work and 24 payload units.
    for (work_limit, bytes, error, paid) in [
        (0, 24, Some(DynamicReflectionError::WorkLimit), 0),
        (2, 24, Some(DynamicReflectionError::WorkLimit), 0),
        (3, 24, Some(DynamicReflectionError::WorkLimit), 3),
        (15, 24, Some(DynamicReflectionError::WorkLimit), 3),
        (16, 0, Some(DynamicReflectionError::PayloadByteLimit), 3),
        (16, 23, Some(DynamicReflectionError::PayloadByteLimit), 3),
        (16, 24, None, 16),
    ] {
        let (result, used, remaining, count) =
            run(&root, EnvironmentDerivation::Slots(&slots), work_limit, bytes);
        assert_eq!(used, paid);
        match error {
            Some(error) => {
                assert_eq!(result.err(), Some(RholangAstLowerError::Preparation(error)));
                assert_eq!((remaining, count), (bytes, 0));
            },
            None => {
                same_context(
                    &result.expect("exact allowance"),
                    &root.extend_slots(&slots).expect("existing helper"),
                );
                assert_eq!((remaining, count), (0, 1));
            },
        }
        assert_eq!(root.scope_width, 1);
        assert_eq!(root.hole_binders.len(), 1);
        assert_eq!(root.hole_binders.get("aa"), Some(&0));
    }
}

#[test]
fn cancellation_at_every_environment_poll_never_appends() {
    let (root, slots) = two_occurrences();
    // Initial reservation, two length polls, terminal poll, final copy debit.
    for cancelled_call in 1..=5 {
        let calls = Cell::new(0);
        let mut cancel = || {
            calls.set(calls.get() + 1);
            calls.get() == cancelled_call
        };
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 16, 24, &mut cancel);
        let mut arena = EnvArena::new(&root);
        let result =
            arena.derive(ROOT_ENV, EnvironmentDerivation::Slots(&slots), &mut |work, bytes| {
                budget
                    .charge(work, bytes)
                    .map_err(RholangAstLowerError::Preparation)
            });
        assert_eq!(
            result,
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        );
        assert!(arena.derived.is_empty());
        assert_eq!(budget.work_used(), if cancelled_call == 1 { 0 } else { 3 });
        assert_eq!(budget.remaining_bytes(), 24);
        assert_eq!(calls.get(), cancelled_call);
        assert_eq!(root.hole_binders.get("aa"), Some(&0));
    }
}

#[test]
fn duplicate_slots_pay_for_occurrences_and_keep_last_binding_and_full_width() {
    let mut root = BoundEnv::new();
    let identity = FreeVar::fresh_named("x".to_string());
    root.scope_width = 2;
    root.binders.insert(identity.clone(), 1);
    root.hole_binders.insert("h".into(), 0);
    let slots = [
        ReceiveSlot::Moniker(Binder(identity.clone())),
        ReceiveSlot::Hole("h".into()),
        ReceiveSlot::Moniker(Binder(identity.clone())),
    ];
    // Eight one-byte key occurrences, two shifts; duplicate aliases still pay.
    let (result, used, bytes, count) = run(&root, EnvironmentDerivation::Slots(&slots), 27, 44);
    let env = result.expect("all duplicate occurrences reserved");
    assert_eq!((used, bytes, count), (27, 0, 1));
    assert_eq!(env.scope_width, 5);
    assert_eq!(env.binders.get(&identity), Some(&0));
    assert_eq!(env.hole_binders.get("h"), Some(&1));
    assert_eq!((env.binders.len(), env.hole_binders.len()), (1, 1));
    same_context(&env, &root.extend_slots(&slots).expect("existing slots"));
}

#[test]
fn binder_copy_counts_utf8_bytes_and_accepts_unnamed_identities() {
    let root = BoundEnv::new();
    let binders = [Binder(FreeVar::fresh_unnamed()), Binder(FreeVar::fresh_named("λ".to_string()))];
    let (result, used, bytes, count) = run(&root, EnvironmentDerivation::Binders(&binders), 7, 14);
    let env = result.expect("unnamed identity remains valid");
    assert_eq!((used, bytes, count), (7, 0, 1));
    same_context(&env, &extend_env(&root, &binders).expect("existing binder helper"));
    assert_eq!(env.binders.get(&binders[0].0), Some(&1));
    assert_eq!(env.binders.get(&binders[1].0), Some(&0));
}

#[test]
fn pattern_copy_preserves_context_and_does_not_charge_shifts() {
    let (root, _) = two_occurrences();
    let (result, used, bytes, count) = run(&root, EnvironmentDerivation::Pattern, 5, 10);
    same_context(&result.expect("paid pattern"), &root.in_pattern_position());
    assert_eq!((used, bytes, count), (5, 0, 1));
    assert!(!root.free_vars_are_patterns);
}

#[test]
fn helper_overflow_keeps_full_reservation_but_publishes_no_environment() {
    let (mut root, slots) = two_occurrences();
    root.hole_binders.insert("aa".into(), usize::MAX);
    let (result, used, bytes, count) = run(&root, EnvironmentDerivation::Slots(&slots), 16, 24);
    assert_eq!(result.err(), Some(RholangAstLowerError::ScopeIndexOverflow));
    assert_eq!((used, bytes, count), (16, 0, 0));
    assert_eq!(root.hole_binders.get("aa"), Some(&usize::MAX));
}

#[test]
fn environment_cost_checks_every_arithmetic_boundary_without_allocation() {
    for (occurrences, shifted, bytes) in [
        (usize::MAX, 0, 0),
        (0, usize::MAX, 0),
        (0, 0, usize::MAX),
        (usize::MAX / 4, 0, 0),
        (0, 0, usize::MAX - 3),
    ] {
        assert_eq!(
            environment_copy_cost(occurrences, shifted, bytes),
            Err(RholangAstLowerError::PreparationSizeOverflow)
        );
    }
    assert_eq!(environment_copy_cost(0, 0, usize::MAX - 4), Ok((usize::MAX - 3, usize::MAX)));
    let mut bytes = usize::MAX;
    assert_eq!(add_key_bytes(&mut bytes, 1), Err(RholangAstLowerError::PreparationSizeOverflow));
    assert_eq!(bytes, usize::MAX);
}

#[test]
fn map_insertion_order_does_not_change_reservations_or_semantics() {
    let mut lhs = BoundEnv::new();
    let mut rhs = BoundEnv::new();
    rhs.resolver = Arc::clone(&lhs.resolver);
    rhs.caller_imports = Arc::clone(&lhs.caller_imports);
    let names = ["short", "λ", "longer-key"];
    for (index, name) in names.iter().enumerate() {
        lhs.hole_binders.insert((*name).into(), index);
    }
    for (index, name) in names.iter().enumerate().rev() {
        rhs.hole_binders.insert((*name).into(), index);
    }
    lhs.scope_width = names.len();
    rhs.scope_width = names.len();
    let mut traces = Vec::new();
    let mut outputs = Vec::new();
    for root in [&lhs, &rhs] {
        let mut arena = EnvArena::new(root);
        let mut trace = Vec::new();
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, 100, &mut cancel);
        arena
            .derive(ROOT_ENV, EnvironmentDerivation::Pattern, &mut |work, units| {
                trace.push((work, units));
                budget
                    .charge(work, units)
                    .map_err(RholangAstLowerError::Preparation)
            })
            .expect("paid pattern");
        outputs.push(arena.derived.pop().expect("one derived context"));
        traces.push((trace, budget.work_used(), budget.remaining_bytes()));
    }
    assert_eq!(traces[0], traces[1]);
    same_context(&outputs[0], &outputs[1]);
}
