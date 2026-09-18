use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use mettail_runtime::{OrdVar, Scope};
use prost::Message;

fn variable(name: &FreeVar<String>) -> Proc {
    Proc::PVar(OrdVar(Var::Free(name.clone())))
}

#[test]
fn paid_scope_opens_map_keys_and_values_including_empty_application_maps() {
    use mettail_languages::rholang::Map;
    use mettail_runtime::HashMapLit;
    for empty in [true, false] {
        let key = Binder(FreeVar::fresh_named("key"));
        let value = Binder(FreeVar::fresh_named("value"));
        let mut entries = HashMapLit::new();
        if !empty {
            entries.insert(variable(&key.0), variable(&value.0));
            entries.insert(variable(&value.0), variable(&key.0));
        }
        let source = Proc::PNew(Scope::new(
            vec![key, value],
            Arc::new(Proc::CastMap(Arc::new(Map::MapLit(entries)))),
        ));
        let expected =
            session::lower_public_body(&source, BoundEnv::new()).expect("original map scope");
        let (actual, work, units) = prepare(&source, BoundEnv::new(), 100_000_000, 100_000_000);
        let actual = actual.expect("checked map scope must no longer refuse MapLit");
        assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
        for (work_limit, unit_limit, succeeds) in
            [(work, units, true), (work - 1, units, false), (work, units - 1, false)]
        {
            assert_eq!(
                prepare(&source, BoundEnv::new(), work_limit, unit_limit)
                    .0
                    .is_ok(),
                succeeds
            );
        }
    }
}

#[test]
fn checked_map_binding_preserves_pair_order_collisions_and_every_refusal_prefix() {
    use mettail_languages::rholang::Map;
    use mettail_runtime::{
        BindingFailure, BindingOperation, BoundTerm, CheckedIterativeBinding, HashMapLit,
    };
    let a = FreeVar::fresh_named("a");
    let b = FreeVar::fresh_named("b");
    let mut entries = HashMapLit::new();
    entries.insert(variable(&a), Proc::PZero);
    entries.insert(variable(&b), variable(&a));
    let source = Map::MapLit(entries);
    let cloned = source
        .try_copy_iterative(BindingOperation::Clone, &mut |_, _| Ok::<_, ()>(()))
        .expect("checked Map clone");
    assert_eq!(cloned, source);
    let close_roster = vec![Binder(a.clone()), Binder(b.clone())];
    let close = BindingOperation::Close {
        state: BindingOperation::Clone.state(),
        binders: &close_roster,
    };
    let mut expected = source.clone();
    expected.close_term(BindingOperation::Clone.state(), &close_roster);
    let closed = source
        .try_copy_iterative(close, &mut |_, _| Ok::<_, ()>(()))
        .unwrap();
    assert_eq!(closed, expected);
    // Opening two distinct bound keys with one repeated binder intentionally
    // collides. Native ordered insertion retains first key/position, last value.
    let merged = FreeVar::fresh_named("merged");
    let open_roster = vec![Binder(merged.clone()), Binder(merged)];
    let open = BindingOperation::Open {
        state: BindingOperation::Clone.state(),
        binders: &open_roster,
    };
    expected.open_term(BindingOperation::Clone.state(), &open_roster);
    let mut trace = Vec::new();
    let actual = closed
        .try_copy_iterative(open, &mut |w, u| {
            trace.push((w, u));
            Ok::<_, ()>(())
        })
        .unwrap();
    assert_eq!(actual, expected);
    let Map::MapLit(actual_entries) = &actual else {
        panic!("Map literal")
    };
    let Map::MapLit(expected_entries) = &expected else {
        panic!("Map literal")
    };
    assert_eq!(actual_entries.len(), 1);
    assert!(actual_entries.iter().eq(expected_entries.iter()));
    for cut in 1..=trace.len() {
        let mut observed = Vec::new();
        let refused = closed.try_copy_iterative(open, &mut |w, u| {
            observed.push((w, u));
            if observed.len() == cut {
                Err(cut)
            } else {
                Ok(())
            }
        });
        assert!(matches!(refused, Err(BindingFailure::Reservation(at)) if at == cut));
        assert_eq!(observed, trace[..cut]);
    }
}

fn nested() -> Proc {
    let outer = Binder(FreeVar::fresh_named("same"));
    let inner = Binder(FreeVar::fresh_named("same"));
    let body = Proc::PParInfix(Arc::new(variable(&outer.0)), Arc::new(variable(&inner.0)));
    Proc::PNew(Scope::new(
        vec![outer],
        Arc::new(Proc::PNew(Scope::new(vec![inner], Arc::new(body)))),
    ))
}

fn uri_scope() -> Proc {
    let a = Binder(FreeVar::fresh_named("a"));
    let b = Binder(FreeVar::fresh_named("b"));
    let body = Proc::PParInfix(Arc::new(variable(&b.0)), Arc::new(variable(&a.0)));
    Proc::PNewUris(
        vec![Uri::UriText("`z`".into()), Uri::UriText("`a`".into())],
        Scope::new(vec![b, a], Arc::new(body)),
    )
}

fn prepare(
    source: &Proc,
    env: BoundEnv,
    work_limit: u64,
    byte_limit: usize,
) -> (Result<session::DirectLoweringOutput, RholangAstLowerError>, u64, usize) {
    let mut used = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut used, work_limit, byte_limit, &mut cancel);
    let result = session::lower_public_body_with_budget(source, env, &mut budget);
    let used_bytes = byte_limit - budget.remaining_bytes();
    (result, budget.work_used(), used_bytes)
}

#[test]
fn paid_scopes_preserve_nested_shadowing_uri_associations_and_repeated_sources() {
    let shared = Arc::new(nested());
    let repeated = Proc::PParInfix(Arc::clone(&shared), shared);
    for source in [nested(), uri_scope(), repeated] {
        let expected =
            session::lower_public_body(&source, BoundEnv::new()).expect("original scope lowering");
        let (actual, work, bytes) = prepare(&source, BoundEnv::new(), 10_000_000, 10_000_000);
        let actual = actual.expect("paid scope preparation");
        assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
        assert_eq!(actual.guard_report, expected.guard_report);
        assert!(actual.folds.is_empty());
        assert!(work > 0 && bytes > 0);
    }
}

#[test]
fn original_scoped_lowering_retains_broader_families_without_checked_fallback() {
    let source = Proc::PNew(Scope::new(
        Vec::<Binder<String>>::new(),
        Arc::new(Proc::CastBag(Arc::new(mettail_languages::rholang::Bag::BagLit(
            mettail_runtime::HashBag::from_iter([Proc::PZero]),
        )))),
    ));
    let original = session::lower_public_body(&source, BoundEnv::new())
        .expect("original scoped Bag lowering remains supported");
    let storage = session::with_owned_outputs(|_| {
        let mut env = BoundEnv::new();
        env.admission = SourceAdmissionMode::Public;
        drive_machine_with_reservation(Seed::Body(&source), &env, &mut |_, _| Ok(()))
    })
    .expect("storage-only internal path retains original source semantics");
    assert_eq!(storage.par.encode_to_vec(), original.par.encode_to_vec());
    assert!(matches!(
        prepare(&source, BoundEnv::new(), 10_000_000, 10_000_000).0,
        Err(RholangAstLowerError::SourceProfile(
            mettail_languages::rholang::SourceProfileError::Unsupported { .. }
        ))
    ));
}

#[test]
fn paid_scope_keeps_nonempty_lexical_context_and_complete_caller_keys() {
    let outside = Binder(FreeVar::fresh_named("outside"));
    let source = Proc::PNew(Scope::new(
        vec![Binder(FreeVar::fresh_named("unused"))],
        Arc::new(variable(&outside.0)),
    ));
    let imports = imports::CheckedCallerImports::admit(
        HashMap::from([
            ("z".into(), new_gint_par(7, vec![], false)),
            ("a".into(), new_gbool_par(true, vec![], false)),
        ]),
        imports::ImportLimits {
            entries: 10,
            nodes: 100,
            payload_bytes: 10_000,
        },
        &mut || false,
    )
    .expect("valid complete caller imports");
    let env = extend_env(&BoundEnv::new().with_caller_imports(imports), &[outside])
        .expect("outer binding");
    let expected =
        session::lower_public_body(&source, env.clone()).expect("original scope context");
    let actual = prepare(&source, env, 10_000_000, 10_000_000)
        .0
        .expect("paid scope context");
    assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
    assert_eq!(
        actual.par.news[0]
            .injections
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["a", "z"]
    );
}

#[test]
fn paid_uri_validation_preserves_original_errors() {
    for (count, uris) in [
        (0, vec![]),
        (2, vec!["`a`"]),
        (1, vec!["a"]),
        (1, vec!["``"]),
        (2, vec!["`a`", "`a`"]),
    ] {
        let source = Proc::PNewUris(
            uris.into_iter()
                .map(|uri| Uri::UriText(uri.into()))
                .collect(),
            Scope::new(
                (0..count)
                    .map(|_| Binder(FreeVar::fresh_named("binder")))
                    .collect::<Vec<_>>(),
                Arc::new(Proc::PZero),
            ),
        );
        let expected = session::lower_public_body(&source, BoundEnv::new())
            .err()
            .expect("invalid URI fixture");
        let actual = prepare(&source, BoundEnv::new(), 10_000_000, 10_000_000)
            .0
            .err()
            .expect("same invalid fixture");
        assert_eq!(actual, expected);
    }
}

#[test]
fn paid_scope_exact_and_one_under_limits_share_the_public_budget() {
    let source = uri_scope();
    let (baseline, work, bytes) = prepare(&source, BoundEnv::new(), 10_000_000, 10_000_000);
    let baseline = baseline
        .expect("measure complete scope preparation")
        .par
        .encode_to_vec();
    let exact = prepare(&source, BoundEnv::new(), work, bytes)
        .0
        .expect("exact limits");
    assert_eq!(exact.par.encode_to_vec(), baseline);
    for (w, b) in [(work - 1, bytes), (work, bytes - 1), (0, bytes), (work, 0)] {
        assert!(prepare(&source, BoundEnv::new(), w, b).0.is_err());
    }
    assert!(prepare(&source, BoundEnv::new(), work, bytes).0.is_ok());
}

#[test]
fn paid_uri_every_callback_cut_refuses_without_changing_source_or_resetting_charges() {
    let source = uri_scope();
    let Proc::PNewUris(uris, scope) = &source else {
        unreachable!()
    };
    let original = scope.unsafe_pattern().clone();
    let original_body = Arc::as_ptr(scope.unsafe_body());
    let mut trace = Vec::new();
    open_uri(uris, scope, &mut |w, u| {
        trace.push((w, u));
        Ok(())
    })
    .expect("complete paid URI path");
    for cut in 0..trace.len() {
        let mut actual = Vec::new();
        let result = open_uri(uris, scope, &mut |w, u| {
            actual.push((w, u));
            if actual.len() == cut + 1 {
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            } else {
                Ok(())
            }
        });
        assert!(matches!(
            result,
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert_eq!(actual, trace[..=cut]);
        assert_eq!(scope.unsafe_pattern(), &original);
        assert_eq!(Arc::as_ptr(scope.unsafe_body()), original_body);
    }
}

#[test]
fn checked_scope_opens_a_deep_generated_body_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let binder = Binder(FreeVar::fresh_named("deep"));
            let closed_leaf = Scope::new(vec![binder.clone()], Arc::new(variable(&binder.0)));
            let mut body = Arc::clone(closed_leaf.unsafe_body());
            for _ in 0..2_048 {
                body = Arc::new(Proc::PParInfix(body, Arc::new(Proc::PZero)));
            }
            let scope = Scope::from_parts_unsafe(vec![binder], body);
            let mut used = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut used, 100_000_000, 100_000_000, &mut cancel);
            let (fresh, opened) = open(&scope, &mut |w, u| {
                budget
                    .charge(w, u)
                    .map_err(RholangAstLowerError::Preparation)
            })
            .expect("generated body opens iteratively");
            let mut cursor = opened.as_ref();
            let mut depth = 0;
            while let Proc::PParInfix(left, _) = cursor {
                depth += 1;
                cursor = left.as_ref();
            }
            assert_eq!(depth, 2_048);
            let Proc::PVar(OrdVar(Var::Free(name))) = cursor else {
                panic!("leaf must open")
            };
            assert_eq!(name.unique_id, fresh[0].0.unique_id);
            assert_eq!(name.pretty_name, fresh[0].0.pretty_name);
        })
        .expect("small-stack test thread")
        .join()
        .expect("checked opening and cleanup fit small stack");
}

#[test]
fn checked_scope_opens_and_cleans_up_a_wide_generated_body_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let binder = Binder(FreeVar::fresh_named("wide"));
            let closed_leaf = Scope::new(vec![binder.clone()], Arc::new(variable(&binder.0)));
            let entries = (0..2_048)
                .map(|index| {
                    if index % 2 == 0 {
                        closed_leaf.unsafe_body().as_ref().clone()
                    } else {
                        Proc::PZero
                    }
                })
                .collect();
            let scope = Scope::from_parts_unsafe(
                vec![binder],
                Arc::new(Proc::CastList(Arc::new(mettail_languages::rholang::List::ListLit(
                    entries,
                )))),
            );
            let source_pointer = Arc::as_ptr(scope.unsafe_body());
            let mut calls = 0;
            let mut used = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut used, 100_000_000, 100_000_000, &mut cancel);
            let (fresh, opened) = open(&scope, &mut |w, u| {
                calls += 1;
                budget
                    .charge(w, u)
                    .map_err(RholangAstLowerError::Preparation)
            })
            .expect("wide generated body opens under the shared finite budget");
            let Proc::CastList(list) = opened.as_ref() else {
                panic!("preserve list carrier")
            };
            let mettail_languages::rholang::List::ListLit(entries) = list.as_ref() else {
                panic!("preserve native vector")
            };
            assert_eq!(entries.len(), 2_048);
            for (index, entry) in entries.iter().enumerate() {
                if index % 2 == 0 {
                    assert!(matches!(entry, Proc::PVar(OrdVar(Var::Free(name)))
                        if name.unique_id == fresh[0].0.unique_id));
                } else {
                    assert!(matches!(entry, Proc::PZero));
                }
            }
            drop(opened);
            for cut in [1, calls / 2, calls] {
                let mut seen = 0;
                let result = open(&scope, &mut |_, _| {
                    seen += 1;
                    if seen == cut {
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    } else {
                        Ok(())
                    }
                });
                assert!(matches!(
                    result,
                    Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                ));
                assert_eq!(seen, cut);
                assert_eq!(Arc::as_ptr(scope.unsafe_body()), source_pointer);
            }
        })
        .expect("small-stack wide test thread")
        .join()
        .expect("wide checked opening and normal refusal cleanup fit small stack");
}
