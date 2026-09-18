use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use mettail_runtime::Scope;
use models::rhoapi::{EList, EMap, GUnforgeable, KeyValuePair};
use prost::Message;

fn limits() -> ImportLimits {
    ImportLimits {
        entries: 64,
        nodes: 20_000,
        payload_bytes: 1_000_000,
    }
}

fn scalar(value: i64) -> Par {
    new_gint_par(value, vec![], false)
}

fn expression(instance: ExprInstance) -> Par {
    Par::default().with_exprs(vec![Expr { expr_instance: Some(instance) }])
}

fn list(values: Vec<Par>) -> Par {
    expression(ExprInstance::EListBody(EList { ps: values, ..Default::default() }))
}

fn import(value: Par) -> Result<CheckedCallerImports, ImportAdmissionError> {
    CheckedCallerImports::admit(HashMap::from([("value".into(), value)]), limits(), &mut || false)
}

fn new_scope(body: Proc) -> Proc {
    Proc::PNew(Scope::new(vec![Binder(FreeVar::fresh_named("unused"))], Arc::new(body)))
}

fn sample_entries() -> Vec<(String, Par)> {
    vec![
        ("".into(), scalar(7)),
        (
            "z".into(),
            list(vec![scalar(-1), new_gbool_par(true, vec![], false), Par::default()]),
        ),
        (
            "a".into(),
            expression(ExprInstance::EMapBody(EMap {
                kvs: vec![
                    new_key_value_pair(scalar(3), list(vec![])),
                    new_key_value_pair(scalar(3), scalar(9)),
                ],
                ..Default::default()
            })),
        ),
    ]
}

#[test]
fn source_news_retain_every_association_and_canonical_outer_key_order() {
    let inner = Proc::PNewUris(
        vec![Uri::UriText("`z`".into())],
        Scope::new(vec![Binder(FreeVar::fresh_named("uri"))], Arc::new(Proc::PZero)),
    );
    let source = new_scope(inner);
    let expected: BTreeMap<_, _> = sample_entries().into_iter().collect();
    let mut runs = Vec::new();
    for entries in [sample_entries(), sample_entries().into_iter().rev().collect()] {
        let admitted =
            CheckedCallerImports::admit(entries.into_iter().collect(), limits(), &mut || false)
                .expect("complete caller map");
        let context = BoundEnv::new().with_caller_imports(admitted);
        let actual = session::lower_public_body(&source, context).expect("nested source new");
        let outer = &actual.par.news[0];
        let inner = &outer.p.as_ref().expect("body").news[0];
        assert_eq!(inner.uri, ["z"]);
        for new in [outer, inner] {
            assert_eq!(new.injections.keys().cloned().collect::<Vec<_>>(), ["", "a", "z"]);
            for (key, value) in &expected {
                assert_eq!(new.injections[key].encode_to_vec(), value.encode_to_vec());
            }
        }
        runs.push(actual.par.encode_to_vec());
    }
    assert_eq!(runs[0], runs[1]);
}

#[test]
fn imported_keys_are_not_lexical_bindings_and_scope_extensions_share_the_roster() {
    let context = BoundEnv::new().with_caller_imports(import(scalar(1)).expect("admitted"));
    let free = FreeVar::fresh_named("value");
    let source = Proc::PVar(OrdVar(Var::Free(free.clone())));
    assert!(matches!(
        session::lower_public_body(&source, context.clone()),
        Err(RholangAstLowerError::UnresolvedProcessReference)
    ));
    let extended = extend_env(&context, &[Binder(free)]).expect("lexical binder");
    assert!(Arc::ptr_eq(&context.caller_imports, &extended.caller_imports));
    assert!(Arc::ptr_eq(
        &context.caller_imports,
        &extended.without_lexical_bindings().caller_imports
    ));
    assert!(Arc::ptr_eq(
        &context.caller_imports,
        &extended.in_pattern_position().caller_imports
    ));
    let actual = session::lower_public_body(&source, extended).expect("actual lexical binding");
    assert_eq!(actual.par.encode_to_vec(), new_boundvar_par(0, vec![], false).encode_to_vec());
}

#[test]
fn generated_fold_reply_scope_does_not_inherit_caller_imports() {
    let source = Proc::IntBinProc(
        Arc::new(Proc::CastInt(Arc::new(Int::NumLit(5)))),
        Arc::new(Int::NumLit(8)),
    );
    let context = BoundEnv::new().with_caller_imports(import(scalar(1)).expect("admitted"));
    let actual = session::lower_public_body(&source, context).expect("fold shell");
    assert_eq!(actual.folds.len(), 1);
    assert!(!actual.par.news.is_empty());
    assert!(actual.par.news.iter().all(|new| new.injections.is_empty()));
}

#[tokio::test]
async fn node_execution_preserves_import_fallback_uri_precedence_and_shadowed_binders() {
    use rholang::rust::interpreter::system_processes::FixedChannels;

    fn emit(channel: &str, free: &FreeVar<String>) -> Proc {
        Proc::POutput(
            Arc::new(Name::NQuote(Arc::new(Proc::CastStr(Arc::new(Str::StringLit(
                channel.into(),
            )))))),
            Arc::new(Proc::PDrop(Arc::new(Name::NVar(OrdVar(Var::Free(free.clone())))))),
        )
    }

    // Same printed name, distinct lexical identities across nested scopes.
    let outer = FreeVar::fresh_named("shadowed");
    let inner = FreeVar::fresh_named("shadowed");
    let runtime = FreeVar::fresh_named("runtime");
    let outputs = Proc::PParInfix(
        Arc::new(emit("OUT-OUTER", &outer)),
        Arc::new(Proc::PParInfix(
            Arc::new(emit("OUT-INNER", &inner)),
            Arc::new(emit("OUT-RUNTIME", &runtime)),
        )),
    );
    let source = Proc::PNewUris(
        // Deliberately unsorted, so binder/URI association must move together.
        vec![Uri::UriText("`z:caller:outer`".into()), Uri::UriText("`rho:io:stdout`".into())],
        Scope::new(
            vec![Binder(outer), Binder(runtime)],
            Arc::new(Proc::PNewUris(
                vec![Uri::UriText("`z:caller:inner`".into())],
                Scope::new(vec![Binder(inner)], Arc::new(outputs)),
            )),
        ),
    );
    let admitted = CheckedCallerImports::admit(
        HashMap::from([
            ("z:caller:outer".into(), scalar(7)),
            ("z:caller:inner".into(), scalar(8)),
            ("rho:io:stdout".into(), scalar(999)),
            ("".into(), scalar(0)),
        ]),
        limits(),
        &mut || false,
    )
    .expect("nonempty caller map");
    let lowered =
        session::lower_public_body(&source, BoundEnv::new().with_caller_imports(admitted))
            .expect("used imports in nested source scopes");
    let observed = crate::run::run_normalized_par_for_oracle_and_read_par_channels(
        &lowered.par,
        &["OUT-OUTER", "OUT-INNER", "OUT-RUNTIME"],
    )
    .await
    .expect("existing node reducer, no source parser");
    for (channel, expected) in [
        ("OUT-OUTER", scalar(7)),
        ("OUT-INNER", scalar(8)),
        // Definition::to_urn_map wraps system channels in a write-only
        // bundle. Preserve that actual runtime authority, not the bare ID.
        (
            "OUT-RUNTIME",
            Par::default().with_bundles(vec![models::rhoapi::Bundle {
                body: Some(FixedChannels::stdout()),
                write_flag: true,
                read_flag: false,
            }]),
        ),
    ] {
        let values = &observed[channel];
        assert_eq!(values.len(), 1, "exactly one output on {channel}");
        assert_eq!(values[0].encode_to_vec(), expected.encode_to_vec(), "{channel}");
    }
}

#[test]
fn every_admitted_primitive_keeps_its_exact_payload() {
    for value in [
        scalar(i64::MIN),
        new_gbool_par(false, vec![], false),
        new_gstring_par("λ\u{0}text".into(), vec![], false),
        expression(ExprInstance::GUri("rho:registry:untrusted-data".into())),
        expression(ExprInstance::GByteArray(vec![0, 255])),
        expression(ExprInstance::GDouble(0x7ff8_0000_0000_0001)),
        GPrivateBuilder::new_par_from_string("opaque-original-id".into()),
    ] {
        let expected = value.encode_to_vec();
        let actual = import(value).expect("admitted carrier");
        assert_eq!(actual.entries[0].1.encode_to_vec(), expected);
    }
}

#[test]
fn malformed_open_and_executable_imports_fail_without_an_admitted_table() {
    let mut stale_child = scalar(1);
    stale_child.locally_free = vec![0];
    let mut stale_parent = scalar(1);
    stale_parent.connective_used = true;
    let mut executable = scalar(1);
    executable.conditionals.push(Default::default());
    let cases = [
        (Par::default(), ImportShapeError::RootNil),
        (stale_parent, ImportShapeError::OpenMetadata),
        (list(vec![stale_child]), ImportShapeError::OpenMetadata),
        (executable, ImportShapeError::ProcessSidecar),
        (
            Par::default().with_exprs(vec![Expr::default()]),
            ImportShapeError::MissingInstance,
        ),
        (
            Par::default().with_unforgeables(vec![GUnforgeable::default()]),
            ImportShapeError::MissingInstance,
        ),
        (scalar(1).append(scalar(2)), ImportShapeError::NotSingleton),
        (
            expression(ExprInstance::EVarBody(Default::default())),
            ImportShapeError::UnsupportedExpression,
        ),
        (
            expression(ExprInstance::EListBody(EList {
                remainder: Some(Default::default()),
                ..Default::default()
            })),
            ImportShapeError::OpenCollection,
        ),
        (
            expression(ExprInstance::EMapBody(EMap {
                kvs: vec![KeyValuePair { key: Some(scalar(1)), value: None }],
                ..Default::default()
            })),
            ImportShapeError::MissingMapField,
        ),
    ];
    for (value, error) in cases {
        assert_eq!(import(value).err(), Some(ImportAdmissionError::Shape(error)));
        assert!(import(scalar(2)).is_ok(), "refusal does not poison another request");
    }
}

#[test]
fn whole_map_limits_and_cancellation_are_checked_before_admission() {
    for (bounded, resource) in [
        (ImportLimits { entries: 0, ..limits() }, ImportResource::Entries),
        (ImportLimits { nodes: 1, ..limits() }, ImportResource::Nodes),
        (ImportLimits { payload_bytes: 5, ..limits() }, ImportResource::PayloadBytes),
    ] {
        assert_eq!(
            CheckedCallerImports::admit(
                HashMap::from([("key".into(), list(vec![scalar(1)]))]),
                bounded,
                &mut || false
            )
            .err(),
            Some(ImportAdmissionError::LimitExceeded(resource))
        );
    }
    let mut polls = 0;
    let result = CheckedCallerImports::admit(
        HashMap::from([("key".into(), list(vec![scalar(1), scalar(2)]))]),
        limits(),
        &mut || {
            polls += 1;
            polls == 5
        },
    );
    assert_eq!(result.err(), Some(ImportAdmissionError::Cancelled));
    assert!(CheckedCallerImports::admit(
        HashMap::new(),
        ImportLimits { entries: 0, nodes: 0, payload_bytes: 0 },
        &mut || false
    )
    .is_ok());
    assert_eq!(
        bounded_add(usize::MAX, 1, usize::MAX, ImportResource::Nodes),
        Err(ImportAdmissionError::LimitExceeded(ImportResource::Nodes))
    );
}

#[test]
fn deep_admission_copy_and_drop_use_bounded_native_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut value = scalar(1);
            for _ in 0..2048 {
                value = list(vec![value]);
            }
            let admitted = import(value).expect("deep borrowed worklist");
            let copies = admitted.values();
            assert_eq!(copies[0].encode_to_vec(), admitted.entries[0].1.encode_to_vec());
            drop(copies);
            drop(admitted);
        })
        .expect("bounded-stack thread")
        .join()
        .expect("iterative traversal/copy/drop");
}

fn sample_imports() -> CheckedCallerImports {
    CheckedCallerImports::admit(sample_entries().into_iter().collect(), limits(), &mut || false)
        .expect("sample imports")
}

#[test]
fn retained_copy_receipts_count_occurrences_and_exact_payloads_in_key_order() {
    let admitted = sample_imports();
    assert_eq!(admitted.keys(), ["", "a", "z"]);
    assert_eq!(
        admitted.copy_receipts,
        [
            ImportCopyReceipt { occurrences: 1, payload_bytes: 8 },
            ImportCopyReceipt { occurrences: 5, payload_bytes: 24 },
            ImportCopyReceipt { occurrences: 4, payload_bytes: 9 },
        ]
    );
    let opaque = import(list(vec![
        GPrivateBuilder::new_par_from_string("original-id".into()),
        expression(ExprInstance::GByteArray(vec![0, 255, 7])),
        new_gstring_par("λ".into(), vec![], false),
    ]))
    .expect("opaque and Unicode payloads");
    let values = opaque.values();
    let ExprInstance::EListBody(value) = values[0].exprs[0].expr_instance.as_ref().unwrap() else {
        panic!("list carrier");
    };
    let Some(UnfInstance::GPrivateBody(private)) = &value.ps[0].unforgeables[0].unf_instance else {
        panic!("private carrier");
    };
    assert_eq!(
        opaque.copy_receipts[0],
        ImportCopyReceipt {
            occurrences: 4,
            payload_bytes: private.id.len() + 3 + "λ".len(),
        }
    );
}

#[test]
fn paid_key_value_copies_preserve_bytes_and_every_refusal_prefix() {
    let admitted = sample_imports();
    let expected: Vec<_> = admitted
        .values()
        .iter()
        .map(Message::encode_to_vec)
        .collect();
    let mut trace = Vec::new();
    let mut reserve = |work, units| {
        trace.push((work, units));
        Ok(())
    };
    let keys = admitted
        .keys_with_reservation(&mut reserve)
        .expect("paid keys");
    let values = admitted
        .values_with_reservation(&mut reserve)
        .expect("paid values");
    assert_eq!(keys, admitted.keys());
    assert_eq!(
        values
            .iter()
            .map(Message::encode_to_vec)
            .collect::<Vec<_>>(),
        expected
    );
    for cut in 0..trace.len() {
        let mut prefix = Vec::new();
        let result = (|| {
            let mut reserve = |work, units| {
                if prefix.len() == cut {
                    return Err(RholangAstLowerError::Preparation(
                        DynamicReflectionError::Cancelled,
                    ));
                }
                prefix.push((work, units));
                Ok(())
            };
            let keys = admitted.keys_with_reservation(&mut reserve)?;
            let values = admitted.values_with_reservation(&mut reserve)?;
            Ok::<_, RholangAstLowerError>((keys, values))
        })();
        assert!(matches!(
            result,
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        ));
        assert_eq!(prefix, trace[..cut]);
        assert_eq!(
            admitted
                .values()
                .iter()
                .map(Message::encode_to_vec)
                .collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn repeated_paid_copies_reuse_the_same_budget_with_exact_and_one_under_limits() {
    let admitted = sample_imports();
    let mut work = 0usize;
    let mut units = 0usize;
    admitted
        .values_with_reservation(&mut |w, u| {
            work += w;
            units += u;
            Ok(())
        })
        .expect("copy trace");
    for (work_limit, unit_limit, succeeds) in [
        (2 * work, 2 * units, true),
        (2 * work - 1, 2 * units, false),
        (2 * work, 2 * units - 1, false),
    ] {
        let mut used = 0;
        let mut cancel = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut used, work_limit as u64, unit_limit, &mut cancel);
        let first = admitted
            .values_with_reservation(&mut |w, u| {
                budget
                    .charge(w, u)
                    .map_err(RholangAstLowerError::Preparation)
            })
            .expect("first complete copy remains affordable");
        assert_eq!(budget.work_used(), work as u64);
        let second = admitted.values_with_reservation(&mut |w, u| {
            budget
                .charge(w, u)
                .map_err(RholangAstLowerError::Preparation)
        });
        assert_eq!(second.is_ok(), succeeds);
        assert!(budget.work_used() >= work as u64);
        if succeeds {
            assert_eq!(second.unwrap(), first);
            assert_eq!(budget.work_used(), work_limit as u64);
            assert_eq!(budget.remaining_bytes(), 0);
        }
    }
}

#[test]
fn receipt_arithmetic_overflow_refuses_before_reservation_callback() {
    for receipt in [
        ImportCopyReceipt {
            occurrences: usize::MAX,
            payload_bytes: 1,
        },
        ImportCopyReceipt {
            occurrences: usize::MAX / 4 + 1,
            payload_bytes: 0,
        },
    ] {
        assert!(receipt
            .reserve(&mut |_, _| panic!("overflow must precede callback"))
            .is_err());
    }
}

#[test]
fn zero_copy_allowance_refuses_even_for_the_empty_roster() {
    for admitted in [CheckedCallerImports::default(), sample_imports()] {
        for (work_limit, units, expected) in [
            (0, 1_000_000, DynamicReflectionError::WorkLimit),
            (1_000_000, 0, DynamicReflectionError::PayloadByteLimit),
        ] {
            let mut used = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut used, work_limit, units, &mut cancel);
            assert_eq!(
                admitted
                    .values_with_reservation(&mut |w, u| {
                        budget
                            .charge(w, u)
                            .map_err(RholangAstLowerError::Preparation)
                    })
                    .err(),
                Some(RholangAstLowerError::Preparation(expected))
            );
            assert_eq!(budget.work_used(), 0);
        }
    }
}

#[test]
fn checked_nested_news_keep_deep_imports_and_exact_shared_budget() {
    let source = new_scope(Proc::PNewUris(
        vec![Uri::UriText("`deep`".into())],
        Scope::new(vec![Binder(FreeVar::fresh_named("uri"))], Arc::new(Proc::PZero)),
    ));
    let mut deep = GPrivateBuilder::new_par_from_string("original-private-id".into());
    for _ in 0..32 {
        deep = list(vec![deep]);
    }
    let expected = deep.encode_to_vec();
    let admitted =
        CheckedCallerImports::admit(HashMap::from([("deep".into(), deep)]), limits(), &mut || {
            false
        })
        .expect("deep original import");
    let context = BoundEnv::new().with_caller_imports(admitted);
    let original = session::lower_public_body(&source, context.clone()).expect("original New");
    let run = |work_limit, units| {
        let mut used = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut used, work_limit, units, &mut cancel);
        let result = session::lower_public_body_with_budget(&source, context.clone(), &mut budget);
        (result, budget.work_used(), units - budget.remaining_bytes())
    };
    let (result, work, units) = run(100_000_000, 100_000_000);
    let result = result.expect("checked nested New");
    assert_eq!(result.par.encode_to_vec(), original.par.encode_to_vec());
    let outer = &result.par.news[0];
    let inner = &outer.p.as_ref().expect("outer body").news[0];
    for new in [outer, inner] {
        assert_eq!(new.injections["deep"].encode_to_vec(), expected);
    }
    assert_eq!(inner.uri, ["deep"]);
    assert!(run(work, units).0.is_ok());
    assert!(run(work - 1, units).0.is_err());
    assert!(run(work, units - 1).0.is_err());
    assert!(run(work, units).0.is_ok(), "failed session must not poison the next request");
}

#[test]
fn paid_deep_copy_and_late_refusal_cleanup_are_stack_safe() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut value = scalar(1);
            for _ in 0..2048 {
                value = list(vec![value]);
            }
            let admitted = import(value).expect("deep admitted input");
            assert_eq!(admitted.copy_receipts[0].occurrences, 2049);
            let expected = admitted.values()[0].encode_to_vec();
            let mut trace = Vec::new();
            let result = admitted
                .values_with_reservation(&mut |w, u| {
                    trace.push((w, u));
                    Ok(())
                })
                .expect("prepaid deep native copy");
            assert_eq!(result[0].encode_to_vec(), expected);
            drop(result);
            let mut calls = 0;
            assert!(matches!(
                admitted.values_with_reservation(&mut |_, _| {
                    calls += 1;
                    if calls == trace.len() {
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    } else {
                        Ok(())
                    }
                }),
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            ));
            drop(
                admitted
                    .values_with_reservation(&mut |_, _| Ok(()))
                    .expect("fresh attempt after refusal"),
            );
            drop(admitted);
        })
        .expect("small-stack thread")
        .join()
        .expect("deep copy and normal cleanup");
}
