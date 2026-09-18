use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};

fn integer(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn event(proc: &Proc) -> Option<i64> {
    match proc {
        Proc::CastInt(value) => match value.as_ref() {
            Int::NumLit(value) => Some(*value),
            _ => None,
        },
        Proc::Add(..) => Some(-1),
        Proc::NegProc(..) => Some(-2),
        Proc::CastList(..) => Some(-3),
        Proc::CastMap(..) => Some(-4),
        Proc::PPar(..) => Some(-5),
        Proc::POutput(..) | Proc::PPersistOutput(..) => Some(-6),
        _ => None,
    }
}

fn trace(
    source: &Proc,
    policy: SourcePreparation,
    reserve: &mut StorageReservation<'_>,
) -> Result<Vec<i64>, RholangAstLowerError> {
    let mut events = Vec::new();
    let result = find_first_body_site_preparing(source, policy, reserve, |candidate, _| {
        if let Some(event) = event(candidate) {
            events.push(event);
        }
        Ok(None::<()>)
    })?;
    assert!(result.is_none());
    Ok(events)
}

fn ordered_cases() -> Vec<(Proc, Vec<i64>)> {
    let mut entries = mettail_runtime::HashMapLit::new();
    entries.insert(integer(3), integer(4));
    entries.insert(integer(1), integer(2));
    let list = Proc::CastList(Arc::new(List::ListLit(vec![integer(1), integer(2)])));
    let channel = Name::NParen(Arc::new(Name::NQuote(Arc::new(integer(7)))));
    let bag =
        mettail_runtime::HashBag::new().rebuild_binding_entries([(integer(1), 0), (integer(2), 3)]);
    vec![
        (Proc::Add(Arc::new(integer(1)), Arc::new(integer(2))), vec![1, 2, -1]),
        (Proc::NegProc(Arc::new(integer(1))), vec![1, -2]),
        (list, vec![1, 2, -3]),
        (Proc::CastMap(Arc::new(Map::MapLit(entries))), vec![3, 4, 1, 2, -4]),
        (Proc::PPar(bag), vec![2, 2, 2, -5]),
        (Proc::POutput(Arc::new(channel), Arc::new(integer(8))), vec![7, 8, -6]),
        (
            Proc::PPersistOutput2Plus(
                Arc::new(Name::NQuote(Arc::new(integer(7)))),
                Arc::new(integer(1)),
                vec![integer(2), integer(3)],
            ),
            vec![7, 1, 2, 3, -3, -6],
        ),
    ]
}

#[test]
fn body_finder_preserves_postorder_pairs_multiplicity_and_original_policy() {
    for (source, expected) in ordered_cases() {
        assert_eq!(
            trace(&source, SourcePreparation::Checked, &mut |_, _| Ok(())).expect("checked trace"),
            expected
        );
        assert_eq!(
            trace(&source, SourcePreparation::Original, &mut |_, _| panic!(
                "original policy must not reserve"
            ))
            .expect("original trace"),
            expected
        );
    }
}

#[test]
fn body_finder_every_cut_preserves_source_and_exact_accepted_prefix() {
    fn bag_snapshot(source: &Proc) -> Option<(usize, Vec<(i64, usize)>)> {
        let Proc::PPar(parts) = source else {
            return None;
        };
        Some((
            parts.len(),
            parts
                .iter()
                .map(|(key, count)| (event(key).expect("integer key"), count))
                .collect(),
        ))
    }
    for (source, expected) in ordered_cases() {
        // Native Clone recomputes the intentionally irregular bag's total and
        // drops its stored zero count. Snapshot those original records instead.
        let unchanged_bag = bag_snapshot(&source);
        let unchanged = unchanged_bag.is_none().then(|| source.clone());
        let mut charges = Vec::new();
        assert_eq!(
            trace(&source, SourcePreparation::Checked, &mut |w, u| {
                charges.push((w, u));
                Ok(())
            })
            .expect("complete trace"),
            expected
        );
        for cut in 0..charges.len() {
            let mut accepted = Vec::new();
            let result = trace(&source, SourcePreparation::Checked, &mut |w, u| {
                if accepted.len() == cut {
                    return Err(RholangAstLowerError::Preparation(
                        DynamicReflectionError::Cancelled,
                    ));
                }
                accepted.push((w, u));
                Ok(())
            });
            assert_eq!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            );
            assert_eq!(accepted, charges[..cut]);
            if let Some(unchanged) = &unchanged {
                assert_eq!(&source, unchanged);
            }
            assert_eq!(bag_snapshot(&source), unchanged_bag);
        }
        let work = charges.iter().map(|(w, _)| *w as u64).sum::<u64>();
        let units = charges.iter().map(|(_, u)| *u).sum::<usize>();
        for (work_limit, unit_limit, succeeds) in [
            (work, units, true),
            (work - 1, units, false),
            (work, units - 1, false),
            (0, 0, false),
        ] {
            let mut used = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut used, work_limit, unit_limit, &mut cancel);
            let result = trace(&source, SourcePreparation::Checked, &mut |w, u| {
                budget
                    .charge(w, u)
                    .map_err(RholangAstLowerError::Preparation)
            });
            assert_eq!(result.is_ok(), succeeds);
            if succeeds {
                assert_eq!(result.expect("exact allowance"), expected);
                assert_eq!(budget.work_used(), work);
                assert_eq!(budget.remaining_bytes(), 0);
            }
        }
    }
}

fn flt() -> Arc<FltNode> {
    Arc::new(
        FltNode::new("guest".into(), "Term".into(), "body".into(), vec![], 0)
            .expect("valid template"),
    )
}

#[test]
fn body_finder_keeps_shared_flt_occurrences_and_returns_original_pointer() {
    let node = flt();
    let source = Proc::POutput2Plus(
        Arc::new(Name::NQuote(Arc::new(Proc::PFltFence(node.clone())))),
        Arc::new(Proc::PFlt(node.clone())),
        vec![Proc::PFltBrace(node.clone())],
    );
    let mut occurrences = 0;
    find_first_body_site_preparing(
        &source,
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
        |candidate, _| {
            if let Proc::PFlt(found) | Proc::PFltFence(found) | Proc::PFltBrace(found) = candidate {
                assert!(Arc::ptr_eq(found, &node));
                occurrences += 1;
            }
            Ok(None::<()>)
        },
    )
    .expect("all occurrences");
    assert_eq!(occurrences, 3);
    let mut projected = 0;
    let found = find_first_body_site_preparing(
        &source,
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
        |candidate, build| {
            projected += 1;
            match candidate {
                Proc::PFltFence(found) => build.share(found).map(Some),
                _ => panic!("quoted channel must be the first postorder event"),
            }
        },
    )
    .expect("first occurrence")
    .expect("found FLT");
    assert_eq!(projected, 1);
    assert!(Arc::ptr_eq(&found, &node));
}

#[test]
fn body_finder_treats_nested_binders_and_receive_patterns_as_opaque() {
    let hidden = Arc::new(Proc::PFlt(flt()));
    let name = Arc::new(Name::NQuote(hidden.clone()));
    let source = Proc::CastList(Arc::new(List::ListLit(vec![
        Proc::PNew(mettail_runtime::Scope::new(Vec::<Binder<String>>::new(), hidden.clone())),
        Proc::PNewUris(
            Vec::new(),
            mettail_runtime::Scope::new(Vec::<Binder<String>>::new(), hidden.clone()),
        ),
        Proc::PForUser(
            vec![ForRow::ForRowSingleNoWhere(Arc::new(InputBind::InputBind(name.clone(), name)))],
            hidden,
        ),
    ])));
    find_first_body_site_preparing(
        &source,
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
        |candidate, _| {
            assert!(!matches!(candidate, Proc::PFlt(..)));
            Ok(None::<()>)
        },
    )
    .expect("opaque nested scopes");
}

#[test]
fn negative_fold_search_is_paid_and_excluded_folds_never_enter_evaluation() {
    let source = Proc::Add(Arc::new(integer(1)), Arc::new(integer(2)));
    let mut calls = 0;
    assert!(find_fold_preparing(&source, SourcePreparation::Checked, &mut |_, _| {
        calls += 1;
        Ok(())
    })
    .expect("negative search")
    .is_none());
    assert!(calls > 0);
    assert!(matches!(
        find_fold_preparing(&source, SourcePreparation::Checked, &mut |_, _| Err(
            RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled)
        )),
        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
    ));
    let source = Proc::IntBinProc(Arc::new(integer(1)), Arc::new(Int::NumLit(8)));
    assert!(matches!(
        find_fold_preparing(&source, SourcePreparation::Checked, &mut |_, _| Ok(())),
        Err(RholangAstLowerError::Binding(
            mettail_runtime::BindingFailure::UnsupportedConstructor {
                category: "Proc",
                constructor: "IntBinProc"
            }
        ))
    ));
    assert!(find_fold(&source).is_some(), "internal original fold remains supported");
}

#[test]
fn body_finder_deep_traversal_and_refusal_cleanup_fit_small_stack() {
    let mut source = Proc::PZero;
    for _ in 0..8192 {
        source = Proc::NegProc(Arc::new(source));
    }
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let mut calls = 0;
            assert!(find_first_body_site_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |_, _| {
                    calls += 1;
                    Ok(())
                },
                |_, _| Ok(None::<()>)
            )
            .expect("deep walk")
            .is_none());
            for cut in [0, calls / 2, calls - 1] {
                let mut seen = 0;
                let result = find_first_body_site_preparing(
                    &source,
                    SourcePreparation::Checked,
                    &mut |_, _| {
                        if seen == cut {
                            return Err(RholangAstLowerError::Preparation(
                                DynamicReflectionError::Cancelled,
                            ));
                        }
                        seen += 1;
                        Ok(())
                    },
                    |_, _| Ok(None::<()>),
                );
                assert!(matches!(
                    result,
                    Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                ));
                assert_eq!(seen, cut);
            }
            drop(source);
        })
        .expect("small-stack thread")
        .join()
        .expect("paid body walk and normal cleanup");
}

#[test]
fn selector_lookup_uses_identity_only_and_preserves_native_hit_and_miss() {
    let mut node = flt().as_ref().clone();
    let selector = FreeVar::fresh_named("guest".to_owned());
    node.selector = OrdVar(Var::Free(selector.clone()));
    let mut env = BoundEnv::new();
    env.binders
        .insert(FreeVar::fresh_named("guest".to_owned()), 7);
    env.hole_binders.insert("guest".into(), 8);
    let mut differently_named = selector.clone();
    differently_named.pretty_name = Some("not-the-selector-spelling".into());

    for expected in [None, Some(3)] {
        if expected.is_some() {
            env.binders.insert(differently_named.clone(), 3);
        }
        let mut charges = Vec::new();
        let actual = SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .selector_level(&node, &env)
        .expect("native selector lookup");
        assert_eq!(actual, expected);
        assert_eq!(actual, flt_selector_level(&node, &env));
        assert_eq!(
            charges,
            [
                (1, 0),
                (1, 0),
                (
                    identity_lookup_work(env.binders.len(), env.binders.capacity())
                        .expect("lookup allowance"),
                    0
                )
            ]
        );
        for cut in 0..charges.len() {
            let mut accepted = Vec::new();
            let result = SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
                if accepted.len() == cut {
                    return Err(RholangAstLowerError::Preparation(
                        DynamicReflectionError::Cancelled,
                    ));
                }
                accepted.push((w, u));
                Ok(())
            })
            .selector_level(&node, &env);
            assert_eq!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            );
            assert_eq!(accepted, charges[..cut]);
            assert_eq!(flt_selector_level(&node, &env), expected);
        }
        let source = Proc::PFlt(Arc::new(node.clone()));
        for policy in [SourcePreparation::Original, SourcePreparation::Checked] {
            let found = find_dynamic_flt_preparing(&source, &env, policy, &mut |_, _| Ok(()))
                .expect("selected FLT");
            assert_eq!(found.is_some(), expected.is_some());
            if let Some(found) = found {
                let Proc::PFlt(original) = &source else {
                    panic!("FLT source")
                };
                assert!(Arc::ptr_eq(&found, original));
            }
        }
    }
    let closed = mettail_runtime::Scope::new(vec![Binder(selector)], node.selector.clone());
    node.selector = closed.inner().unsafe_body.clone();
    assert!(matches!(node.selector.0, Var::Bound(_)));
    let mut charges = Vec::new();
    assert_eq!(
        SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .selector_level(&node, &env)
        .expect("bound selector"),
        None
    );
    assert_eq!(charges, [(1, 0)]);
}

#[test]
fn selector_lookup_empty_shortcut_and_checked_arithmetic_are_explicit() {
    assert_eq!(identity_lookup_work(0, usize::MAX).expect("empty shortcut"), 5);
    assert_eq!(identity_lookup_work(1, 3).expect("small map"), 100);
    assert_eq!(identity_lookup_work(7, 7).expect("one group"), 184);
    assert_eq!(identity_lookup_work(14, 14).expect("one conservative group"), 282);
    for (entries, capacity) in [(1, usize::MAX), (usize::MAX, 3), (1, usize::MAX / 2)] {
        assert_eq!(
            identity_lookup_work(entries, capacity),
            Err(RholangAstLowerError::PreparationSizeOverflow)
        );
    }
    let mut env = BoundEnv::new();
    env.binders.reserve(128);
    let mut charges = Vec::new();
    assert_eq!(
        SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .selector_level(&flt(), &env)
        .expect("allocated empty map"),
        None
    );
    assert_eq!(charges, [(1, 0), (1, 0), (5, 0)]);
}
