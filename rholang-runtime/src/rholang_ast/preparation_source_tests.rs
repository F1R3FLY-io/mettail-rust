use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use prost::Message;

fn integer_signs(count: usize) -> Int {
    let mut value = Int::NumLit(7);
    for _ in 0..count {
        value = Int::NegInt(Arc::new(value));
    }
    value
}

#[test]
fn paid_integer_category_negations_preserve_bytes_and_each_refusal_boundary() {
    for count in [0, 1, 4] {
        let source = integer_signs(count);
        let env = BoundEnv::new();
        let mut expected = Target::integer(7);
        for _ in 0..count {
            expected = unary_expr_par(expected, |p| ExprInstance::ENegBody(ENeg { p }));
        }
        let mut trace = Vec::new();
        let actual =
            lower_int_value_preparing(&source, &env, SourcePreparation::Checked, &mut |w, u| {
                trace.push((w, u));
                Ok(())
            })
            .unwrap();
        assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
        assert!(actual.locally_free.is_empty());
        assert!(!actual.connective_used);
        let total = trace
            .iter()
            .fold((0usize, 0usize), |(w, u), (x, y)| (w + x, u + y));
        assert_eq!(total, (8 * count + 10, 4 * count + 16));
        for cut in 0..trace.len() {
            let mut observed = Vec::new();
            let result = lower_int_value_preparing(
                &source,
                &env,
                SourcePreparation::Checked,
                &mut |w, u| {
                    observed.push((w, u));
                    if observed.len() == cut + 1 {
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    } else {
                        Ok(())
                    }
                },
            );
            assert!(matches!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            ));
            assert_eq!(observed, trace[..=cut]);
        }
        for (work, units, pass) in [
            (total.0, total.1, true),
            (total.0 - 1, total.1, false),
            (total.0, total.1 - 1, false),
            (0, 0, false),
        ] {
            let mut used = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut used, work as u64, units, &mut cancel);
            let result = lower_int_value_preparing(
                &source,
                &env,
                SourcePreparation::Checked,
                &mut |w, u| {
                    budget
                        .charge(w, u)
                        .map_err(RholangAstLowerError::Preparation)
                },
            );
            assert_eq!(result.is_ok(), pass);
        }
        let original =
            lower_int_value_preparing(&source, &env, SourcePreparation::Original, &mut |_, _| {
                panic!("Original policy must not reserve")
            })
            .unwrap();
        assert_eq!(original.encode_to_vec(), expected.encode_to_vec());
        // Exercise the exposed CastInt driver path, not only the helper.
        let process = Proc::CastInt(Arc::new(source));
        let mut used = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut used, 1_000_000, 1_000_000, &mut cancel);
        let prepared =
            session::lower_public_body_with_budget(&process, BoundEnv::new(), &mut budget)
                .expect("public integer-category chain");
        assert_eq!(prepared.par.encode_to_vec(), expected.encode_to_vec());
    }
}

#[test]
fn paid_integer_category_deep_chain_and_partial_output_cleanup_use_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let source = integer_signs(8192);
            let env = BoundEnv::new();
            let mut calls = 0;
            let output = lower_int_value_preparing(
                &source,
                &env,
                SourcePreparation::Checked,
                &mut |_, _| {
                    calls += 1;
                    Ok(())
                },
            )
            .unwrap();
            // Inspect by borrowing the existing one-child spine; never clone it.
            let mut cursor = &output;
            for _ in 0..8192 {
                let Some(ExprInstance::ENegBody(ENeg { p: Some(child) })) =
                    cursor.exprs[0].expr_instance.as_ref()
                else {
                    panic!("negation spine")
                };
                cursor = child;
            }
            assert!(matches!(cursor.exprs[0].expr_instance, Some(ExprInstance::GInt(7))));
            drop(output);
            for stop in [1, 8192, calls - 3, calls] {
                let mut at = 0;
                let result = lower_int_value_preparing(
                    &source,
                    &env,
                    SourcePreparation::Checked,
                    &mut |_, _| {
                        at += 1;
                        if at == stop {
                            Err(RholangAstLowerError::Preparation(
                                DynamicReflectionError::Cancelled,
                            ))
                        } else {
                            Ok(())
                        }
                    },
                );
                assert!(result.is_err());
                assert_eq!(at, stop);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn receive_slot_moves_and_hole_copies_preserve_each_paid_prefix() {
    fn snapshot(slots: &[ReceiveSlot]) -> Vec<(Option<FreeVar<String>>, Option<String>)> {
        slots
            .iter()
            .map(|slot| match slot {
                ReceiveSlot::Moniker(binder) => (Some(binder.0.clone()), None),
                ReceiveSlot::Hole(name) => (None, Some(name.clone())),
            })
            .collect()
    }
    let binders = [Binder(FreeVar::fresh_named("first")), Binder(FreeVar::fresh_named("second"))];
    let names = ["same".to_owned(), "same".to_owned(), "λ".to_owned()];
    for copies in [false, true] {
        let run = |slots: &mut Vec<ReceiveSlot>, reserve: &mut StorageReservation<'_>, policy| {
            let mut build = SourceBuilder::new(policy, reserve);
            if copies {
                build.copy_receive_holes(slots, names.iter())
            } else {
                build.extend_receive_slots(slots, binders.iter().cloned().map(ReceiveSlot::Moniker))
            }
        };
        let mut expected = vec![(None, Some("existing".to_owned()))];
        if copies {
            expected.extend(names.iter().cloned().map(|name| (None, Some(name))));
        } else {
            expected.extend(binders.iter().map(|binder| (Some(binder.0.clone()), None)));
        }
        let mut actual = vec![ReceiveSlot::Hole("existing".into())];
        let mut trace = Vec::new();
        run(
            &mut actual,
            &mut |w, u| {
                trace.push((w, u));
                Ok(())
            },
            SourcePreparation::Checked,
        )
        .unwrap();
        assert_eq!(snapshot(&actual), expected);
        for cut in 0..trace.len() {
            let mut slots = vec![ReceiveSlot::Hole("existing".into())];
            let mut observed = Vec::new();
            let result = run(
                &mut slots,
                &mut |w, u| {
                    observed.push((w, u));
                    if observed.len() == cut + 1 {
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    } else {
                        Ok(())
                    }
                },
                SourcePreparation::Checked,
            );
            assert!(result.is_err());
            assert_eq!(observed, trace[..=cut]);
            let prefix = snapshot(&slots);
            assert_eq!(prefix, expected[..prefix.len()]);
        }
        let total = trace
            .iter()
            .fold((0usize, 0usize), |(w, u), (x, y)| (w + x, u + y));
        for (work, units, pass) in [
            (total.0, total.1, true),
            (total.0 - 1, total.1, false),
            (total.0, total.1 - 1, false),
        ] {
            let mut used = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut used, work as u64, units, &mut cancel);
            let mut slots = vec![ReceiveSlot::Hole("existing".into())];
            let result = run(
                &mut slots,
                &mut |w, u| {
                    budget
                        .charge(w, u)
                        .map_err(RholangAstLowerError::Preparation)
                },
                SourcePreparation::Checked,
            );
            assert_eq!(result.is_ok(), pass);
            if pass {
                assert_eq!(snapshot(&slots), expected);
            }
        }
        let mut slots = vec![ReceiveSlot::Hole("existing".into())];
        run(
            &mut slots,
            &mut |_, _| panic!("original transfer is unmetered"),
            SourcePreparation::Original,
        )
        .unwrap();
        assert_eq!(snapshot(&slots), expected);
    }
}
fn integer(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn receive_cases() -> Vec<(InputBind, Proc)> {
    let channel = Arc::new(Name::NQuoteNil);
    let quoted = Arc::new(Name::NQuote(Arc::new(integer(42))));
    let first = Arc::new(Name::NQuote(Arc::new(integer(1))));
    let rest = vec![Name::NQuote(Arc::new(integer(2)))];
    vec![
        (InputBind::InputBind(quoted.clone(), channel.clone()), integer(42)),
        (InputBind::InputBindPersistent(quoted, channel.clone()), integer(42)),
        (InputBind::InputBindQuoted(Arc::new(integer(42)), channel.clone()), integer(42)),
        (
            InputBind::InputBindQuotedPersistent(Arc::new(integer(42)), channel.clone()),
            integer(42),
        ),
        (InputBind::InputBindEmpty(channel.clone()), mk_proc_list(Vec::new())),
        (InputBind::InputBindEmptyPersistent(channel.clone()), mk_proc_list(Vec::new())),
        (
            InputBind::InputBindPolyadic(first.clone(), rest.clone(), channel.clone()),
            mk_proc_list(vec![integer(1), integer(2)]),
        ),
        (
            InputBind::InputBindPersistentPolyadic(first, rest, channel),
            mk_proc_list(vec![integer(1), integer(2)]),
        ),
    ]
}

#[test]
fn paid_receive_patterns_preserve_arity_and_every_refusal_prefix() {
    for (source, expected) in receive_cases() {
        let unchanged = source.clone();
        assert_eq!(bind_pattern_proc(&source), Some(expected.clone()));
        let mut charges = Vec::new();
        let actual = SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .bind_pattern(&source)
        .expect("checked receive pattern");
        assert_eq!(actual, Some(expected.clone()));
        assert_eq!(
            SourceBuilder::new(SourcePreparation::Original, &mut |_, _| {
                panic!("original adapter must not reserve")
            })
            .bind_pattern(&source)
            .expect("original pattern"),
            Some(expected)
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
            .bind_pattern(&source);
            assert_eq!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            );
            assert_eq!(accepted, charges[..cut]);
            assert_eq!(source, unchanged);
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
            let result = SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
                budget
                    .charge(w, u)
                    .map_err(RholangAstLowerError::Preparation)
            })
            .bind_pattern(&source);
            assert_eq!(result.is_ok(), succeeds);
        }
    }
}

#[test]
fn receive_binder_state_is_atomic_at_every_cut_and_counter_overflow() {
    let variable = FreeVar::fresh_named("capture".to_owned());
    let mut state = PatternState::default();
    let mut charges = Vec::new();
    assert_eq!(
        SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .bind_pattern_variable(&mut state, &variable)
        .expect("first binder"),
        0
    );
    assert_eq!(state.counter, 1);
    assert_eq!(state.binders[0].0, variable);
    for cut in 0..charges.len() {
        let mut state = PatternState::default();
        let mut calls = 0;
        let result = SourceBuilder::new(SourcePreparation::Checked, &mut |_, _| {
            if calls == cut {
                return Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled));
            }
            calls += 1;
            Ok(())
        })
        .bind_pattern_variable(&mut state, &variable);
        assert!(result.is_err());
        assert_eq!(state.counter, 0);
        assert!(state.binders.is_empty());
    }
    let mut state = PatternState { counter: i32::MAX, binders: Vec::new() };
    let result = SourceBuilder::new(SourcePreparation::Checked, &mut |_, _| Ok(()))
        .bind_pattern_variable(&mut state, &variable);
    assert_eq!(result, Err(RholangAstLowerError::PreparationSizeOverflow));
    assert_eq!(state.counter, i32::MAX);
    assert!(state.binders.is_empty());
}

#[test]
fn paid_receive_rows_borrow_original_occurrences_and_guard() {
    let channel = Arc::new(Name::NQuoteNil);
    let first = Arc::new(InputBind::InputBindEmpty(channel.clone()));
    let rest = vec![InputBind::InputBindEmptyPersistent(channel)];
    let condition = Arc::new(integer(42));
    let rows = [
        ForRow::ForRowSingleNoWhere(first.clone()),
        ForRow::ForRowSingleWhere(first.clone(), condition.clone()),
        ForRow::ForRowNoWhere(first.clone(), rest.clone()),
        ForRow::ForRowWhere(first, rest, condition),
    ];
    for row in &rows {
        let expected = decompose_for_row_borrowed(row).expect("borrowed oracle");
        let mut charges = Vec::new();
        let actual = SourceBuilder::new(SourcePreparation::Checked, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .for_row(row)
        .expect("paid row");
        assert_eq!(actual.0.len(), expected.0.len());
        for (left, right) in actual.0.iter().zip(&expected.0) {
            assert!(std::ptr::eq(*left, *right));
        }
        assert_eq!(actual.1, expected.1);
        match (actual.2, expected.2) {
            (Some(left), Some(right)) => assert!(std::ptr::eq(left, right)),
            (None, None) => {},
            _ => panic!("guard association changed"),
        }
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
            .for_row(row);
            assert!(result.is_err());
            assert_eq!(accepted, charges[..cut]);
        }
    }
}

// Expected core constructors are explicit, not obtained through either adapter.
fn sugar_cases() -> Vec<(Proc, Proc)> {
    let channel = Arc::new(Name::NQuote(Arc::new(integer(7))));
    let first = Arc::new(integer(1));
    let rest = vec![integer(2), integer(3)];
    let empty = Arc::new(mk_proc_list(Vec::new()));
    let list = Arc::new(mk_proc_list(vec![integer(1), integer(2), integer(3)]));
    let nil = Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let quoted = Arc::new(Name::NQuote(Arc::new(integer(1))));
    vec![
        (
            Proc::POutputEmpty(channel.clone()),
            Proc::POutput(channel.clone(), empty.clone()),
        ),
        (
            Proc::PPersistOutputEmpty(channel.clone()),
            Proc::PPersistOutput(channel.clone(), empty.clone()),
        ),
        (
            Proc::POutput2Plus(channel.clone(), first.clone(), rest.clone()),
            Proc::POutput(channel.clone(), list.clone()),
        ),
        (
            Proc::PPersistOutput2Plus(channel.clone(), first.clone(), rest.clone()),
            Proc::PPersistOutput(channel.clone(), list.clone()),
        ),
        (Proc::POutputNil(first.clone()), Proc::POutput(nil.clone(), first.clone())),
        (
            Proc::PPersistOutputNil(first.clone()),
            Proc::PPersistOutput(nil.clone(), first.clone()),
        ),
        (Proc::POutputNilEmpty, Proc::POutput(nil.clone(), empty.clone())),
        (Proc::PPersistOutputNilEmpty, Proc::PPersistOutput(nil.clone(), empty.clone())),
        (
            Proc::POutputNil2Plus(first.clone(), rest.clone()),
            Proc::POutput(nil.clone(), list.clone()),
        ),
        (
            Proc::PPersistOutputNil2Plus(first.clone(), rest.clone()),
            Proc::PPersistOutput(nil.clone(), list.clone()),
        ),
        (
            Proc::POutputQuoted(channel.clone(), first.clone()),
            Proc::POutput(channel.clone(), first.clone()),
        ),
        (
            Proc::POutputQuotedEmpty(channel.clone()),
            Proc::POutput(channel.clone(), empty.clone()),
        ),
        (
            Proc::POutputQuoted2Plus(channel.clone(), first.clone(), rest.clone()),
            Proc::POutput(channel.clone(), list.clone()),
        ),
        (
            Proc::POutputShortEmpty(first.clone()),
            Proc::POutput(quoted.clone(), empty.clone()),
        ),
        (
            Proc::PPersistOutputShortEmpty(first.clone()),
            Proc::PPersistOutput(quoted.clone(), empty.clone()),
        ),
        (
            Proc::POutputShort2Plus(first.clone(), first.clone(), rest.clone()),
            Proc::POutput(quoted.clone(), list.clone()),
        ),
        (
            Proc::PPersistOutputShort2Plus(first.clone(), first, rest),
            Proc::PPersistOutput(quoted, list),
        ),
    ]
}

#[test]
fn every_paid_send_sugar_preserves_explicit_core_and_public_bytes() {
    for (source, expected) in sugar_cases() {
        let expanded = desugar_surface_sugar_node_preparing(
            &source,
            SourcePreparation::Checked,
            &mut |_, _| Ok(()),
        )
        .expect("paid sugar")
        .expect("sugar head");
        assert_eq!(expanded, expected);
        assert_eq!(desugar_surface_sugar_node(&source), Some(expected.clone()));
        let expected = session::lower_public_body(&expected, BoundEnv::new()).expect("core source");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let actual = session::lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
            .expect("paid public sugar");
        assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
        assert_eq!(actual.guard_report, expected.guard_report);
        assert!(actual.folds.is_empty());
    }
}

#[test]
fn paid_sugar_stops_at_every_reservation_cut_with_exact_prefix_and_unchanged_source() {
    for (source, expected) in sugar_cases() {
        let unchanged = source.clone();
        let mut trace = Vec::new();
        let actual = desugar_surface_sugar_node_preparing(
            &source,
            SourcePreparation::Checked,
            &mut |w, u| {
                trace.push((w, u));
                Ok(())
            },
        )
        .expect("trace");
        assert_eq!(actual, Some(expected));
        for cut in 0..trace.len() {
            let mut accepted = Vec::new();
            let result = desugar_surface_sugar_node_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |w, u| {
                    if accepted.len() == cut {
                        return Err(RholangAstLowerError::Preparation(
                            DynamicReflectionError::Cancelled,
                        ));
                    }
                    accepted.push((w, u));
                    Ok(())
                },
            );
            assert_eq!(
                result,
                Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
            );
            assert_eq!(accepted, trace[..cut]);
            assert_eq!(source, unchanged);
        }
        let work = trace.iter().map(|(w, _)| *w as u64).sum::<u64>();
        let units = trace.iter().map(|(_, u)| *u).sum::<usize>();
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
            let result = desugar_surface_sugar_node_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |w, u| {
                    budget
                        .charge(w, u)
                        .map_err(RholangAstLowerError::Preparation)
                },
            );
            assert_eq!(result.is_ok(), succeeds);
            if succeeds {
                assert_eq!(budget.work_used(), work);
                assert_eq!(budget.remaining_bytes(), 0);
            }
        }
    }
}

#[test]
fn paid_name_pattern_preserves_variable_identity_and_monadic_shape() {
    let variable = OrdVar(Var::Free(FreeVar::fresh_named("same")));
    for (source, expected) in [
        (Name::NVar(variable.clone()), Proc::PVar(variable)),
        (Name::NQuote(Arc::new(integer(9))), integer(9)),
        (Name::NQuoteShort(Arc::new(integer(9))), integer(9)),
        (Name::NQuoteNil, Proc::PZero),
    ] {
        let mut reserve = |_, _| Ok(());
        let mut build = SourceBuilder::new(SourcePreparation::Checked, &mut reserve);
        assert_eq!(build.name_pattern(&source).expect("paid name pattern"), expected);
    }
    assert_eq!(polyadic_count(usize::MAX), Err(RholangAstLowerError::PreparationSizeOverflow));
    assert_eq!(polyadic_count(0).expect("single entry"), 1);
}

#[test]
fn paid_sugar_deep_and_wide_copy_and_refusal_cleanup_fit_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut deep = Proc::PZero;
            for _ in 0..2048 {
                deep = Proc::PParInfix(Arc::new(deep), Arc::new(Proc::PZero));
            }
            let channel = Arc::new(Name::NQuoteNil);
            for source in [
                Proc::POutput2Plus(channel.clone(), Arc::new(deep), vec![Proc::PZero]),
                Proc::PPersistOutput2Plus(channel, Arc::new(Proc::PZero), vec![Proc::PZero; 2048]),
            ] {
                let mut calls = 0usize;
                let result = desugar_surface_sugar_node_preparing(
                    &source,
                    SourcePreparation::Checked,
                    &mut |_, _| {
                        calls += 1;
                        Ok(())
                    },
                )
                .expect("deep/wide paid sugar");
                drop(result);
                for cut in [0, calls / 2, calls - 1] {
                    let mut seen = 0;
                    let result = desugar_surface_sugar_node_preparing(
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
                    );
                    assert!(matches!(
                        result,
                        Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                    ));
                    assert_eq!(seen, cut);
                }
            }
        })
        .expect("small-stack thread")
        .join()
        .expect("small-stack sugar and normal cleanup");
}

#[test]
fn original_query_sugar_never_consults_checked_reservation() {
    let name = Arc::new(Name::NQuoteNil);
    let source = Proc::PForUser(
        vec![ForRow::ForRowSingleNoWhere(Arc::new(InputBind::InputBindQuery(
            name.clone(),
            name,
            vec![integer(1)],
        )))],
        Arc::new(Proc::PZero),
    );
    let expanded =
        desugar_surface_sugar_node_preparing(&source, SourcePreparation::Original, &mut |_, _| {
            panic!("Original must not charge a checked reservation")
        })
        .expect("unchanged original query expansion")
        .expect("query sugar");
    assert!(matches!(expanded, Proc::PNew(_)));
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
    assert!(matches!(
        session::lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget),
        Err(RholangAstLowerError::SourceProfile(_))
    ));
}

#[test]
fn copied_sugar_payloads_preserve_foreign_node_pointer_identity() {
    let node = Arc::new(
        FltNode::new("guest".into(), "Term".into(), "body".into(), vec![], 0)
            .expect("valid FLT template"),
    );
    let source = Proc::POutput2Plus(
        Arc::new(Name::NQuoteNil),
        Arc::new(Proc::PFlt(node.clone())),
        vec![Proc::PFlt(node.clone())],
    );
    let expanded =
        desugar_surface_sugar_node_preparing(&source, SourcePreparation::Checked, &mut |_, _| {
            Ok(())
        })
        .expect("polyadic FLT copy")
        .expect("sugar");
    let Proc::POutput(_, payload) = &expanded else {
        panic!("core send")
    };
    let Proc::CastList(list) = payload.as_ref() else {
        panic!("arity list")
    };
    let List::ListLit(items) = list.as_ref() else {
        panic!("list entries")
    };
    assert_eq!(items.len(), 2);
    for item in items {
        let Proc::PFlt(copied) = item else {
            panic!("FLT occurrence")
        };
        assert!(Arc::ptr_eq(copied, &node));
    }
    let source = Proc::POutputQuoted(
        Arc::new(Name::NQuote(Arc::new(Proc::PFlt(node.clone())))),
        Arc::new(Proc::PZero),
    );
    let expanded =
        desugar_surface_sugar_node_preparing(&source, SourcePreparation::Checked, &mut |_, _| {
            Ok(())
        })
        .expect("quoted FLT copy")
        .expect("sugar");
    let Proc::POutput(channel, _) = &expanded else {
        panic!("core send")
    };
    let Name::NQuote(child) = channel.as_ref() else {
        panic!("quoted channel")
    };
    let Proc::PFlt(copied) = child.as_ref() else {
        panic!("FLT occurrence")
    };
    assert!(Arc::ptr_eq(copied, &node));
}

#[test]
fn paid_sugar_map_copy_fits_small_stack() {
    let mut entries = mettail_runtime::HashMapLit::new();
    entries.insert(integer(1), integer(2));
    let source = Proc::POutputNil2Plus(
        Arc::new(Proc::CastMap(Arc::new(Map::MapLit(entries)))),
        vec![Proc::PZero],
    );
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let expanded = desugar_surface_sugar_node_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |_, _| Ok(()),
            )
            .expect("paid map-key copy")
            .expect("sugar");
            let Proc::POutput(_, payload) = &expanded else {
                panic!("core send")
            };
            let Proc::CastList(list) = payload.as_ref() else {
                panic!("arity list")
            };
            let List::ListLit(items) = list.as_ref() else {
                panic!("list entries")
            };
            let Proc::CastMap(map) = &items[0] else {
                panic!("copied map")
            };
            let Map::MapLit(entries) = map.as_ref() else {
                panic!("map entries")
            };
            assert_eq!(entries.len(), 1);
        })
        .expect("small-stack map thread")
        .join()
        .expect("paid map-key copy and cleanup");
}

#[test]
fn paid_sugar_parallel_collection_copy_fits_small_stack() {
    let source = Proc::POutputNil2Plus(
        Arc::new(Proc::PPar(mettail_runtime::HashBag::from_iter([integer(1), integer(2)]))),
        vec![Proc::PZero],
    );
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let expanded = desugar_surface_sugar_node_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |_, _| Ok(()),
            )
            .expect("paid parallel-key copy")
            .expect("sugar");
            let Proc::POutput(_, payload) = &expanded else {
                panic!("core send")
            };
            let Proc::CastList(list) = payload.as_ref() else {
                panic!("arity list")
            };
            let List::ListLit(items) = list.as_ref() else {
                panic!("list entries")
            };
            let Proc::PPar(entries) = &items[0] else {
                panic!("copied parallel collection")
            };
            assert_eq!(entries.len(), 2);
        })
        .expect("small-stack parallel thread")
        .join()
        .expect("paid parallel-key copy and cleanup");
}

fn parallel_map_sugar() -> Proc {
    let mut map = mettail_runtime::HashMapLit::new();
    map.insert(integer(1), integer(2));
    map.insert(integer(3), integer(4));
    Proc::POutputNil2Plus(
        Arc::new(Proc::PPar(mettail_runtime::HashBag::from_iter([
            Proc::CastMap(Arc::new(Map::MapLit(map))),
            integer(5),
        ]))),
        vec![Proc::PZero],
    )
}

#[test]
fn paid_sugar_parallel_map_key_inspection_and_cleanup_fit_small_stack() {
    let source = parallel_map_sugar();
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let mut calls = 0;
            let result = desugar_surface_sugar_node_preparing(
                &source,
                SourcePreparation::Checked,
                &mut |_, _| {
                    calls += 1;
                    Ok(())
                },
            )
            .expect("paid parallel multi-entry map key");
            assert!(result.is_some());
            drop(result);
            for cut in [0, calls / 2, calls - 1] {
                let mut seen = 0;
                let result = desugar_surface_sugar_node_preparing(
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
                );
                assert_eq!(seen, cut);
                assert!(matches!(
                    result,
                    Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
                ));
            }
        })
        .expect("small-stack map-key thread")
        .join()
        .expect("map-key inspection and normal cleanup");
}

#[test]
fn paid_collection_sugar_preserves_receipt_prefix_at_every_cut() {
    let source = parallel_map_sugar();
    let unchanged = source.clone();
    let expected = desugar_surface_sugar_node(&source);
    let mut trace = Vec::new();
    let actual =
        desugar_surface_sugar_node_preparing(&source, SourcePreparation::Checked, &mut |w, u| {
            trace.push((w, u));
            Ok(())
        })
        .expect("complete native collection path");
    assert_eq!(actual, expected);
    for cut in 0..trace.len() {
        let mut prefix = Vec::new();
        let result = desugar_surface_sugar_node_preparing(
            &source,
            SourcePreparation::Checked,
            &mut |w, u| {
                if prefix.len() == cut {
                    return Err(RholangAstLowerError::Preparation(
                        DynamicReflectionError::Cancelled,
                    ));
                }
                prefix.push((w, u));
                Ok(())
            },
        );
        assert_eq!(
            result,
            Err(RholangAstLowerError::Preparation(DynamicReflectionError::Cancelled))
        );
        assert_eq!(prefix, trace[..cut]);
        assert_eq!(source, unchanged);
    }
}

#[test]
fn public_sugar_cancellation_covers_head_retention_and_terminal_inspection() {
    let source = Proc::POutputNil2Plus(Arc::new(integer(1)), vec![integer(2)]);
    let mut calls = 0;
    let (expected, paid_work, paid_units) = {
        let mut work = 0;
        let mut cancel = || {
            calls += 1;
            false
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let result = session::lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
            .expect("complete public sugar path");
        (
            result.par.encode_to_vec(),
            budget.work_used(),
            1_000_000 - budget.remaining_bytes(),
        )
    };
    for cut in 0..calls {
        let mut seen = 0;
        let mut work = 0;
        let mut cancel = || {
            let stop = seen == cut;
            seen += 1;
            stop
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let result = session::lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
        assert!(result.is_err(), "cancellation cut {cut}");
        assert!(budget.work_used() <= paid_work);
        assert_eq!(seen, cut + 1, "no source action after refused reservation");
    }
    for (work_limit, units, succeeds) in [
        (paid_work, paid_units, true),
        (paid_work - 1, paid_units, false),
        (paid_work, paid_units - 1, false),
    ] {
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, units, &mut cancel);
        let result = session::lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
        assert_eq!(result.is_ok(), succeeds);
        if let Ok(actual) = result {
            assert_eq!(actual.par.encode_to_vec(), expected);
            assert_eq!(budget.work_used(), paid_work);
            assert_eq!(budget.remaining_bytes(), 0);
        }
    }
}
