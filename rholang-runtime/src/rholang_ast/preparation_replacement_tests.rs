use super::*;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};

fn integer(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn is_seven(proc: &Proc) -> bool {
    matches!(proc, Proc::CastInt(value) if matches!(value.as_ref(), Int::NumLit(7)))
}

fn flt(text: &str) -> Arc<FltNode> {
    Arc::new(
        FltNode::new("guest".into(), "Term".into(), text.into(), vec![], 0)
            .expect("valid template"),
    )
}

fn is_pointer(proc: &Proc, target: &Arc<FltNode>) -> bool {
    match proc {
        Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
            Arc::ptr_eq(node, target)
        },
        _ => false,
    }
}

fn checked(
    source: &Proc,
    replacement: &Proc,
    replaced: &mut bool,
    reserve: &mut StorageReservation<'_>,
) -> Result<Proc, RholangAstLowerError> {
    replace_first_body_site_preparing(
        source,
        replacement,
        replaced,
        is_seven,
        SourcePreparation::Checked,
        reserve,
    )
}

fn cases() -> Vec<Proc> {
    let leaf = Arc::new(integer(7));
    let quote = Arc::new(Name::NParen(Arc::new(Name::NQuote(leaf.clone()))));
    let mut map = mettail_runtime::HashMapLit::new();
    map.insert(integer(7), integer(7));
    map.insert(integer(2), integer(7));
    let mut bag = mettail_runtime::HashBag::new();
    bag.insert_n(integer(7), 3);
    bag.insert(integer(2));
    let mut result = vec![
        Proc::PZero,
        integer(7),
        Proc::Not(leaf.clone()),
        Proc::POutput(quote.clone(), leaf.clone()),
        Proc::PPersistOutput(quote.clone(), leaf.clone()),
        Proc::POutputShort(leaf.clone(), leaf.clone()),
        Proc::PPersistOutputShort(leaf.clone(), leaf.clone()),
        Proc::PDrop(quote.clone()),
        Proc::PDrop(Arc::new(Name::NQuoteShort(leaf.clone()))),
        Proc::POutput2Plus(quote.clone(), leaf.clone(), vec![integer(7), integer(3)]),
        Proc::PPersistOutput2Plus(quote.clone(), leaf.clone(), vec![integer(7)]),
        Proc::POutputQuoted(quote.clone(), leaf.clone()),
        Proc::POutputNil2Plus(leaf.clone(), vec![integer(7)]),
        Proc::CastList(Arc::new(List::ListLit(vec![integer(7), integer(7), integer(2)]))),
        Proc::CastMap(Arc::new(Map::MapLit(map))),
        Proc::PPar(bag),
        Proc::MethodCall(leaf.clone(), "nth".into(), vec![integer(7), integer(2)]),
        Proc::PNew(mettail_runtime::Scope::new(Vec::<Binder<String>>::new(), leaf.clone())),
        Proc::PNewUris(
            Vec::new(),
            mettail_runtime::Scope::new(Vec::<Binder<String>>::new(), leaf.clone()),
        ),
        Proc::PForUser(
            vec![ForRow::ForRowSingleWhere(
                Arc::new(InputBind::InputBind(quote.clone(), quote)),
                leaf.clone(),
            )],
            leaf.clone(),
        ),
    ];
    let binary: [fn(Arc<Proc>, Arc<Proc>) -> Proc; 10] = [
        Proc::Eq,
        Proc::Ne,
        Proc::Lt,
        Proc::Gt,
        Proc::LtEq,
        Proc::GtEq,
        Proc::And,
        Proc::Or,
        Proc::Implies,
        Proc::PParInfix,
    ];
    result.extend(
        binary
            .into_iter()
            .map(|make| make(leaf.clone(), leaf.clone())),
    );
    result
}

#[test]
fn replacement_matches_original_order_at_every_cut_and_exact_allowance() {
    let replacement = integer(99);
    for source in cases() {
        // These are regular collections. Irregular native bags are snapshotted
        // separately below because their Clone normalizes stored zero counts.
        let unchanged = source.clone();
        let mut expected_replaced = false;
        let expected =
            replace_first_body_site(&source, &replacement, &mut expected_replaced, is_seven);
        let mut original_replaced = false;
        let original = replace_first_body_site_preparing(
            &source,
            &replacement,
            &mut original_replaced,
            is_seven,
            SourcePreparation::Original,
            &mut |_, _| panic!("Original must not invoke checked reservation"),
        )
        .expect("original adapter");
        assert_eq!(original, expected);
        assert_eq!(original_replaced, expected_replaced);
        let mut charges = Vec::new();
        let mut replaced = false;
        let actual = checked(&source, &replacement, &mut replaced, &mut |w, u| {
            charges.push((w, u));
            Ok(())
        })
        .expect("complete checked replacement");
        assert_eq!(actual, expected);
        assert_eq!(replaced, expected_replaced);
        if matches!(&source, Proc::PNew(..) | Proc::PNewUris(..) | Proc::PForUser(..)) {
            assert!(!replaced, "nested binder/pattern sites belong to their own body scope");
            assert_eq!(actual, unchanged);
        }
        assert!(!charges.is_empty());
        for cut in 0..charges.len() {
            let mut accepted = Vec::new();
            let result = checked(&source, &replacement, &mut false, &mut |w, u| {
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
            assert_eq!(source, unchanged);
        }
        let work = charges.iter().map(|(w, _)| *w as u64).sum::<u64>();
        let units = charges.iter().map(|(_, u)| *u).sum::<usize>();
        assert!(work > 0 && units > 0);
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
            let result = checked(&source, &replacement, &mut false, &mut |w, u| {
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

#[test]
fn replacement_postorder_channel_priority_and_shared_flt_positions_are_exact() {
    let node = flt("shared");
    let source = Proc::POutput2Plus(
        Arc::new(Name::NQuote(Arc::new(Proc::PFltFence(node.clone())))),
        Arc::new(Proc::PFlt(node.clone())),
        vec![Proc::PFltBrace(node.clone())],
    );
    let mut replaced = false;
    let actual = replace_first_body_site_preparing(
        &source,
        &integer(99),
        &mut replaced,
        |candidate| is_pointer(candidate, &node),
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
    )
    .expect("first original FLT occurrence");
    assert!(replaced);
    let Proc::POutput(channel, payload) = &actual else {
        panic!("core send")
    };
    let Name::NQuote(channel) = channel.as_ref() else {
        panic!("quoted channel")
    };
    assert_eq!(channel.as_ref(), &integer(99));
    let Proc::CastList(list) = payload.as_ref() else {
        panic!("polyadic payload")
    };
    let List::ListLit(items) = list.as_ref() else {
        panic!("list payload")
    };
    assert_eq!(items.len(), 2);
    assert!(matches!(&items[0], Proc::PFlt(found) if Arc::ptr_eq(found, &node)));
    assert!(matches!(&items[1], Proc::PFltBrace(found) if Arc::ptr_eq(found, &node)));

    let source = Proc::Eq(Arc::new(integer(7)), Arc::new(integer(8)));
    let actual = replace_first_body_site_preparing(
        &source,
        &integer(99),
        &mut false,
        |candidate| is_seven(candidate) || matches!(candidate, Proc::Eq(..)),
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
    )
    .expect("postorder");
    assert_eq!(actual, Proc::Eq(Arc::new(integer(99)), Arc::new(integer(8))));
}

#[test]
fn map_collision_retains_first_key_object_and_position_but_last_value() {
    let first = flt("first");
    let original_second = flt("second");
    let replacement_second = flt("second");
    assert!(!Arc::ptr_eq(&original_second, &replacement_second));
    let mut map = mettail_runtime::HashMapLit::new();
    map.insert(Proc::PFlt(first.clone()), integer(10));
    map.insert(integer(3), integer(30));
    map.insert(Proc::PFlt(original_second.clone()), integer(20));
    let source = Proc::CastMap(Arc::new(Map::MapLit(map)));
    let replacement = Proc::PFlt(replacement_second.clone());
    let mut charges = Vec::new();
    let actual = replace_first_body_site_preparing(
        &source,
        &replacement,
        &mut false,
        |candidate| is_pointer(candidate, &first),
        SourcePreparation::Checked,
        &mut |w, u| {
            charges.push((w, u));
            Ok(())
        },
    )
    .expect("collision rebuild");
    let Proc::CastMap(actual) = &actual else {
        panic!("map")
    };
    let Map::MapLit(entries) = actual.as_ref() else {
        panic!("map literal")
    };
    assert_eq!(entries.len(), 2);
    let roster = entries.iter().collect::<Vec<_>>();
    assert!(matches!(roster[0].0, Proc::PFlt(found) if Arc::ptr_eq(found, &replacement_second)));
    assert_eq!(roster[0].1, &integer(20));
    assert_eq!(roster[1], (&integer(3), &integer(30)));
    for cut in 0..charges.len() {
        let mut accepted = Vec::new();
        let result = replace_first_body_site_preparing(
            &source,
            &replacement,
            &mut false,
            |candidate| is_pointer(candidate, &first),
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
        assert!(result.is_err());
        assert_eq!(accepted, charges[..cut]);
    }
    let Proc::CastMap(original) = &source else {
        unreachable!()
    };
    let Map::MapLit(entries) = original.as_ref() else {
        unreachable!()
    };
    assert_eq!(entries.len(), 3);
    assert!(matches!(entries.iter().next().unwrap().0,
        Proc::PFlt(found) if Arc::ptr_eq(found, &first)));
}

#[test]
fn irregular_parallel_multiplicity_uses_native_occurrences_not_clone_metadata() {
    let source = Proc::PPar(
        mettail_runtime::HashBag::new().rebuild_binding_entries([(integer(1), 0), (integer(7), 3)]),
    );
    let Proc::PPar(parts) = &source else {
        unreachable!()
    };
    let before = (
        parts.len(),
        parts
            .iter()
            .map(|(key, n)| (key as *const Proc, n))
            .collect::<Vec<_>>(),
    );
    let actual = checked(&source, &integer(99), &mut false, &mut |_, _| Ok(()))
        .expect("native occurrence rebuild");
    let Proc::PPar(rebuilt) = &actual else {
        panic!("parallel bag")
    };
    assert_eq!(rebuilt.len(), 3);
    assert_eq!(rebuilt.count(&integer(7)), 2);
    assert_eq!(rebuilt.count(&integer(99)), 1);
    assert_eq!(rebuilt.count(&integer(1)), 0);
    assert_eq!(
        (
            parts.len(),
            parts
                .iter()
                .map(|(key, n)| (key as *const Proc, n))
                .collect::<Vec<_>>()
        ),
        before
    );
}

#[test]
fn already_replaced_copies_original_sugar_and_preserves_flt_identity() {
    let node = flt("unchanged");
    let source = Proc::POutputNil2Plus(Arc::new(Proc::PFlt(node.clone())), vec![integer(7)]);
    let actual = replace_first_body_site_preparing(
        &source,
        &integer(99),
        &mut true,
        |_| panic!("no selector after replacement"),
        SourcePreparation::Checked,
        &mut |_, _| Ok(()),
    )
    .expect("copy without further desugaring");
    let Proc::POutputNil2Plus(first, rest) = &actual else {
        panic!("original sugar")
    };
    assert!(matches!(first.as_ref(), Proc::PFlt(found) if Arc::ptr_eq(found, &node)));
    assert_eq!(rest.as_slice(), &[integer(7)]);
}

#[test]
fn deep_replacement_and_refusal_cleanup_fit_128k_native_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = integer(7);
            for _ in 0..2048 {
                source = Proc::Not(Arc::new(source));
            }
            let mut calls = 0usize;
            let actual = checked(&source, &integer(99), &mut false, &mut |_, _| {
                calls += 1;
                Ok(())
            })
            .expect("deep checked replacement");
            let mut leaf = &actual;
            for _ in 0..2048 {
                let Proc::Not(inner) = leaf else {
                    panic!("preserved unary spine")
                };
                leaf = inner.as_ref();
            }
            assert_eq!(leaf, &integer(99));
            drop(actual);
            for cut in [0, calls / 2, calls - 1] {
                let mut accepted = 0usize;
                let result = checked(&source, &integer(99), &mut false, &mut |_, _| {
                    if accepted == cut {
                        return Err(RholangAstLowerError::Preparation(
                            DynamicReflectionError::Cancelled,
                        ));
                    }
                    accepted += 1;
                    Ok(())
                });
                assert!(result.is_err());
                assert_eq!(accepted, cut);
            }
            drop(source);
        })
        .expect("small-stack thread")
        .join()
        .expect("replacement and cleanup");
}
