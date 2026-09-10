use super::*;
use prost::Message;

fn public_env() -> BoundEnv {
    BoundEnv::empty_with_admission(
        Arc::new(EmptyFltResolver),
        LoweringOptions::NO_DISCHARGE,
        SourceAdmissionMode::Public,
    )
}

fn named(name: &str) -> FreeVar<String> {
    FreeVar::fresh_named(name.to_owned())
}

fn variable(free: &FreeVar<String>) -> OrdVar {
    OrdVar(Var::Free(free.clone()))
}

fn same_context(actual: &BoundEnv, expected: &BoundEnv) {
    assert_eq!(actual.options, expected.options);
    assert_eq!(actual.admission, expected.admission);
    assert_eq!(actual.free_vars_are_patterns, expected.free_vars_are_patterns);
    assert!(Arc::ptr_eq(&actual.resolver, &expected.resolver));
}

#[test]
fn public_unresolved_name_and_process_reject_in_the_actual_worker() {
    let env = public_env();
    let var = variable(&named("unresolved"));
    assert_eq!(
        drive(Seed::Name(&Name::NVar(var.clone())), &env),
        Err(RholangAstLowerError::UnresolvedNameReference)
    );
    assert_eq!(
        lower_proc_in_env(&Proc::PVar(var), &env),
        Err(RholangAstLowerError::UnresolvedProcessReference)
    );
    let mut unnamed = named("discarded");
    unnamed.pretty_name = None;
    assert_eq!(
        lower_proc_var(&variable(&unnamed), &env),
        Err(RholangAstLowerError::UnresolvedProcessReference)
    );
    assert_eq!(
        lower_proc_var(&variable(&unnamed), &BoundEnv::new()),
        Err(RholangAstLowerError::FreeVarWithoutName)
    );
}

#[test]
fn harness_markers_remain_explicit_and_literal_marker_text_is_data() {
    let env = BoundEnv::new();
    let var = variable(&named("x"));
    let marker = new_gstring_par("mtl:x".into(), vec![], false);
    assert_eq!(lower_name_var(&var, &env).expect("harness name"), marker);
    assert_eq!(
        lower_proc_var(&var, &env).expect("harness process"),
        send_par(new_gstring_par("mtl#out".into(), vec![], false), vec![marker.clone()])
    );
    let literal = Proc::CastStr(Arc::new(Str::StringLit("mtl:x".into())));
    assert_eq!(lower_proc_in_env(&literal, &public_env()).expect("literal data"), marker);
}

#[test]
fn identity_precedes_hole_names_and_missing_identity_uses_enclosing_holes() {
    let mut env = public_env();
    let moniker = named("x");
    let unrelated = named("x");
    env.binders.insert(moniker.clone(), 9);
    env.hole_binders.insert("x".into(), 2);
    env.scope_width = 10;
    for (var, index) in [(variable(&moniker), 9), (variable(&unrelated), 2)] {
        let expected = new_boundvar_par(index, vec![], false);
        assert_eq!(lower_name_var(&var, &env).expect("name"), expected);
        assert_eq!(lower_proc_var(&var, &env).expect("process"), expected);
    }
    let mut unnamed = named("same identity");
    env.binders.insert(unnamed.clone(), 1);
    unnamed.pretty_name = None;
    assert_eq!(
        lower_proc_var(&variable(&unnamed), &env).expect("identity needs no pretty name"),
        new_boundvar_par(1, vec![], false)
    );
}

#[test]
fn formula_wildcards_do_not_override_bound_references_or_admission_policy() {
    for admission in [SourceAdmissionMode::Public, SourceAdmissionMode::Harness] {
        let mut env = public_env();
        env.admission = admission;
        let bound = named("bound");
        env.binders.insert(bound.clone(), 3);
        env.scope_width = 4;
        let pattern = env.in_pattern_position();
        assert_eq!(pattern.admission, admission);
        assert!(Arc::ptr_eq(&pattern.resolver, &env.resolver));
        assert_eq!(pattern.options, env.options);
        for var in [variable(&named("free")), {
            let mut unnamed = named("unnamed");
            unnamed.pretty_name = None;
            variable(&unnamed)
        }] {
            assert_eq!(
                lower_name_var(&var, &pattern).expect("wildcard"),
                new_wildcard_par(vec![], true)
            );
            assert_eq!(
                lower_proc_var(&var, &pattern).expect("wildcard"),
                new_wildcard_par(vec![], true)
            );
        }
        assert_eq!(
            lower_proc_var(&variable(&bound), &pattern).expect("bound"),
            new_boundvar_par(3, vec![], false)
        );
    }
}

#[test]
fn ordered_slots_preserve_last_insertion_mixed_numbering_and_outer_shifts() {
    let outer = named("outer");
    let inner = named("inner");
    let root = extend_env(&public_env(), &[Binder(outer.clone())]).expect("outer scope");
    let slots = [
        ReceiveSlot::Hole("same".into()),
        ReceiveSlot::Moniker(Binder(inner.clone())),
        ReceiveSlot::Hole("same".into()),
    ];
    let extended = root.extend_slots(&slots).expect("mixed scope");
    assert_eq!(root.scope_width, 1);
    assert_eq!(extended.scope_width, 4);
    same_context(&extended, &root);
    assert_eq!(extended.binders.get(&outer), Some(&3));
    assert_eq!(extended.binders.get(&inner), Some(&1));
    assert_eq!(extended.hole_binders.get("same"), Some(&0));
    assert_eq!(root.binders.get(&outer), Some(&0), "parent/siblings remain unchanged");
    let shadowed = extend_env(&extended, &[Binder(outer.clone()), Binder(outer.clone())])
        .expect("last duplicate moniker wins");
    assert_eq!(shadowed.binders.get(&outer), Some(&0));
    assert_eq!(shadowed.binders.get(&inner), Some(&3));
    assert_eq!(shadowed.hole_binders.get("same"), Some(&2));
    assert_eq!(shadowed.scope_width, 6);
    same_context(&shadowed, &root);
    let reset = shadowed.without_lexical_bindings();
    assert!(reset.binders.is_empty() && reset.hole_binders.is_empty());
    assert_eq!(reset.scope_width, 0);
    same_context(&reset, &shadowed);
}

#[test]
fn declared_width_counts_unused_and_shadowed_slots_without_an_i32_scope_cap() {
    let var = named("same identity");
    let first = extend_env(&public_env(), &[Binder(var.clone()), Binder(var.clone())])
        .expect("repeated identity slots");
    assert_eq!(first.binders.len(), 1);
    assert_eq!(first.scope_width, 2);
    let second = first
        .extend_slots(&[ReceiveSlot::Hole("x".into()), ReceiveSlot::Hole("x".into())])
        .expect("repeated hole slots");
    assert_eq!(second.binders.len() + second.hole_binders.len(), 2);
    assert_eq!(second.scope_width, 4);
    assert_eq!(second.binders.get(&var), Some(&2));
    let mut wide = public_env();
    wide.scope_width = i32::MAX as usize;
    let extended = extend_env(&wide, &[Binder(named("unused"))]).expect("total scope is not i32");
    assert_eq!(extended.scope_width, i32::MAX as usize + 1);
    let mut maximal = public_env();
    maximal.scope_width = usize::MAX;
    assert!(matches!(
        extend_env(&maximal, &[Binder(named("unused"))]),
        Err(RholangAstLowerError::ScopeIndexOverflow)
    ));
    assert!(matches!(
        maximal.extend_slots(&[ReceiveSlot::Hole("unused".into())]),
        Err(RholangAstLowerError::ScopeIndexOverflow)
    ));
    assert_eq!(
        extend_env(&maximal, &[])
            .expect("zero extension")
            .scope_width,
        usize::MAX
    );
    assert_eq!(maximal.scope_width, usize::MAX);
}

#[test]
fn scope_and_arena_overflow_are_checked_without_large_allocations() {
    assert_eq!(checked_shift(usize::MAX, 0), Ok(usize::MAX));
    assert_eq!(checked_shift(usize::MAX, 1), Err(RholangAstLowerError::ScopeIndexOverflow));
    assert_eq!(next_environment_index(0), Ok(1));
    assert_eq!(next_environment_index(u32::MAX as usize - 1), Ok(u32::MAX));
    assert_eq!(
        next_environment_index(u32::MAX as usize),
        Err(RholangAstLowerError::ScopeArenaOverflow)
    );
    assert_eq!(
        next_environment_index(usize::MAX),
        Err(RholangAstLowerError::ScopeArenaOverflow)
    );
    for hole in [false, true] {
        let mut env = public_env();
        let outer = named("outer");
        match hole {
            false => {
                env.binders.insert(outer.clone(), usize::MAX);
            },
            true => {
                env.hole_binders.insert("outer".into(), usize::MAX);
            },
        }
        assert!(matches!(
            extend_env(&env, &[Binder(named("new"))]),
            Err(RholangAstLowerError::ScopeIndexOverflow)
        ));
        assert!(matches!(
            env.extend_slots(&[ReceiveSlot::Hole("new".into())]),
            Err(RholangAstLowerError::ScopeIndexOverflow)
        ));
        assert_eq!(
            env.binders
                .get(&outer)
                .copied()
                .or_else(|| env.flt_hole_level("outer")),
            Some(usize::MAX)
        );
    }
}

#[test]
fn target_index_check_precedes_node_bitvector_construction() {
    assert_eq!(
        checked_bound_reference(usize::MAX, i32::MAX as usize)
            .expect("representable")
            .emitted_index(),
        i32::MAX
    );
    // Never construct the enormous valid endpoint bitvector in this test.
    for index in [i32::MAX as usize + 1, u32::MAX as usize, usize::MAX] {
        assert_eq!(
            lower_bound_index(usize::MAX, index),
            Err(RholangAstLowerError::BoundIndexOutOfRange { index })
        );
        for hole in [false, true] {
            let mut env = public_env();
            let var = named("x");
            if hole {
                env.hole_binders.insert("x".into(), index);
            } else {
                env.binders.insert(var.clone(), index);
            }
            for pattern in [false, true] {
                env.free_vars_are_patterns = pattern;
                assert_eq!(
                    lower_proc_var(&variable(&var), &env),
                    Err(RholangAstLowerError::BoundIndexOutOfRange { index })
                );
            }
        }
    }
}

#[test]
fn bound_metadata_and_protobuf_match_independent_small_index_examples() {
    // Par.exprs=5, Expr.e_var_body=19, EVar.v=1, Var.bound_var=1
    // (sint32 zigzag); Par.locallyFree=9. Oneof zero is present on wire.
    for index in [0usize, 1, 7, 8, 15, 16, 31] {
        // The pinned node uses one byte per membership flag, not packed bits.
        let mut expected_bits = vec![0; index + 1];
        expected_bits[index] = 1;
        let mut expected = vec![0x2a, 7, 0x9a, 1, 4, 0x0a, 2, 0x08, (index * 2) as u8];
        expected.extend([0x4a, expected_bits.len() as u8]);
        expected.extend_from_slice(&expected_bits);
        let value = lower_bound_index(index + 1, index).expect("small bound");
        assert_eq!(value.locally_free, expected_bits);
        assert!(!value.connective_used);
        assert_eq!(value.encode_to_vec(), expected);
    }
}

#[test]
fn public_fresh_pattern_environment_does_not_reenable_harness() {
    let root = public_env();
    let arena: Arena<Arc<Proc>> = Arena::new();
    let zero = Proc::PZero;
    let mut driver = Drive {
        arena: &arena,
        envs: EnvArena::new(&root),
        stacks: Stacks::new(Job::Proc(&zero, ROOT_ENV)),
        pattern_states: Vec::new(),
        empty_env: None,
    };
    let id = driver.empty_env().expect("fresh environment");
    same_context(driver.env(id), &root);
    assert_eq!(driver.empty_env().expect("cached").0, id.0);
    assert_eq!(
        lower_proc_var(&variable(&named("unresolved")), driver.env(id)),
        Err(RholangAstLowerError::UnresolvedProcessReference)
    );
}

#[test]
fn unopened_moniker_coordinates_reject_in_both_roles_and_modes() {
    let free = named("not opened");
    let closed = mettail_runtime::Scope::new(Binder(free.clone()), variable(&free));
    let var = closed.unsafe_body();
    assert!(matches!(var.0, Var::Bound(_)));
    for mut env in [public_env(), BoundEnv::new()] {
        for pattern in [false, true] {
            env.free_vars_are_patterns = pattern;
            assert_eq!(
                lower_name_var(&var, &env),
                Err(RholangAstLowerError::UnsupportedName("unopened bound name variable"))
            );
            assert_eq!(
                lower_proc_var(&var, &env),
                Err(RholangAstLowerError::UnsupportedProc("unopened bound process variable"))
            );
        }
    }
}

#[test]
fn actual_new_worker_opens_multiple_binders_and_preserves_quote_drop() {
    for count in [2, 3] {
        for used in 0..count {
            let binders: Vec<_> = (0..count).map(|_| Binder(named("same spelling"))).collect();
            let body = Proc::PVar(variable(&binders[used].0));
            let quoted = Name::NQuote(Arc::new(body.clone()));
            let dropped = Proc::PDrop(Arc::new(quoted));
            for body in [body, dropped] {
                let source =
                    Proc::PNew(mettail_runtime::Scope::new(binders.clone(), Arc::new(body)));
                let actual = lower_proc_in_env(&source, &public_env()).expect("opened source new");
                let expected = new_new_par(
                    count as i32,
                    new_boundvar_par((count - 1 - used) as i32, vec![], false),
                    vec![],
                    BTreeMap::new(),
                    vec![],
                    vec![],
                    false,
                );
                assert_eq!(actual, expected);
                assert_eq!(actual.encode_to_vec(), expected.encode_to_vec());
                assert!(actual.locally_free.is_empty());
            }
        }
    }
}
