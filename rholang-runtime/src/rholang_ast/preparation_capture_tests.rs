use super::*;

fn public_env() -> BoundEnv {
    BoundEnv::empty_with_admission(
        Arc::new(EmptyFltResolver),
        LoweringOptions::NO_DISCHARGE,
        SourceAdmissionMode::Public,
    )
}

fn named(name: &str) -> Binder<String> {
    Binder(FreeVar::fresh_named(name.to_owned()))
}

#[test]
fn source_alias_shadowing_preserves_distinct_moniker_identities_and_parent() {
    let outer = named("text");
    let inner = named("text");
    let parent = public_env()
        .extend_source_binders(&[outer.clone()])
        .expect("source binder");
    let child = parent
        .extend_source_binders(&[inner.clone()])
        .expect("shadowing source binder");
    assert_eq!(parent.construction_hole_level("text"), Some(0));
    assert_eq!(child.construction_hole_level("text"), Some(0));
    assert_eq!(child.binders.get(&outer.0), Some(&1));
    assert_eq!(child.binders.get(&inner.0), Some(&0));
    assert!(child.hole_binders.is_empty());
    assert_eq!(child.scope_width, 2);
}

#[test]
fn mixed_receive_slots_share_reversed_indices_and_last_alias_wins() {
    let parent = public_env()
        .extend_source_binders(&[named("outer")])
        .expect("outer scope");
    let first = named("text");
    let last = named("text");
    let child = parent
        .extend_slots(&[
            ReceiveSlot::Moniker(first.clone()),
            ReceiveSlot::Hole("captured".into()),
            ReceiveSlot::Moniker(last.clone()),
        ])
        .expect("one joint receive scope");
    assert_eq!(child.construction_hole_level("outer"), Some(3));
    assert_eq!(child.construction_hole_level("text"), Some(0));
    assert_eq!(child.construction_hole_level("captured"), Some(1));
    assert_eq!(child.flt_hole_level("captured"), Some(1));
    assert_eq!(child.binders.get(&first.0), Some(&2));
    assert_eq!(child.binders.get(&last.0), Some(&0));
    assert_eq!(parent.construction_hole_level("outer"), Some(0));
}

#[test]
fn internal_binders_shift_but_do_not_shadow_source_construction_aliases() {
    for name in ["__mtl_flt_ret", "__mtl_flt_result"] {
        let source = named(name);
        let internal = named(name);
        let parent = public_env()
            .extend_source_binders(&[source.clone()])
            .expect("source spelling is unrestricted");
        let child = extend_env(&parent, &[internal.clone()]).expect("internal scope");
        assert_eq!(child.construction_hole_level(name), Some(1));
        assert_eq!(child.binders.get(&source.0), Some(&1));
        assert_eq!(child.binders.get(&internal.0), Some(&0));
        assert_eq!(parent.construction_hole_level(name), Some(0));
    }
}

#[test]
fn source_aliases_do_not_authorize_same_spelling_unrelated_process_or_selector() {
    let source = named("language");
    let env = public_env()
        .extend_source_binders(&[source.clone()])
        .expect("source scope");
    let unrelated = OrdVar(Var::Free(named("language").0));
    assert_eq!(env.construction_hole_level("language"), Some(0));
    assert_eq!(
        lower_proc_var(&unrelated, &env),
        Err(RholangAstLowerError::UnresolvedProcessReference)
    );
    assert_eq!(
        lower_name_var(&unrelated, &env),
        Err(RholangAstLowerError::UnresolvedNameReference)
    );
    assert_eq!(
        lower_proc_var(&OrdVar(Var::Free(source.0)), &env).expect("actual identity"),
        scope::lower_bound_index(1, 0).expect("bound reference")
    );
}

#[test]
fn capture_alias_reset_and_overflow_leave_original_environment_unchanged() {
    let mut parent = public_env()
        .extend_source_binders(&[named("text")])
        .expect("source scope");
    let reset = parent.without_lexical_bindings();
    assert!(reset.construction_holes.is_empty());
    assert_eq!(reset.scope_width, 0);
    parent.construction_holes.insert("text".into(), usize::MAX);
    for result in [
        extend_env(&parent, &[named("internal")]),
        parent.extend_source_binders(&[named("source")]),
        parent.extend_slots(&[ReceiveSlot::Hole("capture".into())]),
    ] {
        assert!(matches!(result, Err(RholangAstLowerError::ScopeIndexOverflow)));
    }
    assert_eq!(parent.construction_hole_level("text"), Some(usize::MAX));
    assert_eq!(parent.scope_width, 1);
}

fn construction_requests(par: &Par) -> Vec<crate::language_install::FltConstructCall> {
    let channel = LANGUAGE_FLT_CONSTRUCT_BAND
        .channel(0, crate::language_install::LANGUAGE_FLT_CONSTRUCT_ABI_V1);
    let mut pending = vec![par];
    let mut requests = Vec::new();
    while let Some(par) = pending.pop() {
        for new in &par.news {
            pending.extend(new.p.as_ref());
        }
        for receive in &par.receives {
            pending.extend(receive.body.as_ref());
        }
        for send in &par.sends {
            if send.chan.as_ref() == Some(&channel) {
                assert_eq!(send.data.len(), 1, "one ABI request datum");
                requests.push(
                    crate::language_install::decode_flt_construct_call(&send.data[0])
                        .expect("actual emitted construction request"),
                );
            }
        }
    }
    requests
}

#[test]
fn whole_body_staging_resolves_source_new_receive_join_and_internal_name_collisions() {
    for (source, levels) in [
        (
            r#"new language, text in { @"out"!(language:Computation`use(${text:Text})`) }"#,
            vec![("text", 1)],
        ),
        (
            r#"new language, text in { new text in { @"out"!(language:Computation`use(${text:Text})`) } }"#,
            vec![("text", 1)],
        ),
        (
            r#"new language in { for(@text <- @"in") { @"out"!(language:Computation`use(${text:Text})`) } }"#,
            vec![("text", 1)],
        ),
        (
            r#"new language in { for(@left <- @"left" & @right <- @"right") { @"out"!(language:Computation`use(${left:Text},${right:Text})`) } }"#,
            vec![("left", 2), ("right", 1)],
        ),
        (
            r#"new language, __mtl_flt_ret in { @"out"!(language:Computation`use(${__mtl_flt_ret:Text})`) }"#,
            vec![("__mtl_flt_ret", 1)],
        ),
    ] {
        let proc = Proc::parse_via_wpda(source).expect("ordinary source with qualified FLT");
        let output = session::lower_public_body(&proc, public_env())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        let requests = construction_requests(&output.par);
        assert_eq!(requests.len(), 1, "{source}: exactly one staged guest construction");
        assert_eq!(requests[0].fills.len(), levels.len());
        for (name, level) in levels {
            assert_eq!(
                requests[0].fills.get(name),
                Some(&scope::lower_bound_index(100, level).expect("small expected index")),
                "{source}: {name} preserves its lexical binding and locally-free metadata"
            );
        }
    }
}

#[test]
fn whole_body_missing_construction_capture_fails_closed() {
    let proc = Proc::parse_via_wpda(
        r#"new language in { @"out"!(language:Computation`use(${missing:Text})`) }"#,
    )
    .expect("well-formed but unresolved capture");
    assert!(matches!(
        session::lower_public_body(&proc, public_env()),
        Err(RholangAstLowerError::FltReflect(message))
            if message.contains("missing") && message.contains("no enclosing lexical binding")
    ));
}

#[test]
fn where_predicates_retain_join_captures_without_a_construction_trampoline() {
    let predicate = "language:Computation`use(${left:Text},${right:Text})`";
    for guard in [
        predicate.to_owned(),
        format!("{predicate} and true"),
        format!("false or {predicate}"),
        format!("not {predicate}"),
        format!("true implies {predicate}"),
    ] {
        let source = format!(
            "new language in {{ for(@left <- @\"left\" & @right <- @\"right\" where {guard}) {{ Nil }} }}"
        );
        let proc = Proc::parse_via_wpda(&source).expect("qualified predicate in ordinary source");
        let output = session::lower_public_body(&proc, public_env())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            construction_requests(&output.par).is_empty(),
            "guard must not run a construction send"
        );
        let receive = &output.par.news[0]
            .p
            .as_ref()
            .expect("source new body")
            .receives[0];
        assert_eq!(receive.bind_count, 2);
        let mut pending = vec![receive
            .condition
            .as_ref()
            .expect("retained where condition")];
        let mut descriptors = Vec::new();
        while let Some(value) = pending.pop() {
            if crate::guard_predicate::is_descriptor(value) {
                let fields = crate::language_install::exact_list(value).expect("descriptor list");
                descriptors.push(
                    crate::language_install::decode_flt_construct_call(&fields[1])
                        .expect("structural predicate template"),
                );
                continue;
            }
            match crate::language_install::exact_expr(value) {
                Some(ExprInstance::EAndBody(EAnd { p1, p2 }))
                | Some(ExprInstance::EOrBody(EOr { p1, p2 })) => {
                    pending.push(p1.as_ref().expect("left guard operand"));
                    pending.push(p2.as_ref().expect("right guard operand"));
                },
                Some(ExprInstance::ENotBody(ENot { p })) => {
                    pending.push(p.as_ref().expect("negated guard operand"));
                },
                Some(ExprInstance::GBool(_)) => {},
                _ => panic!("unexpected guard encoding"),
            }
        }
        assert_eq!(descriptors.len(), 1);
        let descriptor = &descriptors[0];
        assert_eq!(
            descriptor.handle,
            scope::lower_bound_index(3, 2).expect("outer lexical selector")
        );
        assert_eq!(descriptor.fills.len(), 2);
        assert_eq!(
            descriptor.fills.get("left"),
            Some(&scope::lower_bound_index(3, 1).expect("first joined capture"))
        );
        assert_eq!(
            descriptor.fills.get("right"),
            Some(&scope::lower_bound_index(3, 0).expect("last joined capture"))
        );
        assert_eq!(descriptor.category, "Computation");
    }
}
