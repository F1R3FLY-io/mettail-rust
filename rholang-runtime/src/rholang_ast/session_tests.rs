use super::*;
use prost::Message;

fn integer(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn big_integer(value: num_bigint::BigInt) -> Proc {
    Proc::CastBigInt(Arc::new(BigInt::NumLit(mettail_runtime::CanonicalBigInt::from(value))))
}

fn fold(operand: Proc) -> Proc {
    Proc::IntBinProc(Arc::new(operand), Arc::new(Int::NumLit(8)))
}

fn variable(name: &str) -> OrdVar {
    OrdVar(Var::Free(FreeVar::fresh_named(name.to_owned())))
}

fn unresolved_flt() -> Proc {
    Proc::PFlt(Arc::new(
        FltNode::new("guest".into(), "Term".into(), "body".into(), vec![], 0)
            .expect("well-formed structural template"),
    ))
}

fn assert_idle() {
    assert!(!ACTIVE.with(Cell::get));
    assert!(ALTERNATIVE_FOLDS.with(|state| state.borrow().is_none()));
    assert!(HELD_FOLD_SITES.with(|sites| sites.borrow().is_empty()));
    assert_eq!(take_guard_discharge_report(), GuardDischargeReport::default());
}

fn seed_outputs(count: usize) {
    HELD_FOLD_SITES.with(|sites| {
        *sites.borrow_mut() = (0..count)
            .map(|_| FoldSpec {
                kind: FoldKind::Int,
                width: 8,
                site_index: 0,
                fingerprint: "test-only-unused-descriptor".into(),
            })
            .collect();
    });
    GUARD_DISCHARGE_REPORT.with(|report| report.borrow_mut().residual = 3);
}

#[test]
fn bounded_source_refusal_precedes_folds_scopes_and_ddl_preparation() {
    use mettail_languages::rholang::source_profile::SourceRole;
    use mettail_languages::rholang::{
        source_constructor, DdlTheoryExpr, SourceConstructor, SourceProfileError,
    };
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let sources = [
        (fold(integer(5)), 0),
        (
            Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(
                Vec::new(),
                Arc::new(fold(integer(5))),
            )),
            1,
        ),
        (
            Proc::DdlTheory(
                "example".to_owned(),
                Vec::new(),
                Arc::new(DdlTheoryExpr::DdlTheoryDataImplicit(Arc::new(fold(integer(5))))),
            ),
            2,
        ),
    ];
    for (source, ordinal) in sources {
        seed_outputs(1);
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
        let error = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
        assert!(matches!(error, Err(RholangAstLowerError::SourceProfile(
            SourceProfileError::Unsupported {
                constructor: SourceConstructor::Proc(source_constructor::Proc::IntBinProc),
                role: SourceRole::Term,
                ordinal: actual,
            }
        )) if actual == ordinal));
        assert!(budget.work_used() > 0);
        assert_idle();
    }
}

#[test]
fn source_profile_admits_lookahead_and_checks_subject_and_bound() {
    use mettail_languages::rholang::source_profile::{RholangSourceProfile, SourceRole};
    use mettail_languages::rholang::{source_constructor, SourceConstructor, SourceProfileError};

    let admitted = [
        Proc::PLookaheadAll(Arc::new(Proc::POutputNil(Arc::new(integer(1))))),
        Proc::PLookahead(Arc::new(Proc::POutputNil(Arc::new(integer(1)))), Arc::new(integer(3))),
        Proc::PLookahead(
            Arc::new(Proc::POutputNil(Arc::new(integer(1)))),
            Arc::new(big_integer(num_bigint::BigInt::from(u64::MAX))),
        ),
    ];
    for source in admitted {
        source
            .try_check_source_profile(SourceRole::Term, &RholangSourceProfile, &mut |_, _| {
                Ok::<(), ()>(())
            })
            .expect("lookahead fields are admitted under the term role");
    }

    let rejected = [
        Proc::PLookaheadAll(Arc::new(fold(integer(1)))),
        Proc::PLookahead(Arc::new(Proc::PZero), Arc::new(fold(integer(3)))),
    ];
    for source in rejected {
        assert!(matches!(
            source.try_check_source_profile(
                SourceRole::Term,
                &RholangSourceProfile,
                &mut |_, _| Ok::<(), ()>(())
            ),
            Err(SourceProfileError::Unsupported {
                constructor: SourceConstructor::Proc(source_constructor::Proc::IntBinProc),
                role: SourceRole::Term,
                ..
            })
        ));
    }
}

#[test]
fn lookahead_bound_admits_exact_unsigned_range_without_narrowing() {
    assert_eq!(lookahead_bound(&integer(0)).unwrap(), 0);
    assert_eq!(lookahead_bound(&integer(i64::MAX)).unwrap(), i64::MAX as u64);
    for value in [i64::MAX as u64 + 1, u64::MAX] {
        assert_eq!(lookahead_bound(&big_integer(num_bigint::BigInt::from(value))).unwrap(), value,);
    }
    assert!(lookahead_bound(&integer(-1)).is_err());
    assert!(lookahead_bound(&big_integer(num_bigint::BigInt::from(-1))).is_err());
    assert!(lookahead_bound(&big_integer(num_bigint::BigInt::from(u64::MAX) + 1)).is_err());
}

#[test]
fn full_unsigned_lookahead_bounds_use_existing_source_parser_and_exact_wire() {
    for value in [i64::MAX as u64 + 1, u64::MAX] {
        let source = format!(r#"@"r"!(Nil)[{value}]"#);
        let parsed = Proc::parse_via_wpda(&source).expect("upper-half bound parses as Rholang");
        let actual = crate::rholang_ast::lower_rholang_proc(&parsed)
            .expect("upper-half bound lowers without narrowing");
        let expected = crate::lookahead::spec_n_request_v2(
            Par::default(),
            value,
            Vec::new(),
            crate::lookahead::spec_channel_par("r"),
        );
        assert_eq!(actual, expected);
    }
}

#[test]
fn source_gate_and_body_driver_share_both_existing_budget_dimensions() {
    use mettail_languages::rholang::source_profile::{RholangSourceProfile, SourceRole};
    use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
    let source = Proc::PZero;
    let mut gate_work = 0;
    let mut gate_bytes = 0;
    source
        .try_check_source_profile(SourceRole::Term, &RholangSourceProfile, &mut |work, bytes| {
            gate_work += work;
            gate_bytes += bytes;
            Ok::<(), ()>(())
        })
        .expect("measure the exact source gate only");

    for work_is_exact in [true, false] {
        let mut work = 17;
        let mut cancel = || false;
        let limit = if work_is_exact {
            17 + gate_work as u64
        } else {
            100_000
        };
        let bytes = if work_is_exact { 1_000_000 } else { gate_bytes };
        let mut budget = ReflectedCodecBudget::new(&mut work, limit, bytes, &mut cancel);
        let result = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
        let expected = if work_is_exact {
            DynamicReflectionError::WorkLimit
        } else {
            DynamicReflectionError::PayloadByteLimit
        };
        assert!(
            matches!(result, Err(RholangAstLowerError::Preparation(actual)) if actual == expected)
        );
        assert_eq!(budget.work_used(), 17 + gate_work as u64);
        assert_eq!(budget.remaining_bytes(), bytes - gate_bytes);
        assert_idle();
    }
}

#[test]
fn checked_public_source_accepts_concat_and_preserves_eplusplus() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let source = Proc::Concat(
        Arc::new(Proc::CastStr(Arc::new(Str::StringLit("rho:lib:".into())))),
        Arc::new(Proc::CastStr(Arc::new(Str::StringLit("owner".into())))),
    );
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    let prepared = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
        .expect("the public source profile admits ++ in a term");
    assert!(matches!(
        prepared
            .par
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref()),
        Some(ExprInstance::EPlusPlusBody(_))
    ));
    assert!(work > 0);
}

#[test]
fn projected_host_proc_uses_the_public_meter_and_preserves_lowered_bytes() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let source = Proc::PCostSignedTerm(
        Arc::new(Proc::PZero),
        Arc::new(CostSig::CostSigHash(Arc::new(Proc::PZero))),
    );
    let reference = lower_public_body(&source, BoundEnv::new())
        .expect("public source has a canonical host lowering");
    assert!(reference.folds.is_empty());
    assert_eq!(reference.guard_report.disagreements, 0);

    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    let par = super::super::lower_rholang_host_proc_with_budget(&source, &mut budget)
        .expect("selected host value lowers through the public metered path");
    assert_eq!(par.encode_to_vec(), reference.par.encode_to_vec());
    assert!(budget.work_used() > 0);
    assert_idle();
    let arbitrary = Proc::PParInfix(Arc::new(integer(7)), Arc::new(Proc::PZero));
    assert!(matches!(
        super::super::lower_rholang_host_proc_with_budget(&arbitrary, &mut budget),
        Err(RholangAstLowerError::CostPlanUnavailable(_))
    ));

    let mut refused_work = 0;
    let mut cancel = || false;
    let mut zero_budget = ReflectedCodecBudget::new(&mut refused_work, 0, 0, &mut cancel);
    assert!(super::super::lower_rholang_host_proc_with_budget(&source, &mut zero_budget).is_err());
    assert_idle();
}

fn checked_query_bytes(source: &str) -> Vec<u8> {
    use mettail_rholang_codegen::ReflectedCodecBudget;
    use models::rust::rholang::sorter::par_sort_matcher::ParSortMatcher;
    use models::rust::rholang::sorter::sortable::Sortable;

    let proc = Proc::parse_via_wpda(source).expect("query source parses through MeTTaIL");
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 16_000_000, &mut cancel);
    let result = lower_public_body_with_budget(&proc, BoundEnv::new(), &mut budget).unwrap_or_else(
        |error| panic!("checked query preparation failed for {source:?}: {error:?}"),
    );
    assert!(result.folds.is_empty());
    assert!(budget.work_used() > 0);
    assert_idle();
    ParSortMatcher::sort_match(&result.par).term.encode_to_vec()
}

#[test]
fn checked_query_rows_match_explicit_row_local_scopes_and_all_pattern_forms() {
    for (source, expanded) in [
        (
            r#"for(x <- @"svc"!?(1, 2)) { @"OUT"!(*x) }"#,
            r#"new reply in { @"svc"!(*reply, 1, 2) | for(x <- reply) { @"OUT"!(*x) } }"#,
        ),
        (
            r#"for(@x <- @"svc"!?(1)) { @"OUT"!(x) }"#,
            r#"new reply in { @"svc"!(*reply, 1) | for(@x <- reply) { @"OUT"!(x) } }"#,
        ),
        (
            r#"for(<- @"svc"!?()) { @"OUT"!(1) }"#,
            r#"new reply in { @"svc"!(*reply) | for(<- reply) { @"OUT"!(1) } }"#,
        ),
        (
            r#"for(x <- @"first"!?(1); y <- @"second"!?(*x)) { @"OUT"!(*y) }"#,
            r#"new firstReply in { @"first"!(*firstReply, 1) | for(x <- firstReply) {
                new secondReply in { @"second"!(*secondReply, *x) | for(y <- secondReply) { @"OUT"!(*y) } }
            } }"#,
        ),
        (
            r#"for(x <- @"first"; y <- @"second"!?(*x)) { @"OUT"!(*y) }"#,
            r#"for(x <- @"first") { new reply in { @"second"!(*reply, *x) | for(y <- reply) { @"OUT"!(*y) } } }"#,
        ),
        (
            r#"for(x <- @"first"!?(1) & y <- @"second"!?(2)) { @"OUT"!(*x, *y) }"#,
            r#"new firstReply, secondReply in { @"first"!(*firstReply, 1) | @"second"!(*secondReply, 2)
                | for(x <- firstReply & y <- secondReply) { @"OUT"!(*x, *y) } }"#,
        ),
        (
            r#"for(@x <- @"svc"!?(1) where x == 1) { @"OUT"!(x) }"#,
            r#"new reply in { @"svc"!(*reply, 1) | for(@x <- reply where x == 1) { @"OUT"!(x) } }"#,
        ),
        (
            r#"new __r0 in { for(x <- @"svc"!?(*__r0)) { @"OUT"!(*__r0, *x) } }"#,
            r#"new __r0 in { new reply in { @"svc"!(*reply, *__r0)
                | for(x <- reply) { @"OUT"!(*__r0, *x) } } }"#,
        ),
    ] {
        assert_eq!(checked_query_bytes(source), checked_query_bytes(expanded), "{source}");
        assert_eq!(
            checked_query_bytes(source),
            checked_query_bytes(source),
            "fresh identities stay private"
        );
    }
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(16))]

    #[test]
    fn checked_query_request_payload_preserves_every_argument(
        arguments in proptest::collection::vec(proptest::prelude::any::<i16>(), 0..12),
    ) {
        let arguments = arguments.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ");
        let source = format!("for(x <- @\"svc\"!?({arguments})) {{ @\"OUT\"!(*x) }}");
        let payload = if arguments.is_empty() { "*reply".into() } else { format!("*reply, {arguments}") };
        let expanded = format!("new reply in {{ @\"svc\"!({payload}) | for(x <- reply) {{ @\"OUT\"!(*x) }} }}");
        proptest::prop_assert_eq!(checked_query_bytes(&source), checked_query_bytes(&expanded));
    }
}

#[test]
fn checked_query_preparation_refuses_insufficient_budget_and_leaves_the_session_idle() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let proc = Proc::parse_via_wpda(r#"for(x <- @"svc"!?(1, 2, 3)) { @"OUT"!(*x) }"#)
        .expect("query source parses");
    for (work_limit, byte_limit, cancelled) in
        [(0, 1_000_000, false), (1_000_000, 0, false), (1_000_000, 1_000_000, true)]
    {
        let mut work = 0;
        let mut cancel = || cancelled;
        let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, byte_limit, &mut cancel);
        assert!(lower_public_body_with_budget(&proc, BoundEnv::new(), &mut budget).is_err());
        assert_idle();
    }
    checked_query_bytes(r#"for(x <- @"svc"!?(1)) { @"OUT"!(*x) }"#);
}

#[test]
fn source_admission_cancellation_retains_the_typed_failure_and_cleans_session() {
    use mettail_languages::rholang::SourceProfileError;
    use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
    seed_outputs(1);
    let mut work = 17;
    let mut cancel = || true;
    let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
    let result = lower_public_body_with_budget(&Proc::PZero, BoundEnv::new(), &mut budget);
    assert!(matches!(
        result,
        Err(RholangAstLowerError::SourceProfile(SourceProfileError::Reservation(
            mettail_runtime::BindingFailure::Reservation(DynamicReflectionError::Cancelled)
        )))
    ));
    assert_eq!(budget.work_used(), 17);
    assert_eq!(budget.remaining_bytes(), 1_000_000);
    assert_idle();
}

#[test]
fn admitted_public_source_preserves_existing_bytes_and_owned_outputs() {
    use mettail_rholang_codegen::ReflectedCodecBudget;
    let sources = [Proc::PZero, integer(42), Proc::POutputNil(Arc::new(integer(7)))];
    for source in sources {
        let reference =
            lower_public_body(&source, BoundEnv::new()).expect("existing public lowering");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancel);
        let actual = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
            .expect("admitted source uses the same body driver");
        assert_eq!(actual.par.encode_to_vec(), reference.par.encode_to_vec());
        assert!(actual.folds.is_empty());
        assert_eq!(actual.guard_report, reference.guard_report);
        assert_idle();
    }
}

#[test]
fn checked_scalar_parallel_composition_preserves_bytes_at_exact_resource_limits() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let sources = [
        Proc::PParInfix(
            Arc::new(Proc::CastStr(Arc::new(Str::StringLit("left".into())))),
            Arc::new(Proc::CastBool(Arc::new(Bool::BoolLit(true)))),
        ),
        Proc::PParInfix(
            Arc::new(integer(-42)),
            Arc::new(Proc::CastBytes(Arc::new(Bytes::BytesLit(vec![0, 0xff])))),
        ),
        Proc::PParInfix(
            Arc::new(Proc::CastFloat(Arc::new(Float::FloatLit(
                mettail_runtime::CanonicalFloat64::from(1.5),
            )))),
            Arc::new(Proc::PZero),
        ),
    ];
    for source in sources {
        let reference = lower_public_body(&source, BoundEnv::new()).expect("existing lowering");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 10_000_000, &mut cancel);
        let actual = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
            .expect("checked construction with admitted append copies");
        assert_eq!(actual.par.encode_to_vec(), reference.par.encode_to_vec());
        let exact_work = budget.work_used();
        let exact_units = 10_000_000 - budget.remaining_bytes();
        assert!(exact_work > 0 && exact_units > 0);

        for (work_limit, unit_limit, should_succeed) in [
            (0, 0, false),
            (exact_work - 1, exact_units, false),
            (exact_work, exact_units - 1, false),
            (exact_work, exact_units, true),
        ] {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, work_limit, unit_limit, &mut cancel);
            let result = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
            if should_succeed {
                assert_eq!(
                    result.expect("exact budget").par.encode_to_vec(),
                    reference.par.encode_to_vec()
                );
            } else {
                assert!(result.is_err(), "one-under budget must not publish an output");
            }
            assert_idle();
        }
    }
}

#[test]
fn checked_nested_list_construction_preserves_public_bytes_and_exact_limits() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    let source = Proc::CastList(Arc::new(List::ListLit(vec![
        integer(7),
        Proc::CastList(Arc::new(List::ListLit(vec![
            Proc::CastStr(Arc::new(Str::StringLit("nested".into()))),
            Proc::CastBool(Arc::new(Bool::BoolLit(false))),
        ]))),
    ])));
    let reference = lower_public_body(&source, BoundEnv::new()).expect("existing lowering");
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 10_000_000, &mut cancel);
    let actual = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
        .expect("checked nested list");
    assert_eq!(actual.par.encode_to_vec(), reference.par.encode_to_vec());
    let exact_work = budget.work_used();
    let exact_units = 10_000_000 - budget.remaining_bytes();
    assert!(exact_work > 0 && exact_units > 0);
    for (work_limit, unit_limit, accepted) in [
        (0, 0, false),
        (exact_work - 1, exact_units, false),
        (exact_work, exact_units - 1, false),
        (exact_work, exact_units, true),
    ] {
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, work_limit, unit_limit, &mut cancel);
        let result = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
        if accepted {
            assert_eq!(
                result.expect("exact list budget").par.encode_to_vec(),
                reference.par.encode_to_vec()
            );
        } else {
            assert!(result.is_err(), "insufficient list budget must not publish");
        }
        assert_idle();
    }
}

#[test]
fn checked_expression_families_preserve_public_bytes_and_exact_limits() {
    use mettail_rholang_codegen::ReflectedCodecBudget;

    fn integer(value: i64) -> Proc {
        Proc::CastInt(Arc::new(Int::NumLit(value)))
    }
    fn string(value: &str) -> Proc {
        Proc::CastStr(Arc::new(Str::StringLit(value.into())))
    }
    let sources = [
        Proc::NegProc(Arc::new(integer(7))),
        Proc::Not(Arc::new(Proc::CastBool(Arc::new(Bool::BoolLit(true))))),
        Proc::Add(Arc::new(integer(3)), Arc::new(integer(7))),
        Proc::Add(Arc::new(string("a")), Arc::new(string("b"))),
        Proc::Eq(Arc::new(integer(3)), Arc::new(integer(7))),
        Proc::Lt(Arc::new(integer(3)), Arc::new(integer(7))),
        Proc::Implies(
            Arc::new(Proc::CastBool(Arc::new(Bool::BoolLit(true)))),
            Arc::new(Proc::CastBool(Arc::new(Bool::BoolLit(false)))),
        ),
        Proc::Matches(Arc::new(integer(3)), Arc::new(integer(7))),
        Proc::MethodCall(Arc::new(string("abc")), "length".into(), vec![]),
        Proc::MethodCall(Arc::new(string("abc")), "substring".into(), vec![integer(1), integer(2)]),
    ];
    for source in sources {
        let reference = lower_public_body(&source, BoundEnv::new()).expect("existing lowering");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 10_000_000, &mut cancel);
        let actual = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget)
            .expect("checked expression");
        assert_eq!(actual.par.encode_to_vec(), reference.par.encode_to_vec());
        let exact_work = budget.work_used();
        let exact_units = 10_000_000 - budget.remaining_bytes();
        assert!(exact_work > 0 && exact_units > 0);
        for (work_limit, unit_limit, accepted) in [
            (0, 0, false),
            (exact_work - 1, exact_units, false),
            (exact_work, exact_units - 1, false),
            (exact_work, exact_units, true),
        ] {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, work_limit, unit_limit, &mut cancel);
            let result = lower_public_body_with_budget(&source, BoundEnv::new(), &mut budget);
            if accepted {
                assert_eq!(
                    result.expect("exact expression budget").par.encode_to_vec(),
                    reference.par.encode_to_vec()
                );
            } else {
                assert!(result.is_err(), "insufficient expression budget must not publish");
            }
            assert_idle();
        }
    }
}

#[test]
fn public_whole_body_lifts_folds_and_returns_the_exact_direct_output() {
    let proc = fold(integer(5));
    let reference = with_owned_outputs(|owner| owner.drive(Seed::Body(&proc), &BoundEnv::new()))
        .expect("existing driver");
    let actual = lower_public_body(&proc, BoundEnv::new()).expect("public whole body");
    assert_eq!(actual.par.encode_to_vec(), reference.par.encode_to_vec());
    assert_eq!(actual.folds.len(), 1);
    assert_eq!(actual.folds[0].kind, FoldKind::Int);
    assert_eq!(actual.folds[0].width, 8);
    assert_eq!(actual.folds[0].site_index, 0);
    assert_eq!(actual.folds[0].channel(), reference.folds[0].channel());
    assert!(!actual.par.news.is_empty(), "whole-body fold trampoline");
    assert_idle();
}

#[test]
fn public_mode_is_explicit_and_does_not_inherit_harness_markers() {
    let proc = Proc::PVar(variable("unresolved"));
    assert!(lower_rholang_proc(&proc).is_ok(), "explicit compatibility behavior");
    for options in [LoweringOptions::PRODUCTION, LoweringOptions::NO_DISCHARGE] {
        assert!(matches!(
            lower_public_body(&proc, BoundEnv::with_options(options)),
            Err(RholangAstLowerError::UnresolvedProcessReference)
        ));
        let name = Proc::PDrop(Arc::new(Name::NVar(variable("unresolved-name"))));
        assert!(matches!(
            lower_public_body(&name, BoundEnv::with_options(options)),
            Err(RholangAstLowerError::UnresolvedNameReference)
        ));
        assert_idle();
    }
}

#[test]
fn existing_scope_identity_and_formula_pattern_context_are_retained() {
    let free = FreeVar::fresh_named("bound".to_owned());
    let context = extend_env(&BoundEnv::new(), &[Binder(free.clone())]).expect("scope");
    let proc = Proc::PVar(OrdVar(Var::Free(free)));
    let expected = lower_proc_in_env(&proc, &context).expect("existing context");
    let actual = lower_public_body(&proc, context).expect("public bound reference");
    assert_eq!(actual.par.encode_to_vec(), expected.encode_to_vec());
    let pattern = BoundEnv::new().in_pattern_position();
    let wildcard =
        lower_public_body(&Proc::PVar(variable("pattern")), pattern).expect("pattern wildcard");
    assert_eq!(wildcard.par, new_wildcard_par(vec![], true));
    assert_idle();
}

#[test]
fn public_whole_body_retains_hole_scope_and_moniker_identity_precedence() {
    let moniker = FreeVar::fresh_named("x".to_owned());
    let unrelated = FreeVar::fresh_named("x".to_owned());
    let mut context = BoundEnv::new();
    context.binders.insert(moniker.clone(), 9);
    context.hole_binders.insert("x".into(), 2);
    context.scope_width = 10;
    for (free, index) in [(moniker, 9), (unrelated, 2)] {
        let proc = Proc::PVar(OrdVar(Var::Free(free)));
        let actual = lower_public_body(&proc, context.clone()).expect("retained scope");
        assert_eq!(actual.par, new_boundvar_par(index, vec![], false));
        assert_idle();
    }
}

#[test]
fn error_after_recording_a_fold_cleans_both_outputs_before_the_next_request() {
    seed_outputs(2);
    let error = lower_public_body(&fold(Proc::PVar(variable("free"))), BoundEnv::new());
    assert!(matches!(error, Err(RholangAstLowerError::UnresolvedProcessReference)));
    assert_idle();
    let next = lower_public_body(&fold(integer(2)), BoundEnv::new()).expect("next request");
    assert_eq!(next.folds.len(), 1);
    assert_eq!(next.folds[0].site_index, 0);
    assert_eq!(next.guard_report, GuardDischargeReport::default());
    assert_idle();
}

#[test]
fn reentry_rejects_without_touching_borrowed_outer_outputs() {
    let output = with_owned_outputs(|_| {
        seed_outputs(1);
        HELD_FOLD_SITES.with(|sites| {
            let held = sites.borrow_mut();
            GUARD_DISCHARGE_REPORT.with(|report| {
                let guards = report.borrow_mut();
                assert!(matches!(
                    lower_public_body(&Proc::PZero, BoundEnv::new()),
                    Err(RholangAstLowerError::ReentrantLoweringSession)
                ));
                assert_eq!(held.len(), 1);
                assert_eq!(guards.residual, 3);
            });
        });
        Ok(Par::default())
    })
    .expect("outer request remains valid");
    assert_eq!(output.folds.len(), 1);
    assert_eq!(output.guard_report.residual, 3);
    assert_idle();
}

#[test]
#[ignore = "Post-demo milestone: panic-recovery validation requires a supported unwind backend"]
fn unwinding_discards_partial_outputs_and_releases_the_session() {
    let result = std::panic::catch_unwind(|| {
        let _ = with_owned_outputs(|_| {
            seed_outputs(1);
            panic!("synthetic lowering panic");
        });
    });
    assert!(result.is_err());
    assert_idle();
    assert!(lower_public_body(&Proc::PZero, BoundEnv::new()).is_ok());
    assert_idle();
}

#[test]
#[ignore = "Post-demo milestone: panic-recovery validation requires a supported unwind backend"]
fn unwinding_releases_live_accumulator_borrows_before_owner_cleanup() {
    let result = std::panic::catch_unwind(|| {
        let _ = with_owned_outputs(|_| {
            seed_outputs(1);
            HELD_FOLD_SITES.with(|sites| {
                let _folds = sites.borrow_mut();
                GUARD_DISCHARGE_REPORT.with(|report| {
                    let _report = report.borrow_mut();
                    panic!("panic with both accumulator borrows live");
                });
            });
            Ok(Par::default())
        });
    });
    assert!(result.is_err());
    assert_idle();
    assert!(lower_public_body(&Proc::PZero, BoundEnv::new()).is_ok());
    assert_idle();
}

#[test]
fn fold_site_byte_boundary_rejects_before_recording_or_channel_construction() {
    assert_eq!(checked_fold_site_index(0), Ok(0));
    assert_eq!(checked_fold_site_index(255), Ok(255));
    for index in [256, usize::MAX] {
        assert_eq!(
            checked_fold_site_index(index),
            Err(RholangAstLowerError::FoldSiteIndexOverflow { index })
        );
    }
    let proc = fold(integer(1));
    let last = with_owned_outputs(|owner| {
        seed_outputs(255);
        owner.drive(Seed::Body(&proc), &BoundEnv::new())
    })
    .expect("index255 is representable");
    assert_eq!(last.folds.len(), 256);
    assert_eq!(last.folds[255].site_index, 255);
    let overflow = with_owned_outputs(|owner| {
        seed_outputs(256);
        let result = owner.drive(Seed::Body(&proc), &BoundEnv::new());
        assert_eq!(HELD_FOLD_SITES.with(|sites| sites.borrow().len()), 256);
        result
    });
    assert!(matches!(
        overflow,
        Err(RholangAstLowerError::FoldSiteIndexOverflow { index: 256 })
    ));
    assert_idle();
}

#[test]
fn declared_guard_options_and_owned_reports_follow_the_existing_driver() {
    let proc = Proc::parse_via_wpda(r#"new c in { for(x <- c where true){ Nil } }"#)
        .expect("guard source");
    for options in [LoweringOptions::PRODUCTION, LoweringOptions::NO_DISCHARGE] {
        let expected = with_owned_outputs(|owner| {
            owner.drive(Seed::Body(&proc), &BoundEnv::with_options(options))
        })
        .expect("reference");
        let actual =
            lower_public_body(&proc, BoundEnv::with_options(options)).expect("owned public");
        assert_eq!(actual.par.encode_to_vec(), expected.par.encode_to_vec());
        assert_eq!(actual.guard_report, expected.guard_report);
        assert_eq!(actual.guard_report.total(), usize::from(options.guard_discharge));
        assert_idle();
    }
}

#[test]
fn supplied_resolver_is_consulted_by_the_actual_whole_body_driver() {
    struct RecordingResolver(Rc<Cell<usize>>);
    impl FltResolve for RecordingResolver {
        fn resolve(&self, tag: &str) -> Option<&dyn mettail_rholang_codegen::FltReflect> {
            assert_eq!(tag, "guest");
            self.0.set(self.0.get() + 1);
            None
        }
    }
    let calls = Rc::new(Cell::new(0));
    let resolver: Arc<dyn FltResolve> = Arc::new(RecordingResolver(calls.clone()));
    let result = lower_public_body(&unresolved_flt(), BoundEnv::with_resolver(resolver));
    assert!(matches!(result, Err(RholangAstLowerError::UnresolvedFltTag(tag)) if tag == "guest"));
    assert_eq!(calls.get(), 1, "the supplied resolver, not the empty default, ran");
    assert_idle();
}

#[test]
fn compatibility_fold_api_cleans_partial_error_outputs() {
    let term = RholangTerm(RholangTermInner::Proc(fold(unresolved_flt())));
    assert!(matches!(
        lower_rholang_term_with_folds(&term),
        Err(RholangAstLowerError::UnresolvedFltTag(tag)) if tag == "guest"
    ));
    assert_idle();
    let next = RholangTerm(RholangTermInner::Proc(fold(integer(1))));
    let (_, folds) = lower_rholang_term_with_folds(&next).expect("next compatibility request");
    assert_eq!(folds.len(), 1);
    assert_eq!(folds[0].site_index, 0);
    assert_idle();
}

#[test]
fn compatibility_fold_api_keeps_the_successful_guard_report_accessor() {
    let proc = Proc::parse_via_wpda(r#"new c in { for(x <- c where true){ Nil } }"#)
        .expect("guard source");
    let expected = with_owned_outputs(|owner| owner.drive(Seed::Body(&proc), &BoundEnv::new()))
        .expect("reference");
    let term = RholangTerm(RholangTermInner::Proc(proc));
    let (par, folds) = lower_rholang_term_with_folds(&term).expect("compatibility request");
    assert_eq!(par.encode_to_vec(), expected.par.encode_to_vec());
    assert_eq!(folds.len(), expected.folds.len());
    assert_eq!(take_guard_discharge_report(), expected.guard_report);
    assert_idle();
}

#[test]
fn resolver_callbacks_cannot_reenter_legacy_lowering() {
    struct ReenteringResolver;
    impl FltResolve for ReenteringResolver {
        fn resolve(&self, _: &str) -> Option<&dyn mettail_rholang_codegen::FltReflect> {
            let proc = fold(integer(7));
            let context = BoundEnv::new();
            for result in [
                lower_rholang_proc(&proc),
                lower_rholang_proc_with_options(&proc, LoweringOptions::NO_DISCHARGE),
                lower_rholang_proc_with_resolver(&proc, Arc::new(EmptyFltResolver)),
                lower_rholang_proc_with_resolver_and_options(
                    &proc,
                    Arc::new(EmptyFltResolver),
                    LoweringOptions::PRODUCTION,
                ),
                lower_proc_in_env(&proc, &context),
                crate::rholang_formula::lower_formula(&proc),
                lower_rholang_name(&Name::NQuote(Arc::new(integer(1)))),
                lower_rholang_term(&RholangTerm(RholangTermInner::Proc(proc.clone()))),
            ] {
                assert!(matches!(result, Err(RholangAstLowerError::ReentrantLoweringSession)));
            }
            assert!(matches!(
                lower_rholang_term_with_folds(&RholangTerm(RholangTermInner::Proc(proc))),
                Err(RholangAstLowerError::ReentrantLoweringSession)
            ));
            None
        }
    }
    let output = with_owned_outputs(|owner| {
        seed_outputs(1);
        let context = BoundEnv::with_resolver(Arc::new(ReenteringResolver));
        let result = owner.drive(Seed::Body(&unresolved_flt()), &context);
        assert!(matches!(result, Err(RholangAstLowerError::UnresolvedFltTag(_))));
        Ok(Par::default())
    })
    .expect("callback cannot consume or corrupt the outer outputs");
    assert_eq!(output.folds.len(), 1);
    assert_eq!(output.guard_report.residual, 3);
    assert_idle();
}

#[test]
#[ignore = "Post-demo milestone: caught accessor panics require a supported unwind backend"]
fn caught_legacy_accessor_panics_preserve_owned_outputs() {
    let output = with_owned_outputs(|_| {
        seed_outputs(1);
        assert!(std::panic::catch_unwind(clear_held_fold_sites).is_err());
        assert!(std::panic::catch_unwind(take_held_fold_sites).is_err());
        assert!(std::panic::catch_unwind(clear_guard_discharge_report).is_err());
        assert!(std::panic::catch_unwind(take_guard_discharge_report).is_err());
        Ok(Par::default())
    })
    .expect("caught access refusal preserves owner");
    assert_eq!(output.folds.len(), 1);
    assert_eq!(output.guard_report.residual, 3);
    assert_idle();
}

#[test]
fn alternative_fold_scope_cleans_up_and_rejects_reentry() {
    let result = with_owned_outputs(|_| {
        let _alternatives = AlternativeFoldScope::enter().unwrap();
        assert!(matches!(
            AlternativeFoldScope::enter(),
            Err(RholangAstLowerError::ReentrantLoweringSession)
        ));
        assert!(matches!(
            SessionGuard::enter(),
            Err(RholangAstLowerError::ReentrantLoweringSession)
        ));
        register_fold_site(FoldKind::Int, 8, "test").unwrap();
        Err(RholangAstLowerError::UnsupportedProc("test rejection"))
    });
    assert!(result.is_err());
    assert_idle();
    let _owner = SessionGuard::enter().unwrap();
    let _alternatives = AlternativeFoldScope::enter().unwrap();
    assert_eq!(register_fold_site(FoldKind::Int, 8, "test"), Ok(0));
}

#[test]
fn alternative_fold_reuse_at_capacity_does_not_allocate_or_alias() {
    let _owner = SessionGuard::enter().unwrap();
    seed_outputs(255);
    let alternatives = AlternativeFoldScope::enter().unwrap();
    assert_eq!(register_fold_site(FoldKind::Int, 8, "test"), Ok(255));
    alternatives.begin_alternative();
    assert_eq!(register_fold_site(FoldKind::Int, 8, "test"), Ok(255));
    for (kind, width, fingerprint) in [
        (FoldKind::UInt, 8, "test"),
        (FoldKind::Int, 9, "test"),
        (FoldKind::Int, 8, "other"),
    ] {
        alternatives.begin_alternative();
        assert_eq!(
            register_fold_site(kind, width, fingerprint),
            Err(RholangAstLowerError::FoldSiteIndexOverflow { index: 256 })
        );
        assert_eq!(HELD_FOLD_SITES.with(|sites| sites.borrow().len()), 256);
    }
    alternatives.begin_alternative();
    assert_eq!(register_fold_site(FoldKind::Int, 8, "test"), Ok(255));
    assert_eq!(
        register_fold_site(FoldKind::Int, 8, "test"),
        Err(RholangAstLowerError::FoldSiteIndexOverflow { index: 256 })
    );
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(256))]

    #[test]
    fn alternative_fold_allocation_matches_position_and_full_signature(
        base in 0usize..256,
        cases in proptest::collection::vec(
            proptest::collection::vec((0usize..6, -12i64..12, 0u8..3), 0..20), 0..20),
    ) {
        use proptest::prelude::*;
        let _owner = SessionGuard::enter().unwrap();
        seed_outputs(base);
        let alternatives = AlternativeFoldScope::enter().unwrap();
        let kinds = [FoldKind::Int, FoldKind::UInt, FoldKind::Float, FoldKind::Fixed,
            FoldKind::BigIntCast, FoldKind::BigRatCast];
        let mut expected = std::collections::BTreeMap::new();
        for case in cases {
            alternatives.begin_alternative();
            for (ordinal, (kind, width, language)) in case.into_iter().enumerate() {
                let key = (ordinal, kind, width, language);
                let next = base + expected.len();
                let expected_index = expected.get(&key).copied().map(Ok).unwrap_or_else(|| {
                    u8::try_from(next).map_err(|_| RholangAstLowerError::FoldSiteIndexOverflow { index: next })
                });
                let fingerprint = format!("language-{language}");
                let actual = register_fold_site(kinds[kind], width, &fingerprint);
                prop_assert_eq!(&actual, &expected_index);
                if let Ok(index) = actual {
                    expected.insert(key, index);
                    HELD_FOLD_SITES.with(|sites| {
                        let sites = sites.borrow();
                        let spec = &sites[usize::from(index)];
                        assert_eq!((spec.kind, spec.width, spec.fingerprint.as_str()),
                            (kinds[kind], width, fingerprint.as_str()));
                        assert_eq!(spec.site_index, index);
                    });
                }
                prop_assert_eq!(HELD_FOLD_SITES.with(|sites| sites.borrow().len()), base + expected.len());
                HELD_FOLD_SITES.with(|sites| {
                    let sites = sites.borrow();
                    for spec in &sites[..base] {
                        assert_eq!((spec.kind, spec.width, spec.site_index, spec.fingerprint.as_str()),
                            (FoldKind::Int, 8, 0, "test-only-unused-descriptor"));
                    }
                    for (&(_, kind, width, language), &index) in &expected {
                        let spec = &sites[usize::from(index)];
                        assert_eq!((spec.kind, spec.width, spec.site_index), (kinds[kind], width, index));
                        assert_eq!(spec.fingerprint, format!("language-{language}"));
                    }
                });
            }
        }
    }
}
