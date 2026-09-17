use super::*;
use prost::Message;

fn integer(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
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
