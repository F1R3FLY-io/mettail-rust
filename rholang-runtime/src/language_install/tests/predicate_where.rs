use super::*;
use crate::guard_par_substrate::SubstrateGuardMatcher;
use crate::semantic_service::predicate::PredicateCommit;
use mettail_prattail::algebra_tower::Sat3;
use models::rhoapi::{
    tagged_continuation::TaggedCont, BindPattern, ListParWithRandom, TaggedContinuation,
};
use rspace_plus_plus::rspace::{
    errors::RSpaceError,
    r#match::Match,
    rspace_interface::{ISpace, ProduceCommitGuard},
};

fn fixture() -> (Arc<RholangLanguageRuntime>, Par, Par) {
    fixture_result(true)
}

fn fixture_result(accepting: bool) -> (Arc<RholangLanguageRuntime>, Par, Par) {
    let mut language = super::predicate_roles::predicate_language();
    if !accepting {
        let rule = &mut language.theory.rewrites[0];
        rule.arena.terms[rule.right.0 as usize].form = mettail_grammar_core::TheoryTermFormV1::Constructor {
            constructor: "No".into(), arguments: vec![],
        };
    }
    let value = mettail_elab::core_value::language_core_to_value(&language).unwrap();
    let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    ))));
    let token = runtime.install(InstallCandidate::Canonical(value)).unwrap();
    let input = runtime
        .construct_template(
            &token,
            &[RuntimeTemplatePiece::Text("call".into())],
            &[],
            Some("Expr"),
            &BTreeMap::new(),
        )
        .unwrap();
    (runtime, token, input)
}

fn descriptor(token: &Par, source: &str) -> Par {
    crate::guard_predicate::encode_flt_predicate_descriptor(
        token.clone(),
        &[RuntimeTemplatePiece::Text(source.into())],
        &[],
        "Expr",
        &BTreeMap::new(),
    )
}

#[test]
fn where_predicate_reuses_checked_kernel_and_retains_revocable_authority() {
    let (runtime, token, input) = fixture();
    let limits = SemanticServiceLimits::default();
    let mut checks = 0;
    let evidence = runtime.prepare_where_predicate(&token, &input, 0, 0, limits, || {
        checks += 1;
        false
    });
    assert_eq!(evidence.verdict(), Sat3::Sat, "{:?}", evidence.error());
    let exact_work = evidence.work();
    let permit = PredicateCommit::new(vec![evidence], None).unwrap();
    let mut mutations = 0;
    permit.with_commit(Box::new(|| mutations += 1)).unwrap();
    assert_eq!(mutations, 1);
    let report = runtime.execute_semantic(
        SemanticServiceRequest {
            handle: &token,
            operation: SemanticOperation::Observe("Matches"),
            input: &input,
            limits,
        },
        || false,
    );
    assert_eq!(report.outcome.unwrap().len(), 1);
    for cut in [1, checks / 2, checks] {
        let mut seen = 0;
        let refused = runtime.prepare_where_predicate(&token, &input, 0, 0, limits, || {
            seen += 1;
            seen == cut
        });
        assert_eq!(refused.verdict(), Sat3::DontKnow);
        assert!(refused.work() <= exact_work);
    }
    let mut short = limits;
    short.execution.work = exact_work - 1;
    assert_eq!(
        runtime
            .prepare_where_predicate(&token, &input, 0, 0, short, || false)
            .verdict(),
        Sat3::DontKnow
    );
    runtime.revoke(&token).unwrap();
    assert_eq!(
        permit.with_commit(Box::new(|| mutations += 1)),
        Err(RSpaceError::ProduceCommitDenied)
    );
    assert_eq!(mutations, 1, "revocation never invokes the mutation");
}

#[tokio::test]
async fn where_predicate_actual_comm_unknown_is_nonconsuming_and_true_commits_once() {
    use models::rust::utils::new_freevar_par;
    use rspace_plus_plus::rspace::shared::{
        in_mem_store_manager::InMemoryStoreManager, key_value_store_manager::KeyValueStoreManager,
    };
    for (source, accepting) in [("yes", true), ("call", false), ("call", true)] {
        let (runtime, token, _) = fixture_result(accepting);
        let matcher = SubstrateGuardMatcher::with_language_runtime(runtime);
        let ledger = matcher.refusals();
        let mut manager = InMemoryStoreManager::new();
        let space = crate::speculation::Space::create(
            manager.r_space_stores().await.unwrap(),
            Arc::new(Box::new(matcher)),
        )
        .unwrap();
        let channel = new_gstring_par("predicate-comm".into(), vec![], false);
        let k = TaggedContinuation {
            tagged_cont: Some(TaggedCont::ScalaBodyRef(712)),
            guard: Some(descriptor(&token, source)),
        };
        space
            .consume(
                vec![channel.clone()],
                vec![BindPattern {
                    patterns: vec![new_freevar_par(0, vec![])],
                    remainder: None,
                    free_count: 1,
                }],
                k,
                false,
                std::collections::BTreeSet::new(),
            )
            .await
            .unwrap();
        let data = ListParWithRandom {
            pars: vec![new_gint_par(8, vec![], false)],
            random_state: vec![1; 32],
        };
        let result = space.produce(channel.clone(), data, false).await.unwrap();
        if source == "call" && accepting {
            assert!(result.is_some());
            assert!(space.get_data(&channel).await.is_empty());
            assert!(space
                .get_waiting_continuations(vec![channel])
                .await
                .is_empty());
        } else {
            assert!(result.is_none());
            assert_eq!(space.get_data(&channel).await.len(), 1);
            assert_eq!(space.get_waiting_continuations(vec![channel]).await.len(), 1);
            assert_eq!(ledger.decider_gap_error().is_some(), source == "yes");
        }
    }
}

#[test]
fn where_unknown_stays_unknown_under_not_and_short_circuit_does_not_execute_it() {
    use models::rhoapi::{expr::ExprInstance, ENot, EOr, Expr};
    let (runtime, token, _) = fixture();
    let matcher = SubstrateGuardMatcher::with_language_runtime(runtime);
    let unknown = descriptor(&token, "yes");
    let not = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::ENotBody(ENot { p: Some(unknown.clone()) })),
    }]);
    let continuation = |guard| TaggedContinuation {
        tagged_cont: Some(TaggedCont::ScalaBodyRef(712)),
        guard: Some(guard),
    };
    assert!(matcher.prepare_commit(&continuation(not), &[]).is_none());
    let _ = matcher.refusals().take();
    let yes = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::GBool(true)),
    }]);
    let either = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EOrBody(EOr { p1: Some(yes), p2: Some(unknown) })),
    }]);
    assert!(matcher.prepare_commit(&continuation(either), &[]).is_some());
    assert!(matcher.refusals().decider_gap_error().is_none());
}
