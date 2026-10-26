use super::*;
use crate::guard_par_substrate::SubstrateGuardMatcher;
use crate::semantic_service::{predicate::PredicateCommit, InstalledSemanticError};
use mettail_elab::wire::ParsedDdl;
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
        rule.arena.terms[rule.right.0 as usize].form =
            mettail_grammar_core::TheoryTermFormV1::Constructor {
                constructor: "No".into(),
                arguments: vec![],
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

#[test]
fn where_uses_selected_gslt_projection_after_existing_observation_action() {
    let source = r#"
        Module ProjectedPredicate {
          Theory Predicate() {
            Types { noadmit Expr; }
            Terms {
              Call . |- "call" : Expr;
              Yes . |- "yes" : Expr;
              No . |- "no" : Expr;
            }
            Rewrites {
              Match : (Call) ~> (Yes);
              projection Boolean : Expr ~> host::Bool {
                ToTrue : (Yes) ~> true;
                ToFalse : (No) ~> false;
              }
            }
            Data({
              "rights": ["Parse", "Construct", "Match", "Observe", "ReflectAst", "Reduce", "Bridge"],
              "oslf": {
                "effects": [{"name":"pure"}],
                "actions": [{
                  "id":"match", "domain":["Expr"], "codomain":"Expr",
                  "transition":["rewrite","Match"], "effect":"pure",
                  "grade":"Expr", "execution":"one_step"
                }],
                "observations": [{
                  "name":"Matches", "action":"match", "result":"Expr"
                }]
              }
            })
          }
          theory Predicate()
        }
    "#;
    for (result, overlapping, expected) in [
        ("Yes", false, Sat3::Sat),
        ("No", false, Sat3::Unsat),
        ("Yes", true, Sat3::DontKnow),
    ] {
        let source =
            source.replace("Match : (Call) ~> (Yes);", &format!("Match : (Call) ~> ({result});"));
        let source = if overlapping {
            source.replace(
                r#""name":"Matches", "action":"match", "result":"Expr""#,
                r#""name":"Matches", "action":"match", "result":"Expr"},
                   {"name":"MatchesAgain", "action":"match", "result":"Expr""#,
            )
        } else {
            source
        };
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = RholangLanguageRuntime::new(service);
        let module = mettail_elab::parse::parse_module(&source).unwrap();
        let token = runtime
            .install(InstallCandidate::Ddl(ParsedDdl::Module(module)))
            .expect("projected GSLT is installed");
        let input = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("call".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .unwrap();
        let evidence = runtime.prepare_where_predicate(
            &token,
            &input,
            "Expr",
            0,
            0,
            SemanticServiceLimits::default(),
            || false,
        );
        assert_eq!(evidence.verdict(), expected, "{:?}", evidence.error());
    }
}

fn authored_boolean_fixture(
    result: &str,
    include_false_rule: bool,
) -> (Arc<RholangLanguageRuntime>, Par, Par) {
    let source = r#"
        Module ActionlessPredicate {
          Theory Predicate() {
            Types { noadmit Expr; }
            Terms {
              Call . |- "call" : Expr;
              Yes . |- "yes" : Expr;
              No . |- "no" : Expr;
            }
            Rewrites {
              Match : (Call) ~> (Yes);
              projection Boolean : Expr ~> host::Bool {
                ToTrue : (Yes) ~> true;
                ToFalse : (No) ~> false;
              }
            }
            Data({"rights":["Parse","Construct","Match","Observe","ReflectAst","Reduce","Bridge"]})
          }
          theory Predicate()
        }
    "#;
    let source =
        source.replace("Match : (Call) ~> (Yes);", &format!("Match : (Call) ~> ({result});"));
    let source = if include_false_rule {
        source
    } else {
        source.replace("ToFalse : (No) ~> false;", "")
    };
    let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    ))));
    let module = mettail_elab::parse::parse_module(&source).unwrap();
    let token = runtime
        .install(InstallCandidate::Ddl(ParsedDdl::Module(module)))
        .expect("actionless projected GSLT installs");
    let input = runtime
        .construct_template(
            &token,
            &[RuntimeTemplatePiece::Text("call".into())],
            &[],
            Some("Expr"),
            &BTreeMap::new(),
        )
        .expect("exact guest call");
    (runtime, token, input)
}

#[test]
fn where_uses_authored_boolean_projection_without_an_action_descriptor() {
    for (result, include_false_rule, expected) in [
        ("Yes", true, Sat3::Sat),
        ("No", true, Sat3::Unsat),
        ("No", false, Sat3::DontKnow),
    ] {
        let (runtime, token, input) = authored_boolean_fixture(result, include_false_rule);
        let evidence = runtime.prepare_where_predicate(
            &token,
            &input,
            "Expr",
            0,
            0,
            SemanticServiceLimits::default(),
            || false,
        );
        assert_eq!(evidence.verdict(), expected, "{:?}", evidence.error());
    }
}

#[test]
fn where_authored_projection_precedes_native_boolean_carrier_fallback() {
    let source = r#"
        Module BooleanGuestProjection {
          Theory Predicate() {
            Types { noadmit Flag = bool; }
            Terms {
              Yes . |- "yes" : Flag;
              No . |- "no" : Flag;
            }
            Rewrites {
              projection Invert : Flag ~> host::Bool {
                YesIsFalse : (Yes) ~> false;
                NoIsTrue : (No) ~> true;
              }
            }
            Data({"rights":["Parse","Construct","Match","Observe","ReflectAst","Reduce","Bridge"]})
          }
          theory Predicate()
        }
    "#;
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let module = mettail_elab::parse::parse_module(source).expect("Boolean guest DDL parses");
    let token = runtime
        .install(InstallCandidate::Ddl(ParsedDdl::Module(module)))
        .expect("Boolean guest projection installs");
    for (text, expected) in [("yes", Sat3::Unsat), ("no", Sat3::Sat)] {
        let input = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text(text.into())],
                &[],
                Some("Flag"),
                &BTreeMap::new(),
            )
            .expect("exact Boolean guest term");
        let evidence = runtime.prepare_where_predicate(
            &token,
            &input,
            "Flag",
            0,
            0,
            SemanticServiceLimits::default(),
            || false,
        );
        assert_eq!(evidence.verdict(), expected, "{text}: {:?}", evidence.error());
    }
}

fn carrier_projection_fixture(
    rewrites: &str,
    projections: &str,
) -> (RholangLanguageRuntime, Par, Par) {
    let source = format!(
        r#"
        Module CarrierPredicate {{
          Theory Predicate() {{
            Types {{ noadmit Flag = bool; }}
            Terms {{ Call . |- "call" : Flag; }}
            Rewrites {{ {rewrites} {projections} }}
            Data({{"rights":["Parse","Construct","Match","Observe","ReflectAst","Reduce","Bridge"],"oslf":{{}}}})
          }}
          theory Predicate()
        }}
        "#
    );
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let module = mettail_elab::parse::parse_module(&source).expect("carrier projection DDL");
    let token = runtime
        .install(InstallCandidate::Ddl(ParsedDdl::Module(module)))
        .expect("carrier projection installs");
    let input = runtime
        .construct_template(
            &token,
            &[RuntimeTemplatePiece::Text("call".into())],
            &[],
            Some("Flag"),
            &BTreeMap::new(),
        )
        .expect("carrier predicate input");
    (runtime, token, input)
}

fn carrier_descriptor(token: &Par) -> Par {
    crate::guard_predicate::encode_flt_predicate_descriptor(
        token.clone(),
        &[RuntimeTemplatePiece::Text("call".into())],
        &[],
        "Flag",
        &BTreeMap::new(),
    )
}

#[test]
fn where_carrier_relation_uses_complete_checked_native_roster() {
    let projection = "projection Boolean : Flag ~> host::Bool via carrier;";
    for (rewrites, expected) in [
        ("ToTrue : (Call) ~> true;", Sat3::Sat),
        ("ToFalse : (Call) ~> false;", Sat3::Unsat),
        ("ToTrue : (Call) ~> true; AlsoTrue : (Call) ~> true;", Sat3::Sat),
        ("ToTrue : (Call) ~> true; ToFalse : (Call) ~> false;", Sat3::DontKnow),
        ("", Sat3::DontKnow),
    ] {
        let (runtime, token, input) = carrier_projection_fixture(rewrites, projection);
        let evidence = runtime.prepare_where_predicate(
            &token,
            &input,
            "Flag",
            0,
            0,
            SemanticServiceLimits::default(),
            || false,
        );
        assert_eq!(evidence.verdict(), expected, "{rewrites}: {:?}", evidence.error());
    }
}

#[test]
fn where_native_carrier_fallback_requires_no_applicable_authored_relation() {
    let (runtime, token, input) = carrier_projection_fixture("ToTrue : (Call) ~> true;", "");
    let evidence = runtime.prepare_where_predicate(
        &token,
        &input,
        "Flag",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(evidence.verdict(), Sat3::Sat, "{:?}", evidence.error());
}

#[test]
fn where_native_fallback_rechecks_exact_host_profile_at_comm() {
    let (mut runtime, token, input) = carrier_projection_fixture("ToTrue : (Call) ~> true;", "");
    let evidence = runtime.prepare_where_predicate(
        &token,
        &input,
        "Flag",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(evidence.verdict(), Sat3::Sat, "{:?}", evidence.error());
    let permit = PredicateCommit::new(vec![evidence], None).expect("native Boolean evidence");
    let service = Arc::get_mut(&mut runtime.service).expect("sole service owner");
    let grant = std::mem::replace(
        &mut service.builtin_host_profile,
        Err(crate::host_profile::RholangHostProfileError::UnsupportedGeneratedFragment(
            "test authority consumed",
        )),
    )
    .expect("exact built-in host profile");
    service
        .table()
        .revoke_host_profile(grant.revocation)
        .expect("revoke selected host profile");
    let mut mutations = 0;
    assert_eq!(
        permit.with_commit(Box::new(|| mutations += 1)),
        Err(RSpaceError::ProduceCommitDenied)
    );
    assert_eq!(mutations, 0);
}

#[test]
fn where_carrier_relation_refuses_ambiguous_endpoint_and_rechecks_revocation() {
    let (runtime, token, input) = carrier_projection_fixture(
        "ToTrue : (Call) ~> true;",
        "projection First : Flag ~> host::Bool via carrier; projection Second : Flag ~> host::Bool via carrier;",
    );
    let evidence = runtime.prepare_where_predicate(
        &token,
        &input,
        "Flag",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(evidence.verdict(), Sat3::DontKnow);
    assert!(matches!(evidence.error(), Some(InstalledSemanticError::InvalidSelection(_))));

    let (runtime, token, input) = carrier_projection_fixture(
        "ToTrue : (Call) ~> true;",
        "projection Boolean : Flag ~> host::Bool via carrier;",
    );
    let evidence = runtime.prepare_where_predicate(
        &token,
        &input,
        "Flag",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(evidence.verdict(), Sat3::Sat, "{:?}", evidence.error());
    let permit = PredicateCommit::new(vec![evidence], None).expect("checked carrier evidence");
    runtime.revoke(&token).expect("revoke installed guest");
    let mut mutations = 0;
    assert_eq!(
        permit.with_commit(Box::new(|| mutations += 1)),
        Err(RSpaceError::ProduceCommitDenied)
    );
    assert_eq!(mutations, 0);
}

#[tokio::test]
async fn where_carrier_relation_guards_actual_rspace_comm() {
    use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par};
    use rspace_plus_plus::rspace::shared::{
        in_mem_store_manager::InMemoryStoreManager, key_value_store_manager::KeyValueStoreManager,
    };
    for (rewrites, accepts) in [
        ("ToTrue : (Call) ~> true;", true),
        ("ToFalse : (Call) ~> false;", false),
        ("ToTrue : (Call) ~> true; ToFalse : (Call) ~> false;", false),
        ("", false),
    ] {
        let (runtime, token, _) = carrier_projection_fixture(
            rewrites,
            "projection Boolean : Flag ~> host::Bool via carrier;",
        );
        let matcher = SubstrateGuardMatcher::with_language_runtime(Arc::new(runtime));
        let mut manager = InMemoryStoreManager::new();
        let space = crate::speculation::Space::create(
            manager.r_space_stores().await.expect("in-memory RSpace"),
            Arc::new(Box::new(matcher)),
        )
        .expect("guarded RSpace");
        let channel = new_gstring_par("carrier-projection-comm".into(), vec![], false);
        space
            .consume(
                vec![channel.clone()],
                vec![BindPattern {
                    patterns: vec![new_freevar_par(0, vec![])],
                    remainder: None,
                    free_count: 1,
                }],
                TaggedContinuation {
                    tagged_cont: Some(TaggedCont::ScalaBodyRef(716)),
                    guard: Some(carrier_descriptor(&token)),
                    cost_authority: None,
                },
                false,
                std::collections::BTreeSet::new(),
            )
            .await
            .expect("install carrier guarded receive");
        let datum = ListParWithRandom {
            pars: vec![new_gint_par(8, vec![], false)],
            random_state: vec![4; 32],
            ..ListParWithRandom::default()
        };
        let committed = space
            .produce(channel.clone(), datum, false)
            .await
            .expect("offer guarded datum");
        assert_eq!(committed.is_some(), accepts, "{rewrites}");
        assert_eq!(
            space
                .get_data(&channel)
                .await
                .expect("read data")
                .is_empty(),
            accepts
        );
        assert_eq!(
            space
                .get_waiting_continuations(vec![channel])
                .await
                .expect("read waiting continuations")
                .is_empty(),
            accepts
        );
    }
}

#[test]
fn projected_guest_publication_is_refused_after_host_profile_revocation() {
    let source = r#"
        Module HostRevocation {
          Theory Guest() {
            Types { noadmit Expr; }
            Terms { Yes . |- "yes" : Expr; }
            Rewrites {
              projection Boolean : Expr ~> host::Bool {
                YesRule : (Yes) ~> true;
              }
            }
          }
          theory Guest()
        }
    "#;
    let mut service = LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    );
    let module = mettail_elab::parse::parse_module(source).unwrap();
    let batch = service
        .install_all(InstallCandidate::Ddl(ParsedDdl::Module(module)))
        .expect("projected GSLT is installed");
    let handle = &batch.exports[0].receipt.handle;
    assert!(service
        .table()
        .with_authorized_batch([(handle, &[][..])], || ())
        .is_ok());
    let grant = std::mem::replace(
        &mut service.builtin_host_profile,
        Err(crate::host_profile::RholangHostProfileError::UnsupportedGeneratedFragment(
            "test authority consumed",
        )),
    )
    .expect("compiled host profile was installed");
    service
        .table()
        .revoke_host_profile(grant.revocation)
        .unwrap();
    assert_eq!(
        service
            .table()
            .with_authorized_batch([(handle, &[][..])], || ())
            .unwrap_err(),
        mettail_grammar_core::LanguageAccessError::HostProfileUnavailable,
    );
}

/// An authored guest-to-native projection, with no action or observation role.
/// `Yes` and `No` stay guest constructors; only `ToHostBool` reduces to a
/// literal in the declared Boolean carrier.
fn native_boolean_fixture(outcomes: &[bool]) -> (Arc<RholangLanguageRuntime>, Par, Par) {
    native_boolean_fixture_with_policy(outcomes, LanguageInstallPolicy::default())
}

fn native_boolean_fixture_with_policy(
    outcomes: &[bool],
    policy: LanguageInstallPolicy,
) -> (Arc<RholangLanguageRuntime>, Par, Par) {
    let ctor = |name: &str| l([s(name)]);
    let projected = |value: bool| l([s("ToHostBool"), ctor(if value { "Yes" } else { "No" })]);
    let mut rewrites = Vec::new();
    for (index, &value) in outcomes.iter().enumerate() {
        rewrites.push(m([
            ("name", s(&format!("Start{index}"))),
            ("left", ctor("Call")),
            ("right", projected(value)),
        ]));
    }
    for value in [false, true] {
        rewrites.push(m([
            ("name", s(if value { "ProjectYes" } else { "ProjectNo" })),
            ("left", projected(value)),
            ("right", l([s("lit"), s("bool"), RhoValue::Boolean(value)])),
        ]));
    }
    let term = |label: &str, text: &str| {
        m([
            ("label", s(label)),
            ("category", s("Expr")),
            ("syntax", l([l([s("lit"), s(text)])])),
        ])
    };
    let value = m([
        ("mettail", s("language/3")),
        ("name", s("NativePredicate")),
        (
            "types",
            l([m([
                ("name", s("Expr")),
                ("carrier", s("bool")),
                ("admits_variables", RhoValue::Boolean(false)),
            ])]),
        ),
        (
            "terms",
            l([
                term("Call", "call"),
                term("Yes", "yes"),
                term("No", "no"),
                m([
                    ("label", s("ToHostBool")),
                    ("category", s("Expr")),
                    ("context", l([l([s("param"), s("b"), s("Expr")])])),
                    ("syntax", l([l([s("lit"), s("toHostBool(")]), s("b"), l([s("lit"), s(")")])])),
                ]),
            ]),
        ),
        ("rewrites", l(rewrites)),
    ]);
    let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        policy,
    ))));
    let token = runtime
        .install(InstallCandidate::Canonical(value))
        .expect("native Boolean language");
    let input = runtime
        .construct_template(
            &token,
            &[RuntimeTemplatePiece::Text("call".into())],
            &[],
            Some("Expr"),
            &BTreeMap::new(),
        )
        .expect("constructed exact native predicate input");
    (runtime, token, input)
}

#[test]
fn where_native_boolean_requires_rights_owner_and_complete_budget() {
    let (runtime, token, input) = native_boolean_fixture(&[true]);
    let baseline = runtime.prepare_where_predicate(
        &token,
        &input,
        "Expr",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(baseline.verdict(), Sat3::Sat, "{:?}", baseline.error());
    let mut short = SemanticServiceLimits::default();
    short.execution.work = baseline.work() - 1;
    assert_eq!(
        runtime
            .prepare_where_predicate(&token, &input, "Expr", 0, 0, short, || false)
            .verdict(),
        Sat3::DontKnow,
        "an unfinished proof cannot be coerced to false"
    );
    let (_, _, foreign_input) = native_boolean_fixture(&[false]);
    let mismatched = runtime.prepare_where_predicate(
        &token,
        &foreign_input,
        "Expr",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(mismatched.verdict(), Sat3::DontKnow);
    assert!(mismatched.error().is_some(), "foreign owner cannot yield true evidence");

    let grants = LanguageRights::from_rights([
        LanguageRight::Parse,
        LanguageRight::Construct,
        LanguageRight::Observe,
    ]);
    let policy = LanguageInstallPolicy::new(
        grants,
        RuntimePolicy::default(),
        LANGUAGE_CAPABILITY_ABI_CURRENT,
    );
    let (limited, token, input) = native_boolean_fixture_with_policy(&[true], policy);
    let missing_reduce = limited.prepare_where_predicate(
        &token,
        &input,
        "Expr",
        0,
        0,
        SemanticServiceLimits::default(),
        || false,
    );
    assert_eq!(missing_reduce.verdict(), Sat3::DontKnow);
    assert!(matches!(
        missing_reduce.error(),
        Some(InstalledSemanticError::Access(LanguageAccessError::MissingRight(
            LanguageRight::Reduce
        )))
    ));
}

#[test]
fn where_native_boolean_projection_requires_complete_uniform_evidence() {
    for (outcomes, expected) in [
        (&[true][..], Sat3::Sat),
        (&[true, true][..], Sat3::Sat),
        (&[false][..], Sat3::Unsat),
        (&[false, false][..], Sat3::Unsat),
        (&[true, false][..], Sat3::DontKnow),
        (&[][..], Sat3::DontKnow),
    ] {
        let (runtime, token, input) = native_boolean_fixture(outcomes);
        let evidence = runtime.prepare_where_predicate(
            &token,
            &input,
            "Expr",
            0,
            0,
            SemanticServiceLimits::default(),
            || false,
        );
        assert_eq!(evidence.verdict(), expected, "{outcomes:?}: {:?}", evidence.error());
        if expected == Sat3::Sat {
            let permit = PredicateCommit::new(vec![evidence], None).expect("checked true evidence");
            runtime
                .revoke(&token)
                .expect("revoke exact installed owner");
            let mut mutations = 0;
            assert_eq!(
                permit.with_commit(Box::new(|| mutations += 1)),
                Err(RSpaceError::ProduceCommitDenied)
            );
            assert_eq!(mutations, 0);
        }
    }
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
    let evidence = runtime.prepare_where_predicate(&token, &input, "Expr", 0, 0, limits, || {
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
        let refused = runtime.prepare_where_predicate(&token, &input, "Expr", 0, 0, limits, || {
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
            .prepare_where_predicate(&token, &input, "Expr", 0, 0, short, || false)
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
            cost_authority: None,
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
            ..ListParWithRandom::default()
        };
        let result = space.produce(channel.clone(), data, false).await.unwrap();
        if source == "call" && accepting {
            assert!(result.is_some());
            assert!(space
                .get_data(&channel)
                .await
                .expect("read data")
                .is_empty());
            assert!(space
                .get_waiting_continuations(vec![channel])
                .await
                .expect("read waiting continuations")
                .is_empty());
        } else {
            assert!(result.is_none());
            assert_eq!(space.get_data(&channel).await.expect("read data").len(), 1);
            assert_eq!(
                space
                    .get_waiting_continuations(vec![channel])
                    .await
                    .expect("read waiting continuations")
                    .len(),
                1
            );
            assert_eq!(ledger.decider_gap_error().is_some(), source == "yes");
        }
    }
}

#[tokio::test]
async fn where_native_boolean_actual_comm_requires_complete_true_evidence() {
    use models::rust::utils::new_freevar_par;
    use rspace_plus_plus::rspace::shared::{
        in_mem_store_manager::InMemoryStoreManager, key_value_store_manager::KeyValueStoreManager,
    };
    for (outcomes, accepts) in
        [(&[true][..], true), (&[false][..], false), (&[true, false][..], false)]
    {
        let (runtime, token, _) = native_boolean_fixture(outcomes);
        let matcher = SubstrateGuardMatcher::with_language_runtime(runtime);
        let mut manager = InMemoryStoreManager::new();
        let space = crate::speculation::Space::create(
            manager.r_space_stores().await.unwrap(),
            Arc::new(Box::new(matcher)),
        )
        .unwrap();
        let channel = new_gstring_par("native-predicate-comm".into(), vec![], false);
        space
            .consume(
                vec![channel.clone()],
                vec![BindPattern {
                    patterns: vec![new_freevar_par(0, vec![])],
                    remainder: None,
                    free_count: 1,
                }],
                TaggedContinuation {
                    tagged_cont: Some(TaggedCont::ScalaBodyRef(713)),
                    guard: Some(descriptor(&token, "call")),
                    cost_authority: None,
                },
                false,
                std::collections::BTreeSet::new(),
            )
            .await
            .unwrap();
        let data = ListParWithRandom {
            pars: vec![new_gint_par(8, vec![], false)],
            random_state: vec![2; 32],
            ..ListParWithRandom::default()
        };
        let result = space.produce(channel.clone(), data, false).await.unwrap();
        assert_eq!(result.is_some(), accepts, "outcomes: {outcomes:?}");
        assert_eq!(
            space
                .get_data(&channel)
                .await
                .expect("read data")
                .is_empty(),
            accepts
        );
        assert_eq!(
            space
                .get_waiting_continuations(vec![channel])
                .await
                .expect("read waiting continuations")
                .is_empty(),
            accepts
        );
    }
}

#[tokio::test]
async fn where_authored_projection_actual_comm_requires_complete_true_evidence() {
    use models::rust::utils::new_freevar_par;
    use rspace_plus_plus::rspace::shared::{
        in_mem_store_manager::InMemoryStoreManager, key_value_store_manager::KeyValueStoreManager,
    };
    for (result, include_false_rule, accepts, unknown) in [
        ("Yes", true, true, false),
        ("No", true, false, false),
        ("No", false, false, true),
    ] {
        let (runtime, token, input) = authored_boolean_fixture(result, include_false_rule);
        let matcher = SubstrateGuardMatcher::with_language_runtime(Arc::clone(&runtime));
        let ledger = matcher.refusals();
        let mut manager = InMemoryStoreManager::new();
        let space = crate::speculation::Space::create(
            manager.r_space_stores().await.expect("in-memory RSpace"),
            Arc::new(Box::new(matcher)),
        )
        .expect("guarded RSpace");
        let channel = new_gstring_par("authored-projection-comm".into(), vec![], false);
        space
            .consume(
                vec![channel.clone()],
                vec![BindPattern {
                    patterns: vec![new_freevar_par(0, vec![])],
                    remainder: None,
                    free_count: 1,
                }],
                TaggedContinuation {
                    tagged_cont: Some(TaggedCont::ScalaBodyRef(715)),
                    guard: Some(descriptor(&token, "call")),
                    cost_authority: None,
                },
                false,
                std::collections::BTreeSet::new(),
            )
            .await
            .expect("install guarded receive");
        let data = ListParWithRandom {
            pars: vec![new_gint_par(8, vec![], false)],
            random_state: vec![3; 32],
            ..ListParWithRandom::default()
        };
        let committed = space
            .produce(channel.clone(), data, false)
            .await
            .expect("offer guarded datum");
        assert_eq!(
            committed.is_some(),
            accepts,
            "result {result}, false rule {include_false_rule}"
        );
        assert_eq!(
            space
                .get_data(&channel)
                .await
                .expect("read data")
                .is_empty(),
            accepts
        );
        assert_eq!(
            space
                .get_waiting_continuations(vec![channel])
                .await
                .expect("read waiting continuations")
                .is_empty(),
            accepts
        );
        assert_eq!(ledger.decider_gap_error().is_some(), unknown);

        if accepts {
            let evidence = runtime.prepare_where_predicate(
                &token,
                &input,
                "Expr",
                0,
                0,
                SemanticServiceLimits::default(),
                || false,
            );
            assert_eq!(evidence.verdict(), Sat3::Sat);
            let permit = PredicateCommit::new(vec![evidence], None)
                .expect("authored projection yields checked true evidence");
            runtime.revoke(&token).expect("revoke projection owner");
            let mut mutations = 0;
            assert_eq!(
                permit.with_commit(Box::new(|| mutations += 1)),
                Err(RSpaceError::ProduceCommitDenied)
            );
            assert_eq!(mutations, 0, "revocation must precede atomic mutation");
        }
    }
}

#[test]
fn where_native_boolean_negation_requires_determinate_evidence() {
    use models::rhoapi::{expr::ExprInstance, ENot, Expr};
    for (outcomes, expected) in [(&[false][..], true), (&[true, false][..], false)] {
        let (runtime, token, _) = native_boolean_fixture(outcomes);
        let matcher = SubstrateGuardMatcher::with_language_runtime(runtime);
        let not = Par::default().with_exprs(vec![Expr {
            expr_instance: Some(ExprInstance::ENotBody(ENot {
                p: Some(descriptor(&token, "call")),
            })),
        }]);
        let continuation = TaggedContinuation {
            tagged_cont: Some(TaggedCont::ScalaBodyRef(714)),
            guard: Some(not),
            cost_authority: None,
        };
        assert_eq!(matcher.prepare_commit(&continuation, &[]).is_some(), expected);
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
        cost_authority: None,
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
