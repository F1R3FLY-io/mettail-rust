use super::*;
use crate::host_profile::{
    RholangHostCompoundProfileProviderV2, SharedProjectedTheoryImageCompiler,
};
use crate::language_install::{
    tests::rholang_ddl_candidate, EmptyRegistrySnapshot, LanguageInstallPolicy,
    LanguageInstallService, LANGUAGE_CAPABILITY_ABI_V1,
};
use dovetail::egraph::{EGraph, ENode};
use mettail_dovetail_runtime::theory_operator_to_machine;
use mettail_grammar_core as core;
use mettail_languages::rholang::{CostSig, Proc};
use mettail_prattail::runtime_backend::{
    compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI,
};
use proptest::prelude::*;
use std::sync::OnceLock;

const WORK_LIMIT: u64 = 2_000_000;
const PAYLOAD_LIMIT: usize = 16 * 1024 * 1024;
const PROJECTION_OCCURRENCE: u32 = 7;

fn constructor(
    sort: &str,
    name: &str,
    arguments: Vec<core::TheoryTermId>,
) -> core::TheoryTermNodeV1 {
    core::TheoryTermNodeV1 {
        sort: sort.into(),
        form: core::TheoryTermFormV1::Constructor { constructor: name.into(), arguments },
    }
}

fn costed_guest() -> core::LanguageCoreV1 {
    static SOURCE: OnceLock<core::LanguageCoreV1> = OnceLock::new();
    SOURCE
        .get_or_init(|| {
            let service = LanguageInstallService::new(
                Arc::new(EmptyRegistrySnapshot),
                LanguageInstallPolicy::default(),
            );
            let receipt = service
                .install(rholang_ddl_candidate(
                    r#"Theory FundingRoster() {
                        Types { Expr; Sig; }
                        Terms {
                            Start . |- "start" : Expr;
                            Done . |- "done" : Expr;
                            SigTick . |- "tick" : Sig;
                        }
                    }"#,
                ))
                .expect("the guest grammar installs through the existing DDL fixture");
            let installed = service
                .table()
                .authorize(&receipt.handle, LanguageRight::Construct)
                .expect("installed guest grammar");
            let mut language = installed.language_core().clone();
            let mut theory = core::TheoryCoreV1::structural();
            theory.profile = core::TheoryProfileV1::Oslf;
            for name in ["Expr", "Sig"] {
                theory.sorts.push(core::TheorySortV1 {
                    name: name.into(),
                    kind: TheorySortKindV1::Syntax { literal: None },
                });
            }
            for name in ["Stack", "Wrapped", "Located", "Channel", "Datum", "Continuation"] {
                theory.sorts.push(core::TheorySortV1 {
                    name: name.into(),
                    kind: TheorySortKindV1::Opaque { abi: format!("test/{name}/1") },
                });
            }
            for (name, codomain, domain) in [
                ("Start", "Expr", vec![]),
                ("Done", "Expr", vec![]),
                ("SigTick", "Sig", vec![]),
                ("SigUnit", "Sig", vec![]),
                ("SigProduct", "Sig", vec!["Sig".into(), "Sig".into()]),
            ] {
                theory.constructors.push(core::TheoryConstructorV1 {
                    name: name.into(),
                    codomain: codomain.into(),
                    domain,
                });
            }
            theory.rewrites.push(core::TheoryRewriteV1 {
                name: "start-to-done".into(),
                arena: core::TheoryRuleArenaV1 {
                    variables: vec![],
                    terms: vec![
                        constructor("Expr", "Start", vec![]),
                        constructor("Expr", "Done", vec![]),
                        constructor("Sig", "SigTick", vec![]),
                    ],
                    premises: vec![],
                    premise_roots: vec![],
                },
                left: core::TheoryTermId(0),
                right: core::TheoryTermId(1),
            });
            theory.interactive = Some(core::InteractiveDeclV1 {
                cut: "cut".into(),
                channel_sort: "Channel".into(),
                datum_sort: "Datum".into(),
                continuation_sort: "Continuation".into(),
            });
            theory.continued = Some(core::ContinuedDeclV1 {
                k: "K".into(),
                kp: "Kp".into(),
                ke: "Ke".into(),
                k_prime: "KPrime".into(),
                near: "near".into(),
                compute: "compute".into(),
                section: "section".into(),
                wrappability: "wrappable".into(),
                quote_faithfulness: "quote_faithful".into(),
            });
            theory.cost = Some(core::CostDeclV1 {
                base: "G".into(),
                signature_sort: "Sig".into(),
                stack_sort: "Stack".into(),
                wrapped_sort: "Wrapped".into(),
                located_sort: "Located".into(),
                product: "SigProduct".into(),
                unit: "SigUnit".into(),
                rules: vec!["R1".into()],
                grade_rules: vec![core::CostGradeRuleV1 {
                    rewrite: "start-to-done".into(),
                    term: core::TheoryTermId(2),
                }],
                eta: "eta".into(),
                mu: "mu".into(),
                map: "map".into(),
                laws: vec![],
            });
            language.theory = theory;
            language
        })
        .clone()
}

fn installation_request() -> (
    InstalledLanguageTable,
    core::InstalledHostProfileGrant,
    core::ExecutableFundingProjectedLanguageInstallV2,
) {
    let table = InstalledLanguageTable::with_runtime_projection_and_funding_verifier(
        Arc::new(mettail_prattail::wpda_owned::backend::SharedWpdaRuntimeFactory),
        Arc::new(SharedProjectedTheoryImageCompiler),
        Arc::new(core::FiniteNullaryCostFundingVerifierV2),
    );
    let provider = RholangHostCompoundProfileProviderV2::from_generated()
        .expect("independently checked generated host inverse routes");
    let host = provider
        .install(&table, core::LanguageRights::from_rights([LanguageRight::Bridge]))
        .expect("install the actual compound host codec");
    let signature = table
        .authorize_compound_host_profile_v2(&host.handle, &[LanguageRight::Bridge])
        .expect("live compound host owner")
        .raw_signature()
        .expect("exact host signature");
    let base = costed_guest();
    let parser_image = compile_parser_image(&base.grammar).expect("real guest parser image");
    let projected = core::ProjectedLanguageCoreV1 {
        abi: core::PROJECTED_LANGUAGE_CORE_ABI_V1,
        base,
        projections: vec![core::TheoryProjectionV1 {
            name: "grade_to_host".into(),
            guest_category: "Sig".into(),
            host: core::ProjectionHostEndpointV1 {
                signature_fingerprint: signature.signature_fingerprint,
                category: "Proc".into(),
                codec_profile_fingerprint: signature.codec_profile_fingerprint,
            },
            directions: vec![ProjectionDirectionV1::GuestToHost],
            body: core::ProjectionBodyV1::Rules(vec![core::DirectedProjectionRuleV1 {
                direction: ProjectionDirectionV1::GuestToHost,
                source_occurrence: PROJECTION_OCCURRENCE,
                rule: core::TheoryRewriteV1 {
                    name: "tick_to_signed_nil".into(),
                    arena: core::TheoryRuleArenaV1 {
                        variables: vec![],
                        terms: vec![
                            constructor("Sig", "SigTick", vec![]),
                            constructor("host::Proc", "host::Rholang::Proc::PZero", vec![]),
                            constructor(
                                "host::CostSig",
                                "host::Rholang::CostSig::CostSigHash",
                                vec![core::TheoryTermId(1)],
                            ),
                            constructor(
                                "host::Proc",
                                "host::Rholang::Proc::PCostSignedTerm",
                                vec![core::TheoryTermId(1), core::TheoryTermId(2)],
                            ),
                        ],
                        premises: vec![],
                        premise_roots: vec![],
                    },
                    left: core::TheoryTermId(0),
                    right: core::TheoryTermId(3),
                },
            }]),
        }],
    };
    let request = core::ExecutableFundingProjectedLanguageInstallV2 {
        projected,
        selector: core::FundingProjectionSelectorV2 {
            abi: core::FUNDING_PROJECTION_SELECTOR_ABI_V2,
            projection_name: "grade_to_host".into(),
            guest_grade_sort: "Sig".into(),
            host_demand_category: "Proc".into(),
            resource_logic_abi: core::FINITE_COST_RESOURCE_LOGIC_ABI_V2.into(),
            bound_verifier_abi: core::FINITE_COST_BOUND_VERIFIER_ABI_V2.into(),
            projection_proof_abi: core::FINITE_COST_PROJECTION_PROOF_ABI_V2.into(),
            projection_proof_commitment: core::FiniteNullaryCostFundingVerifierV2::proof_commitment(
            ),
        },
        parser_image,
        host_profile: host.handle.clone(),
        granted_rights: core::LanguageRights::from_rights([
            LanguageRight::Reduce,
            LanguageRight::Bridge,
            LanguageRight::Match,
            LanguageRight::Construct,
        ]),
    };
    (table, host, request)
}

fn install(
    table: &InstalledLanguageTable,
    request: core::ExecutableFundingProjectedLanguageInstallV2,
) -> Result<core::InstalledLanguageGrant, core::InstallLanguageError> {
    table
        .install_funding_projected_runtime_batch_v2_with_artifact_limits_and_host(
            vec![request],
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            LANGUAGE_CAPABILITY_ABI_V1,
            [0; 32],
            core::ParserImageAdmissionLimits::default(),
            TheoryImageAdmissionLimits::default(),
            &core::DefaultRuntimeHost,
        )
        .map(|mut grants| grants.pop().expect("one installed funding language"))
}

fn fixture() -> (
    InstalledLanguageTable,
    core::InstalledHostProfileGrant,
    core::InstalledLanguageGrant,
) {
    let (table, host, request) = installation_request();
    let language =
        install(&table, request).expect("the production finite checker admits the fixture");
    (table, host, language)
}

fn execution_limits() -> SemanticTransitionLimits {
    SemanticTransitionLimits {
        work: WORK_LIMIT,
        ..TheoryLimitsV1::default().into()
    }
}

fn guest_roster(
    table: &InstalledLanguageTable,
    handle: &InstalledLanguageHandle,
) -> ProvenSemanticRewriteSteps {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, WORK_LIMIT, PAYLOAD_LIMIT, &mut cancel);
    let prepared = InstalledSemanticBundle::prepare_rewrite_roster(
        table,
        handle,
        &[LanguageRight::Reduce],
        &mut budget,
    )
    .expect("sealed base rewrite matcher");
    let installed = prepared.installed();
    let image = installed
        .base_semantic_image()
        .expect("projected base image");
    let source = installed.language_core();
    let start = source
        .theory
        .constructors
        .iter()
        .position(|constructor| constructor.name == "Start")
        .expect("source Start constructor");
    let start = &image.constructors[start];
    let mut graph = EGraph::new();
    let root = graph.add(ENode::leaf(theory_operator_to_machine(
        &TheoryImageOperatorV1::Constructor(start.id),
    )));
    let SemanticInputDecision::Proven(input) = SemanticTransitionInput::admit(
        graph,
        root,
        SemanticInputLimits {
            work: WORK_LIMIT,
            nodes: 64,
            bytes: PAYLOAD_LIMIT,
        },
        || false,
    ) else {
        panic!("the actual guest Start input must admit")
    };
    let cost = prepared
        .prepare_costed_roster_image(TheoryImageAdmissionLimits::default(), &mut budget)
        .expect("borrow the sealed installation witness");
    let (decision, _) = prepared
        .execute_step_roster_accounted(start.codomain, input, cost, execution_limits(), || false)
        .expect("execute the installed costed rewrite");
    let SemanticTransitionDecision::ProvenSteps(roster) = decision else {
        panic!("the guest rewrite must produce a complete checked roster")
    };
    assert_eq!(roster.occurrences.len(), 1);
    assert_eq!(roster.language_fingerprint, image.language_fingerprint);
    assert_ne!(roster.language_fingerprint, installed.commitment().language_fingerprint);
    assert_eq!(roster.image_fingerprint, image.fingerprint().expect("base image fingerprint"));
    roster
}

fn prepare<'a>(
    table: &InstalledLanguageTable,
    handle: &InstalledLanguageHandle,
    roster: &'a ProvenSemanticRewriteSteps,
) -> Result<PreparedHostDemandRosterV2<'a>, InstalledSemanticError> {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, WORK_LIMIT, PAYLOAD_LIMIT, &mut cancel);
    prepare_checked_host_demand_v2(table, handle, roster, 0, execution_limits(), &mut budget)
}

#[test]
fn installed_cost_grade_projects_through_typed_inverse_to_canonical_par() {
    let (table, _host, language) = fixture();
    let roster = guest_roster(&table, &language.handle);
    let prepared = prepare(&table, &language.handle, &roster)
        .expect("the real base roster composes with its installed funding projection");
    assert!(std::ptr::eq(prepared.grade_receipt(), &roster.occurrences[0].resource));
    let [candidate] = prepared.candidates() else {
        panic!("the complete finite generator roster has exactly one candidate")
    };
    let expected = crate::rholang_ast::lower_rholang_proc(&Proc::PCostSignedTerm(
        Arc::new(Proc::PZero),
        Arc::new(CostSig::CostSigHash(Arc::new(Proc::PZero))),
    ))
    .expect("independent ordinary typed host lowering");
    assert_eq!(candidate.par(), &expected);
    assert_eq!(candidate.par().cost_signed_terms.len(), 1);
    let installed = table
        .authorize(&language.handle, LanguageRight::Bridge)
        .expect("live installed owner");
    let projected = installed.projected_image().expect("projected image");
    let binding = installed.funding_projection_v2().expect("checked selector");
    let SemanticResourceReceipt::Checked {
        grade,
        grade_sort,
        cost_image_fingerprint,
    } = prepared.grade_receipt()
    else {
        panic!("the guest rewrite retains its checked Cost(G) grade")
    };
    assert_eq!(Some(*cost_image_fingerprint), installed.commitment().cost_image_fingerprint);
    let receipt = candidate.projection_receipt();
    assert_eq!(receipt.input, *grade);
    assert_eq!(receipt.input_sort, *grade_sort);
    assert_eq!(receipt.projection, binding.projection);
    assert_eq!(receipt.direction, ProjectionDirectionV1::GuestToHost);
    assert_eq!(receipt.output_sort, binding.host_proc_sort);
    assert_eq!(receipt.source_occurrence, PROJECTION_OCCURRENCE);
    assert_eq!(receipt.base_image_fingerprint, roster.image_fingerprint);
    assert_eq!(receipt.projected_language_fingerprint, language.handle.fingerprint());
    assert_eq!(receipt.host_signature_fingerprint, projected.host_signature_fingerprint);
    assert_eq!(receipt.host_codec_profile_fingerprint, projected.host_codec_profile_fingerprint);
    assert_eq!(receipt.resource, SemanticResourceReceipt::NoSemanticGrade);
    assert!(receipt.rule.0 >= projected.base_rule_count);
    let repeated =
        prepare(&table, &language.handle, &roster).expect("repeat exact installed route");
    assert_eq!(repeated.candidates()[0].par(), candidate.par());
    assert_eq!(repeated.candidates()[0].projection_receipt(), receipt);
}

#[test]
fn funding_preparation_rejects_altered_base_roster_owners() {
    let (table, _host, language) = fixture();
    for field in 0..4 {
        let mut roster = guest_roster(&table, &language.handle);
        match field {
            0 => roster.language_fingerprint[0] ^= 1,
            1 => roster.theory_fingerprint[0] ^= 1,
            2 => roster.image_fingerprint[0] ^= 1,
            _ => roster.language_fingerprint = language.handle.fingerprint(),
        }
        assert!(matches!(
            prepare(&table, &language.handle, &roster),
            Err(InstalledSemanticError::InvalidEvidence(_))
        ));
    }
}

#[test]
fn funding_preparation_rejects_altered_cost_owner_sort_and_grade_key() {
    let (table, _host, language) = fixture();
    for field in 0..5 {
        let mut roster = guest_roster(&table, &language.handle);
        let SemanticResourceReceipt::Checked {
            grade,
            grade_sort,
            cost_image_fingerprint,
        } = &mut roster.occurrences[0].resource
        else {
            panic!("real checked source grade")
        };
        match field {
            0 => cost_image_fingerprint[0] ^= 1,
            1 => grade_sort.0 = grade_sort.0.wrapping_add(1),
            2 => grade[0] ^= 1,
            3 => roster.occurrences[0].resource = SemanticResourceReceipt::NoSemanticGrade,
            _ => {
                let trace = SemanticResourceReceipt::CheckedTraceV2 {
                    grade_sort: *grade_sort,
                    grade: grade.clone(),
                    cost_image_fingerprint: *cost_image_fingerprint,
                    entry_grade: grade.clone(),
                    hops: vec![],
                };
                roster.occurrences[0].resource = trace;
            },
        }
        assert!(
            matches!(
                prepare(&table, &language.handle, &roster),
                Err(InstalledSemanticError::InvalidEvidence(_))
                    | Err(InstalledSemanticError::Undetermined(
                        SemanticMatchUndetermined::InvalidImageEvidence
                            | SemanticMatchUndetermined::ResourceGradeUnavailable
                    ))
            ),
            "altered resource field {field} must refuse the complete preparation"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn funding_preparation_authenticates_every_base_owner_byte(
        field in 0usize..3,
        byte in 0usize..32,
        mask in 1u8..=u8::MAX,
    ) {
        let (table, _host, language) = fixture();
        let mut roster = guest_roster(&table, &language.handle);
        let owner = match field {
            0 => &mut roster.language_fingerprint,
            1 => &mut roster.theory_fingerprint,
            _ => &mut roster.image_fingerprint,
        };
        owner[byte] ^= mask;
        prop_assert!(matches!(
            prepare(&table, &language.handle, &roster),
            Err(InstalledSemanticError::InvalidEvidence(_))
        ));
    }

    #[test]
    fn funding_preparation_authenticates_grade_sort_and_cost_owner(
        change_sort in any::<bool>(),
        byte in 0usize..32,
        mask in 1u8..=u8::MAX,
        sort_delta in 1u32..=u32::MAX,
    ) {
        let (table, _host, language) = fixture();
        let mut roster = guest_roster(&table, &language.handle);
        let SemanticResourceReceipt::Checked { grade_sort, cost_image_fingerprint, .. } =
            &mut roster.occurrences[0].resource
        else {
            panic!("the production kernel returns a one-step checked grade")
        };
        if change_sort {
            grade_sort.0 = grade_sort.0.wrapping_add(sort_delta);
        } else {
            cost_image_fingerprint[byte] ^= mask;
        }
        prop_assert!(matches!(
            prepare(&table, &language.handle, &roster),
            Err(InstalledSemanticError::InvalidEvidence(_))
        ));
    }
}

#[test]
fn funding_preparation_requires_both_rights_and_the_original_registry() {
    let (table, _host, language) = fixture();
    let roster = guest_roster(&table, &language.handle);
    for (retained, missing) in [
        (LanguageRight::Reduce, LanguageRight::Bridge),
        (LanguageRight::Bridge, LanguageRight::Reduce),
    ] {
        let attenuated = language
            .handle
            .attenuate(&core::LanguageRights::from_rights([retained]));
        assert!(matches!(
            prepare(&table, &attenuated, &roster),
            Err(InstalledSemanticError::Access(LanguageAccessError::MissingRight(right)))
                if right == missing
        ));
    }
    assert!(matches!(
        prepare(&InstalledLanguageTable::new(), &language.handle, &roster),
        Err(InstalledSemanticError::Access(LanguageAccessError::WrongRegistry))
    ));
}

#[test]
fn funding_preparation_rejects_revoked_language_and_host_owners() {
    for revoke_host in [false, true] {
        let (table, host, language) = fixture();
        let roster = guest_roster(&table, &language.handle);
        let expected = if revoke_host {
            table
                .revoke_host_profile(host.revocation)
                .expect("revoke host codec");
            LanguageAccessError::HostProfileUnavailable
        } else {
            table
                .revoke(language.revocation)
                .expect("revoke guest language");
            LanguageAccessError::StaleHandle
        };
        assert!(matches!(
            prepare(&table, &language.handle, &roster),
            Err(InstalledSemanticError::Access(actual)) if actual == expected
        ));
    }
}

#[test]
fn funding_preparation_never_publishes_after_work_exhaustion_or_cancellation() {
    let (table, _host, language) = fixture();
    let roster = guest_roster(&table, &language.handle);
    for cancelled in [false, true] {
        let mut work = 0;
        let mut cancel = || cancelled;
        let limit = if cancelled { WORK_LIMIT } else { 0 };
        let mut budget = ReflectedCodecBudget::new(&mut work, limit, PAYLOAD_LIMIT, &mut cancel);
        let result = prepare_checked_host_demand_v2(
            &table,
            &language.handle,
            &roster,
            0,
            execution_limits(),
            &mut budget,
        );
        let expected = if cancelled {
            DynamicReflectionError::Cancelled
        } else {
            DynamicReflectionError::WorkLimit
        };
        assert!(
            matches!(result, Err(InstalledSemanticError::Resource(actual)) if actual == expected)
        );
    }
}

#[test]
fn funding_installation_rejects_wrong_selector_and_proof_commitments() {
    for field in 0..5 {
        let (table, _host, mut request) = installation_request();
        match field {
            0 => request.selector.projection_name = "absent".into(),
            1 => request.selector.guest_grade_sort = "Expr".into(),
            2 => request.selector.resource_logic_abi.push_str("-wrong"),
            3 => request.selector.bound_verifier_abi.push_str("-wrong"),
            _ => request.selector.projection_proof_commitment[0] ^= 1,
        }
        assert!(matches!(
            install(&table, request),
            Err(core::InstallLanguageError::InvalidProjection(_))
        ));
        assert_eq!(table.installed_count().expect("atomic installation count"), 0);
    }
}

#[test]
fn finite_checker_refuses_duplicate_generators_and_uncertified_host_templates() {
    for duplicate in [false, true] {
        let (table, _host, mut request) = installation_request();
        let core::ProjectionBodyV1::Rules(rows) = &mut request.projected.projections[0].body else {
            panic!("the selected relation uses source rules")
        };
        let expected = if duplicate {
            let mut second = rows[0].clone();
            second.source_occurrence += 1;
            second.rule.name.push_str("-duplicate");
            rows.push(second);
            "DuplicateGenerator"
        } else {
            rows[0].rule.right = core::TheoryTermId(1);
            "funding selector proof or host implementation mismatch"
        };
        assert!(matches!(
            install(&table, request),
            Err(core::InstallLanguageError::InvalidProjection(message)) if message.contains(expected)
        ));
        assert_eq!(table.installed_count().expect("atomic installation count"), 0);
    }
}
