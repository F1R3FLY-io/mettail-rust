//! AST-first Cost(Rho) wire retention. These tests never invoke the legacy parser.

use mettail_languages::rholang::Proc;
use mettail_rholang_runtime::{lower_rholang_proc, RholangAstLowerError};
use models::rhoapi::cost_signature::Value as CostValue;
use models::rust::rholang::sorter::par_sort_matcher::ParSortMatcher;
use models::rust::rholang::sorter::sortable::Sortable;
use models::rust::utils::new_gstring_par;
use proptest::prelude::*;
use prost::Message;

fn lower(source: &str) -> Result<models::rhoapi::Par, RholangAstLowerError> {
    let proc = Proc::parse_via_wpda(source).expect("MeTTaIL Cost(Rho) parse");
    lower_rholang_proc(&proc)
}

#[test]
fn signed_nil_preserves_exact_ground_principal_bytes() {
    let rho = lower("{% Nil %}[alice]").expect("signed term lowers");
    assert_eq!(rho.cost_signed_terms.len(), 1);
    let signed = &rho.cost_signed_terms[0];
    assert_eq!(signed.body.as_ref().expect("signed body").sends.len(), 0);
    let expected =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        signed.signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected.as_slice()
    ));
}

#[test]
fn quoted_name_principal_is_distinct_from_hash_signature() {
    let rho = lower("{% Nil %}[@Nil]").expect("quoted name principal lowers");
    let signature = rho.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("signature");
    assert!(matches!(signature.value.as_ref(), Some(CostValue::Name(_))));
    let hashed = lower("{% Nil %}[#(Nil)]").expect("hash signature lowers");
    let signature = hashed.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("hash signature");
    assert!(matches!(signature.value.as_ref(), Some(CostValue::Quote(_))));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    #[test]
    fn quoted_name_and_hash_section_retain_distinct_wire_tags_for_the_same_process(
        value in 0u8..32,
    ) {
        let name = lower(&format!("{{% Nil %}}[@({value})]"))
            .expect("quoted Name ground signature lowers");
        let section = lower(&format!("{{% Nil %}}[#({value})]"))
            .expect("cryptographic section lowers");
        let name_signature = name.cost_signed_terms[0].signature.as_ref().expect("name signature");
        let section_signature = section.cost_signed_terms[0].signature.as_ref().expect("section signature");
        match (name_signature.value.as_ref(), section_signature.value.as_ref()) {
            (Some(CostValue::Name(name_process)), Some(CostValue::Quote(section_process))) => {
                prop_assert_eq!(name_process.encode_to_vec(), section_process.encode_to_vec());
                prop_assert_ne!(name_signature.encode_to_vec(), section_signature.encode_to_vec());
            }
            other => prop_assert!(false, "distinct Name/Quote wire tags required: {other:?}"),
        }
    }
}

#[test]
fn bare_stack_is_inert_evidence_not_a_mint() {
    let rho = lower("alice :: ()").expect("nonempty stack lowers");
    assert!(rho.sends.is_empty(), "source stack syntax cannot mint supply");
    assert_eq!(rho.cost_stacks.len(), 1);
    assert_eq!(rho.cost_stacks[0].cells.len(), 1);
    assert!(matches!(
        lower("(alice -o bob) :: ()"),
        Err(RholangAstLowerError::UnfundableCostSignature)
    ));
}

#[test]
fn parallel_stack_tail_retains_one_shared_prefix() {
    let rho = lower("alice :: (bob :: () | carol :: ())")
        .expect("parallel stack tail lowers without copying its prefix");
    assert!(rho.sends.is_empty(), "source stack syntax cannot mint supply");
    assert_eq!(rho.cost_stacks.len(), 1);
    let stack = &rho.cost_stacks[0];
    assert_eq!(stack.cells.len(), 1);
    assert_eq!(stack.parallel_tail.len(), 2);
    assert_eq!(stack.parallel_tail[0].cells.len(), 1);
    assert_eq!(stack.parallel_tail[1].cells.len(), 1);
    assert!(stack
        .parallel_tail
        .iter()
        .all(|branch| branch.parallel_tail.is_empty()));
}

#[test]
fn unit_is_not_lowered_as_nil() {
    let unit = lower("()").expect("unit lowers as host tuple");
    let nil = lower("Nil").expect("nil lowers as empty process");
    assert_eq!(unit.encode_to_vec(), [0x2a, 3, 0xaa, 1, 0]);
    assert!(nil.encode_to_vec().is_empty());
    assert_ne!(unit, nil);
}

#[test]
fn authority_rewrites_without_a_checked_plan_fail_closed() {
    assert!(matches!(
        lower("{% Nil %}[alice -o bob]"),
        Err(RholangAstLowerError::UnfundableCostSignature)
    ));
    assert!(matches!(
        lower("for({% value <- @\"c\" %}[alice]){% Nil %}"),
        Err(RholangAstLowerError::CostPlanUnavailable(_))
    ));
}

#[test]
fn signed_receive_bind_retains_its_wire_signature() {
    let rho = lower("for({% value <- channel %}[alice]){ Nil }")
        .expect("signed bind lowers through the receive worklist");
    assert_eq!(rho.receives.len(), 1);
    let bind = &rho.receives[0].binds[0];
    let expected =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        bind.cost_signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected.as_slice()
    ));
}

#[test]
fn signed_receive_empty_bind_retains_its_wire_signature() {
    let rho = lower("for({% <- channel %}[alice]){ Nil }")
        .expect("signed empty bind lowers through the receive worklist");
    assert_eq!(rho.receives.len(), 1);
    let bind = &rho.receives[0].binds[0];
    assert!(bind.patterns.is_empty());
    assert!(bind.cost_signature.is_some());
}

#[test]
fn lollipop_signed_receive_keeps_both_authority_slots() {
    let rho = lower("{% for(value <- channel){ Nil } %}[alice -o bob]")
        .expect("lollipop receive lowers without a recursive parser fallback");
    assert_eq!(rho.cost_signed_terms.len(), 1);
    let outer = &rho.cost_signed_terms[0];
    let expected_alice =
        ParSortMatcher::sort_match(&new_gstring_par("alice".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        outer.signature.as_ref().and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected_alice.as_slice()
    ));
    let receive = &outer.body.as_ref().expect("outer body").receives[0];
    let continuation = receive.body.as_ref().expect("receive continuation");
    assert_eq!(continuation.cost_signed_terms.len(), 1);
    let expected_bob =
        ParSortMatcher::sort_match(&new_gstring_par("bob".to_owned(), Vec::new(), false))
            .term
            .encode_to_vec();
    assert!(matches!(
        continuation.cost_signed_terms[0]
            .signature
            .as_ref()
            .and_then(|sig| sig.value.as_ref()),
        Some(CostValue::Ground(bytes)) if bytes.as_slice() == expected_bob.as_slice()
    ));
}

#[test]
fn quote_signature_keeps_enclosing_new_binding() {
    let rho = lower("new x in {{% Nil %}[#x]}").expect("bound quote signature lowers");
    let inner = rho.news[0].p.as_ref().expect("new body");
    let signature = inner.cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("signature");
    let Some(CostValue::Quote(quoted)) = signature.value.as_ref() else {
        panic!("#x must lower as a quote signature")
    };
    assert!(
        quoted.locally_free.iter().any(|bit| *bit != 0),
        "the quoted principal must retain the enclosing bound variable"
    );
}

fn assert_ground_signature(signature: Option<&models::rhoapi::CostSignature>, name: &str) {
    let expected = ParSortMatcher::sort_match(&new_gstring_par(name.to_owned(), Vec::new(), false))
        .term
        .encode_to_vec();
    assert_eq!(
        signature.and_then(|signature| signature.value.as_ref()),
        Some(&CostValue::Ground(expected)),
        "expected the exact ground principal {name}",
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]

    #[test]
    fn signed_semicolon_rows_keep_only_outer_and_authored_final_wrappers(
        row_count in 2usize..=8,
        transfer in any::<bool>(),
        explicit_final in any::<bool>(),
    ) {
        let rows = (0..row_count)
            .map(|index| format!("value{index} <- @\"channel{index}\""))
            .collect::<Vec<_>>()
            .join("; ");
        let body = if explicit_final { "{% Nil %}[carol]" } else { "Nil" };
        let annotation = if transfer { "alice -o bob" } else { "alice" };
        let source = format!("{{% for({rows}){{ {body} }} %}}[{annotation}]");
        let rho = lower(&source).expect("signed semicolon rows lower");
        prop_assert_eq!(rho.cost_signed_terms.len(), 1);
        let outer = &rho.cost_signed_terms[0];
        assert_ground_signature(outer.signature.as_ref(), "alice");
        let mut current = outer.body.as_ref().expect("outer signed body");
        for _ in 0..row_count {
            prop_assert!(current.cost_signed_terms.is_empty(),
                "nesting an authored row must not add another signature wrapper");
            prop_assert_eq!(current.receives.len(), 1);
            prop_assert_eq!(current.receives[0].binds.len(), 1);
            current = current.receives[0].body.as_ref().expect("row continuation");
        }
        prop_assert_eq!(current.cost_signed_terms.len(), 1);
        let final_signature = if transfer { "bob" } else if explicit_final { "carol" } else { "alice" };
        let final_signed = &current.cost_signed_terms[0];
        let final_body = final_signed.body.as_ref().expect("authored final body");
        if transfer && explicit_final {
            let Some(CostValue::Compound(compound)) = final_signed.signature.as_ref()
                .and_then(|signature| signature.value.as_ref()) else {
                    return Err(TestCaseError::fail("nested authority must retain both principals in its canonical compound"));
                };
            prop_assert_eq!(compound.elements.len(), 2);
            assert_ground_signature(compound.elements.first(), "bob");
            assert_ground_signature(compound.elements.get(1), "carol");
        } else {
            assert_ground_signature(final_signed.signature.as_ref(), final_signature);
        }
        prop_assert!(final_body.cost_signed_terms.is_empty());
    }
}

#[test]
fn explicitly_nested_for_retains_its_own_uniform_signature() {
    let rho = lower("{% for(first <- @\"first\"){ for(second <- @\"second\"){ Nil } } %}[alice]")
        .expect("an authored nested receive is uniformly signed at its own boundary");
    let outer = &rho.cost_signed_terms[0];
    assert_ground_signature(outer.signature.as_ref(), "alice");
    let first = &outer.body.as_ref().unwrap().receives[0];
    let nested = &first.body.as_ref().unwrap().cost_signed_terms[0];
    assert_ground_signature(nested.signature.as_ref(), "alice");
    let second = &nested.body.as_ref().unwrap().receives[0];
    let final_signed = &second.body.as_ref().unwrap().cost_signed_terms[0];
    assert_ground_signature(final_signed.signature.as_ref(), "alice");
}

mod source_bound_native {
    use std::collections::{BTreeMap, HashMap};
    use std::sync::Arc;

    use crypto::rust::hash::blake2b512_random::Blake2b512Random;
    use mettail_rholang_runtime::rholang_ast::{RholangPreparationPolicy, RholangProgramFrontend};
    use mettail_rholang_runtime::{EmptyFltResolver, LoweringOptions};
    use models::rhoapi::{BindPattern, ListParWithRandom, Par, TaggedContinuation};
    use models::rust::phlo_schedule::{PhloGenesisPolicy, PhloScheduleV1};
    use models::rust::utils::{new_gint_par, new_gstring_par};
    use rholang::rust::interpreter::accounting::authority::{
        authority_demand, cost_signature_to_sig, AuthorityByteEventKind,
    };
    use rholang::rust::interpreter::accounting::native_phlo_rules::{
        native_resource_compatibility_rule, NativeBoundSource, NativeBudgetTraceLimits,
        NativePhloDimension, NativePhloExecutionContract, NativePhloRegionLimits,
    };
    use rholang::rust::interpreter::accounting::phlo_controls::{
        check_phlo_controls, PhloScheduleBinding, SignedPhloControls,
    };
    use rholang::rust::interpreter::accounting::{NativeRuntimeConfig, Sig};
    use rholang::rust::interpreter::external_services::ExternalServices;
    use rholang::rust::interpreter::frontend::{prepare_program, PreparedProgram};
    use rholang::rust::interpreter::interpreter::EvaluateResult;
    use rholang::rust::interpreter::matcher::r#match::Matcher;
    use rholang::rust::interpreter::merging::mergeable_tags::default_mergeable_tags;
    use rholang::rust::interpreter::rho_runtime::{
        create_replay_rho_runtime, create_rho_runtime, RhoRuntime,
    };
    use rspace_plus_plus::rspace::hashing::stable_hash_provider::EventCodecEpoch;
    use rspace_plus_plus::rspace::rspace::RSpace;
    use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
    use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

    fn prepare(source: &str) -> PreparedProgram {
        let frontend = RholangProgramFrontend::new(
            RholangPreparationPolicy {
                max_source_bytes: 16_384,
                max_import_entries: 16,
                max_import_nodes: 4096,
                max_import_payload_bytes: 65_536,
                lowering: LoweringOptions::NO_DISCHARGE,
            },
            Arc::new(EmptyFltResolver),
        );
        let prepared = prepare_program(&frontend, source, HashMap::new()).expect("checked source");
        assert_eq!(prepared.source_binding().expect("source receipt").0, source.as_bytes());
        prepared
    }

    fn config() -> NativeRuntimeConfig {
        let descriptor = PhloScheduleV1 {
            protocol_version: 6,
            network: b"native-test",
            shard: b"root",
            settlement_asset: b"REV",
            settlement_unit: b"atomic-REV",
            decimal_scale: 8,
            classes: NativePhloDimension::ALL
                .into_iter()
                .zip([2, 3, 5, 7])
                .zip([b"c".as_slice(), b"i", b"t", b"r"])
                .map(|((dimension, weight), name)| dimension.resource_class(name, weight))
                .collect(),
            actual_price: 2,
            compatibility_rule: native_resource_compatibility_rule(),
        };
        let binding = PhloScheduleBinding::new(&descriptor, PhloGenesisPolicy::LIMITS)
            .expect("native schedule");
        let selected = binding.schedule();
        let schedules = [selected];
        let owner_ceilings = [2];
        let controls = check_phlo_controls(
            selected.environment,
            0,
            u64::MAX,
            SignedPhloControls {
                limit: 1_000_000,
                price_ceiling: 2,
                required_owner_ceilings: &owner_ceilings,
                permitted_schedules: &schedules,
            },
            selected,
            1_000_000,
        )
        .expect("checked native controls");
        let contract =
            NativePhloExecutionContract::new(controls, &binding, NativeBoundSource::Certificate)
                .expect("checked native execution contract");
        NativeRuntimeConfig::new(
            contract,
            NativeBudgetTraceLimits {
                attempts: 100_000,
                path_segments: 4096,
                regions: NativePhloRegionLimits {
                    regions: 1000,
                    encoded_authority_bytes: 10_000_000,
                },
            },
        )
        .with_event_codec_epoch(EventCodecEpoch::CostV1)
    }

    fn assert_same_economic_trace(expected: &EvaluateResult, actual: &EvaluateResult) {
        assert!(actual.errors.is_empty(), "{:?}", actual.errors);
        assert_eq!(actual.native_phlo_usage, expected.native_phlo_usage);
        assert_eq!(actual.byte_observations, expected.byte_observations);
        let expected = expected
            .native_budget_recording
            .as_ref()
            .expect("expected budget trace");
        let actual = actual
            .native_budget_recording
            .as_ref()
            .expect("actual budget trace");
        assert_eq!(actual.session, expected.session);
        assert_eq!(actual.used, expected.used);
        let keyed = |recording: &rholang::rust::interpreter::accounting::NativeBudgetRecording| {
            let mut keyed = BTreeMap::new();
            for row in recording.attempts.iter() {
                let path = recording
                    .paths
                    .suffix(row.occurrence.path, 0)
                    .expect("recorded causal path");
                keyed
                    .entry((row.occurrence.session, path, row.occurrence.stage))
                    .or_insert_with(Vec::new)
                    .push((row.observation.clone(), row.granted));
            }
            keyed
        };
        assert_eq!(keyed(actual), keyed(expected));
    }

    #[tokio::test]
    async fn checked_signed_query_executes_and_replays_the_explicit_native_trace() {
        const SEED: &[u8] = b"source-bound-signed-query";
        for (annotation, final_signature) in [("alice", "alice"), ("alice -o bob", "bob")] {
            let source = format!(
                r#"new svc in {{
                {{% for(ret, @value <- svc) {{ ret!(value) }} %}}[alice] |
                {{% for(@answer <- svc!?(7)) {{% @"signed-query-result"!(answer) %}} %}}[{annotation}]
            }}"#
            );
            let expanded = format!(
                r#"new svc in {{
                {{% for(ret, @value <- svc) {{ ret!(value) }} %}}[alice] |
                {{% new reply in {{ svc!(*reply, 7) | for(@answer <- reply) {{
                    {{% @"signed-query-result"!(answer) %}}[{final_signature}]
                }} }} %}}[alice]
            }}"#
            );
            let mut manager = InMemoryStoreManager::new();
            let stores = manager.r_space_stores().await.expect("runtime stores");
            let (space, replay_space) = RSpace::<
                Par,
                BindPattern,
                ListParWithRandom,
                TaggedContinuation,
            >::create_with_replay_for_epoch(
                EventCodecEpoch::CostV1,
                stores,
                Arc::new(Box::new(Matcher)),
            )
            .expect("cost-bearing play and replay spaces");
            let tags = Arc::new(default_mergeable_tags());
            let mut play = create_rho_runtime(
                space,
                Arc::clone(&tags),
                false,
                &mut Vec::new(),
                ExternalServices::noop(),
            )
            .await
            .expect("cost-bearing live runtime");
            let mut replay = create_replay_rho_runtime(
                replay_space,
                tags,
                false,
                &mut Vec::new(),
                ExternalServices::noop(),
            )
            .await
            .expect("cost-bearing replay runtime");
            assert_eq!(play.reducer.space.codec_epoch(), EventCodecEpoch::CostV1);
            assert_eq!(replay.reducer.space.codec_epoch(), EventCodecEpoch::CostV1);
            for runtime in [&play, &replay] {
                runtime
                    .cost
                    .set_deploy_signature_funded(SEED, Sig::Ground(vec![7]));
            }
            let initial_root = play.get_root().await;
            let result = play
                .evaluate_prepared_with_native_phlo(
                    prepare(&source),
                    Blake2b512Random::create_from_bytes(SEED),
                    None,
                    config(),
                )
                .await
                .expect("native signed query evaluation");
            assert!(result.errors.is_empty(), "{:?}", result.errors);
            assert!(result.native_phlo_usage.is_some_and(|usage| usage > 0));
            assert!(result.byte_observations.has_complete_measurements());
            assert!(result
                .byte_observations
                .rows
                .iter()
                .any(|row| row.kind == AuthorityByteEventKind::Comm));
            let output = new_gstring_par("signed-query-result".to_owned(), Vec::new(), false);
            let values = play.get_data(&output).await.expect("native query result");
            assert_eq!(values.len(), 1);
            assert_eq!(values[0].a.pars, vec![new_gint_par(7, Vec::new(), false)]);
            let expected_principal = super::lower(&format!("{{% Nil %}}[{final_signature}]"))
                .expect("continuation principal");
            let principal = cost_signature_to_sig(
                expected_principal.cost_signed_terms[0]
                    .signature
                    .as_ref()
                    .unwrap(),
            )
            .expect("canonical principal")
            .lane_hash();
            let authority = values[0]
                .a
                .cost_authority
                .as_ref()
                .expect("output authority");
            let demand = authority_demand(authority).expect("output authority demand");
            assert_eq!(demand.get(&principal), 1);
            assert_eq!(
                demand.0.len(),
                1,
                "communication authority must not survive into the signed continuation"
            );

            let checkpoint = play.create_checkpoint().await;
            replay
                .reset(&initial_root)
                .await
                .expect("replay initial state");
            replay.rig(checkpoint.log).await.expect("recorded COMM log");
            let replayed = replay
                .evaluate_prepared_with_native_phlo(
                    prepare(&source),
                    Blake2b512Random::create_from_bytes(SEED),
                    None,
                    config(),
                )
                .await
                .expect("native signed query replay");
            replay
                .check_replay_data()
                .await
                .expect("replay log consumed exactly");
            assert_same_economic_trace(&result, &replayed);
            assert_eq!(replay.create_checkpoint().await.root, checkpoint.root);

            play.reset(&initial_root)
                .await
                .expect("explicit expansion initial state");
            let explicit = play
                .evaluate_prepared_with_native_phlo(
                    prepare(&expanded),
                    Blake2b512Random::create_from_bytes(SEED),
                    None,
                    config(),
                )
                .await
                .expect("explicit native query evaluation");
            assert_same_economic_trace(&result, &explicit);
            assert_eq!(play.create_checkpoint().await.root, checkpoint.root);
            let explicit_values = play.get_data(&output).await.expect("explicit query result");
            assert_eq!(explicit_values, values);
        }
    }
}
