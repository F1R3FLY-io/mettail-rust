use super::*;
use crate::language_install::{exact_list, wire_list};
use crate::semantic_wire::{decode_receipt_v1, decode_u64, decode_usage_v1, encode_limits_v1};
use mettail_grammar_core::RuntimeTemplatePiece;
use models::rust::utils::{new_gint_par, new_gstring_par, new_send_par};
use std::collections::BTreeMap;

fn input(runtime: &RholangLanguageRuntime, token: &Par, text: &str) -> Par {
    runtime
        .construct_template(
            token,
            &[RuntimeTemplatePiece::Text(text.into())],
            &[],
            Some("Pattern"),
            &BTreeMap::new(),
        )
        .unwrap()
}

fn request(token: &Par, input: &Par, name: &str, limits: SemanticServiceLimits) -> Vec<Par> {
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 1000, &mut cancel);
    vec![wire_list(vec![
        new_gint_par(1, Vec::new(), false),
        token.clone(),
        new_gstring_par(name.into(), Vec::new(), false),
        input.clone(),
        encode_limits_v1(limits, &mut budget).unwrap(),
        new_gstring_par("OUT".into(), Vec::new(), false),
    ])]
}

fn envelope(reply: &PreparedWireReply) -> (u64, &Par, SemanticWireUsage) {
    assert_eq!(reply.payload.len(), 1);
    let fields = exact_list(&reply.payload[0]).unwrap();
    assert_eq!(fields.len(), 4);
    let mut work = 0;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
    assert_eq!(decode_u64(&fields[0], &mut budget), Ok(1));
    (
        decode_u64(&fields[1], &mut budget).unwrap(),
        &fields[2],
        decode_usage_v1(&fields[3], &mut budget).unwrap(),
    )
}

#[test]
fn semantic_service_wire_composes_exact_prefix_execution_and_receipts() {
    let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
    let input = input(&runtime, &token, "a+");
    let limits = SemanticServiceLimits::default();
    let direct = runtime.execute_semantic(
        SemanticServiceRequest {
            handle: &token,
            operation: SemanticOperation::Reduce("expand-plus"),
            input: &input,
            limits,
        },
        || false,
    );
    let direct_remaining = direct.remaining_boundary_payload_bytes;
    let mut expected_work = direct.work;
    let mut cancel = || false;
    let mut budget = ReflectedCodecBudget::new(
        &mut expected_work,
        limits.execution.work,
        direct_remaining,
        &mut cancel,
    );
    let expected_body = encode_results_v1(direct.outcome.unwrap(), &mut budget).unwrap();
    let expected_remaining = budget.finish();
    let mut header_work = 0;
    let mut header = ReflectedCodecBudget::new(
        &mut header_work,
        limits.execution.work,
        limits.boundary_payload_bytes,
        &mut cancel,
    );
    OwnedSemanticRequest::decode(request(&token, &input, "expand-plus", limits), &mut header)
        .unwrap();
    header.finish();
    for (endpoint, name) in [(Endpoint::Reduce, "expand-plus"), (Endpoint::Observe, "ExpandedPlus")]
    {
        let reply =
            prepare_reply(&runtime, endpoint, request(&token, &input, name, limits), || false)
                .unwrap();
        let (status, body, usage) = envelope(&reply);
        assert_eq!(status, 0);
        assert_eq!(body, &expected_body);
        assert_eq!(usage.kernel_work, direct.kernel_work);
        assert_eq!(usage.effective_limits, direct.effective_limits);
        if matches!(endpoint, Endpoint::Reduce) {
            assert_eq!(usage.work, expected_work + header_work + 154);
            assert_eq!(usage.remaining_boundary_payload_bytes, expected_remaining - 782);
        }
        assert_eq!(reply.channel, new_gstring_par("OUT".into(), Vec::new(), false));
        let mut committed = false;
        reply
            .publication
            .with_commit(Box::new(|| committed = true))
            .unwrap();
        assert!(committed);
        for pair in exact_list(body).unwrap() {
            let pair = exact_list(pair).unwrap();
            let mut work = 0;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
            assert_eq!(decode_receipt_v1(&pair[1], &mut budget).unwrap().action.0, 0);
        }
    }
}

#[test]
fn semantic_service_wire_exact_and_one_less_total_allowances() {
    let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
    let input = input(&runtime, &token, "a+");
    let limits = SemanticServiceLimits::default();
    let baseline = prepare_reply(
        &runtime,
        Endpoint::Reduce,
        request(&token, &input, "expand-plus", limits),
        || false,
    )
    .unwrap();
    let (status, _, usage) = envelope(&baseline);
    assert_eq!(status, 0);
    let spent = usage.effective_limits.unwrap().boundary_payload_bytes
        - usage.remaining_boundary_payload_bytes;
    for (work, bytes, expected) in
        [(usage.work, spent, 0), (usage.work - 1, spent, 2), (usage.work, spent - 1, 2)]
    {
        let limits = SemanticServiceLimits {
            execution: SemanticTransitionLimits { work, ..limits.execution },
            boundary_payload_bytes: bytes,
        };
        let reply = prepare_reply(
            &runtime,
            Endpoint::Reduce,
            request(&token, &input, "expand-plus", limits),
            || false,
        )
        .unwrap();
        let (status, body, usage) = envelope(&reply);
        assert_eq!(status, expected);
        assert!(usage.work <= work);
        assert!(usage.remaining_boundary_payload_bytes <= bytes);
        if expected == 2 {
            assert_eq!(exact_list(body).unwrap().len(), 2);
        }
    }
}

#[test]
fn semantic_service_wire_refutations_and_cancellation_never_fabricate_success() {
    let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
    let literal = input(&runtime, &token, "a");
    let limits = SemanticServiceLimits::default();
    let reply = prepare_reply(
        &runtime,
        Endpoint::Reduce,
        request(&token, &literal, "expand-plus", limits),
        || false,
    )
    .unwrap();
    assert_eq!(envelope(&reply).0, 1);
    let input = input(&runtime, &token, "a+");
    let mut count = 0;
    let baseline = prepare_reply(
        &runtime,
        Endpoint::Reduce,
        request(&token, &input, "expand-plus", limits),
        || {
            count += 1;
            false
        },
    )
    .unwrap();
    assert_eq!(envelope(&baseline).0, 0);
    for stop in [1, 5, 50, count / 2, count - 1, count] {
        let mut seen = 0;
        let result = prepare_reply(
            &runtime,
            Endpoint::Reduce,
            request(&token, &input, "expand-plus", limits),
            || {
                seen += 1;
                seen == stop
            },
        );
        if let Ok(reply) = result {
            assert_eq!(envelope(&reply).0, 2);
        }
    }
    runtime.revoke(&token).unwrap();
    let mut commits = 0;
    assert!(reply
        .publication
        .with_commit(Box::new(|| commits += 1))
        .is_err());
    assert!(baseline
        .publication
        .with_commit(Box::new(|| commits += 1))
        .is_err());
    assert_eq!(commits, 0);
    assert!(prepare_reply(
        &runtime,
        Endpoint::Reduce,
        request(&token, &input, "expand-plus", limits),
        || false
    )
    .is_err());
}

#[test]
fn semantic_service_wire_missing_context_has_no_publishable_reply() {
    let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
    let input = input(&runtime, &token, "a+");
    let limits = SemanticServiceLimits::default();
    for (endpoint, handle, name) in [
        (Endpoint::Reduce, &token, "unknown"),
        (Endpoint::Observe, &token, "expand-plus"),
        (Endpoint::Reduce, &Par::default(), "expand-plus"),
    ] {
        assert!(
            prepare_reply(&runtime, endpoint, request(handle, &input, name, limits), || false)
                .is_err()
        );
    }
    assert!(prepare_reply(&runtime, Endpoint::Reduce, vec![], || false).is_err());
}

#[tokio::test]
async fn semantic_service_wire_definitions_execute_on_the_existing_runtime() {
    let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
    let input = input(&runtime, &token, "a+");
    let runtime = Arc::new(runtime);
    for (endpoint, name) in [(Endpoint::Reduce, "expand-plus"), (Endpoint::Observe, "ExpandedPlus")]
    {
        let channel = LANGUAGE_SEMANTIC_BAND.channel(endpoint.index(), LANGUAGE_SEMANTIC_ABI_V1);
        let send = new_send_par(
            channel,
            request(&token, &input, name, SemanticServiceLimits::default()),
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &send,
            crate::language_install::language_runtime_definitions(Arc::clone(&runtime)),
            &["OUT"],
        )
        .await
        .unwrap();
        let result = outputs.get("OUT").unwrap();
        assert_eq!(result.len(), 1);
        let fields = exact_list(&result[0]).unwrap();
        assert_eq!(fields[0], new_gint_par(1, Vec::new(), false));
        assert_eq!(fields[1], new_gint_par(0, Vec::new(), false));
        assert_eq!(exact_list(&fields[2]).unwrap().len(), 1);
    }
}

#[tokio::test]
async fn semantic_service_wire_inline_module_qualified_flt_and_matched_reply() {
    use crate::language_install::{
        tests::MemoryRegistry, LanguageInstallPolicy, LanguageInstallService,
    };
    use mettail_languages::rholang::Proc;

    let mut commitments = Vec::new();
    for (urn, name, changed, expected_label) in [
        (LANGUAGE_SEMANTIC_REDUCE_URN, "expand-plus", false, "PConcat"),
        (LANGUAGE_SEMANTIC_OBSERVE_URN, "ExpandedPlus", false, "PConcat"),
        (LANGUAGE_SEMANTIC_REDUCE_URN, "expand-plus", true, "PAlt"),
    ] {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::clone(&service)));
        let original = include_str!("../../../tests/fixtures/regex_extension.rho");
        let original_rule = "ExpandPlus : (PPlus P) ~> (PConcat P (PStar P));";
        assert_eq!(original.matches(original_rule).count(), 1);
        // Two different application specifications, each parsed once by the
        // host entrypoint; this is not runtime source rewriting or reparsing.
        let module = if changed {
            original.replace(original_rule, "ExpandPlus : (PPlus P) ~> (PAlt P (PStar P));")
        } else {
            original.to_owned()
        };
        let source = format!(
            r#"
            new install(`rho:mettail:install`), semantic(`{urn}`) in {{
              new loaded, handlePipe, result in {{
                install!({module}, *loaded) |
                for(@installed <- loaded) {{
                  handlePipe!(installed.get("ok").get("exports").nth(0).get("handle"))
                }} |
                for(language <- handlePipe) {{
                  semantic!([1, *language, "{name}", language:Pattern`a+`,
                    [10000000,100000,10000,10000,10000,100000,100000,10000000,100000,10000000,16777216],
                    *result]) |
                  for(@[1, 0, [[term, receipt]], usage] <- result) {{
                    @"OUT"!([term, receipt, usage])
                  }}
                }}
              }}
            }}
        "#
        );
        let proc =
            Proc::parse_via_wpda(&source).expect("one generated host parse including the DDL");
        let program = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("structural DDL and qualified FLT lowering");
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &program,
            crate::language_install::language_runtime_definitions(runtime),
            &["OUT"],
        )
        .await
        .expect("real installed semantic endpoint and waiting receiver execute");
        assert_eq!(service.installed_count().unwrap(), 1);
        let outputs = outputs.get("OUT").unwrap();
        assert_eq!(outputs.len(), 1);
        let fields = exact_list(&outputs[0]).unwrap();
        assert_eq!(fields.len(), 3);
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let receipt = decode_receipt_v1(&fields[1], &mut budget).unwrap();
        assert_eq!(receipt.action.0, 0);
        assert_ne!(receipt.input, receipt.output);
        let usage = decode_usage_v1(&fields[2], &mut budget).unwrap();
        assert!(usage.kernel_work.is_some());
        assert!(usage.work >= usage.kernel_work.unwrap());
        let owner =
            crate::language_install::grammar_fingerprint_label(receipt.language_fingerprint);
        let context =
            mettail_rholang_codegen::ReflectedPositionalContext::new(&owner, &mut budget).unwrap();
        assert_eq!(
            context
                .view(&fields[0], &mut budget)
                .unwrap()
                .unwrap()
                .label(),
            expected_label
        );
        commitments.push((
            receipt.language_fingerprint,
            receipt.theory_fingerprint,
            receipt.image_fingerprint,
            receipt.output,
        ));
    }
    assert_eq!(commitments[0], commitments[1], "observe selects the declared action");
    assert_ne!(
        commitments[0].0, commitments[2].0,
        "full language commitment includes the changed theory"
    );
    assert_ne!(commitments[0].1, commitments[2].1, "theory commitment changes");
    assert_ne!(commitments[0].2, commitments[2].2, "semantic image changes");
    assert_ne!(commitments[0].3, commitments[2].3, "actual kernel output changes");
}
