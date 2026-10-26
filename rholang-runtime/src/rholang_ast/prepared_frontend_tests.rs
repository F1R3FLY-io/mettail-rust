use super::*;
use mettail_runtime::Scope;
use models::rhoapi::cost_signature::Value as CostSignatureValue;
use prost::Message;
use rholang::rust::interpreter::frontend::prepare_program;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::{AtomicBool, Ordering};

fn policy() -> RholangPreparationPolicy {
    RholangPreparationPolicy {
        max_source_bytes: 16_384,
        max_import_entries: 16,
        max_import_nodes: 4096,
        max_import_payload_bytes: 65_536,
        // Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
        // max_preparation_work: 1_000_000,
        // max_preparation_units: 1_000_000,
        lowering: LoweringOptions::NO_DISCHARGE,
    }
}

fn frontend(policy: RholangPreparationPolicy) -> RholangProgramFrontend {
    RholangProgramFrontend::new(policy, Arc::new(EmptyFltResolver))
}

fn error<T>(result: Result<T, PreparationError>) -> String {
    result
        .err()
        .expect("request must refuse without a program")
        .to_string()
}

#[test]
fn frontend_is_thread_safe_and_implements_existing_node_abi() {
    fn assert_thread_safe<T: Send + Sync>() {}
    assert_thread_safe::<RholangProgramFrontend>();
    assert_eq!(frontend(policy()).abi_version(), PREPARED_PROGRAM_ABI_V1);
}

#[test]
fn actual_source_parses_then_borrows_and_moves_existing_node_program() {
    let adapter = frontend(policy());
    let prepared = prepare_program(&adapter, "Nil", HashMap::new()).expect("public Nil");
    let borrowed = prepared.as_par().encode_to_vec();
    assert_eq!(prepared.abi_version(), PREPARED_PROGRAM_ABI_V1);
    assert_eq!(borrowed, Par::default().encode_to_vec());
    assert_eq!(prepared.into_par().encode_to_vec(), borrowed);
}

#[test]
fn checked_public_frontend_keeps_quoted_name_distinct_from_hash_section() {
    let adapter = frontend(policy());
    let name = adapter
        .prepare("{% Nil %}[@Nil]", HashMap::new())
        .expect("quoted Name principal must prepare");
    let section = adapter
        .prepare("{% Nil %}[#(Nil)]", HashMap::new())
        .expect("cryptographic section must prepare");
    let name_signature = name.as_par().cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("name signature");
    let section_signature = section.as_par().cost_signed_terms[0]
        .signature
        .as_ref()
        .expect("section signature");
    match (name_signature.value.as_ref(), section_signature.value.as_ref()) {
        (
            Some(CostSignatureValue::Name(name_process)),
            Some(CostSignatureValue::Quote(section_process)),
        ) => {
            assert_eq!(name_process.encode_to_vec(), section_process.encode_to_vec());
            assert_ne!(name_signature.encode_to_vec(), section_signature.encode_to_vec());
        },
        other => panic!("distinct Name/Quote wire tags required: {other:?}"),
    }
}

fn prepared_bytes(source: &str) -> Vec<u8> {
    use models::rust::rholang::sorter::par_sort_matcher::ParSortMatcher;
    use models::rust::rholang::sorter::sortable::Sortable;

    let prepared = prepare_program(&frontend(policy()), source, HashMap::new())
        .unwrap_or_else(|error| panic!("public source preparation failed for {source:?}: {error}"));
    ParSortMatcher::sort_match(prepared.as_par())
        .term
        .encode_to_vec()
}

#[test]
fn source_bound_signed_queries_match_explicit_row_local_expansion() {
    for (source, expanded) in [
        (
            r#"{% for(x <- @"svc"!?(1, 2)) { @"OUT"!(*x) } %}[alice]"#,
            r#"{% new reply in { @"svc"!(*reply, 1, 2) | for(x <- reply) { {% @"OUT"!(*x) %}[alice] } } %}[alice]"#,
        ),
        (
            r#"{% for(@x <- @"svc"!?(1)) { @"OUT"!(x) } %}[alice -o bob]"#,
            r#"{% new reply in { @"svc"!(*reply, 1) | for(@x <- reply) { {% @"OUT"!(x) %}[bob] } } %}[alice]"#,
        ),
        (
            r#"{% for(<- @"svc"!?()) {% @"OUT"!(1) %} %}[alice]"#,
            r#"{% new reply in { @"svc"!(*reply) | for(<- reply) { {% @"OUT"!(1) %}[alice] } } %}[alice]"#,
        ),
        (
            r#"{% for(x <- @"first"!?(1); y <- @"second"!?(*x)) {% @"OUT"!(*y) %} %}[alice -o bob]"#,
            r#"{% new firstReply in { @"first"!(*firstReply, 1) | for(x <- firstReply) {
                new secondReply in { @"second"!(*secondReply, *x) | for(y <- secondReply) { {% @"OUT"!(*y) %}[bob] } }
            } } %}[alice]"#,
        ),
        (
            r#"{% for(x <- @"first"!?(1) & {% y <- @"second" %}[carol]) {% @"OUT"!(*x, *y) %} %}[alice]"#,
            r#"{% new reply in { @"first"!(*reply, 1) | for(x <- reply & {% y <- @"second" %}[carol]) {
                {% @"OUT"!(*x, *y) %}[alice]
            } } %}[alice]"#,
        ),
        (
            r#"{% for(@x <- @"svc"!?(1) where x == 1) { {% @"OUT"!(x) %}[carol] } %}[alice]"#,
            r#"{% new reply in { @"svc"!(*reply, 1) | for(@x <- reply where x == 1) {
                {% @"OUT"!(x) %}[carol]
            } } %}[alice]"#,
        ),
        (
            r#"for({% value <- @"c" %}[alice]) {% Nil %}"#,
            r#"for({% value <- @"c" %}[alice]) { Nil }"#,
        ),
    ] {
        assert_eq!(prepared_bytes(source), prepared_bytes(expanded), "{source}");
        assert_eq!(prepared_bytes(source), prepared_bytes(source), "fresh binder identities");
    }
}

#[test]
fn ast_only_preparation_cannot_obtain_source_bound_cost_authority() {
    for source in [
        r#"{% for(x <- @"svc"!?(1)) { Nil } %}[alice]"#,
        r#"{% for(x <- @"svc"!?(1)) { Nil } %}[alice -o bob]"#,
        r#"for({% value <- @"c" %}[alice]) {% Nil %}"#,
    ] {
        mettail_runtime::clear_var_cache();
        let proc = Proc::parse_via_wpda(source).expect("signed receive source parses");
        assert!(
            error(frontend(policy()).prepare_process(&proc, HashMap::new()))
                .contains("CostPlanUnavailable"),
            "{source}"
        );
        assert!(prepare_program(&frontend(policy()), source, HashMap::new()).is_ok(), "{source}");
    }
}

#[test]
fn signed_source_cancellation_failure_publishes_no_artifact() {
    let source = r#"{% for(x <- @"svc"!?(1, 2, 3)) {% Nil %} %}[alice -o bob]"#;
    let signal = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&signal);
    let adapter =
        frontend(policy()).with_cancellation(Arc::new(move || observed.load(Ordering::Relaxed)));
    assert!(prepare_program(&adapter, source, HashMap::new()).is_err());
    assert!(session::ensure_inactive().is_ok());
    assert!(prepare_program(&frontend(policy()), source, HashMap::new()).is_ok());
}

#[test]
fn public_preparation_binds_exact_source_language_and_encoded_output() {
    use models::rust::rholang::protobuf_encoder;

    let adapter = frontend(policy());
    let source = r#"{% for(x <- @"svc"!?(1)) {% Nil %} %}[alice -o bob]"#;
    let first = prepare_program(&adapter, source, HashMap::new()).expect("bound source");
    let repeated = prepare_program(&adapter, source, HashMap::new()).expect("repeated source");
    let (bound_source, language, output) = first.source_binding().expect("source receipt");
    assert_eq!(bound_source, source.as_bytes());
    assert_eq!(Some(language), adapter.language_identity());
    assert_eq!(output, protobuf_encoder::encode_to_vec(first.as_par()));
    assert_eq!(first.source_binding(), repeated.source_binding());

    let spaced_source = format!("{source} ");
    let spaced = prepare_program(&adapter, &spaced_source, HashMap::new()).expect("spaced source");
    let spaced_binding = spaced.source_binding().expect("spaced source receipt");
    assert_eq!(spaced_binding.0, spaced_source.as_bytes());
    assert_ne!(bound_source, spaced_binding.0);
    assert_eq!(language, spaced_binding.1);
    assert_eq!(output, spaced_binding.2);

    let (ast_only, _) = adapter
        .prepare_process(&Proc::PZero, HashMap::new())
        .expect("AST-only Nil");
    assert!(ast_only.source_binding().is_none());
}

fn admitted_preparation_process() -> impl proptest::strategy::Strategy<Value = Proc> {
    use proptest::prelude::*;

    prop_oneof![
        Just(Proc::PZero),
        any::<i16>().prop_map(|value| Proc::CastInt(Arc::new(Int::NumLit(i64::from(value))))),
        any::<bool>().prop_map(|value| Proc::CastBool(Arc::new(Bool::BoolLit(value)))),
        "[a-zA-Z0-9 ]{0,48}"
            .prop_map(|value| Proc::CastStr(Arc::new(Str::StringLit(value)))),
    ]
    .prop_recursive(3, 64, 8, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 0..=8)
                .prop_map(|values| Proc::CastList(Arc::new(List::ListLit(values)))),
            (inner.clone(), prop::collection::vec(inner.clone(), 1..=7))
                .prop_map(|(first, rest)| Proc::POutputNil2Plus(Arc::new(first), rest)),
            inner.clone().prop_map(|value| Proc::POutputNil(Arc::new(value))),
            (inner.clone(), inner)
                .prop_map(|(left, right)| Proc::PParInfix(Arc::new(left), Arc::new(right))),
        ]
    })
}

fn paid_preparation(
    source: &Proc,
    work_limit: u64,
) -> Result<session::DirectLoweringOutput, RholangAstLowerError> {
    let limits = policy();
    let mut cancel = || false;
    let imports = CheckedCallerImports::admit(
        HashMap::new(),
        ImportLimits {
            entries: limits.max_import_entries,
            nodes: limits.max_import_nodes,
            payload_bytes: limits.max_import_payload_bytes,
        },
        &mut cancel,
    )
    .expect("empty caller imports");
    let context = BoundEnv::empty_with_admission(
        Arc::new(EmptyFltResolver),
        limits.lowering,
        SourceAdmissionMode::Public,
    )
    .with_caller_imports(imports);
    let mut work = 0;
    let mut budget = mettail_rholang_codegen::ReflectedCodecBudget::new(
        &mut work,
        work_limit,
        10_000_000,
        &mut cancel,
    );
    session::lower_public_body_with_budget(source, context, &mut budget)
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(64))]

    #[test]
    fn public_preparation_preserves_checked_operation_results(
        source in admitted_preparation_process(),
    ) {
        let expected = paid_preparation(&source, 1_000_000).expect("admitted paid operation");
        let (actual, report) = frontend(policy())
            .prepare_process(&source, HashMap::new()).expect("public preparation");
        proptest::prop_assert_eq!(actual.as_par().encode_to_vec(), expected.par.encode_to_vec());
        proptest::prop_assert_eq!(report, expected.guard_report);
        proptest::prop_assert!(expected.folds.is_empty());
        proptest::prop_assert!(session::ensure_inactive().is_ok());
        let refused = paid_preparation(&source, 0).err().expect("zero paid allowance");
        proptest::prop_assert!(format!("{refused:?}").contains("WorkLimit"), "zero paid work must refuse");
        proptest::prop_assert!(session::ensure_inactive().is_ok());
    }

    #[test]
    fn public_preparation_cancellation_never_publishes_and_releases_the_session(
        source in admitted_preparation_process(),
        selected in proptest::prelude::any::<usize>(),
    ) {
        let polls = Arc::new(AtomicUsize::new(0));
        let stop_at = Arc::new(AtomicUsize::new(usize::MAX));
        let observed = Arc::clone(&polls);
        let threshold = Arc::clone(&stop_at);
        let adapter = frontend(policy()).with_cancellation(Arc::new(move || {
            observed.fetch_add(1, Ordering::Relaxed) >= threshold.load(Ordering::Relaxed)
        }));
        let expected = paid_preparation(&source, 1_000_000).expect("admitted paid operation");
        let (baseline, report) = adapter.prepare_process(&source, HashMap::new())
            .expect("count cancellation polls");
        proptest::prop_assert_eq!(baseline.as_par().encode_to_vec(), expected.par.encode_to_vec());
        proptest::prop_assert_eq!(report, expected.guard_report.clone());
        let total = polls.load(Ordering::Relaxed);
        proptest::prop_assert!(total > 0);
        stop_at.store(selected % total, Ordering::Relaxed);
        polls.store(0, Ordering::Relaxed);
        let refused = error(adapter.prepare_process(&source, HashMap::new()));
        proptest::prop_assert!(refused.contains("ancelled"), "{}", refused);
        proptest::prop_assert!(session::ensure_inactive().is_ok());
        stop_at.store(usize::MAX, Ordering::Relaxed);
        polls.store(0, Ordering::Relaxed);
        let (repeated, report) = adapter.prepare_process(&source, HashMap::new())
            .expect("request after cancellation");
        proptest::prop_assert_eq!(repeated.as_par().encode_to_vec(), expected.par.encode_to_vec());
        proptest::prop_assert_eq!(report, expected.guard_report);
        proptest::prop_assert_eq!(polls.load(Ordering::Relaxed), total);
        proptest::prop_assert!(session::ensure_inactive().is_ok());
    }
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(32))]

    #[test]
    fn public_preparation_retains_checked_operation_failures(
        name in "[a-z][a-z0-9]{0,31}",
        value in proptest::prelude::any::<i16>(),
        unsupported in proptest::prelude::any::<bool>(),
    ) {
        let source = if unsupported {
            Proc::IntBinProc(
                Arc::new(Proc::CastInt(Arc::new(Int::NumLit(i64::from(value))))),
                Arc::new(Int::NumLit(8)),
            )
        } else {
            Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named(name))))
        };
        let expected = lowering_error(paid_preparation(&source, 1_000_000)
            .err().expect("checked operation refusal")).to_string();
        let adapter = frontend(policy());
        proptest::prop_assert_eq!(error(adapter.prepare_process(&source, HashMap::new())), expected);
        proptest::prop_assert!(session::ensure_inactive().is_ok());
        let (prepared, report) = adapter.prepare_process(&Proc::PZero, HashMap::new())
            .expect("request after checked refusal");
        proptest::prop_assert_eq!(prepared.as_par().encode_to_vec(), Par::default().encode_to_vec());
        proptest::prop_assert_eq!(report, GuardDischargeReport::default());
        proptest::prop_assert!(session::ensure_inactive().is_ok());
    }
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(8))]

    #[test]
    fn signed_query_preparation_preserves_arbitrary_request_payloads(
        arguments in proptest::collection::vec(proptest::prelude::any::<i16>(), 0..12),
        transfer in proptest::prelude::any::<bool>(),
    ) {
        let arguments = arguments.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ");
        let signature = if transfer { "alice -o bob" } else { "alice" };
        let final_signature = if transfer { "bob" } else { "alice" };
        let source = format!("{{% for(x <- @\"svc\"!?({arguments})) {{% @\"OUT\"!(*x) %}} %}}[{signature}]");
        let payload = if arguments.is_empty() { "*reply".into() } else { format!("*reply, {arguments}") };
        let expanded = format!("{{% new reply in {{ @\"svc\"!({payload}) | for(x <- reply) {{ {{% @\"OUT\"!(*x) %}}[{final_signature}] }} }} %}}[alice]");
        proptest::prop_assert_eq!(prepared_bytes(&source), prepared_bytes(&expanded));
    }
}

#[test]
fn actual_inline_regex_fixture_reaches_the_checked_public_adapter() {
    let source = include_str!("../../tests/fixtures/regex_extension.rho");
    let mut limits = policy();
    limits.max_source_bytes = 1_000_000;
    // Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
    // limits.max_preparation_work = 100_000_000;
    // limits.max_preparation_units = 100_000_000;
    // This is the existing inline theory fixture, not a smaller handwritten
    // substitute. Full application execution remains the public-node gate.
    let (prepared, _) = frontend(limits)
        .prepare_with_report(source, HashMap::new())
        .expect("the actual inline Regex theory must not be over-refused");
    assert_ne!(prepared.as_par().encode_to_vec(), Par::default().encode_to_vec());
}

#[test]
fn actual_regex_application_reaches_the_checked_public_adapter() {
    let source = include_str!("../../tests/fixtures/regex_gslt_application.rho");
    let mut limits = policy();
    limits.max_source_bytes = 1_000_000;
    // Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
    // limits.max_preparation_work = 100_000_000;
    // limits.max_preparation_units = 100_000_000;
    let (prepared, _) = frontend(limits)
        .prepare_with_report(source, HashMap::new())
        .expect("the actual Regex application must pass public preparation");
    assert_ne!(prepared.as_par().encode_to_vec(), Par::default().encode_to_vec());
}

#[test]
fn source_size_and_cancellation_refuse_before_malformed_source_parsing() {
    let mut limits = policy();
    limits.max_source_bytes = 0;
    assert!(error(frontend(limits).prepare("not Rholang", HashMap::new()))
        .contains("source byte limit"));
    let adapter = frontend(policy()).with_cancellation(Arc::new(|| true));
    assert!(error(adapter.prepare("not Rholang", HashMap::new())).contains("cancelled"));
}

#[test]
fn malformed_source_does_not_poison_the_next_request() {
    let adapter = frontend(policy());
    assert!(adapter.prepare("new (", HashMap::new()).is_err());
    assert!(adapter.prepare("Nil", HashMap::new()).is_ok());
}

#[test]
fn malformed_and_trailing_source_preserve_generated_parser_diagnostics() {
    let adapter = frontend(policy());
    for source in ["", "new (", "Nil )", "Module Broken {", "Nil /*"] {
        mettail_runtime::clear_var_cache();
        let expected = Proc::parse_via_wpda(source)
            .expect_err("the generated entrypoint must reject incomplete or trailing input")
            .to_string();
        assert_eq!(error(adapter.prepare(source, HashMap::new())), expected, "{source}");
    }
}

// Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
// Public preparation has no work or storage-unit ceiling, so these limits no longer exist.
// #[test]
// fn explicit_preparation_work_and_payload_limits_refuse_without_fallback() {
//     let mut limits = policy();
//     limits.max_preparation_work = 0;
//     assert!(
//         error(frontend(limits).prepare_process(&Proc::PZero, HashMap::new())).contains("WorkLimit")
//     );
//     limits = policy();
//     limits.max_preparation_units = 0;
//     assert!(error(frontend(limits).prepare_process(&Proc::PZero, HashMap::new()))
//         .contains("PayloadByteLimit"));
// }

#[test]
fn checked_preparation_reservations_poll_cancellation_without_a_work_ceiling() {
    let source = include_str!("../../tests/fixtures/regex_gslt_application.rho");
    let mut limits = policy();
    limits.max_source_bytes = 1_000_000;
    let polls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&polls);
    let adapter = frontend(limits).with_cancellation(Arc::new(move || {
        counted.fetch_add(1, Ordering::Relaxed);
        false
    }));
    adapter
        .prepare_with_report(source, HashMap::new())
        .expect("preparation has no work or storage-unit ceiling");
    let total = polls.load(Ordering::Relaxed);
    assert!(total > 16, "reservation points must poll cancellation: {total}");
    let seen = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&seen);
    let stop_at = total / 2;
    let adapter = frontend(limits)
        .with_cancellation(Arc::new(move || observed.fetch_add(1, Ordering::Relaxed) >= stop_at));
    let refused = error(adapter.prepare_with_report(source, HashMap::new()));
    assert!(refused.contains("ancelled"), "{refused}");
    assert!(session::ensure_inactive().is_ok());
}

#[test]
fn caller_imports_preserve_node_values_and_do_not_become_lexical_binders() {
    let adapter = frontend(policy());
    let value = new_gint_par(42, Vec::new(), false);
    let environment = || HashMap::from([("supplied".to_owned(), value.clone())]);
    let source =
        Proc::PNew(Scope::new(vec![Binder(FreeVar::fresh_named("unused"))], Arc::new(Proc::PZero)));
    let (prepared, _) = adapter
        .prepare_process(&source, environment())
        .expect("source new");
    assert_eq!(
        prepared.as_par().news[0].injections["supplied"].encode_to_vec(),
        value.encode_to_vec(),
    );
    let variable = Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named("supplied"))));
    assert!(error(adapter.prepare_process(&variable, environment()))
        .contains("UnresolvedProcessReference"));
}

#[test]
fn malformed_or_over_limit_imports_do_not_produce_artifacts() {
    let adapter = frontend(policy());
    let empty_value = HashMap::from([("bad".to_owned(), Par::default())]);
    assert!(error(adapter.prepare_process(&Proc::PZero, empty_value)).contains("RootNil"));
    let mut limits = policy();
    limits.max_import_entries = 0;
    let value = new_gint_par(1, Vec::new(), false);
    assert!(error(
        frontend(limits)
            .prepare_process(&Proc::PZero, HashMap::from([("value".to_owned(), value)]),)
    )
    .contains("Entries"));
}

#[test]
fn cancellation_signal_is_polled_for_each_independent_request() {
    let cancelled = Arc::new(AtomicBool::new(true));
    let signal = Arc::clone(&cancelled);
    let adapter =
        frontend(policy()).with_cancellation(Arc::new(move || signal.load(Ordering::Relaxed)));
    assert!(adapter.prepare("Nil", HashMap::new()).is_err());
    cancelled.store(false, Ordering::Relaxed);
    assert!(adapter.prepare("Nil", HashMap::new()).is_ok());
}

#[test]
fn guard_diagnostics_remain_owned_and_disagreement_never_publishes() {
    let report = GuardDischargeReport { residual: 2, ..Default::default() };
    let (_, actual) = finish_output(session::DirectLoweringOutput {
        par: Par::default(),
        folds: Vec::new(),
        guard_report: report.clone(),
    })
    .expect("diagnostic-only output");
    assert_eq!(actual, report);
    assert!(error(finish_output(session::DirectLoweringOutput {
        par: Par::default(),
        folds: Vec::new(),
        guard_report: GuardDischargeReport { disagreements: 1, ..Default::default() },
    }))
    .contains("disagreement"));
}

#[test]
fn unenrolled_fold_output_cannot_be_silently_discarded() {
    assert!(error(finish_output(session::DirectLoweringOutput {
        par: Par::default(),
        folds: vec![FoldSpec {
            kind: FoldKind::Int,
            width: 8,
            site_index: 0,
            fingerprint: "unaccepted-test-output".to_owned(),
        }],
        guard_report: GuardDischargeReport::default(),
    }))
    .contains("Unenrolled fold"));
}
