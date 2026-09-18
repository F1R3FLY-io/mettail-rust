use super::*;
use mettail_runtime::Scope;
use prost::Message;
use rholang::rust::interpreter::frontend::prepare_program;
use std::sync::atomic::{AtomicBool, Ordering};

fn policy() -> RholangPreparationPolicy {
    RholangPreparationPolicy {
        max_source_bytes: 16_384,
        max_import_entries: 16,
        max_import_nodes: 4096,
        max_import_payload_bytes: 65_536,
        max_preparation_work: 1_000_000,
        max_preparation_units: 1_000_000,
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
fn actual_inline_regex_fixture_reaches_the_checked_public_adapter() {
    let source = include_str!("../../tests/fixtures/regex_extension.rho");
    let mut limits = policy();
    limits.max_source_bytes = 1_000_000;
    limits.max_preparation_work = 100_000_000;
    limits.max_preparation_units = 100_000_000;
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
    limits.max_preparation_work = 100_000_000;
    limits.max_preparation_units = 100_000_000;
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

#[test]
fn explicit_preparation_work_and_payload_limits_refuse_without_fallback() {
    let mut limits = policy();
    limits.max_preparation_work = 0;
    assert!(
        error(frontend(limits).prepare_process(&Proc::PZero, HashMap::new())).contains("WorkLimit")
    );
    limits = policy();
    limits.max_preparation_units = 0;
    assert!(error(frontend(limits).prepare_process(&Proc::PZero, HashMap::new()))
        .contains("PayloadByteLimit"));
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
