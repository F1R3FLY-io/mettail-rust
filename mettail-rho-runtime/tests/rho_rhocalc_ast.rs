//! AST-first rhocalc lowering into the Rho machine.
//!
//! The examples are written as rhocalc source for readability, parsed by the
//! MeTTaIL/WPDA parser, and lowered directly to normalized `rhoapi::Par`.
//! Rholang source text is not generated or parsed on this path.

use std::sync::Arc;

use mettail_ast::language::LanguageDef;
use mettail_languages::rhocalc::{
    Bag, Int, List, Map, Name, Proc, RhoCalcTerm, RhoCalcTermInner, Str,
};
use mettail_rho_codegen::{
    plan_rho_default_backend_with_evidence_audit, RhoCoverageEvidence, RhoDefaultBackendEvidence,
};
use mettail_rho_runtime::{
    lower_rhocalc_proc, lower_rhocalc_term, rho_runtime_backed_rhocalc_strings,
    rho_runtime_backed_rhocalc_values, run_normalized_par_for_oracle,
    run_normalized_par_for_oracle_and_read_strings, PlannedRhoBackend, RhocalcAstLowerError,
    RHOCALC_BAG_ABI_TAG,
};
use mettail_runtime::{
    clear_var_cache, Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeObservationValue,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::EList;
use models::rhoapi::Par;
use models::rust::rholang::implicits::GPrivateBuilder;

mod support;

fn parse_lower(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc WPDA parse failed for {source:?}: {err:?}"));
    lower_rhocalc_proc(&proc)
        .unwrap_or_else(|err| panic!("rhocalc AST lowering failed for {source:?}: {err:?}"))
}

const RHOCALC_DYNAMIC_PLAN_FRAGMENT: &str = r#"
    name: RhoCalcDynamicRuntime,
    types { Proc }
    terms {}
"#;

fn passing_dynamic_evidence() -> RhoDefaultBackendEvidence {
    RhoDefaultBackendEvidence {
        proofs_passed: true,
        proof_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v".to_string(),
            "formal/rocq/rho_bridge/theories/RhoLanguageBackendWrapper.v".to_string(),
        ],
        oracle_parity_passed: true,
        oracle_parity_evidence_refs: vec![
            "mettail-rho-runtime/tests/rho_rhocalc_ast.rs".to_string()
        ],
        coverage_audit_passed: true,
        coverage_audit_evidence_refs: vec![
            "formal/rocq/rho_bridge/theories/RhoRejectedCoverage.v".to_string()
        ],
        scheduler_fairness_passed: true,
        scheduler_fairness_evidence_refs: vec![
            "formal/tla/rho_machine/RhoNetScheduler.tla".to_string()
        ],
        coverage: RhoCoverageEvidence::AllRulesLowered,
    }
}

fn rhocalc_dynamic_backend() -> PlannedRhoBackend {
    let def = syn::parse_str::<LanguageDef>(RHOCALC_DYNAMIC_PLAN_FRAGMENT)
        .expect("dynamic rhocalc runtime fragment must parse");
    let audit_policy = support::strict_evidence_audit_policy();
    let plan = plan_rho_default_backend_with_evidence_audit(
        &def,
        passing_dynamic_evidence(),
        &audit_policy,
    )
    .expect("empty dynamic-call Rho backend plan must pass the Rho-default gate");
    assert!(
        plan.lowering.lowered.is_empty(),
        "dynamic RhoCalc plan should not need static scalar contracts"
    );
    assert!(
        plan.lowering.rejected.is_empty(),
        "dynamic RhoCalc plan should not hide rejected static rules"
    );
    PlannedRhoBackend::from_plan(plan)
}

fn quoted_name(value: &str) -> Name {
    Name::NQuote(Arc::new(Proc::CastStr(Arc::new(Str::StringLit(value.to_string())))))
}

fn output_to_out(payload: Proc) -> Proc {
    Proc::POutput(Arc::new(quoted_name("OUT")), Arc::new(payload))
}

fn text_proc(value: &str) -> Proc {
    Proc::CastStr(Arc::new(Str::StringLit(value.to_string())))
}

async fn read_strings(source: &str) -> Vec<String> {
    let par = parse_lower(source);
    let mut values = run_normalized_par_for_oracle_and_read_strings(&par, "OUT")
        .await
        .unwrap_or_else(|err| panic!("lowered rhocalc execution failed for {source:?}: {err}"));
    values.sort();
    values
}

async fn read_strings_from_par(par: &Par) -> Vec<String> {
    let mut values = run_normalized_par_for_oracle_and_read_strings(par, "OUT")
        .await
        .expect("lowered rhocalc execution failed");
    values.sort();
    values
}

async fn observe_runtime_values(payload: Proc) -> Vec<RuntimeObservationValue> {
    let call = lower_rhocalc_proc(&output_to_out(payload)).expect("payload output should lower");
    rhocalc_dynamic_backend()
        .run_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("structured runtime observation should execute")
        .values
}

#[tokio::test]
async fn single_channel_comm_executes_payload_process() {
    let source = r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string()]);
}

#[tokio::test]
async fn ambiguous_term_lowers_every_distinct_proc_alternative() {
    let left = output_to_out(text_proc("left"));
    let right = output_to_out(text_proc("right"));
    let term = RhoCalcTerm(RhoCalcTermInner::Ambiguous(vec![
        RhoCalcTermInner::Proc(left),
        RhoCalcTermInner::Proc(right),
    ]));

    let par = lower_rhocalc_term(&term).expect("ambiguous Proc term should lower");

    assert_eq!(read_strings_from_par(&par).await, vec!["left".to_string(), "right".to_string()]);
}

#[tokio::test]
async fn ambiguous_term_deduplicates_exact_semantic_proc_alternatives() {
    let duplicated = output_to_out(text_proc("same"));
    let term = RhoCalcTerm(RhoCalcTermInner::Ambiguous(vec![
        RhoCalcTermInner::Proc(duplicated.clone()),
        RhoCalcTermInner::Proc(duplicated),
    ]));

    let par = lower_rhocalc_term(&term).expect("duplicate Proc alternatives should lower once");

    assert_eq!(read_strings_from_par(&par).await, vec!["same".to_string()]);
}

#[test]
fn ambiguous_term_rejects_cross_category_alternative_instead_of_dropping_it() {
    let term = RhoCalcTerm(RhoCalcTermInner::Ambiguous(vec![
        RhoCalcTermInner::Proc(output_to_out(text_proc("kept"))),
        RhoCalcTermInner::Name(quoted_name("not-a-proc")),
    ]));

    let err = lower_rhocalc_term(&term)
        .expect_err("cross-category ambiguity must not silently drop non-Proc alternatives");

    assert_eq!(err, RhocalcAstLowerError::ExpectedProcTerm);
}

#[test]
fn rhocalc_language_default_report_observes_runtime_values() {
    let language = rho_runtime_backed_rhocalc_values(rhocalc_dynamic_backend(), "OUT");
    let term = language
        .parse_term(r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#)
        .expect("rhocalc source must parse through the generated language");

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho-backed RhoCalc language must return a structured observation report");
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho-backed RhoCalc report must expose OUT observations");

    assert_eq!(out.values, vec![RuntimeObservationValue::Text("p".to_string())]);
}

#[test]
fn rhocalc_language_default_report_executes_parsed_process_as_ast_call() {
    let language = rho_runtime_backed_rhocalc_strings(rhocalc_dynamic_backend(), "OUT");
    let term = language
        .parse_term(r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#)
        .expect("rhocalc source must parse through the generated language");

    assert_eq!(language.default_runtime_backend(), RuntimeBackend::RhoMachine);
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho-backed RhoCalc language must return an observation report");

    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    assert!(
        report
            .evidence_refs()
            .iter()
            .any(|reference| reference == "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v"),
        "Rho runtime report must retain flip-gate evidence"
    );

    let out = report
        .observations_for_channel("OUT")
        .expect("Rho-backed RhoCalc report must expose OUT observations");
    assert_eq!(out.values, vec![RuntimeObservationValue::Text("p".to_string())]);

    let compat_err = language
        .run_default_backend(term.as_ref())
        .expect_err("Ascent-shaped compatibility API must reject Rho observations");
    assert!(
        compat_err
            .contains("RhoMachine backend for language RhoCalc returned runtime observations"),
        "{compat_err}"
    );
}

#[tokio::test]
async fn runtime_value_observation_preserves_rhocalc_list_map_and_bag_payloads() {
    let list_values = observe_runtime_values(Proc::CastList(Arc::new(List::ListLit(vec![
        Proc::CastInt(Arc::new(Int::NumLit(1))),
        Proc::CastStr(Arc::new(Str::StringLit("two".to_string()))),
    ]))))
    .await;
    assert_eq!(
        list_values,
        vec![RuntimeObservationValue::List(vec![
            RuntimeObservationValue::Int(1),
            RuntimeObservationValue::Text("two".to_string()),
        ])]
    );

    let mut map_entries = mettail_runtime::HashMapLit::new();
    map_entries.insert(
        Proc::CastStr(Arc::new(Str::StringLit("key".to_string()))),
        Proc::CastInt(Arc::new(Int::NumLit(7))),
    );
    let map_values =
        observe_runtime_values(Proc::CastMap(Arc::new(Map::MapLit(map_entries)))).await;
    assert_eq!(
        map_values,
        vec![RuntimeObservationValue::Map(vec![(
            RuntimeObservationValue::Text("key".to_string()),
            RuntimeObservationValue::Int(7),
        )])]
    );

    let alpha = Proc::CastStr(Arc::new(Str::StringLit("alpha".to_string())));
    let beta = Proc::CastStr(Arc::new(Str::StringLit("beta".to_string())));
    let mut bag = mettail_runtime::HashBag::new();
    bag.insert(beta);
    bag.insert(alpha.clone());
    bag.insert(alpha);
    let bag_values = observe_runtime_values(Proc::CastBag(Arc::new(Bag::BagLit(bag)))).await;
    assert_eq!(
        bag_values,
        vec![RuntimeObservationValue::Bag(vec![
            (RuntimeObservationValue::Text("alpha".to_string()), 2),
            (RuntimeObservationValue::Text("beta".to_string()), 1),
        ])]
    );
}

#[tokio::test]
async fn multi_channel_comm_runs_as_one_atomic_join() {
    let source = r#"{
        (@("left")?x,@("right")?y).{{*(x)|*(y)}}
        | @("left")!(@("OUT")!("p"))
        | @("right")!(@("OUT")!("q"))
    }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string(), "q".to_string()]);
}

#[tokio::test]
async fn received_name_can_be_reused_as_channel() {
    let source = r#"{
        (@("c")?x).{x!(@("OUT")!("routed"))}
        | @("c")!(*(@("sink")))
        | (@("sink")?y).{*(y)}
    }"#;

    assert_eq!(read_strings(source).await, vec!["routed".to_string()]);
}

#[tokio::test]
async fn drop_of_quoted_process_executes_without_source_generation() {
    let source = r#"*(@(@("OUT")!("p")))"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string()]);
}

#[tokio::test]
async fn new_name_scope_lowers_to_private_rho_binding() {
    let source = r#"new(x)in{x!(@("OUT")!("private"))}"#;
    let par = parse_lower(source);

    run_normalized_par_for_oracle(&par)
        .await
        .unwrap_or_else(|err| panic!("lowered new-scope rhocalc failed: {err}"));
    assert!(
        run_normalized_par_for_oracle_and_read_strings(&par, "OUT")
            .await
            .expect("rerun for OUT observation")
            .is_empty(),
        "private new-name datum must not leak to OUT"
    );
}

#[test]
fn lowered_comm_is_normalized_ast_with_receive_and_send_members() {
    let par = parse_lower(r#"{ (@("c")?x).{*(x)} | @("c")!(@("OUT")!("p")) }"#);

    assert_eq!(par.receives.len(), 1);
    assert_eq!(par.sends.len(), 1);
    assert!(par.exprs.is_empty());
    assert!(par.matches.is_empty());
}

#[test]
fn list_literal_lowers_to_elist_ast_preserving_order() {
    let proc = Proc::CastList(Arc::new(List::ListLit(vec![
        Proc::CastInt(Arc::new(Int::NumLit(1))),
        Proc::CastStr(Arc::new(Str::StringLit("two".to_string()))),
    ])));

    let par = lower_rhocalc_proc(&proc).expect("list literal should lower");
    let ExprInstance::EListBody(list) = only_expr(&par) else {
        panic!("expected EListBody");
    };

    assert_eq!(list.ps.len(), 2);
    assert!(matches!(only_expr(&list.ps[0]), ExprInstance::GInt(1)));
    assert!(matches!(only_expr(&list.ps[1]), ExprInstance::GString(value) if value == "two"));
}

#[test]
fn map_literal_lowers_to_emap_ast() {
    let mut entries = mettail_runtime::HashMapLit::new();
    entries.insert(
        Proc::CastStr(Arc::new(Str::StringLit("key".to_string()))),
        Proc::CastInt(Arc::new(Int::NumLit(7))),
    );
    let proc = Proc::CastMap(Arc::new(Map::MapLit(entries)));

    let par = lower_rhocalc_proc(&proc).expect("map literal should lower");
    let ExprInstance::EMapBody(map) = only_expr(&par) else {
        panic!("expected EMapBody");
    };

    assert_eq!(map.kvs.len(), 1);
    let pair = &map.kvs[0];
    assert!(matches!(
        only_expr(pair.key.as_ref().expect("map key")),
        ExprInstance::GString(value) if value == "key"
    ));
    assert!(matches!(
        only_expr(pair.value.as_ref().expect("map value")),
        ExprInstance::GInt(7)
    ));
}

#[test]
fn bag_literal_lowers_to_tagged_elist_preserving_multiplicity() {
    let alpha = Proc::CastStr(Arc::new(Str::StringLit("alpha".to_string())));
    let beta = Proc::CastStr(Arc::new(Str::StringLit("beta".to_string())));
    let mut bag = mettail_runtime::HashBag::new();
    bag.insert(beta.clone());
    bag.insert(alpha.clone());
    bag.insert(alpha);
    let proc = Proc::CastBag(Arc::new(Bag::BagLit(bag)));

    let par = lower_rhocalc_proc(&proc).expect("bag literal should lower");
    let outer = only_list(&par);

    assert_eq!(outer.ps.len(), 2);
    assert_eq!(
        outer.ps[0],
        GPrivateBuilder::new_par_from_string(RHOCALC_BAG_ABI_TAG.to_string())
    );

    let entries = only_list(&outer.ps[1]);
    assert_eq!(entries.ps.len(), 2);
    assert_list_count_pair(&entries.ps[0], "alpha", 2);
    assert_list_count_pair(&entries.ps[1], "beta", 1);
}

fn only_expr(par: &Par) -> &ExprInstance {
    assert_eq!(par.exprs.len(), 1, "expected exactly one expression");
    par.exprs[0]
        .expr_instance
        .as_ref()
        .expect("expression instance")
}

fn only_list(par: &Par) -> &EList {
    let ExprInstance::EListBody(list) = only_expr(par) else {
        panic!("expected EListBody");
    };
    list
}

fn assert_list_count_pair(par: &Par, expected_value: &str, expected_count: i64) {
    let pair = only_list(par);
    assert_eq!(pair.ps.len(), 2);
    assert!(matches!(
        only_expr(&pair.ps[0]),
        ExprInstance::GString(value) if value == expected_value
    ));
    assert!(matches!(
        only_expr(&pair.ps[1]),
        ExprInstance::GInt(count) if *count == expected_count
    ));
}
