//! AST-first rholang lowering into the Rho machine.
//!
//! The examples are written as rholang source for readability, parsed by the
//! MeTTaIL/WPDA parser, and lowered directly to normalized `rhoapi::Par`.
//! Rholang source text is not generated or parsed on this path.

use std::sync::Arc;

use mettail_ast::language::LanguageDef;
use mettail_languages::rholang::{
    Bag, Int, List, Map, Name, Proc, RholangLanguage, RholangTerm, RholangTermInner, Str,
};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, suggest_rejected_rule_dispositions,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::fold_contract::FoldKind;
use mettail_rholang_runtime::{
    dovetail_rho_backed_rholang, lower_rholang_proc, lower_rholang_term,
    lower_rholang_term_with_folds, rho_runtime_backed_rholang_strings,
    rho_runtime_backed_rholang_values, rholang_ast_runtime_def, run_normalized_par_for_oracle,
    run_normalized_par_for_oracle_and_read_runtime_values,
    run_normalized_par_for_oracle_and_read_strings, PlannedRhoBackend, RholangAstLowerError,
    RHOLANG_BAG_ABI_TAG,
};
use mettail_runtime::{
    clear_var_cache, Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeObservationValue,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::EList;
use models::rhoapi::Par;
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::new_gint_par;
use prost::Message;

fn parse_lower(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang WPDA parse failed for {source:?}: {err:?}"));
    lower_rholang_proc(&proc)
        .unwrap_or_else(|err| panic!("rholang AST lowering failed for {source:?}: {err:?}"))
}

/// Coverage requirements derived from the language-aware rejected-rule classifier.
/// Structural constructors are covered by generated Rho AST contracts; native/eval and unsupported
/// scalar operators are covered by Rho-native system-process rules. Labels are de-duplicated
/// deterministically because the same label can appear in several categories and
/// `RhoCoverageEvidence` forbids duplicate dispositions.
fn rho_default_coverage_requirements(def: &LanguageDef) -> RhoDefaultBackendRequirements {
    let lowering = lower_language_def(def);
    let dispositions = suggest_rejected_rule_dispositions(def, &lowering);
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
        // DERIVED, mirroring the production planner (`rholang_ast::rho_default_coverage_requirements`).
        // `NoGuardObligations` asserts the language induces none, which stopped being true when
        // Rholang declared its `where` slots as semantic predicates.
        guard_coverage: RhoGuardCoverageEvidence::CoveredGuardObligations(
            mettail_rholang_codegen::guard_quality::substrate_guard_coverage(def),
        ),
    }
}

fn rholang_dynamic_backend() -> PlannedRhoBackend {
    // Build the dynamic Rho backend from the REAL reconstructed Rholang
    // augmented definition, so its fingerprint equals the generated
    // `RholangLanguage` fingerprint and installs on the real identity.
    let def = rholang_ast_runtime_def();
    let plan = plan_rho_default_backend(&def, rho_default_coverage_requirements(&def))
        .expect("real Rholang def must pass the Rho-default gate with Rho-native coverage");
    assert_eq!(
        plan.language_name(),
        "Rholang",
        "the dynamic Rholang plan must carry the real Rholang identity"
    );
    PlannedRhoBackend::from_plan(plan)
}

fn wrong_name_dynamic_backend() -> PlannedRhoBackend {
    // Reconstruct the real Rholang source but rename it so the plan's
    // `language_name()` no longer matches `RholangAstRuntimeLanguage`. The
    // install must then fail with a name-level `LanguagePlanMismatch`.
    use mettail_languages::rholang::RholangLanguage;
    let source = RholangLanguage
        .metadata()
        .definition_source()
        .expect("generated RholangLanguage must expose its definition_source");
    let renamed = source.replacen("name: Rholang", "name: NotRholang", 1);
    assert_ne!(renamed, source, "rename must take effect; body must contain `name: Rholang`");
    let def = mettail_rholang_codegen::reconstruct_language_def(&renamed)
        .expect("renamed Rholang source must reconstruct as a LanguageDef");
    let plan = plan_rho_default_backend(&def, rho_default_coverage_requirements(&def))
        .expect("renamed Rholang def must still pass the Rho-default gate");
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
        .unwrap_or_else(|err| panic!("lowered rholang execution failed for {source:?}: {err}"));
    values.sort();
    values
}

async fn read_strings_from_par(par: &Par) -> Vec<String> {
    let mut values = run_normalized_par_for_oracle_and_read_strings(par, "OUT")
        .await
        .expect("lowered rholang execution failed");
    values.sort();
    values
}

async fn observe_runtime_values(payload: Proc) -> Vec<RuntimeObservationValue> {
    let call = lower_rholang_proc(&output_to_out(payload)).expect("payload output should lower");
    rholang_dynamic_backend()
        .run_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("structured runtime observation should execute")
        .values
}

#[tokio::test]
async fn single_channel_comm_executes_payload_process() {
    let source = r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string()]);
}

#[tokio::test]
async fn ambiguous_term_lowers_every_distinct_proc_alternative() {
    let left = output_to_out(text_proc("left"));
    let right = output_to_out(text_proc("right"));
    let term = RholangTerm(RholangTermInner::Ambiguous(vec![
        RholangTermInner::Proc(left),
        RholangTermInner::Proc(right),
    ]));

    let par = lower_rholang_term(&term).expect("ambiguous Proc term should lower");

    assert_eq!(read_strings_from_par(&par).await, vec!["left".to_string(), "right".to_string()]);
}

#[tokio::test]
async fn ambiguous_term_deduplicates_exact_semantic_proc_alternatives() {
    let duplicated = output_to_out(text_proc("same"));
    let term = RholangTerm(RholangTermInner::Ambiguous(vec![
        RholangTermInner::Proc(duplicated.clone()),
        RholangTermInner::Proc(duplicated),
    ]));

    let par = lower_rholang_term(&term).expect("duplicate Proc alternatives should lower once");

    assert_eq!(read_strings_from_par(&par).await, vec!["same".to_string()]);
}

#[test]
fn ambiguous_term_rejects_cross_category_alternative_instead_of_dropping_it() {
    let term = RholangTerm(RholangTermInner::Ambiguous(vec![
        RholangTermInner::Proc(output_to_out(text_proc("kept"))),
        RholangTermInner::Name(quoted_name("not-a-proc")),
    ]));

    let err = lower_rholang_term(&term)
        .expect_err("cross-category ambiguity must not silently drop non-Proc alternatives");

    assert_eq!(err, RholangAstLowerError::ExpectedProcTerm);
}

// End-to-end: the generated `RholangLanguage` (defined by the `language!` macro)
// driven through the public `Language` trait and evaluated on the REAL
// f1r3node-rust Rholang interpreter, this variant focusing on the observed VALUE.
//
// `rho_runtime_backed_rholang_values` installs Rholang as a Rho-backed `Language`
// whose plan fingerprint matches the generated `RholangLanguage` (built by
// `rholang_dynamic_backend`), so the test exercises the real language identity
// rather than an ad-hoc fragment. The term is parsed by the generated parser,
// lowered to `rhoapi::Par`, and reduced on an in-memory `RhoRuntime`/RSpace.
#[test]
fn rholang_language_default_report_observes_runtime_values() {
    // Install the Rho-backed language; "OUT" is the channel results are read from.
    let language = rho_runtime_backed_rholang_values(rholang_dynamic_backend(), "OUT")
        .expect("dynamic Rholang plan should install through the public AST helper");
    // Parse a COMM example through the generated language's parser:
    //   receiver `(@("c")?x).{*(x)}` listens on channel @("c"), binds x, and drops
    //     it (`*(x)` runs the received process);
    //   sender `@("c")!(@("OUT")!("p"))` transmits the process `@("OUT")!("p")`.
    // After the rendezvous, `*(x)` runs that process, emitting "p" on OUT.
    let term = language
        .parse_term(r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#)
        .expect("rholang source must parse through the generated language");

    // Lower the parsed term to `rhoapi::Par` and run it on the Rholang interpreter,
    // collecting the structured observation report.
    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho-backed Rholang language must return a structured observation report");
    // Read back whatever came to rest on the OUT channel in RSpace.
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho-backed Rholang report must expose OUT observations");

    // The COMM fired and the dropped process emitted "p", surfaced here as a typed
    // `RuntimeObservationValue` (the value-observation projection).
    assert_eq!(out.values, vec![RuntimeObservationValue::Text("p".to_string())]);
}

// Same end-to-end flow as above (parse → lower → reduce on the real Rholang
// interpreter), but this variant additionally pins down the BACKEND WIRING: it
// proves the generated language routes to the Rho machine and that execution went
// through the normalized-AST path (a `Par` artifact), never generated Rholang
// source text. Hence the name "...executes parsed process as ast call".
#[test]
fn rholang_language_default_report_executes_parsed_process_as_ast_call() {
    let language = rho_runtime_backed_rholang_strings(rholang_dynamic_backend(), "OUT")
        .expect("dynamic Rholang plan should install through the public AST helper");
    // Reuse the single-channel COMM example; it reduces to "p" on OUT.
    let term = language
        .parse_term(r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#)
        .expect("rholang source must parse through the generated language");

    // The generated language must declare (and support) the Rho machine as its
    // default runtime backend.
    assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
    assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));

    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("Rho-backed Rholang language must return an observation report");

    // The report must confirm it executed on the Rho machine via the normalized
    // `Par` AST artifact (`RhoNormalizedAst`) — i.e. AST lowering, not source-gen.
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = report
        .observations_for_channel("OUT")
        .expect("Rho-backed Rholang report must expose OUT observations");
    // Same "p" result observed on OUT, confirming the AST-call path actually ran.
    assert_eq!(out.values, vec![RuntimeObservationValue::Text("p".to_string())]);
}

#[test]
fn held_fold_over_comm_received_value_execs_to_the_folded_value() {
    // Tier-3 (exec path): a fold over a COMM-received value, in a NON-standalone position (a send
    // payload). After the receive COMM binds x, the trampoline folds int(5,8)→5 on the metered Rho
    // machine and the result lands on OUT — proving the held-fold contract is registered AND driven
    // on the exec path (not just the stepper), and that the general C[*r] continuation lift works.
    let language =
        dovetail_rho_backed_rholang("OUT").expect("the dovetail+Rho Rholang wrapper installs");
    let term = language
        .parse_term(r#"{ for(x <- @("c")){ @("OUT")!(int(*(x), 8)) } | @("c")!(int(5,8)) }"#)
        .expect("the held-fold-in-send term parses");
    let report = language
        .run_default_backend_report(term.as_ref())
        .expect("the held-fold term execs on the Rho machine via the trampoline");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("the folded value lands on OUT");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)], "int(5,8) = 5");
}

#[test]
fn pure_fold_reports_through_rho_machine_observation() {
    let language =
        dovetail_rho_backed_rholang("OUT").expect("the dovetail+Rho Rholang wrapper installs");
    let term = RholangTerm(RholangTermInner::Proc(Proc::IntBinProc(
        Arc::new(Proc::CastInt(Arc::new(Int::NumLit(5)))),
        Arc::new(Int::NumLit(8)),
    )));
    let report = language
        .run_default_backend_report(&term)
        .expect("the pure fold reports through a Rho observation send");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
    let out = report
        .observations_for_channel("OUT")
        .expect("the folded value lands on OUT");
    assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)], "int(5,8) = 5");
}

#[test]
fn public_rholang_helper_installs_dynamic_ast_runtime_fragment() {
    let result = rho_runtime_backed_rholang_values(rholang_dynamic_backend(), "OUT");

    if let Err(err) = result {
        panic!(
            "dynamic Rholang AST runtime fragment must install through the public helper: {err}"
        );
    }
}

#[test]
fn public_rholang_helper_rejects_wrong_language_identity() {
    let result = rho_runtime_backed_rholang_values(wrong_name_dynamic_backend(), "OUT");

    let err = match result {
        Ok(_) => panic!("wrong language plan must not install on Rholang AST runtime"),
        Err(err) => err,
    };

    assert!(
        err.to_string()
            .contains("cannot be installed on generated language Rholang"),
        "{err}"
    );
}

#[tokio::test]
async fn runtime_value_observation_preserves_rholang_list_map_and_bag_payloads() {
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
        for(x <- @("left") & y <- @("right")){{*(x)|*(y)}}
        | @("left")!(@("OUT")!("p"))
        | @("right")!(@("OUT")!("q"))
    }"#;

    assert_eq!(read_strings(source).await, vec!["p".to_string(), "q".to_string()]);
}

#[tokio::test]
async fn received_name_can_be_reused_as_channel() {
    let source = r#"{
        for(x <- @("c")){x!(@("OUT")!("routed"))}
        | @("c")!(*(@("sink")))
        | for(y <- @("sink")){*(y)}
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
    let source = r#"new x in {x!(@("OUT")!("private"))}"#;
    let par = parse_lower(source);

    run_normalized_par_for_oracle(&par)
        .await
        .unwrap_or_else(|err| panic!("lowered new-scope rholang failed: {err}"));
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
    let par = parse_lower(r#"{ for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#);

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

    let par = lower_rholang_proc(&proc).expect("list literal should lower");
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

    let par = lower_rholang_proc(&proc).expect("map literal should lower");
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

    let par = lower_rholang_proc(&proc).expect("bag literal should lower");
    let outer = only_list(&par);

    assert_eq!(outer.ps.len(), 2);
    assert_eq!(
        outer.ps[0],
        GPrivateBuilder::new_par_from_string(RHOLANG_BAG_ABI_TAG.to_string())
    );

    let entries = only_list(&outer.ps[1]);
    assert_eq!(entries.ps.len(), 2);
    assert_list_count_pair(&entries.ps[0], "alpha", 2);
    assert_list_count_pair(&entries.ps[1], "beta", 1);
}

// ────────────────────────────── A-S4: lowering-purity probes ──────────────────────────────
//
// The host computes NO values at lowering time: arithmetic lowers to the machine's metered
// `Expr`s; width/precision folds lift into fold-contract trampolines the machine drives at COMM
// time. The probes are byte-level value-absence checks in the A-S3 style (`par_bytes_contain`
// over the prost encoding, with a contrastive control proving needle sensitivity) plus
// machine-computed evidence: without the registered fold contract nothing can produce the value
// (OUT stays empty); with it, OUT carries exactly the fold result.

/// Whether the prost-encoded bytes of `par` contain `needle` (the A-S3 probe helper).
fn par_bytes_contain(par: &Par, needle: &[u8]) -> bool {
    let bytes = par.encode_to_vec();
    bytes.windows(needle.len()).any(|window| window == needle)
}

/// The byte needle for "the ground literal `value` rides this `Par`": the encoded bytes of a bare
/// `GInt` value `Par`. A `Par` embedded in any message field serializes its own content
/// contiguously, so the needle matches wherever the literal value-leaf appears.
fn gint_par_needle(value: i64) -> Vec<u8> {
    new_gint_par(value, Vec::new(), false).encode_to_vec()
}

/// The `GBigInt` twin of [`gint_par_needle`] — signed big-endian two's-complement bytes.
///
/// ★ CORRECTED 2026-07-25 (divergence I). The comment that stood here said "plain rholang integer
/// literals lex to `BigInt` (the Rholang 1.4 arbitrary-precision default)". That was FALSE:
/// f1r3node's `normalize_ground` maps a bare numeral to `GInt`, and only the `…n` spelling to
/// `GBigInt`. Rholang's grammar now agrees, so plain operands ride as `GInt` and this needle is
/// used for the `…n` spelling.
fn gbigint_par_needle(value: i64) -> Vec<u8> {
    Par::default()
        .with_exprs(vec![models::rust::utils::new_gbigint_expr(
            num_bigint::BigInt::from(value).to_signed_bytes_be(),
        )])
        .encode_to_vec()
}

/// A-S4 deliverable-3 probe (Rholang arithmetic): the RAW parse tree `@("OUT")!(1 + 2 * 3)`
/// lowers to metered machine `Expr`s — the injected call carries the OPERANDS but NOT the result
/// literal `7` (no host pre-computation), and the machine's send-data evaluation produces `7` on
/// OUT.
#[tokio::test]
async fn a_s4_raw_arithmetic_lowers_to_metered_exprs_and_the_machine_computes_the_value() {
    let par = parse_lower(r#"@("OUT")!(1 + 2 * 3)"#);

    // Value absence: the call embeds 1, 2, 3 (the operands, `GInt` literals — divergence I) and
    // not 7 (the result) in either ground encoding.
    assert!(par_bytes_contain(&par, &gint_par_needle(1)), "operand 1 rides the call");
    assert!(par_bytes_contain(&par, &gint_par_needle(2)), "operand 2 rides the call");
    assert!(par_bytes_contain(&par, &gint_par_needle(3)), "operand 3 rides the call");
    assert!(
        !par_bytes_contain(&par, &gbigint_par_needle(7))
            && !par_bytes_contain(&par, &gint_par_needle(7)),
        "A-S4: no host-pre-computed value may ride the injected call Par"
    );
    // Contrastive control: a call that DOES embed the literal is matched by the needle — the
    // probe is sensitive.
    let literal_par = parse_lower(r#"@("OUT")!(7)"#);
    assert!(
        par_bytes_contain(&literal_par, &gint_par_needle(7)),
        "the needle detects an embedded literal (control)"
    );
    // The `GBigInt` needle is still live — it is what the `…n` spelling produces. Asserting it
    // here keeps BOTH needles proven-sensitive, so the switch above cannot be a silent weakening.
    let bigint_par = parse_lower(r#"@("OUT")!(7n)"#);
    assert!(
        par_bytes_contain(&bigint_par, &gbigint_par_needle(7)),
        "the GBigInt needle detects the `…n` spelling (control)"
    );

    // The MACHINE computes: the metered send-data evaluation reduces `1 + 2 * 3` to 7 on OUT
    // (a `GInt` value — plain literals are `normalize_ground`'s `GInt`, divergence I).
    let values = run_normalized_par_for_oracle_and_read_runtime_values(&par, "OUT")
        .await
        .expect("the metered expression call executes on the Rho machine");
    assert_eq!(values, vec![RuntimeObservationValue::Int(7)], "1 + 2 * 3 = 7, machine-computed");
}

/// A-S4 string-concat parity: Rholang `+` on ground strings is Rholang `++` (`EPlusPlus`) — the
/// machine concatenates; the host does not.
#[tokio::test]
async fn a_s4_ground_string_add_lowers_to_eplusplus_and_concatenates_on_machine() {
    let source = r#"@("OUT")!("con" + "cat")"#;
    assert_eq!(read_strings(source).await, vec!["concat".to_string()]);
}

/// A-S4 deliverable-3 probe (Rholang width cast): `@("OUT")!(int(2 + 3, 8))` lifts the fold into
/// a fold-contract trampoline. Three-part machine-computed evidence (A-S3 style):
///   1. VALUE ABSENCE — the call carries the operands (2, 3) but not the folded value 5;
///      the contrastive control (an explicit `@("OUT")!(5)`) proves needle sensitivity;
///   2. WITHOUT the registered fold `Definition` the value cannot appear (OUT stays EMPTY —
///      nothing else can fabricate it);
///   3. WITH the production wrapper (which drains + registers the recorded fold contract), the
///      machine's trampoline COMM computes `int(5, 8) = 5` and OUT carries exactly it.
#[tokio::test]
async fn a_s4_ground_width_fold_value_is_computed_by_the_fold_contract_at_comm_time() {
    clear_var_cache();
    let term = RholangLanguage
        .parse_term(r#"@("OUT")!(int(2 + 3, 8))"#)
        .expect("the width-fold send parses");
    let (par, specs) =
        lower_rholang_term_with_folds(term.as_ref()).expect("the ground fold lifts and lowers");

    // The lift recorded exactly one Int-width-8 fold site.
    assert_eq!(specs.len(), 1, "one fold ⇒ one fold-contract spec");
    assert_eq!(specs[0].kind, FoldKind::Int);
    assert_eq!(specs[0].width, 8);

    // (1) Value absence + operand presence, with the contrastive control. The operands are
    // `GInt` literals (divergence I), as is the folded result (the `int(·, w)` class) — assert
    // the value 5 is absent in BOTH ground encodings.
    assert!(par_bytes_contain(&par, &gint_par_needle(2)), "operand 2 rides the call");
    assert!(par_bytes_contain(&par, &gint_par_needle(3)), "operand 3 rides the call");
    assert!(
        !par_bytes_contain(&par, &gint_par_needle(5))
            && !par_bytes_contain(&par, &gbigint_par_needle(5)),
        "A-S4: the folded value must NOT be pre-computed into the call Par"
    );
    let control = parse_lower(r#"@("OUT")!(5)"#);
    assert!(
        par_bytes_contain(&control, &gint_par_needle(5)),
        "the needle detects an embedded folded value (control)"
    );

    // (2) Without the registered fold contract the trampoline send rests unconsumed: OUT EMPTY.
    let without_contract = run_normalized_par_for_oracle_and_read_runtime_values(&par, "OUT")
        .await
        .expect("the lifted call runs (inertly) without the fold Definition");
    assert!(
        without_contract.is_empty(),
        "no component but the registered fold contract can produce the value \
         (got {without_contract:?})"
    );

    // (3) With the production wrapper the drained fold Definition is registered and the machine
    // computes the fold at COMM time.
    let language =
        dovetail_rho_backed_rholang("OUT").expect("the dovetail+Rho Rholang wrapper installs");
    let exec_term = language
        .parse_term(r#"int(2 + 3, 8)"#)
        .expect("the pure width-fold term parses");
    let report = language
        .run_default_backend_report(exec_term.as_ref())
        .expect("the fold execs on the Rho machine via the trampoline");
    assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
    let out = report
        .observations_for_channel("OUT")
        .expect("the machine-computed fold value lands on OUT");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Int(5)],
        "int(2 + 3, 8) = 5, computed by the fold contract on the machine"
    );
}

/// A-S4 deliverable-1a: with the E2 Dovetail fold-normalization fallback DELETED, a construct
/// with no machine algebra fails CLOSED with the typed lowering error NAMING it (here the
/// bitwise operator, which has no Rholang `Expr`).
#[test]
fn a_s4_unlowerable_construct_fails_closed_with_a_named_typed_error() {
    clear_var_cache();
    let proc = Proc::parse_via_wpda("5 bitand 3").expect("the bitand term parses");
    let err = lower_rholang_proc(&proc)
        .expect_err("bitand has no Rholang bitwise Expr; the lowering must fail closed");
    match err {
        RholangAstLowerError::UnsupportedProc(name) => {
            assert!(name.contains("bitand"), "the typed error names the construct, got {name:?}");
        },
        other => panic!("expected a typed UnsupportedProc naming the construct, got {other:?}"),
    }
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
