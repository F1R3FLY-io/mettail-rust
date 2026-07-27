//! Stage 3e end-to-end: a GENERATED integer calculator's NATIVE SYSTEM PROCESS fires end-to-end
//! as a COMM on the live f1r3node Rholang interpreter, emitting the value a TRUSTED native handler
//! computed.
//!
//! `NativeDemo` is a generated `language!` whose only reducing rule is the native exponentiation
//! `PowInt(a, b) ~> a^b` (written `a "^" b` in the DSL, a `![a.pow(b as u32)] fold` HOL term). The
//! `^` operator has no in-Rho scalar contract, so the Rho scalar lowering REJECTS it and classifies
//! it as a `RhoNetRuleKind::NativeSystemProcess` (the native-dispatch family, D2(e)) — its value is
//! computed by the host's TRUSTED native handler (the Dovetail `fold` body), not by an in-Rho
//! scalar contract. The pipeline exercised here is the NATIVE-DISPATCH analogue of the base-rewrite
//! σ-injection (`rho_net_equivalence.rs`), the AC firing (`rho_net_ac_firing.rs`), the contextual
//! join (`rho_net_contextual_firing.rs`), and the binder/β-substitution (`rho_net_beta_firing.rs`):
//!
//!  1. [`NativeDemoLanguage::dovetail_report_for`] saturates the redex `2 ^ 3`: the `Int_PowInt`
//!     native rule fires and the host (Dovetail, model-b) matches `PowInt(2, 3)` AND computes the
//!     native value `8` via its trusted `fold` handler, so the sole `rewrite_justifications` entry
//!     is the `Int_PowInt` firing whose CONTRACTUM is the reduced value `8` (`NumLit(8)`);
//!  2. the generated [`NativeDemoLanguage::rho_net_invocation_from_dovetail_to`] σ-injection
//!     F-function (its native arm — base | AC | contextual | subst | native) reflects that
//!     contractum and assembles `c_pow!(⟦NumLit(8)⟧, @OUT)` via `term_contract_call`, where `c_pow`
//!     is the `PowInt` dispatch receiver's source channel;
//!  3. the runtime bridge runs `installed_rho_net_program_par() ∥ call` on the f1r3node
//!     RhoRuntime, where the installed `NativeSystemProcessRewrite` dispatch receiver
//!     (`for([result, out] <- c_pow){ out!(result) }`) forwards the delegated value on `@OUT` —
//!     one atomic COMM (INV-3).
//!
//! `2 ^ 3` reduces to `8`, and `2 ^ 3 ≠ 8` structurally, so a positive OUT observation is
//! non-vacuous evidence the native system process fired as a COMM with the value the trusted
//! handler computed (the computation is host-side — model-b — exactly as the base/AC/contextual/
//! binder arms, and the firing itself runs on the reducer). The structural rendezvous (the COMM on
//! `PowInt`'s dedicated dispatch channel) is real; only the PAYLOAD is delegated to the handler.
//!
//! FV: `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v` (the native dispatch is
//! total-or-reject, and the emitted payload is exactly the trusted handler's value — the encoder
//! delegates, never fabricates) + the trust boundary `RhoHostObligationBoundary.v` + the inherited
//! flat-receiver correspondence (`LinearCommCorrespondence.v`) and install boundary
//! (`RhoLoweringTotalOrRejects.v`).
#![cfg(feature = "native-demo-runtime")]

// Task #11 (extended 2026-07-26): `NativeDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/nativedemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `nativedemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/nativedemo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/nativedemo.rs"]
mod nativedemo;

use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::{
    build_rho_net_injection_invocation_from_contract, PlannedRhoBackend, RhoMachineInvocation,
};
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};
use nativedemo::NativeDemoLanguage;
use prost::Message;

/// Reconstruct NativeDemo's augmented `LanguageDef` from the generated metadata's
/// `definition_source()` and plan its Rho-default backend (the `PowInt`
/// `NativeSystemProcessRewrite` dispatch receiver installs, its rejected native disposition
/// covered), exactly as the Rho/Dovetail installer does. Returns the planned backend and the
/// plan's definition fingerprint (which must equal the generated metadata fingerprint the native
/// injection reflects the contractum with).
fn native_demo_backend() -> (PlannedRhoBackend, String) {
    let source = NativeDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated NativeDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("NativeDemoLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("NativeDemo (PowInt native system process) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The generated native σ-injection fires the installed `PowInt` dispatch receiver as ONE COMM,
/// landing the trusted handler's value `8` on OUT. This is the NATIVE-DISPATCH analogue of
/// `dovetail_report_semantics_match_rho_machine_execution_for_swap` (base) and
/// `lambdademo_beta_reduction_fires_as_a_comm_on_the_reducer` (binder): INV-3, a native system
/// process firing as a COMM on the reducer with a host-computed native value.
#[tokio::test]
async fn nativedemo_native_system_process_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = native_demo_backend();

    // Fingerprint coherence: the installed `PowInt` dispatch receiver (from the reconstructed def)
    // and the native σ-injection (which reflects the contractum with
    // `metadata().definition_fingerprint()`) must agree, or the forwarded value would decode
    // inconsistently.
    assert_eq!(
        NativeDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    // The concrete redex `2 ^ 3` = `PowInt(2, 3)`, parsed through the generated parser. `8 ≠ 2^3`
    // structurally, so a positive OUT observation is non-vacuous evidence the native process fired.
    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    // (1) DOVETAIL REPORT SEMANTICS: the `Int_PowInt` native rule fires and the host computes the
    // native value via its trusted `fold` handler, so the acyclic reduction is Complete with
    // EXACTLY the single `Int_PowInt` firing, whose CONTRACTUM is the reduced value `8`.
    let report = NativeDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("NativeDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic native reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one native firing fires for 2 ^ 3, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(
        justification.rule_label, "Int_PowInt",
        "the fired rule is the PowInt native process (op-variant identity Int_PowInt)"
    );

    // The firing's contractum IS the host-computed native value `8` — the whole point of model-b:
    // the value is computed host-side by the TRUSTED native handler and handed to the σ-injection.
    let eight = RuntimeReflectedSubterm {
        constructor: "NumLit(8)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        justification.contractum.as_ref(),
        Some(&eight),
        "the PowInt firing's contractum is the reduced value 8 the trusted handler computed, got {:?}",
        justification.contractum
    );

    // (2) The generated σ-injection F-function (native arm) reflects the contractum and assembles
    // `c_pow!(⟦NumLit(8)⟧, @OUT)` for the `PowInt` dispatch receiver.
    let invocation =
        NativeDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("NativeDemo native injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    // The Epic-4 bridge selects the INSTALLED-σ-receiver observation shape so the receiver fires.
    match build_rho_net_injection_invocation_from_contract(invocation.clone()) {
        RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
            assert_eq!(out_channel, "OUT", "the bridge must preserve the out channel");
        },
        other => panic!("the native injection must map to RunRhoNet…, got {other:?}"),
    }

    // (3) RHO-MACHINE EXECUTION: run the installed program (the `PowInt` dispatch receiver) ∥ call,
    // and observe OUT. The receiver binds the delivered value and forwards it on `@OUT` — one
    // atomic COMM (INV-3).
    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the native injection must execute on the Rho runtime");

    // Non-vacuity: the dispatch receiver fired exactly once and left exactly one value on OUT.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the native dispatch receiver must fire (got {:?})",
        observation.values
    );

    // EQUIVALENCE: the Rho machine landed the reduced value `8` (its reflected `NumLit(8)` image),
    // the native normal form, non-vacuous against the input `2 ^ 3`.
    let eight_value = RuntimeObservationValue::Term {
        constructor: "NumLit(8)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], eight_value,
        "the native system process fired as a COMM on the reducer and landed the value 8"
    );
}

/// S-native (Stage 4) — the DECISIVE probe that the native redex LOCATION is produced by the `sa:`
/// automaton, NOT by the host report. The native-dispatch analogue of the base
/// `m_reflect_sigma_is_produced_by_the_automaton_not_the_report`.
///
/// We take a real, complete report for `2 ^ 3` and CORRUPT its σ (the matched-subterm record — the
/// LOCATION) to nonsense (`{a ↦ NumLit(999), b ↦ NumLit(999)}`), leaving the rule label
/// (`Int_PowInt`) and the native VALUE (the contractum `NumLit(8)`) valid — so the gate / single
/// native firing checks still admit the MATCH path. The Stage-4 `rho_net_match_invocation_from_dovetail_to`
/// STRUCTURALLY reflects the WHOLE subject `2 ^ 3` = `PowInt(NumLit(2), NumLit(3))` (M-reflect, NOT
/// the report σ), the positional automaton LOCATES that `PowInt` App head + CAPTURES its args ON the
/// reducer, and its located accept GATES the value bridge, which forwards the trusted handler's
/// value (the contractum) on the dispatch channel → `NumLit(8)` on OUT.
///
/// Because the subject — and hence the redex LOCATION — is built from `term`, not from the corrupted
/// report σ, OUT is the CORRECT `NumLit(8)`. A location read from the report would have matched the
/// nonsense σ and never located the real `PowInt`. So a positive, correct OUT observation is
/// non-vacuous evidence the location came from the automaton, not the report. The native VALUE stays
/// the trusted host handler's payload (the contractum — the inherent `NativeSystemProcessBoundary`:
/// BigInt / pow / factorial is outside Rho's own arithmetic); ONLY the structural dispatch moved in
/// Rho.
///
/// FV: `NativeSystemProcessBoundary.v` (the `match_emit` location boundary — the emitted value is
/// invariant under the report σ and tracks the handler value) + `InRhoMatchPositional.v` (the native
/// App head is located + positionally captured, and the delivered value is gated + delegated).
#[tokio::test]
async fn s_native_location_is_produced_by_the_automaton_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = native_demo_backend();

    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    let mut report = NativeDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("NativeDemo Dovetail report must compile");
    assert_eq!(report.rewrite_justifications.len(), 1, "2 ^ 3 fires exactly one native rewrite");

    // Deliberately WRONG σ (the matched-subterm LOCATION): a report-σ locator would key off these
    // and never find the real PowInt(NumLit(2), NumLit(3)). The rule label + contractum (the native
    // VALUE) stay valid — only the LOCATION σ is corrupted.
    let nonsense = RuntimeReflectedSubterm {
        constructor: "NumLit(999)".to_string(),
        children: Vec::new(),
    };
    for justification in &mut report.rewrite_justifications {
        justification.sigma =
            vec![("a".to_string(), nonsense.clone()), ("b".to_string(), nonsense.clone())];
        assert_eq!(
            justification.rule_label, "Int_PowInt",
            "the fired rule label (the location-independent identity) stays valid"
        );
        assert_eq!(
            justification.contractum,
            Some(RuntimeReflectedSubterm {
                constructor: "NumLit(8)".to_string(),
                children: Vec::new(),
            }),
            "the native VALUE (contractum) stays the trusted handler's payload"
        );
    }

    // The MATCH path (M-reflect + locate) admits the native redex despite the corrupted σ, and the
    // automaton LOCATES PowInt from the reflected subject `term`.
    let invocation = NativeDemoLanguage::rho_net_match_invocation_from_dovetail_to(
        term.as_ref(),
        &report,
        "OUT",
    )
    .expect("the MATCH path admits 2 ^ 3 with a corrupted report σ");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho native match + firing executes on the reducer");

    // Non-vacuity: the automaton located PowInt and the value bridge fired exactly once.
    assert_eq!(
        observation.observed_count(),
        1,
        "OUT must carry exactly one value — the located native dispatch must fire (got {:?})",
        observation.values
    );

    // The Rho machine landed the reduced value `8` — located by the automaton (from `term`), valued
    // by the trusted handler (the contractum), NOT by the corrupted report σ.
    let eight_value = RuntimeObservationValue::Term {
        constructor: "NumLit(8)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], eight_value,
        "the native redex was LOCATED by the sa: automaton (from the reflected term, not the \
         corrupted report σ), and the handler's value 8 was delivered on OUT"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// A-S3 (native dispatch boundary tightening): the ADMITTED report-free native path — the
// MACHINE invokes the registered trusted handler at COMM time; no host-pre-computed value
// rides the call `Par`, and there is NO report at all.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// Replace every occurrence of `needle` with `replacement` (same length — protobuf length
/// prefixes stay valid) in the prost-encoded bytes of `par`, and decode back. The reflected-term
/// tags are UTF-8 strings embedded verbatim in the encoded `Par`, so a same-length tag rewrite
/// corrupts EVERY occurrence (the spread's `loc:` head publications and `cap:` collapse values
/// alike) — a CONSISTENTLY corrupted spread, as if the automaton had been handed a different
/// subject.
fn corrupt_par_bytes(
    par: &models::rhoapi::Par,
    needle: &[u8],
    replacement: &[u8],
) -> models::rhoapi::Par {
    assert_eq!(
        needle.len(),
        replacement.len(),
        "same-length replacement keeps the protobuf length prefixes valid"
    );
    let mut bytes = par.encode_to_vec();
    let mut index = 0;
    let mut replaced = 0;
    while index + needle.len() <= bytes.len() {
        if &bytes[index..index + needle.len()] == needle {
            bytes[index..index + needle.len()].copy_from_slice(replacement);
            replaced += 1;
            index += needle.len();
        } else {
            index += 1;
        }
    }
    assert!(replaced > 0, "the corruption probe must actually rewrite something");
    models::rhoapi::Par::decode(bytes.as_slice()).expect("the corrupted bytes re-decode as a Par")
}

/// Whether the prost-encoded bytes of `par` contain `needle` (an ASCII tag fragment).
fn par_bytes_contain(par: &models::rhoapi::Par, needle: &[u8]) -> bool {
    let bytes = par.encode_to_vec();
    bytes.windows(needle.len()).any(|window| window == needle)
}

/// A-S3 CORE + trusted-handler probe (lazily-absent report): the REPORT-FREE compile
/// (`rho_net_match_invocation_to`) ADMITS the located native redex `2 ^ 3` — no deferral, no
/// report anywhere — and the value `8` is produced by the REGISTERED HANDLER at COMM time, not
/// by any host pre-computation:
///
/// 1. the admitted call `Par` does NOT embed the value (`NumLit(8)` is absent from its bytes),
///    while the REPORT path's value-bridge call DOES embed it (the contrastive control that
///    proves the probe is sensitive) — so on the admitted path nothing host-side computed `8`;
/// 2. running the admitted call WITHOUT the registered handler `Definition`s leaves OUT EMPTY —
///    no other component can fabricate the value;
/// 3. running it WITH the drained `Definition`s lands exactly `NumLit(8)` — the machine's
///    dispatch COMM invoked the trusted evaluator (`a.pow(b as u32)` on the located σ) and the
///    rule's σ-receiver consumed the RETURNED value.
#[tokio::test]
async fn a_s3_admitted_native_value_is_computed_by_the_registered_handler_at_comm_time() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = native_demo_backend();

    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    // The REPORT-FREE compile ADMITS (A-S3): located native sites register handler specs
    // instead of deferring. Bracket the pending registry ourselves (the production wrapper's
    // clear/drain bracket, inlined for the probe).
    mettail_rholang_codegen::clear_pending_native_handler_specs();
    let invocation = NativeDemoLanguage::rho_net_match_invocation_to(term.as_ref(), "OUT")
        .expect("A-S3: the report-free match must ADMIT a located native redex");
    let specs = mettail_rholang_codegen::take_pending_native_handler_specs();
    assert_eq!(specs.len(), 1, "one located native rule registers one handler spec");
    assert_eq!(specs[0].fired_rule_label, "Int_PowInt");
    assert_eq!(specs[0].bare_label, "PowInt");
    assert_eq!(specs[0].arity, 2);
    assert!(
        specs[0].urn.starts_with("mtl:native:") && specs[0].urn.ends_with(":Int_PowInt"),
        "the URN rides the mtl:native:{{fingerprint}}:{{label}} band, got {}",
        specs[0].urn
    );

    // (1) VALUE ABSENCE: the admitted call carries the subject (`NumLit(2)`, `NumLit(3)`) but
    // NOT the value `NumLit(8)` — the host computed nothing.
    assert!(
        par_bytes_contain(&invocation.call, b"NumLit(2)"),
        "the reflected subject rides the call"
    );
    assert!(
        !par_bytes_contain(&invocation.call, b"NumLit(8)"),
        "A-S3: no host-pre-computed value may ride the admitted call Par"
    );
    // Contrastive control: the REPORT path's value bridge DOES embed the host value — the
    // probe is sensitive, and the deferral path is byte-compatibly unchanged.
    let report = NativeDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("NativeDemo Dovetail report must compile");
    let report_invocation = NativeDemoLanguage::rho_net_match_invocation_from_dovetail_to(
        term.as_ref(),
        &report,
        "OUT",
    )
    .expect("the report-carrying match still admits");
    assert!(
        par_bytes_contain(&report_invocation.call, b"NumLit(8)"),
        "the report path's value bridge embeds the host-computed contractum (the D-stage lane)"
    );

    // (2) WITHOUT the registered handler Definitions the value cannot appear: the trigger
    // accept fires into the contract-call bridge, whose send rests unconsumed on the reserved
    // contract channel — OUT stays EMPTY (nothing else can produce the value).
    let without_handlers = backend
        .run_rho_net_with_call_definitions_and_observe_runtime_values(
            &invocation.call,
            Vec::new(),
            &invocation.out_channel,
        )
        .await
        .expect("the admitted call runs (inertly) without the handler Definitions");
    assert_eq!(
        without_handlers.observed_count(),
        0,
        "no component but the registered handler can produce the native value (got {:?})",
        without_handlers.values
    );

    // (3) WITH the Definitions, the machine's COMM invokes the trusted evaluator at COMM time
    // and the σ-receiver consumes the RETURNED value: OUT = NumLit(8).
    let definitions = mettail_rholang_runtime::native_definitions_for(&specs)
        .expect("#36 S4/S5: the band allocation is pairwise distinct for a single language");
    let observation = backend
        .run_rho_net_with_call_definitions_and_observe_runtime_values(
            &invocation.call,
            definitions,
            &invocation.out_channel,
        )
        .await
        .expect("the admitted native call executes with the registered handler installed");
    assert_eq!(
        observation.observed_count(),
        1,
        "the dispatch COMM must fire the handler exactly once (got {:?})",
        observation.values
    );
    let eight_value = RuntimeObservationValue::Term {
        constructor: "NumLit(8)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], eight_value,
        "the observed value is the REGISTERED HANDLER's computation (2^3 = 8) at COMM time"
    );
}

/// A-S3 wrong-σ probe: corrupt the SPREAD (the reflected subject inside the admitted call
/// `Par`: every `NumLit(2)` tag → `NumLit(5)`) and run with the SAME registered handler — the
/// handler computes from the OPERANDS THE MACHINE DELIVERS, so the observed value tracks the
/// corrupted σ (`5 ^ 3 = 125`), not any value fixed at compile time. Together with the honest
/// run (`8`), this proves the fired value is a genuine function of the COMM-delivered σ — the
/// dispatch is directed compute ON the machine, not a ferried constant.
#[tokio::test]
async fn a_s3_wrong_sigma_probe_handler_computes_from_the_delivered_operands() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = native_demo_backend();

    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    mettail_rholang_codegen::clear_pending_native_handler_specs();
    let invocation = NativeDemoLanguage::rho_net_match_invocation_to(term.as_ref(), "OUT")
        .expect("A-S3: the report-free match must ADMIT a located native redex");
    let specs = mettail_rholang_codegen::take_pending_native_handler_specs();
    assert_eq!(specs.len(), 1, "one located native rule registers one handler spec");

    // Corrupt the spread: every reflected `NumLit(2)` tag becomes `NumLit(5)` (same length, so
    // the protobuf structure is preserved) — the automaton now locates PowInt(5, 3) and
    // captures σ = (5, 3).
    let corrupted = corrupt_par_bytes(&invocation.call, b"NumLit(2)", b"NumLit(5)");

    let definitions = mettail_rholang_runtime::native_definitions_for(&specs)
        .expect("#36 S4/S5: the band allocation is pairwise distinct for a single language");
    let observation = backend
        .run_rho_net_with_call_definitions_and_observe_runtime_values(
            &corrupted,
            definitions,
            &invocation.out_channel,
        )
        .await
        .expect("the corrupted-spread call executes with the registered handler installed");
    assert_eq!(
        observation.observed_count(),
        1,
        "the corrupted spread still locates one PowInt site (got {:?})",
        observation.values
    );
    let one_two_five = RuntimeObservationValue::Term {
        constructor: "NumLit(125)".to_string(),
        children: Vec::new(),
    };
    assert_eq!(
        observation.values[0], one_two_five,
        "the handler computed 5 ^ 3 = 125 from the CORRUPTED machine-delivered σ — the value \
         is a function of the COMM-delivered operands, not a compile-time constant"
    );
}

/// A-S3 zero-D-stage native exec (the runtime-test home of the `zero_dstage_exec` extension —
/// NativeDemo is not REPL-registered): through the PRODUCTION lazy wrapper, an admitted native
/// exec runs with ZERO Dovetail work (`checked_complete_dovetail_report` never runs — counter
/// delta 0) and the observed value equals the registered handler's computation.
#[cfg(feature = "dstage-instrumentation")]
#[test]
fn a_s3_admitted_native_exec_builds_no_dovetail_report() {
    use mettail_rholang_runtime::dstage_instrumentation::dovetail_report_invocations;
    use mettail_rholang_runtime::{
        install_dovetail_rho_runtime_backend_lazy, RhoBackendInvocation, RhoInvocationDeferral,
    };
    use mettail_runtime::{RuntimeBackend, RuntimeDovetailRunReport, Term};

    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = native_demo_backend();

    fn dovetail(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        NativeDemoLanguage::dovetail_report_for(term, 64, 1_000_000)
    }
    fn invocation_free(term: &dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        match NativeDemoLanguage::rho_net_match_invocation_to(term, "OUT") {
            Ok(invocation) => Ok(RhoBackendInvocation::from(
                build_rho_net_injection_invocation_from_contract(invocation),
            )),
            Err(detail) => Err(RhoInvocationDeferral::GateReject { detail }),
        }
    }
    fn invocation(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        let contract =
            NativeDemoLanguage::rho_net_match_invocation_from_dovetail_to(term, report, "OUT")?;
        Ok(RhoBackendInvocation::from(build_rho_net_injection_invocation_from_contract(
            contract,
        )))
    }

    let language = install_dovetail_rho_runtime_backend_lazy(
        NativeDemoLanguage,
        backend,
        dovetail,
        dovetail,
        invocation_free,
        invocation,
    )
    .expect("the NativeDemo lazy Dovetail+Rho wrapper installs");

    let term = NativeDemoLanguage
        .parse_term("2 ^ 3")
        .expect("NativeDemo must parse the native redex 2 ^ 3");

    let before = dovetail_report_invocations();
    let report = language
        .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
        .expect("the admitted native exec runs report-free on the Rho machine");
    let after = dovetail_report_invocations();

    assert_eq!(
        after - before,
        0,
        "an ADMITTED native exec must build ZERO Dovetail reports (A-S3: the machine invokes \
         the registered handler; the D-stage is not consulted)"
    );
    let out = report
        .observations_for_channel("OUT")
        .expect("the admitted native exec observes OUT");
    assert_eq!(
        out.values,
        vec![RuntimeObservationValue::Term {
            constructor: "NumLit(8)".to_string(),
            children: Vec::new(),
        }],
        "the observed value equals the registered handler's computation (2^3 = 8)"
    );
}
