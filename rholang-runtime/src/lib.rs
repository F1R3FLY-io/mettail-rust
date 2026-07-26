//! # mettail-rho-runtime — bind the generated VM to f1r3node's Rho machine
//!
//! Binds the `mettail-rho-codegen` output to f1r3node-rust's process-wide
//! `RhoRuntime` / `DebruijnInterpreter` (+ a `Vec<Definition>` of native system
//! handlers), and hosts explicit **differential oracle** checks against
//! Ascent-shaped reference evidence.
//!
//! **Threading/scheduling are OWNED BY f1r3node** — `eval_par` (`tokio::spawn`
//! per `P|Q`) + RSpace disjoint-channel COMMs on the work-stealing runtime.
//! MeTTaIL's eval job collapses to "emit `Par` (independent redexes = parallel
//! members) + channel-keying for disjointness" — emit `Par`, never fork.
//!
//! The differential oracle compares Rho observations against an explicitly
//! installed `Language::run_ascent(term)?.normal_forms()` reference, under
//! **weight-erasure + eqrel-quotient**, keyed by `dovetail::key::ContentKey`
//! (exact bytes — never a 64-bit hash), honoring "miss nothing": weights order,
//! never prune; refute only at `0̄`.
//!
//! ## Dependency direction (STRICTLY one-way)
//! Depends ONE-WAY on f1r3node-rust; never the reverse (proven in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`; enforced by the host
//! guard test `mettail_rust_is_not_a_cargo_dependency`).
//!
//! ## Status
//! Integrated bridge runtime. It injects generated normalized `rhoapi::Par`
//! programs directly through `RhoRuntime::inj`, exposes `PlannedRhoBackend` as
//! the flip-gated generated execution boundary, keeps raw `ValidatedRhoProgram`
//! helpers for oracle/debug code, exposes `PlannedCallByNeedThunk` as the
//! M-RHO.2 need-specific planned execution boundary, keeps source-text evaluation only for
//! hand-authored host oracle tests, reads public resting data for oracle checks,
//! runs lowered calculator contracts against an explicit Ascent oracle baseline,
//! and hosts the M-RHO.1 transport-pure COMM oracle. Hand-authored Rholang
//! source evaluation helpers are available only behind the `source-oracle`
//! feature; generated backend execution is always AST-first and enters through
//! validated `rhoapi::Par` artifacts. The Ascent oracle was retired with the
//! legacy backend in P6 once every target language passed its coverage,
//! artifact-validation, and deadlock gates. The
//! default `runtime-report` feature exposes the generic `Language`
//! report-adapter and Dovetail+Rho installer surface. Generated language
//! fixtures, the RhoCalc AST-runtime helper, and source-text oracle helpers
//! remain opt-in through `rhocalc-runtime` and `source-oracle`.

#![forbid(unsafe_code)]

pub mod backend;
/// Track-B benchmark support (B3 fair-comparison hoisting + B4 COMM/match/cost
/// instrumentation) — BENCHMARK-ONLY, quarantined behind `bench-naive-baseline`.
/// No production metering/budget surface: budgets are F1r3node's (wallet.txt).
#[cfg(feature = "bench-naive-baseline")]
pub mod bench_support;
/// E-6a (pgmcp experiment 145): PathMap-backed SUBJECT INDEXING for in-Rho
/// matching — BENCHMARK-ONLY treatment-arm support, quarantined behind
/// `bench-naive-baseline` exactly like `bench_support`. No production surface.
#[cfg(feature = "bench-naive-baseline")]
pub mod e6a_support;
/// Tier-3 held-fold trampoline: Dovetail-backed fold contracts for folds over COMM-received values.
#[cfg(feature = "rhocalc-runtime")]
pub mod fold_contract;
/// COMPILE-TIME GUARD DISCHARGE (D0): deciding a binder-closed `where`-guard at lowering and
/// recording the decision by OMITTING `Receive.condition` — which f1r3node's `check_commit`
/// already short-circuits on. Front-end independent (the host redundancy leg is supplied by the
/// caller), so it is available in every feature configuration.
pub mod guard_discharge;
/// ★ THE `where` → Dovetail/SFT WIRE, lowered half: the `rhoapi::Par` →
/// [`mettail_prattail::guard_formula::GuardFormula`] encoder and the substrate's compile-time
/// verdict — the AUTHORITY leg of [`guard_discharge::classify`].
///
/// A second *encoder*, deliberately not a second *decider*: it targets the same substrate
/// vocabulary the surface encoder (`mettail_languages::rhocalc::guard_substrate`) does, so both
/// legs of a guard's life ask the same procedures.
pub mod guard_par_substrate;
/// A-S3 registered native-handler contracts: the machine-invoked trusted evaluator `Definition`s
/// for admitted `fold` native rules (the held-fold trampoline generalized — same
/// `extra_system_processes` seam, reserved `[0xF1, rule]` band).
pub mod native_contract;
#[cfg(feature = "rhocalc-runtime")]
pub mod rhocalc_ast;
/// M-1b: the FORMULA compiler — a RhoCalc `Proc` read as a Rholang PATTERN
/// (§18.1). The right operand of `matches` goes through here; the left operand
/// and everything else goes through [`rhocalc_ast`].
#[cfg(feature = "rhocalc-runtime")]
pub mod rhocalc_formula;
/// **Stage 1 of the `[*]` speculation space fork** — `SpeculativeSandbox`: a fresh in-memory
/// tuplespace whose reducer STAGES every produce/consume so nothing fires until a rendezvous is
/// named, plus `E(S)` (the enabled rendezvous set), the named firing, and the exact state install.
/// Branching is pinned to 1: this is the mechanism, not the search. See the module header for the
/// four measured corrections it is built around and for what the on-chain decision fixed.
pub mod speculation;
pub mod run;
/// Reactive single-step COMM stepper (the `step` command's live Rho-machine evidence).
#[cfg(feature = "runtime-report")]
pub mod step;
#[cfg(feature = "runtime-report")]
pub use backend::{
    build_fold_dataflow_invocation_from_contract,
    build_rho_net_drive_invocation_from_contract,
    build_rho_net_injection_invocation_from_contract,
    build_rho_net_replay_invocation_from_contracts, build_scalar_contract_invocation,
    build_scalar_contract_invocation_from_contract, install_dovetail_rho_runtime_backend,
    install_dovetail_rho_runtime_backend_lazy, install_rho_runtime_backend, DovetailCompilerStage,
    DovetailRhoRuntimeBackedLanguage, IntoRuntimeObservationValue,
    LazyDovetailRhoRuntimeBackedLanguage, RhoBackendInvocation, RhoInvocationCompilerStage,
    RhoInvocationDeferral, RhoInvocationExecutionSite, RhoMachineInvocation,
    RhoRuntimeBackedLanguage, RhoRuntimeBackedLanguageError, RhoScalarInvocationError,
    RhoScalarInvocationLiteralType, RuntimeReportConversionError,
};
#[cfg(feature = "dstage-instrumentation")]
pub use backend::dstage_instrumentation;
pub use backend::{
    PlannedCallByNeedThunk, PlannedRhoBackend, RhoExecutionBoundary, RhoObservationReport,
};
#[cfg(feature = "bench-naive-baseline")]
pub use bench_support::{
    bench_inj_and_read, bench_runtime_with_counters, compile_bench_language, count_receive_nodes,
    BenchRunResult, BenchWorkloadParams, CommChannelClass, CommCounterSnapshot, CommCounters,
    CompiledBenchLanguage, CountingSpace, MatchAttemptCounters, MatchAttemptSnapshot,
    MAX_UNKNOWN_CHANNEL_SAMPLES,
};
/// E-1 scion grafting (pgmcp experiment 147): the L2 A/B measurement surface —
/// BENCHMARK-ONLY, quarantined behind `bench-scion`.
#[cfg(feature = "bench-scion")]
pub use bench_support::{
    corrupt_reflected_label, drive_arm_with_counters, scion_arm_programs, ScionArmPrograms,
};
#[cfg(feature = "bench-naive-baseline")]
pub use e6a_support::{
    build_pathmap_index, count_send_nodes, decode_sites_par, discovery_call_par,
    drive_e6a_treatment, e6a_entry_root_ops, e6a_index_channel, e6a_node_count,
    e6a_omitted_value_locations, e6a_sites_channel, e6a_tag_string, entry_query_match_par,
    entry_query_shape, pathmap_spread_term_par, sites_non_ancestral, E6aDriveFailure,
    E6aDriveOutcome, EntryQueryShape, PathmapIndex,
};
pub use mettail_rholang_codegen::{REFLECTED_TERM_ABI_PREFIX, RHOCALC_BAG_ABI_TAG};
pub use native_contract::{
    native_definition, native_definitions_for, par_to_ground_term, NativeContractError,
};
pub use guard_discharge::{
    all_operands_ground, classify as classify_guard_discharge, is_binder_closed, machine_verdict,
    GuardDischarge, GuardDischargeReport, GuardRouting, GuardStaticallyFalse, LoweringOptions,
    GUARD_DISCHARGE_TARGET,
};
#[cfg(feature = "rhocalc-runtime")]
pub use rhocalc_ast::{
    clear_guard_discharge_report, dovetail_rho_backed_rhocalc, lower_rhocalc_name,
    lower_rhocalc_proc, lower_rhocalc_proc_with_options, lower_rhocalc_proc_with_resolver,
    lower_rhocalc_proc_with_resolver_and_options, lower_rhocalc_term,
    take_guard_discharge_report,
    lower_rhocalc_term_with_folds, rho_runtime_backed_rhocalc_ints, rho_runtime_backed_rhocalc_strings,
    rho_runtime_backed_rhocalc_values, rhocalc_ast_runtime_def, rhocalc_observe_ints_invocation,
    rhocalc_observe_strings_invocation, rhocalc_observe_values_invocation,
    rhocalc_planned_rho_backend, RhocalcAstLowerError, RhocalcAstRuntimeLanguage,
    RhocalcInvocationMapper, RhocalcRuntimeBackedLanguage, RhocalcRuntimeBackedLanguageResult,
};
#[cfg(feature = "runtime-report")]
pub use run::{
    binder_apply_redex_present, drive_cross_check, flatten_observation_value,
    par_as_runtime_observation_value,
    run_installed_program_with_call_and_read_observation_set,
    run_normalized_par_for_oracle_and_read_runtime_value_channels,
    run_normalized_par_for_oracle_and_read_runtime_values,
    run_validated_program_and_read_runtime_values,
    run_validated_program_with_call_and_read_runtime_values, DriveCrossCheckError,
    DriveNfScan, DriveObservationChannels, DriveObservationSet,
};
pub use run::{
    run_normalized_par_for_oracle, run_normalized_par_for_oracle_and_read_bools,
    run_normalized_par_for_oracle_and_read_ints,
    run_normalized_par_for_oracle_and_read_par_channels,
    run_normalized_par_for_oracle_and_read_string_channels,
    run_normalized_par_for_oracle_and_read_string_tuples,
    run_normalized_par_for_oracle_and_read_strings, run_validated_program,
    run_validated_program_and_read_bools, run_validated_program_and_read_ints,
    run_validated_program_and_read_string_channels, run_validated_program_and_read_strings,
    run_validated_program_with_call, run_validated_program_with_call_and_read_bools,
    run_validated_program_with_call_and_read_ints,
    run_validated_program_with_call_and_read_strings,
};
#[cfg(feature = "source-oracle")]
pub use run::{
    run_rholang_source_for_oracle, run_rholang_source_for_oracle_and_read_bools,
    run_rholang_source_for_oracle_and_read_ints, run_rholang_source_for_oracle_and_read_strings,
    run_rholang_source_for_oracle_then_consume_strings,
    run_rholang_source_sequence_for_oracle_and_read_bools,
    run_rholang_source_sequence_for_oracle_and_read_ints,
    run_rholang_source_sequence_for_oracle_and_read_strings,
};
#[cfg(feature = "runtime-report")]
pub use step::{StepSession, TauChannelClassifier};
