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
/// Tier-3 held-fold trampoline: Dovetail-backed fold contracts for folds over COMM-received values.
#[cfg(feature = "rhocalc-runtime")]
pub mod fold_contract;
#[cfg(feature = "rhocalc-runtime")]
pub mod rhocalc_ast;
pub mod run;
/// Reactive single-step COMM stepper (the `step` command's live Rho-machine evidence).
#[cfg(feature = "runtime-report")]
pub mod step;
#[cfg(feature = "runtime-report")]
pub use backend::{
    build_fold_dataflow_invocation_from_contract,
    build_rho_net_injection_invocation_from_contract,
    build_rho_net_replay_invocation_from_contracts, build_scalar_contract_invocation,
    build_scalar_contract_invocation_from_contract, install_dovetail_rho_runtime_backend,
    install_rho_runtime_backend, DovetailCompilerStage, DovetailRhoRuntimeBackedLanguage,
    IntoRuntimeObservationValue, RhoBackendInvocation, RhoInvocationCompilerStage,
    RhoInvocationExecutionSite, RhoMachineInvocation, RhoRuntimeBackedLanguage,
    RhoRuntimeBackedLanguageError, RhoScalarInvocationError, RhoScalarInvocationLiteralType,
    RuntimeReportConversionError,
};
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
pub use mettail_rholang_codegen::{REFLECTED_TERM_ABI_PREFIX, RHOCALC_BAG_ABI_TAG};
#[cfg(feature = "rhocalc-runtime")]
pub use rhocalc_ast::{
    dovetail_rho_backed_rhocalc, lower_rhocalc_name, lower_rhocalc_proc, lower_rhocalc_term,
    rho_runtime_backed_rhocalc_ints, rho_runtime_backed_rhocalc_strings,
    rho_runtime_backed_rhocalc_values, rhocalc_ast_runtime_def, rhocalc_observe_ints_invocation,
    rhocalc_observe_strings_invocation, rhocalc_observe_values_invocation,
    rhocalc_planned_rho_backend, RhocalcAstLowerError, RhocalcAstRuntimeLanguage,
    RhocalcInvocationMapper, RhocalcRuntimeBackedLanguage, RhocalcRuntimeBackedLanguageResult,
};
#[cfg(feature = "runtime-report")]
pub use run::{
    par_as_runtime_observation_value, run_normalized_par_for_oracle_and_read_runtime_values,
    run_validated_program_and_read_runtime_values,
    run_validated_program_with_call_and_read_runtime_values,
};
pub use run::{
    run_normalized_par_for_oracle, run_normalized_par_for_oracle_and_read_bools,
    run_normalized_par_for_oracle_and_read_ints,
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
pub use step::StepSession;
