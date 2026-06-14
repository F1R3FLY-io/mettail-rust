//! # mettail-rho-runtime — bind the generated VM to f1r3node's Rho machine
//!
//! Binds the `mettail-rho-codegen` output to f1r3node-rust's process-wide
//! `RhoRuntime` / `DebruijnInterpreter` (+ a `Vec<Definition>` of native system
//! handlers), and hosts the **differential oracle** against the Ascent backend.
//!
//! **Threading/scheduling are OWNED BY f1r3node** — `eval_par` (`tokio::spawn`
//! per `P|Q`) + RSpace disjoint-channel COMMs on the work-stealing runtime.
//! MeTTaIL's eval job collapses to "emit `Par` (independent redexes = parallel
//! members) + channel-keying for disjointness" — emit `Par`, never fork.
//!
//! The differential oracle compares the rho-backend normal forms against
//! `Language::run_ascent(term)?.normal_forms()` (the existing baseline the
//! `gen_calculator_op` suite uses), under **weight-erasure + eqrel-quotient**,
//! keyed by `dovetail::key::ContentKey` (exact bytes — never a 64-bit hash),
//! honoring "miss nothing": weights order, never prune; refute only at `0̄`.
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
//! runs lowered calculator contracts against the Ascent baseline, and hosts the
//! M-RHO.1 transport-pure COMM oracle. Ascent remains the per-language flip
//! baseline until a language's proof, oracle, coverage, artifact-validation,
//! scheduler-fairness, and deadlock gates pass.

#![forbid(unsafe_code)]

pub mod backend;
#[cfg(feature = "oracle-rhocalc")]
pub mod rhocalc_ast;
pub mod run;
#[cfg(feature = "runtime-report")]
pub use backend::{
    IntoRuntimeObservationValue, RhoBackendInvocation, RhoRuntimeBackedLanguage,
    RuntimeReportConversionError,
};
pub use backend::{
    PlannedCallByNeedThunk, PlannedRhoBackend, RhoExecutionBoundary, RhoObservationReport,
};
pub use mettail_rho_codegen::RHOCALC_BAG_ABI_TAG;
#[cfg(feature = "oracle-rhocalc")]
pub use rhocalc_ast::{
    lower_rhocalc_name, lower_rhocalc_proc, lower_rhocalc_term, rho_runtime_backed_rhocalc_ints,
    rho_runtime_backed_rhocalc_strings, rho_runtime_backed_rhocalc_values,
    rhocalc_observe_ints_invocation, rhocalc_observe_strings_invocation,
    rhocalc_observe_values_invocation, RhocalcAstLowerError,
};
#[cfg(feature = "runtime-report")]
pub use run::{
    par_as_runtime_observation_value, run_normalized_par_for_oracle_and_read_runtime_values,
    run_validated_program_and_read_runtime_values,
    run_validated_program_with_call_and_read_runtime_values,
};
#[allow(deprecated)]
pub use run::{
    run_and_read_ints, run_and_read_strings, run_par, run_par_and_read_ints,
    run_par_and_read_strings, run_program, run_program_then_consume_strings,
    run_sequence_and_read_ints, run_sequence_and_read_strings,
};
pub use run::{
    run_normalized_par_for_oracle, run_normalized_par_for_oracle_and_read_bools,
    run_normalized_par_for_oracle_and_read_ints,
    run_normalized_par_for_oracle_and_read_string_channels,
    run_normalized_par_for_oracle_and_read_string_tuples,
    run_normalized_par_for_oracle_and_read_strings, run_rholang_source_for_oracle,
    run_rholang_source_for_oracle_and_read_bools, run_rholang_source_for_oracle_and_read_ints,
    run_rholang_source_for_oracle_and_read_strings,
    run_rholang_source_for_oracle_then_consume_strings,
    run_rholang_source_sequence_for_oracle_and_read_bools,
    run_rholang_source_sequence_for_oracle_and_read_ints,
    run_rholang_source_sequence_for_oracle_and_read_strings, run_validated_program,
    run_validated_program_and_read_bools, run_validated_program_and_read_ints,
    run_validated_program_and_read_string_channels, run_validated_program_and_read_strings,
    run_validated_program_with_call, run_validated_program_with_call_and_read_bools,
    run_validated_program_with_call_and_read_ints,
    run_validated_program_with_call_and_read_strings,
};
