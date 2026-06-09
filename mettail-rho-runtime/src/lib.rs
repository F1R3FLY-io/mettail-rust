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
//! Skeleton — fully integrated, NOT feature-gated (no f1r3node deps yet; they land
//! with the code that uses them). Ascent remains the differential oracle until the
//! per-language flip (M-RHO.4). Later substages add: the
//! `RhoBackend { fn rho_source(&self) -> String }` seam + `assert_oracle_agree`
//! (M-RHO.0.4, `rholang`/`dovetail` deps), and a real `RhoRuntime::evaluate` run of
//! the lowered calculator (M-RHO.0.5 — the substage that links
//! `rspace_plus_plus`/`casper`/Tokio).

#![forbid(unsafe_code)]

pub mod run;
pub use run::run_and_read_ints;
