//! # mettail-rho-adapter — the `OslfResourceLogic<MettaGslt>` bridge
//!
//! M-RHO compiles MeTTaIL GSLTs onto f1r3node-rust's Rho machine: MeTTaIL is the
//! COMPILER, f1r3node-rust is the parallel RUNTIME. This crate is the
//! **cost/funding adapter**: it presents a MeTTaIL GSLT to f1r3node-rust's
//! resource logic by implementing the host trait `OslfResourceLogic<MettaGslt>`,
//! delegating `demand`/`is_funded` to the host's VERIFIED `delta_sigma` over a
//! canonicalized `Par`. It is **pure analysis** — no RSpace, no Tokio — so the
//! host's funding gate can consume it GENERICALLY, exactly the way its own
//! `DenyLogic`/`ZeroDemandLogic` test logics plug into
//! `admit_by_funding_with_logic<L: OslfResourceLogic<…>>`.
//!
//! ## Dependency direction (STRICTLY one-way)
//! This crate (and `mettail-rho-codegen`/`mettail-rho-runtime`) depend ONE-WAY on
//! f1r3node-rust; f1r3node-rust NEVER depends on mettail-rust. The invariant is
//! enforced operationally by the host guard test
//! `mettail_rust_is_not_a_cargo_dependency` (f1r3node-rust
//! `rholang/src/rust/interpreter/accounting/resource_logic.rs:293`) and proven
//! internally consistent (acyclic + irreversible) in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`.
//!
//! ## Status — INERT (M-RHO.0.0)
//! Empty + `engine`-gated: the DEFAULT build pulls NOTHING from f1r3node (the
//! inert-milestone convention mirroring the `dovetail` crate). Subsequent
//! substages add, under `engine`:
//! - **M-RHO.0.1** — `MettaGslt` (`GsltPresentation`, `CanonicalProgram = Par`),
//!   `MettaSig` (`ResourceSignature`), and the `OslfResourceLogic<MettaGslt>`
//!   trait surface.
//! - **M-RHO.0.2** — `demand`/`is_funded` delegating to the host `delta_sigma`,
//!   plus an in-crate transcription of the 4 OSLF conformance laws
//!   (`law_sound`/`law_reject_underfunded`/`law_supply_monotone`/`law_decidable`)
//!   proven green for `MettaResourceLogic`; Rocq `MettaOslfLawsConformance.v`
//!   (a second instance of `GSLTOSLFCapstone.v`, reusing `LinearLogicResources.v`).
//!
//! The cost axis is two-fold (vindicated by the cost-accounting papers' R-C
//! obstruction): the **refutation** axis (`is_funded`'s verdict; `0̄` = refuted)
//! and the **ordering** axis (`i64` demand magnitude; rank-only, never refutes).

#![cfg_attr(not(feature = "engine"), allow(unused))]
#![forbid(unsafe_code)]
