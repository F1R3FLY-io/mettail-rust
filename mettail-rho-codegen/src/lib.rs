//! # mettail-rho-codegen — COMPILE-TIME GSLT → Rholang VM lowering
//!
//! MeTTaIL is the COMPILER; f1r3node-rust's Rho machine is the parallel RUNTIME.
//! This crate lowers a MeTTaIL `LanguageDef` into a **parallel-optimized Rholang
//! VM** — three artifacts:
//!  1. reduction rules as `Par` contracts (the COMM family),
//!  2. native `Vec<Definition>` system processes (HOL `fold`/`step`),
//!  3. the `OslfResourceLogic` adapter wiring (see `mettail-rho-adapter`).
//!
//! Rule classification drives the lowering: COMM/interaction → RSpace
//! produce/consume; structural/congruence → par-context (`eval_par` — the AMBIENT
//! structural rule, emit `Par`, never fork); HOL `fold`/`step` → native
//! `Definition` handler; equations → compile-time e-graph; injection/cast → `Par`
//! wrapper. The e-graph / WTA / decision-tree remain **compile-time analyses**
//! that GENERATE indexing + ordering + recognition plugging into f1r3node's
//! existing matcher/join/lock/`check_commit` — speed + parallelism without
//! forking the runtime.
//!
//! ## Dependency direction (STRICTLY one-way)
//! Depends ONE-WAY on f1r3node-rust; never the reverse (proven in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`; enforced by the host
//! guard test `mettail_rust_is_not_a_cargo_dependency`).
//!
//! ## Status — INERT (M-RHO.0.0)
//! Empty + `engine`-gated; the DEFAULT build pulls nothing from f1r3node.
//! M-RHO.0.3 adds the pure `LanguageDef → Rholang` translator
//! (`lower_term_to_rholang` / `lower_rule_to_rholang`) consumed by a new
//! `macros::gen::runtime::rho_vm::generate_rho_vm` sibling of `generate_ascent_source`,
//! plus a `rholang` parse round-trip (`Compiler::source_to_adt → Par == Ok`), and
//! the totality-or-explicit-rejection proof `RhoLoweringTotalOrRejects.v`
//! (out-of-subset constructors are REFUSED, never silently dropped — "miss
//! nothing" at the codegen layer).

#![cfg_attr(not(feature = "engine"), allow(unused))]
#![forbid(unsafe_code)]
