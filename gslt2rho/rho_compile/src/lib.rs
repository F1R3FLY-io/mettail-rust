//! `rho_compile`: compile a MeTTaIL GSLT specification to rho-calculus
//! terms via set-automaton-driven optimal channel naming.
//!
//! ## Overview
//!
//! Given a GSLT (the `rewrites { ... }` portion of a MeTTaIL `language!`
//! block), this crate produces an equivalent rho-calculus program in
//! which:
//!
//! 1. Each direct rewrite `L ~> R` becomes a persistent for-receive that
//!    matches `L` and emits `R` on the same channel.
//! 2. Each contextual rewrite
//!    `S_1 ~> T_1, ..., S_n ~> T_n => K(...) ~> K'(...)` becomes a
//!    persistent for-receive on the channel `tc(K)`, where `tc(K)` is
//!    computed by partial evaluation of a Bouwman--Erkens set automaton
//!    (constructed once, off-line, from the union of all LHSs) on the
//!    surface of `K`.
//!
//! The latter step is what makes the compilation **optimal** in the three
//! senses proved in the accompanying paper: each surface symbol of an
//! outer context is consumed by exactly one for-receive, inner reductions
//! never invalidate outer channels, and the channel quotient is the
//! coarsest equivalence on contexts that preserves outermost firing.
//!
//! ## Pipeline
//!
//! ```text
//!   Gslt   --[ build set automaton ]-->   SetAutomaton
//!     \                                   /
//!      \         [ for each rule ]      /
//!       v                              v
//!     compile_rule  -- tc(K) -->   Proc (rho)
//! ```
//!
//! ## Quick start
//!
//! ```ignore
//! use rho_compile::{compile, gslt::*};
//!
//! let g = Gslt { /* ... */ };
//! let c = compile(&g);
//! for r in &c.processes {
//!     println!("{}: {}", r.label, r.process);
//! }
//! ```

pub mod automaton;
pub mod channel;
pub mod compile;
pub mod gslt;
pub mod rho;

pub use compile::{compile, compile_with, collect_into_par, CompiledGslt, CompiledRule};
