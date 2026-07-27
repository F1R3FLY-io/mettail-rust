//! Grammar- and lexer-aware stochastic term generation infrastructure.
//!
//! This module exists to make generated term strategies produce only
//! valid surface terms of a language's grammar — by walking the actual
//! parser grammar and lexer automata instead of building ASTs from
//! native type ranges and hoping Display→Parse round-trips.
//!
//! # Architecture (see `/Users/dylon/.claude/plans/radiant-pondering-kahan.md`)
//!
//! ```text
//!   language!
//!      │
//!      ▼
//!   LanguageSpec.rules   ── grammar walk ──►  string of terminals
//!   LanguageSpec.tokens  ── per-token classification (bisimilarity)
//!                         + constraint extraction (DFA analysis)
//!                         ── sampler dispatch ──►  valid token
//!                                                    literal text
//! ```
//!
//! # Sub-modules
//!
//! - [`classify`] — compile a regex pattern, minimize its DFA, decide
//!   which *canonical* token family it belongs to (Integer, SignedInt,
//!   Float, …) via language-equivalence against reference DFAs.
//! - [`canonical`] *(follow-up)* — constraint-parameterised samplers
//!   for each canonical family.
//! - [`nfa_walk`] *(follow-up)* — generic tape-driven NFA walk for
//!   patterns that classify as Unclassified.
//! - [`ambiguity`] *(follow-up)* — token-pair whitespace requirement
//!   matrix (prevents `3`+`5` → `35` misre-lexing).
//! - [`grammar_walk`] *(follow-up)* — top-down walker over
//!   `LanguageSpec.rules` with pluggable `SelectionPolicy`.
//!
//! The first cut ships `classify` only, plus a narrow wiring into
//! `strategies.rs` to fix the rholang `NumLit(negative)` bug. The
//! remaining sub-modules land as the rest of the plan is executed.

#[cfg(test)]
pub mod ambiguity;
pub mod classify;
#[cfg(test)]
pub mod grammar_walk;
// L9-3: ungated so `compile_pattern` / `deterministic_sample` (regex-valid
// capture-text sampling, decision F.2) are available to the production term
// generators. `emit_pattern_sampler` remains test-only and is
// `#[allow(dead_code)]` inside the module.
pub mod nfa_walk;
