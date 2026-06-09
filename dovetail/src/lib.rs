//! # Dovetail — substrate-agnostic GSLT reduction engine core
//!
//! `dovetail` is the standalone, extractable core of an off-Ascent reduction
//! engine: a generic-`W` weighted tree automaton (WTA) over a runtime e-graph
//! treated as a deterministic finite tree automaton (DFTA), with N-best /
//! set-valued cube-pruning extraction.
//!
//! Design of record:
//! `docs/design/dovetail-engine/dovetail-core-implementation-plan.md`.
//!
//! ## Invariants (enforced crate-wide)
//!
//! - **Weights ORDER, never PRUNE.** Extraction is N-best / set-valued; two
//!   distinct alternatives of equal weight both survive. An alternative is
//!   refuted only when its composed weight is the semiring zero (`0̄`).
//! - **Exact keying.** E-nodes are deduplicated by an exact content byte-stream
//!   ([`key::ContentKey`]), never a 64-bit hash (proven unsound here —
//!   `hash_only_pair_dedup_can_drop_distinct_keys`) and never a `String`.
//! - **Substrate-agnostic.** No dependency on the parser, the proc-macros, the
//!   AST crates, or any runtime / RSpace, so the crate stays cleanly
//!   extractable.
//!
//! ## Status
//!
//! Milestone **M-E.0 (inert)** is under construction: the engine is gated off by
//! default (`default = []`) and nothing in the existing workspace build path
//! depends on it. See the implementation plan for the increment sequence.

pub mod egraph;
pub mod extract;
pub mod key;
pub mod rules;
pub mod space;
pub mod wta;
