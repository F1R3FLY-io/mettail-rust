//! # Dovetail — substrate-agnostic GSLT reduction engine core
//!
//! `dovetail` is the standalone, extractable core for MeTTaIL rewrite
//! semantics. It replaced the CESK runtime-backend rewrite path (retired in
//! P6): a generic-`W` weighted tree automaton (WTA) over a runtime e-graph
//! treated as a deterministic finite tree automaton (DFTA), with N-best /
//! set-valued exact lazy best-first extraction. The active WPDA
//! parser/recognizer remains upstream of this crate. The generated Ascent
//! engine was retired in P6; only the fail-closed `Language::run_ascent`
//! differential-oracle hook survives, and git history is the archive.
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
//! Installed and live (post-P6). Dovetail is the general-purpose production
//! rewrite backend: the `languages` crate enables it through the default
//! `dovetail-codegen` feature, and the generated `dovetail_report_for`
//! associated fn drives [`rules::saturate_with_native`] for every flipped
//! language. This crate keeps an empty `default = []` on purpose — it carries
//! no optional features of its own, so the production flip is feature-wired
//! from `languages`, not from here. See the implementation plan for the
//! increment sequence and `docs/architecture/dovetail/` for the suite.

pub mod egraph;
pub mod extract;
pub mod flat_matcher;
pub mod hash;
pub mod key;
pub mod report;
pub mod rules;
mod scc;
pub mod set_automaton;
pub mod space;
pub mod wta;
