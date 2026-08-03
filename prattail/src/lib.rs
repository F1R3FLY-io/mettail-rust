// AL03: SIMD-accelerated whitespace skipping requires portable_simd (nightly).
#![feature(portable_simd)]
// Robustness gate (campaign Phase 5): production code uses `.expect("…")` over
// `.unwrap()` so every panic names its invariant. `not(test)` keeps test code
// (which legitimately unwraps in asserts) silent. `deny`, not `warn`: the whole
// production path was converted, so this is a hard tripwire — a reintroduced
// bare `.unwrap()` fails `cargo clippy` rather than adding to a warning backlog.
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

//! # PraTTaIL — Pratt + Recursive Descent Parser Generator for MeTTaIL
//!
//! PraTTaIL is a custom parser generator combining **Pratt parsing**,
//! **recursive descent**, and **automata-optimized lexing** that:
//!
//! - Eliminates all 4 LALRPOP workarounds by design (context-passing parsing)
//! - Generates ~10-14x less code (~1,500-2,000 lines total vs ~20,000)
//! - Produces typed ASTs directly (like LALRPOP, unlike pest)
//! - Runs in O(n) time and O(n) memory
//! - Uses automata-theoretic optimizations for both lexing and parse dispatch
//!
//! ## Architecture
//!
//! ```text
//! language! { ... }
//!        │
//!        ▼
//!  ┌─────────────┐     ┌──────────────────────────────────────┐
//!  │ macros crate │────▶│         PraTTaIL crate               │
//!  │  (proc macro)│     │                                      │
//!  └─────────────┘     │  1. Automata pipeline (lexer):        │
//!        │              │     Terminals → NFA → DFA → Minimize  │
//!        │              │     → Equiv Classes → Codegen         │
//!        │              │                                      │
//!        │              │  2. Prediction engine (parser):       │
//!        │              │     FIRST sets → Decision automata    │
//!        │              │     → Dispatch tables                 │
//!        │              │                                      │
//!        │              │  3. Pratt + RD generators:            │
//!        │              │     BP tables → Pratt loops           │
//!        │              │     Rules → RD handlers               │
//!        │              └──────────────────────────────────────┘
//!        │
//!        ▼
//!   TokenStream (Rust source code)
//! ```

// `trace_diag!` (the compile-time `walker-trace` gate for parser diagnostics)
// must be in textual macro scope for every module below that uses it, so this
// `#[macro_use]` module is declared before all others. See `src/trace.rs`.
#[macro_use]
mod trace;

pub mod automata;
pub mod binding_power;
pub mod classify;
/// ★ The cross-category projection-boundary walk's per-hop decision, factored out so its
/// verified Rocq model can be executed against it (`tests/crosscat_boundary_oracle.rs`).
pub mod crosscat_boundary;
// Stage 10.5b conclusion (2026-05-05): `pub mod dispatch` DELETED (file deleted,
// ~1,940 LoC). Trampoline-side cross-category dispatch emitter; data types
// (CastRule, CrossCategoryRule) migrated to grammar::ir.
pub mod ebnf;
pub mod lexer;
pub mod lexer_types;
pub mod pipeline;
// Stage 10.5b conclusion (2026-05-05): `pub mod pratt` DELETED (file deleted,
// ~2,172 LoC). Trampoline-side Pratt parser emitter; superseded by Walker
// codegen at `macros/src/gen/runtime/wpda_codegen/{prefix,infix,binder}.rs`.
pub mod prediction;
pub mod rd_analysis;
// Stage 10.5b conclusion (2026-05-05): `pub mod recursive` DELETED (file
// deleted, ~1,200 LoC). Trampoline-side recursive-descent emitter; data
// types (RDRuleInfo, RDSyntaxItem, CollectionKind) migrated to grammar::ir.
/// Phase F.13 chain_10000 Exp 9 / Approach P Substage 1.a (2026-05-26):
/// realize-time cohort fanout. `CohortContinuation<W>` defers cohort
/// revives into outer-rule-wrap records interned as SPPF packings at
/// EOI. Targets `cohort_cursors_emitted=335,808` on chain_1000
/// (projected ~3.4 M revived cursors at chain_10000). See ledger +
/// `phase-f13-stage-1-5-4-approach-p-realize-time-fanout.md`.
pub mod cohort_continuation;
/// Phase F.13 Stage L1 (2026-05-25): cohort lazy materialization
/// scaffolding. Adds `Frame<W>` (Concrete | Cohort) + `CohortFrame<W>`
/// + `CohortShell<W>` + `CohortMemberState<W>` types. L2 wires the
/// `InflightCollision` arm to construct cohorts; L3 implements the
/// ObsInvariant fast path. See `docs/design/plans/cohort-lazy-materialization.md`.
pub mod cohort_lazy;
/// Phase F.13 chain_10000 Exp 15 Substage 1 (2026-05-27): CursorId
/// newtype + recycle allocator for the planned CPS walker rewrite.
/// See `prattail/docs/design/plans/exp15-cps-trampolined-walker.md`.
pub mod cursor_id;
/// Phase F.13 chain_10000 Exp 15 Substage 1 (2026-05-27): walker-global
/// persistent state map (HAMT-backed via `im`). Replaces the per-cursor
/// `Arc<FxHashSet<PackedDispatchConfig>>` visited sets + per-cursor
/// recovery_deltas/scope_marks/lex_fork_path Vecs with walker-global
/// im::OrdSet / im::HashMap indexed by CursorId. Lineage chain via
/// `parent_of_inheritance` resolves Fork inheritance in O(Fork-depth x
/// log32 N) without sweeping the visited set at Fork. Substage 1 is
/// dead code; Substage 2 introduces mirror-write feature gate.
pub mod cursor_store;
/// Phase F.13 H12 Tomita-GLR dispatch-cohort sharing. Shares
/// cross-cat-projection sub-parse work across cohort members at the
/// same `(pos, source_src_idx, inner_cur_bp)` key. Each cohort member
/// retains its own return frame; only the sub-parse work is shared.
pub mod dispatch_cohort;
/// Phase F.13 chain_10000 Plan D E6 Substage 1 (2026-05-26):
/// GSS edge-stack interning arena. Thin specialization over
/// `path_tree_arena::PathTreeArena<GssEdgeId>`. Standalone (no
/// walker integration yet); E6 Substage 2 will wire
/// `BranchCursor::incoming_edge_stack_id`. See module docs +
/// ledger row 4-alt.
pub mod edge_stack_arena;
pub mod grammar;
pub mod hang_dump;
/// Phase F.13 chain_10000 Plan D E6 (2026-05-26): generic path-tree
/// interning arena. Both `SppfStackArena` and `EdgeStackArena` are
/// type aliases over `PathTreeArena<T>`. See module docs.
pub mod path_tree_arena;
/// Phase F.13 Task #117 (2026-05-23): recovery-dispatch cohort cache.
/// Synchronous analogue of `dispatch_cohort` for the
/// `emit_recovery_fork` path — shares the WFST-produced
/// `Vec<ForkBranch<W>>` across cohort members that hit the same
/// `(pos, state_cat_src_idx, cur_bp)` recovery dead-end.
pub mod recovery_cohort;
/// Phase F.13 chain_10000 Plan D E3 (2026-05-25 / refactored 2026-05-26):
/// SPPF-stack interning arena. Thin specialization over
/// `path_tree_arena::PathTreeArena<SppfId>`. Wired into BranchCursor
/// at commit `f18a847`. See module docs + ledger row 3.
pub mod sppf_stack_arena;
/// EP-P2 (Stage B) Step-0 substrate: per-position forward suffix-class
/// Parikh masks (`SuffixClassMasks`). Grammar-agnostic (the class
/// function is injected); two builders — a linear backward pass and a
/// lattice backward DP over `LexDag` edges. Consumed by the walker's
/// shadow obligation gate. See `ParikhObligationGate.v` (Part 2) and
/// `docs/design/evidence-pruning/02-staged-implementation-plan.md` §P2.
pub mod suffix_classes;
pub mod token_id;
/// Phase F.13 chain_10000 Exp 14 Substage 1 (2026-05-27): Tomita-style
/// frontier merge map data structure. Coarsens the current 11-axis
/// ConfigKey to a 5-axis TomitaKey = (state, node, pos, edge_top,
/// collection_depth) and groups cursors with the same key under a
/// shared CohortShell + N FrontierArc records. Substage 1 ships only
/// the types + tests as dead code; downstream substages wire the
/// ingest path at step_fanout. See
/// `prattail/docs/design/plans/exp14-tomita-per-arc-gss-merge.md`.
pub mod tomita_frontier;
/// Phase F.13 walker statistics counters (gated by `walker-stats` feature).
pub mod walker_stats;
// Stage 10.6 (2026-05-05): `pub mod trampoline` DELETED (file deleted, 7,351 LoC).
// The Walker (WPDS) is the surviving parser backend. All recovery infrastructure
// (BRACKET_STATE_<cat>, LAST_ERROR_POS_<cat>, RUNNING_WEIGHT_<CAT>,
// PARENT_WEIGHT_<CAT>, frame_kind_of_<cat>, running_weight_<cat>) migrated to
// `macros/src/gen/runtime/wpda_codegen/recovery.rs::emit_recovery_module`.
//
// Stage 10.4 (2026-05-04): `pub mod unified_trampoline` DELETED. Walker
// subsumes the multi-category mutual-recursion CPS dispatch via per-cursor
// BranchCursors and AmbiguityFanout state.
pub mod wfst;

pub mod compose;
pub mod composition_verify;
pub mod cost_benefit;
pub mod decision_tree;
pub mod lattice;
pub mod lint;
pub mod recovery;
/// Stage 3.20 / L12 (Commit C, 2026-05-06): WPDS-edge-driven recovery dispatch.
/// `emit_recovery_fork` constructs lex-min-ranked Fork branches at every
/// PrefixDispatch dead-end (engine_impl.rs:254 `_ => Idle` orphan,
/// rewired in Commit D). Replaces the wrapper-level skip-to-sync retry
/// loop in facade.rs (deleted in Commit E).
pub mod recovery_dispatch;
pub mod runtime_types;
pub mod transducer;
pub mod wpds;

/// WPDS runtime: reactive FSM types (`WpdaState`/`Event`/`Transition`),
/// integer-indexed `StackSymbolV2`, and `WpdaControl` directives.
/// Stage 1 of W7 plan v5.1 — see `prattail/docs/design/wpds-migration-survey.md`.
pub mod wpda_runtime;

/// WPDS walker: pure reactive FSM (`State × Event → Transition`) driving
/// the runtime parser. Stage 4 of W7 plan v5.1.
pub mod wpda_walker;

/// Shared Packed Parse Forest (SPPF) — the ambiguity-preserving parse-forest
/// data structure. Option C (2026-05-15); see
/// `~/.claude/plans/option-c-sppf-on-wpda.md`. Replaces the M11 multiset
/// `DerivationWeight<W, Arc<SemanticBuilder>>` snapshot machinery with a
/// canonical Scott-Johnstone GLL SPPF.
pub mod sppf;

/// SPPF → user-AST realization. Walks a forest from a root, invoking an
/// `ActionResolver` per Packing to materialize AST values. Fans out over
/// multiple Packings linked to the same Symbol to preserve ambiguity.
pub mod sppf_realize;

// Stage 10.3 (2026-05-04): `pub mod parity` (Model A + Model B golden ASTs)
// DELETED. Zero in-tree consumers; parity tests had become tautological
// post-Stage-10b's parse_preserving_vars Walker rewrite.

/// Phase 6: inline sub-language parsers (predicates) used by the WPDS
/// walker for slots that don't fit the main grammar's state machine.
pub mod parser;

/// Phase 6 / F.0-sibling: behavioral predicate AST. Hosted here so the
/// WPDS walker can produce predicates without crossing the
/// prattail → runtime cycle. Runtime re-exports this module's types for
/// backward compatibility.
pub mod behavioral_pred;

/// Railroad diagram generation from grammar specifications.
pub mod railroad;

/// Graph-Structured Stack for GLL parsing.
pub mod gss;

/// Earley recognition with Leo optimization.
pub mod earley;

// ── Algebraic program analysis (always-on — generic over any StarSemiring) ──
// Tarjan path expression algorithm + interprocedural extension
// (Kincaid, Cyphert, Breck & Reps, 2019).
pub mod algebraic;

// ── Forward-backward analysis (always-on — generic over any semiring) ──────
// The core algorithm is semiring-generic and used by A4 (BooleanWeight).
// LogWeight-specific tests are feature-gated within the module itself.
pub mod forward_backward;

// ── Log semiring modules (feature = "wfst-log") ────────────────────────────
pub mod log_push;
pub mod training;

pub mod grammar_gen;

// ── Mathematical Analysis & Theorem Proving modules ─────────────────────────

/// Provenance semiring N[X]: polynomial semiring tracking HOW facts are derived.
pub mod provenance;

/// Relational weight domain: binary relations on finite sets for WPDS analysis.
pub mod relational;

/// EWPDS: Extended WPDS with merging functions for local variable handling.
pub mod ewpds;

/// ARA: Affine-Relation Analysis weight domain (vector spaces of matrices).
/// Discovers all interprocedural affine relationships via WPDS analysis.
pub mod ara;

/// Kleene Algebra with Tests: decidable Hoare logic and program equivalence.
pub mod kat;

/// Visibly Pushdown Automata: decidable equivalence/inclusion for structured grammars.
pub mod vpa;

/// TRS analysis: confluence checking (critical pairs) and termination (dependency pairs).
pub mod confluence;
pub mod termination;

/// E-graph equality saturation: enhanced joinability, term simplification,
/// equivalence discovery via the egg algorithm (Willsey et al., POPL 2021).
pub mod egraph;

/// Buchi/Parity automata: infinite-word acceptance for liveness properties.
pub mod buchi;

/// LTL model checking: WPDS x Buchi product for temporal property verification.
pub mod ltl;

/// Weighted Tree Automata: term recognition, ranking, and transduction.
pub mod tree_automaton;

/// Alternating automata: universal branching for game semantics and CTL.
pub mod alternating;

/// Nominal automata: orbit-finite sets for name-passing calculi.
pub mod nominal;

/// Petri nets / VASS: concurrent process analysis.
pub mod petri;

/// Cost Register Automata: streaming quantitative computation.
pub mod cra;

/// Theory morphisms: cross-theory translation and proof transfer.
pub mod morphism;

/// Layered proof output: verdicts, human-readable explanations, Rocq certificates.
pub mod proof_output;

// ── Advanced Automata Infrastructure ─────────────────────────────────────────

/// Symbolic automata: predicate-labeled transitions over infinite domains.
/// BooleanAlgebra trait, decidability classification (T1-T4), guard analysis.
pub mod symbolic;

/// `AnyAlgebra`: a single `BooleanAlgebra` carrier ranging over a family of
/// per-sort effective Boolean algebras (Int/Char/Bool in M0), so one symbolic
/// automaton/transducer can guard predicates of any supported data type.
pub mod any_algebra;

/// The `where`-guard substrate IR: the single vocabulary both guard front ends
/// (the surface `Proc` and the lowered `rhoapi::Par`) encode into, plus the
/// static (validity/unsatisfiability) and ground (COMM-time evaluation) decision
/// procedures and the `Sat3::DontKnow` policy seam.
pub mod guard_formula;

/// ★ The refusal vocabulary shared by BOTH run-time guard legs — the types that
/// make "the guard is false" and "the guard could not be decided" two different
/// objects. Lives here because `rholang-runtime` depends on `languages`, so the
/// two lanes' only common ancestor is `prattail`; see the module docs.
pub mod guard_refusal;

/// The algebra tower (`RejectSafeAlgebra` ⊃ `HeytingAlgebra` ⊃ classical
/// `BooleanAlgebra`): keeps semi-decidable (behavioral) algebras from being used
/// where classical complement is required. `Sat3`, `Classical<A>` bridge.
pub mod algebra_tower;

/// `BehavioralAlgebra`: semi-decidable behavioral predicates (relational/Datalog
/// now; modal/temporal next) over a fact-base snapshot + host-term LTS. Implements
/// `HeytingAlgebra` (NOT classical `BooleanAlgebra`).
pub mod behavioral_algebra;

/// Bisimulation by partition refinement over a behavioral LTS — the sound,
/// compile-time (clopen / regular-core) layer of the Heyting-SFA bisimulation.
pub mod bisimulation;

/// `OrderedFieldAlgebra<P>`: unbounded interval-union effective Boolean algebra
/// over any totally-ordered point type (BigInt/BigRational/OrderedF64/i128),
/// with a single density-aware witness oracle (`OrderedPoint::witness_in`).
pub mod ordered_field;

/// Generic symbolic-regex engine: `RegexAlgebra<A>` (= the list algebra) —
/// symbolic regular languages over any element algebra, compiled to
/// `SymbolicAutomaton<A>`.
pub mod regex_sfa;

/// `StringAlgebra`: effective Boolean algebra of symbolic regular languages over
/// strings (the `CharClassAlgebra` instantiation of `regex_sfa`).
pub mod string_algebra;

/// N-ary product (tuples/records) and sum (variants) effective Boolean algebra
/// combinators, generic over the element algebra.
pub mod product_nary;

/// Order-insensitive collection algebras: `BagAlgebra` (multisets, minterm-count
/// feasibility) and `MapAlgebra` (key→value), generic over the element algebra.
pub mod collection_algebra;

/// Symbolic tree automata over ranked terms with symbolic payload guards — the
/// structural-recursion core for algebraic/recursive data types.
pub mod sym_tree;

/// `SymbolicTreeTransducer<A,B>`: bottom-up tree transduction with per-node
/// output builders (the tree generalization of the word transducer).
pub mod sym_tree_transducer;

/// Structural-type recognizer (OSLF substrate Phase 2): compile a grammar's
/// ranked-tree constructor alphabet into a `SymbolicTreeAutomaton<AnyAlgebra>`
/// so structural refinement-type inhabitation / disjointness / subtype are
/// decided precisely by `sym_tree` (generalizing the finite
/// `SetTheoreticTypeSystem`). `.0`-inert: always compiled, no live caller yet.
pub mod structural_types;

/// Weighted MSO logic: grammar property specification, lint-as-formula,
/// Büchi-Elgot-Trakhtenbrot theorem bridge (Droste & Gastin 2007).
pub mod weighted_mso;

/// Parity alternating tree automata: mu-calculus model checking on ASTs,
/// structural verification, test generation (Emerson & Jutla 1991).
pub mod parity_tree;

/// `letprop` recursive predicate definitions (Phase 10 of the
/// predicated-types implementation plan). Lowers source-level
/// `letprop name(args) = body;` to mu-calculus + PATA.
pub mod letprop;

/// Hindley-Milner type system scaffold (Phase 12 of the
/// predicated-types implementation plan). Implements `TypeSystem`
/// over `HmType` with Algorithm W unification and `infer_simple_let`.
pub mod hindley_milner;

/// Register automata: data-aware finite-state computation with register storage.
/// Context-sensitive parsing, binding verification (Kaminski & Francez 1994).
pub mod register_automata;

/// Probabilistic automata: statistical disambiguation, expected-case optimization,
/// corpus-driven weight training via Baum-Welch EM.
pub mod probabilistic;

/// Multi-tape automata: synchronized multi-stream computation with k tapes.
/// Multi-channel receives, parallel tokenization (Kempe 2004).
pub mod multi_tape;

/// Multiset automata: multiset-weighted computation for process multiplicity
/// and resource analysis (Müller, Weiß & Lochau 2024).
pub mod multiset_automata;

/// Weighted two-way transducers: bidirectional weighted transductions for
/// cross-channel constraint propagation (Feng & Maletti 2022).
pub mod two_way_transducer;

/// Symbolic Finite Transducers: output-producing transductions over infinite
/// domains. Composition, pre/post-image, functionality (D'Antoni & Veanes 2012).
pub mod sft;

/// Predicate Dispatch Automaton: algebraic variety classification for directed
/// module dispatch. Decomposes predicate formulas into morphemes and activates
/// only the relevant Phase 7 modules (Eilenberg variety theorem).
pub mod predicate_dispatch;

/// LogicT fair backtracking search framework and ConstraintTheory trait.
/// Implements msplit-based LogicT (Kiselyov et al., ICFP 2005) for fair
/// disjunction and conjunction. Provides the ConstraintTheory trait for
/// pluggable constraint domains and TheoryAlgebra bridge to BooleanAlgebra.
pub mod logict;

/// OSLF Phase 8: SMT-backed [`ConstraintTheory`](logict::ConstraintTheory) via the
/// in-process Z3 library. A Sat3-ONLY decider (`is_satisfiable_3v`/`checked_witness`)
/// — `Z3Theory` is NOT a `BooleanAlgebra` and is never routed into the SFA classical
/// consumers. Off by default; needs no libz3 in the default build.
#[cfg(feature = "smt")]
pub mod logict_smt;

/// Presburger arithmetic: automata-based decision procedure for
/// multi-variable linear integer arithmetic (Büchi 1960). Zero external deps.
pub mod presburger;

/// Structural unification with occurs check (Martelli & Montanari 1982).
/// ConstraintTheory implementation for pattern matching and type variable solving.
pub mod unification;

/// Subtype lattice with join/meet (LUB/GLB) operations.
/// ConstraintTheory implementation for type hierarchy analysis.
pub mod lattice_theory;

/// Pluggable type system framework: TypeSystem trait, LatticeTypeSystem,
/// RefinementTypeSystem, TypeSystemAlgebra bridge to BooleanAlgebra.
pub mod type_system;

/// Safety/liveness verification API: WPDS-based property checking.
pub mod verify;

/// Counterexample-Guided Abstraction Refinement (CEGAR): iterative abstraction
/// refinement over the BooleanWeight -> CountingWeight -> TropicalWeight ladder.
pub mod cegar;

/// Repair suggestion engine: analysis-driven fix recommendations.
pub mod repair;

#[cfg(test)]
pub mod test_generators;
#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};
use std::fmt;

use proc_macro2::TokenStream;

use binding_power::Associativity;
use grammar::ir::CollectionKind;

/// Source location for a grammar rule, extracted from proc-macro span data.
///
/// Used to provide rustc-style source pointers in lint diagnostics.
/// When span data is unavailable (e.g., in unit tests), use `SourceLocation::default()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct SourceLocation {
    /// 1-based line number (0 = unknown).
    pub line: u32,
    /// 0-based column number.
    pub column: u32,
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Configuration for beam-width pruning in WFST prediction/recovery.
///
/// Controls how aggressively the parser prunes low-probability alternatives
/// during WFST-based prediction and recovery.
#[derive(Debug, Clone, Default, PartialEq)]
pub enum BeamWidthConfig {
    /// Beam pruning disabled (default). Actions are not pruned by weight.
    /// Set via `beam_width: none` or `beam_width: disabled` in the DSL.
    #[default]
    Disabled,

    /// Explicit beam width. Actions with weight > best + width are pruned.
    /// Set via `beam_width: 1.5` (or any float literal) in the DSL.
    Explicit(f64),

    /// Auto-select beam width from the trained model's `recommended_beam_width`.
    /// Set via `beam_width: auto` in the DSL.
    /// Requires the `wfst-log` feature and `log_semiring_model_path` to be set.
    /// If the trained model has no recommended beam width, falls back to `Disabled`.
    Auto,
}

// BeamWidthConfig derives Default via #[default] on the Disabled variant.

impl BeamWidthConfig {
    /// Convert to an `Option<f64>` for use in WFST construction.
    ///
    /// - `Disabled` → `None`
    /// - `Explicit(w)` → `Some(w)`
    /// - `Auto` → `None` (resolved later by pipeline from trained model)
    pub fn to_option(&self) -> Option<f64> {
        match self {
            BeamWidthConfig::Disabled => None,
            BeamWidthConfig::Explicit(w) => Some(*w),
            BeamWidthConfig::Auto => None,
        }
    }

    /// Whether this config is `Auto`.
    pub fn is_auto(&self) -> bool {
        matches!(self, BeamWidthConfig::Auto)
    }

    /// Whether beam pruning is enabled (explicit or auto).
    pub fn is_enabled(&self) -> bool {
        !matches!(self, BeamWidthConfig::Disabled)
    }
}

/// Configurable literal token patterns for lexer generation.
///
/// Each field holds a PCRE-subset regex pattern that is compiled to an NFA
/// fragment via the Thompson construction pipeline. The canonical source of
/// truth for these patterns is `prattail/src/literal_patterns.ebnf`, which is
/// loaded at pipeline startup via `parse_literal_patterns_ebnf()`.
///
/// `Default` provides the standard patterns (identical to those in the `.ebnf` file):
/// - integer: `[0-9]+`
/// - float:   `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`
/// - string:  `"([^"\\]|\\.)*"`
/// - ident:   `[a-zA-Z_][a-zA-Z0-9_]*`
///
/// When `boolean` is `Some(pattern)`, the lexer uses that regex for boolean
/// literals (e.g. `yes|no`) and emits a single token with the matched text;
/// when `None`, the default `true`/`false` keywords are used.
#[derive(Debug, Clone)]
pub struct LiteralPatterns {
    /// Integer literal pattern (e.g., `[0-9]+`).
    pub integer: String,
    /// Optional per-category integer literal patterns.
    ///
    /// Key = category name from `types {}` (e.g., `Int`, `UInt32`), value = regex pattern.
    /// When non-empty, lexer generation can build separate integer token paths per category.
    pub integer_by_category: std::collections::HashMap<String, String>,
    /// Per-category rational literal regex patterns (e.g. `…r/…r`, optional `…r`).
    pub rational_by_category: std::collections::HashMap<String, String>,
    /// Per-category fixed-point literal regex patterns (`<mantissa>p<scale>`).
    pub fixed_by_category: std::collections::HashMap<String, String>,
    /// Float literal pattern (e.g., `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`).
    pub float: String,
    /// String literal pattern (e.g., `"([^"\\]|\\.)*"`).
    pub string: String,
    /// Identifier pattern (e.g., `[a-zA-Z_][a-zA-Z0-9_]*`).
    pub ident: String,
    /// Optional boolean literal pattern (e.g. `yes|no`). When `None`, default `true`/`false` keywords are used.
    pub boolean: Option<String>,
}

pub mod int_lit;
pub mod rational_lit;
pub use int_lit::{parse_int_lit, IntLit, IntSuffix, Suffix};
pub use rational_lit::{parse_rational_lit, RationalLit};
// Stage 10.6 (2026-05-05): `pub use trampoline::reset_handle_mixfix_emitted` DELETED;
// `prattail/src/trampoline.rs` deleted entirely.
// Note: parse_fixed_lit and parse_float_lit live in the `mettail-runtime` crate
// (they construct runtime types CanonicalFixedPoint / CanonicalFloat64). The
// dependency direction is runtime → prattail (not the reverse), so we keep
// these parsers next to the types they produce. Callers:
//   use mettail_runtime::{parse_fixed_lit, parse_float_lit};

/// The embedded content of `literal_patterns.ebnf`, compiled into the binary.
const DEFAULT_LITERAL_PATTERNS_EBNF: &str = include_str!("literal_patterns.ebnf");

/// Default literal patterns, parsed from the embedded `literal_patterns.ebnf` file.
///
/// This ensures the `.ebnf` file is the single source of truth — the default
/// patterns are never duplicated as string constants in Rust code.
impl Default for LiteralPatterns {
    fn default() -> Self {
        automata::regex::parse_literal_patterns_ebnf(DEFAULT_LITERAL_PATTERNS_EBNF)
            .expect("embedded literal_patterns.ebnf should always be valid")
    }
}

/// Specification for a custom or overridden token kind.
///
/// Produced by the macros crate's bridge from `TokenDef` AST nodes.
/// Consumed by the automata pipeline to build NFA fragments and codegen.
#[derive(Debug, Clone)]
pub struct CustomTokenSpec {
    /// Token name (e.g., "Integer", "HexLiteral").
    pub name: String,
    /// Regex pattern for this token.
    pub pattern: String,
    /// Target category name (e.g., "Int"). None = no payload.
    pub category: Option<String>,
    /// Resolved Rust type for the payload (e.g., "i64", "f64", "&'a str").
    /// Set by the bridge from the category's native type. None = unit variant.
    pub payload_type: Option<String>,
    /// Rust code expression for constructing the payload from `text: &str`.
    pub constructor_code: Option<String>,
    /// Whether this overrides a built-in token kind (Integer, Float, StringLit, Ident).
    pub is_builtin_override: bool,
    /// Disambiguation priority (higher = preferred). Default: 2.
    pub priority: u8,
    /// Push into a named mode after matching. None = no push.
    pub push_mode: Option<String>,
    /// Pop the current mode after matching (return to caller).
    pub is_pop: bool,
    /// Output stream name. None = "main".
    pub stream: Option<String>,
}

/// A lexer mode with its own set of token patterns.
///
/// Each mode gets its own NFA → DFA pipeline and separate codegen.
#[derive(Debug, Clone)]
pub struct LexerModeSpec {
    /// Mode name (e.g., "string_body", "comment_body").
    pub name: String,
    /// Token specs within this mode.
    pub token_specs: Vec<CustomTokenSpec>,
    /// L9-4: RAW guest mode — the lexer does not skip inter-token whitespace
    /// inside this mode (whitespace is `GuestChunk` content). Default `false`.
    pub raw: bool,
}

/// Result of multi-stream lexing.
///
/// Contains the main token stream (consumed by the parser) plus auxiliary streams
/// for tokens routed via `-> stream_name` annotations in the `tokens { ... }` block.
/// Auxiliary streams are available as metadata for tools (IDE comment extraction,
/// formatter whitespace preservation, etc.).
///
/// When no `-> stream` annotations exist, `streams` is empty (zero allocation).
///
/// ## ★ The channel boundary (task #18)
///
/// Only `DEFAULT` (`tokens`) is special: it is the parse stream, and it is the
/// only stream a running program can ever observe. An alternative channel is
/// **compile-time / tooling-facing apparatus**: the backend (interpreter, LSP,
/// formatter, doc-comment or compiler-directive extractor, linter) reads it
/// through the accessors below; there is no path by which a channel token
/// reaches the parser or the running program. `COMMENTS` carries no engine-level
/// privilege — it is an ordinary channel NAME a language conventionally uses for
/// comments, treated identically to `PRAGMAS`, `DOCTESTS`, or any other name.
#[derive(Debug, Clone)]
pub struct LexResult<T> {
    /// Main token stream (consumed by the parser). Includes the Eof token.
    pub tokens: Vec<(T, runtime_types::Range)>,
    /// Auxiliary streams (comments, whitespace, etc.), keyed by stream name.
    pub streams: std::collections::HashMap<String, Vec<(T, runtime_types::Range)>>,
}

/// The channel-filtered token-stream reader — the BACKEND/TOOLING view of the
/// retained alternative channels, modeled on ANTLR4's `CommonTokenStream`
/// (`getHiddenTokensToLeft` / `getHiddenTokensToRight` / channel filtering) so
/// tool authors meet a familiar surface.
///
/// Every accessor is generic over the channel NAME — there is no registry and no
/// privileged channel. Tokens on a channel are buffered in source order, each
/// with the `Range` (byte offset + line/column) the scanner recorded, which is
/// what lets a formatter or LSP re-attach a comment to the code it annotates.
impl<T> LexResult<T> {
    /// Every retained token on `channel`, in source order. An unknown or empty
    /// channel yields an empty slice (never an error) — a source with no
    /// comments is not a failure.
    pub fn tokens_on_channel(&self, channel: &str) -> &[(T, runtime_types::Range)] {
        self.streams.get(channel).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The names of every channel that retained at least one token.
    pub fn channels(&self) -> impl Iterator<Item = &str> + '_ {
        self.streams.keys().map(String::as_str)
    }

    /// The channel tokens lying immediately to the LEFT of `DEFAULT` token
    /// `default_index` — i.e. those whose span starts at or after the end of the
    /// previous `DEFAULT` token and before the start of `tokens[default_index]`.
    /// ANTLR4's `getHiddenTokensToLeft`. For `default_index == 0` the left
    /// boundary is the start of input, so a leading file header comment attaches
    /// to the first real token.
    ///
    /// Returns an empty slice when `default_index` is out of range or nothing on
    /// `channel` falls in the gap.
    pub fn hidden_tokens_to_left(
        &self,
        default_index: usize,
        channel: &str,
    ) -> &[(T, runtime_types::Range)] {
        let Some((_, range)) = self.tokens.get(default_index) else {
            return &[];
        };
        let lower = if default_index == 0 {
            0
        } else {
            self.tokens[default_index - 1].1.end.byte_offset
        };
        self.channel_slice_in(channel, lower, range.start.byte_offset)
    }

    /// The channel tokens lying immediately to the RIGHT of `DEFAULT` token
    /// `default_index` — i.e. those whose span starts at or after the end of
    /// `tokens[default_index]` and before the start of the next `DEFAULT` token.
    /// ANTLR4's `getHiddenTokensToRight`. For the LAST `DEFAULT` token the upper
    /// boundary is the end of input, so a trailing comment attaches to it.
    pub fn hidden_tokens_to_right(
        &self,
        default_index: usize,
        channel: &str,
    ) -> &[(T, runtime_types::Range)] {
        let Some((_, range)) = self.tokens.get(default_index) else {
            return &[];
        };
        let upper = match self.tokens.get(default_index + 1) {
            Some((_, next)) => next.start.byte_offset,
            None => usize::MAX,
        };
        self.channel_slice_in(channel, range.end.byte_offset, upper)
    }

    /// The contiguous run of `channel` tokens whose span STARTS in
    /// `[lower, upper)`. The per-channel buffer is already in source order, so
    /// the run is located by two binary searches and returned as a borrowed
    /// slice — no allocation, no copying.
    fn channel_slice_in(
        &self,
        channel: &str,
        lower: usize,
        upper: usize,
    ) -> &[(T, runtime_types::Range)] {
        let buffer = self.tokens_on_channel(channel);
        let first = buffer.partition_point(|(_, range)| range.start.byte_offset < lower);
        let last = buffer.partition_point(|(_, range)| range.start.byte_offset < upper);
        &buffer[first..last]
    }
}

/// Specification for cross-stream synchronization constraints.
#[derive(Debug, Clone)]
pub struct SyncSpec {
    /// Synchronization constraints.
    pub constraints: Vec<SyncConstraintSpec>,
}

/// A single cross-stream synchronization constraint.
#[derive(Debug, Clone)]
pub enum SyncConstraintSpec {
    /// Align token positions in `stream_a` with `stream_b` at a boundary pattern.
    Align {
        stream_a: String,
        stream_b: String,
        boundary_pattern: String,
    },
    /// Track `auxiliary` stream positions relative to `primary` stream.
    Track { auxiliary: String, primary: String },
}

/// Specification for a tree structural invariant.
///
/// Compiled from the `tree_invariants { ... }` DSL in the `tokens` block.
/// Contains the mu-calculus formula string and invariant name for diagnostics.
#[derive(Debug, Clone)]
pub struct TreeInvariantSpec {
    /// Invariant name (e.g., "no_nested_braces").
    pub name: String,
    /// The tree constraint formula as a string representation.
    /// Compiled to `MuCalculusFormula` during pipeline analysis.
    pub formula: String,
}

/// Keyword-reservation mode for a language (PIECE 3).
///
/// Controls whether grammar-declared identifier-shaped literal terminals are
/// treated as *reserved words* (a keyword spelled like an identifier cannot
/// also lex as a variable of that name).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReservationMode {
    /// Reserve every identifier-shaped literal terminal (`Nil`, `true`,
    /// `Map`, …) as a keyword. The generic `Ident` co-accept is dropped at
    /// each such keyword's DFA accept state, collapsing the spurious
    /// "variable literally named after a keyword" over-generation.
    Auto,
    /// Reserve nothing — full ambiguity is retained (e.g. Fortran-style
    /// languages with no reserved words, where `IF`/`DO`/`THEN` may be used
    /// as identifiers). Byte-identical to the pre-reservation lexer.
    None,
}

/// Keyword-reservation policy for a language (PIECE 3).
///
/// The reserved set is **grammar-derived** — it is not a per-language
/// hardcoded list. Under [`ReservationMode::Auto`], every literal terminal
/// that is lexically an identifier (`is_keyword`) is reserved, EXCEPT those
/// explicitly opted out via `contextual` (per-terminal escape hatch for
/// contextual keywords such as method names that should still be usable as
/// variables).
///
/// The default is [`ReservationMode::None`] (no reservation), so a language
/// that does not opt in is byte-identical to the pre-reservation behavior;
/// a language enables reservation via `options { reserved_keywords: auto }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReservationPolicy {
    /// Whether identifier-shaped keywords are reserved.
    pub mode: ReservationMode,
    /// Per-terminal opt-out: terminal texts that are NOT reserved even under
    /// `Auto` (contextual keywords). Grammar-derived escape hatch used when a
    /// legitimate program names a variable after a keyword at a shared
    /// grammar position. Empty for both bundled test languages.
    pub contextual: std::collections::HashSet<String>,
}

impl Default for ReservationPolicy {
    /// No reservation by default. Enabling reservation is an explicit,
    /// per-language opt-in (`options { reserved_keywords: auto }`), which
    /// keeps every existing language's generated lexer byte-identical.
    fn default() -> Self {
        ReservationPolicy {
            mode: ReservationMode::None,
            contextual: std::collections::HashSet::new(),
        }
    }
}

impl ReservationPolicy {
    /// Reserve every identifier-shaped keyword (no per-terminal opt-outs).
    pub fn auto() -> Self {
        ReservationPolicy {
            mode: ReservationMode::Auto,
            contextual: std::collections::HashSet::new(),
        }
    }

    /// Reserve nothing (full ambiguity retained).
    pub fn none() -> Self {
        ReservationPolicy::default()
    }

    /// Whether this policy reserves anything at all.
    pub fn reserves(&self) -> bool {
        matches!(self.mode, ReservationMode::Auto)
    }

    /// Derive the reserved token-kind set from the language's terminals.
    ///
    /// A terminal is reserved iff (a) the policy mode is `Auto`, (b) the
    /// terminal is `is_keyword` (lexically an identifier — this automatically
    /// excludes operators/punctuation like `@`, `<-`, `!`, `{`), and (c) its
    /// text is not in the `contextual` opt-out set. This is the single,
    /// grammar-derived source of truth for what "reserved" means; the
    /// `reserved_set_is_grammar_derived` test asserts exactly this.
    pub fn reserved_kinds(
        &self,
        terminals: &[crate::automata::TerminalPattern],
    ) -> crate::automata::ReservedKeywords {
        if !self.reserves() {
            return crate::automata::ReservedKeywords::none();
        }
        let kinds: std::collections::HashSet<crate::automata::TokenKind> = terminals
            .iter()
            .filter(|t| t.is_keyword && !self.contextual.contains(&t.text))
            .map(|t| t.kind.clone())
            .collect();
        crate::automata::ReservedKeywords::from_kinds(kinds)
    }
}

/// Language definition input for the parser generator.
///
/// This is a simplified, serializable representation of the grammar,
/// projected from the full `LanguageDef` AST. The macros crate constructs
/// this from the `LanguageDef` and passes it to `generate_parser()`.
#[derive(Debug, Clone)]
pub struct LanguageSpec {
    /// Language name.
    pub name: String,
    /// All type/category declarations.
    pub types: Vec<CategorySpec>,
    /// All grammar rules.
    pub rules: Vec<RuleSpec>,
    /// Beam width configuration for WFST prediction pruning.
    /// Default: `BeamWidthConfig::Disabled`.
    pub beam_width: BeamWidthConfig,
    /// Optional path to a log-semiring trained model JSON file (requires `wfst-log` feature).
    /// When set, the pipeline loads learned weights and recommended beam width.
    pub log_semiring_model_path: Option<String>,
    /// Configurable literal token patterns for the lexer.
    /// Default: `LiteralPatterns::default()` (standard patterns from `literal_patterns.ebnf`).
    pub literal_patterns: LiteralPatterns,
    /// Configuration for error recovery costs and thresholds.
    /// Default: `RecoveryConfig::default()` (matches hardcoded constants).
    pub recovery_config: recovery::RecoveryConfig,
    /// Dependency groups from equations, rewrites, and the logic block.
    ///
    /// Each group is the set of constructor labels co-referenced by a single
    /// equation/rewrite rule or the entire logic block. Used for transitive
    /// liveness analysis in dead-rule detection: if any label in a group is
    /// parsing-live, all labels in the group are semantically live.
    ///
    /// Default: empty (backward compatible — no semantic info available).
    pub semantic_dependency_groups: Vec<HashSet<String>>,
    /// Custom token definitions (default mode). Overrides built-in patterns
    /// for matching names, defines new token kinds for non-matching names.
    /// Default: empty (backward compatible — uses `literal_patterns` only).
    pub custom_tokens: Vec<CustomTokenSpec>,
    /// Named lexer modes with their own DFA pipelines.
    /// Default: empty (single-mode lexing).
    pub modes: Vec<LexerModeSpec>,
    /// Cross-stream synchronization constraints.
    /// Default: None (no multi-stream analysis).
    pub sync: Option<SyncSpec>,
    /// Tree structural invariants for PATA verification.
    /// Default: empty.
    pub tree_invariants: Vec<TreeInvariantSpec>,
    /// Refinement type definitions from the `types { ... }` block.
    /// Each entry describes a type like `PosInt = { x: Int | x > 0 }`.
    /// Default: empty.
    pub refinement_types: Vec<RefinementTypeSpec>,
    /// Lowered guard configuration from the `guards { ... }` block
    /// (design doc §2A). `None` when the block is absent — backward
    /// compatible with existing language definitions.
    ///
    /// Pipeline functions consult this for theory-driven module activation,
    /// channel-driven M8/M11 dispatch, and per-predicate selectivity/cost
    /// overrides. When `None`, the pipeline falls back to heuristic
    /// keyword/structural inference.
    pub guard_config: Option<GuardConfigSpec>,
    /// Keyword-reservation policy (PIECE 3). Default:
    /// [`ReservationMode::None`] — no reservation, byte-identical lexer.
    /// Set from `options { reserved_keywords: auto | none }`.
    pub reservation_policy: ReservationPolicy,
}

/// Lowered guard configuration for pipeline consumption.
///
/// Produced by `language_def_to_spec()` from the macro-side `GuardConfig`
/// AST. All `syn` types are resolved to plain strings so the pipeline crate
/// has zero dependency on `syn`.
#[derive(Debug, Clone, Default)]
pub struct GuardConfigSpec {
    /// Theory registrations: each entry maps a theory name to its type
    /// and the set of grammar categories it handles. Used by
    /// `classify_grammar()` to replace heuristic `is_*_relation()` dispatch
    /// with data-driven module activation.
    pub theories: Vec<TheoryRegistrationSpec>,

    /// Explicit channel categories. When `Some`, only the listed
    /// categories are treated as channels for M8/M11 dispatch.
    /// When `None`, the pipeline falls back to heuristic channel
    /// inference from cross-category references.
    pub channel_categories: Option<Vec<String>>,

    /// Explicit join pattern declarations: `(label, channel_categories)`.
    /// Used to determine M8/M11 activation count and per-pattern arity.
    /// Empty when `channels {}` is omitted.
    pub join_patterns: Vec<JoinPatternSpec>,

    /// Per-predicate selectivity overrides, keyed by predicate name.
    /// Values are in [0.0, 1.0]. When a predicate name appears in this
    /// map, `estimate_predicate_selectivity()` returns the override
    /// value instead of computing a heuristic estimate.
    pub selectivity_overrides: HashMap<String, f64>,

    /// Per-predicate cost overrides, keyed by predicate name.
    /// Values are in ℕ. When a predicate name appears in this map,
    /// `estimate_predicate_cost()` and `condition_cost()` return the
    /// override value instead of computing a heuristic estimate.
    pub cost_overrides: HashMap<String, u32>,

    /// Whether the grammar author provided an explicit `connectives {}`
    /// sub-block. When `true`, the parser uses declared connective
    /// keywords; when `false`, default Rust-token connectives apply.
    pub has_explicit_connectives: bool,

    /// Whether the grammar author provided explicit predicate
    /// declarations (direct items in `guards {}`). When `true`,
    /// closed-world validation is active.
    pub has_explicit_predicates: bool,
}

/// A single theory registration, lowered from `TheoryRegistration`.
///
/// Corresponds to one `name = TheoryType for [Cat1, Cat2];` declaration
/// in the `theories {}` sub-block.
#[derive(Debug, Clone)]
pub struct TheoryRegistrationSpec {
    /// Theory name (e.g., `"arithmetic"`, `"patterns"`).
    pub name: String,
    /// Fully-qualified Rust type path as a string (e.g., `"PresburgerAlgebra"`).
    pub theory_type: String,
    /// Grammar categories this theory handles (e.g., `["Int"]`).
    /// When `None`, the theory handles all categories.
    pub handled_types: Option<Vec<String>>,
}

/// A lowered join pattern declaration: `(label, channel_param_categories)`.
#[derive(Debug, Clone)]
pub struct JoinPatternSpec {
    /// Join pattern label — must match a constructor in `terms {}`.
    pub label: String,
    /// Categories of the channel-binding parameters in declaration order.
    /// `len() >= 2` activates M8 (Multi-Tape).
    pub channel_categories: Vec<String>,
}

/// A category (type) in the language.
#[derive(Debug, Clone)]
pub struct CategorySpec {
    /// Category name (e.g., "Proc", "Name", "Int").
    pub name: String,
    /// Native Rust type name, if any (e.g., "i32", "bool").
    pub native_type: Option<String>,
    /// Whether this is the primary (first-declared) category.
    pub is_primary: bool,
    /// Whether this category has a variable variant (e.g. IVar, BVar).
    /// False for collection-only categories (List, Bag) which have no Var variant.
    pub has_var: bool,
}

impl Default for CategorySpec {
    fn default() -> Self {
        Self {
            name: String::new(),
            native_type: None,
            is_primary: false,
            has_var: false,
        }
    }
}

/// A grammar rule specification.
#[derive(Debug, Clone)]
pub struct RuleSpec {
    /// Constructor label (e.g., "PPar", "Add", "PZero").
    pub label: String,
    /// Category this rule belongs to.
    pub category: String,
    /// Syntax items describing the concrete syntax.
    pub syntax: Vec<SyntaxItemSpec>,
    /// Whether this is an infix rule.
    pub is_infix: bool,
    /// Associativity (only meaningful for infix rules).
    pub associativity: Associativity,
    /// ★ PRECEDENCE LEVELS (2026-07-28): share the preceding infix rule's precedence
    /// level rather than opening a new, tighter one (the DSL's `same` annotation).
    ///
    /// Orthogonal to `associativity`: a level is a SET of operators and each member keeps
    /// its own associativity, which is what lets Rholang's level 6 hold right-associative
    /// `matches` beside left-associative `==` and `!=`. Consumed only by
    /// [`binding_power::analyze_binding_powers`]; see
    /// [`binding_power::InfixRuleInfo::shares_level_with_previous`].
    pub shares_level_with_previous: bool,
    /// Whether this is a variable rule.
    pub is_var: bool,
    /// Whether this is a literal rule.
    pub is_literal: bool,
    /// Whether this involves a single binder.
    pub has_binder: bool,
    /// Whether this involves multiple binders.
    pub has_multi_binder: bool,
    /// Whether this is a collection rule.
    pub is_collection: bool,
    /// Collection type (if applicable).
    pub collection_type: Option<CollectionKind>,
    /// Separator for collections.
    pub separator: Option<String>,
    /// Whether this is a cross-category rule.
    pub is_cross_category: bool,
    /// Source category for cross-category rules.
    pub cross_source_category: Option<String>,
    /// Whether this is a cast rule.
    pub is_cast: bool,
    /// Source category for cast rules.
    pub cast_source_category: Option<String>,
    /// Whether this is a unary prefix operator (e.g., "-" a, "not" a).
    /// Unary prefix rules get high binding power so they only capture their immediate operand.
    pub is_unary_prefix: bool,
    /// Explicit prefix binding power for unary prefix operators.
    /// When `Some(N)`, overrides the default `max_infix_bp + 2`.
    /// Allows different prefix operators to have different binding powers.
    pub prefix_precedence: Option<u8>,
    /// Whether this is a postfix operator (e.g., a "!", a "?", a "++").
    /// Postfix rules have left binding power but no recursive right call.
    pub is_postfix: bool,
    /// Whether this has a Rust code block (HOL native).
    pub has_rust_code: bool,
    /// Rust code expression (as TokenStream).
    pub rust_code: Option<TokenStream>,
    /// Eval mode.
    pub eval_mode: Option<String>,
    /// Source location of the rule label in the `language!` macro invocation.
    /// Extracted from proc-macro span data; `None` when unavailable.
    pub source_location: Option<SourceLocation>,
    /// Stage 3.13b (2026-05-01): provenance flag distinguishing user-written
    /// rules (false) from synthetic auto-injection rules emitted by
    /// `macros/src/gen/runtime/wpda_codegen/auto_inject.rs::make_injection_rule`
    /// (true). Used by:
    /// - Stage 3.13c routing filter (`pipeline.rs:1316`) to exclude synthetic
    ///   rules from legacy unified-trampoline cast_rules.
    /// - Stage 3.13b W05 lint refinement (future) to distinguish synthetic-
    ///   induced ambiguity (Note severity) from user-authored ambiguity
    ///   (Warning severity).
    pub is_auto_injected: bool,
}

/// A syntax item in a rule.
#[derive(Debug, Clone)]
pub enum SyntaxItemSpec {
    /// A terminal token (e.g., "(", "+", "error").
    Terminal(String),
    /// A nonterminal to parse (category name, param name).
    NonTerminal { category: String, param_name: String },
    /// An identifier to capture.
    IdentCapture { param_name: String },
    /// L9-3: consume ONE token of a specific custom KIND, binding its text.
    /// `kind_name` is the declared token kind (matched via `token_to_kind ==
    /// TokenKind::Custom(kind_name)`); `param_name` is the capture slot (a
    /// synthesized `__tok_<name>` when the source had no `@`-bind). Parallel to
    /// `IdentCapture` (a terminal-ish leaf — no nonterminal target, no field
    /// sort), but gated on a specific kind rather than the generic `Ident`.
    TokenKindCapture { param_name: String, kind_name: String },
    /// A binder position.
    Binder {
        param_name: String,
        category: String,
        is_multi: bool,
    },
    /// A collection with separator.
    Collection {
        param_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
        /// Map-only separator between key and value (e.g., ":").
        /// Must be `Some` when `kind == HashMap`, otherwise `None`.
        key_val_separator: Option<String>,
    },
    /// Repeat a body pattern with separator between repetitions.
    /// Nullable (0 iterations). The body can be any SyntaxItemSpec:
    /// - NonTerminal → simple separated list
    /// - Map → structured separated list (single accumulator)
    /// - Zip { body: Map { .. } } → dual-accumulator structured list
    Sep {
        body: Box<SyntaxItemSpec>,
        separator: String,
        kind: CollectionKind,
    },
    /// Structured body pattern: multiple items forming one logical element.
    /// When inside Sep, represents the template for each iteration.
    /// When standalone, equivalent to an inline sequence of items.
    Map { body_items: Vec<SyntaxItemSpec> },
    /// Parallel dual-accumulator collection. Each iteration of the body
    /// produces values for both left and right accumulators in lockstep.
    /// The body is typically a Map whose items reference the accumulator
    /// names via their param_name fields.
    Zip {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body: Box<SyntaxItemSpec>,
    },
    /// A separated list of binder identifiers (e.g., `xs.*sep(",")` where `xs`
    /// is a multi-abstraction binder). Parsed as comma-separated idents, collected
    /// into a `Vec<String>`, then wrapped into `Vec<Binder<String>>` at construction.
    BinderCollection { param_name: String, separator: String },
    /// An optional group of syntax items.
    /// Wraps inner items in a save/restore block: if parsing fails,
    /// the position is reverted and parsing continues.
    Optional { inner: Vec<SyntaxItemSpec> },
    /// Guard expression slot (Phase 2F, predicated types).
    ///
    /// Marks where a `?guard:Guard` parameter reference appears in the
    /// syntax pattern. The macro-generated parser should switch into
    /// the language-generic predicate sublanguage parser
    /// (`mettail_runtime::parser::predicate::PredicateParser`) and
    /// produce a `mettail_runtime::BehavioralPred` runtime value to
    /// store in the corresponding term field.
    ///
    /// The surrounding language syntax pattern determines any trigger
    /// keyword (`where`, `if`, `|`, etc.) — the parser is invoked
    /// AFTER the trigger literal has been consumed.
    GuardExpression { param_name: String },
}

/// Minimal input for constructing a `RuleSpec`.
///
/// The bridge provides structural fields and DSL annotations only.
/// PraTTaIL derives all classification flags via [`classify::classify_rule()`].
#[derive(Debug, Clone)]
pub struct RuleSpecInput {
    /// Constructor label (e.g., "PPar", "Add", "PZero").
    pub label: String,
    /// Category this rule belongs to.
    pub category: String,
    /// Syntax items describing the concrete syntax.
    pub syntax: Vec<SyntaxItemSpec>,
    /// Associativity (only meaningful for infix rules).
    pub associativity: Associativity,
    /// ★ PRECEDENCE LEVELS (2026-07-28): share the preceding infix rule's precedence
    /// level rather than opening a new, tighter one (the DSL's `same` annotation).
    /// See [`RuleSpec::shares_level_with_previous`].
    pub shares_level_with_previous: bool,
    /// Explicit prefix binding power for unary prefix operators.
    pub prefix_precedence: Option<u8>,
    /// Whether this has a Rust code block (HOL native).
    pub has_rust_code: bool,
    /// Rust code expression (as TokenStream).
    pub rust_code: Option<TokenStream>,
    /// Eval mode.
    pub eval_mode: Option<String>,
    /// Source location of the rule label in the `language!` macro invocation.
    /// Extracted from proc-macro span data; `None` when unavailable.
    pub source_location: Option<SourceLocation>,
    /// Stage 3.13b (2026-05-01): provenance flag — see RuleSpec.is_auto_injected.
    /// Default false for parsed user rules; bridge sets true only for synthetic
    /// auto-injection rules emitted by `auto_inject.rs::make_injection_rule`.
    pub is_auto_injected: bool,
}

impl LanguageSpec {
    /// Construct a `LanguageSpec` from categories and minimal rule inputs.
    ///
    /// All classification flags (is_infix, is_postfix, is_cast, etc.) are
    /// derived automatically via [`classify::classify_rule()`]. The bridge
    /// only needs to provide structural data and DSL annotations.
    pub fn new(name: String, types: Vec<CategorySpec>, inputs: Vec<RuleSpecInput>) -> Self {
        Self::with_options(
            name,
            types,
            inputs,
            BeamWidthConfig::Disabled,
            None,
            LiteralPatterns::default(),
        )
    }

    /// Construct a `LanguageSpec` with optional configuration.
    ///
    /// All classification flags (is_infix, is_postfix, is_cast, etc.) are
    /// derived automatically via [`classify::classify_rule()`]. The bridge
    /// only needs to provide structural data and DSL annotations.
    #[allow(clippy::too_many_arguments)]
    pub fn with_options(
        name: String,
        types: Vec<CategorySpec>,
        inputs: Vec<RuleSpecInput>,
        beam_width: BeamWidthConfig,
        log_semiring_model_path: Option<String>,
        literal_patterns: LiteralPatterns,
    ) -> Self {
        let cat_names: Vec<String> = types.iter().map(|t| t.name.clone()).collect();
        let rules = inputs
            .into_iter()
            .map(|input| {
                let c = classify::classify_rule(&input.syntax, &input.category, &cat_names);
                RuleSpec {
                    label: input.label,
                    category: input.category,
                    syntax: input.syntax,
                    is_infix: c.is_infix,
                    is_postfix: c.is_postfix,
                    is_unary_prefix: c.is_unary_prefix,
                    is_var: c.is_var,
                    is_literal: c.is_literal,
                    has_binder: c.has_binder,
                    has_multi_binder: c.has_multi_binder,
                    is_collection: c.is_collection,
                    collection_type: c.collection_type,
                    separator: c.separator,
                    is_cross_category: c.is_cross_category,
                    cross_source_category: c.cross_source_category,
                    is_cast: c.is_cast,
                    cast_source_category: c.cast_source_category,
                    associativity: input.associativity,
                    shares_level_with_previous: input.shares_level_with_previous,
                    prefix_precedence: input.prefix_precedence,
                    has_rust_code: input.has_rust_code,
                    rust_code: input.rust_code,
                    eval_mode: input.eval_mode,
                    source_location: input.source_location,
                    is_auto_injected: input.is_auto_injected,
                }
            })
            .collect();
        LanguageSpec {
            name,
            types,
            rules,
            beam_width,
            log_semiring_model_path,
            literal_patterns,
            recovery_config: recovery::RecoveryConfig::default(),
            semantic_dependency_groups: Vec::new(),
            custom_tokens: Vec::new(),
            modes: Vec::new(),
            sync: None,
            tree_invariants: Vec::new(),
            refinement_types: Vec::new(),
            guard_config: None,
            reservation_policy: ReservationPolicy::default(),
        }
    }
}

impl RuleSpec {
    /// Construct a `RuleSpec` with automatic flag classification.
    ///
    /// Convenience for tests and benchmarks — avoids manually setting 15+ derived flags.
    /// Non-default DSL annotations (associativity, prefix_precedence, etc.) can be
    /// set on the returned value via field mutation.
    pub fn classified(
        label: impl Into<String>,
        category: impl Into<String>,
        syntax: Vec<SyntaxItemSpec>,
        category_names: &[String],
    ) -> Self {
        let category = category.into();
        let c = classify::classify_rule(&syntax, &category, category_names);
        RuleSpec {
            label: label.into(),
            category,
            syntax,
            is_infix: c.is_infix,
            is_postfix: c.is_postfix,
            is_unary_prefix: c.is_unary_prefix,
            is_var: c.is_var,
            is_literal: c.is_literal,
            has_binder: c.has_binder,
            has_multi_binder: c.has_multi_binder,
            is_collection: c.is_collection,
            collection_type: c.collection_type,
            separator: c.separator,
            is_cross_category: c.is_cross_category,
            cross_source_category: c.cross_source_category,
            is_cast: c.is_cast,
            cast_source_category: c.cast_source_category,
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        }
    }
}

// Re-exports for generated code and external use
pub use lint::{LintContext, LintDiagnostic, LintSeverity};
pub use recovery::{ParseSimulator, RecoveryConfig, SimulationResult};

// ── Refinement Type Specifications (unconditional — used by LanguageSpec) ────

/// Specification for a refinement type, passed from macros to prattail pipeline.
#[derive(Clone, Debug)]
pub struct RefinementTypeSpec {
    /// The refinement type name (e.g., "PosInt").
    pub name: String,
    /// The base category name (e.g., "Int").
    pub base_category: String,
    /// The binding variable name (e.g., "x").
    pub variable_name: String,
    /// Classification of the predicate.
    pub predicate_kind: RefinementPredKind,
    /// Serialized predicate representation for analysis.
    pub predicate_repr: String,
}

/// Classification of a refinement predicate for pipeline dispatch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefinementPredKind {
    /// Pure linear arithmetic (e.g., `x > 0`).
    Presburger,
    /// Relation queries / quantified formulas.
    Behavioral,
    /// Structural term patterns.
    Structural,
    /// Mixed domain requiring ProductAlgebra composition.
    Mixed,
}

/// Analysis data produced by the PraTTaIL pipeline during parser generation.
///
/// Captures WFST-derived analysis that would otherwise be discarded after
/// codegen. This data bridges the PraTTaIL pipeline (parser generation) to
/// the macros crate (Ascent codegen), enabling optimizations such as:
/// - Dead-code elimination of Ascent rules referencing dead constructors
/// - WFST-weight-guided rule ordering for cache locality
/// - Isomorphic WFST detection for template instantiation
///
/// Constructed by [`generate_parser_with_analysis()`] and consumed by the
/// macros crate's `generate_ascent_source()`.
#[derive(Debug, Clone, Default)]
pub struct PipelineAnalysis {
    /// Labels of dead rules detected by the 4-tier WFST analysis.
    ///
    /// Includes Tier 1 (LiteralNoNativeType) and Tier 2 (UnreachableCategory)
    /// rules from [`pipeline::collect_dead_rule_labels()`]. Tier 3/4 are excluded
    /// due to false-positive risk (see `collect_dead_rule_labels` doc).
    pub dead_rule_labels: HashSet<String>,

    /// Categories where ALL rules are dead (fully unreachable).
    ///
    /// A category is unreachable if every rule belonging to it appears in
    /// `dead_rule_labels`. Ascent codegen can skip generating relations and
    /// rules for these categories entirely.
    pub unreachable_categories: HashSet<String>,

    /// Per-constructor tropical weight from WFST dispatch (lower = more frequent).
    ///
    /// Populated from `PredictionWfst` actions. Used for:
    /// - Rule ordering (Sprint 3): frequent constructors first for cache locality
    /// - Match arm ordering (Sprint 4): better branch prediction in congruence pools
    /// - Variable selectivity (Sprint 7): constructor frequency as selectivity proxy
    pub constructor_weights: HashMap<String, f64>,

    /// Per-category mean tropical weight across all dispatch actions.
    ///
    /// Used for coarse category-level ordering decisions. Lower weight indicates
    /// a category whose constructors are dispatched to more frequently.
    pub category_weights: HashMap<String, f64>,

    /// Groups of categories with alpha-equivalent WFSTs (De Bruijn canonicalized).
    ///
    /// Only groups with >= 2 members are included. Categories in the same group
    /// have identical WFST structure (states, transitions, weights) differing only
    /// in action labels. Enables template instantiation (Sprint 8).
    pub isomorphic_groups: Vec<Vec<String>>,

    /// Per-group De Bruijn action map: `(group_index, de_bruijn_idx)` -> `Vec<(category, rule_label)>`.
    ///
    /// Maps each De Bruijn-canonicalized action index within an isomorphic group
    /// to the concrete `(category_name, constructor_label)` pairs across group members.
    /// Used by Sprint 8 for `macro_rules!` template parameter generation.
    pub isomorphic_action_maps: Vec<HashMap<u32, Vec<(String, String)>>>,

    /// Per-category decision trees built during parser code generation.
    ///
    /// Available for downstream composition analysis (X06/X07), incremental
    /// codegen (Layer 10 `.prattail-cache`), and diagnostic tools.
    pub decision_trees: HashMap<String, decision_tree::CategoryDecisionTree>,

    /// Binder categories where register analysis proves the bound name
    /// is stored but never tested (dead register). Codegen can skip
    /// alpha-equivalence checking for these categories (RA01-SKIP).
    pub dead_binder_categories: HashSet<String>,

    /// Whether the grammar's bracket structure is deterministic (VPA analysis).
    /// True when `is_determinizable == true` AND `alphabet_mismatches` is empty.
    /// Currently informational; may enable future optimizations (V05-INFO).
    pub bracket_deterministic: bool,

    /// Tokens that VPA analysis found used as both call and return symbols.
    /// Recovery should penalize InsertToken for these tokens (Sprint A2).
    pub bracket_mismatch_tokens: HashSet<String>,

    /// Categories whose multi-tape analysis shows they are independent
    /// (no cross-tape constraints). Currently informational (MT01-INFO).
    pub independent_categories: HashSet<String>,

    /// Tokens where symbolic guard analysis proves one category's guard subsumes another's.
    /// These tokens can be dispatched without backtracking (subsuming category tried first).
    pub guard_disambiguated_tokens: HashSet<String>,

    /// Per-category Shannon entropy from probabilistic analysis.
    /// Higher entropy indicates more ambiguous alternatives, suggesting a wider
    /// beam is needed during spillover beam pruning. Categories with entropy
    /// near zero have a single dominant rule and need no beam at all.
    ///
    /// # ⚠ `BTreeMap`, because this map's ITERATION ORDER reaches generated code
    ///
    /// `macros/src/gen/test_gen/simulation_tests.rs` picks the highest-entropy
    /// category with `.iter().max_by(..)` and interpolates its name into an
    /// emitted signature — `fn sim_<lang>_proptest_campaign(term in arb_<cat>(3))`.
    /// `Iterator::max_by` returns the **last** maximal element, so under a
    /// `HashMap` a *tie* was resolved by hash order and the generated bytes
    /// differed between builds of the same grammar.
    ///
    /// Ties are not exotic. Two categories with the same multiset of rule
    /// weights have bit-identical Shannon entropy, and every single-rule category
    /// has entropy exactly `0.0`. Measured with a two-category fixture whose
    /// rule profiles match: 20 runs, 2 distinct winners.
    ///
    /// A key-ordered carrier makes that tie-break a function of the grammar
    /// alone, at the producer, without the consumer having to sort — which
    /// matters because the consumer lives in another crate and would otherwise
    /// need to know a rule it has no way to discover.
    pub per_category_entropy: std::collections::BTreeMap<String, f64>,

    /// Categories that participate in accepting SCCs (recursive grammar loops).
    /// Recovery prefers InsertToken in these categories to maintain the loop.
    pub recursive_scc_categories: HashSet<String>,
}

/// Generate a complete parser for a language specification.
///
/// This is the main entry point. Returns a `TokenStream` containing:
/// - Token enum
/// - Position and Range structs
/// - Lexer function
/// - Parse functions for each category
/// - Helper functions
///
/// Internally delegates to `pipeline::run_pipeline()` which:
/// 1. Extracts Send+Sync data bundles from `&LanguageSpec` (main thread)
/// 2. Runs lexer then parser codegen sequentially
/// 3. Concatenates results and parses into a single `TokenStream`
///
/// NOTE: Parse entry points (`impl Cat { fn parse() }`) are generated by the
/// macros crate, not by PraTTaIL, to avoid duplication and to integrate
/// with the macros crate's error handling.
///
/// # Errors
///
/// `Err(diagnostic)` when a grammar-level soundness gate rejects the spec. The
/// message is user-facing; `macros` renders it as `compile_error!` at the
/// `language!` invocation.
#[inline]
pub fn generate_parser(spec: &LanguageSpec) -> Result<TokenStream, String> {
    pipeline::run_pipeline(spec)
}

/// Generate a complete parser along with pipeline analysis data.
///
/// Like [`generate_parser()`], but additionally returns a [`PipelineAnalysis`]
/// capturing WFST-derived analysis data (dead rules, constructor weights,
/// category weights, isomorphic groups) that would otherwise be discarded
/// after codegen.
///
/// The macros crate uses this analysis to optimize Ascent codegen:
/// - Dead-code elimination (Sprint 1)
/// - WFST-weight-guided rule ordering (Sprint 3)
/// - Isomorphic WFST template instantiation (Sprint 8)
///
/// # Errors
///
/// `Err(diagnostic)` when a grammar-level soundness gate rejects the spec.
#[inline]
pub fn generate_parser_with_analysis(
    spec: &LanguageSpec,
) -> Result<(TokenStream, PipelineAnalysis), String> {
    pipeline::run_pipeline_with_analysis(spec)
}
