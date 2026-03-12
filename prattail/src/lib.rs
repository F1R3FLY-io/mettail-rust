// AL03: SIMD-accelerated whitespace skipping requires portable_simd (nightly).
#![cfg_attr(feature = "simd-whitespace", feature(portable_simd))]

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

pub mod automata;
pub mod binding_power;
pub mod classify;
pub mod dispatch;
pub mod ebnf;
pub mod lexer;
pub mod pipeline;
pub mod pratt;
pub mod prediction;
pub mod recursive;
pub mod token_id;
pub mod trampoline;
pub mod wfst;

pub mod compose;
pub mod composition_optimize;
pub mod composition_verify;
pub mod cost_benefit;
pub mod decision_tree;
pub mod lattice;
pub mod lint;
pub mod prefix_trie;
pub mod recovery;
pub mod runtime_types;
pub mod tensor;
pub mod transducer;
pub mod wpds;

// ── Algebraic program analysis (always-on — generic over any StarSemiring) ──
// Tarjan path expression algorithm + interprocedural extension
// (Kincaid, Cyphert, Breck & Reps, 2019).
pub mod algebraic;

// ── Newton's method for semiring fixpoints (always-on — generic over any
// StarSemiring) ─────────────────────────────────────────────────────────────
pub mod newton;

// ── Forward-backward analysis (always-on — generic over any semiring) ──────
// The core algorithm is semiring-generic and used by A4 (BooleanWeight).
// LogWeight-specific tests are feature-gated within the module itself.
pub mod forward_backward;

// ── Log semiring modules (feature = "wfst-log") ────────────────────────────
#[cfg(feature = "wfst-log")]
pub mod log_push;
#[cfg(feature = "wfst-log")]
pub mod training;

#[cfg(feature = "grammar-gen")]
pub mod grammar_gen;

// ── Mathematical Analysis & Theorem Proving modules ─────────────────────────

/// Provenance semiring N[X]: polynomial semiring tracking HOW facts are derived.
#[cfg(feature = "provenance")]
pub mod provenance;

/// Relational weight domain: binary relations on finite sets for WPDS analysis.
#[cfg(feature = "wpds-relational")]
pub mod relational;

/// EWPDS: Extended WPDS with merging functions for local variable handling.
#[cfg(feature = "wpds-extended")]
pub mod ewpds;

/// ARA: Affine-Relation Analysis weight domain (vector spaces of matrices).
/// Discovers all interprocedural affine relationships via WPDS analysis.
#[cfg(feature = "wpds-ara")]
pub mod ara;

/// Kleene Algebra with Tests: decidable Hoare logic and program equivalence.
#[cfg(feature = "kat")]
pub mod kat;

/// Visibly Pushdown Automata: decidable equivalence/inclusion for structured grammars.
#[cfg(feature = "vpa")]
pub mod vpa;

/// TRS analysis: confluence checking (critical pairs) and termination (dependency pairs).
#[cfg(feature = "trs-analysis")]
pub mod confluence;
#[cfg(feature = "trs-analysis")]
pub mod termination;

/// Buchi/Parity automata: infinite-word acceptance for liveness properties.
#[cfg(feature = "omega")]
pub mod buchi;

/// LTL model checking: WPDS x Buchi product for temporal property verification.
#[cfg(feature = "ltl")]
pub mod ltl;

/// Weighted Tree Automata: term recognition, ranking, and transduction.
#[cfg(feature = "tree-automata")]
pub mod tree_automaton;

/// Alternating automata: universal branching for game semantics and CTL.
#[cfg(feature = "alternating")]
pub mod alternating;

/// Nominal automata: orbit-finite sets for name-passing calculi.
#[cfg(feature = "nominal")]
pub mod nominal;

/// Petri nets / VASS: concurrent process analysis.
#[cfg(feature = "petri")]
pub mod petri;

/// Cost Register Automata: streaming quantitative computation.
#[cfg(feature = "cra")]
pub mod cra;

/// Theory morphisms: cross-theory translation and proof transfer.
#[cfg(feature = "morphisms")]
pub mod morphism;

/// Layered proof output: verdicts, human-readable explanations, Rocq certificates.
#[cfg(feature = "proofs")]
pub mod proof_output;

// ── Advanced Automata Infrastructure ─────────────────────────────────────────

/// Symbolic automata: predicate-labeled transitions over infinite domains.
/// BooleanAlgebra trait, decidability classification (T1-T4), guard analysis.
#[cfg(feature = "symbolic-automata")]
pub mod symbolic;

/// Weighted MSO logic: grammar property specification, lint-as-formula,
/// Büchi-Elgot-Trakhtenbrot theorem bridge (Droste & Gastin 2007).
#[cfg(feature = "weighted-mso")]
pub mod weighted_mso;

/// Parity alternating tree automata: mu-calculus model checking on ASTs,
/// structural verification, test generation (Emerson & Jutla 1991).
#[cfg(feature = "parity-tree-automata")]
pub mod parity_tree;

/// Register automata: data-aware finite-state computation with register storage.
/// Context-sensitive parsing, binding verification (Kaminski & Francez 1994).
#[cfg(feature = "register-automata")]
pub mod register_automata;

/// Probabilistic automata: statistical disambiguation, expected-case optimization,
/// corpus-driven weight training via Baum-Welch EM.
#[cfg(feature = "probabilistic")]
pub mod probabilistic;

/// Multi-tape automata: synchronized multi-stream computation with k tapes.
/// Multi-channel receives, parallel tokenization (Kempe 2004).
#[cfg(feature = "multi-tape")]
pub mod multi_tape;

/// Multiset automata: multiset-weighted computation for process multiplicity
/// and resource analysis (Müller, Weiß & Lochau 2024).
#[cfg(feature = "multiset-automata")]
pub mod multiset_automata;

/// Weighted two-way transducers: bidirectional weighted transductions for
/// cross-channel constraint propagation (Feng & Maletti 2022).
#[cfg(feature = "two-way-transducer")]
pub mod two_way_transducer;

/// Predicate Dispatch Automaton: algebraic variety classification for directed
/// module dispatch. Decomposes predicate formulas into morphemes and activates
/// only the relevant Phase 7 modules (Eilenberg variety theorem).
#[cfg(feature = "predicate-dispatch")]
pub mod predicate_dispatch;

/// Safety/liveness verification API: WPDS-based property checking.
pub mod verify;

/// Counterexample-Guided Abstraction Refinement (CEGAR): iterative abstraction
/// refinement over the BooleanWeight -> CountingWeight -> TropicalWeight ladder.
pub mod cegar;

/// Repair suggestion engine: analysis-driven fix recommendations.
pub mod repair;

#[cfg(test)]
mod tests;
#[cfg(test)]
pub mod test_generators;

use std::collections::{HashMap, HashSet};
use std::fmt;

use proc_macro2::TokenStream;

use binding_power::Associativity;
use recursive::CollectionKind;

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
#[derive(Debug, Clone)]
pub struct LiteralPatterns {
    /// Integer literal pattern (e.g., `[0-9]+`).
    pub integer: String,
    /// Float literal pattern (e.g., `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`).
    pub float: String,
    /// String literal pattern (e.g., `"([^"\\]|\\.)*"`).
    pub string: String,
    /// Identifier pattern (e.g., `[a-zA-Z_][a-zA-Z0-9_]*`).
    pub ident: String,
}

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
}

/// Result of multi-stream lexing.
///
/// Contains the main token stream (consumed by the parser) plus auxiliary streams
/// for tokens routed via `-> stream_name` annotations in the `tokens { ... }` block.
/// Auxiliary streams are available as metadata for tools (IDE comment extraction,
/// formatter whitespace preservation, etc.).
///
/// When no `-> stream` annotations exist, `streams` is empty (zero allocation).
#[derive(Debug, Clone)]
pub struct LexResult<T> {
    /// Main token stream (consumed by the parser). Includes the Eof token.
    pub tokens: Vec<(T, runtime_types::Range)>,
    /// Auxiliary streams (comments, whitespace, etc.), keyed by stream name.
    pub streams: std::collections::HashMap<String, Vec<(T, runtime_types::Range)>>,
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
    Track {
        auxiliary: String,
        primary: String,
    },
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
    Map {
        body_items: Vec<SyntaxItemSpec>,
    },
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
                    prefix_precedence: input.prefix_precedence,
                    has_rust_code: input.has_rust_code,
                    rust_code: input.rust_code,
                    eval_mode: input.eval_mode,
                    source_location: input.source_location,
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
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
        }
    }
}

// Re-exports for generated code and external use
pub use recovery::{RecoveryConfig, ParseSimulator, SimulationResult};
pub use lint::{LintDiagnostic, LintSeverity, LintContext};

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
    #[cfg(feature = "register-automata")]
    pub dead_binder_categories: HashSet<String>,

    /// Whether the grammar's bracket structure is deterministic (VPA analysis).
    /// True when `is_determinizable == true` AND `alphabet_mismatches` is empty.
    /// Currently informational; may enable future optimizations (V05-INFO).
    #[cfg(feature = "vpa")]
    pub bracket_deterministic: bool,

    /// Upper bound on valid nesting depth from VPA analysis.
    /// Recovery at depths exceeding this bound strongly favors skip.
    #[cfg(feature = "vpa")]
    pub vpa_max_nesting_bound: Option<usize>,

    /// Tokens that VPA analysis found used as both call and return symbols.
    /// Recovery should penalize InsertToken for these tokens (Sprint A2).
    #[cfg(feature = "vpa")]
    pub bracket_mismatch_tokens: HashSet<String>,

    /// Categories whose multi-tape analysis shows they are independent
    /// (no cross-tape constraints). Currently informational (MT01-INFO).
    #[cfg(feature = "multi-tape")]
    pub independent_categories: HashSet<String>,

    /// Tokens where symbolic guard analysis proves one category's guard subsumes another's.
    /// These tokens can be dispatched without backtracking (subsuming category tried first).
    #[cfg(feature = "symbolic-automata")]
    pub guard_disambiguated_tokens: HashSet<String>,

    /// Per-category Shannon entropy from probabilistic analysis.
    /// Higher entropy indicates more ambiguous alternatives, suggesting a wider
    /// beam is needed during spillover beam pruning. Categories with entropy
    /// near zero have a single dominant rule and need no beam at all.
    #[cfg(feature = "probabilistic")]
    pub per_category_entropy: HashMap<String, f64>,

    /// Categories that participate in accepting SCCs (recursive grammar loops).
    /// Recovery prefers InsertToken in these categories to maintain the loop.
    #[cfg(feature = "omega")]
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
/// 2. Runs lexer and parser codegen in parallel via `rayon::join`
/// 3. Concatenates results and parses into a single `TokenStream`
///
/// NOTE: Parse entry points (`impl Cat { fn parse() }`) are generated by the
/// macros crate, not by PraTTaIL, to avoid duplication and to integrate
/// with the macros crate's error handling.
#[inline]
pub fn generate_parser(spec: &LanguageSpec) -> TokenStream {
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
#[inline]
pub fn generate_parser_with_analysis(spec: &LanguageSpec) -> (TokenStream, PipelineAnalysis) {
    pipeline::run_pipeline_with_analysis(spec)
}
