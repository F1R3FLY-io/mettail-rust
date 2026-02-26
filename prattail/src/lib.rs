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
pub mod trampoline;

// ── WFST modules (feature = "wfst") ────────────────────────────────────────
#[cfg(feature = "wfst")]
pub mod compose;
#[cfg(feature = "wfst")]
pub mod lattice;
#[cfg(feature = "wfst")]
pub mod recovery;
#[cfg(feature = "wfst")]
pub mod token_id;
#[cfg(feature = "wfst")]
pub mod wfst;

// ── Log semiring modules (feature = "wfst-log", implies "wfst") ────────────
#[cfg(feature = "wfst-log")]
pub mod forward_backward;
#[cfg(feature = "wfst-log")]
pub mod log_push;
#[cfg(feature = "wfst-log")]
pub mod training;

#[cfg(feature = "grammar-gen")]
pub mod grammar_gen;

#[cfg(test)]
mod tests;

use proc_macro2::TokenStream;

use binding_power::Associativity;
use recursive::CollectionKind;

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
    /// Requires the `wfst` feature.
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

/// Dispatch strategy for cross-category and prefix handler ordering.
///
/// Controls whether the parser uses FIRST-set declaration-order dispatch (static)
/// or WFST-weighted dispatch (weighted). The `auto` mode selects based on grammar
/// complexity metrics.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum DispatchStrategy {
    /// FIRST-set ordering with linear recovery (default).
    /// No WFST overhead — optimal for small/medium grammars.
    #[default]
    Static,

    /// WFST-weighted dispatch and recovery.
    /// Beneficial for grammars with ≥30 rules or ≥3 ambiguous cross-category overlaps.
    /// Requires the `wfst` feature; falls back to `Static` without it.
    Weighted,

    /// Auto-select based on grammar complexity metrics:
    /// - `total_rules >= 30 AND cross_category_count > 0` → Weighted
    /// - `ambiguous_overlap_count >= 3` → Weighted
    /// - Otherwise → Static
    Auto,
}

impl DispatchStrategy {
    /// Resolve an `Auto` strategy into a concrete `Static` or `Weighted` decision
    /// based on grammar metrics.
    ///
    /// When the `wfst` feature is disabled, always returns `Static` (with a warning
    /// if the user explicitly requested `Weighted`).
    ///
    /// # Arguments
    /// - `total_rules`: Total number of grammar rules
    /// - `cross_category_count`: Number of cross-category rules
    /// - `ambiguous_overlap_count`: Number of cross-category pairs with ambiguous FIRST-set overlaps
    #[allow(unused_variables)]
    pub fn resolve(
        &self,
        total_rules: usize,
        cross_category_count: usize,
        ambiguous_overlap_count: usize,
    ) -> DispatchStrategy {
        #[cfg(not(feature = "wfst"))]
        {
            if *self == DispatchStrategy::Weighted {
                eprintln!(
                    "warning: dispatch: weighted requires --features wfst; \
                     falling back to static dispatch"
                );
            }
            DispatchStrategy::Static
        }

        #[cfg(feature = "wfst")]
        match self {
            DispatchStrategy::Static => DispatchStrategy::Static,
            DispatchStrategy::Weighted => DispatchStrategy::Weighted,
            DispatchStrategy::Auto => {
                if (total_rules >= 30 && cross_category_count > 0) || ambiguous_overlap_count >= 3 {
                    DispatchStrategy::Weighted
                } else {
                    DispatchStrategy::Static
                }
            },
        }
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
    /// Dispatch strategy: static (FIRST-set ordering), weighted (WFST), or auto.
    /// Default: `DispatchStrategy::Static`.
    pub dispatch_strategy: DispatchStrategy,
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
    /// A zip+map+sep pattern operation.
    ///
    /// Represents a separated list where each element is a structured pattern
    /// from a zip+map chain. E.g., `#zip(ns,xs).#map(|n,x| n "?" x).#sep(",")`.
    ZipMapSep {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body_items: Vec<SyntaxItemSpec>,
        separator: String,
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
            DispatchStrategy::Static,
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
        dispatch_strategy: DispatchStrategy,
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
                }
            })
            .collect();
        LanguageSpec {
            name,
            types,
            rules,
            beam_width,
            log_semiring_model_path,
            dispatch_strategy,
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
        }
    }
}

/// Generate a complete parser for a language specification.
///
/// This is the main entry point. Returns a `TokenStream` containing:
/// - Token enum
/// - Span struct
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
