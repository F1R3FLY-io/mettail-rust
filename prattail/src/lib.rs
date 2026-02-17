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
pub mod dispatch;
pub mod ebnf;
pub mod lexer;
pub mod pipeline;
pub mod pratt;
pub mod prediction;
pub mod recursive;
pub mod trampoline;

#[cfg(test)]
mod tests;

use proc_macro2::TokenStream;

use binding_power::Associativity;
use recursive::CollectionKind;

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
    Binder { param_name: String, category: String },
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
    /// An optional group of syntax items.
    /// Wraps inner items in a save/restore block: if parsing fails,
    /// the position is reverted and parsing continues.
    Optional {
        inner: Vec<SyntaxItemSpec>,
    },
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
