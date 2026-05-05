//! Grammar IR — data shapes describing grammar rules for Walker-side analysis.
//!
//! These types are the intermediate representation between the parsed
//! grammar (in `macros/src/ast/`) and the emitted parser code. They
//! describe each rule's structure in a form suitable for analyses
//! (`rd_analysis`, `classify`, `wfst`, `lint`, `ebnf`, `decision_tree`,
//! `prediction`) and Walker codegen (`macros/src/gen/runtime/wpds_codegen/`).
//!
//! Pure data — no emitter functions, no thread-locals, no `use` of
//! `automata`/`wfst`/`prediction`/etc. Walker codegen consumes them via
//! `bundle.cast_rules` / `bundle.cross_rules` / `bundle.rd_rules`.

// ─── Recursive-descent rule structure ─────────────────────────────────────

/// Information about a grammar rule needed for Walker-side analyses.
///
/// Originally defined in `prattail/src/recursive.rs:14`. Migrated here
/// when `recursive.rs` was deleted in Stage 10.5b.
#[derive(Debug, Clone)]
pub struct RDRuleInfo {
    /// Constructor label (e.g., "PInputs", "PPar").
    pub label: String,
    /// Category this rule belongs to (e.g., "Proc").
    pub category: String,
    /// Syntax items describing the concrete syntax.
    pub items: Vec<RDSyntaxItem>,
    /// Whether this rule involves a single binder.
    pub has_binder: bool,
    /// Whether this rule involves multiple binders.
    pub has_multi_binder: bool,
    /// Whether this rule is a collection (PPar, etc.).
    pub is_collection: bool,
    /// Collection type if applicable.
    pub collection_type: Option<CollectionKind>,
    /// Separator for collection items.
    pub separator: Option<String>,
    /// Binding power for the recursive call in unary prefix rules.
    /// When set, NonTerminal calls use this bp instead of 0.
    pub prefix_bp: Option<u8>,
    /// Eval mode for HOL rules.
    pub eval_mode: Option<String>,
}

/// A syntax item in a rule's concrete syntax.
///
/// Originally defined in `prattail/src/recursive.rs:40`. Migrated here
/// when `recursive.rs` was deleted in Stage 10.5b.
#[derive(Debug, Clone)]
pub enum RDSyntaxItem {
    /// A fixed terminal token to match (e.g., "(", "+", "error").
    Terminal(String),
    /// A nonterminal to parse (category name, parameter name).
    NonTerminal { category: String, param_name: String },
    /// An identifier to capture (not a category — a raw identifier).
    IdentCapture { param_name: String },
    /// A binder position.
    Binder {
        param_name: String,
        binder_category: String,
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
    /// A separated list using #sep pattern op.
    SepList {
        collection_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
    },
    /// Repeat a body pattern with separator between repetitions.
    Sep {
        body: Box<RDSyntaxItem>,
        separator: String,
        kind: CollectionKind,
    },
    /// Structured body pattern: multiple items forming one logical element.
    Map {
        body_items: Vec<RDSyntaxItem>,
    },
    /// Parallel dual-accumulator collection.
    Zip {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body: Box<RDSyntaxItem>,
    },
    /// A separated list of binder identifiers.
    BinderCollection { param_name: String, separator: String },
    /// An optional group.
    Optional { inner: Vec<RDSyntaxItem> },
    /// Guard expression slot (Phase 2F, predicated types).
    ///
    /// See `SyntaxItemSpec::GuardExpression` for full semantics. Walker
    /// codegen emits a call to `mettail_runtime::parser::parse_predicate_from_str`
    /// that consumes input up to the next structural delimiter and
    /// produces a `mettail_runtime::BehavioralPred` value.
    GuardExpression { param_name: String },
}

/// Kind of collection.
///
/// Originally defined in `prattail/src/recursive.rs:103`. Migrated here
/// when `recursive.rs` was deleted in Stage 10.5b.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollectionKind {
    HashBag,
    HashSet,
    Vec,
    HashMap,
}

// ─── Cross-category dispatch rules ────────────────────────────────────────

/// A cross-category rule that produces a result in one category from
/// operands in another category.
///
/// Originally defined in `prattail/src/dispatch.rs:32`. Migrated here
/// when `dispatch.rs` was deleted in Stage 10.5b.
#[derive(Debug, Clone)]
pub struct CrossCategoryRule {
    /// Constructor label (e.g., "Eq", "Lt").
    pub label: String,
    /// Source category (operand type, e.g., "Int").
    pub source_category: String,
    /// Result category (e.g., "Bool").
    pub result_category: String,
    /// The infix operator terminal (e.g., "==", "<").
    pub operator: String,
    /// Whether save/restore is needed (ambiguous FIRST overlap).
    pub needs_backtrack: bool,
}

/// A cast rule that embeds one category into another.
///
/// Originally defined in `prattail/src/dispatch.rs:47`. Migrated here
/// when `dispatch.rs` was deleted in Stage 10.5b.
#[derive(Debug, Clone)]
pub struct CastRule {
    /// Constructor label (e.g., "CastInt", "CastBool").
    pub label: String,
    /// Source category (e.g., "Int").
    pub source_category: String,
    /// Target category (e.g., "Proc").
    pub target_category: String,
    /// True when source and target categories share at least one infix
    /// operator terminal. When true, the cast-arm emission passes
    /// `u8::MAX` as `min_bp` to `parse_{source}` so the shared infix
    /// operator (e.g., `+` shared by Int and BigInt with IntToBigInt
    /// injection) binds to the target's rule, not the source's.
    /// Default: `false` (safe for cases where target has no shared
    /// infix with source, e.g., ProcInt where Proc has no infix).
    pub shares_infix_with_target: bool,
}
