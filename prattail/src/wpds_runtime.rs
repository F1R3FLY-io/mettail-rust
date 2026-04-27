//! WPDS runtime types: reactive FSM, stack symbols, control directives.
//!
//! Stage 1 of W7 plan v5.1 (originally) — extended by Stage 6 Phase A.1 with
//! semantic-action machinery (`SemanticBuilder`, `ActionArg`, `ActionEntry`,
//! `WpdsTokenSource`, `BinderHandle`) that the codegen and walker share.
//!
//! ## 📌 Long-term recovery note (visible here, in survey, and in Stage 10 audit)
//!
//! Recovery is currently wired at the **wrapper level** (see
//! `parse_<Cat>_via_wpds`): when the walker terminates in `WpdsState::Error`,
//! the wrapper invokes `mettail_prattail::recovery::find_best_recovery` (the
//! existing WFST-based min-cost repair) and retries. This is pragmatic but
//! not ideal.
//!
//! **Long-term ideal:** recovery should be encoded as alternate WPDS edges
//! — Skip/Delete/Substitute/Insert rules that fan out from every
//! prefix-dispatch state, weighted so `LexicographicWeight` lex-min selects
//! them only when no primary rule matches. When that lands, the wrapper
//! plumbing is deleted.
//!
//! The note is also in `prattail/docs/design/wpds-migration-survey.md` §4
//! and `prattail/docs/design/wpds-stage-10-audit.md` as "post-Stage-10
//! follow-up work."
//!
//! ## Reactive contract
//!
//! `WpdsState × WpdsEvent → WpdsTransition` (pure function), per the
//! MeTTaTron-style mandate. External consumers (LSP/DAP/REPL/nREPL) drive
//! `WpdsWalker::process_event` (Stage 4) at their own pace; the
//! `WalkerConsumer` trait (Stage 5) is the secondary side-effect callback.
//!
//! ## Relation to the offline-analysis WPDS
//!
//! The existing [`crate::wpds`] module provides a string-typed `StackSymbol`
//! suitable for compile-time poststar/prestar analysis. This module adds
//! [`StackSymbolV2`] with integer indices for runtime hot-path use. Both
//! coexist; the runtime walker (Stage 4+) uses V2 exclusively.
//!
//! ## Survey reference
//!
//! See `prattail/docs/design/wpds-migration-survey.md` (W7 Stage 0) §4 for
//! the full mandate-to-stage trace. Mandates M5, M6, M7 from the survey are
//! satisfied by this module's type definitions.

use std::any::Any;
use std::fmt;

use crate::automata::semiring::Semiring;
use crate::automata::TokenKind;
use crate::gss::GssNodeId;

// ══════════════════════════════════════════════════════════════════════════════
// Stack symbols (M5: WPDS rule emission carries category + rule index + BP)
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of a stack symbol's role in the parse.
///
/// Used by the walker (Stage 4) to dispatch on what to do at a given stack
/// frame: enter a fresh category, continue mid-rule, await an infix RHS, or
/// pop and return.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SymbolKind {
    /// Entering a category at top level (push symbol onto stack).
    CategoryEntry,
    /// Mid-rule at item position N (0-based index into the rule's syntax items).
    RuleAt(u8),
    /// After consuming an infix operator, awaiting the right-hand side.
    InfixContinuation,
    /// About to pop this frame and return to the caller.
    Return,
    /// Phase 4: marker pushed at collection-literal open delimiter so the
    /// engine knows we're inside a collection scope. The symbol's
    /// `(category_src_idx, rule_index_in_category)` pair identifies the
    /// collection rule; `bp` carries an 8-bit accumulator id pointing into
    /// `SemanticBuilder.collection_stack`.
    CollectionMarker,
}

/// A WPDS stack symbol indexed by integer category and rule position.
///
/// Designed for runtime hot-path use: 8 bytes total (vs. ~96 bytes for
/// [`crate::wpds::StackSymbol`] which uses two `String`s). Indices reference
/// the language's source-order arrays:
///
/// - `category_src_idx`: position in `language!`'s declared categories.
/// - `rule_index_in_category`: position within that category's `rules { … }` block.
///
/// Both indices are stable across compilation; tiebreak ordering uses them
/// directly (lower index wins).
///
/// ## Tiebreak compatibility
///
/// Per plan v5 mandate, source-category-order is the primary tiebreak; rule-
/// within-category is the secondary tiebreak. Both are encoded here with no
/// extra cost. `LexicographicWeight` (Stage 2) consumes these two indices
/// via min-of-product semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StackSymbolV2 {
    /// Category index in the language's declared source order.
    pub category_src_idx: u16,
    /// Rule index within the category (declaration order).
    pub rule_index_in_category: u16,
    /// Optional binding power (None for non-Pratt categories).
    pub bp: Option<u8>,
    /// What this symbol represents.
    pub kind: SymbolKind,
}

impl StackSymbolV2 {
    /// Construct a category entry symbol (just before the first prefix dispatch).
    pub fn category_entry(category_src_idx: u16) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category: 0,
            bp: None,
            kind: SymbolKind::CategoryEntry,
        }
    }

    /// Construct a mid-rule symbol at the given item position.
    pub fn rule_at(
        category_src_idx: u16,
        rule_index_in_category: u16,
        position: u8,
        bp: Option<u8>,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category,
            bp,
            kind: SymbolKind::RuleAt(position),
        }
    }

    /// Construct an infix-continuation symbol (RHS of an infix operator pending).
    pub fn infix_continuation(
        category_src_idx: u16,
        rule_index_in_category: u16,
        bp: u8,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category,
            bp: Some(bp),
            kind: SymbolKind::InfixContinuation,
        }
    }

    /// Phase 4: construct a collection-marker symbol. `accumulator_id`
    /// is packed into the 8-bit `bp` field (collections never nest more
    /// than 256 deep in practice).
    pub fn collection_marker(
        result_src_idx: u16,
        rule_idx: u16,
        accumulator_id: u8,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(accumulator_id),
            kind: SymbolKind::CollectionMarker,
        }
    }

    /// Construct a return symbol (pop pending).
    pub fn return_symbol(category_src_idx: u16, rule_index_in_category: u16) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category,
            bp: None,
            kind: SymbolKind::Return,
        }
    }

    /// Builder-style: convert this symbol into a `Return`-kind symbol
    /// (preserving `category_src_idx`, `rule_index_in_category`, and `bp`).
    /// Used by Phase A.2 atomic-rule emission.
    pub fn with_kind_return(self) -> Self {
        StackSymbolV2 {
            kind: SymbolKind::Return,
            ..self
        }
    }
}

impl fmt::Display for StackSymbolV2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bp_suffix = match self.bp {
            Some(bp) => format!("@bp{}", bp),
            None => String::new(),
        };
        match self.kind {
            SymbolKind::CategoryEntry => {
                write!(f, "⟨cat#{}⟩{}", self.category_src_idx, bp_suffix)
            }
            SymbolKind::RuleAt(pos) => write!(
                f,
                "⟨cat#{}.rule#{}@{}⟩{}",
                self.category_src_idx, self.rule_index_in_category, pos, bp_suffix
            ),
            SymbolKind::InfixContinuation => write!(
                f,
                "⟨cat#{}.rule#{}.infix⟩{}",
                self.category_src_idx, self.rule_index_in_category, bp_suffix
            ),
            SymbolKind::Return => write!(
                f,
                "⟨cat#{}.rule#{}.return⟩",
                self.category_src_idx, self.rule_index_in_category
            ),
            SymbolKind::CollectionMarker => write!(
                f,
                "⟨cat#{}.rule#{}.coll⟩{}",
                self.category_src_idx, self.rule_index_in_category, bp_suffix
            ),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Reactive FSM types (M7: state-machine satisfies survey contract R17 + WPDS)
// ══════════════════════════════════════════════════════════════════════════════

/// The five canonical CEK parsing states from the survey (R17), extended with
/// the two WPDS-specific states (`AmbiguityFanout`, `Saturating`) needed for
/// branching parses. Plus the standard terminal states.
///
/// External consumers inspect this via [`WpdsWalker::state`] (Stage 4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WpdsState {
    /// Initial state at category entry; parser awaits its first event.
    Ready { min_bp: u8 },
    /// Matching on the current token to choose a prefix rule.
    PrefixDispatch { pos: usize, cur_bp: u8 },
    /// Looking for an infix/postfix operator with binding power > `cur_bp`.
    InfixLoop { cur_bp: u8 },
    /// Phase 4: mid-collection-literal. After parsing each element, the
    /// engine peeks the next token to decide between consuming a
    /// separator (parse another element) or consuming the close
    /// delimiter (finalize the collection).
    CollectionLoop {
        /// Result category index (where the constructed collection lives).
        result_src_idx: u16,
        /// Rule index within the result category (selects finalize action).
        rule_idx: u16,
        /// Element category index — what each element is parsed as.
        element_src_idx: u16,
        /// Outer Pratt cur_bp to restore on close-delimiter consumption.
        outer_bp: u8,
        /// Index into `SemanticBuilder.collection_stack` identifying this
        /// in-flight accumulator.
        accumulator_id: u8,
    },
    /// Phase 5: mid-binder-rule. The engine progresses through the rule's
    /// `syntax_pattern` items (literals, binder ident slot, body parse)
    /// using `StackSymbolV2::rule_at(.., position, ..)` on the GSS top to
    /// track which item we're at. After the body returns to Unwinding,
    /// the rule's action fires (constructing `Scope::new(Binder, body)`).
    BinderRule {
        /// Result category index (where the constructed term lives).
        result_src_idx: u16,
        /// Rule index within the result category (selects action).
        rule_idx: u16,
        /// Body category index — what the body is parsed as.
        body_src_idx: u16,
        /// Outer Pratt cur_bp to restore after the rule completes.
        outer_bp: u8,
    },
    /// Phase 5b: mid-binder-list-loop (`^[xs]`). Captures `Ident,
    /// separator, Ident, separator, ..., close` into the active binder
    /// scope, then transitions back to BinderRule at `next_pos`.
    BinderListLoop {
        result_src_idx: u16,
        rule_idx: u16,
        body_src_idx: u16,
        outer_bp: u8,
        /// Position of the BinderListLoop slot in the rule's positions list.
        marker_pos: u8,
        /// Position to advance to after the close delim is consumed.
        next_pos: u8,
    },
    /// Stage 1.1: cross-category projection delegation. After the WPDS
    /// engine has pushed a Return marker for a cross-cat rule (e.g.
    /// `ProcInt` from `Int → Proc`), this state pushes a CategoryEntry
    /// for the source category so the engine recursively parses the
    /// source. When the source's Return pops + its action fires (pushing
    /// a source-category Term to the builder), the cross-cat Return
    /// pops next + its wrap-action fires.
    CrossCatDelegate {
        /// Source category index — what we're about to parse.
        source_src_idx: u16,
        /// Outer Pratt cur_bp to restore after the delegation completes.
        outer_bp: u8,
    },
    /// Multiple GSS branches active simultaneously; awaiting resolution.
    AmbiguityFanout { branches: Vec<GssNodeId> },
    /// WPDS poststar/prestar saturation in progress; `delta_size` frontier size.
    Saturating { delta_size: usize },
    /// Popping continuation frames after a value was produced.
    Unwinding,
    /// Parse complete; result available via the walker's accept hook.
    Accepted,
    /// Parse failed; recovery may repair via the walker's recovery hook.
    Error { message: String },
}

impl WpdsState {
    /// Whether this state is terminal (Accepted or Error).
    pub fn is_terminal(&self) -> bool {
        matches!(self, WpdsState::Accepted | WpdsState::Error { .. })
    }
}

/// Events that drive the reactive FSM forward.
///
/// Generic over the weight type `W` so consumers can read resolved branch
/// weights. The `LexicographicWeight` of Stage 2 will be the canonical
/// instantiation; until then any [`Semiring`] suffices.
#[derive(Debug, Clone)]
pub enum WpdsEvent<W: Semiring> {
    /// Advance one transition. The default driver pulse.
    Step,
    /// A token was consumed at the given position.
    TokenConsumed { pos: usize, token: TokenKind },
    /// A GSS branch fork occurred; multiple stack tops now active.
    BranchForked {
        parent: GssNodeId,
        children: Vec<GssNodeId>,
    },
    /// Ambiguity resolved to a single winning branch with given weight.
    BranchResolved {
        winner: GssNodeId,
        weight: W,
    },
    /// A semantic action fired during AST assembly.
    /// `action_id` is the codegen-assigned identifier; `args` are token positions
    /// captured by the action.
    SemanticActionFired {
        action_id: u32,
        args: Vec<usize>,
    },
    /// Request the walker to record a checkpoint at the current configuration.
    Checkpoint { reason: CheckpointReason },
    /// Inspect the current state without mutating it.
    Inspect,
}

/// Reason a checkpoint is being recorded.
///
/// Used by `WpdsIncrementalSession` (Stage 5) to decide which checkpoints to
/// retain when memory pressure rises.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckpointReason {
    /// Periodic checkpoint at fixed interval (LSP token-level snapshots).
    PeriodicInterval,
    /// Natural boundary (end of category, top of stack empty).
    NaturalBoundary,
    /// Consumer requested via `WalkerConsumer::on_event` returning `Checkpoint`.
    ConsumerRequest,
    /// Pre-pause snapshot before halting (paired with `WpdsControl::Pause`).
    PrePause,
}

/// Output of one [`WpdsState`] × [`WpdsEvent`] transition.
#[derive(Debug, Clone)]
pub enum WpdsTransition<W: Semiring> {
    /// `Inspect` event; no state change.
    NoChange,
    /// State changed; optional trace entry recorded.
    Transition {
        new_state: WpdsState,
        trace: Option<WpdsTraceEntry>,
    },
    /// Checkpoint recorded at the current configuration.
    Checkpoint { config: WpdsConfiguration<W> },
    /// Parse complete; result is available via the walker.
    Done { state: WpdsState },
}

/// A WPDS configuration snapshot suitable for checkpointing or replay.
///
/// Generic over weight type `W`. Stage 5's `WpdsIncrementalSession` uses
/// `BTreeMap<usize, WpdsConfiguration<LexicographicWeight>>` for its
/// checkpoint cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WpdsConfiguration<W: Semiring> {
    /// Token position at the time of snapshot.
    pub pos: usize,
    /// State at the time of snapshot.
    pub state: WpdsState,
    /// Stack contents bottom-to-top.
    pub stack: Vec<StackSymbolV2>,
    /// Cumulative weight from start to this configuration.
    pub weight: W,
}

/// A debug trace entry for one transition.
///
/// Produced when [`WalkerConsumer::on_event`] (Stage 5) requests tracing or
/// when running under `cfg(debug_assertions)`. Otherwise transitions emit
/// `None` and incur no allocation.
#[derive(Debug, Clone)]
pub struct WpdsTraceEntry {
    /// Position when the transition fired.
    pub pos: usize,
    /// State before the transition.
    pub from_state: WpdsState,
    /// State after the transition.
    pub to_state: WpdsState,
    /// Stack depth after the transition.
    pub stack_depth: usize,
}

// ══════════════════════════════════════════════════════════════════════════════
// Control directives (M6: WpdsControl::Pause exists per Rholang §13.1)
// ══════════════════════════════════════════════════════════════════════════════

/// Control directive returned by a [`WalkerConsumer`] (Stage 5) after each
/// event. Determines whether the walker continues, snapshots, halts, or
/// awaits external resumption.
///
/// Mirrors `CekControl` from the surveyed `cek.rs` API and adds the `Pause`
/// variant promised by `docs/design/made/rholang-target/design.md` §13.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WpdsControl {
    /// Proceed to the next transition.
    Continue,
    /// Record a checkpoint, then continue.
    Checkpoint,
    /// Halt evaluation immediately. Walker enters `Error { message: "aborted" }`.
    Abort,
    /// Suspend the walker awaiting external resumption (DAP/REPL pause).
    /// The hosting green thread parks; wake-up via a `PauseResume` event
    /// (delivered by the controller).
    Pause,
}

// ══════════════════════════════════════════════════════════════════════════════
// Token source (Stage 6 Phase A.1 — engine-accessible read-only input window)
// ══════════════════════════════════════════════════════════════════════════════

/// Read-only window onto the token stream that the WPDS engine can peek
/// during `WpdsStepEngine::step`.
///
/// The walker holds a reference to a concrete impl during a parse session
/// (via `WpdsWalker::attach_token_source`). The engine's `step()` peeks
/// the next token to decide BP gating, cross-cat dispatch, etc.
pub trait WpdsTokenSource {
    /// Token at `pos`, or `None` if `pos >= len()`.
    fn peek_kind(&self, pos: usize) -> Option<TokenKind>;
    /// Text slice of the token at `pos`, if known.
    fn peek_text(&self, pos: usize) -> Option<&str>;
    /// Total token count.
    fn len(&self) -> usize;
    /// Convenience: whether `pos` is in range.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A slice-backed `WpdsTokenSource` for tests and simple batch consumers.
///
/// Holds a slice of `TokenKind` plus an optional parallel slice of text
/// strings. Production consumers may implement `WpdsTokenSource` directly
/// over their own richer token types.
pub struct SliceTokenSource<'a> {
    kinds: &'a [TokenKind],
    texts: Option<&'a [&'a str]>,
}

impl<'a> SliceTokenSource<'a> {
    pub fn new(kinds: &'a [TokenKind]) -> Self {
        SliceTokenSource { kinds, texts: None }
    }
    pub fn with_texts(kinds: &'a [TokenKind], texts: &'a [&'a str]) -> Self {
        assert_eq!(kinds.len(), texts.len(), "kinds/texts length mismatch");
        SliceTokenSource { kinds, texts: Some(texts) }
    }
}

impl<'a> WpdsTokenSource for SliceTokenSource<'a> {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        self.kinds.get(pos).cloned()
    }
    fn peek_text(&self, pos: usize) -> Option<&str> {
        self.texts.and_then(|t| t.get(pos).copied())
    }
    fn len(&self) -> usize {
        self.kinds.len()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Binder handle (Stage 6 Phase A.1 — alpha-rename substrate shared with runtime)
// ══════════════════════════════════════════════════════════════════════════════

/// A scope of binder names captured during parsing, ready to be consumed by
/// `mettail_runtime::Scope::new` at semantic-action time.
///
/// Walker-side representation holds the captured names + a depth counter.
/// The runtime-side `mettail_runtime::Binder`/`Scope` types actually perform
/// the alpha-renaming when the action body consumes this handle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinderHandle {
    /// Declaration-order binder names (e.g., `xs` in `new(a, b, c)`).
    pub names: Vec<String>,
    /// Nesting depth — incremented for nested binder scopes. Useful for
    /// debugging and for the runtime `Scope::new` call.
    pub depth: u16,
}

impl BinderHandle {
    pub fn new(names: Vec<String>, depth: u16) -> Self {
        BinderHandle { names, depth }
    }
    /// Single-binder convenience.
    pub fn single(name: String, depth: u16) -> Self {
        BinderHandle { names: vec![name], depth }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Semantic action machinery (Stage 6 Phase A.1 — action-id-indexed dispatch)
// ══════════════════════════════════════════════════════════════════════════════

/// Identifier for a semantic action, packed from `(src_idx, rule_idx)`.
///
/// Walker packs this when popping a `SymbolKind::Return` symbol; engine
/// looks up the corresponding `ActionEntry` via
/// [`WpdsStepEngine::action_for`].
pub type ActionId = u32;

/// Pack a category's source index and a rule's within-category index
/// into the canonical `ActionId`.
#[inline]
pub const fn pack_action_id(src_idx: u16, rule_idx: u16) -> ActionId {
    ((src_idx as u32) << 16) | (rule_idx as u32)
}

/// Unpack an `ActionId` back to `(src_idx, rule_idx)`.
#[inline]
pub const fn unpack_action_id(id: ActionId) -> (u16, u16) {
    (((id >> 16) & 0xFFFF) as u16, (id & 0xFFFF) as u16)
}

/// A captured parsing artifact passed to a semantic action.
///
/// Heterogeneous — actions downcast on demand. The walker pushes these
/// during the parse; actions pop a slice of N (matching the rule's
/// arity) and consume them.
pub enum ActionArg {
    /// A raw token kind + its text + position.
    Token { kind: TokenKind, text: String, pos: usize },
    /// An identifier captured from the token stream.
    Ident { name: String, pos: usize },
    /// A fully-constructed sub-term (downcast via `Any`).
    Term {
        value: Box<dyn Any + Send>,
        /// Static type-name tag for debug rendering and mismatch detection.
        type_name: &'static str,
    },
    /// A completed binder scope (ready for `Scope::new`).
    BinderScope(BinderHandle),
    /// A completed collection (List, Bag, Map — downcast via `Any`).
    Collection {
        value: Box<dyn Any + Send>,
        type_name: &'static str,
    },
    /// Phase 4: identifier of an in-flight collection accumulator. Pushed by
    /// the walker when a `CollectionMarker` symbol is pushed onto the GSS;
    /// consumed by the collection-finalize action via `as_collection_id`.
    CollectionId(u8),
    /// Phase 6: a parsed behavioral predicate. Pushed by the walker after
    /// invoking `parse_predicate_from_tokens`; consumed by the rule's action
    /// to wire the predicate into the constructed AST.
    Predicate(Box<dyn Any + Send>),
}

impl fmt::Debug for ActionArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ActionArg::Token { kind, text, pos } => f
                .debug_struct("Token")
                .field("kind", kind)
                .field("text", text)
                .field("pos", pos)
                .finish(),
            ActionArg::Ident { name, pos } => f
                .debug_struct("Ident")
                .field("name", name)
                .field("pos", pos)
                .finish(),
            ActionArg::Term { type_name, .. } => f
                .debug_struct("Term")
                .field("type_name", type_name)
                .finish(),
            ActionArg::BinderScope(h) => f.debug_tuple("BinderScope").field(h).finish(),
            ActionArg::Collection { type_name, .. } => f
                .debug_struct("Collection")
                .field("type_name", type_name)
                .finish(),
            ActionArg::CollectionId(id) => f.debug_tuple("CollectionId").field(id).finish(),
            ActionArg::Predicate(_) => f.debug_struct("Predicate").finish(),
        }
    }
}

impl ActionArg {
    /// Extract an `Ident` argument's name.
    pub fn as_ident(&self) -> Option<&str> {
        match self {
            ActionArg::Ident { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }
    /// Extract a `Token` argument's kind.
    pub fn as_token_kind(&self) -> Option<&TokenKind> {
        match self {
            ActionArg::Token { kind, .. } => Some(kind),
            _ => None,
        }
    }
    /// Extract a `Token` argument's text.
    pub fn as_token_text(&self) -> Option<&str> {
        match self {
            ActionArg::Token { text, .. } => Some(text.as_str()),
            _ => None,
        }
    }
    /// Consume this `Term` arg and downcast to `T`.
    pub fn into_term<T: 'static>(self) -> Option<T> {
        match self {
            ActionArg::Term { value, .. } => value.downcast::<T>().ok().map(|b| *b),
            _ => None,
        }
    }
    /// Borrow the BinderScope handle.
    pub fn as_binder_scope(&self) -> Option<&BinderHandle> {
        match self {
            ActionArg::BinderScope(h) => Some(h),
            _ => None,
        }
    }
    /// Consume this `Collection` arg and downcast to `T`.
    pub fn into_collection<T: 'static>(self) -> Option<T> {
        match self {
            ActionArg::Collection { value, .. } => value.downcast::<T>().ok().map(|b| *b),
            _ => None,
        }
    }
    /// Phase 4: extract a `CollectionId` argument's id.
    pub fn as_collection_id(&self) -> Option<u8> {
        match self {
            ActionArg::CollectionId(id) => Some(*id),
            _ => None,
        }
    }
    /// Phase 6: consume this `Predicate` arg and downcast to `T`.
    pub fn into_predicate<T: 'static>(self) -> Option<T> {
        match self {
            ActionArg::Predicate(value) => value.downcast::<T>().ok().map(|b| *b),
            _ => None,
        }
    }
}

/// Function pointer to a language-specific semantic action.
///
/// Called by the walker when a `SymbolKind::Return` symbol is popped.
/// The function consumes a captured-argument slice and pushes the
/// resulting term back onto the builder's stack.
pub type SemanticActionFn = fn(&mut SemanticBuilder, args: Vec<ActionArg>);

/// Lookup entry in the per-language action table.
///
/// Carries both the function pointer and the arity (how many top-of-stack
/// args the walker should pop to pass to the action).
#[derive(Clone, Copy)]
pub struct ActionEntry {
    pub action_fn: SemanticActionFn,
    pub arity: u8,
}

impl fmt::Debug for ActionEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActionEntry")
            .field("action_fn", &"fn(...)")
            .field("arity", &self.arity)
            .finish()
    }
}

/// Walker-owned accumulator for captured args and binder scopes.
///
/// Stack-based: pushes grow the top of the stack; pops shrink it. Semantic
/// actions consume args in push order (i.e., the FIRST arg to the action
/// was the FIRST one pushed — standard semantic-action left-to-right
/// convention).
///
/// At parse completion, the builder holds exactly one term on its stack —
/// the root AST node for the parse. `take_result::<T>()` downcasts and
/// returns it.
pub struct SemanticBuilder {
    stack: Vec<ActionArg>,
    binder_scopes: Vec<BinderHandle>,
    /// Phase 4: in-flight collection accumulators, indexed by id. Each
    /// entry collects `ActionArg::Term` values pushed during element
    /// parsing; the collection-finalize action drains the entry and
    /// constructs the final container (HashBag / Vec / etc.).
    collection_stack: Vec<Vec<ActionArg>>,
}

impl SemanticBuilder {
    pub fn new() -> Self {
        SemanticBuilder {
            stack: Vec::new(),
            binder_scopes: Vec::new(),
            collection_stack: Vec::new(),
        }
    }

    /// Current stack depth.
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Whether the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Push a raw token onto the stack.
    pub fn push_token(&mut self, kind: TokenKind, text: String, pos: usize) {
        self.stack.push(ActionArg::Token { kind, text, pos });
    }

    /// Push an identifier (Ident-token's text canonicalised).
    pub fn push_ident(&mut self, name: String, pos: usize) {
        self.stack.push(ActionArg::Ident { name, pos });
    }

    /// Push a constructed sub-term.
    pub fn push_term<T: 'static + Send>(&mut self, value: T) {
        self.stack.push(ActionArg::Term {
            value: Box::new(value),
            type_name: std::any::type_name::<T>(),
        });
    }

    /// Push a completed collection (already of the language's native
    /// collection type, e.g., `HashBag<Proc>` or `Vec<Int>`).
    pub fn push_collection<T: 'static + Send>(&mut self, value: T) {
        self.stack.push(ActionArg::Collection {
            value: Box::new(value),
            type_name: std::any::type_name::<T>(),
        });
    }

    /// Push a completed binder scope.
    pub fn push_binder_scope(&mut self, handle: BinderHandle) {
        self.stack.push(ActionArg::BinderScope(handle));
    }

    /// Phase 4: push a CollectionId arg onto the stack. Used by the walker
    /// when a `CollectionMarker` symbol is pushed onto the GSS so the
    /// finalize action can identify which accumulator to drain.
    pub fn push_collection_id(&mut self, id: u8) {
        self.stack.push(ActionArg::CollectionId(id));
    }

    /// Phase 6: push a parsed behavioral predicate onto the stack.
    pub fn push_predicate<T: 'static + Send>(&mut self, pred: T) {
        self.stack.push(ActionArg::Predicate(Box::new(pred)));
    }

    /// Pop the top N args (returned in push order: result[0] was
    /// pushed first). Panics if fewer than N args are available — a
    /// programming error in the engine's arity table.
    pub fn pop_args(&mut self, n: usize) -> Vec<ActionArg> {
        let start = self
            .stack
            .len()
            .checked_sub(n)
            .expect("SemanticBuilder::pop_args: stack underflow (engine arity bug)");
        self.stack.drain(start..).collect()
    }

    /// Begin a binder scope — used by binder rules before parsing the body.
    pub fn start_binder_scope(&mut self, names: Vec<String>) {
        let depth = self.binder_scopes.len() as u16;
        self.binder_scopes.push(BinderHandle::new(names, depth));
    }

    /// End the innermost binder scope and leave a `BinderScope` arg on the
    /// stack for the surrounding action to consume.
    pub fn end_binder_scope(&mut self) {
        if let Some(handle) = self.binder_scopes.pop() {
            self.stack.push(ActionArg::BinderScope(handle));
        }
    }

    /// Phase 5: end the innermost binder scope WITHOUT pushing a
    /// `BinderScope` arg back onto the stack. Used by binder-rule actions
    /// where the action body already has the binder name as a captured
    /// `Ident` arg and doesn't need a `BinderScope` slot.
    pub fn pop_binder_scope_silent(&mut self) {
        self.binder_scopes.pop();
    }

    /// View the innermost binder scope without popping it (for binder-aware
    /// inner parses that need to know which names are in scope).
    pub fn current_binder_scope(&self) -> Option<&BinderHandle> {
        self.binder_scopes.last()
    }

    /// At parse completion, extract the single remaining term as the
    /// parse result. Returns `None` if the stack is empty, has more than
    /// one entry, or the top entry is not a term of type `T`.
    pub fn take_result<T: 'static + Send>(&mut self) -> Option<T> {
        if self.stack.len() != 1 {
            return None;
        }
        match self.stack.pop()? {
            ActionArg::Term { value, .. } => value.downcast::<T>().ok().map(|b| *b),
            _ => None,
        }
    }

    // ─── Phase 4: collection-literal accumulator helpers ──────────────────

    /// Start a fresh collection accumulator. Returns the id (8-bit) to
    /// embed in the `CollectionMarker` symbol's `bp` field.
    pub fn start_collection(&mut self) -> u8 {
        let id = self.collection_stack.len() as u8;
        self.collection_stack.push(Vec::new());
        id
    }

    /// Pop the top of the argument stack (must be a `Term`) and append
    /// it into the collection identified by `id`. Called by the walker
    /// when transitioning to `CollectionLoop` after a per-element parse.
    pub fn push_to_collection(&mut self, id: u8) {
        if let Some(arg) = self.stack.pop() {
            if let Some(acc) = self.collection_stack.get_mut(id as usize) {
                acc.push(arg);
            }
        }
    }

    /// Drain the collection identified by `id`, returning its elements
    /// in push order. Called by the collection-finalize action.
    pub fn drain_collection(&mut self, id: u8) -> Vec<ActionArg> {
        if let Some(acc) = self.collection_stack.get_mut(id as usize) {
            std::mem::take(acc)
        } else {
            Vec::new()
        }
    }
}

impl Default for SemanticBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for SemanticBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SemanticBuilder")
            .field("stack_depth", &self.stack.len())
            .field("binder_scopes", &self.binder_scopes)
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;

    #[test]
    fn stack_symbol_v2_size_is_compact() {
        // Compact representation is load-bearing for hot-path use.
        // 8 bytes is the target; assert it does not regress unexpectedly.
        // (Actual size depends on enum layout; assert it stays small.)
        assert!(std::mem::size_of::<StackSymbolV2>() <= 8);
    }

    #[test]
    fn stack_symbol_v2_constructors_distinct() {
        let a = StackSymbolV2::category_entry(3);
        let b = StackSymbolV2::rule_at(3, 1, 0, Some(10));
        let c = StackSymbolV2::infix_continuation(3, 1, 10);
        let d = StackSymbolV2::return_symbol(3, 1);
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(c, d);
        assert_ne!(a, d);
    }

    #[test]
    fn stack_symbol_v2_display_includes_kind() {
        let entry = StackSymbolV2::category_entry(5);
        let mid = StackSymbolV2::rule_at(5, 2, 1, Some(20));
        let infix = StackSymbolV2::infix_continuation(5, 2, 20);
        let ret = StackSymbolV2::return_symbol(5, 2);
        assert_eq!(format!("{}", entry), "⟨cat#5⟩");
        assert_eq!(format!("{}", mid), "⟨cat#5.rule#2@1⟩@bp20");
        assert_eq!(format!("{}", infix), "⟨cat#5.rule#2.infix⟩@bp20");
        assert_eq!(format!("{}", ret), "⟨cat#5.rule#2.return⟩");
    }

    #[test]
    fn stack_symbol_v2_ordering_respects_category_first() {
        // Source-category order is the primary tiebreak: lower category index
        // sorts first regardless of rule index.
        let a = StackSymbolV2::rule_at(0, 99, 0, None);
        let b = StackSymbolV2::rule_at(1, 0, 0, None);
        assert!(a < b);
        // Within a category, lower rule index sorts first.
        let c = StackSymbolV2::rule_at(5, 0, 0, None);
        let d = StackSymbolV2::rule_at(5, 1, 0, None);
        assert!(c < d);
    }

    #[test]
    fn wpds_state_terminal_classification() {
        assert!(WpdsState::Accepted.is_terminal());
        assert!(WpdsState::Error { message: "x".into() }.is_terminal());
        assert!(!WpdsState::Ready { min_bp: 0 }.is_terminal());
        assert!(!WpdsState::Unwinding.is_terminal());
        assert!(!WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }.is_terminal());
    }

    #[test]
    fn wpds_event_constructible_with_tropical_weight() {
        let _step: WpdsEvent<TropicalWeight> = WpdsEvent::Step;
        let _tok: WpdsEvent<TropicalWeight> = WpdsEvent::TokenConsumed {
            pos: 0,
            token: TokenKind::Ident,
        };
        let _fork: WpdsEvent<TropicalWeight> = WpdsEvent::BranchForked {
            parent: 0,
            children: vec![1, 2],
        };
        let _resolved: WpdsEvent<TropicalWeight> = WpdsEvent::BranchResolved {
            winner: 1,
            weight: TropicalWeight::one(),
        };
        let _action: WpdsEvent<TropicalWeight> = WpdsEvent::SemanticActionFired {
            action_id: 7,
            args: vec![0, 1],
        };
        let _cp: WpdsEvent<TropicalWeight> = WpdsEvent::Checkpoint {
            reason: CheckpointReason::NaturalBoundary,
        };
        let _ins: WpdsEvent<TropicalWeight> = WpdsEvent::Inspect;
    }

    #[test]
    fn wpds_transition_variants_constructible() {
        let _no: WpdsTransition<TropicalWeight> = WpdsTransition::NoChange;
        let _t: WpdsTransition<TropicalWeight> = WpdsTransition::Transition {
            new_state: WpdsState::Accepted,
            trace: None,
        };
        let _cp: WpdsTransition<TropicalWeight> = WpdsTransition::Checkpoint {
            config: WpdsConfiguration {
                pos: 5,
                state: WpdsState::Ready { min_bp: 0 },
                stack: vec![StackSymbolV2::category_entry(0)],
                weight: TropicalWeight::one(),
            },
        };
        let _done: WpdsTransition<TropicalWeight> = WpdsTransition::Done {
            state: WpdsState::Accepted,
        };
    }

    #[test]
    fn wpds_control_pause_exists() {
        // M6: WpdsControl::Pause must exist for Rholang §13.1 compatibility.
        let _c = WpdsControl::Continue;
        let _h = WpdsControl::Checkpoint;
        let _a = WpdsControl::Abort;
        let _p = WpdsControl::Pause;
    }

    #[test]
    fn checkpoint_reasons_are_distinct() {
        let reasons = [
            CheckpointReason::PeriodicInterval,
            CheckpointReason::NaturalBoundary,
            CheckpointReason::ConsumerRequest,
            CheckpointReason::PrePause,
        ];
        for (i, a) in reasons.iter().enumerate() {
            for (j, b) in reasons.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }

    #[test]
    fn wpds_configuration_round_trip_clone_eq() {
        let cfg: WpdsConfiguration<TropicalWeight> = WpdsConfiguration {
            pos: 42,
            state: WpdsState::InfixLoop { cur_bp: 7 },
            stack: vec![
                StackSymbolV2::category_entry(0),
                StackSymbolV2::rule_at(0, 3, 1, Some(7)),
            ],
            weight: TropicalWeight::one(),
        };
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn wpds_state_ambiguity_fanout_holds_branches() {
        let s = WpdsState::AmbiguityFanout {
            branches: vec![10, 20, 30],
        };
        match s {
            WpdsState::AmbiguityFanout { branches } => {
                assert_eq!(branches, vec![10u32, 20u32, 30u32]);
            }
            _ => panic!("expected AmbiguityFanout"),
        }
    }

    #[test]
    fn symbol_kind_rule_at_carries_position() {
        let s = StackSymbolV2::rule_at(0, 0, 7, None);
        assert_eq!(s.kind, SymbolKind::RuleAt(7));
    }

    // ─── Stage 6 Phase A.1: infrastructure tests ────────────────────────────

    #[test]
    fn pack_and_unpack_action_id_round_trip() {
        for src in [0u16, 1, 7, 255, 1000, u16::MAX] {
            for rule in [0u16, 1, 99, 65535] {
                let id = pack_action_id(src, rule);
                let (s, r) = unpack_action_id(id);
                assert_eq!((s, r), (src, rule), "pack/unpack round-trip");
            }
        }
    }

    #[test]
    fn slice_token_source_peeks_kinds() {
        let tokens = [TokenKind::Ident, TokenKind::Integer, TokenKind::Eof];
        let src = SliceTokenSource::new(&tokens);
        assert_eq!(src.len(), 3);
        assert!(!src.is_empty());
        assert_eq!(src.peek_kind(0), Some(TokenKind::Ident));
        assert_eq!(src.peek_kind(1), Some(TokenKind::Integer));
        assert_eq!(src.peek_kind(3), None);
        assert_eq!(src.peek_text(0), None);
    }

    #[test]
    fn slice_token_source_with_texts_peeks_both() {
        let kinds = [TokenKind::Ident, TokenKind::Integer];
        let texts = ["foo", "42"];
        let src = SliceTokenSource::with_texts(&kinds, &texts);
        assert_eq!(src.peek_kind(0), Some(TokenKind::Ident));
        assert_eq!(src.peek_text(0), Some("foo"));
        assert_eq!(src.peek_kind(1), Some(TokenKind::Integer));
        assert_eq!(src.peek_text(1), Some("42"));
        assert_eq!(src.peek_text(2), None);
    }

    #[test]
    fn binder_handle_construction() {
        let h = BinderHandle::new(vec!["x".into(), "y".into(), "z".into()], 2);
        assert_eq!(h.names.len(), 3);
        assert_eq!(h.depth, 2);
        let s = BinderHandle::single("a".into(), 0);
        assert_eq!(s.names, vec!["a"]);
        assert_eq!(s.depth, 0);
    }

    #[test]
    fn semantic_builder_push_and_pop_terms() {
        let mut b = SemanticBuilder::new();
        assert!(b.is_empty());
        b.push_term::<i32>(7);
        b.push_term::<i32>(11);
        assert_eq!(b.len(), 2);
        let args = b.pop_args(2);
        assert_eq!(args.len(), 2);
        // Push order: result[0] was pushed first (7), result[1] was pushed second (11).
        let first = args.into_iter().next().unwrap();
        let val: i32 = first.into_term().expect("i32");
        assert_eq!(val, 7);
    }

    #[test]
    fn semantic_builder_push_ident_and_token() {
        let mut b = SemanticBuilder::new();
        b.push_ident("my_var".into(), 3);
        b.push_token(TokenKind::Integer, "42".into(), 4);
        let args = b.pop_args(2);
        assert_eq!(args[0].as_ident(), Some("my_var"));
        assert_eq!(args[1].as_token_kind(), Some(&TokenKind::Integer));
        assert_eq!(args[1].as_token_text(), Some("42"));
    }

    #[test]
    fn semantic_builder_binder_scope_push_pop() {
        let mut b = SemanticBuilder::new();
        b.start_binder_scope(vec!["a".into(), "b".into()]);
        assert_eq!(b.current_binder_scope().unwrap().names, vec!["a", "b"]);
        assert_eq!(b.current_binder_scope().unwrap().depth, 0);
        // Nest:
        b.start_binder_scope(vec!["c".into()]);
        assert_eq!(b.current_binder_scope().unwrap().depth, 1);
        b.end_binder_scope();
        // After end, the scope is on the argument stack.
        assert_eq!(b.len(), 1);
        let args = b.pop_args(1);
        assert_eq!(args[0].as_binder_scope().unwrap().names, vec!["c"]);
    }

    #[test]
    fn semantic_builder_take_result_single_term() {
        let mut b = SemanticBuilder::new();
        b.push_term::<String>("parsed".into());
        let result: String = b.take_result().expect("String");
        assert_eq!(result, "parsed");
    }

    #[test]
    fn semantic_builder_take_result_rejects_empty() {
        let mut b = SemanticBuilder::new();
        let r: Option<i32> = b.take_result();
        assert!(r.is_none());
    }

    #[test]
    fn semantic_builder_take_result_rejects_multiple() {
        let mut b = SemanticBuilder::new();
        b.push_term::<i32>(1);
        b.push_term::<i32>(2);
        let r: Option<i32> = b.take_result();
        assert!(r.is_none(), "take_result requires exactly one entry");
    }

    #[test]
    fn semantic_builder_take_result_rejects_type_mismatch() {
        let mut b = SemanticBuilder::new();
        b.push_term::<String>("x".into());
        let r: Option<i32> = b.take_result();
        assert!(r.is_none(), "type mismatch yields None");
    }

    #[test]
    fn action_arg_debug_is_type_safe() {
        // Ensures Debug doesn't try to print the Box<dyn Any> internals.
        let a = ActionArg::Term {
            value: Box::new(42i32),
            type_name: "i32",
        };
        let s = format!("{:?}", a);
        assert!(s.contains("Term"));
        assert!(s.contains("i32"));
    }

    #[test]
    fn action_entry_debug_hides_fn_body() {
        fn my_action(_b: &mut SemanticBuilder, _a: Vec<ActionArg>) {}
        let e = ActionEntry { action_fn: my_action, arity: 3 };
        let s = format!("{:?}", e);
        assert!(s.contains("arity: 3"));
    }

    #[test]
    fn action_entry_is_copy() {
        fn my_action(_b: &mut SemanticBuilder, _a: Vec<ActionArg>) {}
        let e = ActionEntry { action_fn: my_action, arity: 2 };
        let e2 = e; // Copy
        let _e3 = e; // Copy again — would fail if not Copy
        assert_eq!(e.arity, e2.arity);
    }

    #[test]
    fn semantic_builder_collection_push_pop() {
        let mut b = SemanticBuilder::new();
        let v: Vec<i32> = vec![1, 2, 3];
        b.push_collection(v);
        let args = b.pop_args(1);
        let collected: Vec<i32> = args.into_iter().next().unwrap().into_collection().expect("Vec<i32>");
        assert_eq!(collected, vec![1, 2, 3]);
    }
}
