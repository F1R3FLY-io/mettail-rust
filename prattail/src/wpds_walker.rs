//! WPDS walker: reactive FSM driving the runtime parser.
//!
//! Stage 4 of W7 plan v5.1. Implements [`WpdsWalker`], the pure
//! `State × Event → Transition` driver per the survey contract M1
//! (`prattail/docs/design/wpds-migration-survey.md` §4).
//!
//! ## Architecture
//!
//! ```text
//!   External consumer
//!         │
//!         │ WpdsEvent
//!         ▼
//!   ┌─────────────────────────────┐
//!   │ WpdsWalker<W, E>            │
//!   │   state: WpdsState          │  ← inspectable
//!   │   gss:   WpdsGss<W>         │  ← branching substrate (Stage 3)
//!   │   pos:   usize              │  ← input cursor
//!   │   weight: W                 │  ← cumulative path weight
//!   │   engine: E (StepEngine)    │  ← provides per-language rule logic
//!   └─────────────────────────────┘
//!         │
//!         │ WpdsTransition
//!         ▼
//!   External consumer (acts on transition / records trace)
//! ```
//!
//! The walker is **pure** in the sense that `process_event` produces a
//! `WpdsTransition` describing what changed; it does not perform I/O,
//! call observers (those are Stage 5's `WalkerConsumer`), or otherwise
//! interact with the world. External consumers drive the loop.
//!
//! ## Step engine separation
//!
//! Per-language rule logic lives behind the [`WpdsStepEngine`] trait. The
//! walker calls into the engine once per `Step` event to ask "given the
//! current state and stack, what should I do next?" Stage 6's codegen
//! emits a concrete `WpdsStepEngine` per language. Tests use [`MockEngine`].
//!
//! ## Beam pruning
//!
//! Optional via [`WpdsWalker::with_beam_size`]. When set, after each
//! transition the walker prunes the GSS frontier to the K best branches
//! by weight (lex-min on [`crate::automata::lex_weight::LexicographicWeight`]).
//! Off by default — preserves correctness at the cost of memory.
//!
//! ## Saturation step semantics
//!
//! Per WPDS poststar semantics, a single `Step` event may trigger a chain
//! of derived transitions (push followed by automatic intra-cat advances).
//! [`WpdsWalker::run_to_saturation`] drives `Step` events until the
//! engine returns [`WpdsStepAction::Idle`] (nothing more to derive).

use std::any::Any;
use std::sync::Arc;

use crate::automata::semiring::Semiring;
use crate::automata::TokenKind;
use crate::gss::{WpdsGss, WpdsGssNode};
use crate::wpds_runtime::{
    pack_action_id, ActionArg, ActionEntry, CheckpointReason, SemanticBuilder, StackSymbolV2,
    SymbolKind, WpdsConfiguration, WpdsControl, WpdsEvent, WpdsState, WpdsTokenSource,
    WpdsTraceEntry, WpdsTransition,
};

// ══════════════════════════════════════════════════════════════════════════════
// Step engine interface
// ══════════════════════════════════════════════════════════════════════════════

/// Per-language rule logic queried by the walker on each `Step` event.
///
/// Stage 6's codegen emits a concrete `WpdsStepEngine` per `language!`
/// declaration. Tests in this module use [`ScriptedEngine`].
///
/// Phase A.1 extension: `step` gains a `tokens: &dyn WpdsTokenSource`
/// parameter so it can peek the input. `action_for` is the per-language
/// semantic-action lookup — default empty so engines that don't need
/// semantic actions (e.g., `IdleEngine` for tests) don't have to supply one.
pub trait WpdsStepEngine<W: Semiring> {
    /// Decide the next action given the current state, configuration,
    /// and input.
    fn step(
        &self,
        state: &WpdsState,
        gss: &WpdsGss<W>,
        frontier_top: Option<&WpdsGssNode>,
        pos: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsStepAction<W>;

    /// Look up the semantic action attached to a `(src_idx, rule_idx)` pair.
    ///
    /// The walker calls this when popping a [`SymbolKind::Return`] symbol
    /// to dispatch the rule's AST-construction logic. Returning `None` is
    /// permitted: no action fires, but the pop still happens (useful for
    /// structural rules that don't produce AST nodes).
    fn action_for(&self, src_idx: u16, rule_idx: u16) -> Option<&ActionEntry> {
        let _ = (src_idx, rule_idx);
        None
    }
}

/// One step of action returned by a [`WpdsStepEngine`].
///
/// Operations are exhaustive: walker selects exactly one per `Step`.
#[derive(Debug, Clone)]
pub enum WpdsStepAction<W: Semiring> {
    /// Move the FSM into a new state without touching the GSS.
    Advance(WpdsState),
    /// WPDS push: emit a new symbol on top of the frontier, link to current top.
    Push {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// WPDS pop: drop the frontier top, follow the predecessor edge.
    Pop {
        weight: W,
        new_state: WpdsState,
    },
    /// WPDS replace: swap the top symbol for another (intracategory step).
    Replace {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// Fork into multiple branches; each becomes an independent frontier
    /// with its own per-branch target state. The walker constructs one
    /// [`BranchCursor`] per branch and transitions to `WpdsState::AmbiguityFanout`;
    /// `step_fanout` then drives each cursor independently until lex-min
    /// selects the surviving branch.
    ///
    /// Per-branch `new_state` (vs a shared one) lets codegen route each
    /// rule in a multi-rule group to its own target state — e.g., a binder
    /// multi-rule group emits one branch per rule with a distinct
    /// `BinderRule { rule_idx, body_src_idx }`; cross-cat projection
    /// emits one branch per source category with a distinct
    /// `CrossCatDelegate { source_src_idx }`.
    ///
    /// `consume_trigger` advances the walker's `pos` by 1 before allocating
    /// cursors — used when the trigger token (e.g., a binder's `bool(`)
    /// must be consumed atomically with the fork. Mirrors `ConsumeAndPush`'s
    /// pos-advance for the multi-rule case. Cursors inherit the post-advance
    /// pos. Set `false` for cross-cat projection where the source FIRST
    /// token is consumed by the source category's own parse, not by the
    /// fork itself (mirrors `Push`, not `ConsumeAndPush`).
    Fork {
        branches: Vec<ForkBranch<W>>,
        consume_trigger: bool,
    },
    /// Phase A.2 atomic-rule shortcut: optionally capture the current
    /// token into the builder as `ActionArg::Token`, advance `pos` by 1,
    /// push `symbol` onto the stack (typically `kind=Return`), and
    /// transition to `new_state`. Walker handles all four effects
    /// atomically.
    ///
    /// `capture_token` controls whether the consumed token is pushed to
    /// the builder. Atomic-literal prefix arms set this `true` so the
    /// follow-up `Pop(Return)` action sees the token as `ActionArg::Token`.
    /// Infix-operator arms (Phase 3) set this `false` because the
    /// operator token shouldn't appear on the builder stack — only the
    /// LHS/RHS terms (which were already pushed by their own actions).
    ConsumeAndPush {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
        capture_token: bool,
    },
    /// Phase 4: consume the current token (advance `pos` by 1), pop the
    /// stack top (firing the action attached to it if it's a `Return` or
    /// `CollectionMarker`), and transition to `new_state`. Used by the
    /// `CollectionLoop` close arm: consume the close delimiter, pop the
    /// `CollectionMarker`, and fire the finalize action.
    ConsumeAndPop {
        weight: W,
        new_state: WpdsState,
    },
    /// Phase 4: consume the current token (advance `pos` by 1) without
    /// touching the stack, then transition to `new_state`. Used by the
    /// `CollectionLoop` separator arm: consume the separator and re-enter
    /// `PrefixDispatch` to parse the next element.
    Consume {
        weight: W,
        new_state: WpdsState,
    },
    /// Phase 5: consume the current `Ident` token (advance `pos` by 1),
    /// push it as `ActionArg::Ident` to the builder, and replace the GSS
    /// top with `symbol`. If `start_scope` is true, also call
    /// `builder.start_binder_scope(vec![name])` so binder-aware inner
    /// parses see the bound name. Used by the binder-rule state machine
    /// to capture the binder ident slot.
    ConsumeIdentAndReplace {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
        start_scope: bool,
    },
    /// Phase 5: consume the current token (advance `pos` by 1) and
    /// replace the GSS top with `symbol`, then transition to `new_state`.
    /// Used by the binder-rule state machine to advance through literal
    /// terminals in the rule's syntax_pattern (e.g., `"." | "lam"`) while
    /// updating the marker's `position` field.
    ConsumeAndReplace {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// Phase 5b: replace the GSS top with `replace_symbol`, then push
    /// `push_symbol` on top. Used by `ParamParse` slot dispatch to
    /// (1) advance the marker's position before the sub-parse begins, so
    /// when the sub-parse returns Unwinding-RuleAt sees the post-param
    /// position; and (2) push `CategoryEntry(param_cat)` on top to
    /// initiate the sub-parse.
    ReplaceAndPush {
        replace_symbol: StackSymbolV2,
        push_symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// Phase 6: parse a predicate inline via
    /// `mettail_runtime::parser::predicate::parse_predicate_from_tokens`.
    /// Walker invokes the parser, advances `pos` past the predicate,
    /// pushes `ActionArg::Predicate(BehavioralPred)` to builder, replaces
    /// the GSS top with `replace_symbol`, transitions to `new_state`.
    ParsePredicate {
        replace_symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// Parse complete.
    Accept,
    /// Parse failed; message is propagated as `WpdsState::Error { message }`.
    Error(String),
    /// Engine has no opinion at this state. Walker emits `NoChange`.
    Idle,
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdsWalker
// ══════════════════════════════════════════════════════════════════════════════

/// Pure reactive FSM driving WPDS-based parsing.
///
/// External consumers (LSP/DAP/REPL/nREPL) drive [`WpdsWalker::process_event`]
/// at their own pace. The walker tracks state, GSS, cursor position, and
/// cumulative weight; it consults the [`WpdsStepEngine`] for per-language
/// decisions.
pub struct WpdsWalker<W: Semiring, E: WpdsStepEngine<W>> {
    state: WpdsState,
    gss: WpdsGss<W>,
    pos: usize,
    weight: W,
    engine: E,
    /// Most recently pushed GSS node id (the conceptual top).
    top_node: Option<crate::gss::GssNodeId>,
    /// Optional beam pruning bound.
    beam_size: Option<usize>,
    /// Phase A.1: walker-owned accumulator for captured parse artifacts
    /// (tokens, identifiers, sub-terms). Semantic actions consume from
    /// and push back to this builder.
    builder: SemanticBuilder,
    /// Stage 7+ Fork plan, step 2: per-branch micro-state during
    /// `WpdsState::AmbiguityFanout`. Each entry is a `BranchCursor` that
    /// pairs a GSS-tip node id with the branch's own `pos`, accumulated
    /// `weight`, and `inner_state` (the post-Fork target state for that
    /// branch). Empty when the walker is NOT in `AmbiguityFanout`. The
    /// i-th entry here corresponds to the i-th `branches` GssNodeId in
    /// `WpdsState::AmbiguityFanout { branches }`.
    branch_cursors: Vec<BranchCursor<W>>,
}

/// One branch of a [`WpdsStepAction::Fork`] action. Codegen emits a
/// `Vec<ForkBranch<W>>` when a parser-side ambiguity needs WPDS-driven
/// disambiguation (binder multi-rule, cross-cat projection sharing a
/// FIRST token, etc.). Each branch carries everything the walker needs
/// to allocate an independent GSS node and `BranchCursor`:
///
/// - `symbol` — the stack symbol pushed onto this branch's GSS frontier
///   (typically `RuleAt(result_src, rule_idx, …)` for binder fork or
///   `RuleAt(category_src, rule_idx, …).with_kind_return()` for cross-cat).
/// - `weight` — initial branch weight; lex-min over `(primary, src_idx, rule_idx)`
///   selects the surviving branch when the fanout collapses. Default
///   weighting strategy: `LexicographicWeight::from_cost(0.0, src, rule_idx)`
///   gives each branch a unique tiebreak by source-order rule_idx.
/// - `new_state` — the per-branch target state (e.g.,
///   `BinderRule { rule_idx, body_src_idx, … }`). Distinct across branches —
///   this is why `Fork` needs `Vec<ForkBranch>` rather than a shared `new_state`.
#[derive(Clone)]
pub struct ForkBranch<W: Semiring> {
    pub symbol: StackSymbolV2,
    pub weight: W,
    pub new_state: WpdsState,
}

impl<W: Semiring> std::fmt::Debug for ForkBranch<W>
where
    W: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ForkBranch")
            .field("symbol", &self.symbol)
            .field("weight", &self.weight)
            .field("new_state", &self.new_state)
            .finish()
    }
}

/// Stage 7+ Fork plan, step 2: per-branch micro-state during
/// `WpdsState::AmbiguityFanout`. Stored on `WpdsWalker::branch_cursors`
/// parallel to the `Vec<GssNodeId>` in the state itself. Each cursor
/// carries the branch's GSS tip, current input position, accumulated
/// weight, the per-branch target state, and a pending-builder-op log.
///
/// Step 3 (Fork plan F4): `pending_builder_ops` queues
/// [`BuilderDelta`]s representing walker-driven mutations to the live
/// `SemanticBuilder` that must be deferred until a winning branch is
/// chosen. Each cursor's deltas are replayed during `commit_winner`.
pub struct BranchCursor<W: Semiring> {
    /// GSS-tip node id for this branch (matches the corresponding entry
    /// in `WpdsState::AmbiguityFanout { branches }`).
    pub node: crate::gss::GssNodeId,
    /// Per-branch input position. Branches may diverge in `pos` because
    /// their first action (e.g., the Fork's `new_state` PrefixDispatch
    /// over different rule_idx) commits different tokens.
    pub pos: usize,
    /// Per-branch accumulated weight. Lex-min ordering across cursors
    /// selects the surviving branch when the fanout collapses.
    pub weight: W,
    /// The per-branch target state. The Fork action's `new_state` field
    /// becomes each branch's initial `inner_state`; subsequent
    /// `step_fanout` calls dispatch on this state and overwrite it with
    /// the branch's post-step state.
    pub inner_state: WpdsState,
    /// Step 3 (Fork plan F4): deferred builder mutations. The walker logs
    /// per-cursor builder ops here during `apply_action_to_cursor` instead
    /// of mutating the live `SemanticBuilder`. On `commit_winner` the
    /// surviving branch's deltas are replayed against the live builder in
    /// insertion order.
    pub pending_builder_ops: Vec<BuilderDelta>,
    /// Option A (2026-04-28): cursor-local mirror of
    /// `SemanticBuilder.collection_stack`. Each `ConsumeAndPush(CollectionMarker)`
    /// or `Push(CollectionMarker)` allocates an id by appending an empty
    /// `Vec<ActionArg>` here. `MaybeSpliceCollection` deltas (logged
    /// during element pops) splice values into the corresponding slot at
    /// commit time. On `commit_winner`, the cursor's accumulators are
    /// donated en bloc to the live builder via
    /// `SemanticBuilder::adopt_collection_stack` BEFORE delta replay so
    /// that downstream `MaybeSpliceCollection` and `FireAction` deltas
    /// find populated slots.
    pub collection_stack: Vec<Vec<ActionArg>>,
}

impl<W: Semiring> std::fmt::Debug for BranchCursor<W>
where
    W: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BranchCursor")
            .field("node", &self.node)
            .field("pos", &self.pos)
            .field("weight", &self.weight)
            .field("inner_state", &self.inner_state)
            .field("pending_builder_ops_len", &self.pending_builder_ops.len())
            .finish()
    }
}

impl<W: Semiring + Clone> Clone for BranchCursor<W> {
    fn clone(&self) -> Self {
        // Cleanup 4 (Option A refinement, 2026-04-28): `BuilderDelta::PushPredicate`
        // now holds `Arc<dyn Any + Send + Sync>` so the entire BuilderDelta
        // enum derives Clone. The pre-cleanup `clone_non_predicate` helper
        // (which panicked on PushPredicate) is gone; cloning is total over
        // pending_builder_ops.
        //
        // The collection_stack restriction stays for now: `ActionArg::Term`
        // contains `Box<dyn Any + Send>` (non-Clone) for parsed Term values.
        // Cloning a cursor with populated accumulators would silently drop
        // those Terms. No shipped codegen path triggers nested Fork mid-
        // collection-parse today; if a future grammar does, the principled
        // fix is to wrap Term values in `Arc<dyn Any + Send + Sync>` like
        // PushPredicate did here.
        debug_assert!(
            self.collection_stack.iter().all(|acc| acc.is_empty()),
            "BranchCursor::clone called while collection_stack has \
             populated accumulators — Term values inside ActionArg are \
             non-clonable and would be silently lost. Refactor the call \
             site to commit or drain first, or wrap Term values in \
             Arc<dyn Any + Send + Sync> mirroring the Cleanup-4 PushPredicate fix."
        );
        BranchCursor {
            node: self.node,
            pos: self.pos,
            weight: self.weight.clone(),
            inner_state: self.inner_state.clone(),
            pending_builder_ops: self.pending_builder_ops.clone(),
            // Empty per assertion above; clone produces an empty mirror.
            collection_stack: self
                .collection_stack
                .iter()
                .map(|_| Vec::new())
                .collect(),
        }
    }
}

/// Step 3 (Fork plan F4): deferred mutation of the live
/// `SemanticBuilder` performed during a Fork branch's evaluation.
///
/// During `WpdsState::AmbiguityFanout`, the walker cannot apply walker-
/// driven builder side-effects (token captures, ident captures, predicate
/// pushes, binder-scope opens, action firings) directly to the live
/// builder — doing so would corrupt the builder state for losing
/// branches. Instead, each cursor logs deltas into its own
/// `pending_builder_ops` queue. When the winning branch is chosen via
/// lex-min, `commit_winner` replays its deltas against the live builder.
///
/// The six variants cover every walker-driven builder mutation:
///
/// 1. `PushToken` — captured token text from `ConsumeAndPush { capture_token: true }`.
/// 2. `PushIdent` — captured ident from `ConsumeIdentAndReplace`.
/// 3. `PushPredicate` — type-erased predicate from `ParsePredicate`. Boxed
///    because `SemanticBuilder::push_predicate<T>` is generic; the predicate's
///    concrete type (typically `BehavioralPred`) is recovered downstream
///    via `ActionArg::into_predicate::<T>()`'s `Any::downcast`.
/// 4. `StartBinderScope` — binder-scope open from `ConsumeIdentAndReplace { start_scope: true }`.
/// 5. `FireAction` — defer firing the rule's semantic action when the
///    cursor's `Pop` / `ConsumeAndPop` would normally invoke it. The
///    action mutates the live builder stack (consumes args, pushes a
///    Term), which depends on builder state at commit time, not log time.
/// 6. `MaybeSpliceCollection` — defer post-pop splice into the enclosing
///    `CollectionMarker`'s accumulator (`maybe_splice_into_enclosing_collection`).
#[derive(Clone)]
pub enum BuilderDelta {
    PushToken {
        kind: TokenKind,
        text: String,
        pos: usize,
    },
    PushIdent {
        name: String,
        pos: usize,
    },
    PushPredicate(Arc<dyn Any + Send + Sync>),
    StartBinderScope {
        names: Vec<String>,
    },
    FireAction {
        symbol: StackSymbolV2,
    },
    /// Option A (2026-04-28): a cursor opened a collection. The id was
    /// allocated from the cursor's local `collection_stack` mirror; on
    /// commit, replay pushes the corresponding `CollectionId(id)` arg
    /// onto the live builder stack (the cursor's accumulators were
    /// donated en bloc via `adopt_collection_stack` BEFORE delta replay).
    PushCollectionId {
        id: u8,
    },
    /// Cleanup 1 (Option A refinement, 2026-04-28): a cursor popped a
    /// frame whose new GSS top is a `CollectionMarker`. Splice the
    /// just-built top of the builder stack (the constructed element or
    /// nested container) into the enclosing accumulator identified by
    /// `id`. The id is captured at log time directly from the
    /// predecessor's `symbol.bp`, so replay is pure:
    /// `builder.push_to_collection(id)` — no GSS walk, no walker-state
    /// mutation. Replaces the prior `MaybeSpliceCollection { gss_top_at_log }`
    /// design which threaded a GSS node id through the delta and required
    /// `commit_winner` to mutate `top_node` mid-replay. The new design
    /// only emits this delta when the popped frame's predecessor IS a
    /// CollectionMarker — when there's no enclosing collection, no delta
    /// is logged at all (the old code logged unconditionally and let the
    /// helper no-op).
    SpliceIntoCollection { id: u8 },
}

impl std::fmt::Debug for BuilderDelta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuilderDelta::PushToken { kind, text, pos } => f
                .debug_struct("PushToken")
                .field("kind", kind)
                .field("text", text)
                .field("pos", pos)
                .finish(),
            BuilderDelta::PushIdent { name, pos } => f
                .debug_struct("PushIdent")
                .field("name", name)
                .field("pos", pos)
                .finish(),
            BuilderDelta::PushPredicate(_) => f.debug_struct("PushPredicate").finish(),
            BuilderDelta::StartBinderScope { names } => f
                .debug_struct("StartBinderScope")
                .field("names", names)
                .finish(),
            BuilderDelta::FireAction { symbol } => f
                .debug_struct("FireAction")
                .field("symbol", symbol)
                .finish(),
            BuilderDelta::PushCollectionId { id } => f
                .debug_struct("PushCollectionId")
                .field("id", id)
                .finish(),
            BuilderDelta::SpliceIntoCollection { id } => f
                .debug_struct("SpliceIntoCollection")
                .field("id", id)
                .finish(),
        }
    }
}

/// Step 3 (Fork plan F5): outcome of `apply_action_to_cursor`. Drives
/// `step_fanout`'s four-case classification.
///
/// - `Drop` — branch encountered an `Error` action or `Idle` with no
///   GSS predecessor, etc. Discard from `branch_cursors`.
/// - `Alive` — cursor took one step; `pos`/`weight`/`inner_state` mutated
///   in place. Continue iterating.
/// - `ForkInto(children)` — cursor encountered a nested `Fork` action;
///   replace this cursor with N children (typically not emitted by
///   shipped codegen; reserved for completeness).
/// - `Resolved` — cursor reached a "branch-done" state (either
///   `Accepted`, an outer-loop state like `InfixLoop`, or `Pop`'ed past
///   top-of-stack). Candidate winner; final `pos`/`weight` are decisive.
pub enum CursorOutcome<W: Semiring> {
    Drop,
    Alive,
    ForkInto(Vec<BranchCursor<W>>),
    Resolved,
}

impl<W: Semiring> std::fmt::Debug for CursorOutcome<W>
where
    W: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CursorOutcome::Drop => write!(f, "Drop"),
            CursorOutcome::Alive => write!(f, "Alive"),
            CursorOutcome::ForkInto(v) => f
                .debug_tuple("ForkInto")
                .field(&format_args!("{} cursor(s)", v.len()))
                .finish(),
            CursorOutcome::Resolved => write!(f, "Resolved"),
        }
    }
}

impl<W: Semiring, E: WpdsStepEngine<W>> WpdsWalker<W, E> {
    /// Construct a fresh walker in `Ready { min_bp }` state.
    pub fn new(engine: E, initial_min_bp: u8) -> Self {
        WpdsWalker {
            state: WpdsState::Ready { min_bp: initial_min_bp },
            gss: WpdsGss::new(),
            pos: 0,
            weight: W::one(),
            engine,
            top_node: None,
            beam_size: None,
            builder: SemanticBuilder::new(),
            branch_cursors: Vec::new(),
        }
    }

    /// Construct a walker seeded to parse starting at the specified
    /// category. Pushes a `CategoryEntry(cat_src_idx)` symbol onto the GSS
    /// and transitions directly into `PrefixDispatch { pos: 0, cur_bp:
    /// min_bp }` — bypassing the default `Ready → Push(primary) →
    /// PrefixDispatch` path that the no-category `new` constructor takes.
    ///
    /// Used by `parse_<Cat>_via_wpds` facades to start parsing at any
    /// category (not just the primary).
    pub fn new_for_category(engine: E, cat_src_idx: u16, initial_min_bp: u8) -> Self {
        let mut gss: WpdsGss<W> = WpdsGss::new();
        // Push the target category as the sole frame. Phase 5 fix: do NOT
        // create a separate "bottom" node first — `get_or_create_node`
        // deduplicates on `(pos, symbol)`, so a `bottom` of `(0, CE(0))` and
        // a `top` of `(0, CE(cat_src_idx))` collapse to the same id when
        // `cat_src_idx == 0`, yielding a self-loop. Instead, the top frame
        // has no predecessor — the walker treats `top_node = None` after
        // pop as the terminal-Accept signal.
        let top_id = gss.get_or_create_node(WpdsGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(cat_src_idx),
        });
        WpdsWalker {
            state: WpdsState::PrefixDispatch {
                pos: 0,
                cur_bp: initial_min_bp,
            },
            gss,
            pos: 0,
            weight: W::one(),
            engine,
            top_node: Some(top_id),
            beam_size: None,
            builder: SemanticBuilder::new(),
            branch_cursors: Vec::new(),
        }
    }

    /// Construct a walker pre-seeded from a saved [`WpdsConfiguration`].
    ///
    /// Used by [`crate::wpds_session::WpdsIncrementalSession::reparse`] to
    /// resume execution from a checkpoint. Reconstructs the GSS as a linear
    /// chain matching the saved stack (bottom-to-top).
    pub fn seeded_from(engine: E, config: WpdsConfiguration<W>) -> Self {
        let mut gss: WpdsGss<W> = WpdsGss::new();
        let mut top_node: Option<crate::gss::GssNodeId> = None;
        // Stack is stored bottom-to-top; rebuild GSS in that order with
        // each new symbol pushing onto the previous top.
        for symbol in config.stack.iter() {
            let new_id = match top_node {
                None => gss.get_or_create_node(WpdsGssNode {
                    pos: config.pos,
                    symbol: *symbol,
                }),
                Some(prev) => gss.push_symbol(prev, *symbol, config.pos, W::one()),
            };
            top_node = Some(new_id);
        }
        WpdsWalker {
            state: config.state,
            gss,
            pos: config.pos,
            weight: config.weight,
            engine,
            top_node,
            beam_size: None,
            builder: SemanticBuilder::new(),
            branch_cursors: Vec::new(),
        }
    }

    /// Enable beam pruning to at most `k` branches per frontier (builder style).
    pub fn with_beam_size(mut self, k: usize) -> Self {
        self.beam_size = Some(k);
        self
    }

    /// Read-only access to the current state.
    pub fn state(&self) -> &WpdsState {
        &self.state
    }

    /// Current input position.
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Cumulative weight from start to current configuration.
    /// Test-only accessor for `branch_cursors`. Used by the `fork_*` tests
    /// to verify per-branch state propagation.
    #[cfg(test)]
    pub fn branch_cursors_for_test(&self) -> &[BranchCursor<W>] {
        &self.branch_cursors
    }

    pub fn weight(&self) -> &W {
        &self.weight
    }

    /// Read-only access to the GSS.
    pub fn gss(&self) -> &WpdsGss<W> {
        &self.gss
    }

    /// Read-only access to the walker's semantic builder (captured args,
    /// binder scopes, in-progress AST construction).
    pub fn builder(&self) -> &SemanticBuilder {
        &self.builder
    }

    /// Mutable access to the semantic builder. External consumers (or the
    /// codegen-emitted wrapper) use this to seed pre-parse values or to
    /// extract the final parse result via `take_result`.
    pub fn builder_mut(&mut self) -> &mut SemanticBuilder {
        &mut self.builder
    }

    /// Optional beam pruning bound (None = unlimited).
    pub fn beam_size(&self) -> Option<usize> {
        self.beam_size
    }

    /// Snapshot the current configuration for checkpointing.
    pub fn current_configuration(&self) -> WpdsConfiguration<W> {
        // Reconstruct stack from GSS top by walking predecessors.
        let mut stack = Vec::new();
        let mut cursor = self.top_node;
        while let Some(id) = cursor {
            if let Some(node) = self.gss.node(id) {
                stack.push(node.symbol);
            }
            cursor = self.gss.edges_from(id).first().map(|e| e.target);
        }
        // Stack was built top-to-bottom; reverse for bottom-to-top convention.
        stack.reverse();
        WpdsConfiguration {
            pos: self.pos,
            state: self.state.clone(),
            stack,
            weight: self.weight,
        }
    }

    // ─── Reactive driver ────────────────────────────────────────────────────

    /// Pure transition function: apply `event` to the current configuration
    /// and return the resulting [`WpdsTransition`].
    ///
    /// This is the **primary external API** per survey mandate M1. External
    /// consumers (LSP/DAP/REPL/nREPL) drive parsing by calling this in a loop.
    ///
    /// Phase A.1: takes a `tokens: &dyn WpdsTokenSource` parameter so the
    /// engine's `step()` can peek the input during `WpdsEvent::Step`.
    pub fn process_event(
        &mut self,
        event: WpdsEvent<W>,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsTransition<W> {
        // Terminal states absorb events without further action.
        if self.state.is_terminal() {
            return WpdsTransition::NoChange;
        }
        match event {
            WpdsEvent::Inspect => WpdsTransition::NoChange,
            WpdsEvent::Step => self.handle_step(tokens),
            WpdsEvent::TokenConsumed { pos, .. } => {
                let from = self.state.clone();
                self.pos = pos;
                self.maybe_prune_frontier();
                let trace = WpdsTraceEntry {
                    pos,
                    from_state: from.clone(),
                    to_state: from.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdsTransition::Transition {
                    new_state: from,
                    trace: Some(trace),
                }
            }
            WpdsEvent::BranchForked { children, .. } => {
                let from = self.state.clone();
                let new_state = WpdsState::AmbiguityFanout {
                    branches: children.clone(),
                };
                self.state = new_state.clone();
                self.maybe_prune_frontier();
                let trace = WpdsTraceEntry {
                    pos: self.pos,
                    from_state: from,
                    to_state: new_state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdsTransition::Transition { new_state, trace: Some(trace) }
            }
            WpdsEvent::BranchResolved { winner, weight } => {
                let from = self.state.clone();
                self.weight = self.weight.times(&weight);
                self.top_node = Some(winner);
                // Stage 7+ Fork plan, step 2: clear per-branch cursors when
                // the fanout collapses. Step 3's `step_fanout` micro-driver
                // emits this event when exactly one cursor survives.
                self.branch_cursors.clear();
                let new_state = WpdsState::InfixLoop {
                    cur_bp: match from {
                        WpdsState::AmbiguityFanout { .. } => 0,
                        _ => 0,
                    },
                };
                self.state = new_state.clone();
                let trace = WpdsTraceEntry {
                    pos: self.pos,
                    from_state: from,
                    to_state: new_state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdsTransition::Transition { new_state, trace: Some(trace) }
            }
            WpdsEvent::SemanticActionFired { .. } => {
                // Walker records the firing in its trace; no state change.
                let trace = WpdsTraceEntry {
                    pos: self.pos,
                    from_state: self.state.clone(),
                    to_state: self.state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdsTransition::Transition {
                    new_state: self.state.clone(),
                    trace: Some(trace),
                }
            }
            WpdsEvent::Checkpoint { reason: _ } => {
                let config = self.current_configuration();
                WpdsTransition::Checkpoint { config }
            }
        }
    }

    /// Drive `process_event(Step)` repeatedly until a terminal state is
    /// reached or `max_steps` is exceeded. Returns the final state.
    ///
    /// Convenience wrapper for batch consumers (REPL `exec`). External
    /// consumers wanting fine-grained control should call `process_event`
    /// directly.
    pub fn run_to_completion(
        &mut self,
        max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsState {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                break;
            }
            let _ = self.process_event(WpdsEvent::Step, tokens);
        }
        self.state.clone()
    }

    /// Drive `process_event(Step)` until the engine returns `Idle` or a
    /// terminal state is reached. Implements the saturation semantics of
    /// WPDS poststar — process all derivable transitions for the current
    /// input position before returning.
    pub fn run_to_saturation(
        &mut self,
        max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsState {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                break;
            }
            // Step 3 (Fork plan F6): when in AmbiguityFanout, drive each
            // BranchCursor via step_fanout rather than asking the engine
            // about the AmbiguityFanout state itself (engine returns Idle
            // for that state).
            if matches!(self.state, WpdsState::AmbiguityFanout { .. }) {
                let prev_state = self.state.clone();
                self.step_fanout(tokens);
                if self.state == prev_state {
                    // step_fanout made no state-level progress this iter
                    // (cursors still iterating) — retry next iteration.
                    continue;
                }
                continue;
            }
            let frontier_top = self
                .top_node
                .and_then(|id| self.gss.node(id))
                .cloned();
            let action = self.engine.step(
                &self.state,
                &self.gss,
                frontier_top.as_ref(),
                self.pos,
                tokens,
            );
            if matches!(action, WpdsStepAction::Idle) {
                // B6 (2026-04-28): make stalls explicit. The engine has
                // nothing more to derive at this configuration. If the
                // walker is in a non-terminal state, this is a stall —
                // surface as Error rather than silently exiting saturation
                // (which would let the caller think the parse "completed"
                // when it actually got stuck). Terminal states
                // (Accepted/Error) are normal exits.
                if !self.state.is_terminal() {
                    self.state = WpdsState::Error {
                        message: format!(
                            "engine returned Idle in non-terminal state {:?} at pos {}",
                            self.state, self.pos,
                        ),
                    };
                }
                break;
            }
            self.apply_action(action, tokens);
        }
        self.state.clone()
    }

    // ─── Internal step handler ──────────────────────────────────────────────

    fn handle_step(&mut self, tokens: &dyn WpdsTokenSource) -> WpdsTransition<W> {
        let from = self.state.clone();
        // Step 3 (Fork plan F6): when in AmbiguityFanout, drive cursors
        // via step_fanout rather than the per-state engine.step (engine
        // returns Idle for AmbiguityFanout).
        if matches!(self.state, WpdsState::AmbiguityFanout { .. }) {
            self.step_fanout(tokens);
            if self.state == from {
                return WpdsTransition::NoChange;
            }
            let trace = WpdsTraceEntry {
                pos: self.pos,
                from_state: from,
                to_state: self.state.clone(),
                stack_depth: self.gss.frontier_size(),
            };
            if self.state.is_terminal() {
                return WpdsTransition::Done {
                    state: self.state.clone(),
                };
            }
            return WpdsTransition::Transition {
                new_state: self.state.clone(),
                trace: Some(trace),
            };
        }
        let frontier_top = self
            .top_node
            .and_then(|id| self.gss.node(id))
            .cloned();
        let action = self.engine.step(
            &self.state,
            &self.gss,
            frontier_top.as_ref(),
            self.pos,
            tokens,
        );
        if matches!(action, WpdsStepAction::Idle) {
            return WpdsTransition::NoChange;
        }
        self.apply_action(action, tokens);
        if self.state == from {
            // No state change but engine wasn't Idle — trace it as a
            // configuration change without a state transition.
            let trace = WpdsTraceEntry {
                pos: self.pos,
                from_state: from.clone(),
                to_state: from.clone(),
                stack_depth: self.gss.frontier_size(),
            };
            return WpdsTransition::Transition {
                new_state: from,
                trace: Some(trace),
            };
        }
        let trace = WpdsTraceEntry {
            pos: self.pos,
            from_state: from,
            to_state: self.state.clone(),
            stack_depth: self.gss.frontier_size(),
        };
        if self.state.is_terminal() {
            return WpdsTransition::Done {
                state: self.state.clone(),
            };
        }
        WpdsTransition::Transition {
            new_state: self.state.clone(),
            trace: Some(trace),
        }
    }

    fn apply_action(&mut self, action: WpdsStepAction<W>, tokens: &dyn WpdsTokenSource) {
        match action {
            WpdsStepAction::Advance(s) => {
                self.state = s;
            }
            WpdsStepAction::Push { mut symbol, weight, new_state } => {
                // Phase 4: pushing a CollectionMarker auto-allocates a fresh
                // accumulator id and pushes a CollectionId arg so the
                // finalize action can identify which accumulator to drain.
                if symbol.kind == SymbolKind::CollectionMarker {
                    let id = self.builder.start_collection();
                    symbol.bp = Some(id);
                    self.builder.push_collection_id(id);
                }
                let prev = self.top_node.unwrap_or_else(|| {
                    self.gss.get_or_create_node(WpdsGssNode {
                        pos: self.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    })
                });
                let new_id = self.gss.push_symbol(prev, symbol, self.pos, weight);
                self.top_node = Some(new_id);
                self.weight = self.weight.times(&weight);
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::ConsumeAndPush {
                mut symbol,
                weight,
                new_state,
                capture_token,
            } => {
                // Phase A.2: atomic-rule shortcut. Optionally capture the
                // current token, advance pos, push symbol, transition.
                if capture_token {
                    if let Some(kind) = tokens.peek_kind(self.pos) {
                        let text = tokens.peek_text(self.pos).unwrap_or("").to_string();
                        self.builder.push_token(kind, text, self.pos);
                    }
                }
                // Phase 4: same auto-allocation as `Push`.
                if symbol.kind == SymbolKind::CollectionMarker {
                    let id = self.builder.start_collection();
                    symbol.bp = Some(id);
                    self.builder.push_collection_id(id);
                }
                let prev = self.top_node.unwrap_or_else(|| {
                    self.gss.get_or_create_node(WpdsGssNode {
                        pos: self.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    })
                });
                let new_id = self.gss.push_symbol(prev, symbol, self.pos, weight);
                self.top_node = Some(new_id);
                self.weight = self.weight.times(&weight);
                self.pos += 1;
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::ConsumeAndPop { weight, new_state } => {
                // Phase 4: consume + pop + fire-action variant. Used by the
                // CollectionLoop close arm to consume the close delimiter,
                // pop the CollectionMarker, and fire its finalize action.
                let popped_symbol = self
                    .top_node
                    .and_then(|id| self.gss.node(id))
                    .map(|n| n.symbol);
                if let Some(top) = self.top_node {
                    self.top_node = self.gss.pop_symbol(top);
                }
                if let Some(symbol) = popped_symbol {
                    if matches!(
                        symbol.kind,
                        SymbolKind::Return
                            | SymbolKind::CollectionMarker
                            | SymbolKind::RuleAt(_)
                            | SymbolKind::MixfixMarker
                    ) {
                        self.fire_action_for(symbol);
                    }
                }
                // Phase 4: auto-splice into enclosing collection (nested case).
                self.maybe_splice_into_enclosing_collection();
                self.weight = self.weight.times(&weight);
                self.pos += 1;
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::Consume { weight, new_state } => {
                // Phase 4: consume-only — used by CollectionLoop separator arm
                // to advance past the separator without pushing/popping any
                // GSS frame.
                self.weight = self.weight.times(&weight);
                self.pos += 1;
                self.state = new_state;
            }
            WpdsStepAction::ConsumeIdentAndReplace {
                symbol,
                weight,
                new_state,
                start_scope,
            } => {
                // Phase 5: capture the current Ident token, optionally start
                // a binder scope, advance pos, replace the GSS top.
                if let Some(_kind) = tokens.peek_kind(self.pos) {
                    let text = tokens.peek_text(self.pos).unwrap_or("").to_string();
                    if start_scope {
                        self.builder.start_binder_scope(vec![text.clone()]);
                    }
                    self.builder.push_ident(text, self.pos);
                }
                if let Some(top) = self.top_node {
                    let new_id = self.gss.replace_top(top, symbol, self.pos, weight);
                    self.top_node = Some(new_id);
                    self.weight = self.weight.times(&weight);
                }
                self.pos += 1;
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::ConsumeAndReplace {
                symbol,
                weight,
                new_state,
            } => {
                // Phase 5: consume + replace top + transition. Used by the
                // binder-rule state machine to advance through literal
                // terminals while updating the marker's position.
                if let Some(top) = self.top_node {
                    let new_id = self.gss.replace_top(top, symbol, self.pos, weight);
                    self.top_node = Some(new_id);
                    self.weight = self.weight.times(&weight);
                }
                self.pos += 1;
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::ReplaceAndPush {
                replace_symbol,
                push_symbol,
                weight,
                new_state,
            } => {
                // Phase 5b: replace top, then push another symbol on top
                // of the replaced top. Used by ParamParse slot dispatch
                // to advance the marker AND push a CategoryEntry sub-frame.
                if let Some(top) = self.top_node {
                    let replaced = self.gss.replace_top(top, replace_symbol, self.pos, weight);
                    let pushed = self.gss.push_symbol(replaced, push_symbol, self.pos, weight);
                    self.top_node = Some(pushed);
                    self.weight = self.weight.times(&weight);
                }
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::ParsePredicate {
                replace_symbol,
                weight,
                new_state,
            } => {
                // Phase 6: parse a predicate inline. Use the runtime's
                // `parse_predicate_from_tokens` over a (kind, text) view
                // of the remaining tokens. Push as ActionArg::Predicate.
                let parsed_pred =
                    crate::parser::predicate::parse_predicate_via_token_source(
                        tokens, self.pos,
                    );
                match parsed_pred {
                    Ok((pred, new_pos)) => {
                        self.builder.push_predicate(pred);
                        self.pos = new_pos;
                    }
                    Err(msg) => {
                        self.state = WpdsState::Error { message: msg };
                        return;
                    }
                }
                if let Some(top) = self.top_node {
                    let new_id = self.gss.replace_top(top, replace_symbol, self.pos, weight);
                    self.top_node = Some(new_id);
                    self.weight = self.weight.times(&weight);
                }
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::Pop { weight, new_state } => {
                // Capture the popped symbol so we can fire a semantic action
                // if it was a `SymbolKind::Return` (or `CollectionMarker`) frame.
                let popped_symbol = self
                    .top_node
                    .and_then(|id| self.gss.node(id))
                    .map(|n| n.symbol);
                if let Some(top) = self.top_node {
                    self.top_node = self.gss.pop_symbol(top);
                }
                if let Some(symbol) = popped_symbol {
                    if matches!(
                        symbol.kind,
                        SymbolKind::Return
                            | SymbolKind::CollectionMarker
                            | SymbolKind::RuleAt(_)
                            | SymbolKind::MixfixMarker
                    ) {
                        self.fire_action_for(symbol);
                    }
                }
                // Phase 4: when popping a `Return` whose predecessor is a
                // `CollectionMarker`, splice the just-built term into the
                // enclosing collection accumulator.
                self.maybe_splice_into_enclosing_collection();
                self.weight = self.weight.times(&weight);
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::Replace { symbol, weight, new_state } => {
                if let Some(top) = self.top_node {
                    let new_id = self.gss.replace_top(top, symbol, self.pos, weight);
                    self.top_node = Some(new_id);
                    self.weight = self.weight.times(&weight);
                }
                self.state = new_state;
                self.maybe_prune_frontier();
            }
            WpdsStepAction::Fork { branches, consume_trigger } => {
                // Stage 7+ Fork plan, step 2: populate per-branch cursors
                // alongside the GSS-tip ids. Each cursor inherits the walker's
                // current `pos` (advanced by 1 when `consume_trigger`), the
                // branch's weight, and the branch's own `new_state` as its
                // initial inner state. Subsequent `step_fanout` micro-steps
                // drive each cursor independently until exactly one survives
                // (BranchResolved) or all die (Error). Per-branch `new_state`
                // (vs a shared one) lets codegen route each rule in a
                // multi-rule group to its own target state.
                if consume_trigger {
                    self.pos += 1;
                }
                let prev = self.top_node;
                let mut child_ids = Vec::with_capacity(branches.len());
                let mut cursors: Vec<BranchCursor<W>> = Vec::with_capacity(branches.len());
                for branch in branches {
                    if let Some(p) = prev {
                        let id = self.gss.push_symbol(
                            p,
                            branch.symbol,
                            self.pos,
                            branch.weight.clone(),
                        );
                        child_ids.push(id);
                        cursors.push(BranchCursor {
                            node: id,
                            pos: self.pos,
                            weight: branch.weight,
                            inner_state: branch.new_state,
                            pending_builder_ops: Vec::new(),
                            collection_stack: Vec::new(),
                        });
                    }
                }
                self.branch_cursors = cursors;
                self.state = WpdsState::AmbiguityFanout { branches: child_ids };
                self.maybe_prune_frontier();
            }
            WpdsStepAction::Accept => {
                self.state = WpdsState::Accepted;
            }
            WpdsStepAction::Error(message) => {
                self.state = WpdsState::Error { message };
            }
            WpdsStepAction::Idle => { /* unreachable per caller filter */ }
        }
    }

    /// Step 3 (Fork plan F5): per-cursor analog of `apply_action`. Mutates
    /// `cursor.{node,pos,weight,inner_state}` in place and logs walker-driven
    /// builder mutations into `cursor.pending_builder_ops` instead of
    /// touching the live `SemanticBuilder`.
    ///
    /// Returns a [`CursorOutcome`] describing whether the cursor is dead,
    /// alive, forked, or resolved (candidate winner). See module docs for
    /// the detailed mapping per `WpdsStepAction` variant.
    fn apply_action_to_cursor(
        &mut self,
        cursor: &mut BranchCursor<W>,
        action: WpdsStepAction<W>,
        tokens: &dyn WpdsTokenSource,
    ) -> CursorOutcome<W> {
        match action {
            WpdsStepAction::Advance(s) => {
                cursor.inner_state = s;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Push { mut symbol, weight, new_state } => {
                // Option A (2026-04-28): per-cursor CollectionMarker support.
                // Allocate the accumulator id from the cursor's local
                // mirror (NOT the live builder). Set `symbol.bp` so the
                // GSS-deposited symbol carries the id; log a
                // `PushCollectionId` delta so commit_winner pushes the
                // matching `CollectionId(id)` arg onto the live builder
                // stack after `adopt_collection_stack` donates the
                // cursor's accumulators en bloc.
                if symbol.kind == SymbolKind::CollectionMarker {
                    let id = cursor.collection_stack.len() as u8;
                    cursor.collection_stack.push(Vec::new());
                    symbol.bp = Some(id);
                    cursor
                        .pending_builder_ops
                        .push(BuilderDelta::PushCollectionId { id });
                }
                let new_id = self.gss.push_symbol(cursor.node, symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Pop { weight, new_state } => {
                let popped_symbol = self.gss.node(cursor.node).map(|n| n.symbol);
                let predecessor = self.gss.pop_symbol(cursor.node);
                if let Some(symbol) = popped_symbol {
                    if matches!(
                        symbol.kind,
                        SymbolKind::Return
                            | SymbolKind::CollectionMarker
                            | SymbolKind::RuleAt(_)
                            | SymbolKind::MixfixMarker
                    ) {
                        cursor.pending_builder_ops.push(BuilderDelta::FireAction {
                            symbol,
                        });
                    }
                }
                // Cleanup 1 (Option A refinement): log SpliceIntoCollection
                // only when the popped frame's predecessor is a
                // CollectionMarker. The accumulator id is captured directly
                // from the predecessor's symbol.bp; replay is then a pure
                // push_to_collection(id) — no GSS walk, no walker-state
                // mutation. When no enclosing collection exists, no delta
                // is logged (the prior unconditional MaybeSpliceCollection
                // delta was a known-no-op in that case).
                if let Some(pred_id) = predecessor {
                    if let Some(pred_node) = self.gss.node(pred_id) {
                        if pred_node.symbol.kind == SymbolKind::CollectionMarker {
                            let acc_id = pred_node.symbol.bp.unwrap_or(0);
                            cursor
                                .pending_builder_ops
                                .push(BuilderDelta::SpliceIntoCollection { id: acc_id });
                        }
                    }
                }
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                match predecessor {
                    Some(p) => {
                        cursor.node = p;
                        self.cursor_resolution_check(cursor)
                    }
                    None => CursorOutcome::Resolved,
                }
            }
            WpdsStepAction::Replace { symbol, weight, new_state } => {
                let new_id = self.gss.replace_top(cursor.node, symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Consume { weight, new_state } => {
                cursor.pos += 1;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeAndPush {
                mut symbol,
                weight,
                new_state,
                capture_token,
            } => {
                // Cleanup 2 (Option A refinement, 2026-04-28): order matches
                // live `apply_action::ConsumeAndPush` — capture_token logged
                // FIRST, then collection-marker id allocation. The prior
                // (pre-cleanup) order was reversed, which would have produced
                // wrong builder-stack arg order on replay. No shipped grammar
                // emits `capture_token: true` AND `CollectionMarker` together
                // today (atomic-literal arms use Return; collection arms use
                // capture_token: false), so the bug was latent. Fixing it
                // matches live semantics for any future code that combines
                // both flags.
                if capture_token {
                    if let Some(kind) = tokens.peek_kind(cursor.pos) {
                        let text =
                            tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                        cursor.pending_builder_ops.push(BuilderDelta::PushToken {
                            kind,
                            text,
                            pos: cursor.pos,
                        });
                    }
                }
                if symbol.kind == SymbolKind::CollectionMarker {
                    let id = cursor.collection_stack.len() as u8;
                    cursor.collection_stack.push(Vec::new());
                    symbol.bp = Some(id);
                    cursor
                        .pending_builder_ops
                        .push(BuilderDelta::PushCollectionId { id });
                }
                let new_id = self.gss.push_symbol(cursor.node, symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.pos += 1;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeAndPop { weight, new_state } => {
                let popped_symbol = self.gss.node(cursor.node).map(|n| n.symbol);
                let predecessor = self.gss.pop_symbol(cursor.node);
                if let Some(symbol) = popped_symbol {
                    if matches!(
                        symbol.kind,
                        SymbolKind::Return
                            | SymbolKind::CollectionMarker
                            | SymbolKind::RuleAt(_)
                            | SymbolKind::MixfixMarker
                    ) {
                        cursor.pending_builder_ops.push(BuilderDelta::FireAction {
                            symbol,
                        });
                    }
                }
                // Cleanup 1 (Option A refinement): same conditional log
                // as the Pop arm above — splice only when popping reveals
                // an enclosing CollectionMarker.
                if let Some(pred_id) = predecessor {
                    if let Some(pred_node) = self.gss.node(pred_id) {
                        if pred_node.symbol.kind == SymbolKind::CollectionMarker {
                            let acc_id = pred_node.symbol.bp.unwrap_or(0);
                            cursor
                                .pending_builder_ops
                                .push(BuilderDelta::SpliceIntoCollection { id: acc_id });
                        }
                    }
                }
                cursor.pos += 1;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                match predecessor {
                    Some(p) => {
                        cursor.node = p;
                        self.cursor_resolution_check(cursor)
                    }
                    None => CursorOutcome::Resolved,
                }
            }
            WpdsStepAction::ConsumeAndReplace { symbol, weight, new_state } => {
                let new_id = self.gss.replace_top(cursor.node, symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.pos += 1;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeIdentAndReplace {
                symbol,
                weight,
                new_state,
                start_scope,
            } => {
                if let Some(_kind) = tokens.peek_kind(cursor.pos) {
                    let text = tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                    if start_scope {
                        cursor
                            .pending_builder_ops
                            .push(BuilderDelta::StartBinderScope {
                                names: vec![text.clone()],
                            });
                    }
                    cursor.pending_builder_ops.push(BuilderDelta::PushIdent {
                        name: text,
                        pos: cursor.pos,
                    });
                }
                let new_id = self.gss.replace_top(cursor.node, symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.pos += 1;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ReplaceAndPush {
                replace_symbol,
                push_symbol,
                weight,
                new_state,
            } => {
                let replaced =
                    self.gss.replace_top(cursor.node, replace_symbol, cursor.pos, weight);
                let pushed = self.gss.push_symbol(replaced, push_symbol, cursor.pos, weight);
                cursor.node = pushed;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ParsePredicate {
                replace_symbol,
                weight,
                new_state,
            } => {
                let parsed_pred =
                    crate::parser::predicate::parse_predicate_via_token_source(
                        tokens, cursor.pos,
                    );
                match parsed_pred {
                    Ok((pred, new_pos)) => {
                        cursor.pending_builder_ops.push(BuilderDelta::PushPredicate(
                            Arc::new(pred),
                        ));
                        cursor.pos = new_pos;
                    }
                    Err(_msg) => return CursorOutcome::Drop,
                }
                let new_id = self.gss.replace_top(cursor.node, replace_symbol, cursor.pos, weight);
                cursor.node = new_id;
                cursor.weight = cursor.weight.times(&weight);
                cursor.inner_state = new_state;
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Fork { branches, consume_trigger } => {
                // Option A (2026-04-28): nested Fork — cursor encountered
                // another Fork action. F7 (binder multi-rule) and F8
                // (cross-cat projection bucketing) both emit Fork; when a
                // binder body parses a token whose category has its own
                // multi-projection bucket, we land here. Translate to
                // `CursorOutcome::ForkInto(children)`: allocate one child
                // cursor per branch; each inherits this cursor's GSS chain
                // + the branch's symbol, the post-consume pos, the branch's
                // new_state, and a clone of the current pending_builder_ops
                // and collection_stack.
                //
                // Constraint (from BranchCursor::clone debug_asserts):
                // pending_builder_ops contains no PushPredicate (would be
                // silently lost on clone), and collection_stack accumulators
                // are all empty (Term values are non-clonable). Both are
                // satisfied at fanout-entry boundaries: nested Fork only
                // fires at PrefixDispatch transitions where binder bodies
                // delegate to source-category dispatch — no in-flight
                // predicate or collection state.
                let pos_after = if consume_trigger {
                    cursor.pos + 1
                } else {
                    cursor.pos
                };
                let mut children = Vec::with_capacity(branches.len());
                for branch in branches {
                    let new_id = self.gss.push_symbol(
                        cursor.node,
                        branch.symbol,
                        pos_after,
                        branch.weight.clone(),
                    );
                    children.push(BranchCursor {
                        node: new_id,
                        pos: pos_after,
                        weight: cursor.weight.times(&branch.weight),
                        inner_state: branch.new_state,
                        // Cleanup 4: BuilderDelta is now Clone (PushPredicate
                        // carries Arc<dyn Any + Send + Sync>); use direct
                        // Vec::clone instead of the deleted clone_non_predicate.
                        pending_builder_ops: cursor.pending_builder_ops.clone(),
                        collection_stack: cursor
                            .collection_stack
                            .iter()
                            .map(|_| Vec::new())
                            .collect(),
                    });
                }
                CursorOutcome::ForkInto(children)
            }
            WpdsStepAction::Accept => CursorOutcome::Resolved,
            WpdsStepAction::Error(_) => CursorOutcome::Drop,
            WpdsStepAction::Idle => {
                // Cursor's engine has no opinion. Treat as Drop to avoid
                // infinite step_fanout iterations (a branch that cannot
                // make progress is effectively dead).
                CursorOutcome::Drop
            }
        }
    }

    /// After `apply_action_to_cursor` updates `cursor.inner_state`, classify
    /// whether the cursor has reached a "branch is done" state that signals
    /// `Resolved` to the fanout driver. Otherwise return `Alive`.
    ///
    /// "Branch is done" states (per Plan agent F5 §4): `InfixLoop`,
    /// `Accepted`, `Unwinding`. These are the states where a forked branch
    /// has rejoined the main parse trunk — safe to commit the winning
    /// branch's accumulated pending_builder_ops and resume there.
    fn cursor_resolution_check(&self, cursor: &BranchCursor<W>) -> CursorOutcome<W> {
        if matches!(
            cursor.inner_state,
            WpdsState::InfixLoop { .. }
                | WpdsState::Accepted
                | WpdsState::Unwinding
        ) {
            CursorOutcome::Resolved
        } else {
            CursorOutcome::Alive
        }
    }

    /// Step 3 (Fork plan F6): per-step driver for `WpdsState::AmbiguityFanout`.
    ///
    /// Iterates each `BranchCursor`, queries the engine for an action against
    /// the cursor's per-branch state, applies the action via
    /// `apply_action_to_cursor`, classifies the outcome, and dispatches:
    ///
    /// - **Case 1: all dropped** → walker enters `Error("all branches dropped")`.
    /// - **Case 2 / 3: at least one Resolved (and no still-Alive cursors)**
    ///   → pick lex-min winner via `Semiring::plus`-fold across resolved
    ///   cursors, replay its `pending_builder_ops` against the live builder,
    ///   commit its `(node, pos, weight, inner_state)` to the walker.
    /// - **Case 4: still-Alive cursors remain** → keep iterating in the
    ///   `branch_cursors` vec; walker stays in `AmbiguityFanout`.
    ///
    /// Returns the new `WpdsState` after this micro-step (which may still
    /// be `AmbiguityFanout` if Case 4 fires).
    fn step_fanout(&mut self, tokens: &dyn WpdsTokenSource) -> WpdsState {
        let mut new_cursors: Vec<BranchCursor<W>> = Vec::with_capacity(self.branch_cursors.len());
        // Track which entries in `new_cursors` are Resolved.
        let mut resolved_indices: Vec<usize> = Vec::new();
        let drained: Vec<BranchCursor<W>> = std::mem::take(&mut self.branch_cursors);
        for cursor in drained {
            let frontier_top = self.gss.node(cursor.node).cloned();
            let action = self.engine.step(
                &cursor.inner_state,
                &self.gss,
                frontier_top.as_ref(),
                cursor.pos,
                tokens,
            );
            let mut cursor = cursor;
            let outcome = self.apply_action_to_cursor(&mut cursor, action, tokens);
            match outcome {
                CursorOutcome::Drop => { /* discard */ }
                CursorOutcome::Alive => new_cursors.push(cursor),
                CursorOutcome::ForkInto(children) => new_cursors.extend(children),
                CursorOutcome::Resolved => {
                    resolved_indices.push(new_cursors.len());
                    new_cursors.push(cursor);
                }
            }
        }
        self.branch_cursors = new_cursors;

        if self.branch_cursors.is_empty() {
            // CASE 1: all branches dropped.
            let s = WpdsState::Error {
                message: "all fork branches dropped".to_string(),
            };
            self.state = s.clone();
            return s;
        }

        let alive_count = self.branch_cursors.len() - resolved_indices.len();
        if alive_count == 0 {
            // CASE 2/3: every remaining cursor is Resolved. Tiebreak by
            // lex-min weight via `Semiring::plus` (which for
            // LexicographicWeight is lex-min, and for tropical is min).
            let winner_idx = self.pick_lex_min_resolved(&resolved_indices);
            self.commit_winner(winner_idx);
            return self.state.clone();
        }
        // CASE 4: still-Alive cursors remain. Stay in AmbiguityFanout.
        // (Resolved cursors persist in branch_cursors as candidates that
        // will be re-evaluated against any later resolved cursor's weight.)
        let frontier: Vec<crate::gss::GssNodeId> =
            self.branch_cursors.iter().map(|c| c.node).collect();
        let s = WpdsState::AmbiguityFanout { branches: frontier };
        self.state = s.clone();
        s
    }

    /// Lex-min selection across the indices in `resolved_indices` against
    /// `self.branch_cursors`. Uses `Semiring::plus` as the lex-min combiner
    /// (LexicographicWeight::plus returns the smaller; tropical::plus returns
    /// the min). On ties returns the earlier index — preserves source-order
    /// for codegen-driven Fork branches.
    fn pick_lex_min_resolved(&self, resolved_indices: &[usize]) -> usize {
        debug_assert!(!resolved_indices.is_empty(), "no resolved cursors to pick from");
        let mut best = resolved_indices[0];
        for &idx in &resolved_indices[1..] {
            // For lex-min: a wins iff a.plus(b) == a (i.e. a is the smaller
            // of the two under the semiring's lex-min ordering). On equal
            // weights, plus returns *self per LexicographicWeight::plus, so
            // `best` keeps source-order priority.
            let merged = self.branch_cursors[best]
                .weight
                .plus(&self.branch_cursors[idx].weight);
            if merged != self.branch_cursors[best].weight {
                best = idx;
            }
        }
        best
    }

    /// Step 3 (Fork plan F6): commit the winning branch.
    ///
    /// Replays the winner's `pending_builder_ops` against the live
    /// `SemanticBuilder` in insertion order, then splices the winner's
    /// `(node, pos, weight, inner_state)` into the walker's live state.
    /// Clears `branch_cursors`.
    fn commit_winner(&mut self, winner_idx: usize) {
        let mut winner = self.branch_cursors.swap_remove(winner_idx);
        self.branch_cursors.clear();
        // Option A (2026-04-28): donate cursor-local collection
        // accumulators to the live builder en bloc, BEFORE delta replay.
        // Subsequent `MaybeSpliceCollection` (calls
        // `push_to_collection(id)`) and `FireAction` (whose action calls
        // `drain_collection(id)`) deltas need populated slots in the live
        // builder. The cursor's mirror is moved here; the cursor's
        // collection_stack is left empty.
        let donated = std::mem::take(&mut winner.collection_stack);
        if !donated.is_empty() {
            self.builder.adopt_collection_stack(donated);
        }
        for delta in winner.pending_builder_ops {
            match delta {
                BuilderDelta::PushToken { kind, text, pos } => {
                    self.builder.push_token(kind, text, pos);
                }
                BuilderDelta::PushIdent { name, pos } => {
                    self.builder.push_ident(name, pos);
                }
                BuilderDelta::PushPredicate(pred) => {
                    self.builder.push_predicate_arc(pred);
                }
                BuilderDelta::StartBinderScope { names } => {
                    self.builder.start_binder_scope(names);
                }
                BuilderDelta::FireAction { symbol } => {
                    self.fire_action_for(symbol);
                    // Cleanup 3 (Option A refinement): fire_action_for sets
                    // state = WpdsState::Error{..} on builder underflow
                    // (engine arity bug). Bail out of the replay loop and
                    // skip the post-loop state install so the Error survives
                    // — without this guard, the unconditional Step-3 install
                    // would silently overwrite Error with winner.inner_state.
                    if self.state.is_terminal() {
                        self.top_node = Some(winner.node);
                        self.pos = winner.pos;
                        self.weight = self.weight.times(&winner.weight);
                        return;
                    }
                }
                BuilderDelta::PushCollectionId { id } => {
                    self.builder.push_collection_id(id);
                }
                BuilderDelta::SpliceIntoCollection { id } => {
                    // Cleanup 1: pure replay. The id was captured at log
                    // time from the predecessor's CollectionMarker.symbol.bp,
                    // so no walker-state mutation, no GSS read.
                    self.builder.push_to_collection(id);
                }
            }
        }
        self.top_node = Some(winner.node);
        self.pos = winner.pos;
        self.weight = self.weight.times(&winner.weight);
        self.state = winner.inner_state;
    }

    fn maybe_prune_frontier(&mut self) {
        // Stub for Stage 4: real beam pruning needs LexicographicWeight Ord.
        // Kept here as a hook so future commits don't restructure the walker.
        let _ = self.beam_size;
    }

    /// Phase 4: if the new GSS top after a Pop is a `CollectionMarker`,
    /// splice the just-built top of the builder stack into the enclosing
    /// collection accumulator. Called after element-rule `Return` pops
    /// (where the action just pushed the constructed element) and after
    /// nested-collection `CollectionMarker` pops (where the finalize action
    /// just pushed the constructed container).
    fn maybe_splice_into_enclosing_collection(&mut self) {
        if let Some(new_top_id) = self.top_node {
            if let Some(new_top) = self.gss.node(new_top_id) {
                if new_top.symbol.kind == SymbolKind::CollectionMarker {
                    let acc_id = new_top.symbol.bp.unwrap_or(0);
                    self.builder.push_to_collection(acc_id);
                }
            }
        }
    }

    /// Fire the semantic action attached to `(src_idx, rule_idx)` if the
    /// engine has one registered. Consumes `entry.arity` args from the
    /// top of the builder's stack. No-op if the engine returns `None`
    /// (rule has no semantic action).
    fn fire_action_for(&mut self, symbol: StackSymbolV2) {
        if let Some(entry) = self
            .engine
            .action_for(symbol.category_src_idx, symbol.rule_index_in_category)
        {
            let arity = entry.arity as usize;
            let action_fn = entry.action_fn;
            if self.builder.len() >= arity {
                let args = self.builder.pop_args(arity);
                action_fn(&mut self.builder, args);
            } else {
                // Builder under-flow is an engine-arity bug; set Error state.
                self.state = WpdsState::Error {
                    message: format!(
                        "semantic-action arity mismatch at rule (src={}, rule={}): \
                         expected {} args but builder held {}",
                        symbol.category_src_idx,
                        symbol.rule_index_in_category,
                        arity,
                        self.builder.len(),
                    ),
                };
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdsControl helper (re-export for external consumers)
// ══════════════════════════════════════════════════════════════════════════════

/// Re-exported [`WpdsControl`] for convenience.
pub use crate::wpds_runtime::WpdsControl as WalkerControl;

/// A no-op step engine that always returns [`WpdsStepAction::Idle`].
///
/// Useful as a placeholder before Stage 6's codegen lands.
pub struct IdleEngine;

impl<W: Semiring> WpdsStepEngine<W> for IdleEngine {
    fn step(
        &self,
        _state: &WpdsState,
        _gss: &WpdsGss<W>,
        _frontier_top: Option<&WpdsGssNode>,
        _pos: usize,
        _tokens: &dyn WpdsTokenSource,
    ) -> WpdsStepAction<W> {
        WpdsStepAction::Idle
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WalkerConsumer trait (Stage 5: M2 — observer is SECONDARY contract)
// ══════════════════════════════════════════════════════════════════════════════

/// Callback interface attached to a [`WpdsWalker`] for side-effect interception.
///
/// Per the survey contract M2 (`prattail/docs/design/wpds-migration-survey.md`),
/// the observer is the **secondary** contract; primary is `process_event`.
/// Consumers implement this to receive notifications during the walker's
/// reactive loop.
///
/// ## Zero-cost null path
///
/// Generic-typed (no trait objects). [`NullConsumer`] monomorphizes to a
/// no-op the optimizer eliminates entirely. Observed-callback overhead is
/// only paid when a non-trivial consumer is attached.
pub trait WalkerConsumer<W: Semiring> {
    /// Called after each event the walker processes.
    ///
    /// Return value directs the walker's next action:
    /// - `Continue`: proceed to next event
    /// - `Checkpoint`: snapshot current configuration, then continue
    /// - `Abort`: halt evaluation; walker enters Error state
    /// - `Pause`: suspend awaiting external resumption (DAP/REPL)
    fn on_event(&mut self, event: &WpdsEvent<W>, state: &WpdsState) -> WpdsControl;

    /// Called when a Checkpoint transition is emitted.
    #[inline(always)]
    fn on_checkpoint(&mut self, _config: &WpdsConfiguration<W>) {}

    /// Called once when the walker reaches a terminal state.
    #[inline(always)]
    fn on_complete(&mut self, _state: &WpdsState) {}
}

/// Zero-cost no-op consumer — monomorphizes away.
///
/// Use when no tracing or control is required (batch parsing).
pub struct NullConsumer;

impl<W: Semiring> WalkerConsumer<W> for NullConsumer {
    #[inline(always)]
    fn on_event(&mut self, _event: &WpdsEvent<W>, _state: &WpdsState) -> WpdsControl {
        WpdsControl::Continue
    }
}

/// Lightweight event tag for trace recording (avoids cloning event payloads).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WpdsEventTag {
    Step,
    TokenConsumed,
    BranchForked,
    BranchResolved,
    SemanticActionFired,
    Checkpoint,
    Inspect,
}

impl WpdsEventTag {
    fn of<W: Semiring>(event: &WpdsEvent<W>) -> Self {
        match event {
            WpdsEvent::Step => WpdsEventTag::Step,
            WpdsEvent::TokenConsumed { .. } => WpdsEventTag::TokenConsumed,
            WpdsEvent::BranchForked { .. } => WpdsEventTag::BranchForked,
            WpdsEvent::BranchResolved { .. } => WpdsEventTag::BranchResolved,
            WpdsEvent::SemanticActionFired { .. } => WpdsEventTag::SemanticActionFired,
            WpdsEvent::Checkpoint { .. } => WpdsEventTag::Checkpoint,
            WpdsEvent::Inspect => WpdsEventTag::Inspect,
        }
    }
}

/// Tracing consumer: records every event tag and resulting state.
///
/// Useful for DAP step-recording, REPL history, post-mortem analysis.
pub struct TracingConsumer<W: Semiring> {
    pub events: Vec<(WpdsEventTag, WpdsState)>,
    pub checkpoints: Vec<WpdsConfiguration<W>>,
    pub final_state: Option<WpdsState>,
}

impl<W: Semiring> TracingConsumer<W> {
    pub fn new() -> Self {
        TracingConsumer {
            events: Vec::new(),
            checkpoints: Vec::new(),
            final_state: None,
        }
    }
}

impl<W: Semiring> Default for TracingConsumer<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> WalkerConsumer<W> for TracingConsumer<W> {
    fn on_event(&mut self, event: &WpdsEvent<W>, state: &WpdsState) -> WpdsControl {
        self.events.push((WpdsEventTag::of(event), state.clone()));
        WpdsControl::Continue
    }

    fn on_checkpoint(&mut self, config: &WpdsConfiguration<W>) {
        self.checkpoints.push(config.clone());
    }

    fn on_complete(&mut self, state: &WpdsState) {
        self.final_state = Some(state.clone());
    }
}

/// A consumer that aborts evaluation after `n` events.
///
/// Useful for guarding against runaway parses during property tests or
/// DAP step-limit enforcement.
pub struct AbortAfterConsumer {
    pub limit: usize,
    pub count: usize,
}

impl AbortAfterConsumer {
    pub fn new(limit: usize) -> Self {
        AbortAfterConsumer { limit, count: 0 }
    }
}

impl<W: Semiring> WalkerConsumer<W> for AbortAfterConsumer {
    fn on_event(&mut self, _event: &WpdsEvent<W>, _state: &WpdsState) -> WpdsControl {
        self.count += 1;
        if self.count >= self.limit {
            WpdsControl::Abort
        } else {
            WpdsControl::Continue
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdsWalker::run_with_consumer
// ══════════════════════════════════════════════════════════════════════════════

impl<W: Semiring, E: WpdsStepEngine<W>> WpdsWalker<W, E> {
    /// Drive the walker reactively with a [`WalkerConsumer`] attached.
    ///
    /// Each iteration:
    /// 1. Process `WpdsEvent::Step` (driving the FSM via the engine).
    /// 2. If transition was `Checkpoint`, notify `consumer.on_checkpoint`.
    /// 3. Notify `consumer.on_event(Step, current_state)`.
    /// 4. Honor consumer's `WpdsControl` directive.
    ///
    /// Terminates when state is terminal, max_steps exceeded, consumer aborts,
    /// or consumer pauses. Calls `consumer.on_complete(&final_state)` exactly
    /// once unless paused.
    pub fn run_with_consumer<C: WalkerConsumer<W>>(
        &mut self,
        consumer: &mut C,
        max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsState {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                consumer.on_complete(&self.state);
                return self.state.clone();
            }
            let event = WpdsEvent::Step;
            let transition = self.process_event(event.clone(), tokens);
            if let WpdsTransition::Checkpoint { ref config } = transition {
                consumer.on_checkpoint(config);
            }
            match consumer.on_event(&event, &self.state) {
                WpdsControl::Continue => {}
                WpdsControl::Checkpoint => {
                    let config = self.current_configuration();
                    consumer.on_checkpoint(&config);
                }
                WpdsControl::Abort => {
                    self.state = WpdsState::Error {
                        message: "consumer aborted".to_string(),
                    };
                    consumer.on_complete(&self.state);
                    return self.state.clone();
                }
                WpdsControl::Pause => {
                    // Caller resumes by calling run_with_consumer again later.
                    return self.state.clone();
                }
            }
        }
        consumer.on_complete(&self.state);
        self.state.clone()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::TokenKind;
    use std::cell::RefCell;

    fn lex(c: f64, s: u16, r: u16) -> LexicographicWeight {
        LexicographicWeight::from_cost(c, s, r)
    }

    /// Test engine driven by a programmable script of actions.
    struct ScriptedEngine {
        script: RefCell<Vec<WpdsStepAction<LexicographicWeight>>>,
    }

    impl ScriptedEngine {
        fn new(actions: Vec<WpdsStepAction<LexicographicWeight>>) -> Self {
            ScriptedEngine {
                script: RefCell::new(actions),
            }
        }
    }

    impl WpdsStepEngine<LexicographicWeight> for ScriptedEngine {
        fn step(
            &self,
            _state: &WpdsState,
            _gss: &WpdsGss<LexicographicWeight>,
            _frontier_top: Option<&WpdsGssNode>,
            _pos: usize,
            _tokens: &dyn WpdsTokenSource,
        ) -> WpdsStepAction<LexicographicWeight> {
            self.script
                .borrow_mut()
                .pop()
                .unwrap_or(WpdsStepAction::Idle)
        }
    }

    /// Empty token source used by tests that don't inspect input.
    fn empty_tokens() -> crate::wpds_runtime::SliceTokenSource<'static> {
        static EMPTY: [TokenKind; 0] = [];
        crate::wpds_runtime::SliceTokenSource::new(&EMPTY)
    }

    // ─── Shape tests ────────────────────────────────────────────────────────

    #[test]
    fn walker_starts_in_ready_state() {
        let w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        assert_eq!(*w.state(), WpdsState::Ready { min_bp: 0 });
        assert_eq!(w.position(), 0);
        assert!(w.gss().is_empty());
        assert_eq!(w.beam_size(), None);
    }

    #[test]
    fn walker_with_beam_size_records_bound() {
        let w: WpdsWalker<LexicographicWeight, _> =
            WpdsWalker::new(IdleEngine, 0).with_beam_size(8);
        assert_eq!(w.beam_size(), Some(8));
    }

    #[test]
    fn process_event_inspect_yields_no_change() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::Inspect, &empty_tokens());
        assert!(matches!(t, WpdsTransition::NoChange));
    }

    #[test]
    fn process_event_step_with_idle_engine_yields_no_change() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::Step, &empty_tokens());
        assert!(matches!(t, WpdsTransition::NoChange));
    }

    #[test]
    fn process_event_step_advances_state_via_engine() {
        // Script (popped from end): Advance(PrefixDispatch) only — fires once.
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Advance(
            WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        )]);
        let mut w = WpdsWalker::new(engine, 0);
        let t = w.process_event(WpdsEvent::Step, &empty_tokens());
        match t {
            WpdsTransition::Transition { new_state, .. } => {
                assert_eq!(new_state, WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 });
            }
            other => panic!("expected Transition, got {:?}", other),
        }
        assert_eq!(*w.state(), WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 });
    }

    #[test]
    fn process_event_token_consumed_advances_position() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::TokenConsumed {
            pos: 5,
            token: TokenKind::Ident,
        }, &empty_tokens());
        assert!(matches!(t, WpdsTransition::Transition { .. }));
        assert_eq!(w.position(), 5);
    }

    #[test]
    fn process_event_branch_forked_enters_ambiguity_fanout() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::BranchForked {
            parent: 0,
            children: vec![1, 2, 3],
        }, &empty_tokens());
        assert!(matches!(t, WpdsTransition::Transition { .. }));
        match w.state() {
            WpdsState::AmbiguityFanout { branches } => {
                assert_eq!(branches, &vec![1u32, 2u32, 3u32]);
            }
            other => panic!("expected AmbiguityFanout, got {:?}", other),
        }
    }

    #[test]
    fn process_event_branch_resolved_exits_ambiguity_fanout() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let _ = w.process_event(WpdsEvent::BranchForked {
            parent: 0,
            children: vec![1, 2],
        }, &empty_tokens());
        let t = w.process_event(WpdsEvent::BranchResolved {
            winner: 1,
            weight: lex(2.5, 3, 4),
        }, &empty_tokens());
        assert!(matches!(t, WpdsTransition::Transition { .. }));
        match w.state() {
            WpdsState::InfixLoop { .. } => {}
            other => panic!("expected InfixLoop after resolution, got {:?}", other),
        }
        // Cumulative weight should reflect the resolved branch.
        assert!((w.weight().primary.0 - 2.5).abs() < 1e-9);
        assert_eq!(w.weight().src_idx, 3);
        assert_eq!(w.weight().rule_idx, 4);
    }

    #[test]
    fn process_event_semantic_action_fired_records_trace() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::SemanticActionFired {
            action_id: 42,
            args: vec![0, 1, 2],
        }, &empty_tokens());
        assert!(matches!(t, WpdsTransition::Transition { trace: Some(_), .. }));
    }

    #[test]
    fn process_event_checkpoint_emits_checkpoint_transition() {
        let mut w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdsEvent::Checkpoint {
            reason: CheckpointReason::NaturalBoundary,
        }, &empty_tokens());
        match t {
            WpdsTransition::Checkpoint { config } => {
                assert_eq!(config.pos, 0);
                assert_eq!(config.state, WpdsState::Ready { min_bp: 0 });
            }
            other => panic!("expected Checkpoint, got {:?}", other),
        }
    }

    #[test]
    fn terminal_state_absorbs_events_without_change() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Accept]);
        let mut w = WpdsWalker::new(engine, 0);
        let t1 = w.process_event(WpdsEvent::Step, &empty_tokens());
        assert!(matches!(t1, WpdsTransition::Done { .. }));
        assert_eq!(*w.state(), WpdsState::Accepted);
        // Further events yield NoChange.
        let t2 = w.process_event(WpdsEvent::Step, &empty_tokens());
        assert!(matches!(t2, WpdsTransition::NoChange));
        let t3 = w.process_event(WpdsEvent::Inspect, &empty_tokens());
        assert!(matches!(t3, WpdsTransition::NoChange));
    }

    #[test]
    fn step_action_error_transitions_to_error_state() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Error("bad parse".to_string())]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        match w.state() {
            WpdsState::Error { message } => assert_eq!(message, "bad parse"),
            other => panic!("expected Error state, got {:?}", other),
        }
    }

    #[test]
    fn step_action_push_grows_gss_and_updates_weight() {
        // Push action emits a new symbol on top of an entry frame.
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
            weight: lex(2.0, 0, 1),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 7 },
        }]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        // GSS now has at least the entry node + the pushed node.
        assert!(w.gss().node_count() >= 2);
        assert!((w.weight().primary.0 - 2.0).abs() < 1e-9);
    }

    #[test]
    fn step_action_replace_keeps_predecessor() {
        let engine = ScriptedEngine::new(vec![
            // Last popped first: replace runs second, push runs first.
            WpdsStepAction::Replace {
                symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                weight: lex(0.5, 0, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push
        let initial_count = w.gss().node_count();
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Replace
        // Replace adds a new node (replace_top creates rather than mutates).
        assert!(w.gss().node_count() > initial_count);
    }

    #[test]
    fn step_action_fork_enters_ambiguity_fanout() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry first.
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        match w.state() {
            WpdsState::AmbiguityFanout { branches } => {
                assert_eq!(branches.len(), 2);
            }
            other => panic!("expected AmbiguityFanout after Fork, got {:?}", other),
        }
    }

    /// Fork plan F4-F6: synthetic test that asserts the
    /// `Fork → AmbiguityFanout → step_fanout → commit_winner` flow runs
    /// end-to-end and selects the lex-min winner.
    ///
    /// Tracked in `feedback_use_wpds_disambiguation_not_heuristics.md`
    /// and `wpds-fork-action-items-2026-04-27.md`.
    #[test]
    fn fork_drives_to_lex_min_winner() {
        // Engine: at Ready -> Push entry -> Fork with 3 branches.
        // Each branch returns an immediate Pop; LexicographicWeight
        // tiebreaks on (cost, src_idx, rule_idx) — lower rule_idx wins.
        let engine = ScriptedEngine::new(vec![
            // Branch evaluation steps: ScriptedEngine pops in LIFO order, so
            // these are consumed in the order Pop(2), Pop(1), Pop(0) — that
            // is, cursors[0] receives the last-pushed Pop, cursors[1] the
            // middle, cursors[2] the first. Per-cursor weight after Pop:
            //   cursor[0].weight = lex(1.0,0,0).times(lex(1.0,0,2)) = lex(2.0,0,0)
            //   cursor[1].weight = lex(1.0,0,1).times(lex(1.0,0,1)) = lex(2.0,0,1)
            //   cursor[2].weight = lex(1.0,0,2).times(lex(1.0,0,0)) = lex(2.0,0,2)
            // (left-projection of src/rule per LexicographicWeight::times).
            // Lex-min winner: cursor[0] (rule_idx=0).
            // B6 (2026-04-28): script must end in Accept (or Error) — the
            // walker now surfaces Idle-in-non-terminal-state as Error.
            WpdsStepAction::Accept,
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 2),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            // Initial Fork.
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry first.
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        // Drive the fanout to completion. Final state is Accepted (engine
        // consumes one InfixLoop step as Accept after commit_winner).
        let final_state = w.run_to_saturation(100, &empty_tokens());
        assert_eq!(
            final_state,
            WpdsState::Accepted,
            "expected Accepted after commit_winner + Accept transition",
        );
        // The walker's terminal weight reflects the winning cursor's
        // accumulated weight, with src_idx/rule_idx left-projected from
        // cursor[0] (rule_idx=0).
        let final_weight = w.weight();
        assert_eq!(
            final_weight.rule_idx, 0,
            "expected lex-min winner (rule_idx=0) to be selected; got rule_idx={}",
            final_weight.rule_idx,
        );
        assert_eq!(final_weight.src_idx, 0);
        assert!(
            (final_weight.primary.0 - 2.0).abs() < 1e-9,
            "expected primary cost 2.0 (Push 0.0 + Fork branch 1.0 + Pop 1.0); got {}",
            final_weight.primary.0,
        );
    }

    /// Commit A: per-branch `new_state` actually distinguishes — when
    /// branches advertise different post-Fork states, each cursor's
    /// `inner_state` must reflect its own branch's `new_state`, not a
    /// shared one. Asserts before any step: cursor[i].inner_state ==
    /// branches[i].new_state.
    #[test]
    fn fork_per_branch_new_state_routes_to_distinct_states() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 7 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::InfixLoop { cur_bp: 13 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::Unwinding,
                    },
                ],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 3);
        // Each cursor's inner_state must be its own branch's new_state.
        match &cursors[0].inner_state {
            &WpdsState::PrefixDispatch { cur_bp, .. } => assert_eq!(cur_bp, 7),
            other => panic!("cursor[0]: expected PrefixDispatch{{cur_bp:7}}, got {:?}", other),
        }
        match &cursors[1].inner_state {
            &WpdsState::InfixLoop { cur_bp } => assert_eq!(cur_bp, 13),
            other => panic!("cursor[1]: expected InfixLoop{{cur_bp:13}}, got {:?}", other),
        }
        match &cursors[2].inner_state {
            WpdsState::Unwinding => {},
            other => panic!("cursor[2]: expected Unwinding, got {:?}", other),
        }
    }

    /// Commit A: `consume_trigger: true` advances `pos` by 1 before
    /// allocating cursors; cursors inherit the post-advance pos.
    #[test]
    fn fork_consume_trigger_advances_pos_once_for_all_cursors() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: true,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        assert_eq!(w.position(), 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork (consumes trigger)
        assert_eq!(w.position(), 1, "consume_trigger should advance walker pos by 1");
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 2);
        for (i, c) in cursors.iter().enumerate() {
            assert_eq!(c.pos, 1, "cursor[{}].pos should inherit post-advance pos", i);
        }
    }

    #[test]
    fn fork_all_branches_drop_yields_error() {
        // Three branches all immediately Error → step_fanout enters
        // WpdsState::Error("all fork branches dropped").
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Error("branch a failed".into()),
            WpdsStepAction::Error("branch b failed".into()),
            WpdsStepAction::Error("branch c failed".into()),
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        match final_state {
            WpdsState::Error { ref message } => {
                assert!(
                    message.contains("all fork branches dropped"),
                    "expected 'all fork branches dropped' message, got: {}",
                    message
                );
            }
            other => panic!("expected Error state, got {:?}", other),
        }
    }

    #[test]
    fn fork_multi_iter_resolves_after_advance() {
        // Three branches: each takes one Advance to InfixLoop (Resolved
        // after Advance). After step_fanout's first iteration, all three
        // become Resolved simultaneously and lex-min picks rule_idx=0.
        // B6 (2026-04-28): script must terminate in Accept; the walker
        // surfaces Idle-in-non-terminal-state as Error.
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.5, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.5, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(0.5, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        assert_eq!(final_state, WpdsState::Accepted);
        let final_weight = w.weight();
        // Advance does not modify weight; winner's weight is its branch weight only.
        assert_eq!(final_weight.rule_idx, 0);
        assert!((final_weight.primary.0 - 0.5).abs() < 1e-9);
    }

    #[test]
    fn run_to_completion_terminates_at_accept() {
        // Engine emits 3 advances then accepts.
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::Unwinding),
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let final_state = w.run_to_completion(100, &empty_tokens());
        assert_eq!(final_state, WpdsState::Accepted);
    }

    #[test]
    fn run_to_completion_respects_max_steps() {
        // Engine never accepts; run_to_completion bails after max_steps.
        let engine = ScriptedEngine::new(vec![]); // returns Idle
        let mut w = WpdsWalker::new(engine, 0);
        let final_state = w.run_to_completion(10, &empty_tokens());
        // Idle from the engine yields NoChange; we stay in Ready.
        assert_eq!(final_state, WpdsState::Ready { min_bp: 0 });
    }

    #[test]
    fn run_to_saturation_errors_on_idle_in_non_terminal_state() {
        // B6 (2026-04-28): when the engine returns Idle in a non-terminal
        // state, the walker surfaces the stall as Error rather than
        // silently exiting (which would let callers think parse "completed"
        // when it actually got stuck mid-derivation).
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let s = w.run_to_saturation(100, &empty_tokens());
        match s {
            WpdsState::Error { ref message } => {
                assert!(
                    message.contains("Idle in non-terminal state"),
                    "expected stall-Error message; got: {}",
                    message,
                );
            }
            other => panic!("expected Error after Idle in non-terminal state; got {:?}", other),
        }
    }

    #[test]
    fn run_to_saturation_terminates_at_accept_within_limit() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let s = w.run_to_saturation(10, &empty_tokens());
        assert_eq!(s, WpdsState::Accepted);
    }

    #[test]
    fn current_configuration_snapshot_captures_position_and_weight() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 0, 0, None),
            weight: lex(3.5, 1, 2),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdsWalker::new(engine, 7);
        let _ = w.process_event(WpdsEvent::TokenConsumed {
            pos: 4,
            token: TokenKind::Ident,
        }, &empty_tokens());
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cfg = w.current_configuration();
        assert_eq!(cfg.pos, 4);
        assert!((cfg.weight.primary.0 - 3.5).abs() < 1e-9);
        // Stack should contain at least the pushed symbol.
        assert!(!cfg.stack.is_empty());
    }

    #[test]
    fn walker_control_pause_variant_exists() {
        // Sanity check that the re-export works.
        let _: WalkerControl = WalkerControl::Pause;
        let _: WalkerControl = WalkerControl::Continue;
        let _: WalkerControl = WalkerControl::Checkpoint;
        let _: WalkerControl = WalkerControl::Abort;
    }

    // ─── WalkerConsumer tests (Stage 5) ─────────────────────────────────────

    #[test]
    fn null_consumer_always_continues() {
        let mut c = NullConsumer;
        let event: WpdsEvent<LexicographicWeight> = WpdsEvent::Step;
        let r = <NullConsumer as WalkerConsumer<LexicographicWeight>>::on_event(
            &mut c,
            &event,
            &WpdsState::Ready { min_bp: 0 },
        );
        assert_eq!(r, WpdsControl::Continue);
    }

    #[test]
    fn tracing_consumer_records_events_and_final_state() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker = WpdsWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let final_state = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        assert_eq!(final_state, WpdsState::Accepted);
        assert!(!consumer.events.is_empty());
        assert_eq!(consumer.final_state, Some(WpdsState::Accepted));
        // First recorded event should be the Step that drove from Ready.
        assert_eq!(consumer.events[0].0, WpdsEventTag::Step);
    }

    #[test]
    fn abort_after_consumer_halts_after_n_events() {
        let engine = ScriptedEngine::new(
            (0..50)
                .map(|i| WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: i, cur_bp: 0 }))
                .collect(),
        );
        let mut walker: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(engine, 0);
        let mut consumer = AbortAfterConsumer::new(3);
        let final_state = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        match final_state {
            WpdsState::Error { message } => assert_eq!(message, "consumer aborted"),
            other => panic!("expected Error state from abort, got {:?}", other),
        }
        assert_eq!(consumer.count, 3);
    }

    #[test]
    fn run_with_consumer_calls_on_complete_at_terminal() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Accept]);
        let mut walker = WpdsWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let _ = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        assert_eq!(consumer.final_state, Some(WpdsState::Accepted));
    }

    #[test]
    fn run_with_consumer_max_steps_reached_calls_on_complete() {
        // Engine never accepts; consumer should still receive on_complete.
        let engine = ScriptedEngine::new(vec![]);
        let mut walker: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let _ = walker.run_with_consumer(&mut consumer, 5, &empty_tokens());
        assert_eq!(consumer.final_state, Some(WpdsState::Ready { min_bp: 0 }));
    }

    /// A consumer that requests Checkpoint on every event.
    struct CheckpointEveryEvent {
        pub recorded: usize,
    }

    impl<W: Semiring> WalkerConsumer<W> for CheckpointEveryEvent {
        fn on_event(&mut self, _event: &WpdsEvent<W>, _state: &WpdsState) -> WpdsControl {
            WpdsControl::Checkpoint
        }
        fn on_checkpoint(&mut self, _config: &WpdsConfiguration<W>) {
            self.recorded += 1;
        }
    }

    #[test]
    fn checkpoint_consumer_records_per_step() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::InfixLoop { cur_bp: 0 }),
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(engine, 0);
        let mut consumer = CheckpointEveryEvent { recorded: 0 };
        let _ = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        // At least one checkpoint should be recorded per non-terminal step.
        assert!(consumer.recorded >= 2, "expected ≥2 checkpoints, got {}", consumer.recorded);
    }

    /// A consumer that pauses on the first event.
    struct PauseOnFirst {
        pub paused: bool,
    }

    impl<W: Semiring> WalkerConsumer<W> for PauseOnFirst {
        fn on_event(&mut self, _event: &WpdsEvent<W>, _state: &WpdsState) -> WpdsControl {
            if !self.paused {
                self.paused = true;
                WpdsControl::Pause
            } else {
                WpdsControl::Continue
            }
        }
    }

    #[test]
    fn pause_consumer_stops_walker_without_completion() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(engine, 0);
        let mut consumer = PauseOnFirst { paused: false };
        let s = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        // Pause should leave walker in non-terminal state, ready for resumption.
        assert!(!s.is_terminal(), "pause should not enter a terminal state");
        assert!(consumer.paused);
    }

    // ─── Phase A.2: atomic-rule plumbing integration tests ──────────────────

    /// Test engine that simulates an atomic integer-literal rule.
    ///
    /// State transitions:
    /// - `Ready` → emits `Push(CategoryEntry)` + → `PrefixDispatch`
    /// - `PrefixDispatch` + sees Integer token → `ConsumeAndPush(Return)` + → `Unwinding`
    /// - `Unwinding` + frontier is `Return` → `Pop` + → `Unwinding`
    /// - `Unwinding` + frontier is `CategoryEntry` → `Pop` + → `Accepted`
    /// - `Unwinding` + no frontier → `Accept`
    struct AtomicIntEngine;

    impl WpdsStepEngine<LexicographicWeight> for AtomicIntEngine {
        fn step(
            &self,
            state: &WpdsState,
            _gss: &WpdsGss<LexicographicWeight>,
            frontier_top: Option<&WpdsGssNode>,
            _pos: usize,
            tokens: &dyn WpdsTokenSource,
        ) -> WpdsStepAction<LexicographicWeight> {
            match state {
                WpdsState::Ready { min_bp } => WpdsStepAction::Push {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: LexicographicWeight::from_cost(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch {
                        pos: 0,
                        cur_bp: *min_bp,
                    },
                },
                WpdsState::PrefixDispatch { pos, cur_bp } => {
                    if let Some(TokenKind::Integer) = tokens.peek_kind(*pos) {
                        WpdsStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::rule_at(0, 0, 0, None)
                                .with_kind_return(),
                            weight: LexicographicWeight::from_cost(0.0, 0, 0),
                            new_state: WpdsState::Unwinding,
                            capture_token: true,
                        }
                    } else {
                        let _ = cur_bp;
                        WpdsStepAction::Error("expected Integer".into())
                    }
                }
                WpdsState::Unwinding => match frontier_top.map(|n| n.symbol.kind) {
                    Some(SymbolKind::Return) => WpdsStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::Unwinding,
                    },
                    Some(SymbolKind::CategoryEntry) => WpdsStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::Accepted,
                    },
                    _ => WpdsStepAction::Idle,
                },
                _ => WpdsStepAction::Idle,
            }
        }

        fn action_for(&self, src_idx: u16, rule_idx: u16) -> Option<&ActionEntry> {
            fn int_lit_action(b: &mut SemanticBuilder, args: Vec<ActionArg>) {
                // Pop the captured token, parse its text, push the parsed i64.
                let arg = args.into_iter().next().expect("arity 1");
                let text = arg.as_token_text().unwrap_or("0");
                let parsed: i64 = text.parse().unwrap_or(0);
                b.push_term::<i64>(parsed);
            }
            static ACTION: ActionEntry = ActionEntry {
                action_fn: int_lit_action,
                arity: 1,
            };
            if src_idx == 0 && rule_idx == 0 {
                Some(&ACTION)
            } else {
                None
            }
        }
    }

    use crate::wpds_runtime::{ActionArg, ActionEntry, SemanticBuilder, SliceTokenSource};

    #[test]
    fn atomic_int_literal_parses_end_to_end() {
        let tokens = [TokenKind::Integer];
        let texts = ["42"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let mut walker: WpdsWalker<LexicographicWeight, _> =
            WpdsWalker::new(AtomicIntEngine, 0);
        let final_state = walker.run_to_saturation(50, &token_src);
        assert_eq!(final_state, WpdsState::Accepted, "walker reaches Accepted");
        // The semantic action should have left i64(42) on the builder.
        let result: Option<i64> = walker.builder_mut().take_result();
        assert_eq!(result, Some(42));
        // Position should have advanced past the literal.
        assert_eq!(walker.position(), 1);
    }

    #[test]
    fn atomic_int_engine_on_non_integer_token_errors() {
        let tokens = [TokenKind::Ident];
        let texts = ["foo"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let mut walker: WpdsWalker<LexicographicWeight, _> =
            WpdsWalker::new(AtomicIntEngine, 0);
        let final_state = walker.run_to_saturation(50, &token_src);
        match final_state {
            WpdsState::Error { message } => assert!(message.contains("expected Integer")),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // Option A cleanup tests (2026-04-28)
    //
    // Locks down the principled fanout-state-machine contract:
    // - nested Fork via CursorOutcome::ForkInto
    // - cursor-local collection_stack lifecycle
    // - delta replay ordering
    // - PushPredicate Arc clone semantics
    // - commit_winner terminal-state guard
    // ─────────────────────────────────────────────────────────────────────

    /// Engine that returns a collection-aware action table for tests 2 & 3.
    /// `(0,0)` is the element rule (arity 0, pushes a sentinel Term).
    /// `(1,0)` is the collection-finalize rule (arity 1, drains accumulator
    /// 0 and pushes Term<usize> with the drained count).
    struct CollAwareScriptedEngine {
        script: RefCell<Vec<WpdsStepAction<LexicographicWeight>>>,
    }

    impl CollAwareScriptedEngine {
        fn new(actions: Vec<WpdsStepAction<LexicographicWeight>>) -> Self {
            Self { script: RefCell::new(actions) }
        }
    }

    fn coll_elem_action(
        b: &mut crate::wpds_runtime::SemanticBuilder,
        _args: Vec<crate::wpds_runtime::ActionArg>,
    ) {
        b.push_term::<i64>(7);
    }

    fn coll_finalize_action(
        b: &mut crate::wpds_runtime::SemanticBuilder,
        args: Vec<crate::wpds_runtime::ActionArg>,
    ) {
        let id = args
            .first()
            .and_then(|a| match a {
                crate::wpds_runtime::ActionArg::CollectionId(id) => Some(*id),
                _ => None,
            })
            .unwrap_or(0);
        let drained = b.drain_collection(id);
        let n = drained.len();
        b.push_term::<usize>(n);
    }

    static COLL_ELEM_ENTRY: ActionEntry = ActionEntry {
        action_fn: coll_elem_action,
        arity: 0,
    };
    static COLL_FINALIZE_ENTRY: ActionEntry = ActionEntry {
        action_fn: coll_finalize_action,
        arity: 1,
    };

    impl WpdsStepEngine<LexicographicWeight> for CollAwareScriptedEngine {
        fn step(
            &self,
            _state: &WpdsState,
            _gss: &WpdsGss<LexicographicWeight>,
            _frontier_top: Option<&WpdsGssNode>,
            _pos: usize,
            _tokens: &dyn WpdsTokenSource,
        ) -> WpdsStepAction<LexicographicWeight> {
            self.script.borrow_mut().pop().unwrap_or(WpdsStepAction::Idle)
        }
        fn action_for(&self, src_idx: u16, rule_idx: u16) -> Option<&ActionEntry> {
            match (src_idx, rule_idx) {
                (0, 0) => Some(&COLL_ELEM_ENTRY),
                (1, 0) => Some(&COLL_FINALIZE_ENTRY),
                _ => None,
            }
        }
    }

    /// Cleanup: nested Fork resolves to lex-min grandchild winner.
    /// Outer Fork(2) — each branch's new_state = PrefixDispatch so the
    /// engine drives them again to emit the inner Fork. Inner Fork(2)
    /// per outer branch produces 4 grandchildren; each Pops to InfixLoop.
    /// Lex-min by rule_idx picks the lowest grandchild weight.
    #[test]
    fn nested_fork_resolves_to_lex_min_grandchild() {
        let engine = ScriptedEngine::new(vec![
            // B6: terminate cleanly via Accept after the surviving cursor's
            // commit_winner reaches InfixLoop.
            WpdsStepAction::Accept,
            // Pops for 4 grandchildren (LIFO: last popped first).
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 3),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 2),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            // Inner Fork for outer cursor B.
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 3, 0, None),
                        weight: lex(1.0, 0, 3),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Inner Fork for outer cursor A.
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Outer Fork.
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry.
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // outer Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        assert_eq!(final_state, WpdsState::Accepted);
        assert_eq!(
            w.weight().rule_idx, 0,
            "expected lex-min grandchild (rule_idx=0) to win",
        );
    }

    /// Cleanup 1 + Option A core: a Fork branch opens an empty collection
    /// via `Push(CollectionMarker)`, pops via `ConsumeAndPop` firing the
    /// finalize action that drains accumulator 0. The cursor-local id
    /// allocation, donate-en-bloc, and finalize replay should produce
    /// `Term<usize>(0)` in the live builder.
    #[test]
    fn cursor_local_collection_open_push_close() {
        let coll_marker = StackSymbolV2::collection_marker(1, 0, 0);
        let engine = CollAwareScriptedEngine::new(vec![
            // B6: terminate cleanly via Accept after the Pop reaches InfixLoop.
            WpdsStepAction::Accept,
            // Step 3: ConsumeAndPop CollectionMarker -> InfixLoop (Resolved).
            // Cursor pops the marker, logs FireAction(coll_marker_symbol),
            // SpliceIntoCollection (no-op since pred is CategoryEntry, not
            // a marker — actually no splice here).
            WpdsStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            // Step 2: Fork branch's first action — Push(CollectionMarker).
            //
            // Wait — the Fork branch's `symbol` is itself the CollectionMarker.
            // The Fork action allocates the GSS node and triggers cursor-local
            // id allocation IF the branch.symbol is a CollectionMarker.
            //
            // But cursor-local id allocation lives in apply_action_to_cursor's
            // Push and ConsumeAndPush arms — NOT in apply_action::Fork. So
            // putting the CollectionMarker as the Fork branch's symbol skips
            // the id-allocation path. We'd need a separate Push step inside
            // the cursor.
            //
            // Restructure: outer Fork pushes a non-marker symbol, branch
            // transitions to PrefixDispatch, engine emits Push(CollectionMarker)
            // — this exercises apply_action_to_cursor::Push's marker arm.
            WpdsStepAction::Push {
                symbol: coll_marker,
                weight: lex(0.0, 1, 0),
                new_state: WpdsState::Unwinding,
            },
            // Step 1: Single-branch Fork.
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                }],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        assert_eq!(final_state, WpdsState::Accepted);
        // Finalize action drained id=0 (empty) and pushed Term<usize>(0).
        let result: Option<usize> = w.builder_mut().take_result();
        assert_eq!(
            result,
            Some(0),
            "expected drain_collection(0) to yield 0 elements",
        );
    }

    /// Cleanup 4: nested Fork while a cursor has opened a collection (but
    /// not yet pushed elements). Verifies `BranchCursor::clone` succeeds —
    /// the empty `collection_stack` debug_assert holds.
    #[test]
    fn cursor_local_collection_in_nested_fork() {
        let coll_marker = StackSymbolV2::collection_marker(1, 0, 0);
        let engine = CollAwareScriptedEngine::new(vec![
            // Step 4: pops for 2 grandchildren (LIFO).
            WpdsStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            // Step 3: outer cursor's inner Fork (after collection open).
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            // Step 2: outer cursor opens collection.
            WpdsStepAction::Push {
                symbol: coll_marker,
                weight: lex(0.0, 1, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
            // Step 1: outer Fork (single branch to focus the test).
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                }],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // outer Fork
        // Drive — must NOT panic on collection_stack debug_assert during
        // the nested Fork's clone path. (The cursor opened a collection
        // but accumulator 0 is empty when the inner Fork fires.)
        let final_state = w.run_to_saturation(100, &empty_tokens());
        assert!(
            !matches!(final_state, WpdsState::AmbiguityFanout { .. }),
            "fanout must resolve; got {:?}",
            final_state,
        );
    }

    /// Cleanup 4: a losing branch's pending_builder_ops must NOT replay
    /// against the live builder. Two branches each `ConsumeAndPush` with
    /// `capture_token: true` + Pop. Lex-min picks rule_idx=0; the live
    /// builder has exactly ONE captured token (loser's PushToken delta
    /// is dropped with the cursor).
    #[test]
    fn losing_branch_with_deltas_no_live_side_effect() {
        let token_kinds = [TokenKind::Integer, TokenKind::Integer];
        let token_texts = ["42", "99"];
        let token_src = crate::wpds_runtime::SliceTokenSource::with_texts(
            &token_kinds,
            &token_texts,
        );
        let engine = ScriptedEngine::new(vec![
            // Pops for 2 cursors (LIFO).
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            // ConsumeAndPush for cursor B (capture_token: true → logs PushToken).
            WpdsStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(0, 1, 0, None).with_kind_return(),
                weight: lex(1.0, 0, 1),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                capture_token: true,
            },
            // ConsumeAndPush for cursor A (winner).
            WpdsStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(0, 0, 0, None).with_kind_return(),
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                capture_token: true,
            },
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    },
                ],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &token_src); // entry
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Fork
        let _ = w.run_to_saturation(100, &token_src);
        // Builder stack has exactly ONE arg (the winner's captured token).
        // If the loser's delta replayed, builder.len() would be 2.
        assert_eq!(
            w.builder().len(),
            1,
            "loser's PushToken delta must NOT replay; expected 1 arg, got {}",
            w.builder().len(),
        );
    }

    /// Cleanup 4: `BranchCursor::clone()` must succeed when
    /// `pending_builder_ops` contains a `PushPredicate(Arc<dyn Any>)`.
    /// This is a mechanical check — pre-cleanup the clone would panic
    /// via `clone_non_predicate`'s explicit panic on PushPredicate.
    #[test]
    fn predicate_in_fork_branch_clone_path() {
        use crate::behavioral_pred::BehavioralPred;
        let cursor: BranchCursor<LexicographicWeight> = BranchCursor {
            node: 0,
            pos: 0,
            weight: lex(1.0, 0, 0),
            inner_state: WpdsState::InfixLoop { cur_bp: 0 },
            pending_builder_ops: vec![BuilderDelta::PushPredicate(
                Arc::new(BehavioralPred::Top) as Arc<dyn std::any::Any + Send + Sync>,
            )],
            collection_stack: Vec::new(),
        };
        let cloned = cursor.clone();
        assert_eq!(cloned.pending_builder_ops.len(), 1);
        assert!(
            matches!(&cloned.pending_builder_ops[0], BuilderDelta::PushPredicate(_)),
            "cloned cursor must carry PushPredicate variant",
        );
    }

    /// Cleanup 3: a `FireAction` delta whose action arity exceeds the
    /// builder stack must leave the walker in `Error` state — the
    /// post-loop install must NOT silently overwrite with
    /// `winner.inner_state` (which would mask the engine arity bug).
    #[test]
    fn commit_winner_state_overwrite_on_action_arity_underflow() {
        struct ArityBugScriptedEngine {
            script: RefCell<Vec<WpdsStepAction<LexicographicWeight>>>,
        }
        fn underflow_action(
            _b: &mut crate::wpds_runtime::SemanticBuilder,
            _args: Vec<crate::wpds_runtime::ActionArg>,
        ) {
            // Unreachable: pop_args(arity=5) underflows on empty builder
            // BEFORE we get here, setting state = Error.
        }
        static UNDERFLOW_ENTRY: ActionEntry = ActionEntry {
            action_fn: underflow_action,
            arity: 5,
        };
        impl WpdsStepEngine<LexicographicWeight> for ArityBugScriptedEngine {
            fn step(
                &self,
                _state: &WpdsState,
                _gss: &WpdsGss<LexicographicWeight>,
                _frontier_top: Option<&WpdsGssNode>,
                _pos: usize,
                _tokens: &dyn WpdsTokenSource,
            ) -> WpdsStepAction<LexicographicWeight> {
                self.script
                    .borrow_mut()
                    .pop()
                    .unwrap_or(WpdsStepAction::Idle)
            }
            fn action_for(&self, src_idx: u16, rule_idx: u16) -> Option<&ActionEntry> {
                if src_idx == 0 && rule_idx == 0 {
                    Some(&UNDERFLOW_ENTRY)
                } else {
                    None
                }
            }
        }
        let engine = ArityBugScriptedEngine {
            script: RefCell::new(vec![
                // Pop the Return symbol → cursor logs FireAction. On replay,
                // fire_action_for sees arity=5 against empty builder → sets
                // state = Error.
                WpdsStepAction::Pop {
                    weight: lex(1.0, 0, 0),
                    new_state: WpdsState::InfixLoop { cur_bp: 0 },
                },
                WpdsStepAction::Fork {
                    branches: vec![ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None).with_kind_return(),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    }],
                    consume_trigger: false,
                },
                WpdsStepAction::Push {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                },
            ]),
        };
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        // Cleanup 3: state MUST remain Error, NOT be overwritten by InfixLoop.
        match final_state {
            WpdsState::Error { ref message } => {
                assert!(
                    message.contains("arity") || message.contains("under"),
                    "expected arity-mismatch error; got: {}",
                    message,
                );
            }
            other => panic!(
                "expected Error after arity underflow; got {:?}",
                other,
            ),
        }
    }
}
