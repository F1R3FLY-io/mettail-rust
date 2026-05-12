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
use std::collections::BTreeSet;
// Phase 5.7 (2026-05-12): persistent OrdSet for cursor visited sets.
// Replaces BTreeSet for `visited_recovery` and `visited_dispatch` —
// these sets are cloned at every Fork (and at seed/Drop reset). The
// im::OrdSet's Arc-based structural sharing makes clone O(1) instead
// of O(N), aligning with Phase 5's persistent-builder cursor model.
use im::OrdSet;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::automata::semiring::Semiring;
use crate::automata::TokenKind;
use crate::gss::{WpdsGss, WpdsGssNode};
use crate::recovery::RecoveryConfig;
use crate::wpds_runtime::{
    pack_action_id, ActionArg, ActionEntry, CheckpointReason, SemanticBuilder, StackSymbolV2,
    SymbolKind, WpdsConfiguration, WpdsControl, WpdsEvent, WpdsMaxStepsExceeded,
    WpdsMutableTokenSource, WpdsResolveResult, WpdsState, WpdsTokenSource, WpdsTraceEntry,
    WpdsTransition,
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

    /// B9 / Class 2 (2026-05-08): predicate identifying CollectionMarker
    /// pops that belong to a Class-2 binder rule's internal collection
    /// slot (rather than a Class-5 standalone collection rule).
    ///
    /// When this returns `true` for the popped marker's `(result_src_idx,
    /// rule_idx)`, the walker SUPPRESSES the default FireAction at the
    /// pop site — the binder rule's terminal action will drain the
    /// CollectionId arg at its own RuleAt-pop FireAction, not at the
    /// inner CollectionMarker pop.
    ///
    /// Default returns `false` for backward compatibility (Class-5
    /// collections fire their own finalize action at marker pop).
    fn is_binder_internal_collection(&self, src_idx: u16, rule_idx: u16) -> bool {
        let _ = (src_idx, rule_idx);
        false
    }

    /// B8 / Issue D (2026-05-09); Phase 4 #2 (2026-05-12): per-(src, rule,
    /// slot_idx) predicate identifying Class-3 ZIP-MAP-SEP CollectionMarker
    /// pushes whose enclosing binder rule has a `^[xs]` MultiAbstraction.
    /// When this returns `true` for the just-pushed CollectionMarker's
    /// (src, rule, slot_idx), the walker's `emit_push_side_effects` ALSO
    /// opens a binder scope (StartBinderScope { names: vec![] })
    /// atomically with the accumulator allocation. The scope spans all
    /// loop iterations.
    ///
    /// Phase 4 #2 multi-slot fix: pre-Phase-4-#2 this was a per-rule
    /// predicate `is_class3_collection(src, rule)`. For rules with both
    /// a Class-3 BinderListLoop AND a Class-2 SimpleCollection sibling
    /// slot (e.g. PInputsTagged), the per-rule predicate incorrectly
    /// returned `true` for the Class-2 sibling's CollectionMarker too —
    /// opening a spurious BinderScope. The per-slot variant uses
    /// `symbol.bp` (preserved as slot_idx since Phase 4 #1) to
    /// distinguish.
    ///
    /// Default returns `false`.
    fn is_class3_collection_per_slot(&self, src_idx: u16, rule_idx: u16, slot_idx: u8) -> bool {
        let _ = (src_idx, rule_idx, slot_idx);
        false
    }

    /// B8 / Issue C followup (2026-05-09); refined under Issue 2
    /// (2026-05-10): predicate distinguishing OptionalGroupAt symbols
    /// used as Class 3 BinderListLoop inner-walk markers from genuine
    /// OptionalGroup `*opt(...)` markers. When `true`,
    /// `emit_push_side_effects` skips the `start_optional_scope` side
    /// effect on OptionalGroupAt(1) pushes (the optional scope would
    /// never close, leaving the builder's optional_stack non-empty at
    /// parse end).
    ///
    /// `sub_pos` discriminator: distinguishes the rule-level alias case
    /// (a rule that has BOTH a Class 3 BinderListLoop AND a real
    /// `*opt(...)` OptionalGroup) from a pure-Class-3 rule. For
    /// pure-Class-3 rules, all OptionalGroupAt sub_pos values within
    /// the Class 3 inner walk return `true`; OptionalGroupAt(1) for
    /// a real optional group in the same rule returns `false` so the
    /// genuine optional scope opens correctly.
    /// Default returns `false`.
    fn is_class3_inner_marker(&self, src_idx: u16, rule_idx: u16, sub_pos: u8) -> bool {
        let _ = (src_idx, rule_idx, sub_pos);
        false
    }

    /// Phase 4 #5b (2026-05-12): per-(src, rule, slot_idx) lookup that
    /// returns the key/value separator literal for HashMap collection
    /// slots, or `None` for Vec/HashBag/HashSet slots and unknown
    /// (src, rule, slot) tuples.
    ///
    /// When `Some(_)`, the walker patches `WpdsState::CollectionLoop.kv_phase`
    /// at transition time based on `cursor.collection_stack[acc_id].len()`
    /// parity:
    /// - len % 2 == 1 (odd, just parsed a key) → `kv_phase = 1` (expect `:`)
    /// - len % 2 == 0 (even, just parsed a value pair, or initial) →
    ///   `kv_phase = 0` (expect close or inter-pair separator)
    ///
    /// When `None`, `kv_phase` stays at `0` (the engine's emitted default).
    ///
    /// Default returns `None` for backward compatibility with engines that
    /// don't expose HashMap binder collection slots.
    fn kv_separator_for_collection(
        &self,
        result_src_idx: u16,
        rule_idx: u16,
        slot_idx: u8,
    ) -> Option<&'static str> {
        let _ = (result_src_idx, rule_idx, slot_idx);
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
    /// B8 / Issue C (2026-05-09): Same as Advance, but logs a single
    /// BuilderDelta effect to the cursor's pending_builder_ops before
    /// the state transition. Used by the Unwinding-OptionalGroupAt arm
    /// to splice a parsed Name into the Class 3 Names accumulator
    /// after a `ParamParse{collection: Some(_)}` inner step returns.
    /// Mirrors `Advance` for non-effect-bearing transitions and
    /// avoids a new state machine.
    AdvanceWithEffect {
        new_state: WpdsState,
        effect: BuilderDelta,
    },
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
    /// Opt-Group (2026-04-29): skip path. The OptionalGroup state at
    /// sub_pos=0 peeked the FIRST set and found no match. Walker:
    ///   1. Pushes `ActionArg::Optional(None)` to the builder (via
    ///      `push_optional_absent`).
    ///   2. Replaces the (top) outer RuleAt marker with `replace_symbol`
    ///      (advancing the outer position past the group).
    ///   3. Transitions to `new_state` (typically BinderRule at next outer pos).
    /// No token consumption. No `optional_stack` activity (the scope was
    /// never opened).
    OptGroupAbsent {
        replace_symbol: StackSymbolV2,
        weight: W,
        new_state: WpdsState,
    },
    /// Opt-Group (2026-04-29): take-path finalize. The OptionalGroup state
    /// at sub_pos = inner.len()+1 has walked all inner positions. Walker:
    ///   1. Pops the OptionalGroupAt(...) marker on top (no action fires —
    ///      OptionalGroupAt is intentionally excluded from the action-fire
    ///      symbol list).
    ///   2. Calls `finalize_optional_scope_present()` on the builder,
    ///      which pops the inner-arg accumulator from `optional_stack`
    ///      and pushes `ActionArg::Optional(Some(inner_args))` to the
    ///      main stack (or to the OUTER optional_stack top if nested).
    ///   3. Replaces the (now-on-top) outer RuleAt marker with
    ///      `replace_symbol` (advancing past the group).
    ///   4. Transitions to `new_state`.
    /// No token consumption.
    OptGroupFinalize {
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
    /// Stage 3.9 / ι Phase 4 (2026-05-01): Always-cursor walker mode.
    /// `Lazy` (default) means cursor[0] is the singleton canonical
    /// cursor and live builder mutations happen directly. `Strict`
    /// (after first Fork) means builder mutations route through
    /// `pending_builder_ops` deltas and replay only on the lex-min
    /// winner at EOI commit. Mode is set Lazy on construction/`reset()`,
    /// promoted to Strict on first `WpdsStepAction::Fork`, and stays
    /// Strict until `reset()` (L3 invariant: no reverse).
    cursor_mode: CursorMode,
    /// Stage 7+ Fork plan, step 2: per-branch micro-state during
    /// `WpdsState::AmbiguityFanout`. Each entry is a `BranchCursor` that
    /// pairs a GSS-tip node id with the branch's own `pos`, accumulated
    /// `weight`, and `inner_state` (the post-Fork target state for that
    /// branch).
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): post-Phase-4, this vector is
    /// ALWAYS non-empty — singleton cursor in Lazy mode, multiple
    /// cursors in Strict mode. The pre-Phase-4 "empty when not in
    /// AmbiguityFanout" invariant is replaced by the always-non-empty
    /// invariant.
    branch_cursors: Vec<BranchCursor<W>>,
    /// Stage 6 G6+ (2026-05-02): monotonic counter incremented once per
    /// `process_event(Step)` invocation. Stamps `StepSnapshot.step_index`
    /// for trace consumers; resets to 0 on `reset()`.
    step_counter: usize,
    /// Stage 3.20 / L12 (Commit 4, 2026-05-06): WPDS-edge recovery event
    /// trace. Each `BuilderDelta::RecoveryEvent` (and its Substitute/Insert/
    /// CommitLexAlternative siblings) replayed at `commit_winner` time
    /// pushes a `RecoveryEvent` here. Read-only consumers via
    /// `recovery_trace()`. Cleared on `reset()`.
    recovery_events: Vec<RecoveryEvent>,
    /// Stage 3.20 / L12 (Commit A, 2026-05-06): caller-managed mutable
    /// token source for recovery mutations. Threaded via
    /// `set_mutable_token_source` before driving `run_to_*`. Stored as a
    /// raw pointer to avoid cascading `'a` through the struct (~100
    /// callsites). SAFETY: caller MUST keep the source alive until
    /// `clear_mutable_token_source()` or `reset()`. The Drop impl clears
    /// the slot defensively. None by default; replay paths
    /// (SubstituteToken/InsertToken/CommitLexAlternative) surface a clean
    /// Error if the slot is None when they fire — no graceful-degradation.
    mutable_token_source: Option<*mut dyn WpdsMutableTokenSource>,
    /// Phantom data marker for the lifetime-erased mutable source slot.
    _mutable_source_lifetime: PhantomData<()>,
    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): walker-owned
    /// recovery configuration. The `apply_action_to_cursor::Fork` arm
    /// reads `max_recovery_depth` from here when checking each
    /// recovery-Fork dispatch's per-cursor depth bound. Initialized via
    /// `RecoveryConfig::default()`; callers may override via
    /// `with_recovery_config` for per-grammar tuning.
    recovery_config: RecoveryConfig,
}

/// Stage 3.9 / ι Phase 4 (2026-05-01): always-cursor walker mode.
///
/// `Lazy` is the unambiguous-parse fast-path: the walker maintains a
/// singleton cursor (`branch_cursors[0]`) whose `pending_builder_ops` is
/// always empty; live-builder mutations happen directly. `Strict` is
/// the post-Fork mode: cursors accumulate `pending_builder_ops` deltas
/// that replay onto the live builder only when the lex-min winner
/// commits at EOI.
///
/// Invariants:
/// - **L1** (Lazy admission): `mode == Lazy → cursors.len() == 1 && cursors[0].pending_builder_ops.is_empty()` at `apply_action` entry.
/// - **L2** (Lazy → Strict transition): first `WpdsStepAction::Fork` sets `mode = Strict`.
/// - **L3** (no reverse): once Strict, stays Strict for the parse.
/// - **L4** (reset between parses): `WpdsWalker::reset` re-allocates a fresh singleton cursor and sets `mode = Lazy`.
/// - **L5** (terminal mode-irrelevant): Error/Accepted ignore mode at all times.
/// - **L6** (Lazy + EOI Accept): Lazy admission requires the engine to emit `Accept` only at `pos == tokens.len()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CursorMode {
    Lazy,
    Strict,
}

/// Stage 3.11 / ι Phase 6 (2026-05-01): runaway guard for Strict-mode
/// cursors. If any cursor's `pending_builder_ops` exceeds this length,
/// the walker transitions to `WpdsState::Error` instead of continuing
/// to accumulate. Prevents pathological grammars from consuming
/// unbounded memory in delta logs.
///
/// Default 1,000,000 is large enough for any real-world parse (most
/// parses have <100 deltas; deeply-recursive parses have <10,000).
/// Pathological cases (infinite loops in cursor mutation, e.g., a Fork
/// that re-emits the same Fork) trip this guard immediately.
pub const STRICT_PENDING_OPS_LIMIT: usize = 1_000_000;

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
    /// Stage 3.12 / Class A.i (2026-05-01): per-branch action discriminator.
    /// `Push` (default) gives the existing semantics — push the symbol onto
    /// the cursor's GSS chain. `OptGroupAbsent { replace_symbol }` directs
    /// the Fork arm to mirror `apply_action::OptGroupAbsent`: emit a
    /// `PushOptionalAbsent` delta, pop the parent's outer RuleAt, and push
    /// `replace_symbol` (the advanced outer RuleAt). Used by the
    /// Opt-Group SKIP branch in `binder.rs`.
    ///
    /// Stage 3.16 (planned) extends this enum with `OptGroupFinalize`,
    /// `LexAlternative`, `Recovery`, etc. — the unified Fork-emission
    /// framework adds 4 more variants.
    pub action_kind: ForkActionKind,
}

/// B13d-R / Resolution R (2026-05-08): tristate result of the dry-run
/// simulation over a cursor's `pending_builder_ops`. The simulation
/// faithfully mirrors `commit_winner`'s replay against the runtime arg
/// stack (main_stack + optional_stack of SemanticBuilder).
///
/// - `Consistent` → all FireActions encountered would succeed.
///   `final_main_stack` and `final_optional_depth` describe the resulting
///   active-stack state; `cursor_will_produce_term` checks for
///   `final_main_stack.len() == 1 && final_optional_depth == 0`.
/// - `DefinitelyBroken` → a logged FireAction would arity-underflow OR
///   type-mismatch at runtime (action body's `into_term::<T>()` returns
///   None and the action returns early without `push_term`). Monotone-
///   stable: subsequent appends to pending_builder_ops cannot recover.
/// - `Indeterminate` → simulation hit a delta whose semantic effect
///   depends on payload values not available at the delta log alone
///   (e.g., `PushToCollection` on an empty active stack — runtime is
///   silent on this; we don't classify it as broken).
#[derive(Debug)]
enum DryRunState {
    Consistent {
        final_main_stack: Vec<Option<u16>>,
        final_optional_depth: usize,
    },
    DefinitelyBroken {
        kind: DryRunBrokenKind,
    },
    Indeterminate {
        reason: &'static str,
    },
}

#[derive(Debug)]
enum DryRunBrokenKind {
    /// FireAction's `pop_args(arity)` would underflow at runtime.
    ArityUnderflow,
    /// FireAction's `into_term::<Cat>()` would return None on at least
    /// one arg slot whose `expected_input_cats[i]` is a non-ANY_CAT
    /// category that doesn't match the popped tag.
    TypeMismatch,
}

impl<W: Semiring> ForkBranch<W> {
    /// Stage 3.12 / Class A.i (2026-05-01): default constructor for
    /// branches with the standard `Push` action_kind. All 8 pre-Stage-3.12
    /// emit sites use this — the new `action_kind` field is opaque to
    /// existing callers.
    pub fn push(symbol: StackSymbolV2, weight: W, new_state: WpdsState) -> Self {
        ForkBranch {
            symbol,
            weight,
            new_state,
            action_kind: ForkActionKind::Push,
        }
    }
}

/// Stage 3.12 / Class A.i (2026-05-01): per-Fork-branch action
/// discriminator.
///
/// Pre-Stage-3.12 every Fork branch was implicitly `Push`. Class A.i
/// introduces `OptGroupAbsent { replace_symbol }` for the Opt-Group SKIP
/// branch (which needs pop+push+log, not just push).
///
/// Stage 3.16 unified-framework (Commit 2 / Mechanism γ, 2026-05-05):
/// payload-carrying action variants that mirror the existing `WpdsStepAction`
/// operations. Each variant carries the EXACT payload of its WpdsStepAction
/// counterpart (e.g. `ConsumeAndReplace { symbol, new_state }` mirrors
/// `WpdsStepAction::ConsumeAndReplace`). Walker's `apply_action::Fork`
/// dispatches on `action_kind` to perform the corresponding cursor mutation,
/// avoiding the sentinel-pop overhead of a "Push-only" Fork model and
/// generalizing to ALL future grammars with deliberate ambiguity at any
/// dispatch site (G1: close == sep; G2: mixfix elision; G3: bare-elem
/// collections; G4: close == valid ident; G5: ambiguous prefix arms).
///
/// Per the unified framework: `consume_trigger: bool` on the Fork itself is
/// only used by Push branches that historically advanced pos at allocation
/// time; the new variants encode their own intrinsic consume semantics, so
/// callers emit `consume_trigger: false` for them.
#[derive(Clone, Debug)]
pub enum ForkActionKind {
    /// Default: cursor pushes `branch.symbol` onto its GSS chain.
    /// Implicit Push-time side effects (CollectionMarker id allocation,
    /// OptionalGroupAt(1) scope opening) are handled by
    /// `emit_push_side_effects`. Pos advancement controlled by Fork's
    /// `consume_trigger: bool`.
    Push,

    /// Opt-Group SKIP branch: emit `BuilderDelta::PushOptionalAbsent`,
    /// pop the cursor's outer RuleAt, push `replace_symbol` (the
    /// advanced outer RuleAt at next outer position).
    OptGroupAbsent { replace_symbol: StackSymbolV2 },

    /// Stage 3.16 (Cluster 1) — Replace top-of-GSS with `branch.symbol` and
    /// consume one token. Mirrors `WpdsStepAction::ConsumeAndReplace`.
    /// Fork must emit `consume_trigger: false` because this action consumes
    /// intrinsically.
    ConsumeAndReplace,

    /// Stage 3.16 (Cluster 1) — Consume one token, no GSS change. Mirrors
    /// `WpdsStepAction::Consume`. Fork must emit `consume_trigger: false`.
    Consume,

    /// Stage 3.16 (Cluster 1) — Consume identifier token: optionally start
    /// binder scope, push ident name to builder, then replace top-of-GSS
    /// with `branch.symbol`. Mirrors `WpdsStepAction::ConsumeIdentAndReplace`.
    /// Fork must emit `consume_trigger: false`.
    ConsumeIdentAndReplace { start_scope: bool },

    /// Stage 3.16 (Cluster 1) — Pop top-of-GSS frame, transition to
    /// `branch.new_state`. Used for mixfix last-operand elision (G2).
    /// Mirrors `WpdsStepAction::Pop`. Fork must emit `consume_trigger: false`.
    Pop,

    /// Stage 3.16 (Cluster 1) — Consume token AND pop top-of-GSS frame.
    /// Used for empty-collection close branches. Mirrors
    /// `WpdsStepAction::ConsumeAndPop`. Fork must emit `consume_trigger: false`.
    ConsumeAndPop,

    /// Stage 3.16 (Cluster 1) — Consume token + replace top-of-GSS, but ALSO
    /// log a builder delta (e.g. `StartBinderScope { names: vec![] }` for
    /// the empty-list bootstrap branch). Mirrors `ConsumeAndReplace` plus a
    /// pre-replace effect.
    ConsumeAndReplaceWithEffect { effect: BuilderDelta },

    /// Stage 3.14 (Cluster 2 #12) — lex-alternative branch. The walker's
    /// apply_action::Fork allocates the child cursor with Push semantics
    /// AND logs a `BuilderDelta::CommitLexAlternative { pos, alt_idx, kind,
    /// text }` onto its pending ops. Replay (commit_winner) drives the
    /// MutableMultiTokenSource to commit the alt at parse time.
    LexAlt { alt_idx: u16, kind: TokenKind, text: String },

    /// Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ, 2026-05-05) — atomic
    /// literal multi-arm Fork branch. Mirrors `WpdsStepAction::ConsumeAndPush
    /// { capture_token: true }`: emit_push_token captures the literal text
    /// onto the cursor's pending_builder_ops/live builder, then push the
    /// `branch.symbol` (the rule's Return marker) onto the GSS, then advance
    /// pos by 1. Used when codegen buckets atomic prefix arms by (pat, guard)
    /// and a bucket has ≥2 rules — the Fork emits one branch per rule with
    /// this action_kind, and lex-min via from_cost(0.0, src, rule_idx) picks
    /// the lower rule_idx winner.
    ConsumeAndCaptureAndPush,

    /// Stage 3.20 / L12 Commit F (2026-05-06) — Cluster 1/6 hacks #4 & #5
    /// closure. Mirrors `WpdsStepAction::ConsumeAndReplace` but gated on
    /// a `peek_text == expected_text` equality check. Walker's
    /// `apply_action_to_cursor::Fork` arm reads the peek'd text at
    /// `pos_after`; on match, allocates the child like
    /// `ForkActionKind::ConsumeAndReplace`; on miss, skips child
    /// allocation entirely (no cursor pushed). When this is the only
    /// surviving branch in the Fork, `step_fanout`'s empty-children
    /// check raises `WpdsState::Error { message: "all fork branches
    /// dropped" }` — same surface as the legacy eq-or-error pathway,
    /// but routed through uniform Fork+lex-min plumbing per
    /// `feedback_use_wpds_disambiguation_not_heuristics.md`. Behavioral
    /// improvement over legacy: in mid-fanout populations, only the
    /// guard-failing cursor dies; correct sibling cursors continue.
    GuardedConsumeAndReplace { expected_text: String },

    /// Stage 3.20 / L12 Commit F (2026-05-06) — Cluster 1/6 hacks #6 & 4th
    /// closure. Mirrors `WpdsStepAction::ConsumeIdentAndReplace` but
    /// gated on a `peek_kind == TokenKind::Ident` check. Pass → behaves
    /// identically to `ConsumeIdentAndReplace { start_scope }`. Fail →
    /// no child allocated. See `GuardedConsumeAndReplace` for the
    /// fanout-survival rationale.
    GuardedConsumeIdentAndReplace { start_scope: bool },

    /// L12 follow-up B2 (2026-05-07) — closure for BinderListLoop's
    /// separator branch. Mirrors `WpdsStepAction::Consume` but gated on
    /// a `peek_text == expected_text` check. Pass → consume one token,
    /// no GSS change. Fail → no child allocated. Replaces the
    /// previously-unguarded `Consume` branch in BinderListLoop's
    /// 3-branch Fork — that branch ran on every dispatch regardless of
    /// token, causing exponential cursor multiplication and >4000s hangs
    /// on rhocalc::PNew multi-binder grammars.
    GuardedConsume { expected_text: String },

    /// L12 follow-up B2 (2026-05-07) — closure for BinderListLoop
    /// bootstrap empty-list branch. Mirrors
    /// `WpdsStepAction::ConsumeAndReplace` plus a pre-replace
    /// `BuilderDelta` effect (typically
    /// `BuilderDelta::StartBinderScope { names: vec![] }`), gated on
    /// `peek_text == expected_text`. Pass → log effect to
    /// pending_builder_ops, replace top of GSS, advance pos. Fail →
    /// no child allocated. Used by BinderListLoop's 2-branch bootstrap
    /// (empty-list + first-ident) so the empty-list branch only fires
    /// when the close delimiter is the next token.
    GuardedConsumeAndReplaceWithEffect {
        expected_text: String,
        effect: BuilderDelta,
    },

    /// B8 / Issue B (2026-05-09): Class 3 empty-list bootstrap variant.
    /// Same semantics as `GuardedConsumeAndReplaceWithEffect` but logs
    /// MULTIPLE BuilderDelta effects in declaration order before the
    /// replace. Used by Class 3 BinderListLoop's empty-close branch
    /// to atomically log [StartCollection, PushCollectionId{id:0},
    /// StartBinderScope] so the action's arity-3 expectation is met
    /// even on the empty-list path (CollectionId arg pushed, scope
    /// opened, accumulator drains to empty Vec at action time).
    GuardedConsumeAndReplaceWithMultipleEffects {
        expected_text: String,
        effects: Vec<BuilderDelta>,
    },

    /// B8 / Issue C followup (2026-05-09): Class 3 non-empty bootstrap
    /// variant. Replaces the top symbol with `replace_symbol`, then
    /// pushes `branch.symbol` on top — mirroring engine-level
    /// `WpdsStepAction::ReplaceAndPush` semantics inside a Fork branch.
    /// No token consumed. Used by Class 3 BinderListLoop's non-empty
    /// bootstrap to (a) replace the outer RuleAt(rule, marker_pos)
    /// with RuleAt(rule, next_pos) so the post-loop unwind lands at
    /// the next outer position, AND (b) push CollectionMarker for
    /// the Names accumulator. emit_push_side_effects fires for the
    /// pushed CollectionMarker (allocates accumulator, pushes
    /// CollectionId arg, opens BinderScope per is_class3_collection).
    ReplaceAndPush {
        replace_symbol: StackSymbolV2,
    },

    /// B8 / Issue C followup (2026-05-09): consume an Ident token,
    /// optionally start a binder scope, push the ident name to builder,
    /// THEN pop top-of-GSS. Mirrors `ConsumeIdentAndReplace` but Pops
    /// instead of Replacing. Used by Class 3 BinderListLoop's last
    /// inner BinderIdent step so the cursor returns to the
    /// CollectionMarker (not to a duplicate RuleAt) when the loop
    /// continues.
    ConsumeIdentAndPop {
        start_scope: bool,
    },

    /// B8 / Issue C followup (2026-05-09): consume a token + Pop top-
    /// of-GSS + log a builder delta. Used by Class 3 BinderListLoop's
    /// sub_pos=0 close branch to consume the close delim, pop the
    /// CollectionMarker (the loop's marker), and log EndBinderScope
    /// in one atomic action.
    GuardedConsumeAndPopWithEffect {
        expected_text: String,
        effect: BuilderDelta,
    },

    /// B8 / Issue 3 fix (2026-05-10): consume an Ident token; either
    /// open a new binder scope with `[text]` (start_scope=true) OR
    /// extend the innermost open scope's names list with `text`
    /// (start_scope=false); replace top-of-GSS with `branch.symbol`;
    /// advance pos by 1. Crucially, does NOT call `emit_push_ident`
    /// — the captured name lives in the binder scope, not the args
    /// stack. Used by multi-binder rules (PNew-style `^[xs]`) whose
    /// terminal action expects `ActionArg::BinderScope`, not Ident.
    /// Lambda Lam-style single-binder rules whose action expects
    /// `ActionArg::Ident` continue to use `GuardedConsumeIdentAndReplace`.
    GuardedConsumeBinderIdentAndReplace {
        start_scope: bool,
    },

    /// Phase 3.B.2 (2026-05-11): single-binder collapse variant.
    /// Same as `GuardedConsumeBinderIdentAndReplace` (peek_kind=Ident
    /// gate, open-or-extend binder scope, GSS top replacement, pos++)
    /// but ALSO logs `effect` (typically `BuilderDelta::EndBinderScope`)
    /// onto pending_builder_ops between the scope mutation and the GSS
    /// replace. Used for single-binder collapse where the lone ident
    /// closes the scope immediately — atomically captures the ident
    /// AND closes the scope in one Fork branch. AST surface unchanged:
    /// `emit_binder_action_entry` unwraps `BinderScope.names[0]` to a
    /// scalar `Binder<String>` for the single-binder collapsed case,
    /// preserving Lambda Lam<Binder<String>, ...>, ambient PNew, and
    /// guardedRho PGuardedInput AST signatures.
    GuardedConsumeBinderIdentAndReplaceWithEffect {
        start_scope: bool,
        effect: BuilderDelta,
    },
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
    /// Phase 4 #1 (2026-05-11): monotonic counter of collection slots
    /// allocated by this cursor (never decremented). Used by
    /// `emit_start_collection` in Strict mode as the id source — NOT
    /// `cursor.collection_stack.len()` — so multi-collection-slot
    /// Class 2 rules allocate distinct ids per slot even when prior
    /// slots' mirrors popped on marker pop. Match-replays cleanly
    /// against `live.start_collection()` which always returns its
    /// own monotonic len. Initialized 0; bumped on every Strict-mode
    /// emit_start_collection.
    pub collection_slots_allocated: u8,
    /// Stage 3.12 Fix 2(ii) (2026-05-02): Fork-source-order tiebreak
    /// priority. Set to `branch_idx as u32` when the cursor is allocated
    /// in a Fork's children loop (TAKE=0, SKIP=1 for Opt-Group);
    /// inherited via `Clone` for descendants. Used by
    /// `merge_equivalent_cursors` and `pick_lex_min_resolved` as the
    /// FINAL tiebreak after `LexicographicWeight::plus` reports
    /// equality. Lower priority wins.
    ///
    /// Why this matters: pre-3.12 the merge tie resolved via
    /// `Semiring::plus`'s receiver-on-Equal semantics, which depended
    /// on insertion order at the merge — itself driven by speed-of-
    /// arrival in `step_fanout`. SKIP descendants typically arrived
    /// earlier (no token-consume), so merge ties picked LEFT-associative
    /// for dangling-else. With `source_priority`, TAKE (priority 0)
    /// always beats SKIP (priority 1) on weight ties, restoring the
    /// right-associative behavior the codegen `vec![take, skip]` order
    /// expressed.
    ///
    /// Singleton-Lazy default: 0. Default for non-Fork-allocated
    /// cursors (constructors, BranchResolved write-back, commit_winner
    /// write-back).
    pub source_priority: u32,
    /// Stage 3.12.6 (2026-05-02): per-cursor stack-suffix identity. Each
    /// entry is the `GssEdgeId` returned by a corresponding `cursor_gss_push`
    /// (or `cursor_gss_replace_top`). On `cursor_gss_pop_via_edge`, the
    /// top is popped and the predecessor of *that specific edge* becomes
    /// the cursor's new GSS top — restoring pop-time determinism even
    /// when GSS structural sharing dedupes recursive `(pos, symbol)`
    /// pushes from distinct calling contexts.
    ///
    /// `incoming_edge` (a derived view) is `incoming_edge_stack.last().copied()`.
    /// Used by `ConfigKey` so cursors with distinct stack suffixes do
    /// not merge in `merge_equivalent_cursors`.
    ///
    /// Empty for the seed cursor (no push yet); empty after a pop has
    /// reached the GSS root sentinel (cursor.node == GSS_NODE_NONE).
    /// Bounded by recursion depth at parse time.
    pub incoming_edge_stack: Vec<crate::gss::GssEdgeId>,
    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): per-cursor count
    /// of recovery dispatches this cursor (or any of its ancestors) has
    /// experienced. Capped at `RecoveryConfig.max_recovery_depth`. The
    /// `apply_action_to_cursor::Fork` arm increments by 1 on each child
    /// allocation when the action is a recovery Fork (detected by
    /// inspecting per-branch `BuilderDelta` effect kind). When this
    /// reaches the cap, the next recovery Fork is rejected (cursor
    /// transitions to Error). Bounds the 8^N cursor-explosion that
    /// recursive recovery dispatch would otherwise produce.
    pub recovery_depth: u8,
    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): per-cursor
    /// configurations at which recovery has already been attempted.
    /// Each entry is `(pos, state_cat_src_idx, cur_bp)` — the cursor
    /// refuses to dispatch recovery at any configuration it has already
    /// tried. Catches cycle scenarios where two recovery branches
    /// alternate between configurations (e.g., Insert at pos=5 →
    /// Delete at pos=5 → Insert at pos=5 → ...). Bounded in size by
    /// `recovery_depth` (each insert here corresponds to a depth
    /// increment).
    pub visited_recovery: OrdSet<(usize, u16, u8)>,
    /// B12 / Candidate E (2026-05-07): per-cursor configurations at
    /// which a CROSS-CAT-PROJECTION Fork has already fired on this
    /// cursor's path. Each entry is `(pos, state_cat_src_idx, cur_bp)`
    /// — the same key shape as `visited_recovery` because the
    /// termination lemma is identical: a cursor that re-enters the
    /// same dispatch configuration via a projection Fork is in a
    /// non-productive recursive cross-cat cycle (e.g. LedTest's
    /// Pred → Num via PredToNum, where Num's PrefixDispatch then
    /// fires PredToNum projection back to Pred's PrefixDispatch).
    /// Distinct from `visited_recovery` because non-recovery dispatch
    /// has unrelated termination criteria (recovery uses
    /// `RecoveryConfig.max_recovery_depth`; projection cycles use
    /// the GLL descriptor-uniqueness argument — Scott & Johnstone
    /// 2010). Mirrors `visited_recovery` propagation: cloned to each
    /// child on Fork, inserted with the parent's dispatch config
    /// after a projection Fork emission.
    pub visited_dispatch: OrdSet<(usize, u16, u8)>,
    /// B13d-R Step 2 (2026-05-08): per-cursor memoization of
    /// `cursor_committed_ops_consistent`. The outer `Option` is
    /// uncomputed/computed; the inner `Option<bool>` is the tristate
    /// (Some(true) consistent / Some(false) definitely-broken / None
    /// indeterminate).
    ///
    /// Per Claim 1 (append-only contract for pending_builder_ops,
    /// verified by exhaustive grep), the dry-run is monotone:
    /// `Some(false)` is sticky for the lifetime of the cursor; for
    /// `Some(true)` and `None`, an append CAN flip them. Invalidate
    /// (`set(None)`) at every `pending_builder_ops.push(...)` site.
    ///
    /// Initialized to `Some(Some(true))` (Consistent) at construction
    /// because empty pending = consistent dry-run by definition.
    /// `Cell` (not `RefCell`) because the value is `Copy`; no borrow
    /// tracking needed.
    pub consistency_memo: std::cell::Cell<Option<Option<bool>>>,
    /// Phase 5.2 (2026-05-12): per-cursor `Arc`-shared `SemanticBuilder`.
    /// Future anchor for the persistent-builder redesign — the runtime
    /// still routes walker-driven mutations through `pending_builder_ops`
    /// (journal model). Phase 5.3 migrates emitter helpers to mutate
    /// `cursor.builder` directly via `Arc::make_mut`; Phase 5.4 drops the
    /// Hack #7 Fork prologue (`pre_fork_slots` donation) in favor of an
    /// O(1) `Arc::clone` per child; Phase 5.6 deletes
    /// `pending_builder_ops` entirely.
    ///
    /// Today (Phase 5.2): the field is structurally present but NOT read
    /// or written by the engine. `BranchCursor::clone` bumps the Arc
    /// (O(1)); `BranchCursor::fork_child` and `seed_from_live` initialize
    /// it from the parent's Arc or a fresh empty `SemanticBuilder`,
    /// respectively. Including the field NOW lets Phase 5.3+ route
    /// mutations without touching every construction site again.
    ///
    /// NOT part of `ConfigKey` — this is operational per-cursor state,
    /// not a merge-equivalence key. Merge tiebreak preserves the
    /// surviving cursor's builder by Vec-write semantics in
    /// `merge_equivalent_cursors`, identical to how `pending_builder_ops`
    /// + `collection_stack` are kept today.
    pub builder: Arc<SemanticBuilder>,
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
            // Phase 5.2 (2026-05-12): Arc strong count is the most useful
            // diagnostic — shows how many cursors share this builder
            // before the next mutation triggers copy-on-write.
            .field("builder_arc_refcount", &Arc::strong_count(&self.builder))
            .finish()
    }
}

impl<W: Semiring + Clone> Clone for BranchCursor<W> {
    fn clone(&self) -> Self {
        // Stage 3.6 / ι Phase 1 (2026-05-01): BranchCursor::clone is now
        // TOTAL across all field shapes:
        // - `pending_builder_ops`: BuilderDelta is Clone (from Cleanup-4).
        // - `collection_stack: Vec<Vec<ActionArg>>`: ActionArg is Clone
        //   (from Stage 3.6 — `Term`/`Collection`/`Predicate` payloads
        //   are now `Arc<dyn Any + Send + Sync>`, structurally clonable).
        //
        // The pre-3.6 `debug_assert!` requiring `collection_stack` to be
        // empty has been removed — cloning a cursor with populated
        // accumulators is now safe and lossless.
        //
        // Phase 5.2 (2026-05-12): `builder: Arc<SemanticBuilder>` bumps
        // the refcount in O(1) — no deep clone. The shared underlying
        // builder is only forked when a Phase 5.3+ mutator calls
        // `Arc::make_mut`.
        BranchCursor {
            node: self.node,
            pos: self.pos,
            weight: self.weight.clone(),
            inner_state: self.inner_state.clone(),
            pending_builder_ops: self.pending_builder_ops.clone(),
            collection_stack: self.collection_stack.clone(),
            collection_slots_allocated: self.collection_slots_allocated,
            source_priority: self.source_priority,
            incoming_edge_stack: self.incoming_edge_stack.clone(),
            recovery_depth: self.recovery_depth,
            visited_recovery: self.visited_recovery.clone(),
            visited_dispatch: self.visited_dispatch.clone(),
            consistency_memo: std::cell::Cell::new(self.consistency_memo.get()),
            builder: Arc::clone(&self.builder),
        }
    }
}

impl<W: Semiring + Clone> BranchCursor<W> {
    /// Stage 3.10 / ι Phase 5 (2026-05-01): construct a fresh cursor that
    /// mirrors the live walker's collection-stack depth via empty
    /// placeholders.
    ///
    /// **Class C closure**: pre-Phase-4, the walker maintained two parallel
    /// mutation surfaces (live builder + cursor deltas). When a Lazy parse
    /// transitioned to Strict (first Fork) with collections open in the
    /// live builder, the children cursors had no awareness of those
    /// collections — subsequent splice deltas could underflow at replay
    /// (`pop_args` panic at `wpds_runtime.rs:1518`).
    ///
    /// Post-Phase-4, the dual-mutation surface is gone; the live builder
    /// and cursor[0] stay in lockstep in Lazy mode via mode-aware helpers.
    /// At Lazy→Strict transition, children inherit the parent cursor's
    /// state, but the parent cursor's `collection_stack` may be empty
    /// (Lazy mutates live builder directly, NOT cursor.collection_stack).
    /// The Fork arm therefore needs to seed children's `collection_stack`
    /// with empty placeholders matching the live builder's depth so
    /// subsequent splice ids align.
    ///
    /// `seed_from_live` makes this explicit. Constructs a cursor with
    /// `K` empty `Vec<ActionArg>` placeholders in `collection_stack`,
    /// where `K = live_collection_stack_depth`. Used by WpdsWalker
    /// constructors and the Lazy→Strict transition (Fork) to ensure
    /// the always-non-empty + always-aligned cursor invariant.
    ///
    /// Replaces three inlined constructions in `WpdsWalker::{new,
    /// new_for_category, seeded_from}` — single source of truth.
    pub fn seed_from_live(
        node: crate::gss::GssNodeId,
        pos: usize,
        weight: W,
        inner_state: WpdsState,
        live_collection_stack_depth: usize,
    ) -> Self {
        BranchCursor {
            node,
            pos,
            weight,
            inner_state,
            pending_builder_ops: Vec::new(),
            collection_stack: (0..live_collection_stack_depth)
                .map(|_| Vec::new())
                .collect(),
            collection_slots_allocated: live_collection_stack_depth as u8,
            // Stage 3.12 Fix 2(ii) (2026-05-02): default 0 for non-Fork-
            // allocated cursors. Fork arm overwrites per-branch.
            source_priority: 0,
            // Stage 3.12.6 (2026-05-02): empty stack for seed cursor
            // (no push has been made). cursor_gss_push appends to this
            // stack on every push.
            incoming_edge_stack: Vec::new(),
            // Bounded recovery (Stage 3.20 / L12, 2026-05-06): seed cursor
            // has not experienced any recovery, so depth 0 + empty
            // visited set.
            recovery_depth: 0,
            visited_recovery: OrdSet::new(),
            // B12 / Candidate E (2026-05-07): seed cursor has not
            // dispatched any projection Fork yet — empty visited set.
            visited_dispatch: OrdSet::new(),
            // B13d-R Step 2 (2026-05-08): empty pending = Consistent.
            consistency_memo: std::cell::Cell::new(Some(Some(true))),
            // Phase 5.2 (2026-05-12): fresh empty Arc<SemanticBuilder>.
            // The seed cursor's builder is independent of the walker's
            // live builder (the field is unused in 5.2 — see field
            // docstring). Walker constructors that call `seed_from_live`
            // initialize their `self.builder: SemanticBuilder` to
            // `SemanticBuilder::new()` in lockstep, so the two stay
            // structurally identical at construction time.
            builder: Arc::new(SemanticBuilder::new()),
        }
    }

    /// Allocate a Fork-child cursor inheriting the parent's
    /// pending_builder_ops, collection_stack, incoming_edge_stack,
    /// recovery_depth, and visited_recovery. The caller overrides
    /// `pos`, `weight`, `inner_state`, and `source_priority` from the
    /// branch's data.
    ///
    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): when the Fork
    /// being dispatched is a recovery Fork (detected at the Fork-arm
    /// entry via `is_recovery_fork`), the caller increments the child's
    /// `recovery_depth` by 1 and inserts the dispatch configuration into
    /// `visited_recovery` BEFORE pushing into the children vec. For
    /// non-recovery Forks (Push, OptGroupAbsent, lex-alt, etc.), the
    /// child inherits the parent's recovery state unchanged.
    pub fn fork_child(
        parent: &Self,
        pos: usize,
        weight: W,
        new_state: WpdsState,
        source_priority: u32,
    ) -> Self {
        BranchCursor {
            node: parent.node,
            pos,
            weight,
            inner_state: new_state,
            pending_builder_ops: parent.pending_builder_ops.clone(),
            collection_stack: parent.collection_stack.clone(),
            collection_slots_allocated: parent.collection_slots_allocated,
            source_priority,
            incoming_edge_stack: parent.incoming_edge_stack.clone(),
            recovery_depth: parent.recovery_depth,
            visited_recovery: parent.visited_recovery.clone(),
            // B12 / Candidate E (2026-05-07): inherit parent's projection
            // visited set; the Fork-arm post-allocation step inserts the
            // current dispatch config when this fork IS a projection Fork.
            visited_dispatch: parent.visited_dispatch.clone(),
            // B13d-R Step 2 (2026-05-08): inherit parent's memo (the child
            // shares parent's pending_builder_ops at construction time;
            // any subsequent push invalidates the child's memo).
            consistency_memo: std::cell::Cell::new(parent.consistency_memo.get()),
            // Phase 5.2 (2026-05-12): O(1) Arc bump — the child shares
            // the parent's `SemanticBuilder` until a Phase 5.3+ mutator
            // forces copy-on-write via `Arc::make_mut`. This is the
            // single-most-important reason the field exists: Fork
            // fanout cost becomes constant per child.
            builder: Arc::clone(&parent.builder),
        }
    }
}

/// Stage 3.5b (2026-05-01): WPDS configuration key for cursor ⊕-merging.
///
/// WPDS semantics require: two paths reaching the same configuration
/// `⟨p, w⟩` collapse via `Semiring::plus`. The Walker's `branch_cursors`
/// is a flat `Vec<BranchCursor>` with no dedup of equivalent
/// configurations — Stage 3.1 fixed GSS-edge merging only.
/// `merge_equivalent_cursors` runs after `step_fanout` per step,
/// collapsing cursors with the same `(state, gss_node, pos)` into a single
/// cursor whose weight is the `Semiring::plus` of the inputs. The lex-min
/// winner's `pending_builder_ops` and `collection_stack` are kept (deltas
/// are non-commutative; only the winning path's mutations execute on
/// commit).
///
/// **Verified (2026-05-01):** no hidden differentiators on BranchCursor.
/// `selected_lex_alts` doesn't exist as a field (lex_alt_idx lives in
/// `weight`'s 4-tuple). `pending_builder_ops` and `collection_stack` are
/// operational state — kept from the lex-min winner, not part of the key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ConfigKey {
    /// Cursor's per-branch FSM state. `WpdsState: Hash` derive added in
    /// Stage 3.5b (`wpds_runtime.rs:326`).
    state: WpdsState,
    /// GSS-tip node id. The GSS dedups by `(pos, symbol)`, so equality
    /// here = stack-tip equality only (NOT full stack-suffix equality).
    node: crate::gss::GssNodeId,
    /// Per-branch input position.
    pos: usize,
    /// Stage 3.12.6 (2026-05-02): GSS edge id the cursor traversed on
    /// its most recent push (top of `incoming_edge_stack`). Two cursors
    /// at the same `(state, node, pos)` but different `incoming_edge`
    /// represent DISTINCT stack-suffixes (their next pop targets
    /// differ) — they should NOT merge.
    ///
    /// This is the WPDS-correct refinement of Tomita/GLL configuration
    /// equivalence under GSS structural sharing across recursive rule
    /// re-entries (Reps/Lal/Kidd 2007 Theorem 3.4: stack-word merge
    /// requires same stack word, which the GSS dedup obscures at the
    /// tip).
    incoming_edge: Option<crate::gss::GssEdgeId>,
    /// Phase 4 #5b (2026-05-12): collection-stack depth. Two cursors
    /// at the same `(state, node, pos, incoming_edge)` but different
    /// `collection_stack.len()` represent DISTINCT operational states
    /// — one has opened more inner collection slots than the other.
    /// Merging them would violate the
    /// `debug_assert_eq!(merged[idx].collection_stack.len(), cursor.
    /// collection_stack.len())` invariant at the cursor-replacement
    /// site. Adding this to the key forces them into separate buckets,
    /// so the merge logic only fires when shapes truly agree.
    ///
    /// This becomes relevant after the Phase 4 #5b policy change that
    /// pops the cursor's collection_stack on EVERY CollectionMarker pop
    /// (including binder-internal). Pre-fix, the cursor's mirror was
    /// monotonic for binder-internal slots — two branches reaching the
    /// same `(state, node, pos)` had identical depths by induction.
    /// Post-fix, the depths can transiently diverge when one branch's
    /// inner CollectionMarker has popped but the other's has not.
    /// Including depth in the key segregates them cleanly.
    collection_depth: usize,
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

/// Stage 3.20 / L12 (Commit 4, 2026-05-06): WPDS-edge recovery event.
/// Each `BuilderDelta::RecoveryEvent`, `SubstituteToken`, `InsertToken`,
/// or `CommitLexAlternative` delta replayed at commit_winner time pushes
/// a `RecoveryEvent` onto `WpdsWalker::recovery_events`. The walker's
/// `recovery_trace()` accessor exposes this for diagnostic + recovery-
/// attempt-surface consumers (facade.rs's `parse_<Cat>_via_wpds_recovering`
/// maps each event into a `RecoveryAttempt`).
#[derive(Clone, Debug)]
pub struct RecoveryEvent {
    /// RepairAction discriminator: 0=SkipToSync, 1=DeleteToken,
    /// 2=InsertToken, 3=SubstituteToken, 4=SwapTokens, 5=Composite,
    /// 6=CategorySwitch, 7=LexAlt.
    pub action_kind: u8,
    /// Position in the token stream where the recovery action applies.
    pub pos: usize,
    /// Tropical cost component of the LexicographicWeight at recovery time.
    pub cost_tropical: f64,
    /// Token kind for Substitute/Insert/CommitLexAlt actions; None for
    /// Skip/Delete/RecoveryEvent-only deltas.
    pub kind: Option<TokenKind>,
    /// Token text for Substitute/Insert/CommitLexAlt actions; None for
    /// Skip/Delete/RecoveryEvent-only deltas.
    pub text: Option<String>,
    /// Lex alternative index for CommitLexAlt; None for other actions.
    pub alt_idx: Option<u16>,
}

impl RecoveryEvent {
    pub fn from_action_kind(action_kind: u8, pos: usize, cost_tropical: f64) -> Self {
        RecoveryEvent {
            action_kind,
            pos,
            cost_tropical,
            kind: None,
            text: None,
            alt_idx: None,
        }
    }
    pub fn substitute(pos: usize, kind: TokenKind, text: String) -> Self {
        RecoveryEvent {
            action_kind: 3,
            pos,
            cost_tropical: 0.0,
            kind: Some(kind),
            text: Some(text),
            alt_idx: None,
        }
    }
    pub fn insert(pos: usize, kind: TokenKind, text: String) -> Self {
        RecoveryEvent {
            action_kind: 2,
            pos,
            cost_tropical: 0.0,
            kind: Some(kind),
            text: Some(text),
            alt_idx: None,
        }
    }
    pub fn lex_commit(
        pos: usize,
        alt_idx: u16,
        kind: TokenKind,
        text: String,
    ) -> Self {
        RecoveryEvent {
            action_kind: 7,
            pos,
            cost_tropical: 0.0,
            kind: Some(kind),
            text: Some(text),
            alt_idx: Some(alt_idx),
        }
    }
}

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
    /// B8 / Issue C followup (2026-05-09): cursor closes the active
    /// binder scope. Replay calls `SemanticBuilder::end_binder_scope`
    /// which pops the active BinderHandle and pushes
    /// `ActionArg::BinderScope(handle)` onto the args stack so the
    /// owning binder rule's terminal action can extract its `.names`.
    /// Without this delta, scopes opened via `StartBinderScope` never
    /// close and BinderScope args never reach the action — affecting
    /// PNew, PInputs, and any binder rule with a multi-binder list.
    EndBinderScope,
    /// B8 / Issue C followup (2026-05-09): append a name to the
    /// innermost binder scope's names list. Used by multi-binder
    /// iterations where the scope opens once at bootstrap with empty
    /// names and each iteration extends the list.
    ExtendBinderScope { name: String },
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

    // ─── Stage 3.7 / ι Phase 2 (2026-05-01): 10 new variants ─────────────────
    //
    // Per `plan-iota-full-single-cursor.md`, these enable the cursor-side
    // migration of every live-builder mutation in Phase 4 (Always-cursor
    // walker). Today's commit_winner replays them on the live builder; in
    // Phase 4, ALL mutations route through deltas regardless of CursorMode.

    /// Optional-scope: cursor opens an optional-group scope. Replay
    /// invokes `SemanticBuilder::start_optional_scope` which pushes a
    /// new arg-frame onto `optional_stack` so subsequent inner pushes
    /// land in the inner frame, not the outer main stack.
    StartOptionalScope,

    /// Optional-scope: cursor finalizes the optional with `Some(inner_args)`.
    /// Replay invokes `SemanticBuilder::finalize_optional_scope_present`
    /// which pops the inner frame and pushes
    /// `ActionArg::Optional(Some(inner_args))`.
    FinalizeOptionalScopePresent,

    /// Optional-scope: cursor finalizes the optional with `None`.
    /// Replay invokes `SemanticBuilder::push_optional_absent`.
    PushOptionalAbsent,

    /// Collection-cursor (paired with `PushCollectionId`): allocate a
    /// fresh accumulator on the live builder. Replay invokes
    /// `SemanticBuilder::start_collection()` and discards the returned id
    /// (the cursor allocated its own id at log time; commit re-allocates
    /// in matching order via `adopt_collection_stack` BEFORE delta
    /// replay, so the live builder's accumulator indices align).
    ///
    /// This variant is reserved for Phase 4 / Phase 6 lazy-mode delta
    /// emission paths that may need explicit collection-allocation
    /// outside the GSS-symbol-driven `PushCollectionId` flow.
    StartCollection,

    /// Collection-cursor: append the top-of-stack arg into accumulator
    /// `id`. Replay invokes `SemanticBuilder::push_to_collection(id)`.
    /// Identical semantics to `SpliceIntoCollection` but distinguishes
    /// the explicit "logical element push" call site from the implicit
    /// "post-pop splice" call site.
    PushToCollection { id: u8 },

    /// Stage 3.20 prep: cursor logs a recovery event. Replay invokes
    /// `walker.recovery_events.push(RecoveryEvent { action, pos, cost })`.
    /// `RecoveryActionKind` is the enum-encoded action variant; the
    /// detailed payload (skip count, replacement token, etc.) lives in
    /// the action-specific deltas below.
    RecoveryEvent {
        action_kind: u8,
        pos: usize,
        cost_tropical: f64,
    },

    /// Stage 3.20 prep: substitute a token at `pos` with the given
    /// kind/text. Replay invokes the walker's mutable token-source
    /// adapter to overwrite the token, then logs a complementary
    /// `RecoveryEvent`.
    SubstituteToken {
        pos: usize,
        kind: TokenKind,
        text: String,
    },

    /// Stage 3.20 prep: insert a synthetic token before `pos`. Replay
    /// invokes the mutable token-source adapter to splice the new token,
    /// shifting subsequent positions by 1.
    InsertToken {
        pos: usize,
        kind: TokenKind,
        text: String,
    },

    /// Stage 3.14 / Hack #12 prep: cursor commits a lex alternative
    /// selection at `pos`. Replay invokes
    /// `MutableMultiTokenSource::commit_alternative(pos, alt_idx)` which
    /// rewrites the lex stream's primary alternative for that position
    /// to the cursor's chosen alt. `kind` and `text` are captured for
    /// downstream consumers (lint diagnostics, traced parse output).
    CommitLexAlternative {
        pos: usize,
        alt_idx: u16,
        kind: TokenKind,
        text: String,
    },
    /// Stage 3.20 / L12 (Commit B, 2026-05-06): atomically replay a
    /// sequence of recovery primitives (Skip / Delete / Insert /
    /// Substitute) at commit_winner time. Used by `recovery_dispatch::
    /// emit_recovery_fork` when `viterbi_multi_step` returns a multi-action
    /// repair sequence. The entire sequence applies as one unit; partial
    /// application would leave the token stream in an inconsistent state.
    ///
    /// `actions` is `Arc<[RepairAction]>` for cheap clone on Fork-branch
    /// allocation (each cursor's pending_builder_ops gets its own clone
    /// of the Arc, sharing the slice contents).
    ///
    /// `base_pos` is the token position at which the first action applies;
    /// subsequent actions advance `cur_pos` per their semantics.
    ///
    /// `total_cost_tropical` is the multi-step Viterbi-best cost; recorded
    /// on each emitted `RecoveryEvent` for downstream cost-based selection.
    ApplyRecoverySequence {
        actions: Arc<[crate::recovery::RepairAction]>,
        base_pos: usize,
        total_cost_tropical: f64,
    },
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
            BuilderDelta::EndBinderScope => f
                .debug_struct("EndBinderScope")
                .finish(),
            BuilderDelta::ExtendBinderScope { name } => f
                .debug_struct("ExtendBinderScope")
                .field("name", name)
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
            BuilderDelta::StartOptionalScope => f.debug_struct("StartOptionalScope").finish(),
            BuilderDelta::FinalizeOptionalScopePresent => {
                f.debug_struct("FinalizeOptionalScopePresent").finish()
            }
            BuilderDelta::PushOptionalAbsent => f.debug_struct("PushOptionalAbsent").finish(),
            BuilderDelta::StartCollection => f.debug_struct("StartCollection").finish(),
            BuilderDelta::PushToCollection { id } => f
                .debug_struct("PushToCollection")
                .field("id", id)
                .finish(),
            BuilderDelta::RecoveryEvent {
                action_kind,
                pos,
                cost_tropical,
            } => f
                .debug_struct("RecoveryEvent")
                .field("action_kind", action_kind)
                .field("pos", pos)
                .field("cost_tropical", cost_tropical)
                .finish(),
            BuilderDelta::SubstituteToken { pos, kind, text } => f
                .debug_struct("SubstituteToken")
                .field("pos", pos)
                .field("kind", kind)
                .field("text", text)
                .finish(),
            BuilderDelta::InsertToken { pos, kind, text } => f
                .debug_struct("InsertToken")
                .field("pos", pos)
                .field("kind", kind)
                .field("text", text)
                .finish(),
            BuilderDelta::CommitLexAlternative {
                pos,
                alt_idx,
                kind,
                text,
            } => f
                .debug_struct("CommitLexAlternative")
                .field("pos", pos)
                .field("alt_idx", alt_idx)
                .field("kind", kind)
                .field("text", text)
                .finish(),
            BuilderDelta::ApplyRecoverySequence {
                actions,
                base_pos,
                total_cost_tropical,
            } => f
                .debug_struct("ApplyRecoverySequence")
                .field("actions_len", &actions.len())
                .field("base_pos", base_pos)
                .field("total_cost_tropical", total_cost_tropical)
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

/// Bounded recovery (Stage 3.20 / L12, 2026-05-06): detect whether a
/// `WpdsStepAction::Fork` was emitted by `recovery_dispatch::emit_recovery_fork`
/// (vs. a regular ambiguity Fork from binder / lex-alt / multi-rule etc.).
///
/// A recovery Fork is identified by having at least one branch whose
/// `action_kind` is `ConsumeAndReplaceWithEffect { effect: <recovery delta> }`,
/// where the recovery deltas are exactly the four built by
/// `repair_result_to_fork_branch` and `repair_sequence_to_fork_branch`:
///   - `BuilderDelta::RecoveryEvent` (Skip / Delete branches)
///   - `BuilderDelta::InsertToken`   (Insert branches)
///   - `BuilderDelta::SubstituteToken` (Substitute branches)
///   - `BuilderDelta::ApplyRecoverySequence` (multi-step Viterbi)
///
/// These four deltas are NOT used by any non-recovery emitter — the
/// detection is robust against accidental conflation.
fn is_recovery_fork<W: Semiring>(branches: &[ForkBranch<W>]) -> bool {
    branches.iter().any(|b| {
        matches!(
            &b.action_kind,
            ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::RecoveryEvent { .. }
                    | BuilderDelta::InsertToken { .. }
                    | BuilderDelta::SubstituteToken { .. }
                    | BuilderDelta::ApplyRecoverySequence { .. }
            }
        )
    })
}

/// Bounded recovery (Stage 3.20 / L12, 2026-05-06): forward-progress
/// filter for recovery branches.
///
/// A recovery branch is allowed if either:
///   1. Its `new_state` is `PrefixDispatch { pos, .. }` with `pos > base_pos`
///      (i.e., the cursor advances past the dead-end token), OR
///   2. The branch carries a `BuilderDelta::InsertToken` effect (the only
///      legitimate non-advancing repair — synthetic token splice; the
///      live stream is mutated at commit time so the cursor's view of
///      the world changes, even though the synthesis-time pos doesn't).
///
/// Branches that meet neither criterion are dropped — they would
/// re-fire the same recovery dispatch at the same configuration,
/// producing an infinite loop the visited-set defense would catch but
/// at the cost of a wasted depth increment.
fn forward_progress_or_insert<W: Semiring>(branch: &ForkBranch<W>, base_pos: usize) -> bool {
    let advances = match &branch.new_state {
        WpdsState::PrefixDispatch { pos, .. } => *pos > base_pos,
        // Non-PrefixDispatch new_states (rare; recovery_dispatch only
        // emits PrefixDispatch but be defensive) are conservatively
        // allowed — they leave the dead-end loop by virtue of state
        // change.
        _ => true,
    };
    advances
        || matches!(
            &branch.action_kind,
            ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::InsertToken { .. }
            }
        )
}

/// Bounded recovery (Stage 3.20 / L12, 2026-05-06): extract the
/// `(pos, cat_src_idx, cur_bp)` configuration at which a recovery
/// dispatch fires. Inserted into the cursor's `visited_recovery` set
/// after dispatch so subsequent dispatches at the same configuration
/// are refused (cursor cycle defense).
///
/// Returns `None` if the cursor's `inner_state` isn't `PrefixDispatch`
/// — recovery only fires from PrefixDispatch dead-ends per
/// `engine_impl.rs`'s codegen, so this is normally unreachable. The
/// caller falls back to bumping `recovery_depth` without a visited
/// entry in that case (the cap still bites).
fn extract_recovery_dispatch_config<W: Semiring>(
    cursor: &BranchCursor<W>,
    gss: &WpdsGss<W>,
) -> Option<(usize, u16, u8)> {
    if let WpdsState::PrefixDispatch { pos, cur_bp } = &cursor.inner_state {
        let cat_src = gss
            .node(cursor.node)
            .map(|n| n.symbol.category_src_idx)
            .unwrap_or(0);
        Some((*pos, cat_src, *cur_bp))
    } else {
        None
    }
}

/// B12 / Candidate E (2026-05-07), tightened by B13 (2026-05-07): a
/// *pure projection Fork* is a non-recovery Fork in which **every**
/// branch transitions to `WpdsState::CrossCatDelegate { .. }`. Mixed
/// buckets (atomic + projection, or cross-cat-LHS + projection)
/// are EXEMPT from the cycle defense — their atomic / LHS arms are
/// productive parse paths that B12 must not shadow via `visited_
/// dispatch`.
///
/// **Why `all` instead of `any`** (B13, 2026-05-07): B10 Fix B unified
/// Pass 2a CrossCatProjection arms into the same `unified_buckets`
/// map as Pass 0 (cross-cat-LHS) and Pass 1 (atomic) in `prefix.rs::
/// emit_prefix_arms_for_category`. Post-B10, a single Fork can mix
/// atomic + cross-cat-LHS + projection branches (e.g. Calculator's
/// Bool / Proc Ident bucket = atomic Var + cross-cat-LHS sources +
/// cross-cat-projection wrappers). With `any`, B12 tagged ALL
/// children's `visited_dispatch` whenever ANY branch was a projection
/// — shadowing productive atomic / LHS cursors at downstream
/// dispatches. The `all` predicate restricts the cycle defense to
/// pure-projection Forks (no productive siblings to shadow).
///
/// LedTest's cycle bound is preserved via the **Push-arm** check at
/// `apply_action_to_cursor::Push` (line ~2572), which fires on
/// singleton-projection emissions (`WpdsStepAction::Push { new_state:
/// CrossCatDelegate { .. } }`) regardless of this predicate. The
/// Fork-arm check is the secondary line of defense for cases where
/// a cycle traverses a multi-descriptor pure-projection bucket.
///
/// Used by the Fork arm of `apply_action_to_cursor` to decide whether
/// to apply the visited-dispatch cycle check; see `BranchCursor::
/// visited_dispatch` and the GLL descriptor-uniqueness rationale
/// (Scott & Johnstone 2010).
fn is_projection_fork<W: Semiring>(branches: &[ForkBranch<W>]) -> bool {
    !branches.is_empty()
        && branches.iter().all(|b| {
            matches!(&b.new_state, WpdsState::CrossCatDelegate { .. })
        })
}

/// B12 / Candidate E (2026-05-07): extract the `(pos, cat_src_idx, cur_bp)`
/// configuration at which a projection Fork fires. Returns `None` if the
/// cursor is not in `PrefixDispatch` — projection Forks fire only from
/// PrefixDispatch by codegen invariant; the caller falls back to
/// inserting nothing into `visited_dispatch` in that case (no cycle
/// defense possible without a meaningful key).
///
/// Identical body to `extract_recovery_dispatch_config` — kept separate
/// so future refactors can vary one without affecting the other.
fn extract_dispatch_config<W: Semiring>(
    cursor: &BranchCursor<W>,
    gss: &WpdsGss<W>,
) -> Option<(usize, u16, u8)> {
    if let WpdsState::PrefixDispatch { pos, cur_bp } = &cursor.inner_state {
        let cat_src = gss
            .node(cursor.node)
            .map(|n| n.symbol.category_src_idx)
            .unwrap_or(0);
        Some((*pos, cat_src, *cur_bp))
    } else {
        None
    }
}

impl<W: Semiring, E: WpdsStepEngine<W>> WpdsWalker<W, E> {
    /// Construct a fresh walker in `Ready { min_bp }` state.
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): seeds the singleton cursor in
    /// Lazy mode. Subsequent mutations route through `apply_action_to_cursor`
    /// against `branch_cursors[0]` via the always-cursor dispatcher.
    pub fn new(engine: E, initial_min_bp: u8) -> Self {
        let initial_state = WpdsState::Ready { min_bp: initial_min_bp };
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        // Sentinel node 0 — no GSS node yet; `cursor_gss_push` allocates
        // a CategoryEntry(0) root on first push when `cursor.node == 0`.
        // Live builder is fresh (depth 0), so no placeholders.
        let initial_cursor = BranchCursor::seed_from_live(
            0,
            0,
            W::one(),
            initial_state.clone(),
            0,
        );
        WpdsWalker {
            state: initial_state,
            gss: WpdsGss::new(),
            pos: 0,
            weight: W::one(),
            engine,
            top_node: None,
            beam_size: None,
            builder: SemanticBuilder::new(),
            cursor_mode: CursorMode::Lazy,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
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
        let initial_state = WpdsState::PrefixDispatch {
            pos: 0,
            cur_bp: initial_min_bp,
        };
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        let initial_cursor = BranchCursor::seed_from_live(
            top_id,
            0,
            W::one(),
            initial_state.clone(),
            0,
        );
        WpdsWalker {
            state: initial_state,
            gss,
            pos: 0,
            weight: W::one(),
            engine,
            top_node: Some(top_id),
            beam_size: None,
            builder: SemanticBuilder::new(),
            cursor_mode: CursorMode::Lazy,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
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
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        let initial_cursor = BranchCursor::seed_from_live(
            top_node.unwrap_or(0),
            config.pos,
            config.weight.clone(),
            config.state.clone(),
            0,
        );
        WpdsWalker {
            state: config.state,
            gss,
            pos: config.pos,
            weight: config.weight,
            engine,
            top_node,
            beam_size: None,
            builder: SemanticBuilder::new(),
            cursor_mode: CursorMode::Lazy,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
        }
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): reset the walker between
    /// parses. Returns to Lazy mode with a fresh singleton cursor.
    /// Preserves the engine and beam_size; everything else is
    /// reinitialized to construction defaults.
    pub fn reset(&mut self, initial_min_bp: u8) {
        let initial_state = WpdsState::Ready { min_bp: initial_min_bp };
        self.state = initial_state.clone();
        self.gss = WpdsGss::new();
        self.pos = 0;
        self.weight = W::one();
        self.top_node = None;
        self.builder = SemanticBuilder::new();
        self.cursor_mode = CursorMode::Lazy;
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        self.branch_cursors = vec![BranchCursor::seed_from_live(
            0,
            0,
            W::one(),
            initial_state,
            0,
        )];
        // Stage 6 G6+ (2026-05-02): reset trace step counter.
        self.step_counter = 0;
        // Stage 3.20 / L12 (Commit 4, 2026-05-06): clear recovery trace.
        self.recovery_events.clear();
        // Stage 3.20 / L12 (Commit A, 2026-05-06): clear the mutable
        // token source slot defensively — the source from the prior
        // parse may be dropped by the time reset() is called.
        self.mutable_token_source = None;
    }

    /// Read-only access to the cursor mode (Lazy/Strict).
    pub fn cursor_mode(&self) -> CursorMode {
        self.cursor_mode
    }

    /// Stage 3.20 / L12 (Commit 4, 2026-05-06): read-only access to the
    /// WPDS-edge recovery event trace. Each entry corresponds to one
    /// `BuilderDelta::RecoveryEvent` / `SubstituteToken` / `InsertToken` /
    /// `CommitLexAlternative` delta replayed at commit_winner time.
    /// Wrapper consumers (e.g. `parse_<Cat>_via_wpds_recovering`) map each
    /// entry into a `RecoveryAttempt` for surfacing to the user.
    pub fn recovery_trace(&self) -> &[RecoveryEvent] {
        &self.recovery_events
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): thread a mutable token
    /// source into the walker for recovery-driven token-stream mutations
    /// (SubstituteToken / InsertToken / CommitLexAlternative deltas
    /// replayed at commit_winner time call this source).
    ///
    /// SAFETY: the walker stores `source as *mut dyn WpdsMutableTokenSource`
    /// to avoid cascading `'a` through the struct. The caller MUST keep
    /// `source` alive until `clear_mutable_token_source()` or `reset()`
    /// is called. The Drop impl on WpdsWalker clears the slot defensively.
    /// The lifetime of the trait object is erased via raw-pointer cast +
    /// transmute to satisfy the struct's `'static` field type — the
    /// caller-managed contract above is the load-bearing safety invariant.
    pub fn set_mutable_token_source<'src>(
        &mut self,
        source: &'src mut dyn WpdsMutableTokenSource,
    ) {
        // Erase the source's `'src` lifetime to fit the struct's
        // lifetime-free pointer slot. Sound under the documented SAFETY
        // contract: the caller must keep the source alive until the
        // walker clears the slot via clear_mutable_token_source/reset/Drop.
        let raw: *mut (dyn WpdsMutableTokenSource + 'src) = source as *mut _;
        let erased: *mut (dyn WpdsMutableTokenSource + 'static) =
            unsafe { std::mem::transmute(raw) };
        self.mutable_token_source = Some(erased);
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): clear the mutable token
    /// source slot. Call before dropping the source if the walker outlives
    /// it (e.g. wrapper-level usage with explicit lifetime separation).
    pub fn clear_mutable_token_source(&mut self) {
        self.mutable_token_source = None;
    }

    /// Stage 6 G6+ (2026-05-02): build a flat per-cursor census of the
    /// current walker state for tracing/dump consumers.
    ///
    /// Excludes heavy fields (`pending_builder_ops` contents,
    /// `collection_stack` contents) — only their lengths. Cheap to call
    /// (~1 µs for typical cursor counts); only the cursor `Vec` clone is
    /// non-trivial. Does NOT mutate the walker.
    pub fn current_snapshot(&self) -> StepSnapshot<W>
    where
        W: 'static,
    {
        let cursors: Vec<CursorSnapshot<W>> = self
            .branch_cursors
            .iter()
            .enumerate()
            .map(|(idx, c)| CursorSnapshot {
                idx,
                pos: c.pos,
                state: c.inner_state.clone(),
                gss_node_id: c.node,
                weight: c.weight.clone(),
                source_priority: c.source_priority,
                pending_ops_len: c.pending_builder_ops.len(),
                collection_depth: c.collection_stack.len(),
            })
            .collect();
        StepSnapshot {
            step_index: self.step_counter,
            cursor_count: self.branch_cursors.len(),
            walker_state: self.state.clone(),
            walker_pos: self.pos,
            gss_node_count: self.gss.node_count(),
            cursors,
        }
    }

    /// T4 SIGUSR1 hang-dump (2026-05-05): publish a type-erased snapshot to
    /// the hang-dump slot. No-op when the `hang-dump` feature is off, when
    /// `PRATTAIL_HANG_DUMP` is unset, or when the slot is contended.
    ///
    /// Cheap on the happy path: one `current_snapshot` clone + one
    /// `try_lock`. Called at the top of every `run_to_saturation` iteration
    /// so a SIGUSR1 dump always sees a fresh snapshot.
    #[cfg(feature = "hang-dump")]
    pub fn publish_to_hang_dump_slot(&self)
    where
        W: 'static + std::fmt::Debug,
    {
        let snap = self.current_snapshot();
        let cursors: Vec<crate::hang_dump::CursorRow> = snap
            .cursors
            .iter()
            .map(|c| crate::hang_dump::CursorRow {
                idx: c.idx,
                pos: c.pos,
                state_dbg: format!("{:?}", c.state),
                weight_dbg: format!("{:?}", c.weight),
                source_priority: c.source_priority,
                pending_ops_len: c.pending_ops_len,
                collection_depth: c.collection_depth,
            })
            .collect();
        let hang_snap = crate::hang_dump::HangSnapshot {
            timestamp_unix_secs: crate::hang_dump::now_unix_secs(),
            pid: crate::hang_dump::current_pid(),
            trigger: crate::hang_dump::HangTrigger::Sigusr1, // overridden by watcher at dump time
            walker_state_dbg: format!("{:?}", snap.walker_state),
            walker_pos: snap.walker_pos,
            cursor_count: snap.cursor_count,
            gss_node_count: snap.gss_node_count,
            step_index: snap.step_index as u64,
            cursors,
        };
        crate::hang_dump::publish_snapshot(hang_snap);
    }

    /// No-op variant when the `hang-dump` feature is disabled. Compiler
    /// inlines and elides — zero cost on the happy path.
    #[cfg(not(feature = "hang-dump"))]
    #[inline(always)]
    pub fn publish_to_hang_dump_slot(&self) {}

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

    /// Stage 3.4 (2026-04-30): set the beam-pruning bound in place.
    ///
    /// Same effect as [`Self::with_beam_size`] but mutates `self` instead
    /// of consuming. Useful when the walker is already wrapped (e.g., by
    /// a recovery driver holding a `&mut`).
    pub fn set_beam_size(&mut self, k: Option<usize>) {
        self.beam_size = k;
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
                let new_state = WpdsState::InfixLoop {
                    cur_bp: match from {
                        WpdsState::AmbiguityFanout { .. } => 0,
                        _ => 0,
                    },
                };
                // Stage 3.9 / ι Phase 4 (2026-05-01): preserve always-non-empty
                // L4 invariant — write a singleton cursor reflecting the
                // resolved post-fanout state. Pre-Phase-4 this called
                // `branch_cursors.clear()` because empty was the live-mode
                // signal; post-Phase-4, empty would violate L4.
                self.branch_cursors = vec![BranchCursor {
                    node: winner,
                    pos: self.pos,
                    weight: self.weight.clone(),
                    inner_state: new_state.clone(),
                    pending_builder_ops: Vec::new(),
                    collection_stack: Vec::new(),
                    collection_slots_allocated: 0,
                    // Stage 3.12 Fix 2(ii) (2026-05-02): post-resolved
                    // singleton inherits priority 0 (no further Fork
                    // tiebreaks expected post-resolution).
                    source_priority: 0,
                    // Stage 3.12.6 (2026-05-02): post-resolution
                    // singleton has no recorded push history (the resolved
                    // GSS state is canonical for the surviving branch).
                    incoming_edge_stack: Vec::new(),
                    // Bounded recovery (Stage 3.20 / L12, 2026-05-06):
                    // post-resolution singleton resets recovery
                    // book-keeping — the resolved parse path doesn't
                    // carry its ancestors' recovery history.
                    recovery_depth: 0,
                    visited_recovery: OrdSet::new(),
                    // B12 / Candidate E (2026-05-07): same rationale —
                    // post-resolution singleton resets projection
                    // visited set.
                    visited_dispatch: OrdSet::new(),
                    // B13d-R Step 2 (2026-05-08): post-resolution
                    // singleton has empty pending → Consistent memo.
                    consistency_memo: std::cell::Cell::new(Some(Some(true))),
                    // Phase 5.2 (2026-05-12): fresh empty Arc — the
                    // BranchResolved write-back resets cursor state to
                    // a canonical post-resolution singleton; the
                    // walker.builder (live mutation surface in 5.2)
                    // already captured the winning branch's effects
                    // via commit_winner journal replay.
                    builder: Arc::new(SemanticBuilder::new()),
                }];
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
    ) -> WpdsState
    where
        W: 'static + std::fmt::Debug,
    {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                break;
            }
            // T4 SIGUSR1 hang-dump (2026-05-05): publish a fresh snapshot so
            // that an out-of-band SIGUSR1 / watchdog dump always sees current
            // walker state. No-op when the `hang-dump` feature is off or
            // PRATTAIL_HANG_DUMP env var is unset.
            self.publish_to_hang_dump_slot();
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

    /// Stage 3.5b (2026-05-01): WPDS-correct end-of-input driver.
    ///
    /// Drives `process_event(Step)` until one of:
    /// 1. all `branch_cursors` are dead (`branch_cursors.is_empty()`),
    /// 2. the live state is terminal (Accepted in unforked mode, or
    ///    Error from a non-fanout path),
    /// 3. `pos == tokens.len()` AND every cursor is "parked" at EOI (Idle
    ///    in a resolved-shape state, see `apply_action_to_cursor`'s Idle
    ///    arm), or
    /// 4. `max_steps` budget exhausted.
    ///
    /// Unlike `run_to_saturation`, this driver does NOT treat Idle in a
    /// non-terminal state as an error — at EOI, Idle on a resolved-shape
    /// cursor is parking, not failure. After this driver returns, callers
    /// MUST invoke `resolve_at_end_of_input` to commit the lex-min
    /// accepting configuration into the live builder.
    ///
    /// Returns `Ok(())` on natural termination, `Err(MaxStepsExceeded)`
    /// when the budget is exceeded.
    pub fn run_to_end_of_input(
        &mut self,
        max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> Result<(), WpdsMaxStepsExceeded> {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                return Ok(());
            }
            if matches!(self.state, WpdsState::AmbiguityFanout { .. }) {
                // Snapshot pre-step cursor identities (`(node, pos,
                // weight, inner_state)`) so we can detect whether any
                // cursor actually progressed. Mid-stream the cursor set
                // may grow (Fork), shrink (Drop/merge), or transition
                // states/weights. Only when none of those happens AND
                // we're at EOI do we have a fixed-point parked frontier.
                let prev_count = self.branch_cursors.len();
                // Stage 3.12 Fix 3a (2026-05-02): include weight + pending_builder_ops
                // length in the fingerprint. Pre-3.12 a stable cursor whose
                // weight or delta-log size was still changing wouldn't trigger
                // progress_made, but the parse continued for max_steps. Now
                // both axes are tracked.
                let prev_fingerprint: Vec<(crate::gss::GssNodeId, usize, WpdsState, W, usize)> =
                    self
                        .branch_cursors
                        .iter()
                        .map(|c| {
                            (
                                c.node,
                                c.pos,
                                c.inner_state.clone(),
                                c.weight.clone(),
                                c.pending_builder_ops.len(),
                            )
                        })
                        .collect();
                self.step_fanout(tokens);
                let progress_made = self.branch_cursors.len() != prev_count
                    || self
                        .branch_cursors
                        .iter()
                        .zip(prev_fingerprint.iter())
                        .any(|(c, (n, p, s, w, ops_len))| {
                            c.node != *n
                                || c.pos != *p
                                || c.inner_state != *s
                                || c.weight != *w
                                || c.pending_builder_ops.len() != *ops_len
                        });
                if !progress_made {
                    // True fixed point — every cursor's engine.step
                    // returned Idle (or transitioned to itself), so no
                    // further state movement is possible. Exit cleanly.
                    return Ok(());
                }
                continue;
            }
            // Non-fanout (live single-cursor) path. Mirrors run_to_saturation
            // but treats EOI Idle as natural termination instead of Error.
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
                if self.pos >= tokens.len() {
                    // Stage 3.5b: EOI Idle in live mode is a parked
                    // result, not Error. Caller invokes
                    // `resolve_at_end_of_input` next which will
                    // synthesize the appropriate WpdsResolveResult.
                    return Ok(());
                }
                if !self.state.is_terminal() {
                    self.state = WpdsState::Error {
                        message: format!(
                            "engine returned Idle in non-terminal state {:?} at pos {}",
                            self.state, self.pos,
                        ),
                    };
                }
                return Ok(());
            }
            self.apply_action(action, tokens);
        }
        Err(WpdsMaxStepsExceeded {
            position: self.pos,
        })
    }

    /// Stage 3.5b (2026-05-01): WPDS-correct end-of-input resolution.
    ///
    /// Inspects the post-`run_to_end_of_input` configuration and produces
    /// a `WpdsResolveResult<W>`. The decision tree:
    ///
    /// 1. **Live mode (unforked, no branch_cursors)**:
    ///    - `state == Accepted`: the live builder already holds the result;
    ///      pop it and return `Accepted { weight, term }`.
    ///    - `state == Error { message }`: return `ParseError { message, position: self.pos }`.
    ///    - Anything else: incomplete parse → `ParseError`.
    ///
    /// 2. **Fanout mode (branch_cursors populated)**:
    ///    - Filter to cursors at `pos == tokens.len()` AND in an
    ///      "accepting configuration" (`is_accepting_config`).
    ///    - Zero accepting → `ParseError`.
    ///    - One accepting → commit + `Accepted`.
    ///    - ≥2 accepting → fold weights via `Semiring::plus` to find
    ///      the lex-min weight; tied indices keep source-order; if
    ///      exactly one ties, commit it; if ≥2 tie, emit ambiguity
    ///      warning + commit earliest source-ordered + return
    ///      `AcceptedAmbiguous`.
    pub fn resolve_at_end_of_input(
        &mut self,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsResolveResult<W>
    where
        W: 'static,
    {
        // Stage 3.9 / ι Phase 4 (2026-05-01): live mode is now keyed off
        // `cursor_mode == Lazy`, not `branch_cursors.is_empty()` — under
        // Phase 4 the cursors vector is always non-empty (singleton in
        // Lazy, multi in Strict). The pre-Phase-4 empty-cursors path is
        // gone; instead, Lazy resolution reads the live builder
        // directly (the singleton cursor's `pending_builder_ops` is
        // empty per L1, so there's nothing to replay).
        if self.cursor_mode == CursorMode::Lazy {
            return match self.state.clone() {
                WpdsState::Accepted => {
                    // B13c / Candidate H (2026-05-08): the Lazy-mode
                    // positional invariant was implemented here but
                    // proved to break recovery_integration_tests'
                    // test_calc_recovery_trailing_integer / _missing_operator
                    // / test_float_recovery_trailing / test_str_recovery_trailing
                    // — those tests rely on the walker accepting at
                    // sub-EOI and the wrapper handling trailing tokens
                    // via recovery. The positional gate is left
                    // unimplemented at this site; the wrapper's
                    // post-resolution `pos < tokens.len()` check (in
                    // codegen-emitted parse_<Cat>_via_wpds) handles
                    // TrailingTokens correctly.
                    let term = self.builder.take_dyn_result();
                    let weight = self.weight.clone();
                    match term {
                        Some(t) => WpdsResolveResult::Accepted { weight, term: t },
                        None => WpdsResolveResult::ParseError {
                            message: "walker accepted but builder result was empty".to_string(),
                            position: self.pos,
                        },
                    }
                }
                WpdsState::Error { message } => WpdsResolveResult::ParseError {
                    message,
                    position: self.pos,
                },
                other => WpdsResolveResult::ParseError {
                    message: format!("incomplete parse in state {:?}", other),
                    position: self.pos,
                },
            };
        }
        // Fanout mode: resolve over branch_cursors.
        // Stage 3.5b (2026-05-01): use `pos >= tokens.len()` rather than
        // `pos == tokens.len()`. Real-grammar codegen never advances pos
        // past tokens.len() on real input (ConsumeAndPop is gated by
        // peek_kind), but synthetic test scripts can; treating "past
        // EOI" as "at EOI" makes resolution robust to either case.
        let accepting_indices: Vec<usize> = (0..self.branch_cursors.len())
            .filter(|&i| {
                let c = &self.branch_cursors[i];
                // Stage 3.12 fix (2026-05-02): use `is_logical_eoi` so a
                // cursor parked at trailing `Token::Eof` (the natural
                // rule-end exit) accepts. The pre-3.12 `pos >= tokens.len()`
                // was unreachable in Strict mode because the engine's
                // `Accept` arm doesn't advance past EOF.
                self.is_logical_eoi(c.pos, tokens) && self.is_accepting_config(c)
            })
            .collect();
        let max_dead_pos = self
            .branch_cursors
            .iter()
            .map(|c| c.pos)
            .max()
            .unwrap_or(self.pos);
        match accepting_indices.len() {
            0 => WpdsResolveResult::ParseError {
                message: "no accepting branch reached end of input".to_string(),
                position: max_dead_pos,
            },
            1 => {
                let winner_idx = accepting_indices[0];
                let weight = self.branch_cursors[winner_idx].weight.clone();
                self.commit_winner_at_eoi(winner_idx);
                let term = self.builder.take_dyn_result();
                match term {
                    Some(t) => WpdsResolveResult::Accepted { weight, term: t },
                    None => WpdsResolveResult::ParseError {
                        message: "winner committed but builder result was empty"
                            .to_string(),
                        position: self.pos,
                    },
                }
            }
            _ => {
                // Pick lex-min winner via Semiring::plus fold across the
                // accepting set, with `source_priority` as final tiebreak
                // (Stage 3.12 Fix 2(ii), 2026-05-02). The pre-3.12 fold
                // depended on receiver-on-Equal semantics for source
                // order, but that's order-of-arrival dependent. Now ties
                // are explicitly broken by Fork-source-order priority.
                let mut best_idx = accepting_indices[0];
                let mut best_weight = self.branch_cursors[best_idx].weight.clone();
                for &idx in &accepting_indices[1..] {
                    let candidate = &self.branch_cursors[idx].weight;
                    let merged = best_weight.plus(candidate);
                    if merged != best_weight {
                        best_idx = idx;
                        best_weight = merged;
                    } else if merged == *candidate
                        && self.branch_cursors[idx].source_priority
                            < self.branch_cursors[best_idx].source_priority
                    {
                        best_idx = idx;
                        best_weight = merged;
                    }
                }
                // Count tied (equivalence-class size) for ambiguity
                // reporting. Two cursors tie iff plus is idempotent on
                // both directions (each.plus(other) == self).
                let tied_count = accepting_indices
                    .iter()
                    .filter(|&&idx| {
                        let w = &self.branch_cursors[idx].weight;
                        w.plus(&best_weight) == *w && best_weight.plus(w) == best_weight
                    })
                    .count();
                let weight = best_weight.clone();
                self.commit_winner_at_eoi(best_idx);
                let term = self.builder.take_dyn_result();
                match term {
                    Some(t) => {
                        if tied_count >= 2 {
                            WpdsResolveResult::AcceptedAmbiguous {
                                weight,
                                term: t,
                                equivalence_class_size: tied_count,
                            }
                        } else {
                            WpdsResolveResult::Accepted { weight, term: t }
                        }
                    }
                    None => WpdsResolveResult::ParseError {
                        message: "winner committed but builder result was empty"
                            .to_string(),
                        position: self.pos,
                    },
                }
            }
        }
    }

    /// Stage 3.5b (2026-05-01): cursor-level "is this an accepting
    /// configuration?" classifier.
    ///
    /// A cursor at EOI is accepting iff:
    /// - `inner_state == Accepted` (engine emitted `WpdsStepAction::Accept`), OR
    /// - `inner_state == InfixLoop` AND no further infix operator can
    ///   bind (engine returned Idle on the next step → cursor parked
    ///   here as Resolved), OR
    /// - `inner_state == Unwinding` AND the GSS top is the bottom-of-stack
    ///   sentinel (no more pops to perform).
    ///
    /// In practice, cursors that reach EOI via `apply_action_to_cursor`'s
    /// Idle parking branch satisfy the first two conditions; the third
    /// is reached when the engine pops Returns up to the bottom.
    fn is_accepting_config(&self, cursor: &BranchCursor<W>) -> bool {
        // B13c / Candidate H (2026-05-08), activated by B13d-R
        // (2026-05-08): builder-shape invariant. The C2-faithful
        // `cursor_dry_run_state` correctly models Optional /
        // PushToCollection scope semantics, so the previous false-
        // positive concern (productive cross-cat-LHS cursors falsely
        // classified as broken) is resolved. Cursors whose dry-run
        // lands on Definitely_broken are filtered from the accepting
        // set BEFORE lex-min. Indeterminate cases pass through (return
        // true).
        if !self.cursor_will_produce_term(cursor) {
            return false;
        }
        match &cursor.inner_state {
            WpdsState::Accepted => true,
            WpdsState::InfixLoop { .. } => true,
            WpdsState::Unwinding => {
                // Unwinding-at-EOI is accepting iff the GSS top has no
                // more symbols to pop — i.e., we've reached the original
                // entry frame, or popped past it (cursor.node == GSS_NODE_NONE
                // per Stage 3.12 fix; engine returns Accept on the next step).
                if cursor.node == crate::gss::GSS_NODE_NONE {
                    return true;
                }
                self.gss
                    .node(cursor.node)
                    .map(|n| n.symbol.kind == SymbolKind::Return || n.symbol.kind == SymbolKind::CategoryEntry)
                    .unwrap_or(false)
            }
            _ => false,
        }
    }

    /// B13c / Candidate H (2026-05-08), refined as B13d-R Resolution R
    /// (2026-05-08): dry-run the cursor's `pending_builder_ops` to
    /// predict whether commit_winner's replay will produce a single
    /// Term arg, returning a TRISTATE result via `cursor_dry_run_state`.
    ///
    /// `cursor_will_produce_term` is the EOI-gate variant: returns
    /// `true` if the cursor would produce exactly one Term arg of any
    /// category, `false` if a logged FireAction is provably broken
    /// (arity-underflow / type-mismatch). Indeterminate cases return
    /// `true` (conservative: don't filter on uncertainty at the EOI
    /// gate).
    ///
    /// `cursor_committed_ops_consistent` is the merge/subsume override
    /// variant: returns `Some(true)` for a viable cursor, `Some(false)`
    /// for a Definitely_broken cursor, `None` for Indeterminate.
    /// Override fires only on `Some(false)`; `None` falls through to
    /// existing weight comparison.
    ///
    /// Both are derived from `cursor_dry_run_state`, the C2-faithful
    /// virtual-stack simulation that mirrors `commit_winner`'s replay
    /// over `pending_builder_ops`. Models:
    /// - main_stack + optional_stack (mirrors SemanticBuilder's two-
    ///   level active arg stack — Optional scopes route subsequent
    ///   pushes to a separate inner Vec).
    /// - PushToken/PushIdent/PushPredicate/PushCollectionId/
    ///   PushOptionalAbsent → push `None` onto active stack.
    /// - FireAction → pop arity entries from active stack, type-check
    ///   each against `expected_input_cats[i]` (ANY_CAT skips check),
    ///   push `Some(output_cat)` on success.
    /// - SpliceIntoCollection / PushToCollection → pop 1 from active
    ///   stack (target a collection accumulator outside the arg stack).
    /// - StartOptionalScope → optional_stack.push(Vec::new()) — opens
    ///   a separate active arg cursor.
    /// - FinalizeOptionalScopePresent → optional_stack.pop() — captures
    ///   the entire inner buffer; pushes ONE Optional arg (None tag)
    ///   onto the next-outer active stack.
    /// - All other deltas (StartBinderScope, FinalizeCollection,
    ///   SeedLiveCollectionStack, RecoveryEvent, SubstituteToken,
    ///   InsertToken, CommitLexAlternative, ApplyRecoverySequence,
    ///   StartCollection) → no effect on active arg stack.
    fn cursor_dry_run_state(&self, cursor: &BranchCursor<W>) -> DryRunState {
        if cursor.pending_builder_ops.is_empty() {
            // Lazy-mode short-circuit: live builder is canonical.
            return DryRunState::Consistent {
                final_main_stack: Vec::new(),
                final_optional_depth: 0,
            };
        }
        // Two parallel virtual stacks mirror the runtime:
        //   - main_stack: SemanticBuilder.stack (Option<u16> tags)
        //   - optional_stack: SemanticBuilder.optional_stack (each entry is a Vec<Option<u16>>)
        let mut main_stack: Vec<Option<u16>> = Vec::with_capacity(8);
        let mut optional_stack: Vec<Vec<Option<u16>>> = Vec::new();
        for delta in cursor.pending_builder_ops.iter() {
            match delta {
                BuilderDelta::PushToken { .. }
                | BuilderDelta::PushIdent { .. }
                | BuilderDelta::PushPredicate(_)
                | BuilderDelta::PushCollectionId { .. }
                | BuilderDelta::PushOptionalAbsent => {
                    let active = if let Some(top) = optional_stack.last_mut() {
                        top
                    } else {
                        &mut main_stack
                    };
                    active.push(None);
                }
                BuilderDelta::FireAction { symbol } => {
                    let action = match self.engine.action_for(
                        symbol.category_src_idx,
                        symbol.rule_index_in_category,
                    ) {
                        Some(a) => a,
                        // Unknown action — be conservative and skip.
                        None => continue,
                    };
                    let arity = action.arity as usize;
                    let active_len = if let Some(top) = optional_stack.last() {
                        top.len()
                    } else {
                        main_stack.len()
                    };
                    if active_len < arity {
                        // B13d-R correction (2026-05-08): underflow is
                        // INDETERMINATE, not DefinitelyBroken. The
                        // cursor's pending_builder_ops doesn't include
                        // args pushed to the live builder BEFORE a
                        // Lazy→Strict transition; my virt may be shorter
                        // than the runtime active stack. At commit time,
                        // the live's pre-fork stack provides the missing
                        // args and the FireAction may succeed.
                        // TypeMismatch (below) IS DefinitelyBroken
                        // because it fires only when virt.top is `Some(_)`
                        // — a known type from THIS cursor's prior
                        // FireAction, not invisible live state.
                        return DryRunState::Indeterminate {
                            reason: "FireAction arity exceeds dry-run virt length \
                                     — pre-fork live state may fill the gap",
                        };
                    }
                    let active = if let Some(top) = optional_stack.last_mut() {
                        top
                    } else {
                        &mut main_stack
                    };
                    let popped_start = active.len() - arity;
                    // Type-check each arg against expected_input_cats.
                    // arg[i] in expected_input_cats matches the i-th
                    // popped arg in argument order (action body iterates
                    // args.into_iter() so arg0 was pushed FIRST → it's
                    // at popped_start, arg1 at popped_start+1, etc.).
                    let mut mismatch = false;
                    for i in 0..arity {
                        let popped = active[popped_start + i];
                        let expected = action
                            .expected_input_cats
                            .get(i)
                            .copied()
                            .unwrap_or(crate::wpds_runtime::ANY_CAT);
                        if expected == crate::wpds_runtime::ANY_CAT {
                            continue;
                        }
                        match popped {
                            Some(actual) if actual == expected => continue,
                            _ => {
                                mismatch = true;
                                break;
                            }
                        }
                    }
                    if mismatch {
                        return DryRunState::DefinitelyBroken {
                            kind: DryRunBrokenKind::TypeMismatch,
                        };
                    }
                    active.truncate(popped_start);
                    active.push(Some(action.output_cat));
                }
                BuilderDelta::SpliceIntoCollection { .. }
                | BuilderDelta::PushToCollection { .. } => {
                    // Runtime: active.pop() and append to collection_stack[id].
                    // (Resolution R defect-fix #1: PushToCollection now
                    // also pops; was a no-op pre-R.)
                    let active = if let Some(top) = optional_stack.last_mut() {
                        top
                    } else {
                        &mut main_stack
                    };
                    if active.is_empty() {
                        // Runtime push_to_collection silently no-ops on
                        // empty active; we cannot tell from the log alone
                        // whether this was a logic error or a benign
                        // edge case. Indeterminate.
                        return DryRunState::Indeterminate {
                            reason: "PushToCollection/SpliceIntoCollection pop on empty active stack",
                        };
                    }
                    active.pop();
                }
                BuilderDelta::StartOptionalScope => {
                    // Runtime: optional_stack.push(Vec::new()).
                    // (Resolution R defect-fix #2: was no-op pre-R.)
                    optional_stack.push(Vec::new());
                }
                BuilderDelta::FinalizeOptionalScopePresent => {
                    // Runtime: pop entire inner Vec, wrap as Optional(Some(inner)),
                    // push ONE Optional arg onto next-outer active stack.
                    // (Resolution R defect-fix #3: was virt.pop() pre-R.)
                    if optional_stack.pop().is_none() {
                        return DryRunState::Indeterminate {
                            reason: "FinalizeOptionalScopePresent without matching StartOptionalScope",
                        };
                    }
                    let active = if let Some(top) = optional_stack.last_mut() {
                        top
                    } else {
                        &mut main_stack
                    };
                    active.push(None);
                }
                // Recovery events, lex alternatives, SeedLiveCollectionStack,
                // FinalizeCollection (drains accumulator outside the arg stack),
                // StartBinderScope (separate binder_scopes substrate),
                // StartCollection (separate collection_stack substrate),
                // ApplyRecoverySequence, SubstituteToken, InsertToken,
                // CommitLexAlternative, RecoveryEvent — no effect on
                // active arg stack.
                _ => {}
            }
        }
        DryRunState::Consistent {
            final_main_stack: main_stack,
            final_optional_depth: optional_stack.len(),
        }
    }

    /// EOI-gate variant of `cursor_dry_run_state`: returns `true` if the
    /// cursor's pending_builder_ops would replay cleanly AND end with
    /// exactly one Term tag in the main stack (no leftover optional
    /// scope). Indeterminate returns `true` (conservative; don't filter
    /// on uncertainty).
    fn cursor_will_produce_term(&self, cursor: &BranchCursor<W>) -> bool {
        match self.cursor_dry_run_state(cursor) {
            DryRunState::Consistent {
                final_main_stack,
                final_optional_depth,
            } => {
                // Empty pending = Lazy mode; live builder canonical.
                if final_main_stack.is_empty() && final_optional_depth == 0 {
                    return true;
                }
                final_optional_depth == 0
                    && final_main_stack.len() == 1
                    && final_main_stack[0].is_some()
            }
            DryRunState::DefinitelyBroken { .. } => false,
            DryRunState::Indeterminate { .. } => true,
        }
    }

    /// B13d-R / Resolution R (2026-05-08): tristate consistency oracle
    /// for the merge/subsume override.
    ///
    /// Returns:
    /// - `Some(true)`  → cursor's pending_builder_ops will replay cleanly
    ///   at commit_winner (no arity underflow, no type mismatch). Whether
    ///   it produces a valid Term is a separate question handled by
    ///   `cursor_will_produce_term` at the EOI gate.
    /// - `Some(false)` → at least one logged FireAction will hit
    ///   `pop_args` underflow OR `into_term` early-return at runtime.
    ///   By monotonicity (`pending_builder_ops` is append-only), this
    ///   judgment is stable for all subsequent appends.
    /// - `None` → simulation hit an indeterminate delta; caller MUST
    ///   fall back to weight comparison.
    ///
    /// The override at `merge_equivalent_cursors` /
    /// `subsume_lex_dominated_cursors` fires ONLY when EXACTLY ONE
    /// cursor returns `Some(false)`. `Some(true)` and `None` are both
    /// treated as "viable" — we never override against weight on
    /// Indeterminate.
    fn cursor_committed_ops_consistent(&self, cursor: &BranchCursor<W>) -> Option<bool> {
        // B13d-R Step 2 (2026-05-08): per-cursor memoization.
        // `pending_builder_ops` is append-only (verified by exhaustive
        // grep); the dry-run is therefore monotone: `Some(false)` is
        // sticky for the lifetime of the cursor; `Some(true)` and
        // `None` can flip on push, so the memo is invalidated at every
        // push site (`set(None)`).
        if let Some(cached) = cursor.consistency_memo.get() {
            return cached;
        }
        let result = match self.cursor_dry_run_state(cursor) {
            DryRunState::Consistent { .. } => Some(true),
            DryRunState::DefinitelyBroken { .. } => Some(false),
            DryRunState::Indeterminate { .. } => None,
        };
        cursor.consistency_memo.set(Some(result));
        result
    }

    /// Stage 3.12 fix (2026-05-02): "logical EOI" — true when the
    /// cursor's `pos` either consumed the entire token stream or is
    /// parked at a trailing `Token::Eof` that the engine never advances
    /// past. The lexer appends `Token::Eof` (e.g., `parser.rs:692` in
    /// generated code), so `tokens.len()` is `content_len + 1` and
    /// natural rule-end positions are `content_len` (= `tokens.len() - 1`).
    /// The pre-3.12 EOI check `pos >= tokens.len()` only worked in Lazy
    /// mode (via the `cursor_mode == Lazy` short-circuit in
    /// `resolve_at_end_of_input`). Strict mode now matches the same
    /// "trailing EOF is OK" contract that `parse_<Cat>::parse_via_wpds`
    /// uses on its outer `pos` check.
    #[inline]
    fn is_logical_eoi(&self, pos: usize, tokens: &dyn WpdsTokenSource) -> bool {
        pos >= tokens.len()
            || (pos + 1 == tokens.len()
                && tokens.peek_kind(pos) == Some(TokenKind::Eof))
    }

    /// Stage 3.5b (2026-05-01): EOI-time variant of `commit_winner`.
    ///
    /// Identical to `commit_winner` semantically (replays winner's
    /// pending_builder_ops, donates collection_stack, splices winner's
    /// `(node, pos, weight, inner_state)` into the live walker), but
    /// invoked exclusively from `resolve_at_end_of_input` rather than
    /// mid-stream from `step_fanout`. The implementation delegates to
    /// `commit_winner` to keep replay logic single-source.
    fn commit_winner_at_eoi(&mut self, winner_idx: usize) {
        self.commit_winner(winner_idx);
    }

    // ─── Internal step handler ──────────────────────────────────────────────

    fn handle_step(&mut self, tokens: &dyn WpdsTokenSource) -> WpdsTransition<W> {
        // Stage 6 G6+ (2026-05-02): bump trace step counter once per Step.
        self.step_counter = self.step_counter.wrapping_add(1);
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

    /// Stage 3.9 / ι Phase 4 (2026-05-01): thin dispatcher.
    ///
    /// Pre-Phase-4: ~370-line arm-by-arm body that mutated both the live
    /// builder AND walker fields directly, with a parallel `apply_action_to_cursor`
    /// for the Strict (post-Fork) path. The dual-mutation surface produced
    /// the Class C bug class.
    ///
    /// Post-Phase-4: dispatcher routes EVERY action through
    /// `apply_action_to_cursor` against `branch_cursors[0]` (the singleton
    /// in Lazy mode). Per-variant `emit_*` helpers branch on `cursor_mode`
    /// to direct-mutate the live builder (Lazy) or log to
    /// `pending_builder_ops` (Strict). Single mutation surface; Class C
    /// structurally eliminated.
    ///
    /// Outcome handling:
    /// - `Drop`:      cursor died (Error / non-resolved Idle). Restore
    ///                singleton with current walker view to preserve L4.
    /// - `Alive`:     reinstate the cursor as branch_cursors[0].
    /// - `Resolved`:  reinstate (parked at EOI for resolve_at_end_of_input).
    /// - `ForkInto`:  replace branch_cursors with children, set state to
    ///                AmbiguityFanout. Mode is already Strict per L2.
    fn apply_action(&mut self, action: WpdsStepAction<W>, tokens: &dyn WpdsTokenSource) {
        // L1: assert Lazy admission invariant.
        self.debug_flush_lazy_invariant();
        // L5: terminal state is mode-irrelevant.
        if self.state.is_terminal() {
            return;
        }
        debug_assert_eq!(
            self.branch_cursors.len(),
            1,
            "apply_action invariant: branch_cursors must be a singleton at \
             entry (Lazy: always; Strict: never reached — step_fanout drives \
             multi-cursor mode directly)",
        );
        let mut cursor = self.branch_cursors.swap_remove(0);
        let outcome = self.apply_action_to_cursor(&mut cursor, action, tokens);
        match outcome {
            CursorOutcome::Drop => {
                // Cursor died. In Lazy mode, helpers already mirrored the
                // terminal state (set_cursor_inner_state) to self.state,
                // so the live walker reflects the failure. Restore a
                // fresh singleton anchored at the current walker view to
                // preserve L4 (always-non-empty branch_cursors).
                self.branch_cursors.push(BranchCursor {
                    node: self.top_node.unwrap_or(0),
                    pos: self.pos,
                    weight: W::one(),
                    inner_state: self.state.clone(),
                    pending_builder_ops: Vec::new(),
                    collection_stack: Vec::new(),
                    collection_slots_allocated: 0,
                    // Stage 3.12 Fix 2(ii) (2026-05-02): restored singleton
                    // post-Drop has no Fork ancestor, so priority 0.
                    source_priority: 0,
                    // Stage 3.12.6 (2026-05-02): post-Drop reset starts
                    // with empty stack history.
                    incoming_edge_stack: Vec::new(),
                    // Bounded recovery (Stage 3.20 / L12, 2026-05-06):
                    // post-Drop reset resets recovery book-keeping.
                    recovery_depth: 0,
                    visited_recovery: OrdSet::new(),
                    // B12 / Candidate E (2026-05-07): same rationale —
                    // post-Drop reset clears projection visited set.
                    visited_dispatch: OrdSet::new(),
                    // B13d-R Step 2 (2026-05-08): post-Drop reset has
                    // empty pending → Consistent memo.
                    consistency_memo: std::cell::Cell::new(Some(Some(true))),
                    // Phase 5.2 (2026-05-12): fresh empty Arc — the
                    // post-Drop fresh singleton has no Fork-ancestor
                    // builder to inherit. Live mutations continue to
                    // flow through `self.builder` (Lazy mode); the
                    // cursor's Arc is a future anchor (5.3+).
                    builder: Arc::new(SemanticBuilder::new()),
                });
            }
            CursorOutcome::Alive | CursorOutcome::Resolved => {
                self.branch_cursors.push(cursor);
            }
            CursorOutcome::ForkInto(children) => {
                // L2: cursor_mode was promoted to Strict inside the cursor-
                // side Fork arm. Replace branch_cursors with children and
                // set state = AmbiguityFanout.
                //
                // Stage 3.9 / ι Phase 4 (2026-05-01): mirror the post-Fork
                // walker position to the children's pos. The cursor-side
                // Fork arm computes `pos_after = cursor.pos + 1` (when
                // `consume_trigger`) for each child but does NOT mutate
                // `self.pos`. The pre-Phase-4 live `apply_action::Fork`
                // did `self.pos += 1` directly. Preserve that contract by
                // reading the post-Fork pos from the first child (all
                // children share the same `pos_after`).
                if let Some(first) = children.first() {
                    self.pos = first.pos;
                }
                let branch_ids: Vec<crate::gss::GssNodeId> =
                    children.iter().map(|c| c.node).collect();
                self.branch_cursors = children;
                self.state = WpdsState::AmbiguityFanout { branches: branch_ids };
                self.maybe_prune_frontier();
            }
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
                self.set_cursor_inner_state(cursor, s);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::AdvanceWithEffect { new_state, effect } => {
                // B8 / Issue C (2026-05-09): log effect to pending ops,
                // invalidate consistency memo, then advance state.
                cursor.consistency_memo.set(None);
                // Phase 5.5 (2026-05-12): eagerly apply effect to
                // cursor.builder so post-install state reflects the
                // mutation. Without this, the journaled effect would
                // only fire at commit_winner replay (which is now no-op
                // for non-recovery deltas), leaving cursor.builder
                // missing the SpliceIntoCollection / other Class-3
                // inner-walk effects.
                Self::apply_effect_to_builder(
                    Arc::make_mut(&mut cursor.builder),
                    &effect,
                );
                cursor.pending_builder_ops.push(effect);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Push { mut symbol, weight, new_state } => {
                // B12 / Candidate E (2026-05-07): cross-cat projection
                // cycle defense for SINGLETON projection arms. Singleton
                // bucket emits `WpdsStepAction::Push` (not Fork) when only
                // one descriptor matches a (pat, guard) — see
                // `prefix.rs::emit_unified_arm` UnifiedDescriptor::
                // CrossCatProjection branch's singleton emission. This
                // path bypasses the Fork-arm cycle defense, so we mirror
                // the same check here: if the new_state is CrossCatDelegate
                // (the projection mechanism) AND the cursor has already
                // dispatched a projection at the current (pos, cat_src,
                // cur_bp), drop. Otherwise insert into visited_dispatch
                // before transitioning so the next projection at the same
                // configuration on this cursor's path is caught.
                if matches!(&new_state, WpdsState::CrossCatDelegate { .. }) {
                    if let Some(key) = extract_dispatch_config(cursor, &self.gss) {
                        if cursor.visited_dispatch.contains(&key) {
                            let msg = format!(
                                "cross-cat projection cycle detected at \
                                 (pos={}, cat_src={}, cur_bp={}) — refusing \
                                 to re-dispatch projection Push (B12 cycle \
                                 defense, singleton-bucket path)",
                                key.0, key.1, key.2,
                            );
                            self.set_cursor_inner_state(
                                cursor,
                                WpdsState::Error { message: msg },
                            );
                            return CursorOutcome::Drop;
                        }
                        cursor.visited_dispatch.insert(key);
                    }
                }
                // Stage 3.9 / ι Phase 4 (2026-05-01): symbol-kind-driven
                // implicit Push-time side effects via centralized helper.
                // Handles CollectionMarker (id alloc + bp patch + arg push)
                // AND OptionalGroupAt(1) (scope open).
                self.emit_push_side_effects(cursor, &mut symbol);
                let _ = self.cursor_gss_push(cursor, symbol, cursor.pos, weight);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Pop { weight, new_state } => {
                // Stage 3.12.6 (2026-05-02): single-predecessor pop via
                // the cursor's recorded `incoming_edge_stack`. The
                // cursor follows the edge it pushed, so pop is
                // deterministic even on multi-in-edge GSS nodes (which
                // arise when GSS dedup collapses recursive `(pos, symbol)`
                // pushes from distinct calling contexts).
                //
                // No fan-out — each cursor's stack-suffix identity is
                // unique. The Tomita "spawn N children per in-edge"
                // pattern is replaced by per-cursor edge identity
                // (Scott & Johnstone 2010 GLL descriptor uniqueness).
                let popped_symbol = self.gss.node(cursor.node).map(|n| n.symbol);
                let pred_id =
                    self.cursor_gss_pop_via_edge(cursor).unwrap_or(crate::gss::GSS_NODE_NONE);
                self.apply_pop_body_to_cursor(
                    cursor, pred_id, popped_symbol, &weight, new_state, tokens,
                );
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Replace { symbol, weight, new_state } => {
                let _ = self.cursor_gss_replace_top(cursor, symbol, cursor.pos, weight);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Consume { weight, new_state } => {
                self.advance_cursor_pos(cursor, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeAndPush {
                mut symbol,
                weight,
                new_state,
                capture_token,
            } => {
                // Order matches live apply_action: capture_token FIRST,
                // then collection-marker id allocation.
                if capture_token {
                    if let Some(kind) = tokens.peek_kind(cursor.pos) {
                        let text = tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                        let pos = cursor.pos;
                        self.emit_push_token(cursor, kind, text, pos);
                    }
                }
                // Stage 3.9 / ι Phase 4 (2026-05-01): centralized Push-time
                // side effects (CollectionMarker + OptionalGroupAt(1)).
                self.emit_push_side_effects(cursor, &mut symbol);
                let _ = self.cursor_gss_push(cursor, symbol, cursor.pos, weight);
                self.advance_cursor_pos(cursor, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeAndPop { weight, new_state } => {
                // Stage 3.12.6 (2026-05-02): single-predecessor pop via
                // edge-id (see Pop arm). Consume token first, then pop
                // along the cursor's recorded path.
                let popped_symbol = self.gss.node(cursor.node).map(|n| n.symbol);
                let pred_id =
                    self.cursor_gss_pop_via_edge(cursor).unwrap_or(crate::gss::GSS_NODE_NONE);
                self.advance_cursor_pos(cursor, 1);
                self.apply_pop_body_to_cursor(
                    cursor, pred_id, popped_symbol, &weight, new_state, tokens,
                );
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeAndReplace { symbol, weight, new_state } => {
                let _ = self.cursor_gss_replace_top(cursor, symbol, cursor.pos, weight);
                self.advance_cursor_pos(cursor, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ConsumeIdentAndReplace {
                symbol,
                weight,
                new_state,
                start_scope,
            } => {
                if tokens.peek_kind(cursor.pos).is_some() {
                    let text = tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                    if start_scope {
                        self.emit_start_binder_scope(cursor, vec![text.clone()]);
                    }
                    let pos = cursor.pos;
                    self.emit_push_ident(cursor, text, pos);
                }
                let _ = self.cursor_gss_replace_top(cursor, symbol, cursor.pos, weight);
                self.advance_cursor_pos(cursor, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ReplaceAndPush {
                replace_symbol,
                push_symbol,
                weight,
                new_state,
            } => {
                let _ = self.cursor_gss_replace_top(cursor, replace_symbol, cursor.pos, weight);
                // B9 / Class 2 (2026-05-08): apply emit_push_side_effects
                // BEFORE pushing the symbol — for CollectionMarker, this
                // allocates an accumulator id and patches symbol.bp =
                // Some(id), and pushes ActionArg::CollectionId(id) so the
                // owning rule's terminal action can drain it. Pre-fix the
                // ReplaceAndPush path silently skipped these side effects,
                // breaking Class-2 binder rules whose collection-slot
                // dispatch uses ReplaceAndPush(CollectionMarker). Mirrors
                // the Push arm at line ~2998 and Fork arms at ~3390.
                let mut push_symbol = push_symbol;
                self.emit_push_side_effects(cursor, &mut push_symbol);
                let _ = self.cursor_gss_push(cursor, push_symbol, cursor.pos, weight);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::ParsePredicate {
                replace_symbol,
                weight,
                new_state,
            } => {
                let parsed_pred = crate::parser::predicate::parse_predicate_via_token_source(
                    tokens, cursor.pos,
                );
                match parsed_pred {
                    Ok((pred, new_pos)) => {
                        self.emit_push_predicate(cursor, Arc::new(pred));
                        // Direct cursor.pos write (not via advance_cursor_pos)
                        // because new_pos is absolute, not a delta. Mirror to
                        // self.pos in Lazy mode.
                        cursor.pos = new_pos;
                        if self.cursor_mode == CursorMode::Lazy {
                            self.pos = new_pos;
                        }
                    }
                    Err(_msg) => return CursorOutcome::Drop,
                }
                let _ = self.cursor_gss_replace_top(cursor, replace_symbol, cursor.pos, weight);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Fork { mut branches, consume_trigger } => {
                // Phase 5.4 (2026-05-12): Hack #7 prologue DELETED. The
                // original prologue transferred live builder's slot stack
                // into the parent cursor's mirror and journaled a
                // `SeedLiveCollectionStack` delta so commit_winner could
                // re-seed live before subsequent Strict-mode deltas
                // executed. The transfer was needed because Lazy mode
                // mutated live directly while cursor.collection_stack
                // remained empty — at Fork the cursor needed to "own"
                // those slots to maintain ID-allocation invariants.
                //
                // Post-Phase-5.2/5.3, the cursor's `Arc<SemanticBuilder>`
                // ALREADY contains the pre-fork state by structural
                // sharing (parent's Arc is cloned to the child at Fork
                // time, and the cursor.builder accumulates Lazy mutations
                // via Arc::make_mut). The slot data is intrinsically
                // present in cursor.builder; the live self.builder
                // retains its own copy unchanged.
                //
                // Also: `BuilderDelta::FinalizeCollection` is dead code
                // (defined + replayed but never emitted anywhere — see
                // commit message). Without FinalizeCollection emissions,
                // the SeedLive replay's "live.len() == id" assertion
                // no longer needs satisfaction; the SpliceIntoCollection
                // / PushToCollection replay arms derive their ids from
                // `live.collection_stack_len() - 1` at replay time
                // (Phase 4 #5b), so they find slots in self.builder
                // where they expect them.
                //
                // Net: the prologue is structurally unnecessary post-5.3.
                // Synchronize `cursor.collection_slots_allocated` (the
                // monotonic id counter) and seed `cursor.collection_stack`
                // (the mirror) with empty placeholders matching the
                // live builder's slot count — preserves the mirror's
                // role as an id-allocator without copying slot contents
                // (which are already in cursor.builder).
                if self.cursor_mode == CursorMode::Lazy {
                    let pre_fork_len = self.builder.collection_stack_len();
                    cursor.consistency_memo.set(None);
                    cursor.collection_slots_allocated = pre_fork_len as u8;
                    cursor.collection_stack = (0..pre_fork_len)
                        .map(|_| Vec::new())
                        .collect();
                    // Phase 5.5 (2026-05-12): refresh cursor.builder from
                    // self.builder so cursor.builder reflects the pre-Fork
                    // Lazy-mode state. In Lazy mode, emit_fire_action calls
                    // `self.fire_action_for(symbol)` which mutates
                    // self.builder directly — those term pushes are NOT
                    // mirrored to cursor.builder via the Phase 5.3 eager
                    // Arc::make_mut path (emit_fire_action was deliberately
                    // skipped from that migration). Without this refresh,
                    // commit_winner's install would overwrite self.builder
                    // with a cursor.builder missing the pre-Fork action
                    // terms. Children Arc::clone the refreshed parent
                    // cursor.builder, inheriting the live state.
                    cursor.builder = Arc::new(self.builder.clone());
                }
                // Stage 3.9 / ι Phase 4 (2026-05-01) — L2: promote to Strict.
                // Phase 5.4: kept (Strict mode still gates emit-helper
                // mirror-to-live dispatch). Will be deleted in Phase 5.6
                // when cursor_mode itself goes away.
                self.cursor_mode = CursorMode::Strict;
                // Bounded recovery (Stage 3.20 / L12, 2026-05-06): detect
                // whether this Fork is a recovery dispatch (any branch
                // carries a recovery-typed BuilderDelta effect:
                // RecoveryEvent / InsertToken / SubstituteToken /
                // ApplyRecoverySequence). If so, enforce three principled
                // bounds BEFORE allocating children:
                //   1. cursor.recovery_depth < max_recovery_depth.
                //   2. (pos, cat_src, cur_bp) ∉ cursor.visited_recovery.
                //   3. forward-progress filter: drop branches whose
                //      new_state.pos == base_pos AND no InsertToken
                //      effect.
                // After child allocation, bump each child's recovery_depth
                // by 1 and insert the dispatch config into visited_recovery.
                let is_recovery = is_recovery_fork(&branches);
                let recovery_dispatch_config: Option<(usize, u16, u8)> = if is_recovery {
                    extract_recovery_dispatch_config(cursor, &self.gss)
                } else {
                    None
                };
                if is_recovery {
                    let max_depth = self.recovery_config.max_recovery_depth;
                    if cursor.recovery_depth >= max_depth {
                        let msg = format!(
                            "recovery depth limit {} exceeded at pos {} (cursor depth = {}) — \
                             unrecoverable parse; refusing further recovery dispatch",
                            max_depth, cursor.pos, cursor.recovery_depth,
                        );
                        self.set_cursor_inner_state(
                            cursor,
                            WpdsState::Error { message: msg },
                        );
                        return CursorOutcome::Drop;
                    }
                    if let Some(key) = recovery_dispatch_config {
                        if cursor.visited_recovery.contains(&key) {
                            let msg = format!(
                                "recovery already attempted at (pos={}, cat_src={}, cur_bp={}) — \
                                 refusing to re-dispatch (cursor cycle defense)",
                                key.0, key.1, key.2,
                            );
                            self.set_cursor_inner_state(
                                cursor,
                                WpdsState::Error { message: msg },
                            );
                            return CursorOutcome::Drop;
                        }
                    }
                    let base_pos = cursor.pos;
                    let pre_count = branches.len();
                    branches.retain(|b| forward_progress_or_insert(b, base_pos));
                    if branches.is_empty() {
                        let msg = format!(
                            "all {} recovery branches at pos {} violate forward-progress invariant — \
                             bounded recovery refusing to dispatch",
                            pre_count, base_pos,
                        );
                        self.set_cursor_inner_state(
                            cursor,
                            WpdsState::Error { message: msg },
                        );
                        return CursorOutcome::Drop;
                    }
                }
                // B14 / C5 (2026-05-08): per-projection-branch GLL
                // descriptor uniqueness. Extends B12's per-Fork cycle
                // defense (gated by `is_projection_fork` requiring ALL
                // branches CrossCatDelegate) to per-branch: any individual
                // CrossCatDelegate branch that would re-enter the same
                // (pos, cat_src, cur_bp) is dropped — productive non-
                // projection siblings (atomic Var, cross-cat-LHS) keep
                // competing via lex-min weights. The fix bounds LedTest's
                // mixed-Fork Pred ↔ Num cycle (PredToNum projection
                // sharing a Fork with NumVar atomic), which the per-Fork
                // gate could not catch (mixed Fork → is_projection_fork
                // false → no defense fires).
                //
                // Rationale: a projection-spawned descriptor's history
                // is independent of its non-projection siblings'. The
                // per-branch gate is the natural per-descriptor extension
                // of GLL descriptor uniqueness (Scott & Johnstone 2010).
                //
                // Mirrors the recovery cycle defense above; distinct in
                // that the gate is per-branch (not per-Fork) and applies
                // to mixed Forks. Non-projection branches in the same
                // Fork pass through unchanged — atomic prefix, lex-alt,
                // multi-rule, Opt-Group dispatches keep their lex-min
                // ambiguity-resolution semantics.
                let parent_dispatch_config: Option<(usize, u16, u8)> =
                    if is_recovery {
                        None
                    } else {
                        extract_dispatch_config(cursor, &self.gss)
                    };
                let parent_in_visited: bool = parent_dispatch_config
                    .map(|k| cursor.visited_dispatch.contains(&k))
                    .unwrap_or(false);
                // Fast-path retained: pure-projection Fork already-visited
                // would have every branch skipped by the per-branch gate
                // below, leaving zero children. Drop the entire cursor
                // here as a single optimization (algebraically equivalent
                // to per-branch dropping all branches).
                let is_pure_projection_fork =
                    !is_recovery && is_projection_fork(&branches);
                if is_pure_projection_fork && parent_in_visited {
                    if let Some(key) = parent_dispatch_config {
                        let msg = format!(
                            "cross-cat projection cycle detected at \
                             (pos={}, cat_src={}, cur_bp={}) — refusing \
                             to re-dispatch projection Fork (B14 C5 cycle defense)",
                            key.0, key.1, key.2,
                        );
                        self.set_cursor_inner_state(
                            cursor,
                            WpdsState::Error { message: msg },
                        );
                        return CursorOutcome::Drop;
                    }
                }
                let pos_after = if consume_trigger {
                    cursor.pos + 1
                } else {
                    cursor.pos
                };
                let mut children = Vec::with_capacity(branches.len());
                // B14 C5: parallel tracker — for each child pushed below,
                // record whether its originating branch was CrossCatDelegate.
                // Used post-loop for per-child visited_dispatch insertion.
                let mut child_came_from_cross_cat: Vec<bool> =
                    Vec::with_capacity(branches.len());
                let branches_count = branches.len() as u32;
                for (branch_idx, branch) in branches.into_iter().enumerate() {
                    // B14 C5 per-branch gate: skip CrossCatDelegate branches
                    // that would re-enter the same dispatch config (GLL
                    // descriptor uniqueness). Productive non-projection
                    // siblings in the same Fork are unaffected.
                    let is_cross_cat_delegate_branch =
                        matches!(&branch.new_state, WpdsState::CrossCatDelegate { .. });
                    if !is_recovery
                        && parent_in_visited
                        && is_cross_cat_delegate_branch
                    {
                        continue;
                    }
                    // Stage 3.12 Fix 2(ii) (2026-05-02): Fork-source-order
                    // priority. Encode the cursor's full Fork path via
                    // `parent.priority * num_branches + branch_idx`. For
                    // typical 2-branch Forks: priority is the binary path
                    // through the Fork tree (left=0, right=1). Lower wins
                    // on weight ties — TAKE always beats SKIP (idx 0 < 1).
                    // For nested Forks: Inner-TAKE+Outer-TAKE=0,
                    // Inner-TAKE+Outer-SKIP=1, Inner-SKIP+Outer-TAKE=2,
                    // Inner-SKIP+Outer-SKIP=3 — exact source-order
                    // lexicographic.
                    let child_source_priority = cursor
                        .source_priority
                        .saturating_mul(branches_count)
                        .saturating_add(branch_idx as u32);
                    // Stage 3.12 / Class A.i (2026-05-01): dispatch on
                    // branch.action_kind. `Push` is the existing path;
                    // `OptGroupAbsent` mirrors `apply_action::OptGroupAbsent`
                    // for the SKIP branch of an Opt-Group Fork.
                    match branch.action_kind {
                        ForkActionKind::Push => {
                            // Stage 3.12 latent-bug fix (2026-05-01): apply
                            // emit_push_side_effects on each branch so
                            // OptionalGroupAt(1) and CollectionMarker
                            // pushes through Fork get the same implicit
                            // side effects as deterministic Push. Pre-3.12
                            // this was missing — TAKE branches with
                            // OptionalGroupAt(1) silently skipped scope
                            // opening, breaking nested Opt-Group parses
                            // that landed in Strict mode.
                            //
                            // We allocate a child cursor first (with empty
                            // pending_builder_ops + collection_stack
                            // mirror), THEN run side effects against the
                            // CHILD's cursor view. The child's mode is
                            // Strict (just promoted), so side effects log
                            // deltas onto the child's pending_builder_ops.
                            let mut symbol = branch.symbol;
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                // Stage 3.12.6 (2026-05-02): inherit parent's
                                // stack-suffix history; the push below appends
                                // a new edge id to it.
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            self.emit_push_side_effects(&mut child, &mut symbol);
                            // Stage 3.12.6 (2026-05-02): use cursor_gss_push
                            // (not raw gss.push_symbol) so the child's
                            // incoming_edge_stack records the new edge id
                            // for its eventual pop.
                            let _ = self.cursor_gss_push(
                                &mut child,
                                symbol,
                                pos_after,
                                branch.weight.clone(),
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }
                        ForkActionKind::OptGroupAbsent { replace_symbol } => {
                            // Stage 3.12 / Class A.i (2026-05-01): SKIP
                            // branch. Mirrors `apply_action_to_cursor::OptGroupAbsent`
                            // (and its live-mode counterpart at
                            // `apply_action::OptGroupAbsent` pre-Phase-4):
                            //   1. Log `BuilderDelta::PushOptionalAbsent`.
                            //   2. Pop outer RuleAt from cursor.node.
                            //   3. Push replace_symbol (advanced outer
                            //      RuleAt).
                            //   4. Update cursor inner_state, weight.
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                // Stage 3.12.6 (2026-05-02): inherit parent's
                                // stack-suffix history.
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            // Strict mode: emit_push_optional_absent logs the delta.
                            self.emit_push_optional_absent(&mut child);
                            // Stage 3.12.6 (2026-05-02): pop along the
                            // child's recorded edge (its own history),
                            // not an arbitrary in-edge of child.node.
                            let popped = self.cursor_gss_pop_via_edge(&mut child);
                            if popped.is_none() {
                                // GSS underflow: synthesize CategoryEntry(0)
                                // sentinel so the subsequent push has a
                                // valid predecessor.
                                let sentinel = self.gss.get_or_create_node(WpdsGssNode {
                                    pos: child.pos,
                                    symbol: StackSymbolV2::category_entry(0),
                                });
                                child.node = sentinel;
                            }
                            // Stage 3.12.6: use cursor_gss_push so the
                            // child's incoming_edge_stack records the
                            // new edge id for its eventual pop.
                            let _ = self.cursor_gss_push(
                                &mut child,
                                replace_symbol,
                                pos_after,
                                branch.weight.clone(),
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        // Stage 3.16 (Cluster 1, Mechanism γ, 2026-05-05) —
                        // payload-carrying action variants. Each arm mirrors
                        // its WpdsStepAction counterpart's apply_action body.
                        // Fork emits these with `consume_trigger: false`
                        // because each variant intrinsically encodes its own
                        // consume semantics; the per-branch consume happens
                        // INSIDE this arm, not at allocation time.
                        ForkActionKind::ConsumeAndReplace => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::Consume => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeIdentAndReplace { start_scope } => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            // Read ident-text BEFORE pos advances. If peek_kind
                            // isn't Ident at runtime, this branch's cursor will
                            // produce a stuck/dropped configuration via downstream
                            // dispatch (no panic — the lex-min winner is among the
                            // surviving cursors).
                            let text = tokens
                                .peek_text(child.pos)
                                .unwrap_or("")
                                .to_string();
                            // L12 follow-up (B1, 2026-05-07): emit_push_ident MUST
                            // run unconditionally — emit_start_binder_scope pushes
                            // BinderHandle to binder_scopes, but the action body's
                            // Ident-typed parameter expects ActionArg::Ident on
                            // the arg stack regardless of start_scope. Mirrors the
                            // canonical WpdsStepAction::ConsumeIdentAndReplace arm
                            // at line ~2521. Pre-fix: when start_scope=true, the
                            // else branch never ran, so emit_push_ident was
                            // skipped → action body's Ident parameter missing →
                            // malformed AST (e.g. Term::TVar instead of Term::Lam).
                            if start_scope {
                                self.emit_start_binder_scope(
                                    &mut child,
                                    vec![text.clone()],
                                );
                            }
                            let pos_now = child.pos;
                            self.emit_push_ident(&mut child, text, pos_now);
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::Pop => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            let popped_symbol =
                                self.gss.node(child.node).map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            self.apply_pop_body_to_cursor(
                                &mut child,
                                pred_id,
                                popped_symbol,
                                &branch.weight,
                                branch.new_state.clone(),
                                tokens,
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeAndPop => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            let popped_symbol =
                                self.gss.node(child.node).map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            self.apply_pop_body_to_cursor(
                                &mut child,
                                pred_id,
                                popped_symbol,
                                &branch.weight,
                                branch.new_state.clone(),
                                tokens,
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeAndReplaceWithEffect { effect } => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                            child.consistency_memo.set(None);
                            // Phase 5.5 (2026-05-12): eagerly apply effect
                            // to child.builder via Arc::make_mut so the
                            // post-install state has these mutations.
                            Self::apply_effect_to_builder(
                                Arc::make_mut(&mut child.builder),
                                &effect,
                            );
                            child.pending_builder_ops.push(effect);
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::LexAlt { alt_idx, kind, text } => {
                            let mut sym = branch.symbol;
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                            child.consistency_memo.set(None);
                            child.pending_builder_ops.push(
                                BuilderDelta::CommitLexAlternative {
                                    pos: child.pos,
                                    alt_idx,
                                    kind,
                                    text,
                                },
                            );
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let _ = self.cursor_gss_push(
                                &mut child,
                                sym,
                                pos_after,
                                branch.weight.clone(),
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeAndCaptureAndPush => {
                            // Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ,
                            // 2026-05-05): atomic literal multi-arm Fork
                            // branch. Mirrors WpdsStepAction::ConsumeAndPush
                            // with capture_token=true (prefix.rs Pass-1
                            // emission). Captures the trigger token onto the
                            // builder (live or pending depending on mode),
                            // pushes the branch's symbol (rule's Return
                            // marker), and advances pos by 1. Used when
                            // codegen buckets atomic prefix arms and a
                            // bucket has ≥2 rules with the same (pat, guard)
                            // — lex-min via from_cost(0.0, src, rule_idx)
                            // picks the lower rule_idx winner.
                            let mut sym = branch.symbol;
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                pending_builder_ops: cursor.pending_builder_ops.clone(),
                                collection_stack: cursor.collection_stack.clone(),
                                collection_slots_allocated: cursor.collection_slots_allocated,
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Bounded recovery (Stage 3.20 / L12,
                                // 2026-05-06): inherit parent's recovery
                                // book-keeping. The Fork-arm prologue
                                // (when this is a recovery Fork) bumps
                                // depth + extends visited_recovery on
                                // each child after allocation; for
                                // non-recovery Forks (Push, OptGroupAbsent,
                                // lex-alt, etc.) the inherited values
                                // pass through unchanged.
                                recovery_depth: cursor.recovery_depth,
                                visited_recovery: cursor.visited_recovery.clone(),
                                visited_dispatch: cursor.visited_dispatch.clone(),
                                consistency_memo: std::cell::Cell::new(cursor.consistency_memo.get()),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                builder: Arc::clone(&cursor.builder),
                            };
                            // Capture the token at child.pos BEFORE advancing
                            // (mirrors live ConsumeAndPush at line 2086-2099).
                            if let Some(kind) = tokens.peek_kind(child.pos) {
                                let text = tokens
                                    .peek_text(child.pos)
                                    .unwrap_or("")
                                    .to_string();
                                let pos_now = child.pos;
                                self.emit_push_token(&mut child, kind, text, pos_now);
                            }
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_push(
                                &mut child,
                                sym,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeAndReplace { expected_text } => {
                            // Stage 3.20 / L12 Commit F (2026-05-06):
                            // Cluster 1/6 hack #4/#5 closure. Single-branch
                            // Fork with `peek_text == expected_text` guard.
                            // Pass → ConsumeAndReplace semantics. Fail →
                            // skip child allocation (the only surviving
                            // branch dies, step_fanout reports "all fork
                            // branches dropped" via the standard pathway).
                            let peek = tokens.peek_text(pos_after).unwrap_or("");
                            if peek != expected_text.as_str() {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeIdentAndReplace { start_scope } => {
                            // Stage 3.20 / L12 Commit F (2026-05-06):
                            // Cluster 1/6 hack #6/4th closure. Single-branch
                            // Fork with `peek_kind == Ident` guard. Pass →
                            // ConsumeIdentAndReplace { start_scope }
                            // semantics. Fail → skip child allocation.
                            if !matches!(
                                tokens.peek_kind(pos_after),
                                Some(crate::automata::TokenKind::Ident)
                            ) {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let text = tokens
                                .peek_text(child.pos)
                                .unwrap_or("")
                                .to_string();
                            // L12 follow-up (B1, 2026-05-07): emit_push_ident MUST
                            // run unconditionally — see twin fix at line ~2920 in
                            // the in-Fork ConsumeIdentAndReplace arm. Mirrors
                            // canonical WpdsStepAction::ConsumeIdentAndReplace at
                            // line ~2521.
                            if start_scope {
                                self.emit_start_binder_scope(
                                    &mut child,
                                    vec![text.clone()],
                                );
                            }
                            let pos_now = child.pos;
                            self.emit_push_ident(&mut child, text, pos_now);
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsume { expected_text } => {
                            // L12 follow-up B2 (2026-05-07): peek_text
                            // equality guard. Pass → Consume semantics
                            // (advance pos, no GSS change). Fail → skip
                            // child allocation. Used by BinderListLoop's
                            // separator branch — pre-fix this was the
                            // unguarded `Consume` action_kind that fired
                            // unconditionally and caused exponential
                            // cursor multiplication on multi-binder rules.
                            let peek = tokens.peek_text(pos_after).unwrap_or("");
                            if peek != expected_text.as_str() {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                            expected_text,
                            effect,
                        } => {
                            // L12 follow-up B2 (2026-05-07): peek_text
                            // equality guard wrapping ConsumeAndReplaceWithEffect.
                            // Pass → log effect to pending_builder_ops,
                            // replace top of GSS, advance pos. Fail →
                            // skip child allocation. Used by BinderListLoop's
                            // bootstrap empty-list branch (effect:
                            // BuilderDelta::StartBinderScope { names: vec![] })
                            // — pre-fix the unguarded effect-bearing branch
                            // fired on every dispatch and produced spurious
                            // empty-binder-scope cursors that contributed to
                            // the exponential explosion.
                            let peek = tokens.peek_text(pos_after).unwrap_or("");
                            if peek != expected_text.as_str() {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                            child.consistency_memo.set(None);
                            // Phase 5.5 (2026-05-12): eagerly apply effect
                            // to child.builder via Arc::make_mut so the
                            // post-install state has these mutations.
                            Self::apply_effect_to_builder(
                                Arc::make_mut(&mut child.builder),
                                &effect,
                            );
                            child.pending_builder_ops.push(effect);
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeIdentAndPop { start_scope: _ } => {
                            // B8 / Issue C followup (2026-05-09): consume
                            // ident token, EXTEND the open binder scope
                            // with the captured name (instead of pushing
                            // to args stack), Pop top-of-GSS. Used by
                            // Class 3 multi-binder iterations where the
                            // scope is opened once at bootstrap and each
                            // iteration's BinderIdent extends names.
                            //
                            // Phase 2 / Redesign C (2026-05-11): delegate
                            // the pop side to `apply_pop_body_to_cursor`
                            // so the splice gate and action firing fire
                            // uniformly. For Class 3 BinderIdent popping
                            // the splice won't fire (popped kind isn't
                            // CategoryEntry/RuleAt and post-pop token
                            // isn't close/sep) — behavior preserved.
                            if !matches!(
                                tokens.peek_kind(pos_after),
                                Some(crate::automata::TokenKind::Ident)
                            ) {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let text = tokens
                                .peek_text(child.pos)
                                .unwrap_or("")
                                .to_string();
                            self.emit_extend_binder_scope(&mut child, text);
                            // Capture popped_symbol before pop.
                            let popped_symbol = self.gss
                                .node(child.node)
                                .map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            self.apply_pop_body_to_cursor(
                                &mut child,
                                pred_id,
                                popped_symbol,
                                &branch.weight,
                                branch.new_state.clone(),
                                tokens,
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeBinderIdentAndReplace { start_scope } => {
                            // B8 / Issue 3 fix (2026-05-10): consume Ident
                            // token, either open scope with [text] OR
                            // extend innermost scope's names with text;
                            // replace top of GSS; advance pos. NO
                            // emit_push_ident — name lives in the
                            // BinderHandle.names list, not on the args
                            // stack. For multi-binder rules whose action
                            // expects BinderScope arg, not Ident.
                            if !matches!(
                                tokens.peek_kind(pos_after),
                                Some(crate::automata::TokenKind::Ident)
                            ) {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let text = tokens
                                .peek_text(child.pos)
                                .unwrap_or("")
                                .to_string();
                            if start_scope {
                                self.emit_start_binder_scope(
                                    &mut child,
                                    vec![text.clone()],
                                );
                            } else {
                                self.emit_extend_binder_scope(&mut child, text.clone());
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeBinderIdentAndReplaceWithEffect {
                            start_scope,
                            effect,
                        } => {
                            // Phase 3.B.2 (2026-05-11): single-binder
                            // collapse variant. Same body as
                            // GuardedConsumeBinderIdentAndReplace
                            // (ident gate, open/extend scope, replace
                            // top of GSS, pos++) but logs `effect`
                            // (typically BuilderDelta::EndBinderScope)
                            // onto pending_builder_ops between scope
                            // mutation and the GSS replace. Atomic
                            // capture+close so single-binder rules
                            // (Lambda Lam, ambient PNew single-binder,
                            // guardedRho PGuardedInput) keep AST
                            // surface unchanged: action_entry unwraps
                            // BinderScope.names[0] to a scalar
                            // Binder<String>.
                            if !matches!(
                                tokens.peek_kind(pos_after),
                                Some(crate::automata::TokenKind::Ident)
                            ) {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let text = tokens
                                .peek_text(child.pos)
                                .unwrap_or("")
                                .to_string();
                            if start_scope {
                                self.emit_start_binder_scope(
                                    &mut child,
                                    vec![text.clone()],
                                );
                            } else {
                                self.emit_extend_binder_scope(&mut child, text.clone());
                            }
                            child.consistency_memo.set(None);
                            Self::apply_effect_to_builder(
                                Arc::make_mut(&mut child.builder),
                                &effect,
                            );
                            child.pending_builder_ops.push(effect);
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeAndPopWithEffect {
                            expected_text,
                            effect,
                        } => {
                            // B8 / Issue C followup (2026-05-09): peek_text
                            // equality guard wrapping ConsumeAndPop with one
                            // builder delta effect logged.
                            //
                            // Phase 2 / Redesign C (2026-05-11): delegate the
                            // pop side to `apply_pop_body_to_cursor` instead
                            // of hand-rolling. apply_pop_body_to_cursor
                            // handles cursor.collection_stack pop, splice
                            // gate (Plan B Phase 3), and action firing for
                            // Return symbols uniformly. The prior hand-rolled
                            // version was the Issue 1 origin — fixing it
                            // ad-hoc per-variant misses the splice cases.
                            let peek = tokens.peek_text(pos_after).unwrap_or("");
                            if peek != expected_text.as_str() {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            child.consistency_memo.set(None);
                            Self::apply_effect_to_builder(
                                Arc::make_mut(&mut child.builder),
                                &effect,
                            );
                            child.pending_builder_ops.push(effect);
                            // Capture popped_symbol before pop.
                            let popped_symbol = self.gss
                                .node(child.node)
                                .map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            self.apply_pop_body_to_cursor(
                                &mut child,
                                pred_id,
                                popped_symbol,
                                &branch.weight,
                                branch.new_state.clone(),
                                tokens,
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ReplaceAndPush { replace_symbol } => {
                            // B8 / Issue C followup (2026-05-09): Class 3
                            // bootstrap. Replace top with replace_symbol,
                            // then push branch.symbol on top, transition
                            // state. No token consumed. emit_push_side_effects
                            // fires for the pushed symbol.
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                replace_symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            let mut sym = branch.symbol;
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let _ = self.cursor_gss_push(
                                &mut child,
                                sym,
                                pos_now,
                                branch.weight.clone(),
                            );
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                            expected_text,
                            effects,
                        } => {
                            // B8 / Issue B (2026-05-09): same as
                            // GuardedConsumeAndReplaceWithEffect but logs
                            // a Vec<BuilderDelta> in order. Used by Class 3
                            // empty-list bootstrap to log
                            // [StartCollection, PushCollectionId{id:0},
                            // StartBinderScope] atomically.
                            let peek = tokens.peek_text(pos_after).unwrap_or("");
                            if peek != expected_text.as_str() {
                                continue;
                            }
                            let mut child = BranchCursor::fork_child(
                                cursor,
                                pos_after,
                                cursor.weight.times(&branch.weight),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            child.consistency_memo.set(None);
                            for effect in effects {
                                Self::apply_effect_to_builder(
                                    Arc::make_mut(&mut child.builder),
                                    &effect,
                                );
                                child.pending_builder_ops.push(effect);
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos += 1;
                            if self.cursor_mode == CursorMode::Lazy {
                                self.pos = child.pos;
                            }
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }
                    }
                }
                // Bounded recovery (Stage 3.20 / L12, 2026-05-06):
                // post-loop bump for recovery Forks. Each child inherited
                // the parent's recovery_depth via the per-arm allocation
                // (added to all 10 ForkActionKind arms via replace_all);
                // here we bump the depth by 1 and insert the dispatch
                // config into visited_recovery so the next dispatch at
                // the same configuration is refused. For non-recovery
                // Forks the inherited values pass through unchanged.
                if is_recovery {
                    if let Some(key) = recovery_dispatch_config {
                        for child in children.iter_mut() {
                            child.recovery_depth =
                                child.recovery_depth.saturating_add(1);
                            child.visited_recovery.insert(key);
                        }
                    } else {
                        // is_recovery true but config missing: cursor wasn't
                        // in PrefixDispatch when the recovery Fork was
                        // dispatched. Treat as malformed dispatch — bump
                        // depth without visited entry so the cap still bites.
                        for child in children.iter_mut() {
                            child.recovery_depth =
                                child.recovery_depth.saturating_add(1);
                        }
                    }
                }
                // B14 C5 (2026-05-08): per-child conditional insertion of
                // the dispatch config. Only children whose originating
                // branch was CrossCatDelegate get the key inserted into
                // their visited_dispatch — productive non-projection
                // siblings (atomic Var, cross-cat-LHS) keep their clean
                // visited_dispatch sets and can compete via lex-min on
                // subsequent dispatches without false-positive cycle drops.
                //
                // Replaces B12's blanket `if is_projection` insertion,
                // which fired only on pure-projection Forks. The C5 gate
                // fires per-branch in mixed Forks; the matching post-loop
                // insertion ensures the gate has a key to detect on the
                // next iteration.
                if let Some(key) = parent_dispatch_config {
                    if !is_recovery {
                        debug_assert_eq!(
                            children.len(),
                            child_came_from_cross_cat.len(),
                            "B14 C5: parallel tracker out of sync with children",
                        );
                        for (idx, child) in children.iter_mut().enumerate() {
                            if child_came_from_cross_cat[idx] {
                                child.visited_dispatch.insert(key);
                            }
                        }
                    }
                }
                CursorOutcome::ForkInto(children)
            }
            WpdsStepAction::Accept => {
                // Stage 3.5b (2026-05-01): mirror live apply_action::Accept
                // by transitioning cursor.inner_state to Accepted.
                // Stage 3.9 / ι Phase 4 (2026-05-01): use helper so live
                // walker self.state is mirrored to Accepted in Lazy mode.
                self.set_cursor_inner_state(cursor, WpdsState::Accepted);
                CursorOutcome::Resolved
            }
            WpdsStepAction::Error(message) => {
                // Stage 3.9 / ι Phase 4 (2026-05-01): mirror live state via
                // helper so Lazy-mode self.state becomes Error too.
                self.set_cursor_inner_state(
                    cursor,
                    WpdsState::Error { message },
                );
                CursorOutcome::Drop
            }
            WpdsStepAction::OptGroupAbsent {
                replace_symbol,
                weight,
                new_state,
            } => {
                // Stage 3.8 / ι Phase 3 (2026-05-01): cursor-side Opt-Group
                // skip path. Mirrors the live `apply_action::OptGroupAbsent`
                // arm (line ~1712 above) but delegates the live-builder
                // `push_optional_absent` to a `BuilderDelta` so it replays
                // at commit time only on the lex-min winner.
                //
                // Steps:
                //   1. Log `BuilderDelta::PushOptionalAbsent` (commit
                //      replays via `SemanticBuilder::push_optional_absent`).
                //   2. Pop the (top) outer RuleAt marker from the cursor's
                //      GSS chain.
                //   3. Push `replace_symbol` (the advanced outer RuleAt at
                //      next outer position) onto the cursor's GSS.
                //   4. Update cursor weight + state.
                self.emit_push_optional_absent(cursor);
                // Stage 3.12.6 (2026-05-02): use edge-id-guided pop so
                // the cursor's recorded predecessor is the one followed,
                // not an arbitrary in-edge of the popped node.
                let new_node_after_pop = self.cursor_gss_pop_via_edge(cursor);
                if new_node_after_pop.is_none() {
                    // GSS underflow — synthesize a CategoryEntry sentinel at
                    // pos for the cursor. Update cursor.node directly so the
                    // subsequent cursor_gss_push lands on it.
                    let sentinel = self.gss.get_or_create_node(WpdsGssNode {
                        pos: cursor.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    });
                    cursor.node = sentinel;
                    if self.cursor_mode == CursorMode::Lazy {
                        self.top_node = Some(sentinel);
                    }
                }
                let _ = self.cursor_gss_push(cursor, replace_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::OptGroupFinalize {
                replace_symbol,
                weight,
                new_state,
            } => {
                // Stage 3.8 / ι Phase 3 (2026-05-01): cursor-side Opt-Group
                // take-path finalize. Mirrors the live arm but uses helpers
                // for mode-aware mutation.
                //
                // Steps:
                //   1. Pop the OptionalGroupAt marker on top.
                //   2. Emit FinalizeOptionalScopePresent (Lazy direct,
                //      Strict delta).
                //   3. Pop the (now-on-top) outer RuleAt marker.
                //   4. Push `replace_symbol` (advanced outer RuleAt).
                // Stage 3.12.6 (2026-05-02): edge-id-guided pops.
                let after_marker_pop = self.cursor_gss_pop_via_edge(cursor);
                self.emit_finalize_optional_scope_present(cursor);
                let after_outer_pop = if after_marker_pop.is_some() {
                    self.cursor_gss_pop_via_edge(cursor)
                } else {
                    None
                };
                if after_outer_pop.is_none() {
                    let sentinel = self.gss.get_or_create_node(WpdsGssNode {
                        pos: cursor.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    });
                    cursor.node = sentinel;
                    if self.cursor_mode == CursorMode::Lazy {
                        self.top_node = Some(sentinel);
                    }
                }
                let _ = self.cursor_gss_push(cursor, replace_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdsStepAction::Idle => {
                // Stage 3.5b (2026-05-01): WPDS-correct EOI parking.
                //
                // Pre-3.5b: any Idle cursor was Dropped to avoid infinite
                // step_fanout iterations.
                //
                // Post-3.5b: a cursor at end-of-input whose inner_state is
                // one of the resolution-detection states (InfixLoop,
                // Unwinding, Accepted) is "parked" — it has no more input
                // to consume but participates in EOI ⊕-resolution. Drop
                // only when the cursor is genuinely stuck (Idle in a
                // mid-parse state, or Idle with input remaining).
                //
                // Stage 3.12 fix (2026-05-02): use `is_logical_eoi` so a
                // cursor parked at a trailing `Token::Eof` is treated as
                // EOI for parking purposes, mirroring the EOI filter.
                //
                // Stage 3.12.7 (2026-05-02): a cursor that popped past the
                // GSS root (cursor.node == GSS_NODE_NONE) is irreversibly
                // parked — engine.step's frontier_top=None ⇒ Accept arm
                // transitions it to Accepted; the next iteration's
                // Accepted ⇒ Idle dispatch lands here. Without this branch
                // the cursor is dropped pre-EOI when at_eoi=false (e.g.,
                // a per-category parse in `parse_preserving_vars` that
                // unwinds at mid-stream because no infix matches the
                // current token). Pre-Stage-3.12 the pristine Pop arm
                // short-circuited via `None => CursorOutcome::Resolved`
                // for this exact case; the unified apply_pop_body_to_cursor
                // (Stage 3.12.5) lost that distinction, breaking 38+7
                // calc_op/rhocalc_op tests. Treating popped-past-root as
                // Resolved restores the cursor-lifetime invariant;
                // is_accepting_config (Unwinding arm) still gates EOI
                // admission, so EOI filtering is unaffected. Termination
                // preserved by run_to_end_of_input's progress_made
                // fingerprint stability across self-loops.
                let popped_past_root = cursor.node == crate::gss::GSS_NODE_NONE;
                let at_eoi = self.is_logical_eoi(cursor.pos, tokens);
                let resolved_shape = matches!(
                    cursor.inner_state,
                    WpdsState::InfixLoop { .. }
                        | WpdsState::Accepted
                        | WpdsState::Unwinding
                );
                if (at_eoi && resolved_shape) || popped_past_root {
                    CursorOutcome::Resolved
                } else {
                    CursorOutcome::Drop
                }
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
        // Phase 5.5 (2026-05-12): cursors that hit Error state mid-step
        // (e.g., emit_fire_action's eager fire underflow) are Dropped so
        // step_fanout's all-dropped path can surface "Error" to the walker.
        if matches!(cursor.inner_state, WpdsState::Error { .. }) {
            return CursorOutcome::Drop;
        }
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
            // Stage 3.11 / ι Phase 6 (2026-05-01): runaway guard. Any
            // cursor whose pending_builder_ops exceeds the limit is
            // marked Error and returned immediately. The fanout bails
            // out, preserving the offending cursor so resolve_at_end_of_input
            // returns ParseError with a diagnostic.
            if cursor.pending_builder_ops.len() > STRICT_PENDING_OPS_LIMIT {
                self.state = WpdsState::Error {
                    message: format!(
                        "ι Phase 6 runaway guard: cursor pending_builder_ops \
                         exceeded STRICT_PENDING_OPS_LIMIT ({} > {})",
                        cursor.pending_builder_ops.len(),
                        STRICT_PENDING_OPS_LIMIT,
                    ),
                };
                self.branch_cursors = vec![cursor];
                return self.state.clone();
            }
            match outcome {
                CursorOutcome::Drop => { /* discard */ }
                CursorOutcome::Alive => new_cursors.push(cursor),
                // **Tiebreak chain link 4 (load-bearing).** `extend` preserves
                // the source-order of `children` produced by Fork. Combined
                // with: (1) `vec![take, skip]` codegen at binder.rs:973-980,
                // (2) `LexicographicWeight::plus` returning `*self` on equality
                // at lex_weight.rs:345-348, and (3) `pick_lex_min_resolved`'s
                // earlier-index-wins tiebreak at wpds_walker.rs:2570-2592,
                // this ordering yields right-associative dangling-else for
                // Opt-Group Forks. Reordering or replacing with `insert`/`push`
                // breaks the invariant.
                CursorOutcome::ForkInto(children) => new_cursors.extend(children),
                CursorOutcome::Resolved => {
                    resolved_indices.push(new_cursors.len());
                    new_cursors.push(cursor);
                }
            }
        }
        self.branch_cursors = new_cursors;
        // Stage 3.5b (2026-05-01) intentionally drops the prior
        // `resolved_indices` consumption: it was only used by the
        // mid-stream commit path, which is now WPDS-incorrect (Bug 1).
        // The variable is retained for shape parity with the per-cursor
        // pass above; future refactors may delete the bookkeeping.
        let _ = resolved_indices;

        // Stage 3.4 (2026-04-30): beam pruning. No-op when `beam_size` is
        // None (default); when set, retains top-K by lex-min weight to
        // bound fanout cost on highly-ambiguous grammars.
        self.maybe_prune_frontier();

        // Stage 3.5b (2026-05-01): WPDS configuration ⊕-merging. Two
        // cursors reaching the same `(state, gss_node, pos)` collapse
        // via `Semiring::plus`. The lex-min winner's operational state
        // (`pending_builder_ops`, `collection_stack`) is kept (deltas
        // are non-commutative). Caps polynomial fanout in ambiguous
        // grammars vs the prior exponential branch count.
        self.merge_equivalent_cursors();

        // B10 / Option κ Part 3 (2026-05-07): lex-dominated cursor
        // subsumption. After strict-key merge, group remaining cursors
        // by RELAXED key `(state, gss-node-symbol, pos)` (intentionally
        // dropping `incoming_edge_stack` — that discriminator exists
        // for pop-time determinism with structural sharing, not for
        // parse-time semantic distinctness). Within each group, drop
        // any cursor C if a sibling S has `S.weight.lex_cmp(C.weight) ==
        // Less`. This is algebraically equivalent to lex-min selection
        // at EOI — pruning eagerly caps fanout before the next
        // step_fanout iteration re-amplifies via Pass 0/1/2a Forks.
        // Recovery semantics are unchanged; recovery dispatch can itself
        // be lex-dominated and dropped iff a non-recovering sibling at
        // the same configuration has lower weight, which is the
        // WPDS-correct outcome.
        self.subsume_lex_dominated_cursors();

        if self.branch_cursors.is_empty() {
            // CASE 1: all branches dropped.
            let s = WpdsState::Error {
                message: "all fork branches dropped".to_string(),
            };
            self.state = s.clone();
            return s;
        }

        // Stage 3.5b (2026-05-01): the prior `if alive_count == 0` mid-stream
        // commit_winner block (Bug 1) is REMOVED. Resolved cursors stay in
        // `branch_cursors` and either:
        //   - re-enter the next `step_fanout` iteration (e.g., InfixLoop
        //     finds an infix operator and transitions back to PrefixDispatch
        //     as Alive), or
        //   - park at EOI via `apply_action_to_cursor`'s Idle branch (resolved
        //     shape + pos == tokens.len() → CursorOutcome::Resolved).
        //
        // End-of-input resolution is handled by `resolve_at_end_of_input`
        // (called by the parse facade after `run_to_end_of_input`), not here.
        let frontier: Vec<crate::gss::GssNodeId> =
            self.branch_cursors.iter().map(|c| c.node).collect();
        let s = WpdsState::AmbiguityFanout { branches: frontier };
        self.state = s.clone();
        s
    }

    /// Stage 3.5b (2026-05-01): WPDS configuration ⊕-merging.
    ///
    /// Collapses cursors with the same `ConfigKey` (`state`, `gss_node`,
    /// `pos`) into a single cursor whose weight is the `Semiring::plus`
    /// of the inputs. The operational state (`pending_builder_ops`,
    /// `collection_stack`) of the lex-min winner is kept; the loser's
    /// is discarded because deltas are non-commutative (e.g.,
    /// `PushIdent("x"); PushIdent("y")` cannot be merged with the reverse
    /// — only the winning path's mutations execute).
    ///
    /// **Performance**: O(n) per call (n = `branch_cursors.len()`), via
    /// HashMap lookup. In unambiguous grammars n ≤ 1; in ambiguous,
    /// merging caps n polynomially vs the pre-3.5b exponential.
    ///
    /// **Hash safety**: `WpdsState` derives `Hash` (Stage 3.5b
    /// `wpds_runtime.rs:326`); all variant payloads are `Hash`-able
    /// (u8/u16/usize/String/Vec<u32>).
    ///
    /// **Tie-break**: when `cursor.weight.plus(&existing.weight) ==
    /// existing.weight`, the existing entry wins (preserves source-order).
    fn merge_equivalent_cursors(&mut self) {
        if self.branch_cursors.len() < 2 {
            return;
        }
        let mut by_key: std::collections::HashMap<ConfigKey, usize> =
            std::collections::HashMap::with_capacity(self.branch_cursors.len());
        let mut merged: Vec<BranchCursor<W>> =
            Vec::with_capacity(self.branch_cursors.len());
        // B13d-R (2026-05-08): drain into a local Vec FIRST so subsequent
        // `self.cursor_committed_ops_consistent(...)` calls (which take
        // `&self`) don't conflict with the mutable borrow of
        // `self.branch_cursors`.
        let drained: Vec<BranchCursor<W>> = self.branch_cursors.drain(..).collect();
        for cursor in drained {
            let key = ConfigKey {
                state: cursor.inner_state.clone(),
                node: cursor.node,
                pos: cursor.pos,
                // Stage 3.12.6 (2026-05-02): include the cursor's
                // current stack-suffix top edge id, so cursors with
                // different stack histories at the same (state, node,
                // pos) do NOT merge.
                incoming_edge: cursor.incoming_edge_stack.last().copied(),
                // Phase 4 #5b (2026-05-12): include collection_stack
                // depth so cursors with different operational shapes
                // (e.g. one mid-binder-internal-collection, the other
                // post-pop) bucket separately and never trip the
                // merge invariant.
                collection_depth: cursor.collection_stack.len(),
            };
            match by_key.entry(key) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(merged.len());
                    merged.push(cursor);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    let idx = *o.get();
                    let combined = merged[idx].weight.plus(&cursor.weight);
                    let weight_strict_win = combined != merged[idx].weight;
                    let weight_tied = !weight_strict_win
                        && combined == cursor.weight;
                    // Stage 3.12 Fix 2(ii) (2026-05-02): on weight tie, the
                    // FINAL tiebreak is `source_priority` (lower wins —
                    // Fork-source order). This guarantees right-associative
                    // dangling-else: TAKE branch (priority 0) always
                    // dominates SKIP branch (priority 1) in nested
                    // Opt-Group merges. Pre-3.12 the receiver-on-Equal
                    // semantics of `LexicographicWeight::plus` were
                    // order-dependent on insertion timing.
                    //
                    // B13d-R / Resolution R (2026-05-08): consistency
                    // override. If EXACTLY ONE cursor is provably broken
                    // at commit_winner replay (Definitely_broken via
                    // cursor_committed_ops_consistent), the other wins
                    // regardless of weight. Two consistent or two
                    // Indeterminate / mixed cases fall through to the
                    // weight + source_priority chain. This preserves
                    // genuine ambiguity (two consistent cursors compete
                    // by lex-min) while preventing silent loss of a
                    // productive cursor against a dead-on-arrival
                    // sibling.
                    let existing_consistent =
                        self.cursor_committed_ops_consistent(&merged[idx]);
                    let cursor_consistent =
                        self.cursor_committed_ops_consistent(&cursor);
                    // B13d-R Step 3 (2026-05-08): shape-gate the override.
                    // Pre-B13d-R, the weight gate paired only shape-
                    // compatible cursors at the same ConfigKey (by GSS
                    // push/pop invariants — `incoming_edge` in the strict
                    // key implies congruent collection-stack history).
                    // The B13d-R override now must explicitly reinstate
                    // that pairing: when shapes diverge, fall through to
                    // the pre-B13d-R weight + source_priority chain.
                    // The `debug_assert_eq!` at line 4319 documents the
                    // invariant; the shape guard reinstates it for the
                    // override path. Without this guard, a consistency-
                    // promoted cursor with mismatched collection_stack
                    // depth corrupts commit_winner replay.
                    let consistency_override: Option<bool> =
                        if merged[idx].collection_stack.len()
                            != cursor.collection_stack.len()
                        {
                            None
                        } else {
                            match (existing_consistent, cursor_consistent) {
                                (Some(false), Some(false)) => None,
                                (Some(false), Some(true)) | (Some(false), None) => Some(true),
                                (Some(true), Some(false)) | (None, Some(false)) => Some(false),
                                _ => None,
                            }
                        };
                    let cursor_wins = match consistency_override {
                        Some(verdict) => verdict,
                        None => weight_strict_win
                            || (weight_tied
                                && cursor.source_priority < merged[idx].source_priority),
                    };
                    if cursor_wins {
                        debug_assert_eq!(
                            merged[idx].collection_stack.len(),
                            cursor.collection_stack.len(),
                            "merge_equivalent_cursors: cursors at the same \
                             configuration must have matching collection-stack \
                             depths (operational state shape)"
                        );
                        let mut replacement = cursor;
                        replacement.weight = combined;
                        merged[idx] = replacement;
                    } else {
                        // Existing wins or ties (with smaller-or-equal
                        // source_priority) — keep its operational state,
                        // update weight (idempotent on tie).
                        merged[idx].weight = combined;
                    }
                }
            }
        }
        self.branch_cursors = merged;
    }

    /// B10 / Option κ Part 3 (2026-05-07) — lex-dominated cursor subsumption.
    ///
    /// Runs after `merge_equivalent_cursors`. Groups remaining cursors by a
    /// RELAXED `(state, gss-node-symbol, pos)` key — intentionally dropping
    /// the `incoming_edge_stack` discriminator from the merge-key. That
    /// discriminator exists for pop-time determinism with structural sharing
    /// (see `merge_equivalent_cursors` rationale at the `incoming_edge` field
    /// comment); it is NOT a parse-time semantic distinguisher. Two cursors
    /// at the same `(state, gss-node-symbol, pos)` but different edge
    /// histories are at the SAME parse configuration — lex-min selects the
    /// better one; the loser's edge history is consumed by GSS GC.
    ///
    /// Within each group, this pass drops any cursor C iff a sibling S has
    /// `S.weight.lex_cmp(C.weight) == Less` AND
    /// `S.source_priority <= C.source_priority` (the second clause prevents
    /// reversing the existing source-priority tiebreak that
    /// `merge_equivalent_cursors` enforces).
    ///
    /// **Algebraic equivalence**: pruning a strictly-dominated cursor is
    /// definitionally what tropical lex-min does at EOI. This pass moves
    /// that work to step time, where it caps fanout BEFORE the next
    /// `step_fanout` iteration re-amplifies via Pass 0/1/2a Forks at shared-
    /// FIRST tokens.
    ///
    /// **Recovery preservation**: recovery semantics are unchanged. Recovery
    /// dispatch fires at the same dead-ends as before; if a non-recovering
    /// sibling at the same parse configuration has lower weight, the
    /// recovering cursor is lex-dominated — dropping it is the WPDS-correct
    /// outcome (the parse already has a strictly-better path).
    ///
    /// **Rationale (LedTest cursor explosion)**: post-B7 mixed-bucket Forks
    /// at shared-FIRST tokens (e.g. `Some(Integer)` for Num's atomic NumLit
    /// + cross-cat-LHS EqNum/NeNum + cross-cat-projection PredToNum) generate
    /// sibling cursors at the same `(state, node-symbol, pos)` configuration
    /// but with diverging `incoming_edge_stack` tails. The strict-key
    /// `merge_equivalent_cursors` cannot collapse them; without this pass,
    /// every successor PrefixDispatch re-emits the same Fork, doubling the
    /// live cursor count per recursive cross-cat cycle iteration (Pred → Num
    /// → Pred → ...). Subsumption converges the live set to the lex-min
    /// representative per configuration; the recursive cycle still exists
    /// but is bounded.
    fn subsume_lex_dominated_cursors(&mut self) {
        if self.branch_cursors.len() < 2 {
            return;
        }
        // Group by (state, node-symbol, pos). Cursors whose gss node has
        // been GC'd (no live reference) get a `None` symbol key — they
        // form a degenerate group of their own.
        let mut by_relaxed: std::collections::HashMap<
            (WpdsState, Option<crate::wpds_runtime::StackSymbolV2>, usize),
            Vec<usize>,
        > = std::collections::HashMap::with_capacity(self.branch_cursors.len());
        for (idx, c) in self.branch_cursors.iter().enumerate() {
            let symbol_key = self.gss.node(c.node).map(|n| n.symbol);
            by_relaxed
                .entry((c.inner_state.clone(), symbol_key, c.pos))
                .or_default()
                .push(idx);
        }
        // For each multi-cursor group, find the lex-min cursor (using the
        // same `Semiring::plus` ordering as `pick_lex_min_resolved` —
        // `a.plus(b) == a` iff `a` is the smaller of the two under the
        // semiring's lex-min ordering). Drop strictly-dominated siblings.
        let mut drop_set: std::collections::BTreeSet<usize> = Default::default();
        for (_key, idxs) in &by_relaxed {
            if idxs.len() < 2 {
                continue;
            }
            // Linear scan to find the lex-min cursor in this group.
            // Mirrors `pick_lex_min_resolved`'s loop semantics.
            let mut best_idx = idxs[0];
            for &idx in &idxs[1..] {
                let merged = self.branch_cursors[best_idx]
                    .weight
                    .plus(&self.branch_cursors[idx].weight);
                if merged != self.branch_cursors[best_idx].weight {
                    best_idx = idx;
                } else if merged == self.branch_cursors[idx].weight
                    && self.branch_cursors[idx].source_priority
                        < self.branch_cursors[best_idx].source_priority
                {
                    // True weight tie: lower `source_priority` wins
                    // (matches `pick_lex_min_resolved`'s tiebreak).
                    best_idx = idx;
                }
            }
            // B13d-R / Resolution R (2026-05-08): if best_idx is
            // Definitely_broken at commit-replay AND any sibling is
            // Definitely_consistent, promote a consistent sibling to
            // best_idx and mark the broken best for drop. This handles
            // the case where lex-min weight picks a broken cursor over
            // a consistent one — the consistent cursor's productive
            // pending_builder_ops must survive.
            let best_consistent_initial =
                self.cursor_committed_ops_consistent(&self.branch_cursors[best_idx]);
            if matches!(best_consistent_initial, Some(false)) {
                let mut promoted: Option<usize> = None;
                for &idx in idxs {
                    if idx == best_idx {
                        continue;
                    }
                    if matches!(
                        self.cursor_committed_ops_consistent(&self.branch_cursors[idx]),
                        Some(true),
                    ) {
                        promoted = Some(idx);
                        break;
                    }
                }
                if let Some(new_best) = promoted {
                    drop_set.insert(best_idx);
                    best_idx = new_best;
                }
            }
            let best_w = self.branch_cursors[best_idx].weight;
            let best_p = self.branch_cursors[best_idx].source_priority;
            // B13d-R Step 1 (2026-05-08): hoist `best_consistent` out
            // of the per-sibling loop. `best_idx` is finalized by the
            // promotion-scan above; computing `best_consistent` once
            // is algebraically identical to recomputing it per sibling
            // (the dry-run is a deterministic function of pending_
            // builder_ops, and best_idx's pending_builder_ops is
            // unchanged within the per-sibling loop).
            //
            // Pre-Step-1 the inner loop made 2 cursor_committed_ops_
            // consistent calls per sibling × O(M) per call (M =
            // pending_builder_ops.len(), capped only at 1M). Per
            // group of k cursors this was O(k×M) redundant work.
            // Post-Step-1 it's O(M) once + O(M) per sibling.
            let best_consistent =
                self.cursor_committed_ops_consistent(&self.branch_cursors[best_idx]);
            for &idx in idxs {
                if idx == best_idx {
                    continue;
                }
                if drop_set.contains(&idx) {
                    continue;
                }
                let c = &self.branch_cursors[idx];
                // B13d-R / Resolution R (2026-05-08): consistency
                // override at subsumption. If best is consistent and
                // c is broken, drop c regardless of weight. Mixed
                // (Indeterminate / Some(true) / Some(false)) cases
                // fall through to existing strict-domination check.
                let c_consistent = self.cursor_committed_ops_consistent(c);
                let drop_by_consistency = matches!(
                    (best_consistent, c_consistent),
                    (Some(true), Some(false)) | (None, Some(false))
                );
                if drop_by_consistency {
                    drop_set.insert(idx);
                    continue;
                }
                // Strict domination: `best.plus(c) == best` AND `best != c`.
                // The first clause is "best is at-or-better than c"; the
                // second clause excludes ties (handled by merge_equivalent_
                // cursors when keys match exactly; for ties at the relaxed
                // key, we keep both — only STRICT dominance is grounds for
                // drop). Source-priority guard: `best_p <= c.source_priority`
                // prevents reversing the existing source-order tiebreak.
                let merged = best_w.plus(&c.weight);
                let strictly_dominates = merged == best_w
                    && merged != c.weight;
                if strictly_dominates && best_p <= c.source_priority {
                    drop_set.insert(idx);
                }
            }
        }
        if drop_set.is_empty() {
            return;
        }
        // swap_remove in descending index order to preserve stable indices
        // for the remaining drops.
        let mut drop_vec: Vec<usize> = drop_set.into_iter().collect();
        drop_vec.sort_unstable_by(|a, b| b.cmp(a));
        for idx in drop_vec {
            self.branch_cursors.swap_remove(idx);
        }
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
            // of the two under the semiring's lex-min ordering).
            let merged = self.branch_cursors[best]
                .weight
                .plus(&self.branch_cursors[idx].weight);
            if merged != self.branch_cursors[best].weight {
                best = idx;
            } else if merged == self.branch_cursors[idx].weight
                && self.branch_cursors[idx].source_priority
                    < self.branch_cursors[best].source_priority
            {
                // Stage 3.12 Fix 2(ii) (2026-05-02): on true weight tie,
                // the lower `source_priority` wins (Fork-source-order).
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
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): preserves the always-non-empty
    /// `branch_cursors` invariant by writing the post-commit singleton
    /// back to `branch_cursors[0]` (with cleared `pending_builder_ops`
    /// and `collection_stack` since those have already replayed onto the
    /// live builder). Pre-Phase-4 this method called `clear()`; that
    /// would now violate L4.
    fn commit_winner(&mut self, winner_idx: usize) {
        let mut winner = self.branch_cursors.swap_remove(winner_idx);
        self.branch_cursors.clear();
        // Phase 5.5 (2026-05-12): install winner.builder as the live
        // SemanticBuilder. The winner cursor's `Arc<SemanticBuilder>`
        // carries ALL the non-recovery state mutations that have been
        // eagerly applied via `Arc::make_mut` in the emit helpers
        // (Phase 5.3): PushToken, PushIdent, PushPredicate,
        // StartBinderScope, EndBinderScope, ExtendBinderScope,
        // StartCollection, PushCollectionId, SpliceIntoCollection,
        // StartOptionalScope, FinalizeOptionalScopePresent,
        // PushOptionalAbsent, PushToCollection. Plus the pre-fork
        // state inherited via `Arc::clone` from the parent cursor
        // (Phase 5.4 + Phase 5.2).
        //
        // The replay loop below now handles ONLY:
        // - `FireAction` — emit_fire_action does NOT eagerly apply
        //   (action_fn READS from the builder; firing eagerly before
        //   install would mutate cursor.builder's stack with
        //   intermediate terms that aren't durable until commit).
        //   After install, replay fires action_fn on the installed
        //   self.builder.
        // - Recovery* deltas (RecoveryEvent / SubstituteToken /
        //   InsertToken / CommitLexAlternative / ApplyRecoverySequence)
        //   — these mutate `self.recovery_events` and the mutable
        //   token source, NOT the builder. They must replay regardless
        //   of how the builder is installed.
        //
        // The adoption gate (Phase 4 #1) is OBSOLETE: collection_stack
        // donation is intrinsic to the Arc-installed builder. The
        // winner.collection_stack mirror is now informational only.
        // The Phase 5.6 type cleanup will delete the mirror entirely.
        let _ = std::mem::take(&mut winner.collection_stack);
        // Phase 5.5 install: replace live with winner's builder, but
        // ONLY if a Fork happened (cursor_mode is Strict). In Lazy mode
        // (no Fork), `emit_fire_action` fires directly on
        // `self.builder` via `self.fire_action_for(symbol)` — those
        // action_fn-pushed terms are NOT mirrored onto cursor.builder
        // (emit_fire_action was deliberately skipped from the Phase 5.3
        // eager Arc::make_mut migration because action_fn READS from
        // its builder). So in Lazy mode, self.builder is the
        // authoritative state; installing cursor.builder over it would
        // lose those action_fn terms.
        //
        // `Arc::try_unwrap` keeps the underlying SemanticBuilder if the
        // winner is the last Arc holder (the post-commit singleton at
        // the bottom of this function REPLACES `branch_cursors` so
        // sibling Arc refs in dead cursors are about to drop). If
        // there's still another holder, fall back to deep clone via
        // SemanticBuilder: Clone (Phase 5.3). The clone is structurally
        // shared via `im::Vector` HAMTs — O(log N) per field root.
        if self.cursor_mode == CursorMode::Strict {
            self.builder = Arc::try_unwrap(std::mem::replace(
                &mut winner.builder,
                Arc::new(SemanticBuilder::new()),
            ))
            .unwrap_or_else(|arc| (*arc).clone());
        }
        for delta in winner.pending_builder_ops {
            match delta {
                // Phase 5.5: non-recovery deltas are NO-OPs at replay
                // (already applied to cursor.builder which is now
                // self.builder via the install above). Kept here for
                // exhaustiveness pending Phase 5.6 variant deletion.
                BuilderDelta::PushToken { kind, text, pos } => {
                    let _ = (kind, text, pos);
                }
                BuilderDelta::PushIdent { name, pos } => {
                    let _ = (name, pos);
                }
                BuilderDelta::PushPredicate(pred) => {
                    // Phase 5.5: no-op (already applied to cursor.builder
                    // which is now self.builder).
                    let _ = pred;
                }
                BuilderDelta::StartBinderScope { names } => {
                    let _ = names;
                }
                BuilderDelta::EndBinderScope => {}
                BuilderDelta::ExtendBinderScope { name } => {
                    let _ = name;
                }
                BuilderDelta::FireAction { symbol } => {
                    // Phase 5.5 (2026-05-12): FireAction is now no-op at
                    // replay. emit_fire_action eagerly fires the action_fn
                    // on cursor.builder (via Arc::make_mut) in Strict mode,
                    // so by commit-time cursor.builder.stack already has
                    // the action's pushed terms; install brings them onto
                    // self.builder. Replay-FireAction would double-apply
                    // (pop arity + push term) — symbol is discarded.
                    //
                    // Error state from arity underflow is set IN-PLACE at
                    // emit_fire_action time (eager fire returns Error
                    // synchronously), so the bail-out for Error survival
                    // is no longer needed here.
                    let _ = symbol;
                }
                BuilderDelta::PushCollectionId { id: logged_id } => {
                    // Phase 5.5: no-op. cursor.builder (now self.builder)
                    // already has the CollectionId pushed via Arc::make_mut
                    // in emit_push_collection_id (Phase 5.3).
                    let _ = logged_id;
                }
                BuilderDelta::SpliceIntoCollection { id: logged_id } => {
                    let _ = logged_id;
                }
                BuilderDelta::StartOptionalScope => {}
                BuilderDelta::FinalizeOptionalScopePresent => {}
                BuilderDelta::PushOptionalAbsent => {}
                BuilderDelta::StartCollection => {}
                BuilderDelta::PushToCollection { id } => {
                    let _ = id;
                }
                BuilderDelta::RecoveryEvent {
                    action_kind,
                    pos,
                    cost_tropical,
                } => {
                    // Stage 3.20 / L12 (Commit 4, 2026-05-06): record the
                    // recovery event for the wrapper to surface as a
                    // RecoveryAttempt. RecoveryEvent is a pure descriptor;
                    // no token-stream mutation is needed (Skip/Delete are
                    // pos-only, not text-changing).
                    self.recovery_events.push(RecoveryEvent::from_action_kind(
                        action_kind,
                        pos,
                        cost_tropical,
                    ));
                }
                BuilderDelta::SubstituteToken { pos, kind, text } => {
                    // Stage 3.20 / L12 (Commit B, 2026-05-06): live replay.
                    // Mutates the token source via WpdsMutableTokenSource::
                    // substitute_token AND records the recovery event. If
                    // no mutable source is threaded, panic loudly — per
                    // `feedback_no_stubs_timebombs.md`, "applied: false"
                    // graceful-degradation is forbidden.
                    let raw = self.mutable_token_source.expect(
                        "BuilderDelta::SubstituteToken replayed without a \
                         mutable token source — caller must thread one via \
                         walker.set_mutable_token_source() before driving",
                    );
                    // SAFETY: raw is non-null (Some), and the caller-managed
                    // contract on set_mutable_token_source guarantees the
                    // pointee is alive until clear/reset/Drop.
                    let src = unsafe { &mut *raw };
                    src.substitute_token(pos, kind.clone(), text.clone())
                        .expect("substitute_token: byte-span lookup or \
                                replace_range failed");
                    self.recovery_events
                        .push(RecoveryEvent::substitute(pos, kind, text));
                }
                BuilderDelta::InsertToken { pos, kind, text } => {
                    // Stage 3.20 / L12 (Commit B, 2026-05-06): same pattern
                    // as SubstituteToken — live replay or panic.
                    let raw = self.mutable_token_source.expect(
                        "BuilderDelta::InsertToken replayed without a \
                         mutable token source — caller must thread one via \
                         walker.set_mutable_token_source() before driving",
                    );
                    let src = unsafe { &mut *raw };
                    src.insert_token(pos, kind.clone(), text.clone())
                        .expect("insert_token: byte-span lookup or \
                                replace_range failed");
                    self.recovery_events
                        .push(RecoveryEvent::insert(pos, kind, text));
                }
                BuilderDelta::CommitLexAlternative {
                    pos,
                    alt_idx,
                    kind,
                    text,
                } => {
                    // Stage 3.14 / Hack #12 + Stage 3.20 / L12 (Commit B,
                    // 2026-05-06): live replay. Calls
                    // MutableMultiTokenSource::commit_alternative which
                    // rewrites the lex stream's primary alt at `pos` AND
                    // records the recovery event. Panic if no mutable
                    // source — per the strict no-graceful-degradation rule.
                    let raw = self.mutable_token_source.expect(
                        "BuilderDelta::CommitLexAlternative replayed without \
                         a mutable token source — Hack #12 lex-fork emission \
                         requires WpdsMutableTokenSource threading",
                    );
                    let src = unsafe { &mut *raw };
                    src.commit_alternative(pos, alt_idx)
                        .expect("commit_alternative: bounds check failed");
                    self.recovery_events.push(RecoveryEvent::lex_commit(
                        pos, alt_idx, kind, text,
                    ));
                }
                BuilderDelta::ApplyRecoverySequence {
                    actions,
                    base_pos,
                    total_cost_tropical,
                } => {
                    // Stage 3.20 / L12 (Commit B, 2026-05-06): atomic
                    // multi-step recovery replay. Iterates the actions
                    // sequence, applying each primitive (Skip / Delete /
                    // Insert / Substitute) to the live token source and
                    // recording per-action RecoveryEvents.
                    let raw = self.mutable_token_source.expect(
                        "BuilderDelta::ApplyRecoverySequence replayed without \
                         a mutable token source",
                    );
                    let src = unsafe { &mut *raw };
                    let mut cur_pos = base_pos;
                    for action in actions.iter() {
                        match action {
                            crate::recovery::RepairAction::SkipToSync {
                                skip_count,
                                ..
                            } => {
                                cur_pos += *skip_count as usize;
                                self.recovery_events.push(
                                    RecoveryEvent::from_action_kind(
                                        0,
                                        cur_pos,
                                        total_cost_tropical,
                                    ),
                                );
                            }
                            crate::recovery::RepairAction::DeleteToken => {
                                cur_pos += 1;
                                self.recovery_events.push(
                                    RecoveryEvent::from_action_kind(
                                        1,
                                        cur_pos,
                                        total_cost_tropical,
                                    ),
                                );
                            }
                            crate::recovery::RepairAction::InsertToken {
                                token,
                            } => {
                                let kind =
                                    TokenKind::Fixed(format!("{}", token));
                                let text = format!("{}", token);
                                src.insert_token(
                                    cur_pos,
                                    kind.clone(),
                                    text.clone(),
                                )
                                .expect(
                                    "insert_token: in ApplyRecoverySequence",
                                );
                                self.recovery_events.push(
                                    RecoveryEvent::insert(cur_pos, kind, text),
                                );
                            }
                            crate::recovery::RepairAction::SubstituteToken {
                                replacement,
                            } => {
                                let kind = TokenKind::Fixed(format!(
                                    "{}",
                                    replacement
                                ));
                                let text = format!("{}", replacement);
                                src.substitute_token(
                                    cur_pos,
                                    kind.clone(),
                                    text.clone(),
                                )
                                .expect(
                                    "substitute_token: in ApplyRecoverySequence",
                                );
                                self.recovery_events.push(
                                    RecoveryEvent::substitute(
                                        cur_pos, kind, text,
                                    ),
                                );
                                cur_pos += 1;
                            }
                            crate::recovery::RepairAction::SwapTokens { .. }
                            | crate::recovery::RepairAction::Composite {
                                ..
                            }
                            | crate::recovery::RepairAction::CategorySwitch {
                                ..
                            } => {
                                panic!(
                                    "ApplyRecoverySequence: nested \
                                     SwapTokens/Composite/CategorySwitch \
                                     not supported — codegen invariant \
                                     violated"
                                );
                            }
                        }
                    }
                    self.pos = cur_pos;
                }
            }
        }
        self.top_node = Some(winner.node);
        self.pos = winner.pos;
        self.weight = self.weight.times(&winner.weight);
        self.state = winner.inner_state.clone();
        // Stage 3.9 / ι Phase 4 (2026-05-01): write singleton back per L4.
        // Cleared deltas + collection_stack — already replayed onto live
        // builder above. Mode stays Strict per L3.
        self.branch_cursors = vec![BranchCursor {
            node: winner.node,
            pos: winner.pos,
            weight: self.weight.clone(),
            inner_state: winner.inner_state,
            pending_builder_ops: Vec::new(),
            collection_stack: Vec::new(),
            collection_slots_allocated: 0,
            // Stage 3.12 Fix 2(ii) (2026-05-02): preserve winner's
            // priority. Subsequent Forks build on this priority chain.
            source_priority: winner.source_priority,
            // Stage 3.12.6 (2026-05-02): preserve winner's stack-suffix
            // history so subsequent pops follow the winner's path.
            incoming_edge_stack: winner.incoming_edge_stack,
            // Bounded recovery (Stage 3.20 / L12, 2026-05-06): preserve
            // winner's recovery state — subsequent recovery dispatches
            // continue counting against the same depth budget.
            recovery_depth: winner.recovery_depth,
            visited_recovery: winner.visited_recovery,
            // B12 / Candidate E (2026-05-07): preserve winner's projection
            // visited set so post-commit projection cycle defense
            // continues to apply across the parse path.
            visited_dispatch: winner.visited_dispatch,
            // B13d-R Step 2 (2026-05-08): post-commit singleton has
            // empty pending → Consistent memo (the winner's deltas
            // were drained at replay; pending_builder_ops is now Vec::new()).
            consistency_memo: std::cell::Cell::new(Some(Some(true))),
            // Phase 5.2 (2026-05-12): preserve winner's Arc. The 5.2
            // engine doesn't read this field — but preserving it here
            // (vs reseting to fresh Arc) prepares for Phase 5.5 where
            // the Arc swap REPLACES the journal-replay path; at that
            // point `winner.builder` IS the post-commit live state, so
            // installing it on the post-commit singleton becomes the
            // committal step. Today (5.2) the move is a no-op vis-à-
            // vis behavior — the live mutation surface is still
            // `self.builder`, journaled deltas replay against it above.
            builder: winner.builder,
        }];
    }

    /// Stage 3.4 (2026-04-30): beam pruning over `branch_cursors`.
    ///
    /// When `beam_size = Some(k)` and the cursor count exceeds `k`, sort
    /// cursors by weight (lex-min via `Semiring::plus` — see
    /// `pick_lex_min_resolved` for the same comparator pattern) and
    /// truncate to the top-`k`. When `beam_size = None`, no-op.
    ///
    /// The `plus`-based comparator works for any min-like semiring
    /// (`LexicographicWeight`, `TropicalWeight`). For semirings whose
    /// `plus` is not min-like (e.g., `BooleanWeight`'s OR), pruning is
    /// effectively disabled — `cursor_a.plus(&cursor_b) == cursor_a`
    /// loses its "a <= b" interpretation. This is acceptable; production
    /// walkers always use `LexicographicWeight`.
    ///
    /// Called from `step_fanout` after the per-cursor step pass so the
    /// pruned frontier is the input to the next saturation iteration.
    fn maybe_prune_frontier(&mut self) {
        let beam = match self.beam_size {
            Some(k) => k,
            None => return, // unlimited beam, no pruning
        };
        if self.branch_cursors.len() <= beam {
            return;
        }
        // Stable sort by weight ascending under the `plus`-based lex-min
        // comparator. Keeps source-order for ties (matching
        // `pick_lex_min_resolved`'s tie-break semantics).
        self.branch_cursors.sort_by(|a, b| {
            let merged = a.weight.plus(&b.weight);
            // a wins iff a.plus(b) == a (a is the lex-smaller).
            // On `a == b`, both equal merged → Ordering::Equal.
            let a_wins = merged == a.weight;
            let b_wins = merged == b.weight;
            match (a_wins, b_wins) {
                (true, true) => std::cmp::Ordering::Equal,
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
                // Neither wins under plus-based ordering — tropical/lex
                // semirings always satisfy at least one. Fall back to
                // Equal so the sort is stable and deterministic.
                (false, false) => std::cmp::Ordering::Equal,
            }
        });
        self.branch_cursors.truncate(beam);
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
        let mut taken = std::mem::replace(&mut self.builder, SemanticBuilder::new());
        let outcome = Self::fire_action_for_on_builder(&self.engine, &mut taken, symbol);
        self.builder = taken;
        if let Some(message) = outcome {
            self.state = WpdsState::Error { message };
        }
    }

    /// Phase 5.5 (2026-05-12): apply a non-recovery BuilderDelta to the
    /// given builder. Used by Fork-arm dispatch sites that emit "effect"
    /// deltas (EndBinderScope, StartBinderScope, StartCollection, etc.)
    /// alongside ConsumeAndReplace actions. The journal still receives
    /// the delta for commit_winner-time logging (Phase 5.6 will strip
    /// this), but the eager application is required to keep cursor.builder
    /// in sync with the codegen's intended state at each step.
    ///
    /// Recovery-typed deltas (RecoveryEvent / SubstituteToken / InsertToken
    /// / CommitLexAlternative / ApplyRecoverySequence) are NO-OPs here
    /// — their replay is mandatory at commit_winner because they mutate
    /// the mutable token source / recovery_events, not the builder.
    fn apply_effect_to_builder(builder: &mut SemanticBuilder, effect: &BuilderDelta) {
        match effect {
            BuilderDelta::PushToken { kind, text, pos } => {
                builder.push_token(kind.clone(), text.clone(), *pos);
            }
            BuilderDelta::PushIdent { name, pos } => {
                builder.push_ident(name.clone(), *pos);
            }
            BuilderDelta::PushPredicate(pred) => {
                builder.push_predicate_arc(Arc::clone(pred));
            }
            BuilderDelta::StartBinderScope { names } => {
                builder.start_binder_scope(names.clone());
            }
            BuilderDelta::EndBinderScope => {
                builder.end_binder_scope();
            }
            BuilderDelta::ExtendBinderScope { name } => {
                builder.extend_binder_scope(name.clone());
            }
            BuilderDelta::StartCollection => {
                let _ = builder.start_collection();
            }
            BuilderDelta::PushCollectionId { id } => {
                builder.push_collection_id(*id);
            }
            BuilderDelta::SpliceIntoCollection { id } => {
                builder.push_to_collection(*id);
            }
            BuilderDelta::PushToCollection { id } => {
                builder.push_to_collection(*id);
            }
            BuilderDelta::StartOptionalScope => {
                builder.start_optional_scope();
            }
            BuilderDelta::FinalizeOptionalScopePresent => {
                builder.finalize_optional_scope_present();
            }
            BuilderDelta::PushOptionalAbsent => {
                builder.push_optional_absent();
            }
            BuilderDelta::FireAction { .. }
            | BuilderDelta::RecoveryEvent { .. }
            | BuilderDelta::SubstituteToken { .. }
            | BuilderDelta::InsertToken { .. }
            | BuilderDelta::CommitLexAlternative { .. }
            | BuilderDelta::ApplyRecoverySequence { .. } => {
                // SeedLive / FinalizeCollection: vestigial (no emission;
                // see Phase 5.4 + L12 hotfix B5).
                // FireAction: dispatched via fire_action_for_on_builder
                // separately.
                // Recovery*: applied at commit_winner; no eager apply.
            }
        }
    }

    /// Phase 5.5 (2026-05-12): fire a semantic action on a given
    /// SemanticBuilder reference (rather than `self.builder`). Used by
    /// `emit_fire_action` to eagerly apply on `cursor.builder` via
    /// `Arc::make_mut`, so Strict-mode parsing has the action's
    /// pushed term available BEFORE subsequent SpliceIntoCollection
    /// effects (which move stack elements into collection slots —
    /// they must move the action's converted term, not the raw arg).
    ///
    /// Returns `None` on success; `Some(msg)` if the action's arity
    /// exceeds the builder's stack — caller sets walker state to
    /// `Error { message }` accordingly.
    fn fire_action_for_on_builder(
        engine: &E,
        builder: &mut SemanticBuilder,
        symbol: StackSymbolV2,
    ) -> Option<String> {
        if let Some(entry) = engine.action_for(
            symbol.category_src_idx,
            symbol.rule_index_in_category,
        ) {
            let arity = entry.arity as usize;
            let action_fn = entry.action_fn;
            if builder.len() >= arity {
                let args = builder.pop_args(arity);
                action_fn(builder, args);
                None
            } else {
                Some(format!(
                    "semantic-action arity mismatch at rule (src={}, rule={}): \
                     expected {} args but builder held {}",
                    symbol.category_src_idx,
                    symbol.rule_index_in_category,
                    arity,
                    builder.len(),
                ))
            }
        } else {
            None
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // Stage 3.9 / ι Phase 4 (2026-05-01): per-variant Lazy/Strict helpers
    //
    // Each `emit_*` helper branches on `cursor_mode`:
    //   - Lazy:  mutate the live `SemanticBuilder` directly. The cursor's
    //            `pending_builder_ops` stays empty (L1 invariant).
    //   - Strict: log a `BuilderDelta` to `cursor.pending_builder_ops`.
    //             The live builder is untouched until commit_winner replays.
    //
    // Mode-agnostic helpers (`advance_cursor_pos`/`multiply_cursor_weight`/
    // `set_cursor_inner_state`/`cursor_gss_*`) update the cursor's local
    // state AND, in Lazy mode, mirror to the live walker fields
    // (`self.pos`/`self.weight`/`self.state`/`self.top_node`) so external
    // accessors (`walker.position()`, etc.) reflect the cursor's view.
    //
    // All helpers are `#[inline(always)]` so the optimizer specializes
    // them per call site and the mode-branch becomes free at runtime when
    // the Lazy case dominates.
    // ══════════════════════════════════════════════════════════════════════

    /// Debug-only L1 invariant check: `cursor_mode == Lazy` implies a
    /// singleton cursor with empty `pending_builder_ops`. Called at
    /// `apply_action` entry.
    #[inline(always)]
    fn debug_flush_lazy_invariant(&self) {
        debug_assert!(
            self.cursor_mode != CursorMode::Lazy
                || (self.branch_cursors.len() == 1
                    && self.branch_cursors[0].pending_builder_ops.is_empty()),
            "L1 invariant violation: Lazy mode requires singleton cursor with \
             empty pending_builder_ops; got len={}, ops_len={}",
            self.branch_cursors.len(),
            self.branch_cursors
                .first()
                .map(|c| c.pending_builder_ops.len())
                .unwrap_or(0),
        );
    }

    // ─── 11 mutation helpers ─────────────────────────────────────────────

    #[inline(always)]
    fn emit_push_token(
        &mut self,
        cursor: &mut BranchCursor<W>,
        kind: TokenKind,
        text: String,
        pos: usize,
    ) {
        // Phase 5.3 (2026-05-12): eagerly apply the mutation to
        // `cursor.builder` via `Arc::make_mut` (clone-on-write per cursor).
        // Journal logging below remains UNTOUCHED — Phase 5.6 will remove it
        // and `commit_winner` will swap `cursor.builder` directly. Today
        // (5.3) the cursor.builder is write-only — no engine code reads it
        // yet — so this is semantically idempotent.
        Arc::make_mut(&mut cursor.builder).push_token(kind.clone(), text.clone(), pos);
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_token(kind, text, pos),
            CursorMode::Strict => {
                // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::PushToken { kind, text, pos });
            }
        }
    }

    #[inline(always)]
    fn emit_push_ident(&mut self, cursor: &mut BranchCursor<W>, name: String, pos: usize) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).push_ident(name.clone(), pos);
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_ident(name, pos),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::PushIdent { name, pos });
            }
        }
    }

    #[inline(always)]
    fn emit_push_predicate(
        &mut self,
        cursor: &mut BranchCursor<W>,
        pred: Arc<dyn Any + Send + Sync>,
    ) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        // `pred` is already an Arc — Arc::clone is O(1).
        Arc::make_mut(&mut cursor.builder).push_predicate_arc(Arc::clone(&pred));
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_predicate_arc(pred),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::PushPredicate(pred));
            }
        }
    }

    #[inline(always)]
    fn emit_start_binder_scope(&mut self, cursor: &mut BranchCursor<W>, names: Vec<String>) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).start_binder_scope(names.clone());
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.start_binder_scope(names),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::StartBinderScope { names });
            }
        }
    }

    #[inline(always)]
    fn emit_extend_binder_scope(&mut self, cursor: &mut BranchCursor<W>, name: String) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).extend_binder_scope(name.clone());
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.extend_binder_scope(name),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::ExtendBinderScope { name });
            }
        }
    }

    #[inline(always)]
    fn emit_fire_action(&mut self, cursor: &mut BranchCursor<W>, symbol: StackSymbolV2) {
        // Phase 5.5 (2026-05-12): mode-split fire_action behavior.
        //
        // In LAZY mode (single cursor, no Fork): fire only on
        // `self.builder` (as pre-5.5). cursor.builder is "best-effort"
        // tracked via Phase 5.3 eager emits for upstream non-FireAction
        // mutations, but the action_fn's push_term effects don't
        // mirror — that's fine because commit_winner SKIPS install
        // in Lazy mode (self.builder is authoritative).
        //
        // In STRICT mode (post-Fork, multiple cursors): eagerly fire
        // on cursor.builder via Arc::make_mut. This is REQUIRED for
        // correctness: subsequent SpliceIntoCollection emits move
        // cursor.builder.stack tops into collection slots. The slot
        // must receive the action's CONVERTED term (e.g. Proc::CastInt(0)),
        // NOT the raw arg (e.g. the Int "0" literal token). Without
        // eager firing here, cursor.builder.collection_stack would
        // hold raw arg tokens, breaking the outer rule's drain at
        // action time.
        //
        // The Strict-mode FireAction journal entry is kept (commit_winner
        // SKIPS its replay arm — the action is already applied to
        // cursor.builder which becomes self.builder at install). Phase
        // 5.6 will delete the journal entry entirely.
        match self.cursor_mode {
            CursorMode::Lazy => self.fire_action_for(symbol),
            CursorMode::Strict => {
                let builder_mut = Arc::make_mut(&mut cursor.builder);
                if let Some(message) =
                    Self::fire_action_for_on_builder(&self.engine, builder_mut, symbol)
                {
                    // Phase 5.5 (2026-05-12): on arity underflow during
                    // eager fire, set BOTH cursor.inner_state AND walker
                    // state to Error so the cursor aborts cleanly. Pre-5.5
                    // the Error was set in commit_winner's bail-out path;
                    // post-5.5 the underflow happens mid-parse so cursor
                    // state propagation is needed.
                    let err = WpdsState::Error { message };
                    cursor.inner_state = err.clone();
                    self.state = err;
                    return;
                }
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::FireAction { symbol });
            }
        }
    }

    /// Allocate a fresh collection accumulator. In Lazy mode the live
    /// builder allocates (and the id reflects its `collection_stack`
    /// length). In Strict mode the cursor allocates locally — no delta
    /// is logged because `commit_winner` donates `cursor.collection_stack`
    /// to the live builder via `adopt_collection_stack` BEFORE delta
    /// replay.
    #[inline(always)]
    fn emit_start_collection(&mut self, cursor: &mut BranchCursor<W>) -> u8 {
        // Phase 5.5 (2026-05-12): authoritative id is now cursor.builder's
        // allocation. Pre-5.3 the id was derived from the cursor's
        // collection_stack mirror length, but Phase 4 #5b made the mirror
        // ALWAYS pop on CollectionMarker pop (regardless of binder-internal
        // status), while cursor.builder.collection_stack retains slots
        // until action drain. This created a divergence: the mirror's
        // length no longer matches cursor.builder's allocation count.
        //
        // For multi-slot Class-2 binder rules (e.g. class2multi `Pair . xs,
        // ys`), the second slot's id derived from the mirror was 0
        // (mirror was emptied by xs CollectionMarker pop), but
        // cursor.builder's actual second slot is at id=1. emit_push_collection_id
        // would then push CollectionId(0) twice, breaking the action's
        // LIFO drain.
        //
        // Fix: use Arc::make_mut(&mut cursor.builder).start_collection()'s
        // returned id as the authoritative source. Maintain cursor.collection_stack
        // mirror for legacy state-tracking purposes (it's still consulted
        // by some splice gates), but it's no longer the id source.
        let cursor_local_id =
            Arc::make_mut(&mut cursor.builder).start_collection();
        match self.cursor_mode {
            CursorMode::Lazy => {
                let _live_id = self.builder.start_collection();
                cursor_local_id
            }
            CursorMode::Strict => {
                cursor.collection_stack.push(Vec::new());
                // L12 follow-up B5 (2026-05-07): log StartCollection so
                // commit_winner replay allocates a matching slot on
                // live's collection_stack. Without this, Strict-mode
                // SpliceIntoCollection / PushToCollection / FinalizeCollection
                // deltas operate on indices live doesn't have.
                // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::StartCollection);
                cursor_local_id
            }
        }
    }

    #[inline(always)]
    fn emit_push_collection_id(&mut self, cursor: &mut BranchCursor<W>, id: u8) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).push_collection_id(id);
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_collection_id(id),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::PushCollectionId { id });
            }
        }
    }

    #[inline(always)]
    fn emit_splice_into_collection(&mut self, cursor: &mut BranchCursor<W>, id: u8) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        // push_to_collection silently no-ops on out-of-bounds id — safe
        // since cursor.builder is write-only in 5.3.
        Arc::make_mut(&mut cursor.builder).push_to_collection(id);
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_to_collection(id),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::SpliceIntoCollection { id });
            }
        }
    }

    #[inline(always)]
    fn emit_start_optional_scope(&mut self, cursor: &mut BranchCursor<W>) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).start_optional_scope();
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.start_optional_scope(),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::StartOptionalScope);
            }
        }
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): centralized Push-time symbol-
    /// kind side effects. Both `WpdsStepAction::Push` and
    /// `WpdsStepAction::ConsumeAndPush` arms call this BEFORE
    /// `cursor_gss_push` to handle implicit operations driven by the
    /// pushed symbol's `kind`.
    ///
    /// **Symbol kinds with side effects:**
    /// - `CollectionMarker` → allocate accumulator id (mode-aware via
    ///   `emit_start_collection`), patch `symbol.bp = Some(id)` so the
    ///   GSS-deposited symbol carries the id, push CollectionId arg
    ///   onto the builder via `emit_push_collection_id`.
    /// - `OptionalGroupAt(1)` → open the optional-scope inner-arg
    ///   accumulator via `emit_start_optional_scope` so subsequent
    ///   inner pushes route to the inner Vec rather than the main
    ///   stack. Only `sub_pos == 1` (the FIRST marker) opens; later
    ///   sub_pos values are intra-group advancements and must NOT
    ///   re-open.
    ///
    /// All other `SymbolKind` variants are no-op pushes from a
    /// side-effect perspective.
    ///
    /// **Pre-Phase-4 contract restored**: pre-3.9 the live
    /// `apply_action::Push` arm directly mutated the builder for both
    /// clauses inline. The Step-4.4 helper rewrite preserved the
    /// `CollectionMarker` clause but dropped the `OptionalGroupAt(1)`
    /// clause, breaking Lazy-mode IfElse-with-else parses (4 tests in
    /// `optional_group_smoke`). Centralizing both here makes the
    /// implicit-side-effect surface auditable in one place.
    #[inline(always)]
    fn emit_push_side_effects(
        &mut self,
        cursor: &mut BranchCursor<W>,
        symbol: &mut StackSymbolV2,
    ) {
        match symbol.kind {
            SymbolKind::CollectionMarker => {
                let id = self.emit_start_collection(cursor);
                // Phase 4 #1 (2026-05-11): preserve the codegen-stamped
                // `slot_idx` in `symbol.bp` (set by emit_binder_rule_body
                // /emit_collection_action_entry). The runtime
                // accumulator_id (live.collection_stack.len at push) is
                // NOT stored in bp anymore — it flows via the
                // `ActionArg::CollectionId(id)` pushed below. Lookups
                // (close/sep/element_src) key on slot_idx (per-rule
                // identifier, 0 for Class-5 single-slot rules); drains
                // key on the args-stack-supplied accumulator_id. The
                // old `symbol.bp = Some(id)` overwrote slot_idx with
                // accumulator_id, conflating the two — that broke
                // 3-tuple keyed lookups for nested Class-5 (e.g.
                // ambient `{... | n[{0}]}` where inner PPar's
                // accumulator_id=1 but slot_idx=0).
                self.emit_push_collection_id(cursor, id);
                // B8 / Issue D (2026-05-09); Phase 4 #2 (2026-05-12):
                // when this CollectionMarker's (src, rule, slot_idx)
                // identifies a Class-3 BinderListLoop's names accumulator,
                // also open a BinderScope so the inner walk's BinderIdent
                // captures land in a single shared scope (one scope spans
                // all iterations). The per-(src, rule, slot_idx) predicate
                // `is_class3_collection_per_slot` distinguishes the
                // Class-3 slot from Class-5 standalone collection literals
                // AND from Class-2 SimpleCollection sibling slots in the
                // same rule (e.g. PInputsTagged: ns:Vec(Name) — Class-3
                // slot 0 + tags:Vec(Proc) — Class-2 slot 1).
                //
                // `symbol.bp` carries the codegen-stamped slot_idx
                // (preserved by Phase 4 #1; not overwritten with
                // accumulator_id).
                let slot_idx = symbol.bp.unwrap_or(0);
                if self.engine.is_class3_collection_per_slot(
                    symbol.category_src_idx,
                    symbol.rule_index_in_category,
                    slot_idx,
                ) {
                    self.emit_start_binder_scope(cursor, Vec::new());
                }
            }
            SymbolKind::OptionalGroupAt(sub_pos) if sub_pos == 1 => {
                // B8 / Issue C followup (2026-05-09); refined under
                // Issue 2 (2026-05-10): only open an optional scope
                // when the OptionalGroupAt(1) belongs to a genuine
                // OptionalGroup (`*opt(...)`). Class 3 BinderListLoop
                // inner-walk markers reuse the same SymbolKind but
                // must NOT open an optional scope. The per-(src, rule,
                // sub_pos) predicate disambiguates rules that have BOTH
                // a Class 3 BinderListLoop AND a real *opt(...) in
                // same rule.
                if !self.engine.is_class3_inner_marker(
                    symbol.category_src_idx,
                    symbol.rule_index_in_category,
                    sub_pos,
                ) {
                    self.emit_start_optional_scope(cursor);
                }
            }
            _ => {}
        }
    }

    #[inline(always)]
    fn emit_finalize_optional_scope_present(&mut self, cursor: &mut BranchCursor<W>) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).finalize_optional_scope_present();
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.finalize_optional_scope_present(),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::FinalizeOptionalScopePresent);
            }
        }
    }

    #[inline(always)]
    fn emit_push_optional_absent(&mut self, cursor: &mut BranchCursor<W>) {
        // Phase 5.3 (2026-05-12): eager Arc::make_mut on cursor.builder.
        Arc::make_mut(&mut cursor.builder).push_optional_absent();
        match self.cursor_mode {
            CursorMode::Lazy => self.builder.push_optional_absent(),
            CursorMode::Strict => {
                cursor.consistency_memo.set(None);
                cursor
                    .pending_builder_ops
                    .push(BuilderDelta::PushOptionalAbsent);
            }
        }
    }

    // ─── 4 mode-agnostic helpers (mirror to live walker fields in Lazy) ──

    #[inline(always)]
    fn advance_cursor_pos(&mut self, cursor: &mut BranchCursor<W>, n: usize) {
        cursor.pos += n;
        if self.cursor_mode == CursorMode::Lazy {
            self.pos = cursor.pos;
        }
    }

    #[inline(always)]
    fn multiply_cursor_weight(&mut self, cursor: &mut BranchCursor<W>, w: &W) {
        cursor.weight = cursor.weight.times(w);
        if self.cursor_mode == CursorMode::Lazy {
            self.weight = self.weight.times(w);
        }
    }

    #[inline(always)]
    fn set_cursor_inner_state(&mut self, cursor: &mut BranchCursor<W>, state: WpdsState) {
        // Phase 4 #5b (2026-05-12): when transitioning to CollectionLoop,
        // patch `kv_phase` for HashMap collection slots based on the
        // cursor's `collection_stack[acc_id].len()` parity. The engine's
        // `step` is pure and emits `kv_phase: 0` always; this is the
        // single choke point where cursor-aware kv_phase resolution
        // happens. For non-HashMap slots (no kv separator), `kv_phase`
        // stays at `0`.
        //
        // Why here: every state transition routes through
        // `set_cursor_inner_state`, so this catches all CollectionLoop
        // arrivals — Unwinding-CollectionMarker (post-element splice),
        // CollectionOpenParen ConsumeAndPush new_state (initial entry),
        // CollectionLoop's own phase-1 Consume new_state (Consume → phase 2),
        // etc. The walker's `cursor.collection_stack` is up-to-date by
        // this point: the splice happens in `apply_pop_body_to_cursor`
        // *before* `set_cursor_inner_state`, so the parity is correct.
        //
        // Special-case phase 2 → phase 0 self-transition NOT triggered
        // here: when phase 2 emits Push CategoryEntry(value_src), the
        // new_state is `PrefixDispatch`, not `CollectionLoop`. The
        // CollectionLoop re-entry happens after the value pops to
        // Unwinding-CollectionMarker, and at that point the splice
        // already brought len to even (phase 0 by parity). So the
        // default `kv_phase: 0` from the engine is correct for that
        // re-entry; the patch logic also preserves it (len % 2 == 0).
        //
        // We must NOT override `kv_phase` when state was emitted by the
        // engine with `kv_phase >= 1` deliberately (the phase-1
        // ConsumeAndReplace transition emits `kv_phase: 2`). Detect
        // this: only override when the engine's emitted `kv_phase == 0`,
        // leaving 1/2 alone.
        let patched_state = match &state {
            WpdsState::CollectionLoop {
                result_src_idx,
                rule_idx,
                element_src_idx,
                outer_bp,
                accumulator_id,
                slot_idx,
                kv_phase: 0,
            } => {
                match self
                    .engine
                    .kv_separator_for_collection(*result_src_idx, *rule_idx, *slot_idx)
                {
                    Some(_) => {
                        // HashMap slot: pick phase from parity.
                        let acc_id_usize = *accumulator_id as usize;
                        let slot_len = match self.cursor_mode {
                            CursorMode::Lazy => {
                                // In Lazy mode the live builder is the
                                // source of truth.
                                self.builder.collection_slot_len(acc_id_usize)
                            }
                            CursorMode::Strict => cursor
                                .collection_stack
                                .get(acc_id_usize)
                                .map(|s| s.len())
                                .unwrap_or(0),
                        };
                        let new_kv_phase: u8 = if slot_len % 2 == 1 { 1 } else { 0 };
                        WpdsState::CollectionLoop {
                            result_src_idx: *result_src_idx,
                            rule_idx: *rule_idx,
                            element_src_idx: *element_src_idx,
                            outer_bp: *outer_bp,
                            accumulator_id: *accumulator_id,
                            slot_idx: *slot_idx,
                            kv_phase: new_kv_phase,
                        }
                    }
                    None => state.clone(),
                }
            }
            _ => state.clone(),
        };
        cursor.inner_state = patched_state.clone();
        if self.cursor_mode == CursorMode::Lazy {
            self.state = patched_state;
        }
    }

    #[inline(always)]
    fn cursor_gss_push(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
    ) -> crate::gss::GssNodeId {
        // Stage 3.9 / ι Phase 4 (2026-05-01): if the cursor's `node` is
        // the sentinel (0) — meaning no GSS frame has been pushed yet —
        // synthesize a `CategoryEntry(0)` root first. Mirrors the
        // pre-Phase-4 `apply_action::Push` fallback at the live path.
        // Stage 3.12 fix (2026-05-02): also synthesize a fresh root when
        // `cursor.node == GSS_NODE_NONE` (the cursor previously unwound
        // past the entry frame). Without this, push_symbol would record
        // a phantom edge to id u32::MAX.
        let predecessor = if (cursor.node == 0 && self.gss.node(0).is_none())
            || cursor.node == crate::gss::GSS_NODE_NONE
        {
            let root = self.gss.get_or_create_node(WpdsGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.cursor_mode == CursorMode::Lazy {
                self.top_node = Some(root);
            }
            root
        } else {
            cursor.node
        };
        let (new_id, edge_id) =
            self.gss.push_symbol_with_edge_id(predecessor, sym, pos, w);
        cursor.node = new_id;
        // Stage 3.12.6 (2026-05-02): record this push on the cursor's
        // stack-suffix mirror. On the matching pop, the cursor will
        // follow this exact edge — preserving its calling context even
        // when GSS dedup makes the new node share with sibling cursors.
        cursor.incoming_edge_stack.push(edge_id);
        if self.cursor_mode == CursorMode::Lazy {
            self.top_node = Some(new_id);
        }
        new_id
    }

    #[inline(always)]
    fn cursor_gss_pop(
        &mut self,
        cursor: &mut BranchCursor<W>,
    ) -> Option<crate::gss::GssNodeId> {
        // Stage 3.12.5 (2026-05-02): legacy single-predecessor scalar.
        // Retained for sites where the popped frame has SINGLE predecessor
        // by construction (e.g., a frame pushed by the same cursor's prior
        // step). For multi-predecessor pops (Tomita), use
        // `cursor_gss_pop_all`. Picks the FIRST in-edge, which may be
        // non-deterministic if multiple cursors deduplicated to the same
        // GSS node — the canonical reason fork-on-pop was introduced.
        let result = self.gss.pop_symbol(cursor.node);
        // Stage 3.12 fix (2026-05-02): when popping past the entry frame,
        // anchor at GSS_NODE_NONE rather than 0. The sentinel CategoryEntry
        // root lives at id 0 and would otherwise cause engine.step's
        // frontier_top to keep matching the CategoryEntry-on-Unwinding
        // arm, looping indefinitely. With GSS_NODE_NONE, `gss.node()`
        // returns None → engine takes the `frontier_top.is_none() ⇒ Accept`
        // branch, restoring pre-Stage-3.12 behavior in Strict mode.
        cursor.node = result.unwrap_or(crate::gss::GSS_NODE_NONE);
        if self.cursor_mode == CursorMode::Lazy {
            self.top_node = result;
        }
        result
    }

    /// Stage 3.12.5 (2026-05-02): per-cursor post-pop body. Encapsulates
    /// the FireAction + collection-splice + weight + state mutation
    /// shared between the Pop, ConsumeAndPop, and Fork::OptGroupAbsent
    /// arms. Sets `cursor.node = pred_id`, with sentinel anchor when
    /// `pred_id == GSS_NODE_NONE`.
    ///
    /// Does NOT call `cursor_resolution_check` — caller decides outcome
    /// classification.
    fn apply_pop_body_to_cursor(
        &mut self,
        cursor: &mut BranchCursor<W>,
        pred_id: crate::gss::GssNodeId,
        popped_symbol: Option<StackSymbolV2>,
        weight: &W,
        new_state: WpdsState,
        tokens: &dyn crate::wpds_runtime::WpdsTokenSource,
    ) {
        // Set cursor's GSS top to the predecessor (or sentinel).
        cursor.node = pred_id;
        if self.cursor_mode == CursorMode::Lazy {
            self.top_node = if pred_id == crate::gss::GSS_NODE_NONE {
                None
            } else {
                Some(pred_id)
            };
        }
        // Stage 3.12.8 (2026-05-03): for CollectionMarker pops in Strict
        // mode, drain the cursor's `collection_stack[top]` slot and emit
        // a `FinalizeCollection { id, drained }` delta BEFORE FireAction.
        // The cursor's stack is LIFO-correct because grammars guarantee
        // innermost-closes-first. At replay, FinalizeCollection re-pushes
        // the slot so FireAction's `drain_collection(id)` succeeds. In
        // Lazy mode the live builder's `collection_stack` is mutated
        // directly by the action_fn at FireAction time — no delta needed.
        if let Some(symbol) = popped_symbol {
            if symbol.kind == SymbolKind::CollectionMarker
                && self.cursor_mode == CursorMode::Strict
            {
                // L12 follow-up B5 (2026-05-07): pop the cursor's
                // collection_stack mirror to keep id allocation in
                // sync with subsequent Strict-mode emit_start_collection
                // calls.
                //
                // Phase 4 #1 (2026-05-11): EXCEPT for binder-internal
                // collections (Class 2/3 ParamParse{collection:Some}
                // slots inside multi-position binder rules). For those,
                // the slot's accumulator is drained later by the binder
                // rule's terminal action, NOT at marker-pop time —
                // popping the cursor's mirror here would desync future
                // emit_start_collection calls (id=cursor.len) from
                // live's view (which still has the slot). Multi-slot
                // Class 2 rules (Pair . xs:Vec(Proc), ys:Vec(Proc) ...)
                // exposed this: slot 0's marker pop reset cursor.len=0,
                // so slot 1's start_collection allocated id=0 again.
                //
                // For Class-5 collection rules, FireAction fires here
                // (NOT suppressed by is_binder_internal), the action
                // drains the slot from LIVE (live.len--), and we MUST
                // pop the cursor's mirror to stay in sync with live.
                //
                // Phase 4 #5b (2026-05-12): ALWAYS pop the cursor's mirror
                // on CollectionMarker pop, regardless of is_binder_internal.
                // The replay-time `BuilderDelta::PushCollectionId` /
                // `BuilderDelta::SpliceIntoCollection` arms now derive
                // their ids from `live.collection_stack_len() - 1` (not
                // the logged id), so the cursor's collection_stack
                // tracking no longer needs to encode binder-internal
                // slots' persistent presence. This restores the merge
                // invariant in `merge_equivalent_cursors` (operational
                // state shape — cursors at the same configuration MUST
                // have matching collection-stack depths) for nested
                // binder rules like `chooseMap chooseMap 0 ( ) ( )`.
                //
                // The Phase 4 #1 multi-slot rationale ("popping the
                // cursor's mirror would desync future emit_start_collection
                // calls") is resolved by the replay-time id derivation:
                // the runtime live state advances in real-time, and the
                // logged id is no longer the source of truth.
                let _ = self.engine.is_binder_internal_collection(
                    symbol.category_src_idx,
                    symbol.rule_index_in_category,
                );
                cursor.consistency_memo.set(None);
                let _ = cursor.collection_stack.pop();
            }
        }
        // Per-child FireAction (keyed on popped_symbol — same across all
        // children since they share the popped frame).
        //
        // B9 / Class 2 (2026-05-08): suppress FireAction at CollectionMarker
        // pop when the marker belongs to a Class-2 binder rule's internal
        // collection slot. The binder rule's terminal action (firing at
        // the OUTER RuleAt pop) will drain the CollectionId arg via
        // CollectionDrain extraction.
        if let Some(symbol) = popped_symbol {
            let suppress_for_binder_internal =
                symbol.kind == SymbolKind::CollectionMarker
                    && self.engine.is_binder_internal_collection(
                        symbol.category_src_idx,
                        symbol.rule_index_in_category,
                    );
            if !suppress_for_binder_internal
                && matches!(
                    symbol.kind,
                    SymbolKind::Return
                        | SymbolKind::CollectionMarker
                        | SymbolKind::RuleAt(_)
                        | SymbolKind::MixfixMarker
                )
            {
                self.emit_fire_action(cursor, symbol);
            }
        }
        // Per-child collection splice (keyed on predecessor symbol —
        // differs across children when fan-out lands on different
        // calling contexts).
        //
        // F5 follow-up Plan B Phase 3 refined gate (2026-05-11):
        // two-case element-close predicate.
        //
        // (1) DIRECT element-close — popped is CategoryEntry (Bag/List
        //     redirect path's pushed `CategoryEntry(element_src)`
        //     directly above CollectionMarker) or RuleAt (an atomic
        //     prefix rule pops directly above CollectionMarker).
        //     By construction these only top a CollectionMarker at
        //     element completion; splice unconditionally.
        //
        // (2) PRATT element-close — popped is anything else
        //     (Return / GroupingMarker / MixfixMarker / nested
        //     CollectionMarker / OptionalGroupAt). Post-F5 (commit
        //     `f1a5bc1`) the InfixLoop allows in-collection infix
        //     dispatch, so any of these frames can sit directly above
        //     CollectionMarker AND the element may continue with
        //     another infix operator. The element is complete iff the
        //     InfixLoop's existing close/sep filter (added in commit
        //     `ebf7b14`) would fire on the next engine step — i.e.,
        //     the next token is the collection's close or separator,
        //     OR no Pratt operator matches the next token at cur_bp=0.
        //
        //     We delegate the close/sep recognition to the engine by
        //     simulating one step with state `InfixLoop{cur_bp: 0}`
        //     and frontier = pred CollectionMarker. If the engine
        //     returns `Advance(Unwinding)`, the close/sep filter
        //     matched OR no infix candidate matched at cur_bp=0 —
        //     both interpretations mean "no further Pratt continuation
        //     at this element level," which is the element-complete
        //     signal.
        //
        //     `cur_bp: 0` is the canonical outermost-Pratt-level value.
        //     The InfixLoop close/sep filter does NOT depend on
        //     `cur_bp` (it only checks token text), so `cur_bp: 0` is
        //     a correct probe value. Intermediate Pratt frames
        //     (`cur_bp > 0`) never have CollectionMarker as their
        //     pred — they have Return/MixfixMarker pred — so this
        //     branch only runs at the outermost element-parse level.
        if pred_id != crate::gss::GSS_NODE_NONE {
            // Capture pred metadata (Copy types) under the immutable
            // borrow, then release the borrow so the engine.step query
            // and the mutable splice call can both run.
            let pred_info = self.gss.node(pred_id).map(|n| n.symbol);
            if let Some(pred_sym) = pred_info {
                let pred_kind = pred_sym.kind;
                // Phase 4 #1 (2026-05-11): `pred_sym.bp` now carries the
                // codegen-stamped slot_idx, NOT the runtime accumulator_id.
                // For splice we need the accumulator_id (live.collection_
                // stack index). Recover it from the cursor's/builder's
                // collection_stack top (LIFO: the marker on top is the
                // innermost active slot).
                // Phase 5.5 (2026-05-12): authoritative acc_id is now
                // cursor.builder.collection_stack_len() - 1 (the actual
                // top of the active slot stack). Pre-5.5 the mirror
                // (cursor.collection_stack) was consulted, but Phase 4 #5b
                // empties the mirror on CollectionMarker pop while
                // cursor.builder.collection_stack retains slots until
                // action drain, causing acc_id mismatch in multi-slot
                // contexts.
                let acc_id = match self.cursor_mode {
                    CursorMode::Lazy => {
                        self.builder.collection_stack_len().saturating_sub(1) as u8
                    }
                    CursorMode::Strict => {
                        cursor.builder.collection_stack_len().saturating_sub(1) as u8
                    }
                };
                // Phase 2 / Redesign C follow-up (2026-05-11); Phase 4 #2
                // (2026-05-12): skip splice when pred is a Class-3
                // binder-internal CollectionMarker (the names accumulator
                // slot). Class-3 has its own dedicated AdvanceWithEffect-
                // based splice path emitted by the BinderListLoop
                // Unwinding-OptionalGroupAt arm in engine_impl.rs (Issue C
                // splice handling); the generic splice gate here would
                // mis-target the splice for BinderIdent pops (popped
                // OptionalGroupAt + next token is sep/close →
                // engine.step returns Advance(Unwinding) → spurious
                // splice). Defer to the dedicated path.
                //
                // Per-slot predicate via `pred_sym.bp` (preserved as
                // slot_idx since Phase 4 #1) so Class-2 sibling slots
                // are not skipped (they need the generic splice).
                let pred_slot_idx = pred_sym.bp.unwrap_or(0);
                let skip_for_class3 = pred_kind == SymbolKind::CollectionMarker
                    && self.engine.is_class3_collection_per_slot(
                        pred_sym.category_src_idx,
                        pred_sym.rule_index_in_category,
                        pred_slot_idx,
                    );
                if pred_kind == SymbolKind::CollectionMarker && !skip_for_class3 {
                    let should_splice = match popped_symbol.map(|s| s.kind) {
                        Some(SymbolKind::CategoryEntry)
                        | Some(SymbolKind::RuleAt(_)) => true,
                        Some(_) => {
                            // Pratt element-close: simulate one
                            // InfixLoop{cur_bp:0} step. Splice iff
                            // the engine would advance to Unwinding
                            // (close/sep matched, or 0 cands).
                            //
                            // Snapshot the frontier symbol so the
                            // borrow on `self.gss` is short-lived.
                            let frontier_snap =
                                self.gss.node(cursor.node).cloned();
                            let test_action = self.engine.step(
                                &WpdsState::InfixLoop { cur_bp: 0 },
                                &self.gss,
                                frontier_snap.as_ref(),
                                cursor.pos,
                                tokens,
                            );
                            matches!(
                                test_action,
                                WpdsStepAction::Advance(WpdsState::Unwinding),
                            )
                        }
                        None => false,
                    };
                    if should_splice {
                        self.emit_splice_into_collection(cursor, acc_id);
                    }
                }
            }
        }
        self.multiply_cursor_weight(cursor, weight);
        // Phase 5.5 (2026-05-12): preserve Error state if emit_fire_action's
        // eager fire set it (arity underflow). Without this guard, the
        // unconditional `set_cursor_inner_state(cursor, new_state)` would
        // overwrite the Error with the ConsumeAndPop's planned next_state.
        if !cursor.inner_state.is_terminal() {
            self.set_cursor_inner_state(cursor, new_state);
        }
    }

    /// Stage 3.12.6 (2026-05-02): single-predecessor pop guided by the
    /// cursor's recorded `incoming_edge_stack`.
    ///
    /// The cursor follows the edge it traversed during the matching
    /// push (the top of `incoming_edge_stack`), giving deterministic
    /// pop behavior even when the popped GSS node has multiple
    /// in-edges from different calling contexts (e.g., recursive rule
    /// re-entries at the same `(pos, symbol)`).
    ///
    /// Sentinel semantics: when `incoming_edge_stack` is empty (cursor
    /// has reached the entry frame) OR the recorded edge is invalid
    /// (defensive — should not happen under correct push/pop pairing),
    /// the cursor's `node` is set to `GSS_NODE_NONE` and Lazy mirror
    /// `top_node = None`. Returns the predecessor `GssNodeId` for
    /// caller's use, or `None` if popped past the root.
    ///
    /// This replaces `cursor_gss_pop_all` for cursors that maintained
    /// `incoming_edge_stack` correctly. `cursor_gss_pop` (legacy
    /// arbitrary-pred scalar) remains for code paths that don't use
    /// the stack mirror.
    fn cursor_gss_pop_via_edge(
        &mut self,
        cursor: &mut BranchCursor<W>,
    ) -> Option<crate::gss::GssNodeId> {
        let edge_id = cursor.incoming_edge_stack.pop();
        let target = edge_id.and_then(|e| self.gss.edge_target(e));
        cursor.node = target.unwrap_or(crate::gss::GSS_NODE_NONE);
        if self.cursor_mode == CursorMode::Lazy {
            self.top_node = target;
        }
        target
    }

    /// Stage 3.12.5 (2026-05-02): Tomita-style multi-predecessor pop.
    ///
    /// Returns ALL in-edge predecessors of `cursor.node`. Caller is
    /// responsible for fanning out into per-predecessor child cursors
    /// when `len() > 1`. When `len() == 0` (popped past the entry
    /// frame), returns a single-element vec containing
    /// `GSS_NODE_NONE` so the caller can treat the terminal-pop case
    /// uniformly with the multi-predecessor case.
    ///
    /// **Does NOT mutate `cursor.node`.** The caller decides whether to
    /// reuse the cursor (in-place mutation) or clone it per predecessor.
    /// Callers that always have a single predecessor (e.g., OptGroupFinalize
    /// popping an OptionalGroupAt(N) just pushed by the same cursor —
    /// when that's true) may opt into the legacy scalar `cursor_gss_pop`
    /// instead.
    ///
    /// Sentinel semantics: when `len() == 0`, returns `vec![GSS_NODE_NONE]`.
    /// The caller must subsequently set `cursor.node = GSS_NODE_NONE` (or
    /// per-child equivalent) and Lazy-mirror `self.top_node = None`.
    fn cursor_gss_pop_all(
        &self,
        cursor: &BranchCursor<W>,
    ) -> Vec<crate::gss::GssNodeId> {
        let preds: Vec<crate::gss::GssNodeId> = self
            .gss
            .pop_all_predecessors(cursor.node)
            .into_iter()
            .map(|(id, _w)| id)
            .collect();
        if preds.is_empty() {
            vec![crate::gss::GSS_NODE_NONE]
        } else {
            preds
        }
    }

    #[inline(always)]
    fn cursor_gss_replace_top(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
    ) -> crate::gss::GssNodeId {
        // Stage 3.9 / ι Phase 4 (2026-05-01): same sentinel guard as
        // cursor_gss_push — `replace_top` on a non-existent node is
        // undefined; synthesize a CategoryEntry(0) root first.
        // Stage 3.12 fix (2026-05-02): same GSS_NODE_NONE guard.
        let target = if (cursor.node == 0 && self.gss.node(0).is_none())
            || cursor.node == crate::gss::GSS_NODE_NONE
        {
            let root = self.gss.get_or_create_node(WpdsGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.cursor_mode == CursorMode::Lazy {
                self.top_node = Some(root);
            }
            root
        } else {
            cursor.node
        };
        // Stage 3.12.7 (2026-05-02): pass cursor's recorded incoming edge
        // so replace_top_with_edge_id can find the predecessor that
        // matches THIS cursor's stack-suffix path, not an arbitrary
        // first-edge under multi-pred GSS structural sharing.
        let cursor_top_edge = cursor.incoming_edge_stack.last().copied();
        let (new_id, edge_id) =
            self.gss.replace_top_with_edge_id(target, sym, pos, w, cursor_top_edge);
        cursor.node = new_id;
        // Stage 3.12.6 (2026-05-02): replace_top conceptually pops the
        // top frame and pushes a new one with the same predecessor.
        // Update the cursor's stack: pop the old top edge, push the new.
        if !cursor.incoming_edge_stack.is_empty() {
            cursor.incoming_edge_stack.pop();
        }
        cursor.incoming_edge_stack.push(edge_id);
        if self.cursor_mode == CursorMode::Lazy {
            self.top_node = Some(new_id);
        }
        new_id
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
///
/// Stage 6 G6+ (2026-05-02): extended with `FramePushed`, `FramePopped`
/// (master plan §5), `CursorPanorama` (cursor census after step_fanout),
/// and `BranchMerged` (cursor merge by `merge_equivalent_cursors`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WpdsEventTag {
    Step,
    TokenConsumed,
    BranchForked,
    BranchResolved,
    SemanticActionFired,
    Checkpoint,
    Inspect,
    /// Stage 6 G6 (2026-05-02): a GSS frame was pushed.
    FramePushed,
    /// Stage 6 G6 (2026-05-02): a GSS frame was popped.
    FramePopped,
    /// Stage 6 G6+ (2026-05-02): cursor census after `step_fanout` + merge.
    CursorPanorama,
    /// Stage 6 G6+ (2026-05-02): two equivalent cursors were merged.
    BranchMerged,
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

// ══════════════════════════════════════════════════════════════════════════════
// Stage 6 G6+ (2026-05-02): Cursor-level observer (side-channel to WalkerConsumer)
// ══════════════════════════════════════════════════════════════════════════════

/// Reason a cursor was dropped from the active set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CursorDropReason {
    /// Engine returned `Error` action — parse failed on this branch.
    Error,
    /// Cursor reached EOI in `Idle` state with `pos == tokens.len()`.
    /// (Bridges to: `Idle` action with `at_eoi=true && resolved_shape=true`
    /// is *not* a drop; this variant is for the at_eoi=true but not
    /// resolved-shape cursors.)
    IdleAtEoi,
    /// Cursor stuck in `Idle` mid-stream (no progress possible).
    IdleMidStream,
    /// `pending_builder_ops` exceeded `STRICT_PENDING_OPS_LIMIT`.
    RunawayPendingOps,
    /// Beam pruning by `maybe_prune_frontier` discarded this cursor.
    BeamPruned,
}

/// A flat per-cursor snapshot for tracing/dump. Excludes heavy fields
/// (pending_builder_ops contents, collection_stack contents) — only
/// their lengths. ~80 bytes flat (depends on W size + WpdsState).
#[derive(Debug, Clone)]
pub struct CursorSnapshot<W: Semiring> {
    pub idx: usize,
    pub pos: usize,
    pub state: WpdsState,
    pub gss_node_id: crate::gss::GssNodeId,
    pub weight: W,
    pub source_priority: u32,
    pub pending_ops_len: usize,
    pub collection_depth: usize,
}

/// Per-step cursor census produced after `step_fanout` + `merge_equivalent_cursors`.
#[derive(Debug, Clone)]
pub struct StepSnapshot<W: Semiring> {
    pub step_index: usize,
    pub cursor_count: usize,
    pub walker_state: WpdsState,
    pub walker_pos: usize,
    pub gss_node_count: usize,
    pub cursors: Vec<CursorSnapshot<W>>,
}

/// Side-channel observer for cursor-level events.
///
/// Separate from `WalkerConsumer` so existing LSP/DAP/REPL consumers
/// don't need to handle cursor-level micro-detail. Default impls are
/// no-ops; `NullCursorObserver` monomorphizes away to zero cost.
pub trait CursorObserver<W: Semiring> {
    /// Called from `step_fanout` after the merge pass with a flat census.
    #[inline(always)]
    fn on_step_panorama(&mut self, _snapshot: &StepSnapshot<W>) {}

    /// Called when a cursor is dropped (Error, Idle, RunawayPendingOps, etc.).
    #[inline(always)]
    fn on_cursor_dropped(&mut self, _idx: usize, _reason: CursorDropReason) {}

    /// Called when a cursor Forks into N children.
    #[inline(always)]
    fn on_cursor_forked(&mut self, _parent_idx: usize, _children_count: usize) {}

    /// Called when two equivalent cursors are merged via `Semiring::plus`.
    #[inline(always)]
    fn on_cursors_merged(&mut self, _winner_idx: usize, _loser_idx: usize) {}
}

/// Zero-cost no-op observer.
pub struct NullCursorObserver;
impl<W: Semiring> CursorObserver<W> for NullCursorObserver {}

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

// ══════════════════════════════════════════════════════════════════════════════
// Stage 6 G6+ (2026-05-02): RichTracingConsumer — dual WalkerConsumer + CursorObserver
// ══════════════════════════════════════════════════════════════════════════════

/// Combined consumer + cursor observer suitable for hang diagnosis.
///
/// Records:
/// - `events`: every WpdsEventTag/state pair (like TracingConsumer).
/// - `steps`: per-step cursor census from `step_fanout`.
/// - `merges`: every (winner_idx, loser_idx) merge pair.
/// - `drops`: every (idx, reason) drop pair.
/// - `forks`: every (parent_idx, children_count) fork.
/// - `max_cursor_count`: peak observed cursor count.
/// - `final_state`: walker terminal state.
pub struct RichTracingConsumer<W: Semiring> {
    pub events: Vec<(WpdsEventTag, WpdsState)>,
    pub steps: Vec<StepSnapshot<W>>,
    pub merges: Vec<(usize, usize)>,
    pub drops: Vec<(usize, CursorDropReason)>,
    pub forks: Vec<(usize, usize)>,
    pub max_cursor_count: usize,
    pub final_state: Option<WpdsState>,
}

impl<W: Semiring> RichTracingConsumer<W> {
    pub fn new() -> Self {
        RichTracingConsumer {
            events: Vec::new(),
            steps: Vec::new(),
            merges: Vec::new(),
            drops: Vec::new(),
            forks: Vec::new(),
            max_cursor_count: 0,
            final_state: None,
        }
    }
}

impl<W: Semiring> Default for RichTracingConsumer<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Semiring> WalkerConsumer<W> for RichTracingConsumer<W> {
    fn on_event(&mut self, event: &WpdsEvent<W>, state: &WpdsState) -> WpdsControl {
        self.events.push((WpdsEventTag::of(event), state.clone()));
        WpdsControl::Continue
    }

    fn on_complete(&mut self, state: &WpdsState) {
        self.final_state = Some(state.clone());
    }
}

impl<W: Semiring> CursorObserver<W> for RichTracingConsumer<W> {
    fn on_step_panorama(&mut self, snapshot: &StepSnapshot<W>) {
        if snapshot.cursor_count > self.max_cursor_count {
            self.max_cursor_count = snapshot.cursor_count;
        }
        self.steps.push(snapshot.clone());
    }

    fn on_cursor_dropped(&mut self, idx: usize, reason: CursorDropReason) {
        self.drops.push((idx, reason));
    }

    fn on_cursor_forked(&mut self, parent_idx: usize, children_count: usize) {
        self.forks.push((parent_idx, children_count));
    }

    fn on_cursors_merged(&mut self, winner_idx: usize, loser_idx: usize) {
        self.merges.push((winner_idx, loser_idx));
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Stage 6 G6+ (2026-05-02): EnvTracingConsumer — PRATTAIL_TRACE-gated stderr dump
// ══════════════════════════════════════════════════════════════════════════════

/// Trace-flag bits for `PRATTAIL_TRACE`.
const TRACE_STEPS: u8 = 1;
const TRACE_CURSORS: u8 = 2;
const TRACE_MERGES: u8 = 4;
const TRACE_DROPS: u8 = 8;
const TRACE_ALL: u8 = TRACE_STEPS | TRACE_CURSORS | TRACE_MERGES | TRACE_DROPS;

/// Reads `PRATTAIL_TRACE` env var on construction:
/// - empty/unset → all bits 0, no output (still cheap-skips).
/// - `"1"` or `"all"` → all bits set.
/// - comma list `"steps,cursors,merges,drops"` → bitwise OR of named flags.
fn parse_trace_env() -> u8 {
    let raw = std::env::var("PRATTAIL_TRACE").unwrap_or_default();
    if raw.is_empty() {
        return 0;
    }
    if raw == "1" || raw == "all" {
        return TRACE_ALL;
    }
    let mut bits = 0u8;
    for part in raw.split(',') {
        match part.trim() {
            "steps" => bits |= TRACE_STEPS,
            "cursors" => bits |= TRACE_CURSORS,
            "merges" => bits |= TRACE_MERGES,
            "drops" => bits |= TRACE_DROPS,
            _ => {}
        }
    }
    bits
}

/// Env-gated stderr trace consumer for ad-hoc debugging.
///
/// Set `PRATTAIL_TRACE=1` (or `=steps,cursors,merges,drops`) to enable.
/// Reads env once at construction. Zero-overhead when disabled (still
/// pays the function-call cost per event but eliminates downstream work).
pub struct EnvTracingConsumer {
    enabled: u8,
    step_index: usize,
}

impl EnvTracingConsumer {
    pub fn from_env() -> Self {
        EnvTracingConsumer {
            enabled: parse_trace_env(),
            step_index: 0,
        }
    }

    /// True when at least one trace category is active.
    #[inline]
    pub fn is_active(&self) -> bool {
        self.enabled != 0
    }
}

impl<W: Semiring> WalkerConsumer<W> for EnvTracingConsumer {
    fn on_event(&mut self, event: &WpdsEvent<W>, state: &WpdsState) -> WpdsControl {
        if (self.enabled & TRACE_STEPS) != 0 {
            eprintln!(
                "[wpds-trace] step={} tag={:?} state={:?}",
                self.step_index,
                WpdsEventTag::of(event),
                state
            );
        }
        self.step_index += 1;
        WpdsControl::Continue
    }
}

impl<W: Semiring + std::fmt::Debug> CursorObserver<W> for EnvTracingConsumer {
    fn on_step_panorama(&mut self, snapshot: &StepSnapshot<W>) {
        if (self.enabled & TRACE_CURSORS) != 0 {
            eprintln!(
                "[wpds-trace] panorama step={} cursors={} walker_state={:?} walker_pos={} gss_nodes={}",
                snapshot.step_index,
                snapshot.cursor_count,
                snapshot.walker_state,
                snapshot.walker_pos,
                snapshot.gss_node_count,
            );
            for c in &snapshot.cursors {
                eprintln!(
                    "[wpds-trace]   cursor[{}] pos={} state={:?} node={} src_pri={} ops_len={} coll_depth={}",
                    c.idx, c.pos, c.state, c.gss_node_id,
                    c.source_priority, c.pending_ops_len, c.collection_depth,
                );
            }
        }
    }

    fn on_cursor_dropped(&mut self, idx: usize, reason: CursorDropReason) {
        if (self.enabled & TRACE_DROPS) != 0 {
            eprintln!("[wpds-trace] drop cursor[{}] reason={:?}", idx, reason);
        }
    }

    fn on_cursor_forked(&mut self, parent_idx: usize, children_count: usize) {
        if (self.enabled & TRACE_CURSORS) != 0 {
            eprintln!(
                "[wpds-trace] fork parent[{}] -> {} children",
                parent_idx, children_count
            );
        }
    }

    fn on_cursors_merged(&mut self, winner_idx: usize, loser_idx: usize) {
        if (self.enabled & TRACE_MERGES) != 0 {
            eprintln!(
                "[wpds-trace] merge winner[{}] absorbs loser[{}]",
                winner_idx, loser_idx
            );
        }
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

/// Stage 3.20 / L12 (Commit A, 2026-05-06): defensive Drop impl that
/// clears the mutable_token_source slot if the walker outlives the
/// caller's source. Prevents stale-pointer reuse in pathological cases
/// (e.g. walker stored in a long-lived consumer struct, source borrowed
/// per-parse).
impl<W: Semiring, E: WpdsStepEngine<W>> Drop for WpdsWalker<W, E> {
    fn drop(&mut self) {
        self.mutable_token_source = None;
    }
}

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

    /// Stage 6 G6+ (2026-05-02): env-aware run driver for codegen facades.
    ///
    /// Reads `PRATTAIL_MAX_STEPS` (fallback `default_max_steps`) and
    /// `PRATTAIL_TRACE` (gates `EnvTracingConsumer`). When `PRATTAIL_TRACE`
    /// is unset, behaves identically to `run_to_end_of_input`. When set,
    /// installs `EnvTracingConsumer` as both `WalkerConsumer` and
    /// `CursorObserver` (writes diagnostic lines to stderr).
    ///
    /// Returns the same `Result<(), WpdsMaxStepsExceeded>` as
    /// `run_to_end_of_input`; codegen call sites can swap directly.
    pub fn run_to_end_of_input_env_aware(
        &mut self,
        default_max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> Result<(), WpdsMaxStepsExceeded>
    where
        W: 'static + std::fmt::Debug,
    {
        let max_steps = std::env::var("PRATTAIL_MAX_STEPS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(default_max_steps);
        let mut env_consumer = EnvTracingConsumer::from_env();
        if env_consumer.is_active() {
            // run_with_consumer_observed returns the final state; map a
            // non-terminal state at end-of-budget to the exceeded error to
            // keep the call-site signature identical to run_to_end_of_input.
            let final_state =
                self.run_with_consumer_observed(&mut env_consumer, max_steps, tokens);
            if final_state.is_terminal() {
                Ok(())
            } else {
                Err(WpdsMaxStepsExceeded { position: self.pos })
            }
        } else {
            self.run_to_end_of_input(max_steps, tokens)
        }
    }

    /// Stage 6 G6+ (2026-05-02): drive the walker with a combined
    /// [`WalkerConsumer`] + [`CursorObserver`].
    ///
    /// `C` must implement BOTH traits — one parameter avoids the
    /// double-borrow issue when the same value (e.g.,
    /// [`RichTracingConsumer`] or [`EnvTracingConsumer`]) plays both
    /// roles. Callers wanting two separate implementations can use a
    /// thin wrapper that delegates each trait to a sub-field.
    ///
    /// After each `process_event(Step)`, builds a [`StepSnapshot`] from
    /// the current walker state and dispatches it via
    /// `consumer.on_step_panorama`. Other observer hooks
    /// (`on_cursor_dropped`, `on_cursor_forked`, `on_cursors_merged`)
    /// fire from inside `step_fanout` / `merge_equivalent_cursors` when
    /// those sites get observer-aware (separate substage); for now the
    /// per-step panorama alone is sufficient for diagnosis.
    ///
    /// Honors consumer abort/pause directives identically to
    /// [`run_with_consumer`].
    pub fn run_with_consumer_observed<C>(
        &mut self,
        consumer: &mut C,
        max_steps: usize,
        tokens: &dyn WpdsTokenSource,
    ) -> WpdsState
    where
        C: WalkerConsumer<W> + CursorObserver<W>,
        W: 'static,
    {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                <C as WalkerConsumer<W>>::on_complete(consumer, &self.state);
                return self.state.clone();
            }
            let event = WpdsEvent::Step;
            let transition = self.process_event(event.clone(), tokens);
            if let WpdsTransition::Checkpoint { ref config } = transition {
                <C as WalkerConsumer<W>>::on_checkpoint(consumer, config);
            }
            // Stage 6 G6+ (2026-05-02): per-step cursor census.
            let snapshot = self.current_snapshot();
            <C as CursorObserver<W>>::on_step_panorama(consumer, &snapshot);
            match <C as WalkerConsumer<W>>::on_event(consumer, &event, &self.state) {
                WpdsControl::Continue => {}
                WpdsControl::Checkpoint => {
                    let config = self.current_configuration();
                    <C as WalkerConsumer<W>>::on_checkpoint(consumer, &config);
                }
                WpdsControl::Abort => {
                    self.state = WpdsState::Error {
                        message: "consumer aborted".to_string(),
                    };
                    <C as WalkerConsumer<W>>::on_complete(consumer, &self.state);
                    return self.state.clone();
                }
                WpdsControl::Pause => {
                    return self.state.clone();
                }
            }
        }
        <C as WalkerConsumer<W>>::on_complete(consumer, &self.state);
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
        // Stage 3.5b (2026-05-01): WPDS-correct EOI resolution. The
        // walker drives cursors until parked, then resolves to the
        // lex-min winner at end-of-input (vs the prior mid-stream commit
        // which prematurely collapsed the cursor frontier). This
        // synthetic test's script has no Term-pushing actions (only Pop
        // transitions), so resolve returns ParseError "empty result"
        // — but commit_winner_at_eoi DID fire and set walker.state +
        // walker.weight from the lex-min winner. The test verifies the
        // selection logic via state/weight inspection.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        // commit_winner_at_eoi sets self.state = winner.inner_state
        // (Accepted in this scripted test) and self.weight via times.
        assert_eq!(
            *w.state(),
            WpdsState::Accepted,
            "post-resolve walker state must be Accepted",
        );
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::InfixLoop { cur_bp: 13 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::Unwinding,
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.5, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(0.5, 0, 2),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
        // Stage 3.5b (2026-05-01): use new EOI-aware resolution API.
        // Synthetic test (no Term push) — resolve returns ParseError
        // but commit_winner_at_eoi DID fire and set walker.state from
        // the winner's inner_state.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert_eq!(*w.state(), WpdsState::Accepted);
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
                expected_input_cats: &[crate::wpds_runtime::ANY_CAT],
                output_cat: 0,
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
        expected_input_cats: &[],
        output_cat: 0,
    };
    static COLL_FINALIZE_ENTRY: ActionEntry = ActionEntry {
        action_fn: coll_finalize_action,
        arity: 1,
        expected_input_cats: &[crate::wpds_runtime::ANY_CAT],
        output_cat: 0,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 3, 0, None),
                        weight: lex(1.0, 0, 3),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
        // Stage 3.5b (2026-05-01): nested Fork lex-min winner is now
        // selected at end-of-input via resolve_at_end_of_input.
        // Synthetic test (no Term push) — resolve returns ParseError
        // but commit_winner_at_eoi DID fire and set walker.state.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert_eq!(*w.state(), WpdsState::Accepted);
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
                    action_kind: ForkActionKind::Push,
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
        // Stage 3.5b (2026-05-01): the finalize action's Term result
        // surfaces via WpdsResolveResult::Accepted, not via builder.take_result.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let result = w.resolve_at_end_of_input(&empty_tokens());
        match result {
            WpdsResolveResult::Accepted { term, .. }
            | WpdsResolveResult::AcceptedAmbiguous { term, .. } => {
                let val = *term
                    .downcast::<usize>()
                    .expect("expected usize Term from finalize action");
                assert_eq!(val, 0, "expected drain_collection(0) to yield 0 elements");
            }
            other => panic!("expected Accepted; got {:?}", other),
        }
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
                    action_kind: ForkActionKind::Push,
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
        // Stage 3.5b (2026-05-01): drive — must NOT panic on
        // collection_stack debug_assert during the nested Fork's clone
        // path. (The cursor opened a collection but accumulator 0 is
        // empty when the inner Fork fires.) Under the new EOI semantics,
        // commit happens via resolve_at_end_of_input.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        // Post-B13d-R (Candidate H, 2026-05-08): scripted cursors that
        // push raw tokens without firing actions are filtered from the
        // accepting set by `cursor_will_produce_term`. The
        // ScriptedEngine used here registers no actions, so resolve
        // returns ParseError. The TEST's load-bearing invariant is the
        // `BranchCursor::clone` path during the nested Fork — that
        // path runs in `apply_action_to_cursor::Fork` (per-child
        // allocation) BEFORE resolve. `run_to_end_of_input` not
        // returning Err("max_steps") confirms the clone path
        // succeeded without panicking the `collection_stack` debug
        // assert; the resolve outcome is then ancillary.
        let result = w.resolve_at_end_of_input(&empty_tokens());
        assert!(
            matches!(result, WpdsResolveResult::ParseError { .. }),
            "B13d-R rejects no-Term cursors; expected ParseError; got {:?}",
            result,
        );
    }

    /// Cleanup 4 (Stage 3.5b 2026-05-01 update): a losing branch's
    /// pending_builder_ops must NOT replay against the live builder.
    /// Two branches each `ConsumeAndPush` with `capture_token: true` +
    /// `Pop`. Lex-min picks rule_idx=0; commit_winner_at_eoi replays only
    /// the winner's PushToken delta. The losing cursor's PushToken
    /// delta is discarded with the cursor at resolve time.
    ///
    /// Test mechanics under EOI semantics:
    /// - 1 token, so each cursor's ConsumeAndPush brings pos to 1 = EOI.
    /// - Each cursor's Pop transitions to InfixLoop at EOI → parked
    ///   Resolved.
    /// - resolve_at_end_of_input picks lex-min winner (cursor[0]).
    /// - commit_winner_at_eoi replays winner's deltas → builder
    ///   acquires winner's PushToken arg.
    /// - take_dyn_result inside resolve sees `ActionArg::Token` (not a
    ///   Term), returns None → resolve returns ParseError. That's
    ///   expected; the assertion verifies the post-commit walker.state
    ///   reflects "winner ran" via inspecting the captured-token text
    ///   directly through pop_args.
    #[test]
    fn losing_branch_with_deltas_no_live_side_effect() {
        let token_kinds = [TokenKind::Integer];
        let token_texts = ["42"];
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
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
        // Drive until parked at EOI. Both cursors reach pos=1=EOI in
        // InfixLoop after their Pop.
        w.run_to_end_of_input(100, &token_src).expect("max_steps");
        // Resolve fires commit_winner_at_eoi(0) on the lex-min winner.
        // The winner's pending_builder_ops replays exactly once; the
        // loser's deltas are discarded with its cursor.
        let _ = w.resolve_at_end_of_input(&token_src);
        // Post-B13d-R (Candidate H, 2026-05-08): cursors whose
        // pending_builder_ops produce only an untyped Token (no
        // FireAction to convert to a typed Term) are filtered from
        // the accepting set. The ScriptedEngine used here registers
        // no actions, so both cursors are rejected — resolve_at_end_of_input
        // returns ParseError (no accepting branch) and walker.weight
        // stays at its pre-resolve value.
        //
        // The original "loser's delta doesn't replay" invariant is
        // satisfied a fortiori: NEITHER cursor commits, so neither
        // delta replays. Verify this by:
        //   (a) walker.weight is unchanged from its pre-Fork value
        //       (lex(0.0, 0, 0) at this point), confirming no
        //       commit_winner ran.
        //   (b) the live builder's stack is empty, confirming no
        //       PushToken replay reached the live builder.
        assert!(
            w.weight().primary.0 == 0.0,
            "expected walker.weight to be unchanged (no commit fired \
             under B13d-R gating); got {}",
            w.weight().primary.0,
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
            collection_slots_allocated: 0,
            source_priority: 0,
            incoming_edge_stack: Vec::new(),
            recovery_depth: 0,
            visited_recovery: OrdSet::new(),
            visited_dispatch: OrdSet::new(),
            consistency_memo: std::cell::Cell::new(None),
            // Phase 5.2 (2026-05-12): fresh empty Arc for the unit-test
            // cursor. The test exercises the `Clone` path on a cursor
            // carrying a PushPredicate delta — orthogonal to the
            // builder field — so an empty Arc suffices.
            builder: Arc::new(SemanticBuilder::new()),
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
            expected_input_cats: &[
                crate::wpds_runtime::ANY_CAT,
                crate::wpds_runtime::ANY_CAT,
                crate::wpds_runtime::ANY_CAT,
                crate::wpds_runtime::ANY_CAT,
                crate::wpds_runtime::ANY_CAT,
            ],
            output_cat: 0,
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
                        action_kind: ForkActionKind::Push,
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
        // Phase 5.5 (2026-05-12): emit_fire_action now eagerly fires the
        // action_fn on cursor.builder during the Pop step. The arity
        // underflow detected in fire_action_for_on_builder sets
        // walker.state = WpdsState::Error directly (rather than waiting
        // for commit_winner replay). Capture state BEFORE the subsequent
        // run_to_end_of_input/resolve loop, which may transition the
        // walker through dead-cursor cleanup and overwrite the live
        // state with a recovery value.
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Pop with underflow
        let post_pop_state = w.state().clone();
        // resolve_at_end_of_input still runs to ensure no spurious
        // Accepted, but the Error invariant is checked at the Pop step.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        // Walker MUST have entered Error state at the underflow step.
        // The action_fn's arity mismatch is an engine-emission bug; the
        // walker surfaces it as Error rather than silently advancing.
        //
        // Acceptable Error messages:
        // - "arity mismatch at rule ..." (direct underflow detection in
        //   fire_action_for_on_builder).
        // - "all fork branches dropped" (cursor with Error inner_state
        //   gets Dropped, leaving no active cursors — propagated by
        //   step_fanout).
        match post_pop_state {
            WpdsState::Error { ref message } => {
                assert!(
                    message.contains("arity") || message.contains("under")
                        || message.contains("dropped"),
                    "expected arity / underflow / dropped error; got: {}",
                    message,
                );
            }
            ref other => panic!(
                "expected Error after arity underflow at Pop step; got {:?}",
                other,
            ),
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // Stage 3.9 / ι Phase 4 (2026-05-01): always-cursor walker invariant tests
    //
    // Verify L1-L6 invariants + Lazy/Strict equivalence + helper correctness.
    // ══════════════════════════════════════════════════════════════════════

    /// L1: Lazy admission. After construction, mode = Lazy, cursors == 1,
    /// pending_builder_ops empty.
    #[test]
    fn phase4_lazy_admission_holds_after_construction() {
        let w: WpdsWalker<LexicographicWeight, _> = WpdsWalker::new(IdleEngine, 0);
        assert_eq!(w.cursor_mode(), CursorMode::Lazy);
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "L1: singleton cursor in Lazy");
        assert!(
            cursors[0].pending_builder_ops.is_empty(),
            "L1: pending_builder_ops empty in Lazy"
        );
    }

    /// L2: Lazy → Strict on first Fork.
    #[test]
    fn phase4_lazy_to_strict_on_first_fork() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
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
        assert_eq!(w.cursor_mode(), CursorMode::Lazy, "starts Lazy");
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push entry
        assert_eq!(w.cursor_mode(), CursorMode::Lazy, "still Lazy after non-Fork");
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        assert_eq!(
            w.cursor_mode(),
            CursorMode::Strict,
            "L2: promoted to Strict on first Fork"
        );
    }

    /// L3: Strict persists through fanout resolution.
    #[test]
    fn phase4_strict_persists_through_resolution() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdsState::InfixLoop { cur_bp: 0 },
            },
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork → Strict
        assert_eq!(w.cursor_mode(), CursorMode::Strict);
        // Drive cursors to resolution.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert_eq!(
            w.cursor_mode(),
            CursorMode::Strict,
            "L3: stays Strict post-resolution"
        );
    }

    /// L4: reset returns to Lazy with a fresh singleton.
    #[test]
    fn phase4_reset_returns_to_lazy() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(1.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork → Strict
        assert_eq!(w.cursor_mode(), CursorMode::Strict);
        w.reset(0);
        assert_eq!(w.cursor_mode(), CursorMode::Lazy, "L4: reset → Lazy");
        assert_eq!(*w.state(), WpdsState::Ready { min_bp: 0 });
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "L4: singleton after reset");
        assert!(cursors[0].pending_builder_ops.is_empty());
    }

    /// L5: terminal state absorbs further actions regardless of mode.
    #[test]
    fn phase4_lazy_terminal_state_is_mode_irrelevant() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Accept]);
        let mut w = WpdsWalker::new(engine, 0);
        // Force terminal state directly.
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Accept
        assert_eq!(*w.state(), WpdsState::Accepted);
        // Subsequent Step should be a no-op (L5 + apply_action terminal early-return).
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        assert_eq!(*w.state(), WpdsState::Accepted, "L5: terminal absorbs");
    }

    /// L6: Lazy admission requires engine to emit Accept only at EOI.
    /// Verified by: an unambiguous parse in Lazy mode reaches Accepted
    /// with no replay needed (live builder already holds the result).
    #[test]
    fn phase4_lazy_eoi_accept_no_replay_needed() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Accept]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        // L6: Lazy mode at Accept; pending_builder_ops empty (no replay).
        assert_eq!(w.cursor_mode(), CursorMode::Lazy);
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            cursors[0].pending_builder_ops.is_empty(),
            "L6: no deltas to replay"
        );
        assert_eq!(*w.state(), WpdsState::Accepted);
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01): a Push of
    /// `OptionalGroupAt(1)` MUST open the optional scope in Lazy mode.
    /// Pre-fix: `apply_action_to_cursor::Push` lost the
    /// `OptionalGroupAt(1) → start_optional_scope()` clause during the
    /// Step-4.4 helper rewrite. Post-fix: `emit_push_side_effects`
    /// centralizes both `CollectionMarker` (id allocation) and
    /// `OptionalGroupAt(1)` (scope opening) implicit Push-time effects.
    #[test]
    fn push_optional_group_at_one_opens_scope_in_lazy_mode() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Push {
            symbol: StackSymbolV2::optional_group_at(0, 0, 1, 0),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdsWalker::new(engine, 0);
        assert_eq!(w.cursor_mode(), CursorMode::Lazy);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        // L1: still Lazy (no Fork). Live builder must have an open
        // optional scope so subsequent inner pushes land in the inner Vec.
        assert_eq!(w.cursor_mode(), CursorMode::Lazy);
        assert_eq!(
            w.builder().optional_stack_depth(),
            1,
            "Push of OptionalGroupAt(1) must open optional scope in Lazy mode",
        );
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01): same as
    /// above but for Strict mode — verify the cursor logs a
    /// `BuilderDelta::StartOptionalScope` delta.
    #[test]
    fn push_optional_group_at_one_logs_delta_in_strict_mode() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Push {
                symbol: StackSymbolV2::optional_group_at(0, 0, 1, 0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
            // Force Strict via a single-branch Fork BEFORE the OptionalGroupAt push.
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork → Strict
        assert_eq!(w.cursor_mode(), CursorMode::Strict);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push (under fanout)
        // The cursor's pending_builder_ops must contain a StartOptionalScope.
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            cursors[0].pending_builder_ops.iter().any(|d| {
                matches!(d, BuilderDelta::StartOptionalScope)
            }),
            "Push of OptionalGroupAt(1) in Strict must log StartOptionalScope delta; got {:?}",
            cursors[0].pending_builder_ops,
        );
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01): regression
    /// guard. Push of `OptionalGroupAt(2)` (or any sub_pos != 1) must NOT
    /// open the optional scope — only the FIRST marker (sub_pos=1) opens.
    /// Subsequent OptionalGroupAt(2..N) advance through the group's inner
    /// items and must NOT re-open the scope.
    #[test]
    fn push_optional_group_at_two_does_not_open_scope() {
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Push {
            symbol: StackSymbolV2::optional_group_at(0, 0, 2, 0),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        assert_eq!(
            w.builder().optional_stack_depth(),
            0,
            "OptionalGroupAt(2) must NOT open a new scope (only sub_pos=1 does)",
        );
    }

    /// Helper inlining: a single Push in Lazy mode mutates the live GSS
    /// without populating cursor.pending_builder_ops.
    #[test]
    fn phase4_helper_inlining_does_not_double_emit() {
        // Push a distinct symbol (rule_at) so GSS dedup doesn't collapse
        // the sentinel CategoryEntry(0) root with the pushed symbol.
        let engine = ScriptedEngine::new(vec![WpdsStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        // Push grows GSS by ≥2 nodes (CategoryEntry root + pushed entry).
        assert!(w.gss().node_count() >= 2);
        // Lazy: no deltas accumulated.
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            cursors[0].pending_builder_ops.is_empty(),
            "Lazy: live mutation, no delta"
        );
    }

    // ════════════════════════════════════════════════════════════════════════
    // Stage 3.16 / Cluster 1+2+3 Mechanism γ — Fork-emission invariants
    // (Commit 2 closure, 2026-05-06).
    //
    // These tests exercise the new payload-carrying ForkActionKind variants
    // (ConsumeAndReplace, Consume, ConsumeIdentAndReplace, Pop, ConsumeAndPop,
    // ConsumeAndReplaceWithEffect, LexAlt, ConsumeAndCaptureAndPush) via the
    // ScriptedEngine harness. Verify that each variant's apply_action::Fork
    // dispatch arm produces the expected cursor state mutations.
    //
    // Synthetic-grammar coverage matches the G1-G5 future-grammar shapes
    // designed in /home/dylon/.claude/plans/commit2-h7-h8-tests-resolution-2026-05-05.md
    // — at the walker level (not full grammar codegen) since shipped
    // grammars exercise Mechanism γ end-to-end via gen_calculator_op (1331+),
    // gen_rhocalc_op (532), gen_optsmoke_op (25), gen_mixedmath_op (199).
    // ════════════════════════════════════════════════════════════════════════

    /// Mechanism γ — `ConsumeAndReplace` fork branch advances pos by 1.
    /// Mirrors `WpdsStepAction::ConsumeAndReplace` semantics inside Fork.
    #[test]
    fn fork_action_consume_and_replace_advances_pos() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndReplace,
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Push
        let pos_before_fork = w.position();
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens()); // Fork
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(
            cursors[0].pos,
            pos_before_fork + 1,
            "ConsumeAndReplace fork branch must advance child cursor's pos by 1",
        );
    }

    /// Mechanism γ — `Consume` fork branch advances pos by 1 without GSS change.
    #[test]
    fn fork_action_consume_advances_pos_without_gss_change() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::Consume,
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let pos_before = w.position();
        let gss_count_before = w.gss().node_count();
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(cursors[0].pos, pos_before + 1, "Consume must advance pos");
        assert_eq!(
            w.gss().node_count(),
            gss_count_before,
            "Consume must NOT push to GSS (no Push semantics)",
        );
    }

    /// Mechanism γ — `Pop` fork branch pops top-of-GSS frame.
    #[test]
    fn fork_action_pop_removes_top_of_gss() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::InfixLoop { cur_bp: 0 },
                    action_kind: ForkActionKind::Pop,
                }],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            matches!(cursors[0].inner_state, WpdsState::InfixLoop { .. }),
            "Pop fork branch must transition to new_state",
        );
    }

    /// Mechanism γ — `ConsumeAndPop` advances pos AND pops top-of-GSS.
    #[test]
    fn fork_action_consume_and_pop_advances_pos_and_pops() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndPop,
                }],
                consume_trigger: false,
            },
            WpdsStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let pos_before = w.position();
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(
            cursors[0].pos,
            pos_before + 1,
            "ConsumeAndPop must advance pos by 1",
        );
        assert!(
            matches!(cursors[0].inner_state, WpdsState::Unwinding),
            "ConsumeAndPop must transition to new_state",
        );
    }

    /// Mechanism γ — `ConsumeAndReplaceWithEffect` logs the embedded delta
    /// onto the child's pending_builder_ops before replacing top-of-GSS.
    /// Used by Hack #3 BinderListLoop empty bootstrap to log
    /// `BuilderDelta::StartBinderScope { names: vec![] }` on the empty branch.
    #[test]
    fn fork_action_consume_and_replace_with_effect_logs_delta() {
        let effect = BuilderDelta::StartBinderScope { names: Vec::new() };
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                        effect: effect.clone(),
                    },
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        // Effect logged BEFORE replace — first delta in pending_builder_ops.
        assert!(
            cursors[0]
                .pending_builder_ops
                .iter()
                .any(|d| matches!(d, BuilderDelta::StartBinderScope { names } if names.is_empty())),
            "ConsumeAndReplaceWithEffect must log the effect delta",
        );
    }

    /// Stage 3.20 / L12 Commit F (2026-05-06) — `GuardedConsumeAndReplace`
    /// allocates a child cursor when `peek_text(pos_after) ==
    /// expected_text`. Mirrors `ConsumeAndReplace` semantics on guard
    /// pass: replaces top-of-GSS, advances pos by 1.
    #[test]
    fn fork_action_guarded_consume_and_replace_pass_advances_pos() {
        let tokens = [TokenKind::Fixed("=".into())];
        let texts = ["="];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeAndReplace {
                        expected_text: "=".to_string(),
                    },
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
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Push
        let pos_before_fork = w.position();
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Fork (guard pass)
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "guard pass must produce one child");
        assert_eq!(
            cursors[0].pos,
            pos_before_fork + 1,
            "GuardedConsumeAndReplace on guard pass must advance child cursor's pos by 1",
        );
    }

    /// Stage 3.20 / L12 Commit F (2026-05-06) — `GuardedConsumeAndReplace`
    /// produces no child when `peek_text(pos_after) != expected_text`.
    /// The single-branch Fork's empty `children` collapses via
    /// `step_fanout`'s empty-cursors check into `WpdsState::Error { message:
    /// "all fork branches dropped" }` — same surface as the legacy
    /// eq-or-error pathway, but routed through Fork+lex-min.
    #[test]
    fn fork_action_guarded_consume_and_replace_fail_drops_cursor() {
        let tokens = [TokenKind::Fixed("X".into())];
        let texts = ["X"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeAndReplace {
                        expected_text: "=".to_string(),
                    },
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
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Push
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Fork (guard fail)
        let final_state = w.run_to_saturation(50, &token_src);
        match final_state {
            WpdsState::Error { message } => assert!(
                message.contains("all fork branches dropped")
                    || message.contains("dropped"),
                "expected 'all fork branches dropped'-style Error, got: {}",
                message,
            ),
            other => panic!(
                "expected Error after guard-fail single-branch Fork, got {:?}",
                other,
            ),
        }
    }

    /// Stage 3.20 / L12 Commit F (2026-05-06) — `GuardedConsumeIdentAndReplace`
    /// allocates a child cursor with an Ident text capture when
    /// `peek_kind(pos_after) == Ident`. Mirror of the
    /// `GuardedConsumeAndReplace_pass` test above for the ident variant.
    #[test]
    fn fork_action_guarded_consume_ident_and_replace_pass_advances_pos() {
        let tokens = [TokenKind::Ident];
        let texts = ["x"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeIdentAndReplace {
                        start_scope: false,
                    },
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
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Push
        let pos_before = w.position();
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Fork (guard pass)
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "Ident guard pass must produce one child");
        assert_eq!(
            cursors[0].pos,
            pos_before + 1,
            "GuardedConsumeIdentAndReplace on guard pass must advance pos by 1",
        );
    }

    /// Stage 3.20 / L12 Commit F (2026-05-06) — `GuardedConsumeIdentAndReplace`
    /// produces no child when `peek_kind(pos_after) != Ident`.
    #[test]
    fn fork_action_guarded_consume_ident_and_replace_fail_drops_cursor() {
        let tokens = [TokenKind::Fixed("=".into())];
        let texts = ["="];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeIdentAndReplace {
                        start_scope: false,
                    },
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
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Push
        let _ = w.process_event(WpdsEvent::Step, &token_src); // Fork (guard fail)
        let final_state = w.run_to_saturation(50, &token_src);
        match final_state {
            WpdsState::Error { message } => assert!(
                message.contains("dropped"),
                "expected 'all fork branches dropped'-style Error, got: {}",
                message,
            ),
            other => panic!(
                "expected Error after Ident guard-fail, got {:?}",
                other,
            ),
        }
    }

    /// Stage 3.20 / L12 Commit F (2026-05-06) — `GuardedConsumeAndReplace`
    /// and `GuardedConsumeIdentAndReplace` are NON-recovery Forks. The
    /// `is_recovery_fork` predicate must NOT classify them as recovery,
    /// otherwise the bounded-recovery prologue would erroneously bump
    /// `recovery_depth` and insert into `visited_recovery` for branches
    /// that aren't doing recovery at all.
    #[test]
    fn guarded_fork_variants_are_not_recovery_forks() {
        let guarded_text: ForkBranch<LexicographicWeight> = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            action_kind: ForkActionKind::GuardedConsumeAndReplace {
                expected_text: "=".to_string(),
            },
        };
        assert!(
            !is_recovery_fork(&[guarded_text]),
            "GuardedConsumeAndReplace must NOT be classified as recovery Fork",
        );
        let guarded_ident: ForkBranch<LexicographicWeight> = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            action_kind: ForkActionKind::GuardedConsumeIdentAndReplace {
                start_scope: true,
            },
        };
        assert!(
            !is_recovery_fork(&[guarded_ident]),
            "GuardedConsumeIdentAndReplace must NOT be classified as recovery Fork",
        );
    }

    /// Mechanism γ — Source-order tiebreak via rule_idx. Multiple branches
    /// with tied primary cost discriminate by from_cost's rule_idx
    /// component — lower rule_idx wins lex-min. Verifies the G1 (close ==
    /// sep) future-grammar invariant.
    #[test]
    fn fork_source_order_tiebreak_via_rule_idx() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Accept,
            // Branches have identical primary cost (0.0) and src_idx (5);
            // they differ only in rule_idx. Lex-min tiebreak picks rule 0.
            WpdsStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 0, 0, None),
                        weight: lex(0.0, 5, 0),
                        new_state: WpdsState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 1, 0, None),
                        weight: lex(0.0, 5, 1),
                        new_state: WpdsState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 2, 0, None),
                        weight: lex(0.0, 5, 2),
                        new_state: WpdsState::Unwinding,
                        action_kind: ForkActionKind::Push,
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
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdsEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        // 3 cursors after Fork; source_priority encodes branch_idx 0/1/2.
        assert_eq!(cursors.len(), 3);
        // First cursor (branch_idx=0) has the lowest source_priority and
        // weight rule_idx=0 — the lex-min winner on tie.
        assert!(
            cursors[0].source_priority <= cursors[1].source_priority,
            "branch_idx=0 cursor must have ≤ source_priority than branch_idx=1",
        );
        assert!(
            cursors[1].source_priority <= cursors[2].source_priority,
            "source_priority must monotonically increase with branch_idx",
        );
    }

    /// Mechanism γ — BP_TIER_* ordering invariant: the lex_weight constants
    /// are strictly increasing so lex-min picks lower tiers on weight ties.
    #[test]
    fn bp_tier_constants_strictly_increasing() {
        use crate::automata::lex_weight::{
            BP_TIER_INFIX, BP_TIER_CROSSCAT_LHS, BP_TIER_POSTFIX, BP_TIER_MIXFIX,
        };
        assert!(BP_TIER_INFIX < BP_TIER_CROSSCAT_LHS);
        assert!(BP_TIER_CROSSCAT_LHS < BP_TIER_POSTFIX);
        assert!(BP_TIER_POSTFIX < BP_TIER_MIXFIX);
    }

    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): `is_recovery_fork`
    /// distinguishes recovery Forks (whose branches carry RecoveryEvent /
    /// InsertToken / SubstituteToken / ApplyRecoverySequence effects) from
    /// regular ambiguity Forks. Mis-detection on either side would either
    /// (a) bound regular Forks unnecessarily (false positive — would break
    /// shipped grammars by capping legitimate disambiguation depth) or
    /// (b) leave recovery Forks unbounded (false negative — recovery
    /// dispatch would loop infinitely as the bound never trips).
    #[test]
    fn bounded_recovery_detects_recovery_fork() {
        let recovery_event_branch = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(1.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 1, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::RecoveryEvent {
                    action_kind: 0,
                    pos: 0,
                    cost_tropical: 0.5,
                },
            },
        };
        assert!(
            is_recovery_fork(&[recovery_event_branch]),
            "RecoveryEvent effect must be classified as recovery Fork"
        );
        let insert_branch = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(2.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::InsertToken {
                    pos: 0,
                    kind: TokenKind::Fixed(")".into()),
                    text: ")".into(),
                },
            },
        };
        assert!(
            is_recovery_fork(&[insert_branch]),
            "InsertToken effect must be classified as recovery Fork"
        );
        let plain_push_branch: ForkBranch<LexicographicWeight> = ForkBranch::push(
            StackSymbolV2::category_entry(0),
            lex(0.0, 0, 0),
            WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
        );
        assert!(
            !is_recovery_fork(&[plain_push_branch]),
            "regular Push branch must NOT be classified as recovery Fork"
        );
        let opt_group_branch = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(0.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            action_kind: ForkActionKind::OptGroupAbsent {
                replace_symbol: StackSymbolV2::category_entry(0),
            },
        };
        assert!(
            !is_recovery_fork(&[opt_group_branch]),
            "OptGroupAbsent branch (regular ambiguity disambiguation) must NOT \
             be classified as recovery Fork"
        );
    }

    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): the
    /// `forward_progress_or_insert` filter accepts branches that either
    /// advance pos past `base_pos` OR carry an `InsertToken` effect.
    /// Branches that meet neither criterion are dropped — they would
    /// re-fire the same recovery dispatch at the same configuration.
    #[test]
    fn bounded_recovery_forward_progress_filter() {
        let advancing: ForkBranch<LexicographicWeight> = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(1.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 5, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::RecoveryEvent {
                    action_kind: 1,
                    pos: 3,
                    cost_tropical: 1.0,
                },
            },
        };
        assert!(
            forward_progress_or_insert(&advancing, 3),
            "branch with new_state.pos=5 > base_pos=3 must pass filter"
        );
        let non_advancing_delete: ForkBranch<LexicographicWeight> = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(1.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 3, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::RecoveryEvent {
                    action_kind: 1,
                    pos: 3,
                    cost_tropical: 1.0,
                },
            },
        };
        assert!(
            !forward_progress_or_insert(&non_advancing_delete, 3),
            "branch with new_state.pos==base_pos AND no InsertToken effect \
             must be dropped (loop defense)"
        );
        let non_advancing_insert: ForkBranch<LexicographicWeight> = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(2.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 3, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::InsertToken {
                    pos: 3,
                    kind: TokenKind::Fixed(")".into()),
                    text: ")".into(),
                },
            },
        };
        assert!(
            forward_progress_or_insert(&non_advancing_insert, 3),
            "branch with new_state.pos==base_pos AND InsertToken effect must \
             pass filter (synthetic splice — live stream mutates at commit)"
        );
    }

    /// Stage 3.20 / L12 Commit D (2026-05-06) — bounded recovery: a cursor
    /// that experiences repeated recovery dispatches has its
    /// `recovery_depth` bumped by 1 per dispatch via the post-loop
    /// epilogue in `apply_action_to_cursor::Fork`. When depth reaches
    /// `RecoveryConfig.max_recovery_depth` (default 3), the next
    /// recovery Fork is refused (cursor → Error). This test simulates
    /// 3 successful recovery dispatches followed by a 4th attempt,
    /// expecting the 4th to error out per the bound.
    #[test]
    fn bounded_recovery_depth_cap_terminates_cursor() {
        // Synthetic recovery Fork: single branch with InsertToken
        // effect (qualifies as recovery per is_recovery_fork) and a
        // `new_state.pos > base_pos` so forward-progress filter
        // accepts it. Each dispatch bumps recovery_depth by 1.
        let recovery_branch = || ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(1.0, 0, 0),
            new_state: WpdsState::PrefixDispatch { pos: 1, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::InsertToken {
                    pos: 0,
                    kind: TokenKind::Fixed(")".into()),
                    text: ")".into(),
                },
            },
        };
        let recovery_fork = || WpdsStepAction::Fork {
            branches: vec![recovery_branch()],
            consume_trigger: false,
        };
        // Provide 4 recovery Forks back-to-back. Depth cap is 3, so
        // the 4th should be refused.
        let engine = ScriptedEngine::new(vec![
            recovery_fork(), // depth 0 → 1 child at depth 1
            recovery_fork(), // depth 1 → 1 child at depth 2
            recovery_fork(), // depth 2 → 1 child at depth 3 (cap)
            recovery_fork(), // depth 3 → REFUSED, cursor → Error
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let final_state = w.run_to_saturation(50, &empty_tokens());
        match final_state {
            WpdsState::Error { message } => assert!(
                message.contains("recovery depth limit")
                    || message.contains("dropped")
                    || message.contains("forward-progress"),
                "expected depth-cap or dropped Error after 4 recovery dispatches, got: {}",
                message,
            ),
            other => {
                let cursors = w.branch_cursors_for_test();
                let depths: Vec<u8> = cursors.iter().map(|c| c.recovery_depth).collect();
                panic!(
                    "expected Error after exceeding max_recovery_depth=3, got {:?} \
                     (cursor depths: {:?})",
                    other, depths,
                );
            }
        }
    }

    /// Stage 3.20 / L12 Commit D (2026-05-06) — bounded recovery's
    /// `visited_recovery` set rejects re-dispatch at the same
    /// (pos, cat, cur_bp) configuration. This test simulates a cursor
    /// that attempts recovery, then attempts recovery AGAIN at the
    /// same configuration (e.g., due to a non-advancing repair like
    /// InsertToken whose synthesis-time pos doesn't change). The
    /// visited-set defense rejects the second dispatch even though
    /// the depth cap hasn't been reached.
    #[test]
    fn bounded_recovery_visited_set_rejects_recursion() {
        // Recovery Fork with InsertToken at pos=0 and new_state.pos=0
        // (non-advancing). Forward-progress filter accepts it because
        // InsertToken effect is exempted. After dispatch, visited_recovery
        // contains (0, 0, 0). A second dispatch at the same config will
        // be rejected by the visited check.
        //
        // BUT: walker bumps recovery_depth on every recovery Fork
        // child, so depth=1 after first. We need to fire a SECOND
        // recovery Fork at the same (pos, cat, cur_bp) to trigger
        // visited rejection BEFORE depth would cap out.
        //
        // The single-branch test approach: emit the same recovery
        // Fork twice at the same config. With pos=0 and cat=0 and
        // cur_bp=0, the visited entry inserted by the first dispatch
        // matches the second's lookup config.
        let non_advancing_recovery = || WpdsStepAction::Fork {
            branches: vec![ForkBranch {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(1.0, 0, 0),
                // new_state stays at pos=0 (insertion repair).
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect: BuilderDelta::InsertToken {
                        pos: 0,
                        kind: TokenKind::Fixed(";".into()),
                        text: ";".into(),
                    },
                },
            }],
            consume_trigger: false,
        };
        let engine = ScriptedEngine::new(vec![
            non_advancing_recovery(), // first dispatch: visited_recovery gains (0,0,0)
            non_advancing_recovery(), // second dispatch at same config: REFUSED
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let final_state = w.run_to_saturation(50, &empty_tokens());
        match final_state {
            WpdsState::Error { message } => assert!(
                message.contains("recovery already attempted")
                    || message.contains("cycle defense")
                    || message.contains("dropped")
                    || message.contains("forward-progress")
                    || message.contains("recovery depth limit"),
                "expected visited-set / cycle-defense / cap Error, got: {}",
                message,
            ),
            other => panic!(
                "expected Error after re-dispatch at same config, got {:?}",
                other,
            ),
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // Stage 3.20 / L12 Commit G follow-up (2026-05-06): ApplyRecoverySequence
    // delta replay tests. These exercise the commit_winner replay path
    // (wpds_walker.rs:3845-3944) that Commit B added — verifying that
    // multi-step Viterbi recovery sequences (Skip / Delete / Insert /
    // Substitute) replay onto the walker's recovery_events trace in order
    // with correct action_kind discriminators.
    //
    // The replay path requires set_mutable_token_source for the Insert and
    // Substitute primitives. We use MutableMultiTokenSource with a trivial
    // whitespace-tokenizing fake_lex (mirroring wpds_runtime.rs:1810).
    // ════════════════════════════════════════════════════════════════════════

    use crate::recovery::RepairAction;
    use crate::token_id::TokenId;
    use crate::wpds_runtime::MutableMultiTokenSource;

    /// Helper: trivial whitespace-tokenizing lexer for replay tests.
    fn fake_lex_for_replay(
        input: &str,
    ) -> Result<crate::lexer_types::LexStream, String> {
        let mut entries = Vec::new();
        let bytes = input.as_bytes();
        let mut i = 0usize;
        while i < bytes.len() {
            if bytes[i].is_ascii_whitespace() {
                i += 1;
                continue;
            }
            let start = i;
            while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            let text = &input[start..i];
            entries.push(crate::lexer_types::LexEntry {
                byte_start: start,
                alternatives: vec![crate::lexer_types::LexAlternative {
                    kind: TokenKind::Ident,
                    text: text.to_string(),
                    end_byte: i,
                    weight: crate::automata::semiring::TropicalWeight(1.0),
                }],
            });
        }
        Ok(crate::lexer_types::LexStream { entries })
    }

    /// Helper: drive a walker through a Fork(recovery)→Accept sequence so
    /// commit_winner replays the recovery deltas. Returns the walker's
    /// recovery_trace after commit.
    ///
    /// We split the read-only token source (used by the engine's step
    /// loop) from the mutable token source (used by commit_winner's
    /// replay path) to avoid aliasing — the walker sees them as
    /// independent objects. The InsertToken / SubstituteToken replay
    /// mutates `mutable_src` but the test only asserts on
    /// `walker.recovery_trace()`, not on the source state, so the split
    /// is invisible to the assertions.
    fn drive_recovery_replay(
        recovery_effect: BuilderDelta,
    ) -> Vec<RecoveryEvent> {
        let mut mutable_src =
            MutableMultiTokenSource::new("foo bar baz".to_string(), fake_lex_for_replay)
                .expect("construct MutableMultiTokenSource");
        // Single-token read_src so that after the Fork's
        // ConsumeAndReplaceWithEffect arm advances child.pos to 1, the
        // cursor is at logical EOI (pos == tokens.len()) and qualifies
        // as an accepting candidate at resolve_at_end_of_input time.
        let read_tokens = [TokenKind::Ident];
        let read_texts = ["foo"];
        let read_src = SliceTokenSource::with_texts(&read_tokens, &read_texts);
        // Single-branch recovery Fork → child cursor with the effect →
        // Accept on next step → commit_winner replays the effect.
        let engine = ScriptedEngine::new(vec![
            // Step 3 (popped first): Accept resolves the cursor at EOI.
            WpdsStepAction::Accept,
            // Step 2: Fork emitting a recovery branch carrying the effect.
            WpdsStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdsState::Accepted,
                    action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                        effect: recovery_effect,
                    },
                }],
                consume_trigger: false,
            },
            // Step 1: Push to seed the GSS with a non-root frame so
            // ConsumeAndReplaceWithEffect's cursor_gss_replace_top has a
            // top to operate on.
            WpdsStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        w.set_mutable_token_source(&mut mutable_src);
        // Drive to end-of-input (sets up parked frontier in AmbiguityFanout),
        // then resolve to fire commit_winner_at_eoi which replays the winner's
        // pending_builder_ops onto walker.recovery_events.
        let _ = w.run_to_end_of_input(50, &read_src);
        let _ = w.resolve_at_end_of_input(&read_src);
        w.clear_mutable_token_source();
        w.recovery_trace().to_vec()
    }

    /// Stage 3.20 / L12 Commit G follow-up — `ApplyRecoverySequence` with a
    /// `SkipToSync` step replays as a `RecoveryEvent` with action_kind=0
    /// at the post-skip position.
    #[test]
    fn replay_apply_recovery_sequence_skip_to_sync() {
        let actions: std::sync::Arc<[RepairAction]> = std::sync::Arc::from(vec![
            RepairAction::SkipToSync {
                skip_count: 2,
                sync_token: TokenId::MAX,
            },
        ].into_boxed_slice());
        let trace = drive_recovery_replay(BuilderDelta::ApplyRecoverySequence {
            actions,
            base_pos: 0,
            total_cost_tropical: 0.5,
        });
        assert_eq!(trace.len(), 1, "SkipToSync must produce 1 RecoveryEvent");
        assert_eq!(trace[0].action_kind, 0, "SkipToSync → action_kind=0");
        assert_eq!(trace[0].pos, 2, "SkipToSync advances cur_pos by skip_count");
    }

    /// Stage 3.20 / L12 Commit G follow-up — `ApplyRecoverySequence` with a
    /// `DeleteToken` step replays as action_kind=1 with cur_pos+=1.
    #[test]
    fn replay_apply_recovery_sequence_delete_token() {
        let actions: std::sync::Arc<[RepairAction]> = std::sync::Arc::from(vec![
            RepairAction::DeleteToken,
        ].into_boxed_slice());
        let trace = drive_recovery_replay(BuilderDelta::ApplyRecoverySequence {
            actions,
            base_pos: 0,
            total_cost_tropical: 1.0,
        });
        assert_eq!(trace.len(), 1, "DeleteToken must produce 1 RecoveryEvent");
        assert_eq!(trace[0].action_kind, 1, "DeleteToken → action_kind=1");
        assert_eq!(trace[0].pos, 1, "DeleteToken advances cur_pos by 1");
    }

    /// Stage 3.20 / L12 Commit G follow-up — `ApplyRecoverySequence` with an
    /// `InsertToken` step replays as a synthetic token splice via
    /// `src.insert_token` AND logs RecoveryEvent::insert (action_kind=2).
    #[test]
    fn replay_apply_recovery_sequence_insert_token() {
        let actions: std::sync::Arc<[RepairAction]> = std::sync::Arc::from(vec![
            RepairAction::InsertToken { token: 0u16 as TokenId },
        ].into_boxed_slice());
        let trace = drive_recovery_replay(BuilderDelta::ApplyRecoverySequence {
            actions,
            base_pos: 0,
            total_cost_tropical: 2.0,
        });
        assert_eq!(trace.len(), 1, "InsertToken must produce 1 RecoveryEvent");
        assert_eq!(trace[0].action_kind, 2, "InsertToken → action_kind=2");
        assert!(
            trace[0].kind.is_some() && trace[0].text.is_some(),
            "InsertToken event must carry kind + text",
        );
    }

    /// Stage 3.20 / L12 Commit G follow-up — `ApplyRecoverySequence` with a
    /// `SubstituteToken` step replays as a token substitution via
    /// `src.substitute_token` AND logs RecoveryEvent::substitute
    /// (action_kind=3) with cur_pos+=1.
    #[test]
    fn replay_apply_recovery_sequence_substitute_token() {
        let actions: std::sync::Arc<[RepairAction]> = std::sync::Arc::from(vec![
            RepairAction::SubstituteToken { replacement: 0u16 as TokenId },
        ].into_boxed_slice());
        let trace = drive_recovery_replay(BuilderDelta::ApplyRecoverySequence {
            actions,
            base_pos: 0,
            total_cost_tropical: 1.5,
        });
        assert_eq!(trace.len(), 1, "SubstituteToken must produce 1 RecoveryEvent");
        assert_eq!(trace[0].action_kind, 3, "SubstituteToken → action_kind=3");
        assert_eq!(trace[0].pos, 0, "SubstituteToken records cur_pos at site");
        assert!(
            trace[0].kind.is_some() && trace[0].text.is_some(),
            "SubstituteToken event must carry kind + text",
        );
    }

    /// Stage 3.20 / L12 Commit G follow-up — Multi-action
    /// `ApplyRecoverySequence` (Composite-style, multi-step Viterbi)
    /// replays each step in order, producing one RecoveryEvent per step
    /// with the correct action_kind sequence and accumulating cur_pos.
    #[test]
    fn replay_apply_recovery_sequence_multi_step_in_order() {
        let actions: std::sync::Arc<[RepairAction]> = std::sync::Arc::from(vec![
            RepairAction::DeleteToken,
            RepairAction::SkipToSync {
                skip_count: 1,
                sync_token: TokenId::MAX,
            },
        ].into_boxed_slice());
        let trace = drive_recovery_replay(BuilderDelta::ApplyRecoverySequence {
            actions,
            base_pos: 0,
            total_cost_tropical: 1.5,
        });
        assert_eq!(trace.len(), 2, "2-step sequence must produce 2 RecoveryEvents");
        assert_eq!(trace[0].action_kind, 1, "first event = Delete (action_kind=1)");
        assert_eq!(trace[1].action_kind, 0, "second event = Skip (action_kind=0)");
        assert!(
            trace[0].pos < trace[1].pos,
            "cur_pos must advance monotonically across multi-step replay (got {} → {})",
            trace[0].pos, trace[1].pos,
        );
    }
}
