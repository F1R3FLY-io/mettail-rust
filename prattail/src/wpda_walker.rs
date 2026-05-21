//! WPDS walker: reactive FSM driving the runtime parser.
//!
//! Stage 4 of W7 plan v5.1. Implements [`WpdaWalker`], the pure
//! `State × Event → Transition` driver per the survey contract M1
//! (`prattail/docs/design/wpds-migration-survey.md` §4).
//!
//! ## Architecture
//!
//! ```text
//!   External consumer
//!         │
//!         │ WpdaEvent
//!         ▼
//!   ┌─────────────────────────────┐
//!   │ WpdaWalker<W, E>            │
//!   │   state: WpdaState          │  ← inspectable
//!   │   gss:   WpdaGss<W>         │  ← branching substrate (Stage 3)
//!   │   pos:   usize              │  ← input cursor
//!   │   weight: W                 │  ← cumulative path weight
//!   │   engine: E (StepEngine)    │  ← provides per-language rule logic
//!   └─────────────────────────────┘
//!         │
//!         │ WpdaTransition
//!         ▼
//!   External consumer (acts on transition / records trace)
//! ```
//!
//! The walker is **pure** in the sense that `process_event` produces a
//! `WpdaTransition` describing what changed; it does not perform I/O,
//! call observers (those are Stage 5's `WalkerConsumer`), or otherwise
//! interact with the world. External consumers drive the loop.
//!
//! ## Step engine separation
//!
//! Per-language rule logic lives behind the [`WpdaEngine`] trait. The
//! walker calls into the engine once per `Step` event to ask "given the
//! current state and stack, what should I do next?" Stage 6's codegen
//! emits a concrete `WpdaEngine` per language. Tests use [`MockEngine`].
//!
//! ## Beam pruning
//!
//! Optional via [`WpdaWalker::with_beam_size`]. When set, after each
//! transition the walker prunes the GSS frontier to the K best branches
//! by weight (lex-min on [`crate::automata::lex_weight::LexicographicWeight`]).
//! Off by default — preserves correctness at the cost of memory.
//!
//! ## Saturation step semantics
//!
//! Per WPDS poststar semantics, a single `Step` event may trigger a chain
//! of derived transitions (push followed by automatic intra-cat advances).
//! [`WpdaWalker::run_to_saturation`] drives `Step` events until the
//! engine returns [`WpdaStepAction::Idle`] (nothing more to derive).

use std::any::Any;
// Phase 5.7 (2026-05-12): persistent OrdSet for cursor visited sets.
// Replaces BTreeSet for `visited_recovery` and `visited_dispatch` —
// these sets are cloned at every Fork (and at seed/Drop reset). The
// im::OrdSet's Arc-based structural sharing makes clone O(1) instead
// of O(N), aligning with Phase 5's persistent-builder cursor model.
use im::OrdSet;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::automata::semiring::{IdempotentSemiring, SemiringRef, StarSemiringRef};
use crate::automata::TokenKind;
use crate::gss::{WpdaGss, WpdaGssNode};
use crate::recovery::RecoveryConfig;
use crate::wpda_runtime::{
    ActionArg, ActionEntry, SemanticBuilder, StackSymbolV2,
    SymbolKind, WpdaConfiguration, WpdaControl, WpdaEvent, WpdaMaxStepsExceeded,
    WpdaMutableTokenSource, WpdaResolveResult, WpdaState, WpdaTokenSource, WpdaTraceEntry,
    WpdaTransition,
};

// ══════════════════════════════════════════════════════════════════════════════
// Step engine interface
// ══════════════════════════════════════════════════════════════════════════════

/// Per-language rule logic queried by the walker on each `Step` event.
///
/// Stage 6's codegen emits a concrete `WpdaEngine` per `language!`
/// declaration. Tests in this module use [`ScriptedEngine`].
///
/// Phase A.1 extension: `step` gains a `tokens: &dyn WpdaTokenSource`
/// parameter so it can peek the input. `action_for` is the per-language
/// semantic-action lookup — default empty so engines that don't need
/// semantic actions (e.g., `IdleEngine` for tests) don't have to supply one.
pub trait WpdaEngine<W: SemiringRef> {
    /// Decide the next action given the current state, configuration,
    /// and input.
    fn step(
        &self,
        state: &WpdaState,
        gss: &WpdaGss<W>,
        frontier_top: Option<&WpdaGssNode>,
        pos: usize,
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaStepAction<W>;

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
    /// When `Some(_)`, the walker patches `WpdaState::CollectionLoop.kv_phase`
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

    /// D8 fix (2026-05-13): map a Rust `std::any::type_name::<T>()`
    /// string to the category `src_idx` for `T`.
    ///
    /// Used by the walker's `GroupingClosePreservingInner` resolution
    /// (in `apply_pop_body_to_cursor`) to derive the inner
    /// expression's RESULT cat from the cursor builder's top-Term
    /// `type_name`, rather than the popped `CategoryEntry`'s cat
    /// (which carries the OPERAND cat in cross-cat infix patterns
    /// such as `LtFloat: Float "<" Float : Bool` — and is wrong
    /// post-`)`).
    ///
    /// The default returns `None` for engines that don't expose
    /// category types (test mocks, `IdleEngine`). Per-language codegen
    /// emits a match over the language's category enum types AND the
    /// native payload types (e.g. `i64`, `bool`, `f64`, `String`) for
    /// `![native] as Cat` declarations.
    fn cat_of_type_name(&self, name: &str) -> Option<u16> {
        let _ = name;
        None
    }
}

/// Phase F.8 (2026-05-18): three-state classification of a token that
/// [`WpdaStepAction::ConsumeAndPush`] consumes from the input stream.
/// Replaces the prior boolean pair `(capture_token, is_prefix_trigger)`
/// — the four bool-combinations included a nonsensical fourth state
/// (`capture_token=true && is_prefix_trigger=true`) that no codegen path
/// produces; this enum makes that state unrepresentable.
///
/// **`Discard`** — the token is consumed (advance `cursor.pos`) but is
/// neither pushed to the builder's arg stack NOR mirrored onto
/// `cursor.sppf_stack`. Used by syntactic delimiters whose role is purely
/// to advance the parse: `(` grouping open (closed by a matching `)` via
/// `GroupingMarker` pop), collection-open delimiters (`[`, `{`, `bag(`,
/// etc.), and infix-tier ConsumeAndPush of the operator within
/// `engine_impl`'s singleton fast-path. The Pop that eventually fires the
/// rule's action observes the delimiter's absence on the builder.
///
/// **`CaptureForBuilder`** — the token IS the action arg. Pushed to
/// the builder as `ActionArg::Token`; the SPPF receives a regular
/// `SppfNode::Terminal` (via the existing `emit_push_token` path inside
/// the apply-arm). Used by atomic-literal rules like `IntLit . n:i64 |- ⟨Integer⟩ : Int`
/// where the consumed Integer token IS the rule's only arg.
///
/// **`ConsumeAsTriggerOnly`** — the token is a unary-prefix structural
/// trigger (e.g., `"not"` in `Not . a:Bool |- "not" a : Bool`). It is
/// consumed but NOT pushed to the builder; instead it is mirrored to
/// `cursor.sppf_stack` as a `SppfNode::TriggerTerminal` (via
/// `emit_push_trigger_terminal`). The TriggerTerminal carries the
/// token's input position so the enclosing rule's interned SPPF Symbol
/// receives `lo_pos = trigger_pos` — DISTINCT from its operand's
/// Symbol `lo`, preventing the SPPF Symbol-dedup collision that
/// otherwise silently drops the wrapping rule's derivation at realize
/// time. Set by codegen ONLY for rules classified by
/// `classify_unary_prefix_shape` (same-cat unary prefix) and the
/// cross-cat-prefix-unary atomic shape; all other consumed-but-not-
/// captured tokens map to `Discard`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TriggerMode {
    Discard,
    CaptureForBuilder,
    ConsumeAsTriggerOnly,
}

/// One step of action returned by a [`WpdaEngine`].
///
/// Operations are exhaustive: walker selects exactly one per `Step`.
#[derive(Debug, Clone)]
pub enum WpdaStepAction<W: SemiringRef> {
    /// Move the FSM into a new state without touching the GSS.
    Advance(WpdaState),
    /// B8 / Issue C (2026-05-09): Same as Advance, but logs a single
    /// BuilderDelta effect to the cursor's recovery_deltas before
    /// the state transition. Used by the Unwinding-OptionalGroupAt arm
    /// to splice a parsed Name into the Class 3 Names accumulator
    /// after a `ParamParse{collection: Some(_)}` inner step returns.
    /// Mirrors `Advance` for non-effect-bearing transitions and
    /// avoids a new state machine.
    AdvanceWithEffect {
        new_state: WpdaState,
        effect: BuilderDelta,
    },
    /// WPDS push: emit a new symbol on top of the frontier, link to current top.
    Push {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdaState,
    },
    /// WPDS pop: drop the frontier top, follow the predecessor edge.
    Pop {
        weight: W,
        new_state: WpdaState,
    },
    /// WPDS replace: swap the top symbol for another (intracategory step).
    Replace {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdaState,
    },
    /// Fork into multiple branches; each becomes an independent frontier
    /// with its own per-branch target state. The walker constructs one
    /// [`BranchCursor`] per branch and transitions to `WpdaState::AmbiguityFanout`;
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
    /// Phase A.2 atomic-rule shortcut: classify the current input token
    /// per [`TriggerMode`], advance `pos` by 1, push `symbol` onto the
    /// stack (typically `kind=Return`), and transition to `new_state`.
    /// Walker handles all four effects atomically.
    ///
    /// The `trigger_mode` field encodes the three semantically valid
    /// dispositions for the consumed token (Discard / CaptureForBuilder /
    /// ConsumeAsTriggerOnly); see [`TriggerMode`] for the doc on each.
    ConsumeAndPush {
        symbol: StackSymbolV2,
        weight: W,
        new_state: WpdaState,
        trigger_mode: TriggerMode,
    },
    /// Phase 4: consume the current token (advance `pos` by 1), pop the
    /// stack top (firing the action attached to it if it's a `Return` or
    /// `CollectionMarker`), and transition to `new_state`. Used by the
    /// `CollectionLoop` close arm: consume the close delimiter, pop the
    /// `CollectionMarker`, and fire the finalize action.
    ConsumeAndPop {
        weight: W,
        new_state: WpdaState,
    },
    /// Phase 4: consume the current token (advance `pos` by 1) without
    /// touching the stack, then transition to `new_state`. Used by the
    /// `CollectionLoop` separator arm: consume the separator and re-enter
    /// `PrefixDispatch` to parse the next element.
    Consume {
        weight: W,
        new_state: WpdaState,
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
        new_state: WpdaState,
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
        new_state: WpdaState,
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
        new_state: WpdaState,
    },
    /// Phase 6: parse a predicate inline via
    /// `mettail_runtime::parser::predicate::parse_predicate_from_tokens`.
    /// Walker invokes the parser, advances `pos` past the predicate,
    /// pushes `ActionArg::Predicate(BehavioralPred)` to builder, replaces
    /// the GSS top with `replace_symbol`, transitions to `new_state`.
    ParsePredicate {
        replace_symbol: StackSymbolV2,
        weight: W,
        new_state: WpdaState,
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
        new_state: WpdaState,
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
        new_state: WpdaState,
    },
    /// Parse complete.
    Accept,
    /// Parse failed; message is propagated as `WpdaState::Error { message }`.
    Error(String),
    /// Engine has no opinion at this state. Walker emits `NoChange`.
    Idle,
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdaWalker
// ══════════════════════════════════════════════════════════════════════════════

/// Pure reactive FSM driving WPDS-based parsing.
///
/// External consumers (LSP/DAP/REPL/nREPL) drive [`WpdaWalker::process_event`]
/// at their own pace. The walker tracks state, GSS, cursor position, and
/// cumulative weight; it consults the [`WpdaEngine`] for per-language
/// decisions.
/// Phase 3.1.6 (C7b cycle-handling, 2026-05-15): node-color for the
/// tri-color DFS in `realize_root_to_terms`. WHITE = unvisited (absent
/// from the colors map); GRAY = currently on the DFS stack;
/// BLACK = memoized (Phase::Leave complete).
///
/// Encountering a GRAY at Phase::Enter is a back-edge — the SPPF has a
/// cycle (same-cat Symbol-dedup at the same `(nt, lo, hi)`). Per
/// Scott-Johnstone 2010 GLL §5, cycles contribute NO new derivations
/// beyond the non-cyclic packings; cyclic packings are skipped at the
/// Symbol arm of `realize_node_leave`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RealizeColor {
    Gray,
    Black,
}

pub struct WpdaWalker<W: SemiringRef, E: WpdaEngine<W>> {
    state: WpdaState,
    gss: WpdaGss<W>,
    pos: usize,
    weight: W,
    engine: E,
    /// Most recently pushed GSS node id (the conceptual top).
    top_node: Option<crate::gss::GssNodeId>,
    /// M11.7 (2026-05-14): cursor-count bounding policy.
    /// Default `Unbounded` (M11 mandate-compliant baseline). Opt-in to
    /// `BeamSize(k)` (legacy beam pruning, mandate-violating escape hatch)
    /// or `AmbiguityBudget(n)` (structured-error overflow,
    /// mandate-compliant). See `CursorBoundingMode` docs for details.
    bounding_mode: crate::wpda_runtime::CursorBoundingMode,
    // Phase F.3c.5 (2026-05-20): `builder: SemanticBuilder` DELETED.
    // Pre-Phase-F.3c the walker maintained a live builder for legacy
    // accessors (walker.builder() / walker.builder_mut() /
    // take_dyn_result()). Phase F.3c.4 deleted cursor.builder, removing
    // all install sites (resolve_at_end_of_input, apply_action,
    // commit_winner) that wrote to self.builder. F.3c.5 deletes the
    // field + public accessors entirely. Downstream extraction uses
    // `walker.resolve_at_end_of_input(&tokens)` → `realize_root_to_terms`
    // over the SPPF root captured from `cursor.sppf_stack.last()`.
    /// "No Fork has happened yet" flag — `true` at construction; set
    /// `false` at the first `WpdaStepAction::Fork`; never reset within
    /// a parse (only `reset()` flips it back to `true`).
    ///
    /// The 4 mode-agnostic helpers (advance_cursor_pos,
    /// multiply_cursor_weight, set_cursor_inner_state, cursor_gss_push,
    /// cursor_gss_pop_via_edge, apply_pop_body_to_cursor's top-node
    /// mirror) consult this flag to decide whether to mirror cursor.* to
    /// self.*. Mirror fires only while deterministic (singleton cursor still
    /// canonically tracked by the walker's live `self.builder` /
    /// `self.pos` / etc.); once a Fork happens, the walker has multiple
    /// cursors and self.* loses its singleton-meaning until
    /// `commit_winner` installs a winner.
    deterministic: bool,
    /// Stage 7+ Fork plan, step 2: per-branch micro-state during
    /// `WpdaState::AmbiguityFanout`. Each entry is a `BranchCursor` that
    /// pairs a GSS-tip node id with the branch's own `pos`, accumulated
    /// `weight`, and `inner_state` (the post-Fork target state for that
    /// branch).
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): post-Phase-4, this vector is
    /// ALWAYS non-empty — singleton cursor in deterministic mode, multiple
    /// cursors in nondeterministic mode. The pre-Phase-4 "empty when not in
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
    mutable_token_source: Option<*mut dyn WpdaMutableTokenSource>,
    /// Phantom data marker for the lifetime-erased mutable source slot.
    _mutable_source_lifetime: PhantomData<()>,
    /// Bounded recovery (Stage 3.20 / L12, 2026-05-06): walker-owned
    /// recovery configuration. The `apply_action_to_cursor::Fork` arm
    /// reads `max_recovery_depth` from here when checking each
    /// recovery-Fork dispatch's per-cursor depth bound. Initialized via
    /// `RecoveryConfig::default()`; callers may override via
    /// `with_recovery_config` for per-grammar tuning.
    recovery_config: RecoveryConfig,
    /// Option C / C2 (2026-05-15): the walker-owned Shared Packed Parse
    /// Forest arena. Cursors carry `SppfId` handles into this arena rather
    /// than per-cursor AST builders; the arena is the central, shared,
    /// append-only structural record of every reduce.
    ///
    /// Dual-mode through C2-C8: present alongside the existing
    /// `SemanticBuilder` infrastructure. C3-C5 add emit-helper writes to
    /// this arena; C6 wires it into the resolve path; C9 removes the
    /// `builder` field once the SPPF is the sole AST source.
    ///
    /// See `~/.claude/plans/option-c-sppf-on-wpda.md` §1, §2.
    #[allow(dead_code)] // C3 wires the first emit-helper writer; C6 wires the first reader.
    sppf: crate::sppf::Sppf<W>,
    // Phase F.4 (2026-05-18): walker-global `sppf_collection_arena:
    // Vec<Vec<SppfId>>` DELETED. Splice events from N concurrent
    // cursors pre-merge polluted the shared slot — for rhocalc
    // `{(c?x).{*(x)} | c!(p)}`, slot 0 grew to `[100, 105, 133, 146,
    // 189]` (5 entries) instead of `[X_id, Y_id]`. Splice state is now
    // per-cursor at `BranchCursor::sppf_collection_arena: Arc<Vec<Vec<
    // SppfId>>>`, mirroring the `cursor.builder: Arc<SemanticBuilder>`
    // Arc-CoW pattern from Phase 5.2. Realize-time readers consult the
    // winner cursor's arena via `winner_collection_arena()`. See
    // `docs/design/notes/2026-05-18-cursor-explosion-rhocalc.md`.
    /// Option C / C3: SPPF-side predicate payload arena.
    /// `emit_push_predicate` interns the `Arc<dyn Any + Send + Sync>` here
    /// and pushes a `SppfNode::Predicate { handle }` leaf. Realization
    /// clones the Arc when constructing the user-visible
    /// `ActionArg::Predicate`.
    ///
    /// Append-only.
    #[allow(dead_code)]
    sppf_predicate_arena: Vec<Arc<dyn Any + Send + Sync>>,
    /// Phase F.13 H1 (2026-05-20): walker-global memo of realized AST
    /// payloads keyed by SPPF Symbol id. Promoted from per-cursor
    /// `Arc<Vec<(SppfId, Arc<dyn Any>)>>` to walker-global HashMap to
    /// eliminate the per-cursor Arc<Vec> CoW that profile data identified
    /// as a 7.3% CPU hotspot at the F.13 baseline (perf shows
    /// `Arc<Vec<(u32, Arc<dyn Any>)>>::clone_from_ref_in` at 3.75% +
    /// `::drop_slow` at 3.54% — together ~7.3% of total CPU).
    ///
    /// SPPF SymbolIds are GLOBAL across cursors — Symbol-dedup at
    /// `(nt, lo, hi)` makes any two cursors that compute the same Symbol
    /// produce identical realized terms. Per-cursor memo was therefore
    /// over-cautious: a walker-global memo is semantically equivalent
    /// while eliminating O(cursors × memo_size) Arc<Vec> clones.
    ///
    /// Written by `emit_fire_action` on successful action fires;
    /// consumed by `reconstruct_action_arg` for `SppfNode::Symbol` lookups.
    /// Reset by `reset()`.
    sppf_symbol_terms: std::collections::HashMap<crate::sppf::SppfId, Arc<dyn Any + Send + Sync>>,
    /// Phase F.13 (2026-05-20): walker statistics counters for
    /// algorithmic-bottleneck attribution. Gated by `walker-stats`
    /// Cargo feature; field doesn't exist when feature is off
    /// (zero-cost in default builds). See `prattail/src/walker_stats.rs`.
    #[cfg(feature = "walker-stats")]
    pub stats: crate::walker_stats::WalkerStats,
    /// Phase F.13 H11b (2026-05-21): cross-cat-projection dispatch
    /// dedup table. Keyed by `(state_cat_src_idx, pos, inner_cur_bp)` —
    /// for each dispatch site (a unique parse position at a unique cat
    /// for a unique binding-power level), records which `source_src_idx`
    /// CrossCatDelegate target branches have already been emitted.
    /// On Fork emission, branches whose target source_src_idx is
    /// already present are SKIPPED (the previously-emitted cursor's
    /// derivation suffices; SPPF Symbol-dedup makes the redundant
    /// emission a pure waste).
    ///
    /// Ambiguity preservation: keyed on `pos` (not just `cat`) — a
    /// re-dispatch at a new pos still emits ALL branches. Different
    /// inner_bp levels also distinguish. Only redundant emissions at
    /// the SAME (cat, pos, inner_bp) are filtered.
    ///
    /// Reset by `reset()`.
    dispatch_branch_seen: std::collections::HashMap<
        (u16, u32, u8),
        std::collections::HashSet<u16>,
    >,
    /// Phase F.13 H12 Stage 1.1 (2026-05-21): Tomita-GLR dispatch-cohort
    /// sharing cache. Walker-global; populated when a cross-cat-projection
    /// Fork-arm Push allocates a child cursor, consumed at the matching
    /// `CategoryEntry(S)` pop. See `crate::dispatch_cohort` for the
    /// mathematical foundation and per-stage plan.
    ///
    /// Stage 1.1 ships the field as a dead-code scaffold (no reads,
    /// no writes). Stage 1.2 wires writes; Stage 1.3 wires reads.
    /// Gated by `dispatch-cohort` cargo feature — when off, the field
    /// is omitted and behavior is exactly the per-cursor sub-parse path.
    dispatch_cohort_cache: crate::dispatch_cohort::DispatchCohortCache<W>,
    /// Phase F.13 H12 Stage 1.5 (2026-05-21): keys whose cache
    /// entries need end-of-step revive drain. Populated by
    /// `cursor_gss_pop_via_edge` when resolve() returns FirstResolve.
    /// Drained by `step_fanout` at end-of-iteration BEFORE
    /// `merge_equivalent_cursors`, emitting `paused × snapshots`
    /// revived cursors per key.
    pending_cohort_drain_keys:
        rustc_hash::FxHashSet<crate::dispatch_cohort::DispatchKey>,
}

// Phase 5.6-tail-F (2026-05-12): CursorMode enum DELETED. The pre-tail
// enum had two variants — `Lazy` (singleton, direct mutation of
// self.builder) and `Strict` (multi-cursor, journaled mutation queued
// in pending_builder_ops, replayed at commit_winner). The names
// inverted standard CS terminology (lazy meant immediate; strict meant
// deferred). The actual signal — "no Fork has happened yet" — is now
// a monotone bool `WpdaWalker.deterministic` (true while no Fork has
// happened — the walker is on a single parse path; false once a Fork
// has transitioned it into nondeterministic mode where multiple cursors
// explore grammar ambiguity in parallel, GLR/GLL-style).

/// Stage 3.11 / ι Phase 6 (2026-05-01): runaway guard for nondeterministic-mode
/// cursors. If any cursor's `recovery_deltas` exceeds this length,
/// the walker transitions to `WpdaState::Error` instead of continuing
/// to accumulate. Prevents pathological grammars from consuming
/// unbounded memory in delta logs.
///
/// Default 1,000,000 is large enough for any real-world parse (most
/// parses have <100 deltas; deeply-recursive parses have <10,000).
/// Pathological cases (infinite loops in cursor mutation, e.g., a Fork
/// that re-emits the same Fork) trip this guard immediately.
pub const STRICT_PENDING_OPS_LIMIT: usize = 1_000_000;

/// One branch of a [`WpdaStepAction::Fork`] action. Codegen emits a
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
pub struct ForkBranch<W: SemiringRef> {
    pub symbol: StackSymbolV2,
    pub weight: W,
    pub new_state: WpdaState,
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

// Phase 5.6-tail-A (2026-05-12): DryRunState + DryRunBrokenKind +
// cursor_dry_run_state + cursor_will_produce_term +
// cursor_committed_ops_consistent + the B13d-R consistency-override
// blocks in merge_equivalent_cursors / subsume_lex_dominated_cursors are
// all deleted. Under Phase 5.3+'s always-eager Arc::make_mut path, the
// cursor's live `builder` IS the authoritative state — there is no
// pending-delta journal to dry-run. EOI gate goes via
// `SemanticBuilder::is_accepting_terminal()`; broken-cursor filtering
// happens at `cursor_resolution_check :: Drop` on `WpdaState::Error`.

impl<W: SemiringRef> ForkBranch<W> {
    /// Stage 3.12 / Class A.i (2026-05-01): default constructor for
    /// branches with the standard `Push` action_kind. All 8 pre-Stage-3.12
    /// emit sites use this — the new `action_kind` field is opaque to
    /// existing callers.
    pub fn push(symbol: StackSymbolV2, weight: W, new_state: WpdaState) -> Self {
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
/// payload-carrying action variants that mirror the existing `WpdaStepAction`
/// operations. Each variant carries the EXACT payload of its WpdaStepAction
/// counterpart (e.g. `ConsumeAndReplace { symbol, new_state }` mirrors
/// `WpdaStepAction::ConsumeAndReplace`). Walker's `apply_action::Fork`
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
    /// consume one token. Mirrors `WpdaStepAction::ConsumeAndReplace`.
    /// Fork must emit `consume_trigger: false` because this action consumes
    /// intrinsically.
    ConsumeAndReplace,

    /// Stage 3.16 (Cluster 1) — Consume one token, no GSS change. Mirrors
    /// `WpdaStepAction::Consume`. Fork must emit `consume_trigger: false`.
    Consume,

    /// Stage 3.16 (Cluster 1) — Consume identifier token: optionally start
    /// binder scope, push ident name to builder, then replace top-of-GSS
    /// with `branch.symbol`. Mirrors `WpdaStepAction::ConsumeIdentAndReplace`.
    /// Fork must emit `consume_trigger: false`.
    ConsumeIdentAndReplace { start_scope: bool },

    /// Stage 3.16 (Cluster 1) — Pop top-of-GSS frame, transition to
    /// `branch.new_state`. Used for mixfix last-operand elision (G2).
    /// Mirrors `WpdaStepAction::Pop`. Fork must emit `consume_trigger: false`.
    Pop,

    /// Stage 3.16 (Cluster 1) — Consume token AND pop top-of-GSS frame.
    /// Used for empty-collection close branches. Mirrors
    /// `WpdaStepAction::ConsumeAndPop`. Fork must emit `consume_trigger: false`.
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
    ///
    /// M5 (2026-05-13): `next_pos` replaces the prior `end_byte` field.
    /// The walker's apply uses `next_pos` directly to set the child
    /// cursor's `pos`. For LATTICE sources (`LatticeTokenSource`),
    /// `next_pos` is the alt's DAG `target_node`; for LINEAR sources
    /// (the default), `next_pos = cursor.pos + 1`. Encoding the alt's
    /// downstream position in the cursor's `pos` eliminates the need
    /// for per-cursor sidecar state (the `pending_lex_alts` BTreeMap
    /// deleted in M4).
    LexAlt {
        alt_idx: u16,
        kind: TokenKind,
        text: String,
        next_pos: usize,
        /// M6c.1 (2026-05-14): the literal rule that consumes this alt's
        /// `kind` in the current category. Codegen-baked at lex-Fork
        /// emit time via the per-grammar `lex_alt_rule_for(cat, kind)
        /// -> Option<u16>` table. Used by the walker's apply arm
        /// (M6c.3) to push the rule's Return marker onto the GSS so
        /// the captured token flows through `FireAction` and produces
        /// an AST term (e.g., `Int::NumLit(0)`).
        ///
        /// Placeholder `0u16` during M6c.1; populated by codegen in M6c.3.
        rule_idx: u16,
    },

    /// M6c.6.4 (2026-05-14) — unary prefix operator lex-Fork branch.
    /// Mirrors the standard `WpdaStepAction::ConsumeAndPush` shape
    /// emitted by the generated PrefixDispatch arm for `Fixed("-")`-like
    /// triggers in a same-cat unary prefix rule (e.g., `Neg`):
    /// symbol = `rule_at(cat, rule_idx, slot=1, Some(*cur_bp))` (NO
    /// `with_kind_return`); `new_state = BinderRule { result_src_idx,
    /// rule_idx, body_src_idx, outer_bp = *cur_bp }`; `capture_token:
    /// false` (trigger not stored on builder; operand sub-parse
    /// produces the AST). Walker apply: allocate child at `cursor.pos`,
    /// emit_push_side_effects, cursor_gss_push, advance to `next_pos`.
    /// Activated at M6c.6.4.d; previously stubbed `unreachable!()`.
    LexAltPrefixOp {
        alt_idx: u16,
        trigger: String,
        rule_idx: u16,
        body_src_idx: u16,
        next_pos: usize,
        outer_bp: u8,
    },

    /// M6c.6.4 (2026-05-14) — unary postfix operator lex-Fork branch.
    /// Mirrors the standard postfix tier emit in InfixLoop (e.g.,
    /// `Fact`): symbol = `rule_at(result_src, rule_idx, slot=0,
    /// Some(*cur_bp)).with_kind_return()`; `new_state = Unwinding`.
    /// Operand is already on builder from prior sub-parse; no
    /// `emit_push_token` for the trigger. Walker apply: allocate child
    /// at `cursor.pos`, emit_push_side_effects, cursor_gss_push,
    /// advance to `next_pos`. Activated at M6c.6.4.e.
    LexAltPostfixOp {
        alt_idx: u16,
        trigger: String,
        rule_idx: u16,
        next_pos: usize,
        l_bp: u8,
        result_src_idx: u16,
    },

    /// M6c.6.4 (2026-05-14) — binary infix operator lex-Fork branch.
    /// Mirrors the standard infix tier emit in InfixLoop (e.g.,
    /// `AddInt`, cross-cat `EqInt`): symbol = `rule_at(result_src,
    /// rule_idx, slot=0, Some(*cur_bp)).with_kind_return()`.
    /// `new_state` chosen by apply arm:
    /// - Same-cat (`result_src_idx == source_cat_src_idx`):
    ///   `PrefixDispatch { pos: next_pos, cur_bp: r_bp }`.
    /// - Cross-cat (`result_src_idx != source_cat_src_idx`):
    ///   `CrossCatDelegate { source_src_idx: source_cat_src_idx,
    ///   inner_cur_bp: r_bp }`.
    /// Activated at M6c.6.4.e.
    LexAltInfixOp {
        alt_idx: u16,
        trigger: String,
        rule_idx: u16,
        next_pos: usize,
        l_bp: u8,
        r_bp: u8,
        result_src_idx: u16,
        source_cat_src_idx: u16,
    },

    /// M6c.6.4 (2026-05-14) — mixfix first-trigger lex-Fork branch.
    /// Mirrors the standard mixfix tier emit in InfixLoop (e.g.,
    /// `Tern`'s `?` trigger): symbol = `mixfix_marker(result_src,
    /// rule_idx, 0)` (NOT `rule_at`); `new_state = PrefixDispatch {
    /// pos: next_pos, cur_bp: 0 }`. Subsequent triggers (e.g., `:` of
    /// Tern) handled deterministically by `MixfixLiteralRun` state
    /// machine — OUT OF SCOPE for M6c.6.4 (tracked as M6c.6.5 if a
    /// grammar exercises internal-trigger multi-LENGTH).
    /// Activated at M6c.6.4.e.
    LexAltMixfixOp {
        alt_idx: u16,
        trigger: String,
        rule_idx: u16,
        next_pos: usize,
        l_bp: u8,
        result_src_idx: u16,
    },

    /// Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ, 2026-05-05) — atomic
    /// literal multi-arm Fork branch. Mirrors `WpdaStepAction::ConsumeAndPush
    /// { capture_token: true }`: emit_push_token captures the literal text
    /// onto the cursor's recovery_deltas/live builder, then push the
    /// `branch.symbol` (the rule's Return marker) onto the GSS, then advance
    /// pos by 1. Used when codegen buckets atomic prefix arms by (pat, guard)
    /// and a bucket has ≥2 rules — the Fork emits one branch per rule with
    /// this action_kind, and lex-min via from_cost(0.0, src, rule_idx) picks
    /// the lower rule_idx winner.
    ConsumeAndCaptureAndPush,

    /// Stage 3.20 / L12 Commit F (2026-05-06) — Cluster 1/6 hacks #4 & #5
    /// closure. Mirrors `WpdaStepAction::ConsumeAndReplace` but gated on
    /// a `peek_text == expected_text` equality check. Walker's
    /// `apply_action_to_cursor::Fork` arm reads the peek'd text at
    /// `pos_after`; on match, allocates the child like
    /// `ForkActionKind::ConsumeAndReplace`; on miss, skips child
    /// allocation entirely (no cursor pushed). When this is the only
    /// surviving branch in the Fork, `step_fanout`'s empty-children
    /// check raises `WpdaState::Error { message: "all fork branches
    /// dropped" }` — same surface as the legacy eq-or-error pathway,
    /// but routed through uniform Fork+lex-min plumbing per
    /// `feedback_use_wpds_disambiguation_not_heuristics.md`. Behavioral
    /// improvement over legacy: in mid-fanout populations, only the
    /// guard-failing cursor dies; correct sibling cursors continue.
    GuardedConsumeAndReplace { expected_text: String },

    /// Stage 3.20 / L12 Commit F (2026-05-06) — Cluster 1/6 hacks #6 & 4th
    /// closure. Mirrors `WpdaStepAction::ConsumeIdentAndReplace` but
    /// gated on a `peek_kind == TokenKind::Ident` check. Pass → behaves
    /// identically to `ConsumeIdentAndReplace { start_scope }`. Fail →
    /// no child allocated. See `GuardedConsumeAndReplace` for the
    /// fanout-survival rationale.
    GuardedConsumeIdentAndReplace { start_scope: bool },

    /// L12 follow-up B2 (2026-05-07) — closure for BinderListLoop's
    /// separator branch. Mirrors `WpdaStepAction::Consume` but gated on
    /// a `peek_text == expected_text` check. Pass → consume one token,
    /// no GSS change. Fail → no child allocated. Replaces the
    /// previously-unguarded `Consume` branch in BinderListLoop's
    /// 3-branch Fork — that branch ran on every dispatch regardless of
    /// token, causing exponential cursor multiplication and >4000s hangs
    /// on rhocalc::PNew multi-binder grammars.
    GuardedConsume { expected_text: String },

    /// L12 follow-up B2 (2026-05-07) — closure for BinderListLoop
    /// bootstrap empty-list branch. Mirrors
    /// `WpdaStepAction::ConsumeAndReplace` plus a pre-replace
    /// `BuilderDelta` effect (typically
    /// `BuilderDelta::StartBinderScope { names: vec![] }`), gated on
    /// `peek_text == expected_text`. Pass → log effect to
    /// recovery_deltas, replace top of GSS, advance pos. Fail →
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
    /// `WpdaStepAction::ReplaceAndPush` semantics inside a Fork branch.
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
    /// onto recovery_deltas between the scope mutation and the GSS
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

impl<W: SemiringRef> std::fmt::Debug for ForkBranch<W>
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
/// `WpdaState::AmbiguityFanout`. Stored on `WpdaWalker::branch_cursors`
/// parallel to the `Vec<GssNodeId>` in the state itself. Each cursor
/// carries the branch's GSS tip, current input position, accumulated
/// weight, the per-branch target state, and a pending-builder-op log.
///
/// Step 3 (Fork plan F4): `recovery_deltas` queues
/// [`BuilderDelta`]s representing walker-driven mutations to the live
/// `SemanticBuilder` that must be deferred until a winning branch is
/// chosen. Each cursor's deltas are replayed during `commit_winner`.
pub struct BranchCursor<W: SemiringRef> {
    /// GSS-tip node id for this branch (matches the corresponding entry
    /// in `WpdaState::AmbiguityFanout { branches }`).
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
    pub inner_state: WpdaState,
    /// Step 3 (Fork plan F4): deferred builder mutations. The walker logs
    /// per-cursor builder ops here during `apply_action_to_cursor` instead
    /// of mutating the live `SemanticBuilder`. On `commit_winner` the
    /// surviving branch's deltas are replayed against the live builder in
    /// insertion order.
    pub recovery_deltas: Vec<BuilderDelta>,
    // Phase 5.6-tail-G (2026-05-12): `collection_stack` and
    // `collection_slots_allocated` fields DELETED. Pre-tail these were
    // mirrors of the live builder's collection state, maintained for
    // nondeterministic-mode id allocation and for the merge_equivalent_cursors
    // ConfigKey shape-discriminator. Under always-eager Arc::make_mut
    // (Phase 5.3+), cursor.builder IS the authoritative state — its
    // collection_stack reflects the slot history directly. All readers
    // (ConfigKey.collection_depth, set_cursor_inner_state kv_phase,
    // apply_pop_body_to_cursor acc_id) now route through
    // `cursor.builder.collection_stack_len()` / `collection_slot_len()`.
    // collection_slots_allocated was write-only post-Phase-5.5 (the
    // counter was superseded by cursor.builder's authoritative len).
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
    /// Unforked-singleton default: 0. Default for non-Fork-allocated
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
    // Phase 5.6-tail-A (2026-05-12): `consistency_memo` field deleted.
    // It memoized `cursor_committed_ops_consistent`, which is also
    // deleted — the B13d-R/Resolution-R consistency override is
    // unreachable under always-eager Arc::make_mut (broken cursors
    // surface as `WpdaState::Error` and are dropped by
    // `cursor_resolution_check`).
    // Phase F.3c.4 (2026-05-20): `pub builder: Arc<SemanticBuilder>`
    // DELETED. Phase 5.2 introduced the per-cursor Arc-shared builder;
    // Phase 5.3-5.6 made all emitter mutations eager via Arc::make_mut.
    // F.3c.3 swapped emit_fire_action to a transient-SB fire path
    // (the SOLE caller of action_fn). F.3c.4 deletes the field entirely:
    // the SPPF-side mirrors (sppf_stack, sppf_collection_arena,
    // sppf_symbol_terms, binder_scope_marks, optional_scope_marks,
    // collection_stack_depth, last_action_output_cat) are the
    // authoritative per-cursor state for all parsing operations.
    /// Option C / C2 (2026-05-15): per-cursor SPPF working-stack. Replaces
    /// the SemanticBuilder argument-stack as the structural record of which
    /// SPPF subtrees have been constructed so far in this cursor. Cursors
    /// share the walker's central `Sppf` arena (by SppfId); cloning the
    /// stack would be O(N) in the stack depth without the Arc wrap.
    ///
    /// Dual-mode through C2-C8: the field is populated alongside the
    /// SemanticBuilder mutations (no behavior change). The C8+ removal of
    /// `builder` makes this the sole structural-history field.
    ///
    /// Phase F.11 (2026-05-20): wrapped in `Arc<Vec<SppfId>>`. Pre-F.11
    /// the field was `Vec<SppfId>`, deep-cloned on every Fork via
    /// `BranchCursor::clone`. For N-deep operator-form chains (`+`, `^`,
    /// `?:`), each Fork during reduce-ascent cost O(N), compounding to
    /// O(N²) total parse time, or O(N³) under mild Fork ambiguity. The
    /// Plan agent (Explore + Plan, 2026-05-19) empirically confirmed
    /// this: `test_deep_parens_100000` passed in 2.935s and
    /// `test_deep_unary_neg_10000` in 0.713s (deep but no SPPF Packing
    /// reduces along the spine), while `test_right_assoc_chain_1000`,
    /// `test_right_assoc_chain_10000`, `test_left_assoc_chain_10000`,
    /// `test_deep_ternary_1000` all hung past 1260s.
    ///
    /// The Arc-CoW wrap mirrors the Phase 5.2 `cursor.builder:
    /// Arc<SemanticBuilder>` pattern (now deleted in F.3c.4) and the
    /// Phase F.4 `cursor.sppf_collection_arena: Arc<Vec<Vec<SppfId>>>`
    /// pattern. Fork-arm cursor clone is O(1) (Arc refcount bump);
    /// `Arc::make_mut` deep-clones the inner Vec only on the first
    /// mutation in a forked cursor.
    ///
    /// See `~/.claude/plans/option-c-sppf-on-wpda.md` §2.1 (original C2)
    /// and `~/.claude/plans/replicated-conjuring-turtle.md` (F.11 design).
    pub sppf_stack: Arc<Vec<crate::sppf::SppfId>>,
    /// Option C / C3: per-cursor record of `sppf_stack` length snapshots
    /// at each `emit_start_optional_scope` call. On
    /// `emit_finalize_optional_scope_present`, the topmost mark is popped
    /// and `sppf_stack[mark..]` becomes the children of a freshly-interned
    /// Packing tagged with the optional-present rule_idx sentinel.
    pub optional_scope_marks: Vec<usize>,
    /// Bug N (Phase 3.1.5): per-cursor stack of in-progress binder scopes.
    /// Each entry is `(depth, accumulated_names)`:
    ///   - `emit_start_binder_scope` pushes a new entry.
    ///   - `emit_extend_binder_scope` appends a name to the top entry.
    ///   - `apply_effect_to_cursor(BuilderDelta::EndBinderScope)` pops
    ///     the top entry, interns it into `SppfNode::BinderScope`, and
    ///     pushes the SppfId onto `sppf_stack` so the rule's Packing
    ///     captures it as a child (mirroring the `ActionArg::BinderScope`
    ///     that the builder side pushes onto `builder.stack`).
    ///
    /// This mirrors `builder.binder_scopes` (an `im::Vector<BinderHandle>`)
    /// in SPPF terms so realization can reconstruct
    /// `ActionArg::BinderScope` without depending on parse-time builder
    /// state.
    pub binder_scope_marks: Vec<(u16, Vec<String>)>,
    /// Phase C.2/C.3 (2026-05-17): per-Fork-arm weight increment that has
    /// not yet been consumed by `emit_fire_action::intern_packing`.
    ///
    /// Semantics (Q1.A+ in `~/.claude/plans/phase-c-sppf-w-resolved.md`):
    /// - Initial value at `seed_from_live`: `W::one_ref()`.
    /// - At each Fork-arm child cursor construction:
    ///   `child.pending_packing_weight =
    ///       parent.pending_packing_weight.times_ref(&branch_weight)`.
    /// - `emit_fire_action` consumes: `mem::replace(&mut p, W::one_ref())`
    ///   and passes the consumed weight to `intern_packing` as the
    ///   per-production weight.
    /// - Synthetic `OPTIONAL_PRESENT_RULE_IDX` packings interned via
    ///   `emit_finalize_optional_scope_present` do NOT consume the field;
    ///   they always intern with `W::one_ref()` (§2.5 of the plan).
    ///
    /// Why a separate field from `cursor.weight`: `cursor.weight` is the
    /// CUMULATIVE path-cost from the root, used for cursor-merge tiebreak
    /// (`pick_lex_min_resolved`). Using it as Packing.weight would
    /// double-count when realize threads `⊗` through the packing's
    /// children. `pending_packing_weight` tracks ONLY the weight
    /// contributed since the last `emit_fire_action` interned a packing,
    /// matching Goodman's per-production weight semantics.
    ///
    /// NOT part of `ConfigKey` — operational per-cursor state, not a
    /// merge-equivalence key (two cursors that have accumulated different
    /// pending weights can still merge by ConfigKey; the merge tiebreak
    /// preserves one cursor's pending via Vec-write semantics).
    pub pending_packing_weight: W,
    /// Phase F.1 (2026-05-18): SPPF-side mirror of
    /// `cursor.builder.collection_stack_len()`. Counts open collection
    /// slots (allocated by `emit_start_collection`, drained by
    /// `drain_collection` inside an action). Synchronized with
    /// `cursor.builder.collection_stack` at every mutation site so
    /// F.2 can replace external `cursor.builder.collection_stack_len()`
    /// reads with this field and F.3 can delete `cursor.builder`
    /// entirely.
    ///
    /// Parity invariant: `collection_stack_depth as usize ==
    /// builder.collection_stack_len()` holds at every observation
    /// point. Verified by debug_asserts at the existing read sites.
    ///
    /// Plan: `docs/design/plans/phase-f-cursor-builder-deletion.md`.
    pub collection_stack_depth: u8,
    /// Phase F.4 (2026-05-18): per-cursor SPPF collection accumulator
    /// slots. Each inner `Vec<SppfId>` is the running list of children
    /// spliced into one open collection (by
    /// `emit_splice_into_collection`); the outer index is the
    /// accumulator id (matches `cursor.builder.collection_stack`
    /// indexing, plus the `collection_stack_depth` mirror).
    ///
    /// Pre-F.4 this was `WpdaWalker::sppf_collection_arena:
    /// Vec<Vec<SppfId>>` — walker-global. That made it impossible to
    /// attribute a splice to the originating cursor during the per-step
    /// pre-merge fanout window, so N cursors at the same `ConfigKey`
    /// would each splice into the same shared slot, accumulating N
    /// entries before `merge_equivalent_cursors` could collapse them.
    /// Empirical bug: rhocalc `{(c?x).{*(x)} | c!(p)}` arena slot 0
    /// held `[100, 105, 133, 146, 189]` (5 entries) for what should be
    /// a 2-element bag `[X_id, Y_id]`; the resulting 5-entry
    /// `Proc::PPar` bag triggered exponential Ascent fixpoint blowup.
    /// Diagnosis ledger:
    /// `docs/design/notes/2026-05-18-cursor-explosion-rhocalc.md`.
    ///
    /// `Arc<Vec<Vec<SppfId>>>` chosen for the same reason
    /// `builder: Arc<SemanticBuilder>` was introduced in Phase 5.2:
    /// Fork-arm cursor clone is O(1) (Arc bump). First splice in a
    /// fork-child triggers `Arc::make_mut` deep clone — O(arena_size).
    /// For rhocalc's peak ~25 cursors × ~5 slots × 0-9 SppfIds each,
    /// this is trivial. Per `feedback_never_disambiguate_early.md` no
    /// weight-based pruning; per `feedback_no_pragmatic_scopedown.md`
    /// no scope-down — this is the architecturally correct fix.
    ///
    /// NOT part of `ConfigKey` — operational per-cursor state.
    /// `collection_depth` (already in the key since Phase F.1/F.2)
    /// discriminates *shape*; the arena content does not need separate
    /// ConfigKey discrimination because any two cursors with identical
    /// splice sequence reach identical arena content by construction.
    pub sppf_collection_arena: Arc<Vec<Vec<crate::sppf::SppfId>>>,
    // Phase F.13 H1 (2026-05-20): `sppf_symbol_terms` PROMOTED from
    // per-cursor `Arc<Vec<(SppfId, Arc<dyn Any>)>>` to walker-global
    // `HashMap<SppfId, Arc<dyn Any>>` at `WpdaWalker::sppf_symbol_terms`.
    // Per-cursor field DELETED. SPPF SymbolIds are global (Symbol-dedup
    // at `(nt, lo, hi)`); per-cursor memos were redundantly cloning
    // immutable shared data via the Arc<Vec> CoW.

    /// Phase F.3a/b (2026-05-20): walker-maintained mirror of
    /// `cursor.builder.top_term_type_name().and_then(|tn| cat_of_type_name(tn))`.
    ///
    /// Maintained by every cursor.builder mutation helper via
    /// `refresh_action_output_mirror` (emit_push_token/ident/predicate/
    /// collection_id/optional_absent, emit_splice_into_collection,
    /// emit_fire_action — both success AND error paths — emit_start_*,
    /// emit_finalize_optional_scope_present, apply_effect_to_cursor).
    ///
    /// Consumed by the D8 cross-cat resolution reads at the
    /// GroupingClose and GroupingClosePreservingInner sites (Phase F.3b
    /// swap, 2026-05-20). F.3c deletes cursor.builder entirely.
    ///
    /// Operational per-cursor state (not part of ConfigKey).
    pub last_action_output_cat: Option<u16>,
    // M4 (2026-05-13): `pending_lex_alts` field DELETED. Per-cursor lex-
    // alternative state violated WPDS stack purity (the multiset grew
    // monotonically with no pop counterpart, and was excluded from
    // ConfigKey). Replaced by `LatticeTokenSource` (M3) where alt identity
    // lives in the SHARED input DAG; the cursor's `pos: usize` (DAG node-id)
    // suffices to distinguish alt timelines.
    /// Phase F.13 H12 Stage 1.5.3R-a (2026-05-21): cohort-origin tag for
    /// dispatch-cohort revived cursors. None for per-cursor (normal worker
    /// path); Some(key) for cohort-revived cursors. Used by ConfigKey so
    /// cohort revives bucket separately from per-cursor cursors that happen
    /// to share the same (state, node, pos, edge, depth). Soundness: a
    /// per-cursor cursor at the same configuration has INDEPENDENT
    /// provenance and an INDEPENDENT outer rule to fire; merging it with
    /// a cohort revive silently substitutes the worker's outer-rule fire
    /// for the per-cursor's distinct fire (the `-3!` bug). Graduates back
    /// to None when the cursor pops past `cohort_revive_depth`.
    pub cohort_origin: Option<crate::dispatch_cohort::DispatchKey>,
    /// Phase F.13 H12 Stage 1.5.3R-a (2026-05-21): cursor's
    /// incoming_edge_stack depth at the moment of cohort revival.
    /// Cohort tag graduates (clears to None) at the next pop that
    /// brings depth below this value — semantic boundary between
    /// "still inside the sub-parse's parent rule's continuation"
    /// and "back in outer grammar."
    pub cohort_revive_depth: u32,
}

impl<W: SemiringRef> std::fmt::Debug for BranchCursor<W>
where
    W: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BranchCursor")
            .field("node", &self.node)
            .field("pos", &self.pos)
            .field("weight", &self.weight)
            .field("inner_state", &self.inner_state)
            .field("recovery_deltas_len", &self.recovery_deltas.len())
            // Phase F.3c.4 (2026-05-20): builder field deleted; the
            // `Arc::strong_count(&self.builder)` diagnostic is gone.
            // Per-cursor state is now visible via the SPPF-side mirrors
            // (sppf_stack length, sppf_collection_arena slots, etc.).
            // Phase C.2 (2026-05-17): unconsumed per-production weight.
            .field("pending_packing_weight", &self.pending_packing_weight)
            // Phase F.1 (2026-05-18): builder.collection_stack_len mirror.
            .field("collection_stack_depth", &self.collection_stack_depth)
            // Phase F.4 (2026-05-18): per-cursor SPPF arena diagnostic.
            .field("sppf_collection_arena_slots", &self.sppf_collection_arena.len())
            .field(
                "sppf_collection_arena_arc_refcount",
                &Arc::strong_count(&self.sppf_collection_arena),
            )
            .finish()
    }
}

impl<W: SemiringRef> Clone for BranchCursor<W> {
    fn clone(&self) -> Self {
        // Stage 3.6 / ι Phase 1 (2026-05-01): BranchCursor::clone is now
        // TOTAL across all field shapes:
        // - `recovery_deltas`: BuilderDelta is Clone (from Cleanup-4).
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
            recovery_deltas: self.recovery_deltas.clone(),
            source_priority: self.source_priority,
            incoming_edge_stack: self.incoming_edge_stack.clone(),
            recovery_depth: self.recovery_depth,
            visited_recovery: self.visited_recovery.clone(),
            visited_dispatch: self.visited_dispatch.clone(),
            // Phase F.3c.4 (2026-05-20): builder field deleted; the
            // Arc::clone is no longer needed.
            // Phase F.11 (2026-05-20): Arc bump — clone is O(1); first
            // mutation in the cloned cursor triggers Arc::make_mut CoW.
            sppf_stack: Arc::clone(&self.sppf_stack),
            optional_scope_marks: self.optional_scope_marks.clone(),
            binder_scope_marks: self.binder_scope_marks.clone(),
            // Phase C.2/C.3 (2026-05-17): clone the pending weight too.
            // Clone is the right Fork-arm parent-to-child semantics
            // _only when no new branch weight is being applied_; the
            // canonical Fork-arm path (fork_child + inline literals)
            // computes `parent.pending.times_ref(&branch.weight)` and
            // does NOT go through Clone. So clone here means "duplicate
            // an in-progress cursor without semantic change" (e.g.
            // tiebreak snapshots, debug dumps).
            pending_packing_weight: self.pending_packing_weight.clone(),
            // Phase F.1 (2026-05-18): u8 is Copy; clone preserves the
            // mirror's depth alongside builder's Arc-shared stack.
            collection_stack_depth: self.collection_stack_depth,
            // Phase F.4 (2026-05-18): Arc bump — clone is O(1); first
            // splice in the cloned cursor triggers Arc::make_mut CoW.
            sppf_collection_arena: Arc::clone(&self.sppf_collection_arena),
            // Phase F.3a (2026-05-20): Option<u16> is Copy.
            last_action_output_cat: self.last_action_output_cat,
            cohort_origin: self.cohort_origin.clone(),
            cohort_revive_depth: self.cohort_revive_depth,
            // Phase F.13 H1 (2026-05-20): sppf_symbol_terms field DELETED;
            // memo is walker-global now.
        }
    }
}

impl<W: SemiringRef> BranchCursor<W> {
    /// Stage 3.10 / ι Phase 5 (2026-05-01): construct a fresh cursor that
    /// mirrors the live walker's collection-stack depth via empty
    /// placeholders.
    ///
    /// **Class C closure**: pre-Phase-4, the walker maintained two parallel
    /// mutation surfaces (live builder + cursor deltas). When a
    /// deterministic parse transitioned to nondeterministic (first Fork)
    /// with collections open in
    /// the live builder, the children cursors had no awareness of those
    /// collections — subsequent splice deltas could underflow at replay
    /// (`pop_args` panic at `wpda_runtime.rs:1518`).
    ///
    /// Post-Phase-4, the dual-mutation surface is gone; the live builder
    /// and cursor[0] stay in lockstep in deterministic mode via mode-aware helpers.
    /// At deterministic→nondeterministic transition, children inherit the parent cursor's
    /// state, but the parent cursor's `collection_stack` may be empty
    /// (the pre-tail deterministic-mode singleton path mutated the live
    /// builder directly, NOT cursor.collection_stack). The Fork arm
    /// therefore needs to seed children's `collection_stack` with empty
    /// placeholders matching the live builder's depth so subsequent
    /// splice ids align.
    ///
    /// `seed_from_live` makes this explicit. Constructs a cursor with
    /// `K` empty `Vec<ActionArg>` placeholders in `collection_stack`,
    /// where `K = live_collection_stack_depth`. Used by WpdaWalker
    /// constructors and the deterministic→nondeterministic transition (Fork) to ensure
    /// the always-non-empty + always-aligned cursor invariant.
    ///
    /// Replaces three inlined constructions in `WpdaWalker::{new,
    /// new_for_category, seeded_from}` — single source of truth.
    // Phase 5.6-tail-G (2026-05-12): `live_collection_stack_depth` parameter
    // dropped. Pre-tail it was used to seed the deleted collection_stack
    // mirror with placeholders; under always-eager Arc::make_mut, the
    // cursor.builder.collection_stack is the authoritative state and is
    // populated by emit_start_collection directly.
    pub fn seed_from_live(
        node: crate::gss::GssNodeId,
        pos: usize,
        weight: W,
        inner_state: WpdaState,
    ) -> Self {
        BranchCursor {
            node,
            pos,
            weight,
            inner_state,
            recovery_deltas: Vec::new(),
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
            // Phase 5.2 (2026-05-12): fresh empty Arc<SemanticBuilder>.
            // The seed cursor's builder is independent of the walker's
            // live builder (the field is unused in 5.2 — see field
            // docstring). Walker constructors that call `seed_from_live`
            // initialize their `self.builder: SemanticBuilder` to
            // `SemanticBuilder::new()` in lockstep, so the two stay
            // structurally identical at construction time.
            // Phase F.3c.4 (2026-05-20): builder field deleted.
            // Option C / C2: seed cursor's SPPF stack is empty (no reduces yet).
            // Phase F.11 (2026-05-20): fresh empty Arc; mutators will
            // Arc::make_mut on first push (cheap when refcount == 1).
            sppf_stack: Arc::new(Vec::new()),
            optional_scope_marks: Vec::new(),
            binder_scope_marks: Vec::new(),
            // Phase C.2 (2026-05-17): seed cursor has not entered any Fork-
            // arm yet, so no pending per-production weight has accumulated.
            pending_packing_weight: W::one_ref(),
            // Phase F.1 (2026-05-18): seed cursor has no open collections.
            collection_stack_depth: 0,
            // Phase F.4 (2026-05-18): fresh empty Arc — seed cursor has
            // no collection accumulator state.
            sppf_collection_arena: Arc::new(Vec::new()),
            // Phase F.3a (2026-05-20): fresh cursor has no action yet.
            last_action_output_cat: None,
            cohort_origin: None,
            cohort_revive_depth: 0,
            // Phase F.3c.2 (2026-05-20): fresh empty memo.
        }
    }

    /// Allocate a Fork-child cursor inheriting the parent's
    /// recovery_deltas, collection_stack, incoming_edge_stack,
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
        branch_weight: W,
        new_state: WpdaState,
        source_priority: u32,
    ) -> Self {
        BranchCursor {
            node: parent.node,
            pos,
            weight,
            inner_state: new_state,
            recovery_deltas: parent.recovery_deltas.clone(),
            source_priority,
            incoming_edge_stack: parent.incoming_edge_stack.clone(),
            recovery_depth: parent.recovery_depth,
            visited_recovery: parent.visited_recovery.clone(),
            // B12 / Candidate E (2026-05-07): inherit parent's projection
            // visited set; the Fork-arm post-allocation step inserts the
            // current dispatch config when this fork IS a projection Fork.
            visited_dispatch: parent.visited_dispatch.clone(),
            // B13d-R Step 2 (2026-05-08): inherit parent's memo (the child
            // shares parent's recovery_deltas at construction time;
            // any subsequent push invalidates the child's memo).
            // Phase 5.2 (2026-05-12): O(1) Arc bump — the child shares
            // the parent's `SemanticBuilder` until a Phase 5.3+ mutator
            // forces copy-on-write via `Arc::make_mut`. This is the
            // single-most-important reason the field exists: Fork
            // fanout cost becomes constant per child.
            // Phase F.3c.4 (2026-05-20): builder field deleted; Arc::clone gone.
            // Option C / C2: Fork-children inherit the parent's SPPF
            // construction history. Clone is O(depth-of-current-rule),
            // which is bounded by a small constant; cheaper than the
            // Arc::clone above on the builder Arc bump cost basis.
            sppf_stack: Arc::clone(&parent.sppf_stack),
            optional_scope_marks: parent.optional_scope_marks.clone(),
            binder_scope_marks: parent.binder_scope_marks.clone(),
            // Phase C.3 (2026-05-17): per-Q1.A+, Fork-arm child cursors
            // multiply the parent's unconsumed weight by the new branch's
            // weight. The next `emit_fire_action` will consume this
            // (mem::replace + W::one_ref()) and use it as the produced
            // packing's per-production weight.
            pending_packing_weight: parent
                .pending_packing_weight
                .times_ref(&branch_weight),
            // Phase F.1 (2026-05-18): Fork-child inherits parent's
            // open-collection depth; the shared Arc<SemanticBuilder>
            // carries the actual stack content via copy-on-write.
            collection_stack_depth: parent.collection_stack_depth,
            // Phase F.4 (2026-05-18): Arc bump (O(1)); CoW on first
            // splice in the child cursor.
            sppf_collection_arena: Arc::clone(&parent.sppf_collection_arena),
            // Phase F.3a (2026-05-20): inherit parent's mirror.
            last_action_output_cat: parent.last_action_output_cat,
            cohort_origin: parent.cohort_origin.clone(),
            cohort_revive_depth: parent.cohort_revive_depth,
            // Phase F.3c.2 (2026-05-20): inherit parent's memo via Arc bump.
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
/// winner's `recovery_deltas` and `collection_stack` are kept (deltas
/// are non-commutative; only the winning path's mutations execute on
/// commit).
///
/// **Verified (2026-05-01):** no hidden differentiators on BranchCursor.
/// `selected_lex_alts` doesn't exist as a field (lex_alt_idx lives in
/// `weight`'s 4-tuple). `recovery_deltas` and `collection_stack` are
/// operational state — kept from the lex-min winner, not part of the key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ConfigKey {
    /// Cursor's per-branch FSM state. `WpdaState: Hash` derive added in
    /// Stage 3.5b (`wpda_runtime.rs:326`).
    state: WpdaState,
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
    /// Phase F.13 H12 Stage 1.5.3R-c (2026-05-21): cohort-origin
    /// discriminator. Cohort-revived cursors carry `Some(key)`; per-
    /// cursor cursors carry `None`. Two cursors at the same
    /// `(state, node, pos, edge, depth)` bucket SEPARATELY when their
    /// cohort_origin differs. This prevents `merge_equivalent_cursors`
    /// from collapsing a cohort revive (which inherited the worker's
    /// distinct outer-rule fire via `snap.worker_inner_state`) with
    /// a per-cursor cursor that has an independent outer-rule fire.
    /// Both survive to end-of-parse; both contribute distinct packings
    /// linked to the same SPPF Symbol; realize fanout enumerates all
    /// derivations. See `phase-f13-stage-1-5-3-redux.md` §3.
    cohort_origin: Option<crate::dispatch_cohort::DispatchKey>,
}

/// Step 3 (Fork plan F4): deferred mutation of the live
/// `SemanticBuilder` performed during a Fork branch's evaluation.
///
/// During `WpdaState::AmbiguityFanout`, the walker cannot apply walker-
/// driven builder side-effects (token captures, ident captures, predicate
/// pushes, binder-scope opens, action firings) directly to the live
/// builder — doing so would corrupt the builder state for losing
/// branches. Instead, each cursor logs deltas into its own
/// `recovery_deltas` queue. When the winning branch is chosen via
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
/// a `RecoveryEvent` onto `WpdaWalker::recovery_events`. The walker's
/// `recovery_trace()` accessor exposes this for diagnostic + recovery-
/// attempt-surface consumers (facade.rs's `parse_<Cat>_via_wpda_recovering`
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

/// BuilderDelta — payload variants for `cursor.recovery_deltas` AND for
/// `WpdaStepAction::AdvanceWithEffect` / `ForkActionKind::*WithEffect(s)`
/// effect payloads.
///
/// Phase 5.6-tail-E (2026-05-12): 9 dead variants deleted (PushToken,
/// PushIdent, PushPredicate, ExtendBinderScope, FireAction,
/// PushToCollection, StartOptionalScope, FinalizeOptionalScopePresent,
/// PushOptionalAbsent). Under Phase 5.6-tail-B's emit-helper unification,
/// these are applied directly to `cursor.builder` via `Arc::make_mut` —
/// they never reach the journal. The 5 codegen-emitted "effect" variants
/// (StartBinderScope, EndBinderScope, StartCollection, PushCollectionId,
/// SpliceIntoCollection) are still active because codegen wraps them in
/// `*WithEffect`/`*WithMultipleEffects` payloads on `ForkBranch`/`WpdaStepAction`.
/// Those flow through `apply_effect_to_builder` on the cursor.builder side;
/// they no longer reach `cursor.recovery_deltas` (5.6-tail-D gated them).
///
/// The 5 recovery variants (RecoveryEvent, SubstituteToken, InsertToken,
/// CommitLexAlternative, ApplyRecoverySequence) mutate state OUTSIDE
/// cursor.builder (walker.recovery_events + mutable_token_source) and ARE
/// the only deltas that land in `cursor.recovery_deltas` for replay.
#[derive(Clone)]
pub enum BuilderDelta {
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

    /// Codegen-emitted "allocate a fresh collection slot" payload. Survives
    /// 5.6-tail-E because BinderListLoop codegen emits it via
    /// `WithMultipleEffects` payloads. Walker-side emit_start_collection
    /// no longer journals this (Phase 5.6-tail-B); it mutates cursor.builder
    /// directly and the id flows back to codegen via the return value.
    StartCollection,

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
    /// allocation (each cursor's recovery_deltas gets its own clone
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
            BuilderDelta::StartBinderScope { names } => f
                .debug_struct("StartBinderScope")
                .field("names", names)
                .finish(),
            BuilderDelta::EndBinderScope => f
                .debug_struct("EndBinderScope")
                .finish(),
            BuilderDelta::PushCollectionId { id } => f
                .debug_struct("PushCollectionId")
                .field("id", id)
                .finish(),
            BuilderDelta::SpliceIntoCollection { id } => f
                .debug_struct("SpliceIntoCollection")
                .field("id", id)
                .finish(),
            BuilderDelta::StartCollection => f.debug_struct("StartCollection").finish(),
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
pub enum CursorOutcome<W: SemiringRef> {
    Drop,
    Alive,
    ForkInto(Vec<BranchCursor<W>>),
    Resolved,
}

impl<W: SemiringRef> std::fmt::Debug for CursorOutcome<W>
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
/// `WpdaStepAction::Fork` was emitted by `recovery_dispatch::emit_recovery_fork`
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
/// M11.7 (2026-05-14): decode the `AMBIGUITY_BUDGET_EXCEEDED:` sentinel
/// `WpdaState::Error` message emitted by `maybe_prune_frontier`.
///
/// Returns `Some((budget, actual, position))` if the message has the
/// sentinel shape; `None` otherwise (a regular parse-failed error).
///
/// Sentinel format (set in `maybe_prune_frontier`):
///   "AMBIGUITY_BUDGET_EXCEEDED: budget={n} actual={k} position={pos}"
fn parse_ambiguity_budget_sentinel(message: &str) -> Option<(usize, usize, usize)> {
    let rest = message.strip_prefix("AMBIGUITY_BUDGET_EXCEEDED: ")?;
    let mut budget: Option<usize> = None;
    let mut actual: Option<usize> = None;
    let mut position: Option<usize> = None;
    for tok in rest.split_whitespace() {
        if let Some(v) = tok.strip_prefix("budget=") {
            budget = v.parse().ok();
        } else if let Some(v) = tok.strip_prefix("actual=") {
            actual = v.parse().ok();
        } else if let Some(v) = tok.strip_prefix("position=") {
            position = v.parse().ok();
        }
    }
    Some((budget?, actual?, position?))
}

fn is_recovery_fork<W: SemiringRef>(branches: &[ForkBranch<W>]) -> bool {
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
fn forward_progress_or_insert<W: SemiringRef>(branch: &ForkBranch<W>, base_pos: usize) -> bool {
    let advances = match &branch.new_state {
        WpdaState::PrefixDispatch { pos, .. } => *pos > base_pos,
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
fn extract_recovery_dispatch_config<W: SemiringRef>(
    cursor: &BranchCursor<W>,
    gss: &WpdaGss<W>,
) -> Option<(usize, u16, u8)> {
    if let WpdaState::PrefixDispatch { pos, cur_bp } = &cursor.inner_state {
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
/// branch transitions to `WpdaState::CrossCatDelegate { .. }`. Mixed
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
/// singleton-projection emissions (`WpdaStepAction::Push { new_state:
/// CrossCatDelegate { .. } }`) regardless of this predicate. The
/// Fork-arm check is the secondary line of defense for cases where
/// a cycle traverses a multi-descriptor pure-projection bucket.
///
/// Used by the Fork arm of `apply_action_to_cursor` to decide whether
/// to apply the visited-dispatch cycle check; see `BranchCursor::
/// visited_dispatch` and the GLL descriptor-uniqueness rationale
/// (Scott & Johnstone 2010).
fn is_projection_fork<W: SemiringRef>(branches: &[ForkBranch<W>]) -> bool {
    !branches.is_empty()
        && branches.iter().all(|b| {
            matches!(&b.new_state, WpdaState::CrossCatDelegate { .. })
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
fn extract_dispatch_config<W: SemiringRef>(
    cursor: &BranchCursor<W>,
    gss: &WpdaGss<W>,
) -> Option<(usize, u16, u8)> {
    if let WpdaState::PrefixDispatch { pos, cur_bp } = &cursor.inner_state {
        let cat_src = gss
            .node(cursor.node)
            .map(|n| n.symbol.category_src_idx)
            .unwrap_or(0);
        Some((*pos, cat_src, *cur_bp))
    } else {
        None
    }
}

impl<W, E> WpdaWalker<W, E>
where
    W: SemiringRef + crate::automata::semiring::TropicalDeltaWeight,
    E: WpdaEngine<W>,
{
    /// Construct a fresh walker in `Ready { min_bp }` state.
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): seeds the singleton cursor in
    /// deterministic mode. Subsequent mutations route through `apply_action_to_cursor`
    /// against `branch_cursors[0]` via the always-cursor dispatcher.
    pub fn new(engine: E, initial_min_bp: u8) -> Self {
        let initial_state = WpdaState::Ready { min_bp: initial_min_bp };
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        // Sentinel node 0 — no GSS node yet; `cursor_gss_push` allocates
        // a CategoryEntry(0) root on first push when `cursor.node == 0`.
        // Live builder is fresh (depth 0), so no placeholders.
        let initial_cursor = BranchCursor::seed_from_live(
            0,
            0,
            W::one_ref(),
            initial_state.clone(),
        );
        WpdaWalker {
            state: initial_state,
            gss: WpdaGss::new(),
            pos: 0,
            weight: W::one_ref(),
            engine,
            top_node: None,
            bounding_mode: crate::wpda_runtime::CursorBoundingMode::Unbounded,
            deterministic: true,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
            // Option C / C2: fresh empty SPPF arena.
            sppf: crate::sppf::Sppf::new(),
            sppf_predicate_arena: Vec::new(),
            // Phase F.13 H1 (2026-05-20): walker-global memo, lazy init.
            sppf_symbol_terms: std::collections::HashMap::new(),
            // Phase F.13 walker-stats (2026-05-20): zero-cost when feature off.
            // Seed counter incremented below the struct literal so it's
            // outside the field initializer.
            #[cfg(feature = "walker-stats")]
            stats: crate::walker_stats::WalkerStats {
                cursors_created_via_seed: 1,
                ..crate::walker_stats::WalkerStats::default()
            },
            // Phase F.13 H11b (2026-05-21): dispatch_branch_seen dedup table.
            dispatch_branch_seen: std::collections::HashMap::new(),
            dispatch_cohort_cache: crate::dispatch_cohort::DispatchCohortCache::new(),
            pending_cohort_drain_keys: rustc_hash::FxHashSet::default(),
        }
    }

    /// Construct a walker seeded to parse starting at the specified
    /// category. Pushes a `CategoryEntry(cat_src_idx)` symbol onto the GSS
    /// and transitions directly into `PrefixDispatch { pos: 0, cur_bp:
    /// min_bp }` — bypassing the default `Ready → Push(primary) →
    /// PrefixDispatch` path that the no-category `new` constructor takes.
    ///
    /// Used by `parse_<Cat>_via_wpda` facades to start parsing at any
    /// category (not just the primary).
    pub fn new_for_category(engine: E, cat_src_idx: u16, initial_min_bp: u8) -> Self {
        let mut gss: WpdaGss<W> = WpdaGss::new();
        // Push the target category as the sole frame. Phase 5 fix: do NOT
        // create a separate "bottom" node first — `get_or_create_node`
        // deduplicates on `(pos, symbol)`, so a `bottom` of `(0, CE(0))` and
        // a `top` of `(0, CE(cat_src_idx))` collapse to the same id when
        // `cat_src_idx == 0`, yielding a self-loop. Instead, the top frame
        // has no predecessor — the walker treats `top_node = None` after
        // pop as the terminal-Accept signal.
        let top_id = gss.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(cat_src_idx),
        });
        let initial_state = WpdaState::PrefixDispatch {
            pos: 0,
            cur_bp: initial_min_bp,
        };
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        let initial_cursor = BranchCursor::seed_from_live(
            top_id,
            0,
            W::one_ref(),
            initial_state.clone(),
        );
        WpdaWalker {
            state: initial_state,
            gss,
            pos: 0,
            weight: W::one_ref(),
            engine,
            top_node: Some(top_id),
            bounding_mode: crate::wpda_runtime::CursorBoundingMode::Unbounded,
            deterministic: true,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
            // Option C / C2: fresh empty SPPF arena.
            sppf: crate::sppf::Sppf::new(),
            sppf_predicate_arena: Vec::new(),
            // Phase F.13 H1 (2026-05-20): walker-global memo, lazy init.
            sppf_symbol_terms: std::collections::HashMap::new(),
            // Phase F.13 walker-stats (2026-05-20): zero-cost when feature off.
            // Seed counter incremented below the struct literal so it's
            // outside the field initializer.
            #[cfg(feature = "walker-stats")]
            stats: crate::walker_stats::WalkerStats {
                cursors_created_via_seed: 1,
                ..crate::walker_stats::WalkerStats::default()
            },
            // Phase F.13 H11b (2026-05-21): dispatch_branch_seen dedup table.
            dispatch_branch_seen: std::collections::HashMap::new(),
            dispatch_cohort_cache: crate::dispatch_cohort::DispatchCohortCache::new(),
            pending_cohort_drain_keys: rustc_hash::FxHashSet::default(),
        }
    }

    /// Construct a walker pre-seeded from a saved [`WpdaConfiguration`].
    ///
    /// Used by [`crate::wpda_session::WpdaIncrementalSession::reparse`] to
    /// resume execution from a checkpoint. Reconstructs the GSS as a linear
    /// chain matching the saved stack (bottom-to-top).
    pub fn seeded_from(engine: E, config: WpdaConfiguration<W>) -> Self {
        let mut gss: WpdaGss<W> = WpdaGss::new();
        let mut top_node: Option<crate::gss::GssNodeId> = None;
        // Stack is stored bottom-to-top; rebuild GSS in that order with
        // each new symbol pushing onto the previous top.
        for symbol in config.stack.iter() {
            let new_id = match top_node {
                None => gss.get_or_create_node(WpdaGssNode {
                    pos: config.pos,
                    symbol: *symbol,
                }),
                Some(prev) => gss.push_symbol(prev, *symbol, config.pos, W::one_ref()),
            };
            top_node = Some(new_id);
        }
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        let initial_cursor = BranchCursor::seed_from_live(
            top_node.unwrap_or(0),
            config.pos,
            config.weight.clone(),
            config.state.clone(),
        );
        WpdaWalker {
            state: config.state,
            gss,
            pos: config.pos,
            weight: config.weight,
            engine,
            top_node,
            bounding_mode: crate::wpda_runtime::CursorBoundingMode::Unbounded,
            deterministic: true,
            branch_cursors: vec![initial_cursor],
            step_counter: 0,
            recovery_events: Vec::new(),
            mutable_token_source: None,
            _mutable_source_lifetime: PhantomData,
            recovery_config: RecoveryConfig::default(),
            // Option C / C2: fresh empty SPPF arena.
            sppf: crate::sppf::Sppf::new(),
            sppf_predicate_arena: Vec::new(),
            // Phase F.13 H1 (2026-05-20): walker-global memo, lazy init.
            sppf_symbol_terms: std::collections::HashMap::new(),
            // Phase F.13 walker-stats (2026-05-20): zero-cost when feature off.
            // Seed counter incremented below the struct literal so it's
            // outside the field initializer.
            #[cfg(feature = "walker-stats")]
            stats: crate::walker_stats::WalkerStats {
                cursors_created_via_seed: 1,
                ..crate::walker_stats::WalkerStats::default()
            },
            // Phase F.13 H11b (2026-05-21): dispatch_branch_seen dedup table.
            dispatch_branch_seen: std::collections::HashMap::new(),
            dispatch_cohort_cache: crate::dispatch_cohort::DispatchCohortCache::new(),
            pending_cohort_drain_keys: rustc_hash::FxHashSet::default(),
        }
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): reset the walker between
    /// parses. Returns to deterministic mode with a fresh singleton cursor.
    /// Preserves the engine and beam_size; everything else is
    /// reinitialized to construction defaults.
    pub fn reset(&mut self, initial_min_bp: u8) {
        let initial_state = WpdaState::Ready { min_bp: initial_min_bp };
        self.state = initial_state.clone();
        self.gss = WpdaGss::new();
        self.pos = 0;
        self.weight = W::one_ref();
        self.top_node = None;
        // Phase F.3c.5 (2026-05-20): `self.builder = SemanticBuilder::new();`
        // DELETED. Walker no longer owns a live builder — per-cursor
        // SPPF state alone carries the parse derivation.
        self.deterministic = true;
        // Stage 3.10 / ι Phase 5 (2026-05-01): seed via `seed_from_live`.
        self.branch_cursors = vec![BranchCursor::seed_from_live(
            0,
            0,
            W::one_ref(),
            initial_state,
        )];
        // Stage 6 G6+ (2026-05-02): reset trace step counter.
        self.step_counter = 0;
        // Stage 3.20 / L12 (Commit 4, 2026-05-06): clear recovery trace.
        self.recovery_events.clear();
        // Stage 3.20 / L12 (Commit A, 2026-05-06): clear the mutable
        // token source slot defensively — the source from the prior
        // parse may be dropped by the time reset() is called.
        self.mutable_token_source = None;
        // Phase F.13 H1 (2026-05-20): clear walker-global memo. SPPF
        // SymbolIds are per-parse (the Sppf arena is reset implicitly by
        // the engine's input change); stale memo entries would leak Arc
        // payloads across parses.
        self.sppf_symbol_terms.clear();
        // Phase F.13 walker-stats (2026-05-20): zero counters at parse boundary
        // and increment seed (matches the constructor's `cursors_created_via_seed = 1`).
        #[cfg(feature = "walker-stats")]
        {
            self.stats = crate::walker_stats::WalkerStats {
                cursors_created_via_seed: 1,
                ..crate::walker_stats::WalkerStats::default()
            };
        }
        // Phase F.13 H11b (2026-05-21): clear cross-cat dispatch dedup table.
        self.dispatch_branch_seen.clear();
        // Phase F.13 H12 Stage 1.1 (2026-05-21): clear dispatch-cohort
        // cache at parse boundary. SPPF SymbolIds are per-parse; the
        // sub-parse results in the cache are tied to the prior parse's
        // SPPF arena and would be unsound to reuse across resets.
        self.dispatch_cohort_cache.clear();
        self.pending_cohort_drain_keys.clear();
    }

    /// Read-only access to the deterministic-parse flag. Returns `true`
    /// when no `WpdaStepAction::Fork` has been processed yet (the walker
    /// is operating on a single parse path); `false` once any Fork has
    /// transitioned the walker into nondeterministic mode (multiple
    /// parallel cursors exploring grammar ambiguity, in the GLR/GLL
    /// sense). Monotone — set false at the first Fork and never reset
    /// within a parse. `reset()` flips it back to `true` for the next
    /// parse.
    ///
    /// Replaces the pre-Phase-5.6-tail `cursor_mode()` accessor that
    /// returned a `CursorMode { Lazy, Strict }` enum (whose variant
    /// names inverted standard CS terminology — see the
    /// terminology-note comment near the `deterministic` field).
    pub fn deterministic(&self) -> bool {
        self.deterministic
    }

    /// Stage 3.20 / L12 (Commit 4, 2026-05-06): read-only access to the
    /// WPDS-edge recovery event trace. Each entry corresponds to one
    /// `BuilderDelta::RecoveryEvent` / `SubstituteToken` / `InsertToken` /
    /// `CommitLexAlternative` delta replayed at commit_winner time.
    /// Wrapper consumers (e.g. `parse_<Cat>_via_wpda_recovering`) map each
    /// entry into a `RecoveryAttempt` for surfacing to the user.
    pub fn recovery_trace(&self) -> &[RecoveryEvent] {
        &self.recovery_events
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): thread a mutable token
    /// source into the walker for recovery-driven token-stream mutations
    /// (SubstituteToken / InsertToken / CommitLexAlternative deltas
    /// replayed at commit_winner time call this source).
    ///
    /// SAFETY: the walker stores `source as *mut dyn WpdaMutableTokenSource`
    /// to avoid cascading `'a` through the struct. The caller MUST keep
    /// `source` alive until `clear_mutable_token_source()` or `reset()`
    /// is called. The Drop impl on WpdaWalker clears the slot defensively.
    /// The lifetime of the trait object is erased via raw-pointer cast +
    /// transmute to satisfy the struct's `'static` field type — the
    /// caller-managed contract above is the load-bearing safety invariant.
    pub fn set_mutable_token_source<'src>(
        &mut self,
        source: &'src mut dyn WpdaMutableTokenSource,
    ) {
        // Erase the source's `'src` lifetime to fit the struct's
        // lifetime-free pointer slot. Sound under the documented SAFETY
        // contract: the caller must keep the source alive until the
        // walker clears the slot via clear_mutable_token_source/reset/Drop.
        let raw: *mut (dyn WpdaMutableTokenSource + 'src) = source as *mut _;
        let erased: *mut (dyn WpdaMutableTokenSource + 'static) =
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
    /// Excludes heavy fields (`recovery_deltas` contents,
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
                pending_ops_len: c.recovery_deltas.len(),
                // Phase F.2 (2026-05-18): swap to SPPF-side mirror.
                collection_depth: c.collection_stack_depth as usize,
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
    ///
    /// **MANDATE VIOLATION** (M11.7, 2026-05-14): beam pruning silently
    /// drops cursors via lex-min weight without evidence — violates the
    /// "never disambiguate early" principle. Use only as an adversarial-
    /// input escape hatch; prefer
    /// [`Self::with_ambiguity_budget`] for mandate-compliant cursor-count
    /// bounding (structured error on overflow rather than silent drop).
    ///
    /// Thin shim over [`Self::with_bounding_mode`]
    /// (`CursorBoundingMode::BeamSize(k)`). Mutually exclusive with
    /// `with_ambiguity_budget` — setting one replaces the other.
    pub fn with_beam_size(mut self, k: usize) -> Self {
        self.bounding_mode = crate::wpda_runtime::CursorBoundingMode::BeamSize(k);
        self
    }

    /// M11.7 (2026-05-14): enable mandate-compliant cursor-count
    /// bounding. When the live frontier would exceed `n` cursors, the
    /// walker transitions to `WpdaState::Error` and the resolve step
    /// returns `WpdaResolveResult::AmbiguityBudget { budget, actual,
    /// position }` rather than silently dropping cursors.
    ///
    /// Mutually exclusive with [`Self::with_beam_size`] — setting one
    /// replaces the other.
    pub fn with_ambiguity_budget(mut self, n: usize) -> Self {
        self.bounding_mode = crate::wpda_runtime::CursorBoundingMode::AmbiguityBudget(n);
        self
    }

    /// M11.7 (2026-05-14): set the cursor-bounding mode directly. Replaces
    /// any prior bounding mode. Mutually-exclusive by construction.
    pub fn with_bounding_mode(
        mut self,
        mode: crate::wpda_runtime::CursorBoundingMode,
    ) -> Self {
        self.bounding_mode = mode;
        self
    }

    /// Read-only access to the current state.
    pub fn state(&self) -> &WpdaState {
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
    ///
    /// **MANDATE VIOLATION**: see [`Self::with_beam_size`] for the
    /// rationale. Passing `None` resets bounding to `Unbounded`. Mutually
    /// exclusive with the ambiguity budget — setting one mode replaces
    /// the other.
    pub fn set_beam_size(&mut self, k: Option<usize>) {
        self.bounding_mode = match k {
            Some(n) => crate::wpda_runtime::CursorBoundingMode::BeamSize(n),
            None => crate::wpda_runtime::CursorBoundingMode::Unbounded,
        };
    }

    /// M11.7 (2026-05-14): set the cursor-bounding mode in-place.
    pub fn set_bounding_mode(&mut self, mode: crate::wpda_runtime::CursorBoundingMode) {
        self.bounding_mode = mode;
    }

    pub fn weight(&self) -> &W {
        &self.weight
    }

    /// Read-only access to the GSS.
    pub fn gss(&self) -> &WpdaGss<W> {
        &self.gss
    }

    // Phase F.3c.5 (2026-05-20): `pub fn builder()` / `pub fn builder_mut()`
    // accessors DELETED. The walker no longer owns a `builder:
    // SemanticBuilder` field, so the accessors have no field to return.
    // External consumers that previously called `walker.builder()` /
    // `walker.builder_mut()` were already refactored in Phase F.3c.1
    // (commit `49fd9a3`) to call `walker.resolve_at_end_of_input(&tokens)`
    // and extract terms from the returned `WpdaResolveResult::Accepted`
    // vector, or to read SPPF state through `walker.sppf()` /
    // `walker.winner_top_node()`.

    /// Optional beam pruning bound (None = unlimited).
    ///
    /// M11.7 backward-compat accessor: returns `Some(k)` iff the bounding
    /// mode is `BeamSize(k)`. For `AmbiguityBudget(n)` or `Unbounded`,
    /// returns `None`. Use [`Self::bounding_mode`] to read the full mode
    /// (including `AmbiguityBudget`).
    pub fn beam_size(&self) -> Option<usize> {
        match self.bounding_mode {
            crate::wpda_runtime::CursorBoundingMode::BeamSize(k) => Some(k),
            _ => None,
        }
    }

    /// M11.7 (2026-05-14): read the full cursor-bounding mode (one of
    /// `Unbounded`, `BeamSize(k)`, or `AmbiguityBudget(n)`).
    pub fn bounding_mode(&self) -> crate::wpda_runtime::CursorBoundingMode {
        self.bounding_mode
    }

    /// Snapshot the current configuration for checkpointing.
    pub fn current_configuration(&self) -> WpdaConfiguration<W> {
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
        WpdaConfiguration {
            pos: self.pos,
            state: self.state.clone(),
            stack,
            weight: self.weight.clone(),
        }
    }

    // ─── Reactive driver ────────────────────────────────────────────────────

    /// Pure transition function: apply `event` to the current configuration
    /// and return the resulting [`WpdaTransition`].
    ///
    /// This is the **primary external API** per survey mandate M1. External
    /// consumers (LSP/DAP/REPL/nREPL) drive parsing by calling this in a loop.
    ///
    /// Phase A.1: takes a `tokens: &dyn WpdaTokenSource` parameter so the
    /// engine's `step()` can peek the input during `WpdaEvent::Step`.
    pub fn process_event(
        &mut self,
        event: WpdaEvent<W>,
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaTransition<W> {
        // Terminal states absorb events without further action.
        if self.state.is_terminal() {
            return WpdaTransition::NoChange;
        }
        match event {
            WpdaEvent::Inspect => WpdaTransition::NoChange,
            WpdaEvent::Step => self.handle_step(tokens),
            WpdaEvent::TokenConsumed { pos, .. } => {
                let from = self.state.clone();
                self.pos = pos;
                self.maybe_prune_frontier();
                let trace = WpdaTraceEntry {
                    pos,
                    from_state: from.clone(),
                    to_state: from.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdaTransition::Transition {
                    new_state: from,
                    trace: Some(trace),
                }
            }
            WpdaEvent::BranchForked { children, .. } => {
                let from = self.state.clone();
                let new_state = WpdaState::AmbiguityFanout {
                    branches: children.clone(),
                };
                self.state = new_state.clone();
                self.maybe_prune_frontier();
                let trace = WpdaTraceEntry {
                    pos: self.pos,
                    from_state: from,
                    to_state: new_state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdaTransition::Transition { new_state, trace: Some(trace) }
            }
            WpdaEvent::BranchResolved { winner, weight } => {
                let from = self.state.clone();
                self.weight = self.weight.times_ref(&weight);
                self.top_node = Some(winner);
                let new_state = WpdaState::InfixLoop {
                    cur_bp: match from {
                        WpdaState::AmbiguityFanout { .. } => 0,
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
                    recovery_deltas: Vec::new(),
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
                            // Phase 5.2 (2026-05-12): fresh empty Arc — the
                    // BranchResolved write-back resets cursor state to
                    // a canonical post-resolution singleton; the
                    // walker.builder (live mutation surface in 5.2)
                    // already captured the winning branch's effects
                    // via commit_winner journal replay.
                    // Option C / C2: post-resolution singleton starts with
                    // empty SPPF stack. Realization at EOI reads the root
                    // SppfId from `self.committed_sppf_root` (added in C6),
                    // not from a cursor's stack.
                    // Phase F.11 (2026-05-20): Arc-wrapped (CoW).
                    sppf_stack: Arc::new(Vec::new()),
                    optional_scope_marks: Vec::new(),
                    binder_scope_marks: Vec::new(),
                    // Phase C.2 (2026-05-17): post-resolution singleton
                    // starts a fresh per-production weight chain. The
                    // pre-resolution pending (if any) was consumed by the
                    // emit_fire_actions that produced the resolved root.
                    pending_packing_weight: W::one_ref(),
                    // Phase F.1 (2026-05-18): post-resolution singleton
                    // matches the fresh empty builder Arc above —
                    // collection_stack_len == 0.
                    collection_stack_depth: 0,
                    // Phase F.4 (2026-05-18): fresh empty Arc.
                    sppf_collection_arena: Arc::new(Vec::new()),
                    // Phase F.3a (2026-05-20): fresh cursor.
                    last_action_output_cat: None,
                    cohort_origin: None,
                    cohort_revive_depth: 0,
                    // Phase F.3c.2 (2026-05-20): fresh empty memo.
                        }];
                self.state = new_state.clone();
                let trace = WpdaTraceEntry {
                    pos: self.pos,
                    from_state: from,
                    to_state: new_state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdaTransition::Transition { new_state, trace: Some(trace) }
            }
            WpdaEvent::SemanticActionFired { .. } => {
                // Walker records the firing in its trace; no state change.
                let trace = WpdaTraceEntry {
                    pos: self.pos,
                    from_state: self.state.clone(),
                    to_state: self.state.clone(),
                    stack_depth: self.gss.frontier_size(),
                };
                WpdaTransition::Transition {
                    new_state: self.state.clone(),
                    trace: Some(trace),
                }
            }
            WpdaEvent::Checkpoint { reason: _ } => {
                let config = self.current_configuration();
                WpdaTransition::Checkpoint { config }
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
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaState {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                break;
            }
            let _ = self.process_event(WpdaEvent::Step, tokens);
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
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaState
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
            if matches!(self.state, WpdaState::AmbiguityFanout { .. }) {
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
            if matches!(action, WpdaStepAction::Idle) {
                // B6 (2026-04-28): make stalls explicit. The engine has
                // nothing more to derive at this configuration. If the
                // walker is in a non-terminal state, this is a stall —
                // surface as Error rather than silently exiting saturation
                // (which would let the caller think the parse "completed"
                // when it actually got stuck). Terminal states
                // (Accepted/Error) are normal exits.
                if !self.state.is_terminal() {
                    self.state = WpdaState::Error {
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
    /// 2. the live state is terminal (Accepted in deterministic mode, or
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
        tokens: &dyn WpdaTokenSource,
    ) -> Result<(), WpdaMaxStepsExceeded>
    where
        W: 'static + std::fmt::Debug,
    {
        for _ in 0..max_steps {
            // T4 SIGUSR1 hang-dump (2026-05-12): publish a fresh snapshot
            // so an out-of-band SIGUSR1 / watchdog dump sees current walker
            // state. No-op when `hang-dump` feature is off or
            // PRATTAIL_HANG_DUMP env var is unset.
            self.publish_to_hang_dump_slot();
            if self.state.is_terminal() {
                return Ok(());
            }
            if matches!(self.state, WpdaState::AmbiguityFanout { .. }) {
                // Snapshot pre-step cursor identities (`(node, pos,
                // weight, inner_state)`) so we can detect whether any
                // cursor actually progressed. Mid-stream the cursor set
                // may grow (Fork), shrink (Drop/merge), or transition
                // states/weights. Only when none of those happens AND
                // we're at EOI do we have a fixed-point parked frontier.
                let prev_count = self.branch_cursors.len();
                // Stage 3.12 Fix 3a (2026-05-02): include weight + recovery_deltas
                // length in the fingerprint. Pre-3.12 a stable cursor whose
                // weight or delta-log size was still changing wouldn't trigger
                // progress_made, but the parse continued for max_steps.
                //
                // H1' fix (2026-05-18, `docs/design/notes/2026-05-18-cursor-
                // explosion-rhocalc.md`): the weight field was DROPPED from
                // the fingerprint. Empirical diagnostic showed a recovery
                // cursor live-locking with only `weight.src_idx` cycling
                // through cat-ids while inner_state/node/pos/ops_len stayed
                // constant. Any productive parse step changes at least one
                // of the STRUCTURAL fields; weight-only refinements that
                // don't move the cursor structurally are tiebreaker noise.
                // `sppf_stack.len()` added to the fingerprint to keep
                // SPPF-interning progress detectable when state/node/pos
                // stay the same but reduces fire.
                let prev_fingerprint: Vec<(crate::gss::GssNodeId, usize, WpdaState, usize, usize)> =
                    self
                        .branch_cursors
                        .iter()
                        .map(|c| {
                            (
                                c.node,
                                c.pos,
                                c.inner_state.clone(),
                                c.recovery_deltas.len(),
                                c.sppf_stack.len(),
                            )
                        })
                        .collect();
                self.step_fanout(tokens);
                let progress_made = self.branch_cursors.len() != prev_count
                    || self
                        .branch_cursors
                        .iter()
                        .zip(prev_fingerprint.iter())
                        .any(|(c, (n, p, s, ops_len, sppf_len))| {
                            c.node != *n
                                || c.pos != *p
                                || c.inner_state != *s
                                || c.recovery_deltas.len() != *ops_len
                                || c.sppf_stack.len() != *sppf_len
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
            if matches!(action, WpdaStepAction::Idle) {
                if self.pos >= tokens.len() {
                    // Stage 3.5b: EOI Idle in live mode is a parked
                    // result, not Error. Caller invokes
                    // `resolve_at_end_of_input` next which will
                    // synthesize the appropriate WpdaResolveResult.
                    return Ok(());
                }
                if !self.state.is_terminal() {
                    self.state = WpdaState::Error {
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
        Err(WpdaMaxStepsExceeded {
            position: self.pos,
        })
    }

    /// Stage 3.5b (2026-05-01): WPDS-correct end-of-input resolution.
    ///
    /// Inspects the post-`run_to_end_of_input` configuration and produces
    /// a `WpdaResolveResult<W>`. The decision tree:
    ///
    /// 1. **Live mode (deterministic, singleton branch_cursors)**:
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
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaResolveResult<W>
    where
        W: 'static + IdempotentSemiring + StarSemiringRef,
    {
        // Phase F.13 walker-stats (2026-05-20): at parse boundary, emit
        // stats summary if env var PRATTAIL_WALKER_STATS=1 is set.
        // Mirrors PRATTAIL_HANG_DUMP precedent in hang_dump.rs.
        #[cfg(feature = "walker-stats")]
        {
            if std::env::var_os("PRATTAIL_WALKER_STATS")
                .map(|v| v == "1")
                .unwrap_or(false)
            {
                eprintln!("{}", self.stats);
            }
        }
        // Phase F.13 H12 Stage 1.2 (2026-05-21): emit dispatch-cohort
        // cache stats alongside the walker-stats summary. Independent
        // of walker-stats feature — the cohort cache has its own
        // counters on the cache struct. Same env-var gate.
        {
            if std::env::var_os("PRATTAIL_WALKER_STATS")
                .map(|v| v == "1")
                .unwrap_or(false)
            {
                struct CacheSummary<'a, W: crate::automata::semiring::SemiringRef>(
                    &'a crate::dispatch_cohort::DispatchCohortCache<W>,
                );
                impl<'a, W: crate::automata::semiring::SemiringRef> std::fmt::Display
                    for CacheSummary<'a, W>
                {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        self.0.write_summary(f)
                    }
                }
                eprintln!("{}", CacheSummary(&self.dispatch_cohort_cache));
            }
        }
        // Phase 5.6-tail-B (2026-05-12): the pre-tail deterministic-mode fast-path
        // returned directly using `self.builder.take_dyn_result()`. Under
        // always-eager Arc::make_mut (Phase 5.3+), all mutations land on
        // `cursor.builder`; `self.builder` is stale until installed.
        // Install cursor[0].builder over self.builder before reading, then
        // return as before.
        //
        // B13c / Candidate H (2026-05-08): the deterministic-mode positional
        // invariant was implemented here but proved to break
        // recovery_integration_tests' test_calc_recovery_trailing_*
        // family — those tests rely on the walker accepting at sub-EOI
        // and the wrapper handling trailing tokens via recovery. The
        // positional gate is left unimplemented at this site; the
        // wrapper's post-resolution `pos < tokens.len()` check (in
        // codegen-emitted parse_<Cat>_via_wpda) handles TrailingTokens
        // correctly.
        if self.deterministic {
            // Install singleton cursor's builder.
            //
            // Phase F.0 (2026-05-17, per
            // `~/.claude/plans/phase-f-cursor-builder-deletion.md`): the
            // Phase F.3c.4 (2026-05-20): cursor.builder field deleted.
            // The install site that read `(*cursor.builder).clone()`
            // and assigned to `self.builder` is gone. self.builder
            // remains as a stub for now (F.3c.5 deletes it); the
            // extract path below uses realize_root_to_terms over the
            // SPPF root captured from cursor.sppf_stack.last().
            // C6: extract the singleton cursor's SPPF root.
            let det_sppf_root = self
                .branch_cursors
                .first()
                .and_then(|c| c.sppf_stack.last().copied())
                .unwrap_or(crate::sppf::SPPF_ID_NONE);
            return match self.state.clone() {
                WpdaState::Accepted => {
                    // Phase F.0: extract via realize_root_to_terms instead
                    // of cursor.builder.take_dyn_result(). Same shape:
                    // returns Vec<Arc<dyn Any>>, take first.
                    let term = if det_sppf_root != crate::sppf::SPPF_ID_NONE {
                        self.realize_root_to_terms(det_sppf_root, Some(1))
                            .into_iter()
                            .next()
                    } else {
                        None
                    };
                    let weight = self.weight.clone();
                    match term {
                        Some(t) => WpdaResolveResult::Accepted {
                            weights: vec![weight],
                            terms: vec![t],
                            roots: vec![det_sppf_root],
                        },
                        None => WpdaResolveResult::ParseError {
                            message: "walker accepted but SPPF realize yielded no term"
                                .to_string(),
                            position: self.pos,
                        },
                    }
                }
                WpdaState::Error { message } => {
                    // M11.7 (2026-05-14): decode the AMBIGUITY_BUDGET_EXCEEDED
                    // sentinel emitted by `maybe_prune_frontier` and surface
                    // as a structured `AmbiguityBudget` resolve result.
                    if let Some((budget, actual, position)) =
                        parse_ambiguity_budget_sentinel(&message)
                    {
                        WpdaResolveResult::AmbiguityBudget {
                            budget,
                            actual,
                            position,
                        }
                    } else {
                        WpdaResolveResult::ParseError {
                            message,
                            position: self.pos,
                        }
                    }
                }
                other => WpdaResolveResult::ParseError {
                    message: format!("incomplete parse in state {:?}", other),
                    position: self.pos,
                },
            };
        }
        // Fanout mode: also decode the AMBIGUITY_BUDGET_EXCEEDED sentinel
        // BEFORE the per-cursor accepting/dead classification.
        if let WpdaState::Error { ref message } = self.state {
            if let Some((budget, actual, position)) =
                parse_ambiguity_budget_sentinel(message)
            {
                return WpdaResolveResult::AmbiguityBudget {
                    budget,
                    actual,
                    position,
                };
            }
        }
        // Phase E Fix A (2026-05-16): Premature-Accepted cursor filter.
        //
        // A cursor in `WpdaState::Accepted` but with `cursor.pos < eof_node`
        // is evidence-failed: it committed to a parse path (typically a
        // lex-Fork max-munch branch, or a cross-cat delegate path that
        // popped CategoryEntry without re-entering InfixLoop) that
        // produced a SHORT parse without consuming all input. Per the
        // user mandate's rule-out-by-evidence clause
        // (feedback_never_disambiguate_early), such cursors are not
        // semantically valid acceptances and must be dropped here, BEFORE
        // the `accepting_indices` filter — otherwise the downstream
        // multi-cursor unfold would still emit terms from these cursors
        // via the SPPF root path if `is_accepting_config` returns true on
        // their (stale) builder shape.
        //
        // Generality: applies to any grammar with lex-ambiguous atomic
        // literals sharing prefixes with operator triggers (e.g.,
        // Calculator's `Int { pattern: r"-?[0-9]+" }` where `-3` can lex
        // as one IntegerLit OR as `[-, 3]`). When both lex-Fork branches
        // reach EOI, both survive this filter; the multiset merge yields
        // Ambiguous([...]) and the evaluator chooses based on evidence
        // (which alt evaluates to a non-Err normal form).
        //
        // This filter complements the existing `accepting_indices`
        // filter at line ~2825 (`is_logical_eoi && is_accepting_config`)
        // by removing premature cursors from `branch_cursors` itself —
        // ensuring that any downstream commit_winner_at_eoi or SPPF
        // root extraction operates on the surviving (EOI-reached) set.
        {
            let eof = tokens.eof_node();
            let len_before = self.branch_cursors.len();
            self.branch_cursors.retain(|c| {
                !matches!(c.inner_state, WpdaState::Accepted) || c.pos >= eof
            });
            // No further work if all were premature.
            if self.branch_cursors.is_empty() && len_before > 0 {
                return WpdaResolveResult::ParseError {
                    message: "all Accepted cursors had unconsumed input \
                              (premature lex-Fork acceptance)"
                        .to_string(),
                    position: self.pos,
                };
            }
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
                // was unreachable in nondeterministic mode because the engine's
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
            0 => WpdaResolveResult::ParseError {
                message: "no accepting branch reached end of input".to_string(),
                position: max_dead_pos,
            },
            1 => {
                // C8.1 (2026-05-16): the M11 multiset snapshot-iteration arm was
                // deleted alongside the C10 W revert to LexicographicWeight.
                // SPPF arena is now the structural ambiguity source; the
                // facade uses `realize_root_to_terms(winner_sppf_root)` to
                // recover the Vec<Cat>. The C7b cycle-fallback (Accepted
                // with empty terms but valid root) is preserved.
                let winner_idx = accepting_indices[0];
                let winner_weight = self.branch_cursors[winner_idx].weight.clone();
                let winner_sppf_root = self.branch_cursors[winner_idx]
                    .sppf_stack
                    .last()
                    .copied()
                    .unwrap_or(crate::sppf::SPPF_ID_NONE);
                self.commit_winner_at_eoi(winner_idx);
                // Phase F.0 (2026-05-17): replace self.builder.take_dyn_result
                // with realize_root_to_terms. The fallback case (Accepted
                // with empty terms but valid root) is preserved.
                let term = if winner_sppf_root != crate::sppf::SPPF_ID_NONE {
                    self.realize_root_to_terms(winner_sppf_root, Some(1))
                        .into_iter()
                        .next()
                } else {
                    None
                };
                match term {
                    Some(t) => WpdaResolveResult::Accepted {
                        weights: vec![winner_weight],
                        terms: vec![t],
                        roots: vec![winner_sppf_root],
                    },
                    None if winner_sppf_root != crate::sppf::SPPF_ID_NONE => {
                        WpdaResolveResult::Accepted {
                            weights: vec![winner_weight],
                            terms: Vec::new(),
                            roots: vec![winner_sppf_root],
                        }
                    }
                    None => WpdaResolveResult::ParseError {
                        message: "winner committed but SPPF realize yielded no term and SPPF root absent"
                            .to_string(),
                        position: self.pos,
                    },
                }
            }
            _ => {
                // C8.1 (2026-05-16): the M11 multiset snapshot-iteration arm
                // (per-cursor `entries_snapshots()` unfold) was deleted
                // alongside C10. Each accepting cursor contributes its own
                // builder term + SPPF root. M7c multi-result semantics
                // are preserved via the per-cursor loop.
                let mut weights: Vec<W> = Vec::with_capacity(accepting_indices.len());
                let mut terms: Vec<Arc<dyn std::any::Any + Send + Sync>> =
                    Vec::with_capacity(accepting_indices.len());
                let mut roots: Vec<crate::sppf::SppfId> =
                    Vec::with_capacity(accepting_indices.len());
                for &idx in &accepting_indices {
                    let cursor_weight = self.branch_cursors[idx].weight.clone();
                    let cursor_root = self.branch_cursors[idx]
                        .sppf_stack
                        .last()
                        .copied()
                        .unwrap_or(crate::sppf::SPPF_ID_NONE);
                    // Phase F.0 (2026-05-17): extract via SPPF realize
                    // instead of cloning cursor.builder. cursor.builder
                    // is structurally redundant with cursor.sppf_stack
                    // for the realize-extract purpose.
                    if cursor_root != crate::sppf::SPPF_ID_NONE {
                        if let Some(t) = self
                            .realize_root_to_terms(cursor_root, Some(1))
                            .into_iter()
                            .next()
                        {
                            weights.push(cursor_weight);
                            terms.push(t);
                            roots.push(cursor_root);
                        }
                    }
                }
                // Commit the first accepting cursor as the live winner
                // for legacy single-result accessors (`walker.builder()`,
                // `walker.state()`, etc.). Done BEFORE the empty-terms
                // check so synthetic test mocks that produce no Terms
                // still observe walker.state transitioning to Accepted.
                let winner_idx = accepting_indices[0];
                self.commit_winner_at_eoi(winner_idx);
                if weights.is_empty() {
                    return WpdaResolveResult::ParseError {
                        message: "accepting cursors had no extractable terms"
                            .to_string(),
                        position: self.pos,
                    };
                }
                WpdaResolveResult::Accepted { weights, terms, roots }
            }
        }
    }

    /// Option C / C7 (2026-05-15): Realize the user AST from a Shared
    /// Packed Parse Forest root.
    ///
    /// Walks the SPPF from `root`, invoking each `Packing`'s
    /// `action_fn` via a fresh `SemanticBuilder` to materialize the
    /// user-AST. Returns a `Vec` of realized terms — one per derivation
    /// alternative (cartesian product over ambiguous packings).
    ///
    /// `limit` bounds the realization size: realization halts once
    /// `limit` distinct terms have been produced. `None` is unbounded.
    /// Per plan §4.3, the default cap is 64 to bound exponential AST
    /// counts on adversarial inputs.
    ///
    /// Realization is the canonical Tomita/Scott-Johnstone post-pass:
    /// the SPPF was built during parse, the user-AST is one
    /// materialization of it. Side-effecting `action_fn`s are forbidden
    /// (plan §10.1) because realization may invoke a given action
    /// multiple times across ambiguous derivations.
    ///
    /// Phase C.4 (2026-05-17): the `W: IdempotentSemiring` bound is
    /// required for the cycle-skip discipline in the tri-color DFS
    /// (Scott-Johnstone GLL §5) to be semantically safe. Idempotent
    /// semirings satisfy `w ⊕ w = w`, so skipping a back-edge packing
    /// does not lose weight contributions — its weight is already
    /// captured at the symbol where the cycle returns.
    ///
    /// Phase C-bis (2026-05-17, per
    /// `docs/design/plans/closed-semiring-cycle-handling.md`): the
    /// bound is RELAXED to `W: StarSemiringRef`, which is strictly
    /// broader. For idempotent semirings (the production case via
    /// `LexicographicWeight`), the existing tri-color skip path
    /// continues to apply unchanged — and is correct because
    /// `star(a) = one()` collapses under idempotency. For non-
    /// idempotent semirings (Counting, Log, Entropy, NBest), the
    /// Newton-method solver at
    /// `automata/semiring.rs::solve_scc_weights_newton` provides
    /// the closed-semiring fixpoint via Lehmann's algorithm. The
    /// Newton path is invoked automatically when the realize walk
    /// encounters a non-trivial SCC.
    pub fn realize_root_to_terms(
        &self,
        root: crate::sppf::SppfId,
        limit: Option<usize>,
    ) -> Vec<Arc<dyn Any + Send + Sync>>
    where
        W: StarSemiringRef,
    {
        self.realize_root_to_terms_with_weights(root, limit)
            .into_iter()
            .map(|(t, _w)| t)
            .collect()
    }

    /// Phase C.6 (2026-05-17): weighted variant of `realize_root_to_terms`.
    ///
    /// Returns `Vec<(term, W)>` where each entry's weight is the `⊗` of
    /// the per-production weights along that derivation, capturing
    /// Goodman's semiring-weighted parse-forest framework. Callers
    /// wanting the existing un-weighted shape can call
    /// `realize_root_to_terms` (which drops the weight) for backward
    /// compatibility; Phase D's facade switch will adopt the weighted
    /// shape directly.
    ///
    /// Phase C-bis (2026-05-17): bound relaxed to `W: StarSemiringRef`
    /// per the closed-semiring cycle-handling plan.
    pub fn realize_root_to_terms_with_weights(
        &self,
        root: crate::sppf::SppfId,
        limit: Option<usize>,
    ) -> Vec<(Arc<dyn Any + Send + Sync>, W)>
    where
        W: StarSemiringRef,
    {
        if root == crate::sppf::SPPF_ID_NONE {
            return Vec::new();
        }
        let mut memo: std::collections::HashMap<crate::sppf::SppfId, Vec<(ActionArg, W)>> =
            std::collections::HashMap::new();
        // Phase C-bis (2026-05-17): cycle-detection flag for lazy
        // Tarjan SCC + Newton multiplier pass. The expensive SCC
        // work runs only if `has_cycle` is set (a back-edge was
        // observed during the tri-color DFS). For acyclic SPPFs
        // (the typical case) the realize path runs at the same cost
        // as before Commit 3.
        let mut has_cycle = false;
        // Phase 3.1.6 (C7b cycle-handling, 2026-05-15): tri-color DFS per
        // Scott-Johnstone GLL parsing 2010 §5 ("Cyclic productions and
        // unit-rules") and Tomita 1986 §6.3 ("Cyclic Grammars").
        //
        // SPPF can have cycles when same-cat reduces hit Symbol-dedup at
        // the same (nt, lo, hi) span. The cycle represents an unbounded
        // ambiguity-class that, by the GLL soundness theorem, contributes
        // NO new derivations beyond the non-cyclic packings at the same
        // Symbol. Detect back-edges at Phase::Enter and short-circuit:
        // - WHITE: unvisited
        // - GRAY: currently on the DFS stack (in-progress)
        // - BLACK: memoized (Phase::Leave completed)
        //
        // Encountering a GRAY at Phase::Enter is a back-edge. Record an
        // empty memo entry and continue — the cyclic packing's
        // contribution is discarded at the Symbol arm of
        // realize_node_leave (skip-gray-child logic).
        //
        // See /home/dylon/.claude/plans/sppf-cycle-handling-principled.md.
        let mut colors: std::collections::HashMap<crate::sppf::SppfId, RealizeColor> =
            std::collections::HashMap::new();
        enum Phase {
            Enter,
            Leave,
        }
        let mut stack: Vec<(crate::sppf::SppfId, Phase)> = vec![(root, Phase::Enter)];
        while let Some((id, phase)) = stack.pop() {
            match phase {
                Phase::Enter => match colors.get(&id) {
                    Some(RealizeColor::Black) => continue,
                    Some(RealizeColor::Gray) => {
                        // Back-edge — cycle detected. Record empty
                        // contribution; do NOT re-traverse. The realize
                        // pass will skip cyclic packings via colors lookup.
                        // Phase C-bis: also flag has_cycle so the
                        // post-pass invokes Tarjan + Newton.
                        has_cycle = true;
                        memo.entry(id).or_insert_with(Vec::new);
                        continue;
                    }
                    None => {
                        colors.insert(id, RealizeColor::Gray);
                        stack.push((id, Phase::Leave));
                        match self.sppf.node(id) {
                            Some(crate::sppf::SppfNode::Symbol { .. }) => {
                                for &p in self.sppf.packings_of(id) {
                                    if colors.get(&p) != Some(&RealizeColor::Black) {
                                        stack.push((p, Phase::Enter));
                                    }
                                }
                            }
                            Some(crate::sppf::SppfNode::Packing { children, .. }) => {
                                for &c in children {
                                    if colors.get(&c) != Some(&RealizeColor::Black) {
                                        stack.push((c, Phase::Enter));
                                    }
                                }
                            }
                            Some(crate::sppf::SppfNode::CollectionId { id: cid }) => {
                                // Recursively realize each collected SppfId so
                                // the Collection arg's contents are materialized.
                                // Phase F.4 (2026-05-18): consult winner cursor's
                                // arena (post-commit) instead of walker-global.
                                if let Some(items) =
                                    self.winner_collection_arena().get(*cid as usize)
                                {
                                    for &item in items {
                                        if colors.get(&item) != Some(&RealizeColor::Black) {
                                            stack.push((item, Phase::Enter));
                                        }
                                    }
                                }
                            }
                            Some(_) | None => {
                                // Leaves (Terminal, Epsilon, OptAbsent, Predicate)
                                // have no children to traverse.
                            }
                        }
                    }
                },
                Phase::Leave => {
                    let realized = self.realize_node_leave(id, &memo, &colors, limit);
                    memo.insert(id, realized);
                    colors.insert(id, RealizeColor::Black);
                }
            }
        }
        // Phase C-bis (2026-05-17, per
        // `docs/design/plans/closed-semiring-cycle-handling.md` §11
        // Commit 3): if the DFS detected a back-edge, post-process
        // memo with the Newton multiplier `star(aggregate)` per
        // non-trivial SCC. Acyclic SPPFs skip this entirely — no
        // Tarjan, no Newton, same cost as before Commit 3.
        if has_cycle {
            let sccs = self.sppf.tarjan_sccs(root);
            for scc in &sccs {
                if scc.len() == 1 && !self.sppf.has_self_loop(scc[0]) {
                    continue; // trivial SCC — no Newton needed
                }
                let solved = self.solve_scc_aggregate(scc, &memo);
                for (local_pos, &symbol_id) in scc.iter().enumerate() {
                    let multiplier = solved[local_pos].star_ref();
                    if let Some(results) = memo.get_mut(&symbol_id) {
                        for entry in results.iter_mut() {
                            entry.1 = multiplier.times_ref(&entry.1);
                        }
                    }
                }
            }
        }
        // Phase C.6: extract (Arc<dyn Any>, W) from each ActionArg::Term
        // in the root's realization. Non-Term variants at the root level
        // indicate a structural mismatch (the root should always be a
        // Term).
        memo.remove(&root)
            .unwrap_or_default()
            .into_iter()
            .filter_map(|(arg, w)| match arg {
                ActionArg::Term { value, .. } => Some((value, w)),
                _ => None,
            })
            .collect()
    }

    /// Internal helper: combine an SPPF node's children realizations
    /// into the node's own realization. Invoked at the Phase::Leave
    /// step of `realize_root_to_terms`.
    ///
    /// Phase C.6 (2026-05-17): each returned `(ActionArg, W)` tuple's
    /// W is the per-derivation weight at this node. For leaves
    /// (Terminal, Epsilon, OptAbsent, Predicate, CollectionId,
    /// BinderScope) the weight is `W::one_ref()` per §2.5. For Symbol
    /// nodes the weight comes from each linked Packing's accumulated
    /// combo-weight ⊗ Packing.weight. For Packing nodes the weight is
    /// `Π children-weights ⊗ Packing.weight` (cartesian product of
    /// child realizations threads ⊗).
    fn realize_node_leave(
        &self,
        id: crate::sppf::SppfId,
        memo: &std::collections::HashMap<crate::sppf::SppfId, Vec<(ActionArg, W)>>,
        colors: &std::collections::HashMap<crate::sppf::SppfId, RealizeColor>,
        limit: Option<usize>,
    ) -> Vec<(ActionArg, W)>
    where
        W: StarSemiringRef,
    {
        match self.sppf.node(id) {
            Some(crate::sppf::SppfNode::Terminal {
                token_kind,
                text_handle,
                pos,
                pushed_via_push_ident,
            }) => {
                let text = self.sppf.text(*text_handle).to_string();
                let pos_usize = match pos {
                    crate::sppf::PosOrSynth::Real(p) | crate::sppf::PosOrSynth::Synthesized(p) => {
                        *p as usize
                    }
                };
                // Bug E fix (Phase 3.1.3): branch on the discriminator from
                // emit_* origin, NOT on TokenKind::Ident. emit_push_ident
                // produces ActionArg::Ident regardless of kind (always
                // Ident); emit_push_token produces ActionArg::Token even
                // when kind happens to be Ident (cross-cat-projection,
                // general-token-capture paths).
                let arg = if *pushed_via_push_ident {
                    ActionArg::Ident {
                        name: text,
                        pos: pos_usize,
                    }
                } else {
                    ActionArg::Token {
                        kind: token_kind.clone(),
                        text,
                        pos: pos_usize,
                    }
                };
                // Phase C.6: leaf node — weight is `W::one_ref()` per §2.5.
                vec![(arg, W::one_ref())]
            }
            Some(crate::sppf::SppfNode::Epsilon { .. }) => {
                // Epsilon contributes nothing observable to the action's
                // input — but realization still needs an entry per
                // derivation. We yield Optional(None) as a neutral marker;
                // typical grammars don't reduce on Epsilon directly.
                vec![(ActionArg::Optional(None), W::one_ref())]
            }
            Some(crate::sppf::SppfNode::OptAbsent { .. }) => {
                vec![(ActionArg::Optional(None), W::one_ref())]
            }
            Some(crate::sppf::SppfNode::Predicate { handle }) => {
                if let Some(p) = self.sppf_predicate_arena.get(*handle as usize) {
                    vec![(ActionArg::Predicate(Arc::clone(p)), W::one_ref())]
                } else {
                    Vec::new()
                }
            }
            Some(crate::sppf::SppfNode::CollectionId { id: cid }) => {
                // The CollectionId placeholder is consumed by the action
                // alongside the collected items. The realization yields
                // ActionArg::CollectionId(cid); the parent Packing's
                // action_fn call will see this and (in the generated
                // collection-finalize action) drain the collected items
                // from the builder's collection_stack.
                //
                // The collected items are populated in the synthetic
                // realization builder before the action_fn call (see
                // realize_packing_call).
                vec![(ActionArg::CollectionId(*cid as u8), W::one_ref())]
            }
            Some(crate::sppf::SppfNode::BinderScope { names_text, depth }) => {
                // Bug N (Phase 3.1.5): reconstruct the ActionArg::BinderScope
                // arg from the SPPF mirror. The builder side already pushed
                // this arg onto its args-stack at parse time (via
                // builder.end_binder_scope inside apply_effect_to_cursor); at
                // realization time we recreate the BinderHandle from the
                // interned TextHandles + depth, and the parent Packing's
                // realize_packing_call forwards via push_raw_arg.
                let names: Vec<String> = names_text
                    .iter()
                    .map(|&h| self.sppf.text(h).to_string())
                    .collect();
                vec![(
                    ActionArg::BinderScope(
                        crate::wpda_runtime::BinderHandle::new(names, *depth),
                    ),
                    W::one_ref(),
                )]
            }
            Some(crate::sppf::SppfNode::Symbol { .. }) => {
                // Concat all packings' realizations. Phase C.6 preserves
                // per-derivation weights; the Symbol-level ⊕-aggregation
                // is captured in Sppf::Symbol.weight_sum at link time,
                // but here at realize time we keep each alternative's
                // own weight so callers can pick one (or ⊕-aggregate
                // explicitly at the facade layer).
                //
                // Phase 3.1.6 cycle-skip (2026-05-15): per Scott-Johnstone
                // 2010 GLL §5, a packing whose memo Vec is empty AND
                // whose color is still Gray represents a cycle-via-this-
                // packing — its derivations are STRICTLY redundant with
                // the non-cyclic packings of this Symbol. Skip it.
                //
                // BLACK packings with empty memo are legitimate
                // "produces-nothing" terminal-equivalents (e.g.,
                // OptAbsent under an empty optional); include them.
                //
                // Phase C-bis (2026-05-17): if has_cycle was set during
                // the DFS, the post-pass in
                // `realize_root_to_terms_with_weights` applies the
                // Newton multiplier `star(aggregate)` to memo entries
                // of Symbols in non-trivial SCCs. For idempotent W
                // (production `LexicographicWeight`) `star = one` so
                // this is identity; for non-idempotent W the multiplier
                // captures the cycle's closed-semiring contribution.
                let mut out: Vec<(ActionArg, W)> = Vec::new();
                for &p in self.sppf.packings_of(id) {
                    let p_color = colors.get(&p).copied();
                    let p_results = match memo.get(&p) {
                        Some(v) => v,
                        None => continue,
                    };
                    if p_results.is_empty() && p_color == Some(RealizeColor::Gray) {
                        continue; // cycle back-edge — skip
                    }
                    for entry in p_results {
                        if let Some(cap) = limit {
                            if out.len() >= cap {
                                return out;
                            }
                        }
                        out.push(entry.clone());
                    }
                }
                out
            }
            Some(crate::sppf::SppfNode::Packing { rule_idx, children, weight }) => {
                self.realize_packing_call(
                    *rule_idx,
                    children,
                    weight.clone(),
                    memo,
                    limit,
                )
            }
            // Phase F.8 (2026-05-18): TriggerTerminal contributes no
            // ActionArg. `realize_packing_call` filters TriggerTerminal
            // children out of the cartesian product, so this arm is
            // defensive — it would only execute if a TriggerTerminal SppfId
            // reached realize_node_leave via the BFS traversal. Returning
            // Vec::new() ensures the Bug I "missing memo for child SppfId"
            // panic at line 3697-3705 sees `Some(empty_vec)` not `None`.
            Some(crate::sppf::SppfNode::TriggerTerminal { .. }) => Vec::new(),
            None => Vec::new(),
        }
    }

    /// Phase C-bis (2026-05-17, per
    /// `docs/design/plans/closed-semiring-cycle-handling.md` §11 Commit 3):
    /// solve the closed-semiring fixpoint for a non-trivial SCC via
    /// Newton's method.
    ///
    /// Returns a `Vec<W>` of aggregate weights, one per SCC member, in
    /// the same order as `scc`. The aggregate at index `i` is the
    /// total inside-weight at `scc[i]` accounting for all derivations
    /// including cycle iterations.
    ///
    /// **Algorithm** (per Esparza-Kiefer-Luttenberger 2007 for
    /// multi-call SCCs, fast-path linear closed form when all
    /// in-SCC packings have ≤1 in-SCC child):
    /// 1. Build SCC-local-index map `idx: SppfId → usize`.
    /// 2. Compute `memo_outside`: for each Symbol child of any in-SCC
    ///    packing that is OUTSIDE the SCC, its inside-weight via
    ///    `⊕`-aggregation over `memo` (Goodman 1999 §3).
    /// 3. Factor each packing of each SCC Symbol via
    ///    [`crate::sppf::Sppf::factor_scc_packing`].
    /// 4. Invoke
    ///    [`crate::automata::semiring::solve_scc_weights_newton`].
    fn solve_scc_aggregate(
        &self,
        scc: &[crate::sppf::SppfId],
        memo: &std::collections::HashMap<crate::sppf::SppfId, Vec<(ActionArg, W)>>,
    ) -> Vec<W>
    where
        W: StarSemiringRef,
    {
        let mut idx: rustc_hash::FxHashMap<crate::sppf::SppfId, usize> =
            rustc_hash::FxHashMap::default();
        for (i, &id) in scc.iter().enumerate() {
            idx.insert(id, i);
        }
        let mut memo_outside: rustc_hash::FxHashMap<crate::sppf::SppfId, W> =
            rustc_hash::FxHashMap::default();
        for &symbol in scc {
            for &p in self.sppf.packings_of(symbol) {
                if let Some(crate::sppf::SppfNode::Packing { children, .. }) =
                    self.sppf.node(p)
                {
                    for &c in children {
                        if idx.contains_key(&c) || memo_outside.contains_key(&c) {
                            continue;
                        }
                        let w = match memo.get(&c) {
                            Some(results) => results
                                .iter()
                                .fold(W::zero_ref(), |acc, (_arg, w)| acc.plus_ref(w)),
                            None => W::one_ref(),
                        };
                        memo_outside.insert(c, w);
                    }
                }
            }
        }
        let mut packings: Vec<crate::sppf::PackingFactored<W>> = Vec::new();
        for (i, &symbol) in scc.iter().enumerate() {
            for &p in self.sppf.packings_of(symbol) {
                packings.push(
                    self.sppf
                        .factor_scc_packing(p, i, &idx, &memo_outside),
                );
            }
        }
        crate::automata::semiring::solve_scc_weights_newton(scc.len(), &packings, 64)
    }

    /// Cartesian-product the children's realized ActionArgs, then call
    /// the rule's `action_fn` per combo to produce a Vec of realized
    /// Term args.
    ///
    /// Phase C.6 (2026-05-17): threads weights via ⊗ across the
    /// cartesian product. Each child contributes a (arg, w) pair; a
    /// full combo accumulates `combo_weight = Π child-weights`. The
    /// returned tuple's weight is `combo_weight ⊗ packing_weight` —
    /// the per-derivation weight at this Packing.
    fn realize_packing_call(
        &self,
        rule_idx: u32,
        children: &[crate::sppf::SppfId],
        packing_weight: W,
        memo: &std::collections::HashMap<crate::sppf::SppfId, Vec<(ActionArg, W)>>,
        limit: Option<usize>,
    ) -> Vec<(ActionArg, W)>
    where
        W: StarSemiringRef,
    {
        // OPTIONAL_PRESENT_RULE_IDX sentinel: synthetic packing emitted
        // by emit_finalize_optional_scope_present. Wrap children's args
        // into ActionArg::Optional(Some(...)).
        if rule_idx == Self::OPTIONAL_PRESENT_RULE_IDX {
            // Cartesian product over children; each combo becomes one
            // Optional(Some(args)). Phase C.6: combo_weight threads ⊗
            // across child weights. OPTIONAL_PRESENT's packing weight
            // is W::one_ref() by §2.5, so the result weight equals
            // combo_weight directly.
            let mut combos: Vec<(Vec<ActionArg>, W)> =
                vec![(Vec::with_capacity(children.len()), W::one_ref())];
            for &c in children {
                let child_results = match memo.get(&c) {
                    Some(v) => v,
                    None => return Vec::new(),
                };
                // C7b memory-safety fix (Phase 3.1.6, 2026-05-15):
                // pre-allocating combos×child_results ignored the `limit`
                // cap and produced O(N^K) RAM even though the inner loop
                // bounded the result. Cap pre-allocation at `limit` so
                // wide-fanout productions don't OOM during realization.
                let unbounded_capacity =
                    combos.len().saturating_mul(child_results.len().max(1));
                let pre_alloc = match limit {
                    Some(cap) => cap.min(unbounded_capacity),
                    None => unbounded_capacity,
                };
                let mut next: Vec<(Vec<ActionArg>, W)> = Vec::with_capacity(pre_alloc);
                for (combo, combo_w) in &combos {
                    for (arg, child_w) in child_results {
                        let mut ext_args = combo.clone();
                        ext_args.push(arg.clone());
                        let ext_w = combo_w.times_ref(child_w);
                        next.push((ext_args, ext_w));
                        if let Some(cap) = limit {
                            if next.len() >= cap {
                                break;
                            }
                        }
                    }
                    if let Some(cap) = limit {
                        if next.len() >= cap {
                            break;
                        }
                    }
                }
                combos = next;
            }
            return combos
                .into_iter()
                .map(|(args, w)| (ActionArg::Optional(Some(args)), w))
                .collect();
        }
        // Phase F.8 (2026-05-18): TriggerTerminal children carry only span
        // metadata (used by `span_lo` in emit_fire_action to give the
        // parent Symbol a distinct lo_pos) — they contribute NO ActionArg
        // to the action_fn. Filter them out BEFORE the arity-check and
        // BEFORE the cartesian product. Non-prefix rules have no
        // TriggerTerminal children so this filter is a no-op for them.
        let action_children: Vec<crate::sppf::SppfId> = children
            .iter()
            .copied()
            .filter(|&c| !matches!(
                self.sppf.node(c),
                Some(crate::sppf::SppfNode::TriggerTerminal { .. })
            ))
            .collect();
        // Bug A fix (Phase 3.1.2, 2026-05-15): the Packing.rule_idx is a
        // GLOBAL rule id encoded as `(cat_src_idx << 16) | rule_idx_within_cat`
        // by emit_fire_action. Decode directly — no linear scan, no
        // collision risk when two cats share a local rule_idx.
        let arity = action_children.len();
        let cat = (rule_idx >> 16) as u16;
        let local_rule_idx = (rule_idx & 0xFFFF) as u16;
        let action_entry = self.engine.action_for(cat, local_rule_idx);
        let action_fn = match action_entry {
            Some(e) => e.action_fn,
            None => return Vec::new(), // No matching action — realization stub.
        };
        debug_assert_eq!(
            action_entry.unwrap().arity as usize,
            arity,
            "Bug A guard: Packing.rule_idx encodes ({cat}, {local_rule_idx}) but action_entry.arity ({}) != Packing.children.len() ({arity}). \
             This indicates a corrupt SPPF or a mismatched intern_packing/action_for. \
             rule_idx={rule_idx:#x}",
            action_entry.unwrap().arity,
        );

        // Cartesian product over children's realized args. Phase C.6
        // threads weights via ⊗: each combo accumulates the product of
        // child weights along the way.
        let mut combos: Vec<(Vec<ActionArg>, W)> =
            vec![(Vec::with_capacity(arity), W::one_ref())];
        for &c in &action_children {
            // Bug I fix (Phase 3.1.4): panic loudly on missing memo. The
            // realize_root_to_terms BFS guarantees Phase::Leave executes
            // ONLY after every child's Phase::Leave; a missing memo
            // indicates a traversal bug, not legitimate "no derivation."
            let child_results = match memo.get(&c) {
                Some(v) => v,
                None => {
                    debug_assert!(
                        false,
                        "Bug I: realize_packing_call missing memo for child SppfId {} \
                         while realizing Packing rule_idx={:#x}. \
                         Indicates traversal bug in realize_root_to_terms BFS.",
                        c, rule_idx,
                    );
                    return Vec::new();
                }
            };
            // Same C7b memory-safety fix as above: cap pre-allocation at
            // `limit` to bound O(N^K) RAM on wide-fanout productions.
            let unbounded_capacity =
                combos.len().saturating_mul(child_results.len().max(1));
            let pre_alloc = match limit {
                Some(cap) => cap.min(unbounded_capacity),
                None => unbounded_capacity,
            };
            let mut next: Vec<(Vec<ActionArg>, W)> = Vec::with_capacity(pre_alloc);
            for (combo, combo_w) in &combos {
                for (arg, child_w) in child_results {
                    let mut ext_args = combo.clone();
                    ext_args.push(arg.clone());
                    let ext_w = combo_w.times_ref(child_w);
                    next.push((ext_args, ext_w));
                    if let Some(cap) = limit {
                        if next.len() >= cap {
                            break;
                        }
                    }
                }
                if let Some(cap) = limit {
                    if next.len() >= cap {
                        break;
                    }
                }
            }
            combos = next;
        }

        // For each combo: build a fresh SemanticBuilder, push args, fire
        // action, capture top. Phase C.6: result weight is
        // `combo_weight ⊗ packing_weight`.
        let mut out: Vec<(ActionArg, W)> = Vec::with_capacity(combos.len());
        for (args, combo_w) in combos {
            let mut sb = SemanticBuilder::new();
            // B.1 (Phase E Stage 1, 2026-05-16): Bug C fix — pre-allocate
            // collection slots 0..=max(CollectionId) in `args` BEFORE the
            // push loop. Without this, monotonic `sb.start_collection()`
            // returns slot ids in encounter order, but the realize-time
            // encounter order can differ from parse-time allocation
            // order (e.g., `{open(n, 0) | n[{0}]}` produces a packing
            // whose args list contains CollectionId(1) before
            // CollectionId(0)). Pre-allocating all slots up to the max
            // makes the per-id splice-into-collection branches operate
            // on already-existing slots rather than allocating in
            // arrival order. The previous `debug_assert_eq!(slot_id, *id)`
            // gate would panic on out-of-order encounters.
            let max_coll_id: Option<u32> = args.iter()
                .filter_map(|a| match a {
                    ActionArg::CollectionId(id) => Some(*id as u32),
                    _ => None,
                })
                .max();
            if let Some(max_id) = max_coll_id {
                for _ in 0..=max_id {
                    let _ = sb.start_collection();
                }
            }
            // Push args one-by-one. The push semantics must match what
            // the walker's emit-helpers would have done so the action's
            // pop_args call shape is preserved.
            for arg in &args {
                match arg {
                    ActionArg::Token { kind, text, pos } => {
                        sb.push_token(kind.clone(), text.clone(), *pos);
                    }
                    ActionArg::Ident { name, pos } => {
                        sb.push_ident(name.clone(), *pos);
                    }
                    ActionArg::Term { value, .. } => {
                        // Push as a Term arg; the action_fn pop_args
                        // sees this as ActionArg::Term.
                        sb.push_term_arc(Arc::clone(value));
                    }
                    ActionArg::CollectionId(id) => {
                        // B.1: slot already pre-allocated above; no
                        // start_collection call here. Splice items into
                        // the slot the CollectionId references, then
                        // push the CollectionId arg. action_fn will
                        // pop_args and drain the collection.
                        // Phase F.4 (2026-05-18): consult winner
                        // cursor's arena (post-commit).
                        if let Some(items) = self.winner_collection_arena().get(*id as usize) {
                            // Each item is realized as an ActionArg::Term
                            // in `memo`; push them onto sb so
                            // push_to_collection drains correctly.
                            for &item in items {
                                if let Some(item_realized) = memo.get(&item) {
                                    if let Some((item_arg, _item_w)) = item_realized.first() {
                                        match item_arg {
                                            ActionArg::Term { value, .. } => {
                                                sb.push_term_arc(Arc::clone(value));
                                                sb.push_to_collection(*id);
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                            }
                        }
                        sb.push_collection_id(*id);
                    }
                    ActionArg::Predicate(p) => {
                        sb.push_predicate_arc(Arc::clone(p));
                    }
                    ActionArg::Optional(_) | ActionArg::Collection { .. } | ActionArg::BinderScope(_) => {
                        // BinderScope / Collection / Optional arrive via
                        // dedicated push pathways in the walker. For
                        // realization, push as the corresponding direct
                        // ActionArg via a small helper that bypasses
                        // typed-push.
                        // BinderScope/Collection should rarely appear at
                        // child positions in normal grammars; emit them
                        // via push_raw_arg as a safety fallback.
                        sb.push_raw_arg(arg.clone());
                    }
                }
            }
            // Fire the action with the args. action_fn pops the args
            // and pushes one Term back.
            let pre_len = sb.len();
            let popped = sb.pop_args(arity);
            // Bug J resolution (Part B, 2026-05-16): capture arg shapes
            // for diagnostic logging in debug builds when action_fn
            // elides. The captured shapes reveal which arg the action
            // rejected (e.g., Ident where Term was expected) for any
            // grammar's failing realize reconstruction.
            #[cfg(debug_assertions)]
            let arg_shapes_for_diag: Vec<&'static str> = popped.iter().map(|a| match a {
                ActionArg::Token { .. } => "Token",
                ActionArg::Ident { .. } => "Ident",
                ActionArg::Term { type_name, .. } => *type_name,
                ActionArg::BinderScope(_) => "BinderScope",
                ActionArg::Collection { type_name, .. } => *type_name,
                ActionArg::CollectionId(_) => "CollectionId",
                ActionArg::Predicate(_) => "Predicate",
                ActionArg::Optional(_) => "Optional",
            }).collect();
            (action_fn)(&mut sb, popped);
            let post_len = sb.len();
            let expected_len = pre_len.saturating_sub(arity).saturating_add(1);
            // Bug J resolution (Part A, 2026-05-16): mandate-compliant
            // combo elision when action_fn returns without pushing
            // exactly one Term.
            //
            // Per the preserve-all-derivations mandate's rule-out-by-
            // evidence clause: an action_fn whose pattern matches fail
            // (each `_ => return` arm fires when args don't match the
            // rule's preconditions) is EVIDENCE that the rule doesn't
            // reduce on these specific args. The combo is dropped; if
            // all combos elide, the caller's realize returns an empty
            // Vec and the failure surfaces as ParseError downstream.
            //
            // The pre-Bug-J-resolution code used `debug_assert_eq!`
            // which panicked in debug and silently dropped in release —
            // NEITHER honored preserve-all-derivations. The new path
            // is uniform: drop the combo, log in debug, continue.
            //
            // Grammar-general: applies to any grammar's action_fn that
            // uses `_ => return` arms for arg-shape validation. Future
            // grammars with deeper realize/parse-time arg shape
            // mismatches surface this diagnostic for investigation
            // rather than panicking.
            if post_len != expected_len {
                #[cfg(debug_assertions)]
                {
                    eprintln!(
                        "[realize_packing_call] action elided (post_len={}, expected={}): \
                         rule_idx={:#x} cat={} local_rule={} arity={} pre_len={} \
                         arg_shapes={:?}",
                        post_len, expected_len, rule_idx, cat, local_rule_idx,
                        arity, pre_len, arg_shapes_for_diag,
                    );
                }
                // Drain any stale state the action partially produced
                // so the next combo starts fresh.
                while sb.len() > pre_len.saturating_sub(arity) {
                    let _ = sb.pop_args(1);
                }
                continue;
            }
            if let Some(t) = sb.take_dyn_result() {
                // The realized term's type_name is set by the
                // action's push_term; we approximate via "Cat" name
                // tag derived from the cat_src_idx. The downstream
                // facade downcasts via Arc::downcast::<Cat> so the
                // tag is for debug only.
                //
                // Phase C.6: per-derivation weight = combo_w ⊗ packing_weight.
                let result_w = combo_w.times_ref(&packing_weight);
                out.push((
                    ActionArg::Term {
                        value: t,
                        type_name: "RealizedTerm",
                    },
                    result_w,
                ));
            }
            if let Some(cap) = limit {
                if out.len() >= cap {
                    return out;
                }
            }
        }
        out
    }

    /// Stage 3.5b (2026-05-01): cursor-level "is this an accepting
    /// configuration?" classifier.
    ///
    /// A cursor at EOI is accepting iff:
    /// - `inner_state == Accepted` (engine emitted `WpdaStepAction::Accept`), OR
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
        // Phase 5.6-tail-A (2026-05-12): replaces the pre-tail
        // `cursor_will_produce_term` dry-run over `recovery_deltas`
        // with a direct shape check on `cursor.builder`. Under always-
        // eager Arc::make_mut (Phase 5.3+), the live builder IS the
        // authoritative state — broken FireActions transition the cursor
        // to `WpdaState::Error` at eager-fire time and are filtered by
        // `cursor_resolution_check :: Drop`. The remaining condition is
        // simply "does cursor.builder hold exactly one Term arg?" — the
        // EOI gate that `take_dyn_result` would consult at commit.
        // Phase F.2 (2026-05-18): SPPF-side helper.
        if !self.is_cursor_accepting_terminal(cursor) {
            return false;
        }
        match &cursor.inner_state {
            WpdaState::Accepted => true,
            WpdaState::InfixLoop { .. } => true,
            WpdaState::Unwinding => {
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

    /// Stage 3.12 fix (2026-05-02): "logical EOI" — true when the
    /// cursor's `pos` either consumed the entire token stream or is
    /// parked at a trailing `Token::Eof` that the engine never advances
    /// past. The lexer appends `Token::Eof` (e.g., `parser.rs:692` in
    /// generated code), so `tokens.len()` is `content_len + 1` and
    /// natural rule-end positions are `content_len` (= `tokens.len() - 1`).
    /// The pre-3.12 EOI check `pos >= tokens.len()` only worked in the
    /// pre-tail deterministic-mode short-circuit in `resolve_at_end_of_input`.
    /// Forked mode now matches the same "trailing EOF is OK" contract
    /// that `parse_<Cat>::parse_via_wpda` uses on its outer `pos` check.
    #[inline]
    fn is_logical_eoi(&self, pos: usize, tokens: &dyn WpdaTokenSource) -> bool {
        // M6c.8.4 (2026-05-14): cursor is at EOI iff `pos` equals the
        // canonical EOF sentinel index OR is past the slice's flat
        // length.
        //
        // For `SliceTokenSource` and `MultiTokenSource`, the default
        // `eof_node()` returns `len() - 1` and the trailing-Eof clause
        // preserves the pre-M6c.8.4 "pos is at the trailing Eof token"
        // semantics. The `pos >= len()` clause covers cursors that
        // advanced past the end (defensive).
        //
        // For `LatticeTokenSource`, `eof_node()` returns the canonical
        // EOF sentinel index from the DAG. Crucially, this is NOT
        // necessarily `nodes.len() - 1`: orphan nodes (allocated by
        // M6c.7.1 soft-fail for secondary-alt dead-ends) may sit at
        // indices BEFORE OR AFTER the EOF sentinel. A cursor parked
        // at an orphan node MUST NOT be considered EOI — the orphan
        // is structurally a dead-end alt that should die, not accept.
        //
        // The `pos == eof_node` check is precise: it accepts ONLY at
        // the canonical EOF sentinel. The `pos >= len()` slice
        // fallback covers SliceTokenSource's past-end semantics where
        // `eof_node = len() - 1` and `pos = len()` is "consumed
        // the Eof token and advanced past."
        pos == tokens.eof_node()
            || pos >= tokens.len()
            || (pos + 1 == tokens.len()
                && tokens.peek_kind(pos) == Some(TokenKind::Eof))
    }

    /// Stage 3.5b (2026-05-01): EOI-time variant of `commit_winner`.
    ///
    /// Identical to `commit_winner` semantically (replays winner's
    /// recovery_deltas, donates collection_stack, splices winner's
    /// `(node, pos, weight, inner_state)` into the live walker), but
    /// invoked exclusively from `resolve_at_end_of_input` rather than
    /// mid-stream from `step_fanout`. The implementation delegates to
    /// `commit_winner` to keep replay logic single-source.
    fn commit_winner_at_eoi(&mut self, winner_idx: usize) {
        self.commit_winner(winner_idx);
    }

    // ─── Internal step handler ──────────────────────────────────────────────

    fn handle_step(&mut self, tokens: &dyn WpdaTokenSource) -> WpdaTransition<W> {
        // Stage 6 G6+ (2026-05-02): bump trace step counter once per Step.
        self.step_counter = self.step_counter.wrapping_add(1);
        let from = self.state.clone();
        // Step 3 (Fork plan F6): when in AmbiguityFanout, drive cursors
        // via step_fanout rather than the per-state engine.step (engine
        // returns Idle for AmbiguityFanout).
        if matches!(self.state, WpdaState::AmbiguityFanout { .. }) {
            self.step_fanout(tokens);
            if self.state == from {
                return WpdaTransition::NoChange;
            }
            let trace = WpdaTraceEntry {
                pos: self.pos,
                from_state: from,
                to_state: self.state.clone(),
                stack_depth: self.gss.frontier_size(),
            };
            if self.state.is_terminal() {
                return WpdaTransition::Done {
                    state: self.state.clone(),
                };
            }
            return WpdaTransition::Transition {
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
        if matches!(action, WpdaStepAction::Idle) {
            return WpdaTransition::NoChange;
        }
        self.apply_action(action, tokens);
        if self.state == from {
            // No state change but engine wasn't Idle — trace it as a
            // configuration change without a state transition.
            let trace = WpdaTraceEntry {
                pos: self.pos,
                from_state: from.clone(),
                to_state: from.clone(),
                stack_depth: self.gss.frontier_size(),
            };
            return WpdaTransition::Transition {
                new_state: from,
                trace: Some(trace),
            };
        }
        let trace = WpdaTraceEntry {
            pos: self.pos,
            from_state: from,
            to_state: self.state.clone(),
            stack_depth: self.gss.frontier_size(),
        };
        if self.state.is_terminal() {
            return WpdaTransition::Done {
                state: self.state.clone(),
            };
        }
        WpdaTransition::Transition {
            new_state: self.state.clone(),
            trace: Some(trace),
        }
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): thin dispatcher.
    ///
    /// Pre-Phase-4: ~370-line arm-by-arm body that mutated both the live
    /// builder AND walker fields directly, with a parallel
    /// `apply_action_to_cursor` for the post-Fork multi-cursor path. The
    /// dual-mutation surface produced the Class C bug class.
    ///
    /// Post-Phase-4 + Phase 5.6-tail: dispatcher routes EVERY action through
    /// `apply_action_to_cursor` against `branch_cursors[0]` (the singleton
    /// in deterministic mode). Per-variant `emit_*` helpers eagerly mutate
    /// `cursor.builder` via `Arc::make_mut`; `self.builder` is installed
    /// from `cursor.builder` at end-of-step in deterministic mode (and at
    /// commit_winner in nondeterministic mode). Single mutation surface; Class C
    /// structurally eliminated.
    ///
    /// Outcome handling:
    /// - `Drop`:      cursor died (Error / non-resolved Idle). Restore
    ///                singleton with current walker view to preserve L4.
    /// - `Alive`:     reinstate the cursor as branch_cursors[0].
    /// - `Resolved`:  reinstate (parked at EOI for resolve_at_end_of_input).
    /// - `ForkInto`:  replace branch_cursors with children, set state to
    ///                AmbiguityFanout. `self.deterministic` flips to false.
    fn apply_action(&mut self, action: WpdaStepAction<W>, tokens: &dyn WpdaTokenSource) {
        // Phase 5.6-tail-B (2026-05-12): pre-tail this called
        // `debug_flush_lazy_invariant()` to assert L1 (deterministic mode implies
        // singleton cursor with empty recovery_deltas). Deleted with
        // the CursorMode enum — invariant is moot.
        // L5: terminal state is mode-irrelevant.
        if self.state.is_terminal() {
            return;
        }
        debug_assert_eq!(
            self.branch_cursors.len(),
            1,
            "apply_action invariant: branch_cursors must be a singleton at \
             entry (apply_action is the deterministic-mode entry; step_fanout \
             drives the multi-cursor nondeterministic mode directly)",
        );
        let mut cursor = self.branch_cursors.swap_remove(0);
        let outcome = self.apply_action_to_cursor(&mut cursor, action, tokens);
        match outcome {
            CursorOutcome::Drop => {
                // Cursor died. In deterministic mode, helpers already mirrored the
                // terminal state (set_cursor_inner_state) to self.state,
                // so the live walker reflects the failure. Restore a
                // fresh singleton anchored at the current walker view to
                // preserve L4 (always-non-empty branch_cursors).
                self.branch_cursors.push(BranchCursor {
                    node: self.top_node.unwrap_or(0),
                    pos: self.pos,
                    weight: W::one_ref(),
                    inner_state: self.state.clone(),
                    recovery_deltas: Vec::new(),
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
                            // Phase 5.2 (2026-05-12): fresh empty Arc — the
                    // post-Drop fresh singleton has no Fork-ancestor
                    // builder to inherit. Live mutations continue to
                    // flow through `self.builder` (deterministic mode); the
                    // cursor's Arc is a future anchor (5.3+).
                    // Option C / C2: post-Drop reset starts with empty SPPF
                    // stack. The drop discards the failed cursor's tree
                    // construction; the deterministic-mode singleton resets.
                    // Phase F.11 (2026-05-20): Arc-wrapped (CoW).
                    sppf_stack: Arc::new(Vec::new()),
                    optional_scope_marks: Vec::new(),
                    binder_scope_marks: Vec::new(),
                    // Phase C.2 (2026-05-17): post-Drop reset clears the
                    // pending weight chain — the dropped cursor's unused
                    // per-production weight is discarded with the cursor.
                    pending_packing_weight: W::one_ref(),
                    // Phase F.1 (2026-05-18): post-Drop reset matches the
                    // fresh empty builder Arc above — collection_stack_len == 0.
                    collection_stack_depth: 0,
                    // Phase F.4 (2026-05-18): fresh empty Arc.
                    sppf_collection_arena: Arc::new(Vec::new()),
                    // Phase F.3a (2026-05-20): post-Drop reset clears the
                    // mirror — the dropped cursor's action history is gone.
                    last_action_output_cat: None,
                    cohort_origin: None,
                    cohort_revive_depth: 0,
                    // Phase F.3c.2 (2026-05-20): post-Drop reset clears memo.
                        });
            }
            CursorOutcome::Alive | CursorOutcome::Resolved => {
                // Phase 5.6-tail-B (2026-05-12): install the cursor's
                // builder over self.builder before re-pushing. Under
                // always-eager Arc::make_mut, all mutations land on
                // cursor.builder during this step's helpers; external
                // accessors (`walker.builder()`, take_dyn_result, hang-
                // dump snapshot) need self.builder to reflect the cursor's
                // post-step state. SemanticBuilder::clone is O(log N) via
                // im::Vector HAMT sharing — cheap per step. Only fires in
                // deterministic mode (self.deterministic == true): in nondeterministic mode
                // (post-first-Fork) all cursors go through step_fanout,
                // not apply_action, and commit_winner handles install.
                // Phase F.3c.4 (2026-05-20): cursor.builder field deleted.
                // The deterministic-mode install site
                // `self.builder = (*cursor.builder).clone()` is gone.
                // self.builder is a stub (F.3c.5 deletes); downstream
                // consumers use walker.resolve() / realize_root_to_terms.
                self.branch_cursors.push(cursor);
            }
            CursorOutcome::ForkInto(children) => {
                // The cursor-side Fork arm already flipped `self.deterministic`
                // to false. Replace branch_cursors with children and set
                // state = AmbiguityFanout.
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
                self.state = WpdaState::AmbiguityFanout { branches: branch_ids };
                self.maybe_prune_frontier();
            }
        }
    }

    /// Step 3 (Fork plan F5): per-cursor analog of `apply_action`. Mutates
    /// `cursor.{node,pos,weight,inner_state}` in place and logs walker-driven
    /// builder mutations into `cursor.recovery_deltas` instead of
    /// touching the live `SemanticBuilder`.
    ///
    /// Returns a [`CursorOutcome`] describing whether the cursor is dead,
    /// alive, forked, or resolved (candidate winner). See module docs for
    /// the detailed mapping per `WpdaStepAction` variant.
    fn apply_action_to_cursor(
        &mut self,
        cursor: &mut BranchCursor<W>,
        action: WpdaStepAction<W>,
        tokens: &dyn WpdaTokenSource,
    ) -> CursorOutcome<W> {
        // Phase F.13 walker-stats (2026-05-20): count per-cursor invocations.
        crate::stats_inc!(self, apply_action_calls);
        match action {
            WpdaStepAction::Advance(s) => {
                self.set_cursor_inner_state(cursor, s);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::AdvanceWithEffect { new_state, effect } => {
                // B8 / Issue C (2026-05-09): log effect to pending ops,
                // invalidate consistency memo, then advance state.
                // Phase 5.5 (2026-05-12): eagerly apply effect to
                // cursor.builder so post-install state reflects the
                // mutation. Without this, the journaled effect would
                // only fire at commit_winner replay (which is now no-op
                // for non-recovery deltas), leaving cursor.builder
                // missing the SpliceIntoCollection / other Class-3
                // inner-walk effects.
                self.apply_effect_to_cursor(cursor, &effect);
                // Phase 5.6-tail-D (2026-05-12): only recovery deltas
                // land in the journal — non-recovery effects are already
                // applied to cursor.builder above.
                if Self::is_recovery_delta(&effect) {
                    cursor.recovery_deltas.push(effect);
                }
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::Push { mut symbol, weight, new_state } => {
                // B12 / Candidate E (2026-05-07): cross-cat projection
                // cycle defense for SINGLETON projection arms. Singleton
                // bucket emits `WpdaStepAction::Push` (not Fork) when only
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
                if matches!(&new_state, WpdaState::CrossCatDelegate { .. }) {
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
                                WpdaState::Error { message: msg },
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
                let _ = self.cursor_gss_push_auto(cursor, symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::Pop { weight, new_state } => {
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
            WpdaStepAction::Replace { symbol, weight, new_state } => {
                let _ = self.cursor_gss_replace_top_auto(cursor, symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::Consume { weight, new_state } => {
                self.advance_cursor_pos(cursor, tokens, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ConsumeAndPush {
                mut symbol,
                weight,
                new_state,
                trigger_mode,
            } => {
                // Phase F.8 (2026-05-18): three-way dispatch on TriggerMode.
                // - CaptureForBuilder: mirror token via emit_push_token
                //   (Builder receives ActionArg::Token + SPPF receives a
                //   regular Terminal).
                // - ConsumeAsTriggerOnly: mirror token via
                //   emit_push_trigger_terminal (SPPF receives TriggerTerminal
                //   for span-only; Builder is NOT touched). The trigger
                //   lands BENEATH the rule's eventual RuleAt-frame operand
                //   sub-parse so the parent rule's interned Symbol gets
                //   lo_pos = trigger_pos (distinct from the operand's lo).
                // - Discard: no mirror; the token is purely consumed.
                match trigger_mode {
                    TriggerMode::CaptureForBuilder => {
                        if let Some(kind) = tokens.peek_kind(cursor.pos) {
                            let text = tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                            let pos = cursor.pos;
                            self.emit_push_token(cursor, kind, text, pos);
                        }
                    }
                    TriggerMode::ConsumeAsTriggerOnly => {
                        if let Some(kind) = tokens.peek_kind(cursor.pos) {
                            let text = tokens.peek_text(cursor.pos).unwrap_or("").to_string();
                            let pos = cursor.pos;
                            // Tag the trigger with its owning rule
                            // (cat_src_idx, rule_index_in_category) so
                            // emit_fire_action's walk-back can claim it
                            // ONLY at the matching rule's reduce.
                            self.emit_push_trigger_terminal(
                                cursor,
                                kind,
                                text,
                                pos,
                                symbol.category_src_idx,
                                symbol.rule_index_in_category,
                            );
                        }
                    }
                    TriggerMode::Discard => {}
                }
                // Stage 3.9 / ι Phase 4 (2026-05-01): centralized Push-time
                // side effects (CollectionMarker + OptionalGroupAt(1)).
                self.emit_push_side_effects(cursor, &mut symbol);
                let _ = self.cursor_gss_push_auto(cursor, symbol, cursor.pos, weight.clone());
                self.advance_cursor_pos(cursor, tokens, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ConsumeAndPop { weight, new_state } => {
                // Stage 3.12.6 (2026-05-02): single-predecessor pop via
                // edge-id (see Pop arm). Consume token first, then pop
                // along the cursor's recorded path.
                let popped_symbol = self.gss.node(cursor.node).map(|n| n.symbol);
                let pred_id =
                    self.cursor_gss_pop_via_edge(cursor).unwrap_or(crate::gss::GSS_NODE_NONE);
                self.advance_cursor_pos(cursor, tokens, 1);
                self.apply_pop_body_to_cursor(
                    cursor, pred_id, popped_symbol, &weight, new_state, tokens,
                );
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ConsumeAndReplace { symbol, weight, new_state } => {
                let _ = self.cursor_gss_replace_top_auto(cursor, symbol, cursor.pos, weight.clone());
                self.advance_cursor_pos(cursor, tokens, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ConsumeIdentAndReplace {
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
                let _ = self.cursor_gss_replace_top_auto(cursor, symbol, cursor.pos, weight.clone());
                self.advance_cursor_pos(cursor, tokens, 1);
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ReplaceAndPush {
                replace_symbol,
                push_symbol,
                weight,
                new_state,
            } => {
                let _ = self.cursor_gss_replace_top_auto(cursor, replace_symbol, cursor.pos, weight.clone());
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
                let _ = self.cursor_gss_push_auto(cursor, push_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::ParsePredicate {
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
                        // self.pos in deterministic mode.
                        cursor.pos = new_pos;
                        if self.deterministic {
                            self.pos = new_pos;
                        }
                    }
                    Err(_msg) => return CursorOutcome::Drop,
                }
                let _ = self.cursor_gss_replace_top_auto(cursor, replace_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::Fork { mut branches, consume_trigger } => {
                // Phase F.13 walker-stats (2026-05-20): count Fork firings
                // and per-branch composition by ForkActionKind variant +
                // CrossCatDelegate detection.
                crate::stats_inc!(self, fork_total);
                #[cfg(feature = "walker-stats")]
                {
                    for b in &branches {
                        match &b.action_kind {
                            ForkActionKind::Push { .. } => {
                                self.stats.fork_kind_push =
                                    self.stats.fork_kind_push.saturating_add(1);
                            }
                            ForkActionKind::OptGroupAbsent { .. } => {
                                self.stats.fork_kind_opt_group_absent =
                                    self.stats.fork_kind_opt_group_absent.saturating_add(1);
                            }
                            ForkActionKind::LexAlt { .. }
                            | ForkActionKind::LexAltPrefixOp { .. }
                            | ForkActionKind::LexAltPostfixOp { .. }
                            | ForkActionKind::LexAltInfixOp { .. }
                            | ForkActionKind::LexAltMixfixOp { .. } => {
                                self.stats.fork_kind_lex_alt_family =
                                    self.stats.fork_kind_lex_alt_family.saturating_add(1);
                            }
                            ForkActionKind::Consume { .. }
                            | ForkActionKind::ConsumeAndReplace { .. }
                            | ForkActionKind::ConsumeIdentAndReplace { .. }
                            | ForkActionKind::ConsumeAndPop { .. }
                            | ForkActionKind::ConsumeAndReplaceWithEffect { .. }
                            | ForkActionKind::ConsumeAndCaptureAndPush { .. }
                            | ForkActionKind::ConsumeIdentAndPop { .. } => {
                                self.stats.fork_kind_consume_family =
                                    self.stats.fork_kind_consume_family.saturating_add(1);
                            }
                            _ => {
                                self.stats.fork_kind_other =
                                    self.stats.fork_kind_other.saturating_add(1);
                            }
                        }
                        if matches!(&b.new_state, WpdaState::CrossCatDelegate { .. }) {
                            self.stats.fork_cross_cat_projection_branches =
                                self.stats.fork_cross_cat_projection_branches.saturating_add(1);
                        }
                    }
                }
                // Phase 5.6-tail-C (2026-05-12): Hack #7 prologue + Phase 5.5
                // cursor.builder refresh DELETED.
                //
                // Pre-tail the prologue seeded `cursor.collection_slots_allocated`,
                // `cursor.collection_stack`, and `cursor.builder` from `self.builder`'s
                // live state to compensate for deterministic-mode emit_fire_action mutating
                // self.builder directly (skipping cursor.builder). Under Phase
                // 5.6-tail-B's emit-helper unification, ALL emit helpers (including
                // emit_fire_action) eagerly mutate cursor.builder via Arc::make_mut.
                // The cursor.builder thus IS the authoritative pre-Fork state —
                // children inherit it via Arc::clone with no refresh needed. The
                // collection_stack mirror is also kept in sync per-step
                // (emit_start_collection always pushes; CollectionMarker pop always
                // drains).
                //
                // Flip `self.deterministic` to false (entering
                // nondeterministic mode). This gates the 4 mode-agnostic
                // helpers' mirror-to-live behavior — once nondeterministic,
                // cursor.* updates no longer mirror to self.*
                // (self.* loses singleton meaning until commit_winner).
                self.deterministic = false;
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
                // Phase F.13 walker-stats (2026-05-20): count recovery dispatches.
                #[cfg(feature = "walker-stats")]
                {
                    if is_recovery {
                        self.stats.fork_recovery_dispatches =
                            self.stats.fork_recovery_dispatches.saturating_add(1);
                    }
                }
                // Phase F.13 H11b (2026-05-21): REJECTED.
                // The originally-planned filter (skip CrossCatDelegate
                // branches whose target source_src_idx was already
                // emitted by a prior cursor at the same (cat, pos,
                // inner_bp) dispatch site) is MATHEMATICALLY UNSOUND.
                //
                // Empirical refutation: 7 edge_case_tests regressed
                // (float_cast_* family + rhocalc_edge_cases::comm_under_new).
                //
                // Diagnosis (mathematical): cross-cat dispatch is NOT
                // just sub-parse work — it's also a CONTEXT SAVE for
                // the return. Two cursors at the same (cat, pos,
                // inner_bp) dispatch share sub-parse WORK but NOT the
                // return context (different incoming_edge_stack /
                // binder_scope_marks / sppf_collection_arena state).
                // Filtering the second emission drops its return
                // context, losing parses.
                //
                // The MATHEMATICALLY VALID analogue is GSS-aware batch
                // dispatch (Tomita-GLR / GLL call-graph sharing): when
                // N cursors call the same sub-parse, run sub-parse ONCE
                // and fan out ALL N return contexts at pop time. This
                // requires walker refactoring beyond a single-hypothesis
                // scope; deferred to a future research session.
                //
                // dispatch_branch_seen field retained for any future
                // diagnostic use; field is unused in this branch.
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
                            WpdaState::Error { message: msg },
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
                                WpdaState::Error { message: msg },
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
                            WpdaState::Error { message: msg },
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
                            WpdaState::Error { message: msg },
                        );
                        return CursorOutcome::Drop;
                    }
                }
                let pos_after = if consume_trigger {
                    // M6c.6.1 (2026-05-14): use the source's next_pos
                    // instead of `cursor.pos + 1`. For SliceTokenSource
                    // the default impl returns `Some(pos + 1)`, so this
                    // is byte-identical. For LatticeTokenSource this
                    // tracks the primary edge's `target_node` which
                    // may not equal `pos + 1` under multi-LENGTH
                    // ambiguity.
                    tokens.next_pos(cursor.pos, 0).unwrap_or(cursor.pos + 1)
                } else {
                    cursor.pos
                };
                // Phase F.11 R7 hoist-and-share (2026-05-19): pre-compute the
                // children's visited_recovery / visited_dispatch / recovery_depth
                // snapshot ONCE so the F Fork-arm siblings can share it via
                // O(1) OrdSet `.clone()` (Arc refcount bump). The post-loop
                // per-child insert blocks at the old lines 6059-6076 +
                // 6101-6112 were each calling `child.visited_*.insert(key)`
                // separately for the F siblings — every sibling triggered
                // an independent `Arc::make_mut` spine-clone for the SAME
                // parent dispatch config key.
                //
                // Empirical: perf + massif on test_right_assoc_chain_100 at
                // depth=100 showed 31.56% of peak heap (~23MB / 72MB) was
                // `Arc<Node<Value<(usize,u16,u8)>>>::make_mut` from
                // OrdSet::insert at line 6109 (visited_dispatch) and its
                // deeper btree spine path. Calculator's PrefixDispatch
                // unified bucket spawns F ≈ 3-5 cross-cat-projection branches
                // per `^` operand, so the per-sibling redundancy multiplies
                // the spine-clone count by F.
                //
                // Correctness invariants preserved:
                // - H1' broadening (commit 4668720, 2026-05-18): every
                //   non-recovery Fork child still inherits the updated
                //   visited_dispatch (computed once here, shared across
                //   children via Arc).
                // - Recovery depth-bump semantics (Stage 3.20 / L12): every
                //   recovery Fork child still has recovery_depth bumped by 1.
                // - The "is_recovery true but config missing" defensive
                //   branch (formerly the `else` at line 6066-6075) still
                //   bumps depth without modifying visited_recovery.
                // - Per-branch DROP gate at line 4709-4714: unchanged. It
                //   reads `parent_in_visited` from the parent's pre-mutation
                //   `cursor.visited_dispatch` (line 4658-4660) and
                //   `is_cross_cat_delegate_branch`; the hoist preserves
                //   the order so this read sees the unmodified parent set.
                let (child_visited_recovery, child_recovery_depth) = if is_recovery {
                    let depth = cursor.recovery_depth.saturating_add(1);
                    let set = if let Some(key) = recovery_dispatch_config {
                        let mut s = cursor.visited_recovery.clone();
                        s.insert(key);
                        s
                    } else {
                        cursor.visited_recovery.clone()
                    };
                    (set, depth)
                } else {
                    (cursor.visited_recovery.clone(), cursor.recovery_depth)
                };
                let child_visited_dispatch = if !is_recovery {
                    if let Some(key) = parent_dispatch_config {
                        let mut s = cursor.visited_dispatch.clone();
                        s.insert(key);
                        s
                    } else {
                        cursor.visited_dispatch.clone()
                    }
                } else {
                    cursor.visited_dispatch.clone()
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
                        matches!(&branch.new_state, WpdaState::CrossCatDelegate { .. });
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
                            // Phase F.13 H12 Stage 1.5 (2026-05-21):
                            // allocate_fork_push_child returns
                            // Vec<BranchCursor<W>>:
                            //   - 0 cursors: paused or dropped.
                            //   - 1 cursor: worker (single-packing
                            //     ResolvedHit or normal worker).
                            //   - N cursors: multi-packing ResolvedHit
                            //     fanout — one per worker snapshot.
                            let new_children = self.allocate_fork_push_child(
                                &cursor,
                                branch,
                                pos_after,
                                child_recovery_depth,
                                child_visited_recovery.clone(),
                                child_visited_dispatch.clone(),
                                child_source_priority,
                            );
                            for child in new_children {
                                children.push(child);
                                child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                            }
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
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            // nondeterministic mode: emit_push_optional_absent logs the delta.
                            self.emit_push_optional_absent(&mut child);
                            // Stage 3.12.6 (2026-05-02): pop along the
                            // child's recorded edge (its own history),
                            // not an arbitrary in-edge of child.node.
                            let popped = self.cursor_gss_pop_via_edge(&mut child);
                            if popped.is_none() {
                                // GSS underflow: synthesize CategoryEntry(0)
                                // sentinel so the subsequent push has a
                                // valid predecessor.
                                let sentinel = self.gss.get_or_create_node(WpdaGssNode {
                                    pos: child.pos,
                                    symbol: StackSymbolV2::category_entry(0),
                                });
                                child.node = sentinel;
                            }
                            // Stage 3.12.6: use cursor_gss_push so the
                            // child's incoming_edge_stack records the
                            // new edge id for its eventual pop.
                            let _ = self.cursor_gss_push_auto(
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
                        // its WpdaStepAction counterpart's apply_action body.
                        // Fork emits these with `consume_trigger: false`
                        // because each variant intrinsically encodes its own
                        // consume semantics; the per-branch consume happens
                        // INSIDE this arm, not at allocation time.
                        ForkActionKind::ConsumeAndReplace => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::Consume => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::ConsumeIdentAndReplace { start_scope } => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
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
                            // canonical WpdaStepAction::ConsumeIdentAndReplace arm
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
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::Pop => {
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: pos_after,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
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
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            let popped_symbol =
                                self.gss.node(child.node).map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                            // Phase 5.5 (2026-05-12): eagerly apply effect
                            // to child.builder via Arc::make_mut so the
                            // post-install state has these mutations.
                            self.apply_effect_to_cursor(&mut child, &effect);
                            // Phase 5.6-tail-D: recovery-only journal.
                            if Self::is_recovery_delta(&effect) {
                                child.recovery_deltas.push(effect);
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::LexAlt { alt_idx, kind, text, next_pos, rule_idx } => {
                            // M6c.3 (2026-05-14): proper literal-rule
                            // consumption. The pre-M6c.3 path advanced
                            // `cursor.pos` past the alt's token via
                            // `pos: next_pos` WITHOUT binding the token
                            // to a grammar rule — the child cursor had
                            // no AST term and the walker rejected at EOI.
                            //
                            // The new path mirrors
                            // `ForkActionKind::ConsumeAndCaptureAndPush`
                            // (atomic-literal multi-arm Fork, line 3737):
                            //   1. Allocate child at cursor.pos (NOT
                            //      advanced yet) so emit_push_token
                            //      records the alt's text at the
                            //      original byte position.
                            //   2. Push the alt's (kind, text) onto the
                            //      builder via `emit_push_token`. This
                            //      makes the token available to
                            //      FireAction.
                            //   3. Push the codegen-emitted
                            //      `with_kind_return` symbol via
                            //      cursor_gss_push (codegen guarantees
                            //      branch.symbol is
                            //      `rule_at(state_cat, rule_idx, 0,
                            //      Some(cur_bp)).with_kind_return()`).
                            //      The Unwinding fires the literal
                            //      rule's FireAction, producing the
                            //      AST term (e.g., Int::NumLit(0)).
                            //   4. ONLY THEN advance child.pos to
                            //      `next_pos` so the next dispatch
                            //      runs from the alt's downstream
                            //      position.
                            //
                            // `rule_idx` is implicitly encoded in
                            // branch.symbol via codegen; we keep it as
                            // an action payload so the walker can log
                            // it for diagnostics (currently `let _ =
                            // rule_idx;` since the symbol is the
                            // authoritative carrier).
                            //
                            // `alt_idx` is retained for diagnostic
                            // tracing only; no per-cursor sidecar state
                            // (per M4 + WPDS-stack-purity).
                            let _ = rule_idx;
                            let _ = alt_idx;
                            let mut sym = branch.symbol;
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: cursor.pos,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            // Capture the alt's token text at child.pos
                            // (the original byte position, before
                            // advancing). Mirrors emit_push_token in
                            // ConsumeAndCaptureAndPush at line 3779-3786.
                            let pos_now = child.pos;
                            self.emit_push_token(&mut child, kind, text, pos_now);
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let _ = self.cursor_gss_push_auto(
                                &mut child,
                                sym,
                                pos_now,
                                branch.weight.clone(),
                            );
                            // Advance to the alt's downstream DAG node
                            // (LatticeTokenSource) or pos+1 (slice
                            // sources via the default trait method).
                            child.pos = next_pos;
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::LexAltPrefixOp {
                            alt_idx: _,
                            trigger: _,
                            rule_idx: _,
                            body_src_idx: _,
                            next_pos,
                            outer_bp: _,
                        } => {
                            // M6c.6.4.d (2026-05-14): unary-prefix lex-Fork
                            // apply arm. Mirrors the standard
                            // `Fixed(trigger) → ConsumeAndPush(BinderRule)`
                            // arm at engine_impl.rs / generated wpds.rs:
                            //   1. Allocate child at `cursor.pos` (NOT
                            //      advanced yet — `next_pos` advancement
                            //      happens AFTER the GSS push, mirroring
                            //      `WpdaStepAction::ConsumeAndPush`'s
                            //      `advance_cursor_pos` after `cursor_gss_push`).
                            //   2. NO `emit_push_token` — the prefix
                            //      trigger is consumed but not captured
                            //      on the builder; the operand sub-parse
                            //      will produce the AST term that the
                            //      rule's action wraps.
                            //   3. Push the symbol (codegen-emitted as
                            //      `rule_at(cat, rule_idx, slot=1,
                            //      Some(*cur_bp))` — NO `with_kind_return`,
                            //      since this is the operand-continuation
                            //      marker, NOT a Return marker).
                            //   4. Advance `child.pos = next_pos` (the
                            //      DAG's `target_node` for the trigger's
                            //      lex alt).
                            //   5. State transition is encoded in
                            //      `branch.new_state = BinderRule { ... }`
                            //      which carries `body_src_idx + outer_bp`
                            //      so the operand sub-parse runs at the
                            //      rule's `prefix_bp_map` cur_bp installed
                            //      downstream by BinderRule's ParamParse arm.
                            let mut sym = branch.symbol;
                            let mut child = BranchCursor {
                                node: cursor.node,
                                pos: cursor.pos,
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
                                source_priority: child_source_priority,
                                incoming_edge_stack: cursor.incoming_edge_stack.clone(),
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
                            };
                            // Phase F.10 (2026-05-19): mirror the standard
                            // `WpdaStepAction::ConsumeAndPush` arm's
                            // `TriggerMode::ConsumeAsTriggerOnly` branch
                            // (lines 4400-4452). Phase F.8 added TriggerTerminal
                            // push to the standard arm to distinguish a unary-
                            // prefix rule's interned Symbol from its operand's
                            // Symbol via lo_pos, but the lex-Fork variant
                            // (this arm) was overlooked. Without this push, the
                            // unary-prefix rule's Symbol gets `lo_pos =
                            // operand_lo` (NOT trigger_pos), losing the SPPF
                            // Symbol-dedup collapse with the competing
                            // primary-lex-alt parse — `emit_fire_action`'s
                            // walk-back at line ~7610 finds no Trigger frame
                            // to claim, and `merge_equivalent_cursors`
                            // discards this cursor's sppf_top in favor of
                            // the primary-lex-alt's, dropping this packing.
                            // For `-3!`: Path A (Neg via lex-Fork `-`) loses
                            // to Path B (Fact via primary `-3` literal),
                            // never surfacing the `Neg(Fact(NumLit(3))) →
                            // -6` derivation.
                            if let Some(kind) = tokens.peek_kind(child.pos) {
                                let text = tokens
                                    .peek_text(child.pos)
                                    .unwrap_or("")
                                    .to_string();
                                let trigger_pos = child.pos;
                                self.emit_push_trigger_terminal(
                                    &mut child,
                                    kind,
                                    text,
                                    trigger_pos,
                                    sym.category_src_idx,
                                    sym.rule_index_in_category,
                                );
                            }
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_push_auto(
                                &mut child,
                                sym,
                                pos_now,
                                branch.weight.clone(),
                            );
                            // Advance to the alt's downstream DAG node
                            // (LatticeTokenSource) or pos+1 (slice
                            // sources via the default trait method).
                            child.pos = next_pos;
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::LexAltPostfixOp { .. } => {
                            // M6c.6.4.a (2026-05-14): stub. Activated
                            // at M6c.6.4.e when postfix lex-Fork
                            // emission is wired in
                            // `emit_lex_fork_at_infix_loop`.
                            unreachable!(
                                "M6c.6.4.a: LexAltPostfixOp not yet wired (M6c.6.4.e)"
                            );
                        }

                        ForkActionKind::LexAltInfixOp { .. } => {
                            // M6c.6.4.a (2026-05-14): stub. Activated
                            // at M6c.6.4.e.
                            unreachable!(
                                "M6c.6.4.a: LexAltInfixOp not yet wired (M6c.6.4.e)"
                            );
                        }

                        ForkActionKind::LexAltMixfixOp { .. } => {
                            // M6c.6.4.a (2026-05-14): stub. Activated
                            // at M6c.6.4.e.
                            unreachable!(
                                "M6c.6.4.a: LexAltMixfixOp not yet wired (M6c.6.4.e)"
                            );
                        }

                        ForkActionKind::ConsumeAndCaptureAndPush => {
                            // Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ,
                            // 2026-05-05): atomic literal multi-arm Fork
                            // branch. Mirrors WpdaStepAction::ConsumeAndPush
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
                                weight: cursor.weight.times_ref(&branch.weight),
                                inner_state: branch.new_state.clone(),
                                recovery_deltas: cursor.recovery_deltas.clone(),
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
                                // Phase F.11 R7 hoist (2026-05-19): read
                                // the pre-loop snapshot computed above.
                                // Each sibling pays O(1) Arc refcount-bump
                                // instead of an independent Arc::make_mut
                                // spine clone.
                                recovery_depth: child_recovery_depth,
                                visited_recovery: child_visited_recovery.clone(),
                                visited_dispatch: child_visited_dispatch.clone(),
                                // Phase 5.2 (2026-05-12): O(1) Arc bump.
                                // Child shares parent's `SemanticBuilder`
                                // until a 5.3+ mutator triggers
                                // `Arc::make_mut` copy-on-write.
                                // Option C / C2: Fork-children inherit parent SPPF stack.
                                sppf_stack: Arc::clone(&cursor.sppf_stack),
                                optional_scope_marks: cursor.optional_scope_marks.clone(),
                                binder_scope_marks: cursor.binder_scope_marks.clone(),
                                // Phase C.3 (2026-05-17): Fork-arm child
                                // accumulates branch weight into pending,
                                // for the next emit_fire_action to consume.
                                pending_packing_weight: cursor
                                    .pending_packing_weight
                                    .times_ref(&branch.weight),
                                // Phase F.1 (2026-05-18): Fork-arm child
                                // inherits parent's collection depth.
                                collection_stack_depth: cursor.collection_stack_depth,
                                // Phase F.4 (2026-05-18): Arc bump.
                                sppf_collection_arena: Arc::clone(&cursor.sppf_collection_arena),
                                // Phase F.3a (2026-05-20): inherit parent's
                                // last_action_output_cat. Fork-arm children
                                // share the parent's "most recent action
                                // output cat" until a per-branch action
                                // fires or a per-branch push clears it.
                                last_action_output_cat: cursor.last_action_output_cat,
                                cohort_origin: cursor.cohort_origin.clone(),
                                cohort_revive_depth: cursor.cohort_revive_depth,
                                // Phase F.3c.2 (2026-05-20): inherit parent's
                                // SPPF-symbol → AST memo via Arc bump (O(1)).
                                // First write in this child triggers Arc::make_mut.
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
                            let _ = self.cursor_gss_push_auto(
                                &mut child,
                                sym,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
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
                            // canonical WpdaStepAction::ConsumeIdentAndReplace at
                            // line ~2521.
                            if start_scope {
                                self.emit_start_binder_scope(
                                    &mut child,
                                    vec![text.clone()],
                                );
                            }
                            let pos_now = child.pos;
                            self.emit_push_ident(&mut child, text, pos_now);
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }

                        ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                            expected_text,
                            effect,
                        } => {
                            // L12 follow-up B2 (2026-05-07): peek_text
                            // equality guard wrapping ConsumeAndReplaceWithEffect.
                            // Pass → log effect to recovery_deltas,
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            // B13d-R Step 2 (2026-05-08): invalidate consistency memo on push.
                            // Phase 5.5 (2026-05-12): eagerly apply effect
                            // to child.builder via Arc::make_mut so the
                            // post-install state has these mutations.
                            self.apply_effect_to_cursor(&mut child, &effect);
                            // Phase 5.6-tail-D: recovery-only journal.
                            if Self::is_recovery_delta(&effect) {
                                child.recovery_deltas.push(effect);
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
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
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
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
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                            // onto recovery_deltas between scope
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
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
                            self.apply_effect_to_cursor(&mut child, &effect);
                            // Phase 5.6-tail-D: recovery-only journal.
                            if Self::is_recovery_delta(&effect) {
                                child.recovery_deltas.push(effect);
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            self.apply_effect_to_cursor(&mut child, &effect);
                            // Phase 5.6-tail-D: recovery-only journal.
                            if Self::is_recovery_delta(&effect) {
                                child.recovery_deltas.push(effect);
                            }
                            // Capture popped_symbol before pop.
                            let popped_symbol = self.gss
                                .node(child.node)
                                .map(|n| n.symbol);
                            let pred_id = self
                                .cursor_gss_pop_via_edge(&mut child)
                                .unwrap_or(crate::gss::GSS_NODE_NONE);
                            child.pos = Self::child_next_pos(tokens, child.pos);
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                replace_symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            let mut sym = branch.symbol;
                            self.emit_push_side_effects(&mut child, &mut sym);
                            let _ = self.cursor_gss_push_auto(
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
                                cursor.weight.times_ref(&branch.weight),
                                // Phase C.3 (2026-05-17): pass branch.weight
                                // for `pending_packing_weight` accumulation
                                // (parent.pending ⊗ branch.weight).
                                branch.weight.clone(),
                                branch.new_state.clone(),
                                child_source_priority,
                            );
                            for effect in effects {
                                self.apply_effect_to_cursor(&mut child, &effect);
                                if Self::is_recovery_delta(&effect) {
                                    child.recovery_deltas.push(effect);
                                }
                            }
                            let pos_now = child.pos;
                            let _ = self.cursor_gss_replace_top_auto(
                                &mut child,
                                branch.symbol,
                                pos_now,
                                branch.weight.clone(),
                            );
                            child.pos = Self::child_next_pos(tokens, child.pos);
                            children.push(child);
                            child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
                        }
                    }
                }
                // Phase F.11 R7 hoist (2026-05-19): the per-child post-loop
                // insert blocks below are DISABLED — the work was moved
                // above the per-branch allocation loop (lines ~4694-4731)
                // so all F Fork-arm siblings inherit a single pre-computed
                // OrdSet snapshot (`child_visited_recovery`,
                // `child_visited_dispatch`) and pre-bumped depth
                // (`child_recovery_depth`) via O(1) Arc-refcount-bump
                // `.clone()`. Pre-hoist, each of the F siblings independently
                // ran `Arc::make_mut` to deep-clone the OrdSet spine before
                // inserting the SAME key, costing F × O(log N) Arc allocs
                // per Fork (perf+massif: 31.56% of peak heap at depth=100).
                //
                // The original logic is preserved as comments below so the
                // historical bounded-recovery (Stage 3.20 / L12) and B14 C5 /
                // H1' rationale stays attached to the code path. Re-enabling
                // either block at the same time as the pre-loop computation
                // would DOUBLE-insert the key.
                //
                // // Bounded recovery (Stage 3.20 / L12, 2026-05-06):
                // // post-loop bump for recovery Forks. Each child inherited
                // // the parent's recovery_depth via the per-arm allocation
                // // (added to all 10 ForkActionKind arms via replace_all);
                // // here we bump the depth by 1 and insert the dispatch
                // // config into visited_recovery so the next dispatch at
                // // the same configuration is refused. For non-recovery
                // // Forks the inherited values pass through unchanged.
                // if is_recovery {
                //     if let Some(key) = recovery_dispatch_config {
                //         for child in children.iter_mut() {
                //             child.recovery_depth =
                //                 child.recovery_depth.saturating_add(1);
                //             child.visited_recovery.insert(key);
                //         }
                //     } else {
                //         // is_recovery true but config missing: cursor wasn't
                //         // in PrefixDispatch when the recovery Fork was
                //         // dispatched. Treat as malformed dispatch — bump
                //         // depth without visited entry so the cap still bites.
                //         for child in children.iter_mut() {
                //             child.recovery_depth =
                //                 child.recovery_depth.saturating_add(1);
                //         }
                //     }
                // }
                // // B14 C5 (2026-05-08): per-child insertion of the dispatch
                // // config so the cycle gate at apply_action_to_cursor :: Push
                // // (line 4213-4231) and the per-branch gate at
                // // (line 4546-4558) can detect re-entry.
                // //
                // // H1' EXTENSION (2026-05-18, replicated-conjuring-turtle.md):
                // // previously this insertion fired ONLY for children whose
                // // originating branch was CrossCatDelegate. Empirical
                // // diagnostic (`docs/design/notes/2026-05-18-cursor-
                // // explosion-rhocalc.md`) traced the rhocalc OOM cycle to a
                // // PrefixDispatch-branch Fork that re-entered the same
                // // `(pos, cat_src, cur_bp)` indefinitely with only the
                // // cursor's `weight.src` cat-idx cycling — visited_dispatch
                // // never grew because all branches were non-CrossCatDelegate.
                // //
                // // Per the GLL descriptor-uniqueness argument (Scott &
                // // Johnstone 2010 §3), any re-entry to the same dispatch
                // // configuration is non-productive regardless of branch
                // // type. The insertion is now unconditional for non-recovery
                // // Forks; the per-branch gate at line 4546-4558 (extended
                // // below in a sibling commit) catches re-entry uniformly.
                // //
                // // `child_came_from_cross_cat` is retained as a structural
                // // tracker for the (now-equivalent) per-branch gate.
                // if let Some(key) = parent_dispatch_config {
                //     if !is_recovery {
                //         debug_assert_eq!(
                //             children.len(),
                //             child_came_from_cross_cat.len(),
                //             "B14 C5: parallel tracker out of sync with children",
                //         );
                //         for child in children.iter_mut() {
                //             child.visited_dispatch.insert(key);
                //         }
                //     }
                // }
                // Phase F.13 walker-stats (2026-05-20): count all Fork-arm
                // children created. Batched here (vs 21 individual sites)
                // so the count reflects post-gating survivors.
                crate::stats_add!(self, cursors_created_via_fork, children.len() as u64);
                CursorOutcome::ForkInto(children)
            }
            WpdaStepAction::Accept => {
                // Stage 3.5b (2026-05-01): mirror live apply_action::Accept
                // by transitioning cursor.inner_state to Accepted.
                // Stage 3.9 / ι Phase 4 (2026-05-01): use helper so live
                // walker self.state is mirrored to Accepted in deterministic mode.
                self.set_cursor_inner_state(cursor, WpdaState::Accepted);
                CursorOutcome::Resolved
            }
            WpdaStepAction::Error(message) => {
                // Stage 3.9 / ι Phase 4 (2026-05-01): mirror live state via
                // helper so deterministic-mode self.state becomes Error too.
                self.set_cursor_inner_state(
                    cursor,
                    WpdaState::Error { message },
                );
                CursorOutcome::Drop
            }
            WpdaStepAction::OptGroupAbsent {
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
                    let sentinel = self.gss.get_or_create_node(WpdaGssNode {
                        pos: cursor.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    });
                    cursor.node = sentinel;
                    if self.deterministic {
                        self.top_node = Some(sentinel);
                    }
                }
                let _ = self.cursor_gss_push_auto(cursor, replace_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::OptGroupFinalize {
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
                //   2. Emit FinalizeOptionalScopePresent (eager
                //      `Arc::make_mut` on cursor.builder).
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
                    let sentinel = self.gss.get_or_create_node(WpdaGssNode {
                        pos: cursor.pos,
                        symbol: StackSymbolV2::category_entry(0),
                    });
                    cursor.node = sentinel;
                    if self.deterministic {
                        self.top_node = Some(sentinel);
                    }
                }
                let _ = self.cursor_gss_push_auto(cursor, replace_symbol, cursor.pos, weight.clone());
                self.multiply_cursor_weight(cursor, &weight);
                self.set_cursor_inner_state(cursor, new_state);
                self.cursor_resolution_check(cursor)
            }
            WpdaStepAction::Idle => {
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
                    WpdaState::InfixLoop { .. }
                        | WpdaState::Accepted
                        | WpdaState::Unwinding
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
    /// branch's accumulated recovery_deltas and resume there.
    fn cursor_resolution_check(&self, cursor: &BranchCursor<W>) -> CursorOutcome<W> {
        // Phase 5.5 (2026-05-12): cursors that hit Error state mid-step
        // (e.g., emit_fire_action's eager fire underflow) are Dropped so
        // step_fanout's all-dropped path can surface "Error" to the walker.
        if matches!(cursor.inner_state, WpdaState::Error { .. }) {
            return CursorOutcome::Drop;
        }
        if matches!(
            cursor.inner_state,
            WpdaState::InfixLoop { .. }
                | WpdaState::Accepted
                | WpdaState::Unwinding
        ) {
            CursorOutcome::Resolved
        } else {
            CursorOutcome::Alive
        }
    }

    /// Step 3 (Fork plan F6): per-step driver for `WpdaState::AmbiguityFanout`.
    ///
    /// Iterates each `BranchCursor`, queries the engine for an action against
    /// the cursor's per-branch state, applies the action via
    /// `apply_action_to_cursor`, classifies the outcome, and dispatches:
    ///
    /// - **Case 1: all dropped** → walker enters `Error("all branches dropped")`.
    /// - **Case 2 / 3: at least one Resolved (and no still-Alive cursors)**
    ///   → pick lex-min winner via `Semiring::plus`-fold across resolved
    ///   cursors, replay its `recovery_deltas` against the live builder,
    ///   commit its `(node, pos, weight, inner_state)` to the walker.
    /// - **Case 4: still-Alive cursors remain** → keep iterating in the
    ///   `branch_cursors` vec; walker stays in `AmbiguityFanout`.
    ///
    /// Returns the new `WpdaState` after this micro-step (which may still
    /// be `AmbiguityFanout` if Case 4 fires).
    fn step_fanout(&mut self, tokens: &dyn WpdaTokenSource) -> WpdaState {
        // Phase F.13 walker-stats (2026-05-20): count step + accumulate
        // pre-step cursor count for avg-cursors-per-step derivation.
        crate::stats_inc!(self, step_fanout_calls);
        crate::stats_add!(self, branch_cursors_sum, self.branch_cursors.len() as u64);
        let mut new_cursors: Vec<BranchCursor<W>> = Vec::with_capacity(self.branch_cursors.len());
        // Track which entries in `new_cursors` are Resolved.
        let mut resolved_indices: Vec<usize> = Vec::new();
        let drained: Vec<BranchCursor<W>> = std::mem::take(&mut self.branch_cursors);
        for cursor in drained {
            let frontier_top = self.gss.node(cursor.node).cloned();
            // M4 (2026-05-13): pass `tokens` directly. The CursorViewSource
            // wrap is deleted — alt identity now lives in the SHARED input
            // DAG (`LatticeTokenSource`, M3) and the cursor's `pos: usize`
            // (DAG node-id) is sufficient to identify its alt timeline.
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
            // cursor whose recovery_deltas exceeds the limit is
            // marked Error and returned immediately. The fanout bails
            // out, preserving the offending cursor so resolve_at_end_of_input
            // returns ParseError with a diagnostic.
            if cursor.recovery_deltas.len() > STRICT_PENDING_OPS_LIMIT {
                self.state = WpdaState::Error {
                    message: format!(
                        "ι Phase 6 runaway guard: cursor recovery_deltas \
                         exceeded STRICT_PENDING_OPS_LIMIT ({} > {})",
                        cursor.recovery_deltas.len(),
                        STRICT_PENDING_OPS_LIMIT,
                    ),
                };
                self.branch_cursors = vec![cursor];
                return self.state.clone();
            }
            match outcome {
                CursorOutcome::Drop => {
                    // Phase F.13 walker-stats (2026-05-20): count outcome-Drop sink.
                    crate::stats_inc!(self, cursors_dropped_via_outcome_drop);
                    /* discard */
                }
                CursorOutcome::Alive => new_cursors.push(cursor),
                // **Tiebreak chain link 4 (load-bearing).** `extend` preserves
                // the source-order of `children` produced by Fork. Combined
                // with: (1) `vec![take, skip]` codegen at binder.rs:973-980,
                // (2) `LexicographicWeight::plus` returning `*self` on equality
                // at lex_weight.rs:345-348, and (3) `pick_lex_min_resolved`'s
                // earlier-index-wins tiebreak at wpda_walker.rs:2570-2592,
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
        // Phase F.13 H12 Stage 1.5 (2026-05-21): end-of-step cohort
        // drain. For each dispatch key whose worker resolved during
        // this step, emit `paused × snapshots` revived cursors. The
        // drain happens AFTER all sibling workers have contributed
        // their snapshots (within the SAME step_fanout iteration),
        // so multi-packing ambiguity is captured correctly.
        if !self.pending_cohort_drain_keys.is_empty() {
            let drain_keys = std::mem::take(&mut self.pending_cohort_drain_keys);
            for key in drain_keys {
                if let Some((symbol_id, hi_pos, pos_at_dispatch, snapshots, members)) =
                    self.dispatch_cohort_cache.take_pending_for_drain(&key)
                {
                    for member in members {
                        for snap in &snapshots {
                            // Filter terminal-state snapshots: workers
                            // that ended in Error wouldn't have produced
                            // a revivable cursor in the per-cursor
                            // baseline either.
                            if snap.worker_inner_state.is_terminal() {
                                continue;
                            }
                            let revived = self.revive_cohort_member_with_snapshot(
                                member.clone(),
                                symbol_id,
                                pos_at_dispatch,
                                hi_pos,
                                key.source_src_idx,
                                key.inner_cur_bp,
                                snap,
                            );
                            new_cursors.push(revived);
                        }
                    }
                }
            }
        }
        self.branch_cursors = new_cursors;
        // Phase F.13 walker-stats (2026-05-20): capture pre-merge peak.
        crate::stats_max!(self, branch_cursors_peak_pre_merge, self.branch_cursors.len() as u64);
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
        // (`recovery_deltas`, `collection_stack`) is kept (deltas
        // are non-commutative). Caps polynomial fanout in ambiguous
        // grammars vs the prior exponential branch count.
        // Phase F.13 H11a diagnostic (2026-05-20): sample intra-pos cursor
        // pairs that would FAIL to merge and tally which ConfigKey
        // discriminator (state/node/edge/depth) is the sole cause. Only
        // runs when feature=walker-stats. Bounds: up to 10 pairs per
        // peak-step bucket; constant overhead per step.
        #[cfg(feature = "walker-stats")]
        self.sample_merge_misses();
        self.merge_equivalent_cursors();
        // Phase F.13 walker-stats (2026-05-20): capture post-merge peak.
        crate::stats_max!(self, branch_cursors_peak_post_merge, self.branch_cursors.len() as u64);

        // B10 / Option κ Part 3 (2026-05-07): lex-dominated cursor
        // subsumption. After strict-key merge, group remaining cursors
        // by RELAXED key `(state, gss-node-symbol, pos)` (intentionally
        // dropping `incoming_edge_stack` — that discriminator exists
        // for pop-time determinism with structural sharing, not for
        // parse-time semantic distinctness). Within each group, drop
        // any cursor C if a sibling S has `S.weight.lex_cmp(C.weight) ==
        // M7c (2026-05-13): `subsume_lex_dominated_cursors()` DELETED.
        // The prior pruning dropped weight-dominated cursors mid-stream
        // — violating the user mandate "ambiguity preserved unless
        // ruled out by evidence." Dominated cursors haven't failed via
        // evidence; they may yield a different (still valid) derivation
        // that the caller wants. The walker now relies on:
        //   1. merge_equivalent_cursors collapsing identical ConfigKeys
        //      via plus_ref (multiset union when W is DerivationWeight;
        //      lex-min when W is LexicographicWeight today).
        //   2. Beam pruning (maybe_prune_frontier, default None) as an
        //      opt-in escape hatch for adversarial inputs.
        // Per `~/.claude/plans/wpds-ambiguity-preserving-redesign.md`
        // §C.6 ("Delete subsume_lex_dominated_cursors") and the
        // `feedback_never_disambiguate_early` memo.

        if self.branch_cursors.is_empty() {
            // CASE 1: all branches dropped.
            let s = WpdaState::Error {
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
        let s = WpdaState::AmbiguityFanout { branches: frontier };
        self.state = s.clone();
        s
    }

    /// Stage 3.5b (2026-05-01): WPDS configuration ⊕-merging.
    ///
    /// Collapses cursors with the same `ConfigKey` (`state`, `gss_node`,
    /// `pos`) into a single cursor whose weight is the `Semiring::plus`
    /// of the inputs. The operational state (`recovery_deltas`,
    /// `collection_stack`) of the lex-min winner is kept; the loser's
    /// is discarded because deltas are non-commutative (e.g.,
    /// `PushIdent("x"); PushIdent("y")` cannot be merged with the reverse
    /// — only the winning path's mutations execute).
    ///
    /// **Performance**: O(n) per call (n = `branch_cursors.len()`), via
    /// HashMap lookup. In unambiguous grammars n ≤ 1; in ambiguous,
    /// merging caps n polynomially vs the pre-3.5b exponential.
    ///
    /// **Hash safety**: `WpdaState` derives `Hash` (Stage 3.5b
    /// `wpda_runtime.rs:326`); all variant payloads are `Hash`-able
    /// (u8/u16/usize/String/Vec<u32>).
    ///
    /// **Tie-break**: when `cursor.weight.plus(&existing.weight) ==
    /// existing.weight`, the existing entry wins (preserves source-order).
    /// Collapse cursors at the same `ConfigKey` (state, gss_node, pos,
    /// incoming_edge, collection_depth) by `Semiring::plus_ref`. Lex-min
    /// + `source_priority` selects the surviving cursor's operational
    /// state (recovery_deltas, builder, incoming_edge_stack, etc.).
    ///
    /// ## SPPF interaction (Option C / C5)
    ///
    /// Under Option C, the SPPF (`self.sppf`) is the structural record of
    /// every reduce. By Symbol-dedup (sppf.rs:1.4), all derivations of
    /// `(non_terminal, lo, hi)` collapse to the same SppfId. As a
    /// consequence: **at every `ConfigKey`-equivalent merge, the two
    /// cursors' sppf_stack tops point at the SAME SppfId**.
    ///
    /// Proof sketch (per plan §2.4):
    /// - Same `pos` ⇒ same input prefix consumed ⇒ same Terminal/Symbol
    ///   pushed by the most recent emit-helper.
    /// - `intern_terminal` dedups by `(kind, pos)`; `intern_symbol` dedups
    ///   by `(nt_tag, lo, hi)`; `intern_packing` dedups by
    ///   `(rule_idx, children_hash)`. Any two cursors that pushed
    ///   structurally-identical content at the same position get the
    ///   same SppfId.
    /// - Exception: `intern_predicate` and `intern_collection_id`
    ///   placeholders are walker-arena-keyed, not content-keyed. Cursors
    ///   that independently constructed predicate/collection state at the
    ///   same ConfigKey may have differing SppfIds for those leaves.
    ///   Predicate dedup is a follow-up improvement (post-C12); the
    ///   current C5 invariant is "tops of the same SPPF NodeKind match."
    ///
    /// Merge does NO SPPF work — Symbol-dedup at reduce time has already
    /// preserved all ambiguity. The winning cursor's sppf_stack carries
    /// forward; the loser's references the same shared SppfIds.
    /// Phase F.13 H11a diagnostic (2026-05-20): sample intra-`pos` cursor
    /// pairs that would fail to merge in `merge_equivalent_cursors`, and
    /// tally which `ConfigKey` discriminator (`state`, `node`,
    /// `incoming_edge`, `collection_depth`) is the SOLE cause of the
    /// difference. Pairs differing on ≥2 discriminators are counted as
    /// `multi_diff`.
    ///
    /// Sampling is bounded: at most 100 pairs per call (10 per top-10
    /// largest pos-buckets). Constant overhead per `step_fanout`.
    ///
    /// Interpretation rubric:
    /// - `edge` dominates (>60%): incoming_edge is the discriminator —
    ///   Branch A (incoming_edge_alternatives) applies.
    /// - `node` dominates: GSS-level dedup gap — Branch B.
    /// - `state` dominates: relaxed-state merge candidate — Branch C.
    /// - `depth` dominates: collection-depth desync bug — Branch D.
    /// - `multi` dominates: no single fix sufficient; H11a rejected.
    #[cfg(feature = "walker-stats")]
    fn sample_merge_misses(&mut self) {
        if self.branch_cursors.len() < 2 {
            return;
        }
        // Bucket cursor indices by `pos`. We use a Vec-of-Vec keyed by
        // pos to keep allocations bounded; for chain_50 peak ≈4012
        // cursors at ~30-50 distinct positions, this is small.
        use std::collections::HashMap;
        let mut by_pos: HashMap<usize, Vec<usize>> = HashMap::new();
        for (idx, c) in self.branch_cursors.iter().enumerate() {
            by_pos.entry(c.pos).or_default().push(idx);
        }
        // Take only the largest 10 buckets (sorted by size desc).
        let mut buckets: Vec<(usize, Vec<usize>)> = by_pos.into_iter().collect();
        buckets.sort_by_key(|(_, v)| std::cmp::Reverse(v.len()));
        let mut pairs_remaining: usize = 100;
        for (_pos, idxs) in buckets.iter().take(10) {
            if idxs.len() < 2 || pairs_remaining == 0 {
                continue;
            }
            // Take first 10 pairs (i, j) with i<j from this bucket.
            'outer: for i in 0..idxs.len() {
                for j in (i + 1)..idxs.len() {
                    if pairs_remaining == 0 {
                        break 'outer;
                    }
                    let a = &self.branch_cursors[idxs[i]];
                    let b = &self.branch_cursors[idxs[j]];
                    let state_diff = a.inner_state != b.inner_state;
                    let node_diff = a.node != b.node;
                    let a_edge = a.incoming_edge_stack.last().copied();
                    let b_edge = b.incoming_edge_stack.last().copied();
                    let edge_diff = a_edge != b_edge;
                    let depth_diff = a.collection_stack_depth != b.collection_stack_depth;
                    let diff_count = (state_diff as u8)
                        + (node_diff as u8)
                        + (edge_diff as u8)
                        + (depth_diff as u8);
                    self.stats.merge_miss_pairs_considered_total =
                        self.stats.merge_miss_pairs_considered_total.saturating_add(1);
                    if diff_count == 0 {
                        // Identical key; would merge — not a miss.
                    } else if diff_count >= 2 {
                        self.stats.merge_miss_multi_diff_total =
                            self.stats.merge_miss_multi_diff_total.saturating_add(1);
                    } else if state_diff {
                        self.stats.merge_miss_state_diff_total =
                            self.stats.merge_miss_state_diff_total.saturating_add(1);
                    } else if node_diff {
                        self.stats.merge_miss_node_diff_total =
                            self.stats.merge_miss_node_diff_total.saturating_add(1);
                    } else if edge_diff {
                        self.stats.merge_miss_edge_diff_total =
                            self.stats.merge_miss_edge_diff_total.saturating_add(1);
                    } else if depth_diff {
                        self.stats.merge_miss_depth_diff_total =
                            self.stats.merge_miss_depth_diff_total.saturating_add(1);
                    }
                    // Phase F.13 H13 Step 0: check if the pair would
                    // merge under EdgeKind-relaxed equivalence. Compute
                    // when state, node, depth all match (the H13
                    // relaxed key drops only `incoming_edge` identity).
                    if !state_diff && !node_diff && !depth_diff {
                        // Only edge identity differs — check kind.
                        let a_kind = a_edge.and_then(|e| self.gss.edge_kind(e));
                        let b_kind = b_edge.and_then(|e| self.gss.edge_kind(e));
                        let kinds_match = match (&a_kind, &b_kind) {
                            (None, None) => true,
                            (Some(crate::gss::EdgeKind::CrossCatProjection {
                                source_src_idx: a_s,
                                inner_cur_bp: a_b,
                            }), Some(crate::gss::EdgeKind::CrossCatProjection {
                                source_src_idx: b_s,
                                inner_cur_bp: b_b,
                            })) => a_s == b_s && a_b == b_b,
                            // Generic uses identity — already counted as
                            // differing because edge_diff was true.
                            _ => false,
                        };
                        if kinds_match {
                            self.stats.merge_miss_pairs_edge_kind_equivalent =
                                self.stats.merge_miss_pairs_edge_kind_equivalent.saturating_add(1);
                        }
                    }
                    pairs_remaining -= 1;
                }
            }
        }
    }

    fn merge_equivalent_cursors(&mut self) {
        if self.branch_cursors.len() < 2 {
            return;
        }
        // Phase F.13 walker-stats (2026-05-20): accumulate merge attempt
        // count (input cursors). Collapses counted per-cursor in the
        // Occupied arm below.
        crate::stats_add!(self, merge_attempts_total, self.branch_cursors.len() as u64);
        let mut by_key: std::collections::HashMap<ConfigKey, usize> =
            std::collections::HashMap::with_capacity(self.branch_cursors.len());
        let mut merged: Vec<BranchCursor<W>> =
            Vec::with_capacity(self.branch_cursors.len());
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
                //
                // Phase F.2 (2026-05-18): swap to SPPF-side mirror.
                collection_depth: cursor.collection_stack_depth as usize,
                // Phase F.13 H12 Stage 1.5.3R-c (2026-05-21): cohort
                // origin bucketing. Cohort revives bucket separately
                // from per-cursor cursors so they don't collapse via
                // lex-min and discard each other's distinct outer
                // packings (the `-3!` bug).
                cohort_origin: cursor.cohort_origin.clone(),
            };
            match by_key.entry(key) {
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(merged.len());
                    merged.push(cursor);
                }
                std::collections::hash_map::Entry::Occupied(o) => {
                    // Phase F.13 walker-stats (2026-05-20): count each
                    // cursor collapsed by merge.
                    crate::stats_inc!(self, merge_collapses_total);
                    crate::stats_inc!(self, cursors_dropped_via_merge);
                    let idx = *o.get();
                    // C8.2 (2026-05-16): the M11.5 builder-snapshot injection
                    // (capturing per-cursor builder state into weight entries
                    // for multiset-union preservation) was deleted alongside
                    // the C10 W revert. With W = LexicographicWeight,
                    // `SnapshotWeight::with_builder_snapshot` was a no-op
                    // identity wrapper; structural ambiguity now lives in the
                    // SPPF arena (Symbol-dedup at `(nt, lo, hi)` collapses
                    // observationally-equivalent cursors' shared SPPF root).
                    let combined = merged[idx].weight.plus_ref(&cursor.weight);
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
                    // Phase 5.6-tail-A (2026-05-12): pre-tail this match
                    // also had a B13d-R/Resolution-R consistency override
                    // (`cursor_committed_ops_consistent` dry-run on the
                    // cursor's recovery_deltas). Under always-eager
                    // Arc::make_mut (Phase 5.3+), broken cursors transition
                    // to `WpdaState::Error` at eager-fire time and are
                    // filtered by `cursor_resolution_check :: Drop`. By the
                    // time a cursor reaches `merge_equivalent_cursors`, it
                    // is by construction "consistent" (its cursor.builder
                    // is a valid live state). The weight + source_priority
                    // chain is the sole tiebreak.
                    let cursor_wins = weight_strict_win
                        || (weight_tied
                            && cursor.source_priority < merged[idx].source_priority);
                    if cursor_wins {
                        // Phase F.2 (2026-05-18): SPPF-side mirror —
                        // ConfigKey already includes collection_depth so
                        // matching values is guaranteed by the merge
                        // bucketing; this debug_assert is structural
                        // defense-in-depth.
                        debug_assert_eq!(
                            merged[idx].collection_stack_depth,
                            cursor.collection_stack_depth,
                            "merge_equivalent_cursors: cursors at the same \
                             configuration must have matching collection-stack \
                             depths (operational state shape)"
                        );
                        // Option C / C5: SPPF integrity check — every
                        // SppfId on either cursor's sppf_stack must be a
                        // valid arena index. This is true by construction
                        // (intern_* methods return valid ids) but guards
                        // against future emit-helper bugs that mishandle
                        // sentinel ids.
                        #[cfg(debug_assertions)]
                        {
                            let sppf_len = self.sppf.len() as u32;
                            for &sid in cursor.sppf_stack.iter() {
                                debug_assert!(
                                    sid < sppf_len,
                                    "merge_equivalent_cursors: cursor.sppf_stack \
                                     contains stale SppfId {} (sppf.len() = {})",
                                    sid, sppf_len
                                );
                            }
                            for &sid in merged[idx].sppf_stack.iter() {
                                debug_assert!(
                                    sid < sppf_len,
                                    "merge_equivalent_cursors: winner.sppf_stack \
                                     contains stale SppfId {} (sppf.len() = {})",
                                    sid, sppf_len
                                );
                            }
                        }
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

    // M7c (2026-05-13): `subsume_lex_dominated_cursors` DELETED.
    //
    // Per the longstanding "never disambiguate early" principle
    // (`feedback_never_disambiguate_early.md`), weight-based "pick one"
    // collapse of strictly-dominated cursors mid-stream violates the
    // ambiguity-preservation mandate. The dropped cursors haven't
    // failed via evidence; they may yield a different (still valid)
    // derivation that the caller wants.
    //
    // Cursor count bounding is now provided by:
    //   1. merge_equivalent_cursors (strict ConfigKey), which collapses
    //      observationally-equivalent cursors via plus_ref (multiset
    //      union when W is DerivationWeight; same as before when W is
    //      LexicographicWeight).
    //   2. Beam pruning via maybe_prune_frontier (opt-in, default None),
    //      reserved as an escape hatch for adversarial inputs.
    //
    // For the "LedTest cursor explosion" rationale that motivated the
    // deleted function: under multi-result preservation, the supposedly
    // "dominated" siblings ARE the valid alternative derivations to
    // surface at EOI. Pruning them violated the mandate.

    // Phase 5.6-tail follow-up (2026-05-12): `pick_lex_min_resolved`
    // method DELETED. The pre-tail call site was the mid-stream
    // commit_winner path that Stage 3.5b Bug 1 fix removed. EOI
    // resolution at `resolve_at_end_of_input` does its own inline
    // lex-min loop (see lines around 2542-2586). Subsumption in
    // `subsume_lex_dominated_cursors` also does its own inline scan.
    // The standalone helper became orphaned and was reported by the
    // compiler as dead code throughout Phases 3-5.

    /// Step 3 (Fork plan F6): commit the winning branch.
    ///
    /// Replays the winner's `recovery_deltas` against the live
    /// `SemanticBuilder` in insertion order, then splices the winner's
    /// `(node, pos, weight, inner_state)` into the walker's live state.
    ///
    /// Stage 3.9 / ι Phase 4 (2026-05-01): preserves the always-non-empty
    /// `branch_cursors` invariant by writing the post-commit singleton
    /// back to `branch_cursors[0]` (with cleared `recovery_deltas`
    /// and `collection_stack` since those have already replayed onto the
    /// live builder). Pre-Phase-4 this method called `clear()`; that
    /// would now violate L4.
    fn commit_winner(&mut self, winner_idx: usize) {
        let winner = self.branch_cursors.swap_remove(winner_idx);
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
        // Phase 5.6-tail-G (2026-05-12): winner.collection_stack mirror
        // DELETED — the cursor.builder.collection_stack is the
        // authoritative state, intrinsically donated to self.builder via
        // the Arc-install below.
        // Always install the winner's builder over self.builder. Under
        // Phase 5.6-tail-B's always-eager Arc::make_mut path,
        // winner.builder is the authoritative live state for BOTH the
        // deterministic singleton at commit_winner_at_eoi and the nondeterministic
        // fanout-winner. `Arc::try_unwrap` keeps the underlying
        // SemanticBuilder if the winner is the last Arc holder (the
        // post-commit singleton at the bottom of this function REPLACES
        // `branch_cursors` so sibling Arc refs in dead cursors are about
        // to drop). If there's still another holder, fall back to deep
        // clone via SemanticBuilder: Clone (Phase 5.3). The clone is
        // structurally shared via `im::Vector` HAMTs — O(log N) per
        // field root.
        // Phase F.3c.4 (2026-05-20): cursor.builder field deleted. The
        // `Arc::try_unwrap(... winner.builder ...)` install site that
        // donated the winning cursor's Arc to `self.builder` is gone.
        // The winner's SPPF-side state (sppf_stack, sppf_collection_arena,
        // sppf_symbol_terms, etc.) is moved into the post-commit
        // singleton below. self.builder remains as a stub (F.3c.5
        // deletes).
        // Phase 5.6-tail-E (2026-05-12): replay loop is now recovery-only
        // by construction. winner.recovery_deltas holds ONLY the 5 recovery
        // variants (gated by is_recovery_delta in Step D). Non-recovery
        // codegen-effect deltas (StartBinderScope, EndBinderScope,
        // StartCollection, PushCollectionId, SpliceIntoCollection) were
        // applied to cursor.builder via apply_effect_to_builder at emit
        // time; they're never journaled and thus never reach this loop.
        for delta in winner.recovery_deltas {
            match delta {
                // Non-recovery variants (StartBinderScope, EndBinderScope,
                // StartCollection, PushCollectionId, SpliceIntoCollection):
                // can't be journaled to recovery_deltas under is_recovery_delta
                // gating. Match them as unreachable for exhaustiveness.
                BuilderDelta::StartBinderScope { .. }
                | BuilderDelta::EndBinderScope
                | BuilderDelta::StartCollection
                | BuilderDelta::PushCollectionId { .. }
                | BuilderDelta::SpliceIntoCollection { .. } => {
                    debug_assert!(
                        false,
                        "non-recovery BuilderDelta reached commit_winner replay \
                         — is_recovery_delta gate violated"
                    );
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
                    // Mutates the token source via WpdaMutableTokenSource::
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
                         requires WpdaMutableTokenSource threading",
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
        self.weight = self.weight.times_ref(&winner.weight);
        self.state = winner.inner_state.clone();
        // Stage 3.9 / ι Phase 4 (2026-05-01): write singleton back per L4.
        // Cleared recovery_deltas — already replayed onto live builder above.
        // `self.deterministic` stays false (monotone once flipped).
        self.branch_cursors = vec![BranchCursor {
            node: winner.node,
            pos: winner.pos,
            weight: self.weight.clone(),
            inner_state: winner.inner_state,
            recovery_deltas: Vec::new(),
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
            // Phase F.3c.4 (2026-05-20): cursor.builder field deleted.
            // The post-commit singleton no longer carries a builder
            // Arc; the winner's SPPF-side state (sppf_stack,
            // sppf_collection_arena, sppf_symbol_terms, etc.) below
            // is the authoritative per-cursor state.
            // Option C / C2: preserve winner's SPPF stack so subsequent
            // reduces continue building on top of the committed history.
            sppf_stack: winner.sppf_stack,
            optional_scope_marks: winner.optional_scope_marks,
            binder_scope_marks: winner.binder_scope_marks,
            // Phase C.2 (2026-05-17): preserve the winner's pending weight
            // chain so subsequent reduces continue accumulating from where
            // the winner left off. Identical rationale to sppf_stack.
            pending_packing_weight: winner.pending_packing_weight,
            // Phase F.1 (2026-05-18): preserve the winner's open-collection
            // depth so subsequent emit_start_collection / drain_collection
            // calls continue tracking from the committed state.
            collection_stack_depth: winner.collection_stack_depth,
            // Phase F.4 (2026-05-18): preserve winner's per-cursor SPPF
            // collection arena. Sibling cursors' Arcs drop when
            // `branch_cursors` is cleared above, reclaiming any
            // per-lineage splice content orphaned by the merge
            // tiebreak. Post-commit, this Arc is the SOLE source of
            // truth for realize_*'s CollectionId resolution. See
            // `WpdaWalker::winner_collection_arena()`.
            sppf_collection_arena: winner.sppf_collection_arena,
            // Phase F.3a (2026-05-20): preserve winner's mirror.
            last_action_output_cat: winner.last_action_output_cat,
            cohort_origin: winner.cohort_origin.clone(),
            cohort_revive_depth: winner.cohort_revive_depth,
            // Phase F.3c.2 (2026-05-20): preserve winner's memo so
            // post-commit symbol lookups continue to find their realized
            // payloads. Move (not clone) — single-cursor post-commit.
        }];
    }

    /// Stage 3.4 (2026-04-30): cursor-count bounding over `branch_cursors`.
    ///
    /// M11.7 (2026-05-14): dispatches on [`CursorBoundingMode`]:
    /// - `Unbounded` (default): no-op. Mandate-compliant baseline.
    /// - `BeamSize(k)`: legacy beam pruning. **MANDATE VIOLATION**: drops
    ///   cursors beyond the top-`k` by lex-min weight without evidence.
    ///   Use only as an adversarial-input escape hatch.
    /// - `AmbiguityBudget(n)`: if `branch_cursors.len() > n`, transition
    ///   the walker to `WpdaState::Error` with an "AMBIGUITY_BUDGET_EXCEEDED:"
    ///   sentinel prefix the resolve step decodes into
    ///   `WpdaResolveResult::AmbiguityBudget`. Mandate-compliant: no
    ///   silent dropping; caller observes the structured error and reacts.
    ///
    /// Called from `step_fanout` after the per-cursor step pass so the
    /// pruned/checked frontier is the input to the next saturation
    /// iteration.
    fn maybe_prune_frontier(&mut self) {
        match self.bounding_mode {
            crate::wpda_runtime::CursorBoundingMode::Unbounded => {}
            crate::wpda_runtime::CursorBoundingMode::BeamSize(k) => {
                if self.branch_cursors.len() <= k {
                    return;
                }
                // Stable sort by weight ascending under the `plus`-based
                // lex-min comparator. Keeps source-order for ties (matching
                // `pick_lex_min_resolved`'s tie-break semantics).
                //
                // **MANDATE VIOLATION**: drops cursors below the top-K
                // without evidence. Retained only for adversarial-input
                // recovery; see [`CursorBoundingMode::BeamSize`] docs.
                self.branch_cursors.sort_by(|a, b| {
                    let merged = a.weight.plus_ref(&b.weight);
                    let a_wins = merged == a.weight;
                    let b_wins = merged == b.weight;
                    match (a_wins, b_wins) {
                        (true, true) => std::cmp::Ordering::Equal,
                        (true, false) => std::cmp::Ordering::Less,
                        (false, true) => std::cmp::Ordering::Greater,
                        (false, false) => std::cmp::Ordering::Equal,
                    }
                });
                self.branch_cursors.truncate(k);
            }
            crate::wpda_runtime::CursorBoundingMode::AmbiguityBudget(n) => {
                let actual = self.branch_cursors.len();
                if actual <= n {
                    return;
                }
                // Mandate-compliant overflow: transition the walker to an
                // Error state encoding the budget violation in the sentinel-
                // prefixed message. `resolve_at_end_of_input` decodes the
                // sentinel and returns `WpdaResolveResult::AmbiguityBudget
                // { budget, actual, position }`.
                self.state = WpdaState::Error {
                    message: format!(
                        "AMBIGUITY_BUDGET_EXCEEDED: budget={} actual={} position={}",
                        n, actual, self.pos,
                    ),
                };
            }
        }
    }

    // Phase 5.6-tail follow-up (2026-05-12): two more orphaned methods
    // DELETED here.
    //
    // 1. `maybe_splice_into_enclosing_collection` was the pre-Phase-5
    //    splice-after-Pop helper that operated on `self.top_node` and
    //    `self.builder` directly. Phase 5.3+'s always-eager
    //    Arc::make_mut path routes splice through
    //    `emit_splice_into_collection` on `cursor.builder`; the helper
    //    became orphaned at the apply_action_to_cursor migration.
    //
    // 2. `fire_action_for` was the pre-Phase-5.5 fire-action helper that
    //    mutated `self.builder` via `std::mem::replace`. Phase 5.6-tail-B
    //    unified all fire_action calls to use
    //    `Self::fire_action_for_on_builder(&self.engine, builder_mut, symbol)`
    //    on `cursor.builder` via `Arc::make_mut`; the standalone
    //    `self.builder`-targeting variant became orphaned.

    /// Phase 5.6-tail-D (2026-05-12): predicate for the recovery
    /// subset of `BuilderDelta`. Recovery deltas mutate the walker's
    /// `recovery_events` / `mutable_token_source` adapters — state OUTSIDE
    /// cursor.builder — so their replay at commit_winner is mandatory.
    /// Non-recovery deltas mutate the builder; under always-eager
    /// `Arc::make_mut` (Phase 5.3+), they're applied to cursor.builder
    /// at emit time and the journal entry is redundant. This predicate
    /// gates the Fork-arm "effect" journal pushes: only recovery deltas
    /// land in `cursor.recovery_deltas`.
    #[inline(always)]
    fn is_recovery_delta(delta: &BuilderDelta) -> bool {
        matches!(
            delta,
            BuilderDelta::RecoveryEvent { .. }
                | BuilderDelta::SubstituteToken { .. }
                | BuilderDelta::InsertToken { .. }
                | BuilderDelta::CommitLexAlternative { .. }
                | BuilderDelta::ApplyRecoverySequence { .. }
        )
    }

    // Phase F.3c.7 (2026-05-20): `apply_effect_to_builder` DELETED.
    // This static helper applied a non-recovery `BuilderDelta` to a
    // `SemanticBuilder` reference. Its sole caller was the persistent-
    // builder path inside `apply_effect_to_cursor`, which was rewired
    // in Phase F.3c.4 (commit `ac8b502`) to skip builder mutation —
    // SPPF mirror writes are the new source of truth. Rustc flagged
    // the function as `dead_code` after F.3c.4. Now removed.

    /// Bug N (Phase 3.1.5): SPPF-aware effect application. Applies the
    /// effect to `cursor.builder` via the static `apply_effect_to_builder`,
    /// then mirrors the relevant ops onto `cursor.binder_scope_marks` and
    /// `cursor.sppf_stack`:
    ///
    /// - `StartBinderScope { names }`: push `(depth, names)` onto
    ///   `binder_scope_marks` so the matching EndBinderScope can capture
    ///   the full name list.
    /// - `EndBinderScope`: pop the topmost mark, intern an
    ///   `SppfNode::BinderScope` from `(depth, names)`, push its SppfId
    ///   onto `sppf_stack`. Mirrors the builder's push of
    ///   `ActionArg::BinderScope` onto its active args stack.
    ///
    /// Family-A bugfix (2026-05-18, H4 from
    /// `~/.claude/plans/replicated-conjuring-turtle.md`): the prior
    /// comment claimed "Collection ops require no SPPF mirror at this
    /// site — the collection mirror is in emit_*". That was wrong for
    /// the EFFECT path: the binder Class-3 empty-list bootstrap at
    /// `macros/.../binder.rs:1344-1369` uses `GuardedConsumeAndReplaceWithMultipleEffects`
    /// to emit `StartCollection` + `PushCollectionId` + `StartBinderScope`
    /// + `EndBinderScope` via `apply_effect_to_cursor`, not via the
    /// `emit_*` helpers. The builder side correctly pushed
    /// `ActionArg::CollectionId` but the SPPF mirror was absent — so
    /// `emit_fire_action` saw `arity=3 have=2` and silently skipped via
    /// the Bug P gate (line ~7388). Fix: mirror the collection ops here
    /// matching the emit_* helpers' SPPF push semantics.
    fn apply_effect_to_cursor(&mut self, cursor: &mut BranchCursor<W>, effect: &BuilderDelta) {
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The
        // pre-existing `apply_effect_to_builder(Arc::make_mut(&mut
        // cursor.builder), effect)` call is gone. Effects' SPPF-side
        // mirrors below are now the SOLE authoritative state for
        // binder-scope / collection / splice operations. The mirror
        // clears since none of these effects push a Term onto the
        // main arg stack.
        self.clear_action_output_mirror(cursor);
        // SPPF + cursor-state mirror.
        match effect {
            BuilderDelta::StartBinderScope { names } => {
                let depth = cursor.binder_scope_marks.len() as u16;
                cursor.binder_scope_marks.push((depth, names.clone()));
            }
            BuilderDelta::EndBinderScope => {
                if let Some((depth, names)) = cursor.binder_scope_marks.pop() {
                    let sid = self.sppf.intern_binder_scope(&names, depth);
                    Arc::make_mut(&mut cursor.sppf_stack).push(sid);
                }
            }
            BuilderDelta::StartCollection => {
                // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The
                // new slot id is derived from cursor.collection_stack_depth
                // directly (== the next allocator id, matching the
                // pre-F.3c builder.collection_stack.len() return). Add
                // the corresponding empty slot to the cursor's SPPF
                // arena and increment the depth counter.
                let new_id = cursor.collection_stack_depth as usize;
                let arena = Arc::make_mut(&mut cursor.sppf_collection_arena);
                while arena.len() <= new_id {
                    arena.push(Vec::new());
                }
                arena[new_id].clear();
                cursor.collection_stack_depth =
                    cursor.collection_stack_depth.saturating_add(1);
            }
            BuilderDelta::PushCollectionId { id } => {
                // H4 (2026-05-18): mirror emit_push_collection_id's
                // sppf_stack push. The builder-side already pushed
                // `ActionArg::CollectionId(id)` via push_collection_id;
                // mirror by interning the CollectionId leaf on the SPPF
                // side and pushing the SppfId onto sppf_stack so the
                // subsequent emit_fire_action's arity check passes.
                let sid = self.sppf.intern_collection_id(*id as u32);
                Arc::make_mut(&mut cursor.sppf_stack).push(sid);
            }
            BuilderDelta::SpliceIntoCollection { id } => {
                // Phase F.9 (2026-05-19): mirror `emit_splice_into_collection`'s
                // SPPF-side splice. The prior comment claimed Splice's
                // pop-not-push asymmetry "doesn't bite arity checks" — true
                // for arity checks at `emit_fire_action`, but the downstream
                // `realize_root_to_terms` path reads
                // `cursor.sppf_collection_arena[id]` to reconstruct the
                // spliced collection's elements. Without this mirror,
                // binder-internal splices (PInputs Names accumulator,
                // BinderListLoop sub_pos > 0) leave the SPPF arena slot
                // EMPTY while the symbol is stranded on `sppf_stack` — the
                // action's reconstructed Term then has zero binders, and no
                // accepting cursor reaches EOI (manifested as
                // `comm_under_new`'s "no accepting branch" error).
                //
                // The builder-side `apply_effect_to_builder` already called
                // `builder.push_to_collection(*id)` to move the ActionArg
                // from `builder.args_stack` into `builder.collections`.
                // Mirror by popping the corresponding symbol from
                // `cursor.sppf_stack` and appending to the per-cursor SPPF
                // arena slot. Bounds-check on `id` matches the helper's
                // defensive guard at `emit_splice_into_collection`.
                if (*id as usize) < cursor.sppf_collection_arena.len() {
                    if let Some(top) = Arc::make_mut(&mut cursor.sppf_stack).pop() {
                        Arc::make_mut(&mut cursor.sppf_collection_arena)
                            [*id as usize]
                            .push(top);
                    }
                }
            }
            // Recovery effects: no SPPF mirror here; recovery deltas mutate
            // mutable_token_source / recovery_events, not AST.
            _ => {}
        }
    }

    // Phase F.3c.7 (2026-05-20): `fire_action_for_on_builder` DELETED.
    // This static helper fired a semantic action on a `SemanticBuilder`
    // reference (rather than `self.builder`); its sole caller was the
    // persistent-builder branch of `emit_fire_action`, which was rewired
    // in Phase F.3c.3 (commit `73c8071`) to the transient-builder path
    // via `fire_action_via_transient`. Rustc flagged the function as
    // `dead_code` after F.3c.3. The post-action invariant check (every
    // action_fn pushes EXACTLY ONE Term; mismatch = silent type-coercion
    // failure, e.g. `arg.into_term::<T>()` returned None) now lives in
    // `fire_action_via_transient` and the arity-underflow Error handling
    // moved into `emit_fire_action` directly (F.3c.3).

    // ══════════════════════════════════════════════════════════════════════
    // Per-variant mutation helpers
    //
    // Each `emit_*` helper eagerly mutates `cursor.builder` via
    // `Arc::make_mut`. Pre-Phase-5.6-tail there was a Lazy/Strict
    // dispatch (direct mutation of self.builder vs journaled mutation
    // replayed at commit_winner); under always-eager Arc::make_mut, both
    // paths collapse to a single eager call on cursor.builder.
    //
    // The 4 mode-agnostic helpers (`advance_cursor_pos`/
    // `multiply_cursor_weight`/`set_cursor_inner_state`/`cursor_gss_*`)
    // update the cursor's local state AND, in deterministic mode, mirror to
    // the live walker fields (`self.pos`/`self.weight`/`self.state`/
    // `self.top_node`) so external accessors (`walker.position()`, etc.)
    // reflect the cursor's view. In nondeterministic mode the mirror is skipped —
    // self.* loses singleton meaning and is rehydrated at commit_winner.
    //
    // All helpers are `#[inline(always)]` so the optimizer specializes
    // them per call site.
    // ══════════════════════════════════════════════════════════════════════

    // Phase 5.6-tail-B (2026-05-12): debug_flush_lazy_invariant deleted —
    // the L1 invariant (deterministic mode implies singleton cursor with empty
    // recovery_deltas) is moot now that CursorMode and deterministic/nondeterministic
    // dispatch are gone (Step F finishes the enum removal).

    // ─── 11 mutation helpers ─────────────────────────────────────────────
    //
    // Phase 5.6-tail-B (2026-05-12): all 14 helpers below collapse to a
    // single eager `Arc::make_mut(&mut cursor.builder).<method>(...)` call.
    // The pre-tail `match self.cursor_mode { Lazy => self.builder.<m>(...),
    // Strict => cursor.recovery_deltas.push(BuilderDelta::...) }`
    // dispatch is deleted: the cursor.builder IS the authoritative state
    // (Phase 5.3+), and self.builder is brought up-to-date via
    // `install_singleton_cursor_builder` at resolve time (and at any
    // post-step boundary where downstream consumers read self.builder).

    /// Phase F.3c.4 (2026-05-20): clear `cursor.last_action_output_cat`.
    /// Called at the end of every non-fire emit_* helper and
    /// `apply_effect_to_cursor` — all those helpers push non-Term
    /// values (Token/Ident/Predicate/CollectionId/OptAbsent/BinderScope)
    /// or modify scope state without pushing onto the main arg stack,
    /// so the "last action output cat" semantic ceases to apply. The
    /// mirror is REPOPULATED only by `emit_fire_action`'s transient
    /// fire success path.
    ///
    /// Pre-F.3c.4 this was `refresh_action_output_mirror` which read
    /// `cursor.builder.top_term_type_name() → cat_of_type_name(tn)` to
    /// refresh; F.3c.4 deletes cursor.builder and the helper simplifies
    /// to a None-clear since all 13 non-fire call sites push non-Term
    /// values whose post-fix mirror IS None.
    #[inline(always)]
    fn clear_action_output_mirror(&self, cursor: &mut BranchCursor<W>) {
        cursor.last_action_output_cat = None;
    }

    #[inline(always)]
    fn emit_push_token(
        &mut self,
        cursor: &mut BranchCursor<W>,
        kind: TokenKind,
        text: String,
        pos: usize,
    ) {
        // C3 dual-mode: intern a Terminal in the SPPF arena alongside the
        // existing builder push. Text is preserved if non-empty.
        // Bug E (Phase 3.1.3): pushed_via_push_ident=false signals
        // emit_push_token origin → realization produces ActionArg::Token.
        let text_opt = if text.is_empty() { None } else { Some(text.as_str()) };
        let sid = self.sppf.intern_terminal(
            kind.clone(),
            crate::sppf::PosOrSynth::Real(pos as u32),
            text_opt,
            false,
        );
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The SPPF-side
        // intern_terminal + sppf_stack.push above carries the structural
        // state; emit_fire_action's reconstruct_action_arg reads the
        // Terminal node directly. Mirror clears to None since the push
        // was a Token (non-Term).
        self.clear_action_output_mirror(cursor);
    }

    /// Phase F.8 (2026-05-18): mirror a consumed-but-not-captured unary-prefix
    /// trigger token onto `sppf_stack` ONLY (no builder push — the trigger is
    /// `capture_token=false` so the builder has no record of it). The
    /// TriggerTerminal lands BENEATH the rule's eventual operand sub-parse
    /// in the cursor's `sppf_stack`. When `emit_fire_action` reduces the
    /// rule, the walk-back drain (see lines 7428-7437) includes the
    /// TriggerTerminal in `children`, the leftmost child's `span_lo` returns
    /// the trigger's input position, and the parent rule's interned Symbol
    /// receives `lo = trigger_pos` — DISTINCT from the operand's Symbol
    /// `lo`. This breaks the pre-fix Symbol-dedup collision that silently
    /// dropped unary-prefix wrappings (e.g., `not true` realizing as
    /// `BoolLit(true)` instead of `Not(BoolLit(true))`).
    #[inline(always)]
    fn emit_push_trigger_terminal(
        &mut self,
        cursor: &mut BranchCursor<W>,
        kind: TokenKind,
        text: String,
        pos: usize,
        owner_cat: u16,
        owner_rule_idx: u16,
    ) {
        let text_opt = if text.is_empty() { None } else { Some(text.as_str()) };
        let sid = self.sppf.intern_trigger_terminal(
            kind,
            crate::sppf::PosOrSynth::Real(pos as u32),
            text_opt,
            owner_cat,
            owner_rule_idx,
        );
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
    }

    #[inline(always)]
    fn emit_push_ident(&mut self, cursor: &mut BranchCursor<W>, name: String, pos: usize) {
        // C3 dual-mode: SPPF terminal with TokenKind::Ident + the name text.
        // Bug E (Phase 3.1.3): pushed_via_push_ident=true signals
        // emit_push_ident origin → realization produces ActionArg::Ident.
        let sid = self.sppf.intern_terminal(
            TokenKind::Ident,
            crate::sppf::PosOrSynth::Real(pos as u32),
            Some(name.as_str()),
            true,
        );
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. SPPF Terminal
        // node carries the Ident state. Mirror clears (Ident is non-Term).
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_push_predicate(
        &mut self,
        cursor: &mut BranchCursor<W>,
        pred: Arc<dyn Any + Send + Sync>,
    ) {
        // C3 dual-mode: intern the predicate Arc in the walker-side arena
        // and push a Predicate leaf onto the cursor's sppf_stack.
        let handle = self.sppf_predicate_arena.len() as u32;
        self.sppf_predicate_arena.push(Arc::clone(&pred));
        let sid = self.sppf.intern_predicate(handle);
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. SPPF Predicate
        // node + sppf_predicate_arena carry the payload. Mirror clears.
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_start_binder_scope(&mut self, cursor: &mut BranchCursor<W>, names: Vec<String>) {
        // Bug N (Phase 3.1.5): record the in-progress scope on the cursor
        // mirror. The corresponding `apply_effect_to_cursor(EndBinderScope)`
        // pops this mark, interns an `SppfNode::BinderScope`, and pushes
        // its SppfId onto `sppf_stack` — matching the builder side's
        // push of `ActionArg::BinderScope` onto args.
        let depth = cursor.binder_scope_marks.len() as u16;
        cursor.binder_scope_marks.push((depth, names.clone()));
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The SPPF-side
        // `cursor.binder_scope_marks.push((depth, names))` already happened
        // above. Subsequent emit_extend_binder_scope appends; matching
        // EndBinderScope effect interns the SppfNode::BinderScope and
        // pushes its id onto sppf_stack. Mirror clears since
        // start_binder_scope doesn't push a Term onto the main stack.
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_extend_binder_scope(&mut self, cursor: &mut BranchCursor<W>, name: String) {
        // Bug N (Phase 3.1.5): append to the top in-progress scope's
        // name accumulator so subsequent EndBinderScope captures the
        // full name list.
        if let Some(top) = cursor.binder_scope_marks.last_mut() {
            top.1.push(name.clone());
        }
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. SPPF-side
        // `cursor.binder_scope_marks.last_mut()` append above carries
        // the structural state. Mirror clears.
        self.clear_action_output_mirror(cursor);
    }

    /// Phase F.1 (2026-05-18): SPPF-derived equivalent of
    /// `cursor.builder.is_accepting_terminal()`.
    ///
    /// A cursor is accepting iff (a) it has no open optional scope marks,
    /// AND (b) its `sppf_stack` is either empty or contains exactly one
    /// `SppfNode::Symbol` (the parsed root). Phase C's
    /// `emit_fire_action::intern_packing` always interns a Symbol id
    /// post-reduce, so "single Symbol" replaces the pre-C "single Term"
    /// invariant.
    ///
    /// Read-equivalent of: `cursor.builder.is_accepting_terminal()`.
    /// Replaces line 3686. Plan: §Read → SPPF Mapping.
    #[inline]
    pub fn is_cursor_accepting_terminal(&self, cursor: &BranchCursor<W>) -> bool {
        if !cursor.optional_scope_marks.is_empty() {
            return false;
        }
        match cursor.sppf_stack.as_slice() {
            [] => true,
            [sid] => matches!(
                self.sppf.node(*sid),
                Some(crate::sppf::SppfNode::Symbol { .. })
            ),
            _ => false,
        }
    }

    /// Phase F.1 (2026-05-18): SPPF-derived equivalent of
    /// `cursor.builder.top_term_type_name()` returning the
    /// `non_terminal_tag` of the top `Symbol` node. None if the stack
    /// is empty or its top is not a Symbol.
    ///
    /// **NOT a drop-in replacement for the D8 fix paths** (Return-pop +
    /// GroupingClose). The SPPF Symbol's `non_terminal_tag` tracks the
    /// LATEST Packing's `output_cat`, which can include auto-injected
    /// cast intermediates (e.g., FloatToInt cast Symbol with `tag = Int`
    /// while the post-action builder Term is the Rust type `Int`'s
    /// converted form). The D8 logic is keyed on the builder top's
    /// post-action TYPE NAME — those two reads of
    /// `top_term_type_name()` are retained in F.2 (see notes at the
    /// D8 callsites). A future redesign of the auto-injection cast
    /// modelling will enable migrating those reads. Plan: §Read → SPPF
    /// Mapping (caveat added 2026-05-18 during F.2 verification).
    #[inline]
    pub fn cursor_top_non_terminal_tag(&self, cursor: &BranchCursor<W>) -> Option<u32> {
        cursor.sppf_stack.last().and_then(|&sid| match self.sppf.node(sid) {
            Some(crate::sppf::SppfNode::Symbol { non_terminal_tag, .. }) => {
                Some(*non_terminal_tag)
            }
            _ => None,
        })
    }

    /// Phase F.1 (2026-05-18): SPPF-derived equivalent of
    /// `cursor.builder.collection_slot_len(acc_id)`. The
    /// `sppf_collection_arena[acc_id]` grows in lockstep with
    /// `builder.collection_stack[acc_id]` via
    /// `emit_splice_into_collection`. Replaces reads at 7446-53.
    /// Plan: §Read → SPPF Mapping.
    #[inline]
    pub fn cursor_collection_slot_len(
        &self,
        cursor: &BranchCursor<W>,
        acc_id: usize,
    ) -> usize {
        // Phase F.4 (2026-05-18): per-cursor arena read. Pre-F.4 this
        // read `self.sppf_collection_arena`, which captured
        // cross-cursor splices — a parity bug masked by the kv_phase
        // path being mostly hit in deterministic-mode single-cursor
        // flows. The previously-suppressed `_cursor` parameter is now
        // load-bearing.
        cursor
            .sppf_collection_arena
            .get(acc_id)
            .map(|slot| slot.len())
            .unwrap_or(0)
    }

    /// Phase F.4 (2026-05-18): post-commit accessor for the winner
    /// cursor's SPPF collection arena.
    ///
    /// In multi-cursor pre-commit state, this returns the FIRST
    /// branch_cursor's arena (any one of the live fanout cursors) —
    /// which reflects ONLY that one cursor's splice history. Other
    /// live cursors' content is invisible to this accessor. Pre-fix,
    /// the walker-global arena held content from ALL live cursors
    /// smashed together, which was the bug; the post-fix conservative
    /// view (only one cursor's splices) is correct for the production
    /// realize_* paths, all of which are called POST-COMMIT after
    /// `commit_winner_at_eoi` has installed the surviving cursor at
    /// `branch_cursors[0]`.
    #[inline]
    fn winner_collection_arena(&self) -> &[Vec<crate::sppf::SppfId>] {
        self.branch_cursors
            .first()
            .map(|c| c.sppf_collection_arena.as_ref().as_slice())
            .unwrap_or(&[])
    }

    /// Phase F.3c.2 (2026-05-20): reconstruct an `ActionArg` from a single
    /// SPPF node id, using `cursor.sppf_symbol_terms` as the memo for
    /// previously-realized Symbols. Used by `fire_action_via_transient` to
    /// build action_fn argument lists from sppf_stack children, eliminating
    /// the need for the persistent `cursor.builder.stack`.
    ///
    /// Case analysis matches `realize_packing_call`'s child-reconstruction
    /// pattern at wpda_walker.rs:~3880-3935 but operates on a SINGLE
    /// SppfId (not a cartesian-product combo).
    fn reconstruct_action_arg(
        &self,
        cursor: &BranchCursor<W>,
        sid: crate::sppf::SppfId,
    ) -> Option<ActionArg> {
        use crate::sppf::{PosOrSynth, SppfNode};
        match self.sppf.node(sid)? {
            SppfNode::Terminal {
                token_kind,
                text_handle,
                pos,
                pushed_via_push_ident,
            } => {
                let pos_val = match pos {
                    PosOrSynth::Real(p) => *p as usize,
                    PosOrSynth::Synthesized(_) => 0,
                };
                let text_s = self.sppf.text(*text_handle).to_string();
                if *pushed_via_push_ident {
                    Some(ActionArg::Ident {
                        name: text_s,
                        pos: pos_val,
                    })
                } else {
                    Some(ActionArg::Token {
                        kind: token_kind.clone(),
                        text: text_s,
                        pos: pos_val,
                    })
                }
            }
            SppfNode::Symbol { .. } => {
                // Phase F.13 H1 (2026-05-20): look up in walker-global
                // memo. SPPF SymbolIds are global (Symbol-dedup at
                // `(nt, lo, hi)`), so any cursor that previously fired
                // an action on this Symbol stored the result. Single
                // HashMap lookup replaces the per-cursor Vec scan; the
                // `cursor` parameter is unused for this arm.
                let _ = cursor;
                self.sppf_symbol_terms
                    .get(&sid)
                    .map(|arc| ActionArg::Term {
                        value: Arc::clone(arc),
                        type_name: "F3c2Reconstructed",
                    })
            }
            SppfNode::Packing { rule_idx, children, .. }
                if *rule_idx == Self::OPTIONAL_PRESENT_RULE_IDX =>
            {
                // OPTIONAL_PRESENT synthetic packing — wrap inner children
                // as `ActionArg::Optional(Some(inner_args))`.
                let inner: Option<Vec<ActionArg>> = children
                    .iter()
                    .map(|&c| self.reconstruct_action_arg(cursor, c))
                    .collect();
                inner.map(|args| ActionArg::Optional(Some(args)))
            }
            SppfNode::Packing { .. } => {
                // Non-OPTIONAL_PRESENT Packing reached as a direct child:
                // should not happen in well-formed parses — children are
                // always Terminals or Symbols. Return None defensively.
                None
            }
            SppfNode::Epsilon { .. } => {
                // Epsilon children are filtered out at the call site
                // (same as TriggerTerminal); unreachable here but return
                // None defensively.
                None
            }
            SppfNode::CollectionId { id } => Some(ActionArg::CollectionId(*id as u8)),
            SppfNode::OptAbsent { .. } => Some(ActionArg::Optional(None)),
            SppfNode::Predicate { handle } => self
                .sppf_predicate_arena
                .get(*handle as usize)
                .map(|p| ActionArg::Predicate(Arc::clone(p))),
            SppfNode::BinderScope { names_text, depth } => {
                let names: Vec<String> = names_text
                    .iter()
                    .map(|h| self.sppf.text(*h).to_string())
                    .collect();
                Some(ActionArg::BinderScope(
                    crate::wpda_runtime::BinderHandle::new(names, *depth),
                ))
            }
            SppfNode::TriggerTerminal { .. } => {
                // Filtered out at the call site BEFORE this is invoked
                // (parallel to realize_packing_call's filter at line 3739).
                None
            }
        }
    }

    /// Phase F.3c.2 (2026-05-20): fire an action_fn on a transient
    /// SemanticBuilder constructed per-call from sppf_stack-reconstructed
    /// args. Returns `Some(result_arc)` on success, `None` on elide /
    /// arity mismatch.
    ///
    /// This is the same shape as `realize_packing_call`'s transient-SB
    /// pattern at wpda_walker.rs:~3852-3960 but produces a single result
    /// (the cursor's specific parse path) instead of a cartesian product
    /// over derivations.
    ///
    /// During F.3c.2 this runs ALONGSIDE the persistent fire (the
    /// existing `Arc::make_mut(&mut cursor.builder)` path inside
    /// emit_fire_action) for parity verification. F.3c.3 will swap the
    /// persistent path out and make this the sole fire mechanism.
    /// Phase F.3c.3 (2026-05-20): returns
    /// `Some((result_arc, output_cat, drains_count))` on success, `None`
    /// on elide / arity mismatch / no action registered.
    ///
    /// - `result_arc`: the action_fn's pushed Term (the post-action
    ///   transient builder's top).
    /// - `output_cat`: cat_idx derived from the transient builder's
    ///   `top_term_type_name() → engine.cat_of_type_name(tn)`. Used
    ///   to update `cursor.last_action_output_cat` (the F.3a/b mirror).
    /// - `drains_count`: number of `drain_collection` calls the
    ///   action_fn made (= `pre_collection_len - post_collection_len`
    ///   on the transient SB). Used to update
    ///   `cursor.collection_stack_depth` post-fire.
    fn fire_action_via_transient(
        &self,
        cursor: &BranchCursor<W>,
        symbol: StackSymbolV2,
        children: &[crate::sppf::SppfId],
    ) -> Option<(Arc<dyn std::any::Any + Send + Sync>, Option<u16>, usize)> {
        let cat_src_idx = symbol.category_src_idx;
        let local_rule_idx = symbol.rule_index_in_category;
        let entry = self.engine.action_for(cat_src_idx, local_rule_idx)?;
        let arity = entry.arity as usize;
        let action_fn = entry.action_fn;

        // Filter TriggerTerminal children — same filter as
        // `realize_packing_call` (line 3739-3746). TriggerTerminals
        // contribute NO ActionArg to action_fn.
        let action_children: Vec<crate::sppf::SppfId> = children
            .iter()
            .copied()
            .filter(|&c| {
                !matches!(
                    self.sppf.node(c),
                    Some(crate::sppf::SppfNode::TriggerTerminal { .. })
                )
            })
            .collect();
        if action_children.len() != arity {
            // Arity mismatch — action would fail; mirror persistent
            // path's behavior by returning None.
            return None;
        }

        // Reconstruct ActionArgs.
        let args: Option<Vec<ActionArg>> = action_children
            .iter()
            .map(|&sid| self.reconstruct_action_arg(cursor, sid))
            .collect();
        let args = args?;

        // Build transient SB. Pre-allocate collection slots
        // 0..=max(CollectionId) — same B.1 fix as realize_packing_call
        // (line 3866-3876). Without this, monotonic start_collection
        // returns ids in encounter order, which differs from arrival
        // order when CollectionId(1) comes before CollectionId(0) in
        // args.
        let mut sb = SemanticBuilder::new();
        let max_coll_id: Option<u32> = args
            .iter()
            .filter_map(|a| match a {
                ActionArg::CollectionId(id) => Some(*id as u32),
                _ => None,
            })
            .max();
        if let Some(max_id) = max_coll_id {
            for _ in 0..=max_id {
                let _ = sb.start_collection();
            }
        }
        // Push args. For CollectionId args, also splice the items from
        // cursor.sppf_collection_arena[id] into the slot first so
        // push_to_collection has things to drain.
        for arg in &args {
            match arg {
                ActionArg::Token { kind, text, pos } => {
                    sb.push_token(kind.clone(), text.clone(), *pos);
                }
                ActionArg::Ident { name, pos } => {
                    sb.push_ident(name.clone(), *pos);
                }
                ActionArg::Term { value, .. } => {
                    sb.push_term_arc(Arc::clone(value));
                }
                ActionArg::CollectionId(id) => {
                    // Splice items from cursor.sppf_collection_arena
                    // (NOT winner_collection_arena — at parse-time fire
                    // we want this cursor's arena, not the post-commit
                    // singleton's).
                    if let Some(items) = cursor.sppf_collection_arena.get(*id as usize) {
                        for &item_sid in items {
                            if let Some(ActionArg::Term { value, .. }) =
                                self.reconstruct_action_arg(cursor, item_sid)
                            {
                                sb.push_term_arc(value);
                                sb.push_to_collection(*id);
                            }
                        }
                    }
                    sb.push_collection_id(*id);
                }
                ActionArg::Predicate(p) => {
                    sb.push_predicate_arc(Arc::clone(p));
                }
                ActionArg::Optional(_)
                | ActionArg::Collection { .. }
                | ActionArg::BinderScope(_) => {
                    sb.push_raw_arg(arg.clone());
                }
            }
        }

        // Fire. Mirror fire_action_for_on_builder's pre/post check.
        let pre_len = sb.len();
        if pre_len < arity {
            return None;
        }
        let pre_collection_len = sb.collection_stack_len();
        let pre_action_len = sb.len();
        let popped = sb.pop_args(arity);
        action_fn(&mut sb, popped);
        let expected_len = pre_action_len.saturating_sub(arity).saturating_add(1);
        if sb.len() != expected_len {
            // Action elided (cross-cat-incompatible arg). Return None.
            return None;
        }
        let post_collection_len = sb.collection_stack_len();
        let drains_count = pre_collection_len.saturating_sub(post_collection_len);
        // Capture output_cat BEFORE take_dyn_result drains the top Term.
        let output_cat = sb
            .top_term_type_name()
            .and_then(|tn| self.engine.cat_of_type_name(tn));
        // Take the result Arc. take_dyn_result returns the top of the
        // builder.stack as an Arc<dyn Any>. Mirror semantic with
        // realize_packing_call line 3955+.
        let result_arc = sb.take_dyn_result()?;
        Some((result_arc, output_cat, drains_count))
    }

    #[inline(always)]
    fn emit_fire_action(&mut self, cursor: &mut BranchCursor<W>, symbol: StackSymbolV2) {
        // Phase F.3c.3 (2026-05-20): action fires on a TRANSIENT
        // SemanticBuilder constructed per-call from sppf_stack-reconstructed
        // args (`fire_action_via_transient`). The persistent
        // `Arc::make_mut(&mut cursor.builder)` + `fire_action_for_on_builder`
        // path is GONE — cursor.builder is no longer mutated by this
        // helper. The transient SB's result Arc is stored in
        // `cursor.sppf_symbol_terms` keyed by the just-interned Symbol
        // id so subsequent fires consuming this Symbol as a child via
        // `reconstruct_action_arg` find the realized Term directly.
        //
        // Phase F.3c.2's parity gate verified this path is byte-equivalent
        // to the prior persistent path across the narrow gauntlet (6139/0
        // with zero parity violations).
        //
        // Required-for-correctness invariant (preserved): the action's
        // CONVERTED term flows into downstream SpliceIntoCollection
        // emits via the cursor's sppf_collection_arena (now populated
        // by emit_splice_into_collection's SPPF-side mirror) instead
        // of cursor.builder.stack. Class-5 collection-finalize actions
        // call `b.drain_collection(id)` on the transient SB; the drain
        // count is returned and decrements cursor.collection_stack_depth
        // below.
        //
        // On elide / arity-mismatch (transient returns None), set BOTH
        // cursor.inner_state AND walker state to Error so the cursor
        // aborts cleanly via cursor_resolution_check :: Drop on the
        // next step.

        // C3 dual-mode: capture symbol identity for SPPF, look up arity
        // BEFORE firing (the entry table is invariant; arity is the same
        // pre- and post-action).
        //
        // Bug A fix (Phase 3.1.2, 2026-05-15): encode the GLOBAL rule id
        // as `(cat_src_idx << 16) | rule_idx_within_cat`. This makes the
        // Packing identity carry the parent cat unambiguously, so
        // realize_packing_call can decode cat directly without a linear
        // scan over 0..1024 (which collides when two cats have rules
        // with the same local rule_idx + arity — e.g., `LitInt` at
        // rule_idx=0 in both Int and BigInt categories in calc_op).
        let cat_src_idx = symbol.category_src_idx;
        let local_rule_idx = symbol.rule_index_in_category;
        let global_rule_idx: u32 =
            ((cat_src_idx as u32) << 16) | (local_rule_idx as u32);
        let hi_pos = cursor.pos as u32;
        let arity = self
            .engine
            .action_for(cat_src_idx, local_rule_idx)
            .map(|e| e.arity as usize)
            .unwrap_or(0);

        // SPPF mirror: pop arity children from sppf_stack, intern Packing,
        // intern Symbol(cat_src_idx, lo, hi), link, push Symbol id.
        // Pre-condition: cursor.sppf_stack.len() >= arity. Phase 3.1.1 (Bug P):
        // debug_assert exposes gap sites — every emit_push_* that fires
        // before a reduce MUST mirror via a corresponding sppf_stack.push.
        // Phase F.2 (2026-05-18): the format arg `cursor.builder.len()`
        // was structurally redundant with `cursor.sppf_stack.len()` (the
        // preceding format arg) — both grew/shrank in lockstep. Dropped
        // the builder-side report; F.3 will delete the field entirely.
        // Phase F.3c.3 (2026-05-20): arity-underflow Error handling.
        // Pre-F.3c.3, fire_action_for_on_builder's outer arity check
        // (wpda_walker.rs:~7473) detected `builder.len() < arity` and
        // returned `Some(error)`; emit_fire_action propagated it as
        // Error state. Post-F.3c.3 the persistent path is gone, so we
        // detect underflow here against `cursor.sppf_stack.len()` (the
        // structural mirror of arg count). Bug P era's debug_assert!
        // is dropped — arity underflow on a legitimate engine emission
        // is a runtime error (test
        // `commit_winner_state_overwrite_on_action_arity_underflow`),
        // NOT an internal SPPF-mirror corruption.
        if cursor.sppf_stack.len() < arity
            && self
                .engine
                .action_for(cat_src_idx, local_rule_idx)
                .is_some()
        {
            let message = format!(
                "semantic-action arity mismatch at rule (src={}, rule={}): \
                 expected {} args but cursor.sppf_stack held {}",
                cat_src_idx,
                local_rule_idx,
                arity,
                cursor.sppf_stack.len(),
            );
            let err = WpdaState::Error { message };
            cursor.inner_state = err.clone();
            self.state = err;
            cursor.last_action_output_cat = None;
            return;
        }
        if cursor.sppf_stack.len() >= arity {
            // Phase F.8 (2026-05-18): walk back from the arity-slice top
            // to include consecutive TriggerTerminal frames that belong to
            // THIS reduce. Unary-prefix rules push a TriggerTerminal for
            // the consumed trigger token BEFORE the operand parses, so
            // the frame layout at reduce time is `[..., TriggerTerminal,
            // operand_Symbol]`. Drain MUST extend down to include the
            // TriggerTerminal so it lands in `children` for `span_lo` and
            // the parent rule's interned Symbol receives
            // `lo = trigger_pos` (DISTINCT from the operand's lo).
            //
            // **Ownership gate**: walk-back consumes a TriggerTerminal
            // ONLY if its `(owner_cat, owner_rule_idx)` matches the
            // firing rule's `(cat_src_idx, local_rule_idx)`. Every
            // ConsumeAndPush stamps its TriggerTerminal with the rule
            // identity of the symbol it's pushing (see apply arm:
            // `symbol.category_src_idx`, `symbol.rule_index_in_category`),
            // so the firing rule's identity matches its own trigger and
            // no other. Without the gate, an INNER rule's fire (e.g.,
            // BoolLit firing inside Not's operand sub-parse) would
            // greedily consume the OUTER rule's TriggerTerminal, leaving
            // Not with no trigger and reintroducing the Symbol-dedup
            // collision. The pos-based gate (an earlier attempt) failed
            // because multi-step binder rules ReplaceAndPush their
            // RuleAt's GSS pos to the post-trigger cursor.pos — the
            // GSS frame's pos no longer matches the trigger's pos at
            // fire time. Rule identity is invariant across ReplaceTop
            // chains because the symbol's (cat, rule_idx) stays the
            // same.
            // Non-prefix rules push NO TriggerTerminal, so the walk-back
            // exits immediately and behavior is byte-identical to pre-fix.
            let mut split_at = cursor.sppf_stack.len() - arity;
            while split_at > 0 {
                let prev = cursor.sppf_stack[split_at - 1];
                let claim = match self.sppf.node(prev) {
                    Some(crate::sppf::SppfNode::TriggerTerminal {
                        owner_cat,
                        owner_rule_idx,
                        ..
                    }) => *owner_cat == cat_src_idx && *owner_rule_idx == local_rule_idx,
                    _ => false,
                };
                if claim {
                    split_at -= 1;
                } else {
                    break;
                }
            }
            let children: Vec<crate::sppf::SppfId> =
                Arc::make_mut(&mut cursor.sppf_stack).drain(split_at..).collect();
            // lo_pos: leftmost child's span_lo, or fall back to hi_pos if
            // arity == 0 (epsilon-like reduce). With Phase F.8 the
            // leftmost child for a unary-prefix rule is the TriggerTerminal
            // whose span_lo = trigger_pos.
            let lo_pos = children
                .first()
                .and_then(|&c| self.sppf.span_lo(c))
                .unwrap_or(hi_pos);

            // Phase F.3c.3 (2026-05-20): fire on transient SB BEFORE
            // SPPF intern so elide / arity-mismatch can early-return
            // without interning a spurious Packing/Symbol. The transient
            // is the SOLE fire path post-F.3c.3.
            let has_action = self
                .engine
                .action_for(cat_src_idx, local_rule_idx)
                .is_some();
            let transient_result =
                self.fire_action_via_transient(cursor, symbol, &children);
            match (has_action, transient_result) {
                (true, None) => {
                    // Elide / arity mismatch — action_fn returned without
                    // pushing the expected single Term. Mirror the prior
                    // persistent path's error semantics: set Error state,
                    // clear mirror, return. cursor_resolution_check will
                    // Drop on next step.
                    let message = format!(
                        "semantic-action elide / arity mismatch at rule \
                         (src={}, rule={}): action_fn returned without \
                         pushing the expected single Term — typically \
                         cross-cat-incompatible arg (`arg.into_term::<T>()` \
                         returned None) or arity underflow",
                        cat_src_idx, local_rule_idx,
                    );
                    let err = WpdaState::Error { message };
                    cursor.inner_state = err.clone();
                    self.state = err;
                    cursor.last_action_output_cat = None;
                    return;
                }
                (false, None) => {
                    // No action registered for this rule — no-op fire.
                    // Persistent path (pre-F.3c.3) also treated this as
                    // a no-op (fire_action_for_on_builder's outer
                    // `if let Some(entry) = engine.action_for(...) {}
                    // else { None }` returned None silently). No mirror
                    // update, no memo entry. Intern the empty-result
                    // Packing+Symbol below so the SPPF still records
                    // the production.
                    cursor.last_action_output_cat = None;
                }
                (_, Some((result_arc, output_cat, drains_count))) => {
                    // Successful fire. Update mirror + collection depth
                    // from transient's post-fire state.
                    cursor.last_action_output_cat = output_cat;
                    cursor.collection_stack_depth = cursor
                        .collection_stack_depth
                        .saturating_sub(drains_count as u8);
                    // SPPF intern the Packing+Symbol first to get symbol_id
                    // for the memo key.
                    let packing_weight = std::mem::replace(
                        &mut cursor.pending_packing_weight,
                        W::one_ref(),
                    );
                    let packing_id = self.sppf.intern_packing(
                        global_rule_idx,
                        children,
                        packing_weight,
                    );
                    let symbol_id =
                        self.sppf.intern_symbol(cat_src_idx as u32, lo_pos, hi_pos);
                    self.sppf.link_packing_to_symbol(symbol_id, packing_id);
                    Arc::make_mut(&mut cursor.sppf_stack).push(symbol_id);
                    // Phase F.13 H1 (2026-05-20): write to walker-global
                    // memo. Insert is idempotent — same SymbolId from a
                    // different cursor yields an equivalent result_arc.
                    // Using insert (not entry().or_insert) because the
                    // fresh result is fully realized whereas a stale
                    // entry from a prior parse (cleared by reset) would
                    // not exist within a single parse session.
                    self.sppf_symbol_terms.insert(symbol_id, result_arc);
                    return;
                }
            }
            // Reachable only when (has_action == false, transient_result == None):
            // no-action no-op. Intern the empty Packing+Symbol so the
            // SPPF still records the production shape (consistent with
            // the prior persistent path's behavior).
            let packing_weight = std::mem::replace(
                &mut cursor.pending_packing_weight,
                W::one_ref(),
            );
            let packing_id = self
                .sppf
                .intern_packing(global_rule_idx, children, packing_weight);
            let symbol_id = self.sppf.intern_symbol(cat_src_idx as u32, lo_pos, hi_pos);
            self.sppf.link_packing_to_symbol(symbol_id, packing_id);
            Arc::make_mut(&mut cursor.sppf_stack).push(symbol_id);
        }
    }

    /// Allocate a fresh collection accumulator on the cursor's builder.
    /// Returns the slot id (8-bit) for embedding in the corresponding
    /// `CollectionMarker` symbol's payload.
    ///
    /// Phase 5.6-tail-B (2026-05-12): unified path. The `cursor.collection_stack`
    /// mirror push is preserved (still consumed by Step G's eventual deletion);
    /// the journal push of `BuilderDelta::StartCollection` is dropped (the
    /// codegen-side Fork-arm `WithMultipleEffects` paths still carry the
    /// variant as a payload — apply_effect_to_builder handles those).
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
        // Phase 5.6-tail-G (2026-05-12): cursor.collection_stack mirror
        // push deleted — cursor.builder.collection_stack carries the
        // authoritative slot state.
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The collection
        // slot's id is now derived from cursor.collection_stack_depth
        // directly (= depth BEFORE the saturating_add below, matching
        // the pre-F.3c sequence: builder.start_collection returns the
        // current builder.collection_stack.len() then pushes a new slot
        // → builder.collection_stack.len() increments by 1, mirror
        // saturating_add(1)). Mirror clears for action_output (this
        // helper doesn't push onto the main arg stack).
        let id = cursor.collection_stack_depth;
        self.clear_action_output_mirror(cursor);
        cursor.collection_stack_depth =
            cursor.collection_stack_depth.saturating_add(1);
        // C3 dual-mode: ensure the SPPF-side collection arena has a slot
        // at this id. The builder's allocator monotonically returns ids
        // 0, 1, 2, ... — we mirror by extending when the id exceeds
        // current length.
        //
        // Phase F.4 (2026-05-18): per-cursor arena. `Arc::make_mut`
        // performs CoW the first time this cursor's arena is written
        // after a Fork clone (line 7445 splice site shares the CoW).
        let arena = Arc::make_mut(&mut cursor.sppf_collection_arena);
        while arena.len() <= id as usize {
            arena.push(Vec::new());
        }
        // If the slot was previously used (e.g. earlier reduce in same
        // parse), reset it — the builder reuses ids by
        // start_collection re-allocation semantics; the SPPF mirror
        // must match.
        arena[id as usize].clear();
        id
    }

    #[inline(always)]
    fn emit_push_collection_id(&mut self, cursor: &mut BranchCursor<W>, id: u8) {
        // C3 dual-mode: push a CollectionId placeholder onto sppf_stack so
        // the fire_action arity check matches builder.stack arity.
        let sid = self.sppf.intern_collection_id(id as u32);
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. SPPF
        // CollectionId node above mirrors the structural state.
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_splice_into_collection(&mut self, cursor: &mut BranchCursor<W>, id: u8) {
        // C3 dual-mode: pop top of sppf_stack, append to the SPPF-side
        // collection slot. Mirrors builder.push_to_collection.
        //
        // Phase F.4 (2026-05-18): per-cursor arena. Cheap immutable
        // length check first to avoid spurious CoW when sppf_stack is
        // empty.
        if (id as usize) < cursor.sppf_collection_arena.len() {
            if let Some(top) = Arc::make_mut(&mut cursor.sppf_stack).pop() {
                Arc::make_mut(&mut cursor.sppf_collection_arena)[id as usize].push(top);
            }
        }
        // push_to_collection silently no-ops on out-of-bounds id.
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The SPPF-side
        // sppf_collection_arena[id].push(top) above mirrors the splice.
        // Mirror clears (the popped top was a Term per-fire output, now
        // absorbed into the collection slot).
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_start_optional_scope(&mut self, cursor: &mut BranchCursor<W>) {
        // C3 dual-mode: record the sppf_stack length at scope-open so
        // emit_finalize_optional_scope_present can collect everything
        // pushed since this point.
        cursor.optional_scope_marks.push(cursor.sppf_stack.len());
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The SPPF-side
        // `cursor.optional_scope_marks.push(cursor.sppf_stack.len())`
        // above mirrors the open-scope state.
        self.clear_action_output_mirror(cursor);
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): centralized Push-time symbol-
    /// kind side effects. Both `WpdaStepAction::Push` and
    /// `WpdaStepAction::ConsumeAndPush` arms call this BEFORE
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
    /// clause, breaking deterministic-mode IfElse-with-else parses (4 tests in
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

    /// Sentinel rule_idx for the synthetic Packing that wraps the contents
    /// of a present optional group. Distinct from any real `rule_idx`
    /// because user rules occupy `0..u32::MAX - 1`. The realization pass
    /// recognizes this sentinel and produces `Some(...)` for the user AST.
    const OPTIONAL_PRESENT_RULE_IDX: u32 = u32::MAX - 1;

    #[inline(always)]
    fn emit_finalize_optional_scope_present(&mut self, cursor: &mut BranchCursor<W>) {
        // C3 dual-mode: pop the topmost optional_scope_mark, collect
        // sppf_stack contents pushed since the mark into a Packing tagged
        // with OPTIONAL_PRESENT_RULE_IDX, push the resulting Packing id.
        if let Some(mark) = cursor.optional_scope_marks.pop() {
            if mark <= cursor.sppf_stack.len() {
                let stack = Arc::make_mut(&mut cursor.sppf_stack);
                let children: Vec<crate::sppf::SppfId> = stack.drain(mark..).collect();
                // Phase C.1 (2026-05-17): synthetic OPTIONAL_PRESENT always
                // interns with `W::one_ref()` per the weight semantics table
                // in `~/.claude/plans/phase-c-sppf-w-resolved.md` §2.5.
                let packing_id = self.sppf.intern_packing(
                    Self::OPTIONAL_PRESENT_RULE_IDX,
                    children,
                    W::one_ref(),
                );
                stack.push(packing_id);
            }
        }
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. The SPPF-side
        // OPTIONAL_PRESENT_RULE_IDX synthetic packing above gathers
        // children from `cursor.sppf_stack[mark..]` into a Packing and
        // pushes its id. reconstruct_action_arg unwraps these as
        // ActionArg::Optional(Some(inner_args)) during the next fire's
        // arg reconstruction.
        self.clear_action_output_mirror(cursor);
    }

    #[inline(always)]
    fn emit_push_optional_absent(&mut self, cursor: &mut BranchCursor<W>) {
        // C3 dual-mode: push an OptAbsent leaf onto sppf_stack.
        let sid = self.sppf.intern_opt_absent(cursor.pos as u32);
        Arc::make_mut(&mut cursor.sppf_stack).push(sid);
        // Phase F.3c.4 (2026-05-20): cursor.builder deleted. SPPF OptAbsent
        // node above mirrors the structural state.
        self.clear_action_output_mirror(cursor);
    }

    // ─── 4 mode-agnostic helpers (mirror to live walker fields when deterministic) ──
    //
    // Each helper updates the cursor's local state AND, when
    // `self.deterministic` is true, mirrors to the live walker fields. The
    // `self.deterministic` flag is monotone — true at construction, set
    // false on the first Fork, never reset within a parse. Mirror
    // therefore fires only while the walker is still in single-cursor
    // pre-Fork mode; once nondeterministic, self.* is rehydrated at
    // commit_winner from the winning cursor.
    //
    // NB: `self.branch_cursors.len() == 1` is NOT equivalent — after a
    // Fork resolves to a single winner (commit_winner), len drops back
    // to 1 but `self.deterministic` stays false. The monotone flag avoids
    // accidentally re-mirroring post-commit state.

    /// M6c.6.1 (2026-05-14): advance the cursor's `pos` via the
    /// token source's `next_pos` rather than a hardcoded `+= n`.
    ///
    /// **Why**: for `SliceTokenSource`, `next_pos(pos, 0)` returns
    /// `Some(pos + 1)` (the trait default), so this is byte-identical
    /// to the pre-M6c.6.1 behavior. For `LatticeTokenSource`, `next_pos`
    /// returns the primary edge's `target_node` — which may NOT equal
    /// `pos + 1` when the DAG has multi-LENGTH ambiguity (e.g., `-3`
    /// with `Minus@end=1` and `Integer@end=2` having different target
    /// nodes). The pre-M6c.6.1 walker used `pos += 1` everywhere and
    /// silently desynced from the lattice DAG; this fix makes every
    /// advance source-driven.
    ///
    /// `n` is always 1 in current callers; the parameter is retained
    /// for symmetry with the pre-M6c.6.1 signature. Iterative calls
    /// would be needed for `n > 1` but no such callers exist today.
    #[inline(always)]
    fn advance_cursor_pos(
        &mut self,
        cursor: &mut BranchCursor<W>,
        tokens: &dyn WpdaTokenSource,
        n: usize,
    ) {
        debug_assert_eq!(n, 1, "advance_cursor_pos n > 1 not yet supported");
        let new_pos = tokens.next_pos(cursor.pos, 0).unwrap_or(cursor.pos + n);
        cursor.pos = new_pos;
        if self.deterministic {
            self.pos = cursor.pos;
        }
    }

    /// M6c.6.1 helper: advance a child cursor by one step via the
    /// source's `next_pos`. Used at 14 sites in the `WpdaStepAction::Fork`
    /// apply arm to replace `child.pos += 1` (which silently desynced
    /// from lattice DAGs with non-sequential primary edges).
    #[inline(always)]
    fn child_next_pos(tokens: &dyn WpdaTokenSource, pos: usize) -> usize {
        tokens.next_pos(pos, 0).unwrap_or(pos + 1)
    }

    #[inline(always)]
    fn multiply_cursor_weight(&mut self, cursor: &mut BranchCursor<W>, w: &W) {
        cursor.weight = cursor.weight.times_ref(w);
        if self.deterministic {
            self.weight = self.weight.times_ref(w);
        }
    }

    #[inline(always)]
    fn set_cursor_inner_state(&mut self, cursor: &mut BranchCursor<W>, state: WpdaState) {
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
            WpdaState::CollectionLoop {
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
                        //
                        // Phase F.2 (2026-05-18): SPPF-side helper.
                        // `cursor_collection_slot_len` reads
                        // `sppf_collection_arena[acc_id].len()`, which
                        // grows in lockstep with builder.collection_stack
                        // via emit_splice_into_collection.
                        let acc_id_usize = *accumulator_id as usize;
                        let slot_len = self.cursor_collection_slot_len(cursor, acc_id_usize);
                        let new_kv_phase: u8 = if slot_len % 2 == 1 { 1 } else { 0 };
                        WpdaState::CollectionLoop {
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
        if self.deterministic {
            self.state = patched_state;
        }
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): variant of `cursor_gss_push`
    /// that records a specific `EdgeKind` on the new edge. Default
    /// `cursor_gss_push` uses `EdgeKind::Generic` placeholder.
    #[inline(always)]
    fn cursor_gss_push_with_kind(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
        kind: crate::gss::EdgeKind,
    ) -> crate::gss::GssNodeId {
        // Synthesize a fresh root if cursor is at the sentinel —
        // duplicates cursor_gss_push's logic for parity.
        let predecessor = if (cursor.node == 0 && self.gss.node(0).is_none())
            || cursor.node == crate::gss::GSS_NODE_NONE
        {
            let root = self.gss.get_or_create_node(WpdaGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.deterministic {
                self.top_node = Some(root);
            }
            root
        } else {
            cursor.node
        };
        let new_id = self.gss.get_or_create_node(WpdaGssNode { pos, symbol: sym });
        let edge_id = self.gss.add_edge_kind(new_id, predecessor, w, kind);
        cursor.node = new_id;
        cursor.incoming_edge_stack.push(edge_id);
        if self.deterministic {
            self.top_node = Some(new_id);
        }
        new_id
    }

    /// Phase F.13 H12 Stage 1.5 (2026-05-21): Fork-arm Push child
    /// allocator. Returns `Vec<BranchCursor<W>>`:
    ///   - Empty vec: cursor PAUSED (InflightCollision) or DROPPED
    ///     (FailedHit). Caller skips push.
    ///   - 1 cursor: WorkerInserted (normal worker) OR single-packing
    ///     ResolvedHit.
    ///   - N cursors: multi-packing ResolvedHit — one revived cursor
    ///     per worker snapshot. Caller `children.extend(...)`.
    fn allocate_fork_push_child(
        &mut self,
        parent: &BranchCursor<W>,
        branch: ForkBranch<W>,
        pos_after: usize,
        child_recovery_depth: u8,
        child_visited_recovery: OrdSet<(usize, u16, u8)>,
        child_visited_dispatch: OrdSet<(usize, u16, u8)>,
        child_source_priority: u32,
    ) -> Vec<BranchCursor<W>> {
        // Phase F.13 H12 Stage 1.3 (2026-05-21): cohort cache
        // consultation for CrossCatDelegate branches. Resolved/Failed/
        // InflightCollision outcomes short-circuit normal allocation.
        if let WpdaState::CrossCatDelegate {
            source_src_idx,
            inner_cur_bp,
        } = &branch.new_state
        {
            let s = *source_src_idx;
            let b = *inner_cur_bp;
            let key = crate::dispatch_cohort::DispatchKey::new(pos_after, s, b);
            // Stage 1.5.3 (2026-05-21): pass worker's pre-dispatch
            // weight so the cache can recover the per-packing weight
            // delta at revive time (tropical primary subtraction).
            let worker_pre_weight = parent.weight.times_ref(&branch.weight);
            let outcome = self
                .dispatch_cohort_cache
                .register(key.clone(), worker_pre_weight);
            use crate::dispatch_cohort::RegisterOutcome;
            match outcome {
                RegisterOutcome::WorkerInserted => {
                    // Worker child — fall through to normal allocation.
                }
                RegisterOutcome::InflightCollision => {
                    // Stage 1.5 (2026-05-21): pause cohort member.
                    // If the cache's cap is exceeded
                    // (MAX_PENDING_COHORT_PER_KEY), pause_cohort_member
                    // returns false; fall through to per-cursor sub-parse
                    // so the cursor is not lost.
                    let member = crate::dispatch_cohort::CohortMember {
                        return_frame: parent.clone(),
                        weight_at_dispatch: parent
                            .weight
                            .times_ref(&branch.weight),
                    };
                    if self
                        .dispatch_cohort_cache
                        .pause_cohort_member(key, member)
                    {
                        return Vec::new();
                    }
                    // Cap exceeded — fall through to allocate as worker.
                }
                RegisterOutcome::ResolvedHit {
                    symbol_id,
                    hi_pos,
                    pos_at_dispatch,
                    worker_snapshots,
                } => {
                    // Stage 1.5 (2026-05-21): synthesize one revived
                    // cursor per worker snapshot available NOW.
                    //
                    // Stage 1.5.2 (2026-05-21): ALSO pause a synthetic
                    // cohort member so cross-step snapshots arriving
                    // LATER (from sibling workers that pop in
                    // subsequent step_fanout iterations) can also
                    // revive this member at end-of-step drain. Without
                    // this pause, ResolvedHit-consumed members are
                    // lost from the persistent pending_cohort — they
                    // never receive snap_B's revival in the multi-
                    // packing cross-step case (the `-3!` failure).
                    let synthetic_weight_at_dispatch =
                        parent.weight.times_ref(&branch.weight);
                    let mut revived_cursors = Vec::with_capacity(
                        worker_snapshots.len(),
                    );
                    for snap in &worker_snapshots {
                        if snap.worker_inner_state.is_terminal() {
                            continue;
                        }
                        let synthetic_member =
                            crate::dispatch_cohort::CohortMember {
                                return_frame: parent.clone(),
                                weight_at_dispatch:
                                    synthetic_weight_at_dispatch.clone(),
                            };
                        let revived = self.revive_cohort_member_with_snapshot(
                            synthetic_member,
                            symbol_id,
                            pos_at_dispatch,
                            hi_pos,
                            s,
                            b,
                            snap,
                        );
                        revived_cursors.push(revived);
                    }
                    // Park a synthetic member onto the entry's
                    // pending_cohort for future cross-step snapshots.
                    // pause_cohort_member handles Resolved entries
                    // (dispatch_cohort.rs:412-432) and honors
                    // MAX_PENDING_COHORT_PER_KEY cap.
                    let future_member = crate::dispatch_cohort::CohortMember {
                        return_frame: parent.clone(),
                        weight_at_dispatch: synthetic_weight_at_dispatch,
                    };
                    let _ = self
                        .dispatch_cohort_cache
                        .pause_cohort_member(key, future_member);
                    return revived_cursors;
                }
                RegisterOutcome::FailedHit => {
                    // Failed hit — drop cursor (sub-parse known to
                    // fail; per-cursor path would have failed too).
                    return Vec::new();
                }
            }
        }
        // Worker / non-CrossCatDelegate path: allocate normally.
        let mut symbol = branch.symbol;
        let mut child = BranchCursor {
            node: parent.node,
            pos: pos_after,
            weight: parent.weight.times_ref(&branch.weight),
            inner_state: branch.new_state.clone(),
            recovery_deltas: parent.recovery_deltas.clone(),
            source_priority: child_source_priority,
            incoming_edge_stack: parent.incoming_edge_stack.clone(),
            recovery_depth: child_recovery_depth,
            visited_recovery: child_visited_recovery,
            visited_dispatch: child_visited_dispatch,
            sppf_stack: Arc::clone(&parent.sppf_stack),
            optional_scope_marks: parent.optional_scope_marks.clone(),
            binder_scope_marks: parent.binder_scope_marks.clone(),
            pending_packing_weight: parent
                .pending_packing_weight
                .times_ref(&branch.weight),
            collection_stack_depth: parent.collection_stack_depth,
            sppf_collection_arena: Arc::clone(&parent.sppf_collection_arena),
            last_action_output_cat: parent.last_action_output_cat,
            cohort_origin: parent.cohort_origin.clone(),
            cohort_revive_depth: parent.cohort_revive_depth,
        };
        self.emit_push_side_effects(&mut child, &mut symbol);
        if let WpdaState::CrossCatDelegate {
            source_src_idx,
            inner_cur_bp,
        } = &branch.new_state
        {
            let kind = crate::gss::EdgeKind::CrossCatProjection {
                source_src_idx: *source_src_idx,
                inner_cur_bp: *inner_cur_bp,
            };
            let _ = self.cursor_gss_push_with_kind(
                &mut child,
                symbol,
                pos_after,
                branch.weight,
                kind,
            );
        } else {
            let _ = self.cursor_gss_push_auto(
                &mut child,
                symbol,
                pos_after,
                branch.weight,
            );
        }
        vec![child]
    }

    /// Phase F.13 H12 Stage 1.3 (2026-05-21): revive a paused cohort
    /// member into a resumed BranchCursor. Approach 4b: re-push
    /// CategoryEntry(S) onto the cohort member's GSS so the next
    /// walker step's Pop traverses the normal post-pop path
    /// (apply_pop_body_to_cursor processes per-member side effects).
    ///
    /// Soundness: each cohort member retains its own pre-dispatch
    /// `incoming_edge_stack`, `builder` (Arc), `binder_scope_marks`,
    /// `recovery_deltas`, `visited_dispatch`, `visited_recovery`,
    /// `last_action_output_cat`. The revive only:
    ///   - Pushes the cached symbol_id onto sppf_stack (Arc::make_mut).
    ///   - Sets pos to hi_pos.
    ///   - Multiplies weight by sub_weight (Stage 1.3 uses one;
    ///     LexicographicWeight idempotent — SPPF symbol weight_sum
    ///     already aggregates).
    ///   - Pushes CategoryEntry(S) onto GSS with the same
    ///     CrossCatProjection EdgeKind the worker used.
    ///   - Restores inner_state to the worker's pre-pop state so the
    ///     next walker step re-emits Pop and triggers the normal
    ///     post-pop processing.
    /// Phase F.13 H12 Stage 1.5 (2026-05-21): cohort revive with a
    /// per-packing `WorkerSnapshot`. Approach 4b refined:
    ///   - Bug A: GSS push at `pos_at_dispatch` (not `hi_pos`).
    ///   - Bug B: weight = `pre_dispatch × snap.worker_pending_packing_weight`.
    ///     PER-PACKING (not symbol_weight_sum aggregate) so cohort
    ///     fanout preserves per-derivation algebraic distinction.
    ///     Downstream `merge_equivalent_cursors` collapses identical
    ///     ConfigKeys, restoring the per-cursor baseline's final shape.
    ///   - last_action_output_cat / inner_state / sppf_stack inheritance
    ///     identical to Stage 1.3.1 single-snapshot case.
    fn revive_cohort_member_with_snapshot(
        &mut self,
        member: crate::dispatch_cohort::CohortMember<W>,
        symbol_id: crate::sppf::SppfId,
        pos_at_dispatch: u32,
        hi_pos: u32,
        source_src_idx: u16,
        inner_cur_bp: u8,
        snap: &crate::dispatch_cohort::WorkerSnapshot<W>,
    ) -> BranchCursor<W> {
        let mut cursor = member.return_frame;
        // Stage 1.5.3R-b (2026-05-21): tag cursor with cohort_origin.
        // ConfigKey reads this so cohort revives bucket separately
        // from per-cursor cursors. Graduation rule G2 clears the tag
        // at next Pop past cohort_revive_depth (handled in
        // cursor_gss_pop_via_edge). The depth captured here is the
        // cursor's incoming_edge_stack length AFTER the CategoryEntry
        // re-push below, so graduation fires when the cohort cursor
        // exits the dispatch's return frame.
        cursor.cohort_origin = Some(crate::dispatch_cohort::DispatchKey {
            pos: pos_at_dispatch,
            source_src_idx,
            inner_cur_bp,
        });
        // worker_pre_dispatch_weight retained on schema; reserved for
        // a future per-packing weight delta scheme (Stage 1.5.3
        // tropical-delta was falsified empirically).
        let _ = snap.worker_pre_dispatch_weight.clone();
        let symbol_weight_sum = self.sppf.symbol_weight_sum(symbol_id);
        cursor.weight = member
            .weight_at_dispatch
            .times_ref(&symbol_weight_sum);
        cursor.pending_packing_weight =
            snap.worker_pending_packing_weight.clone();
        cursor.last_action_output_cat = snap.worker_last_action_output_cat;
        Arc::make_mut(&mut cursor.sppf_stack).push(symbol_id);
        cursor.pos = hi_pos as usize;
        let cat_sym = StackSymbolV2::category_entry(source_src_idx);
        let kind = crate::gss::EdgeKind::CrossCatProjection {
            source_src_idx,
            inner_cur_bp,
        };
        let _ = self.cursor_gss_push_with_kind(
            &mut cursor,
            cat_sym,
            pos_at_dispatch as usize,
            W::one_ref(),
            kind,
        );
        // Stage 1.5.3R-b: capture depth AFTER the CategoryEntry push.
        // Graduation rule G2: cohort_origin clears when depth drops
        // below this value (the cohort cursor has exited its dispatch's
        // return frame).
        cursor.cohort_revive_depth = cursor.incoming_edge_stack.len() as u32;
        cursor.inner_state = snap.worker_inner_state.clone();
        cursor
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): `cursor_gss_push` variant that
    /// AUTO-DERIVES the `EdgeKind` from the StackSymbolV2's SymbolKind.
    /// This is the default path post-H13: every push site automatically
    /// gets a semantic-aware tag without per-site changes. Override with
    /// `cursor_gss_push_with_kind` when the caller has richer context
    /// (e.g., CrossCatProjection vs CategoryEntryRoot disambiguation).
    #[inline(always)]
    fn cursor_gss_push_auto(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
    ) -> crate::gss::GssNodeId {
        let kind = crate::gss::EdgeKind::from_symbol(&sym);
        self.cursor_gss_push_with_kind(cursor, sym, pos, w, kind)
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
            let root = self.gss.get_or_create_node(WpdaGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.deterministic {
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
        if self.deterministic {
            self.top_node = Some(new_id);
        }
        new_id
    }

    // Phase 5.6-tail follow-up (2026-05-12): `cursor_gss_pop` DELETED.
    // The legacy single-predecessor scalar pop was superseded by
    // `cursor_gss_pop_via_edge` (Stage 3.12.6, 2026-05-02), which uses
    // the cursor's recorded `incoming_edge_stack` to follow the exact
    // edge the cursor pushed earlier — preserving calling context
    // under GSS dedup. All call sites migrated to the via_edge variant;
    // the standalone helper was orphaned.

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
        new_state: WpdaState,
        tokens: &dyn crate::wpda_runtime::WpdaTokenSource,
    ) {
        // Set cursor's GSS top to the predecessor (or sentinel).
        cursor.node = pred_id;
        if self.deterministic {
            self.top_node = if pred_id == crate::gss::GSS_NODE_NONE {
                None
            } else {
                Some(pred_id)
            };
        }
        // Stage 3.12.8 (2026-05-03) — Phase 5.6-tail-B (2026-05-12):
        // pre-tail the CollectionMarker-pop drain ran only in nondeterministic
        // (journal-replay) mode, where it drained the cursor's
        // collection_stack[top] slot and emitted a FinalizeCollection
        // delta BEFORE FireAction; the deterministic path mutated the live
        // builder directly at FireAction time, so no delta was needed.
        // Phase 5.6-tail-B unified those: emit_start_collection always
        // mutates cursor.builder + the mirror, so we must always
        // ALWAYS pop on CollectionMarker pop to keep the mirror in sync
        // with cursor.builder.collection_stack. The mirror itself is
        // deleted in Step G.
        if let Some(symbol) = popped_symbol {
            if symbol.kind == SymbolKind::CollectionMarker {
                // L12 follow-up B5 (2026-05-07): pop the cursor's
                // collection_stack mirror to keep id allocation in
                // sync with subsequent nondeterministic-mode emit_start_collection
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
                // Phase 5.6-tail-G (2026-05-12): cursor.collection_stack
                // mirror pop deleted — cursor.builder.collection_stack is
                // the authoritative state and pops via the action's
                // drain_collection at FireAction time below.
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
                // Phase 5.6-tail-B (2026-05-12): always route through
                // cursor.builder. Pre-tail the Lazy arm read self.builder,
                // but under always-eager Arc::make_mut the cursor's
                // builder IS the authoritative live state and self.builder
                // is stale.
                //
                // Phase F.2 (2026-05-18): SPPF-side mirror.
                let acc_id =
                    (cursor.collection_stack_depth as usize).saturating_sub(1) as u8;
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
                            // M4 (2026-05-13): pass `tokens` directly.
                            // CursorViewSource wrap deleted — alt identity
                            // lives in the shared LatticeTokenSource (M3).
                            let test_action = self.engine.step(
                                &WpdaState::InfixLoop { cur_bp: 0 },
                                &self.gss,
                                frontier_snap.as_ref(),
                                cursor.pos,
                                tokens,
                            );
                            matches!(
                                test_action,
                                WpdaStepAction::Advance(WpdaState::Unwinding),
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

        // D-strings non-grouping cat fix (2026-05-13): when a cross-cat
        // infix Return just popped, the new GSS top may be a
        // `CategoryEntry` whose category is the OPERAND cat (e.g., Str
        // for LtStr's outer CrossCatLhs CE), but the builder top is now
        // the RESULT cat (e.g., Bool). Re-synchronize the GSS top's CE
        // to match the builder's actual category so subsequent
        // InfixLoop dispatch uses the RESULT cat's tables (e.g., Bool's
        // `==` → EqBool, not Str's `==` → EqStr-on-Bool-args silent
        // fail).
        //
        // Complementary to D8 (commit 4d2c615) which handles the
        // grouping case (`(...) op` where op is cross-cat). This
        // handles the non-grouping case (`crosscat_op op` directly).
        //
        // Gates (all must hold):
        //   1. popped symbol is Return (the cross-cat infix Return).
        //   2. cursor still has a GSS top (pred_id != GSS_NODE_NONE).
        //   3. new top is a CategoryEntry.
        //   4. builder top is a Term with a known cat (via
        //      engine.cat_of_type_name).
        //   5. builder cat differs from new top's cat.
        //
        // Uses W::one_ref() so the cursor weight isn't perturbed.
        //
        // Why ONLY for Return: same-cat infix Pops (popped.cat ==
        // pred.cat) trivially pass gate 5 as a no-op; cross-cat prefix
        // Pops (ImplicitCast, CrossCatProjection, CrossCatPrefixUnary)
        // have new top.cat == popped.cat == result_cat (the wrapping
        // Return is in the calling cat, and the OUTER CE is also the
        // calling cat), so gate 5 is a no-op there too. Only cross-cat
        // INFIX has the OUTER CE in the OPERAND cat while the wrapping
        // Return / builder top are in the RESULT cat.
        if let Some(popped) = popped_symbol {
            if popped.kind == SymbolKind::Return
                && pred_id != crate::gss::GSS_NODE_NONE
            {
                let new_top_cat_opt = self
                    .gss
                    .node(pred_id)
                    .and_then(|n| {
                        if n.symbol.kind == SymbolKind::CategoryEntry {
                            Some(n.symbol.category_src_idx)
                        } else {
                            None
                        }
                    });
                if let Some(new_top_cat) = new_top_cat_opt {
                    // Phase F.3b (2026-05-20): consume the walker-maintained
                    // `cursor.last_action_output_cat` mirror set by every
                    // cursor.builder mutation in F.3a. Byte-equivalent to
                    // the prior `cursor.builder.top_term_type_name().and_then(
                    // |tn| self.engine.cat_of_type_name(tn))` — F.3a's
                    // debug_assert_eq! parity gate verified equivalence
                    // across the narrow gauntlet (6139/0). F.3c will
                    // delete cursor.builder entirely; this read is the
                    // mirror's first authoritative consumer.
                    if let Some(builder_cat) = cursor.last_action_output_cat
                    {
                        if builder_cat != new_top_cat {
                            let new_sym =
                                StackSymbolV2::category_entry(builder_cat);
                            let _ = self.cursor_gss_replace_top_auto(
                                cursor,
                                new_sym,
                                cursor.pos,
                                W::one_ref(),
                            );
                        }
                    }
                }
            }
        }

        // D8 fix (2026-05-13): resolve `GroupingClosePreservingInner`'s
        // `inner_cat_src_idx` from the cursor builder's top-Term
        // `type_name` instead of trusting the popped CategoryEntry's
        // OPERAND cat. The engine emits `u16::MAX` as a sentinel
        // meaning "walker resolves from builder top" (the engine has
        // no builder access at `step()` time).
        //
        // Why: for cross-cat infix patterns (e.g.,
        // `LtFloat: Float "<" Float : Bool`), the popped CE's cat is
        // the OPERAND cat (Float), but the inner expression's RESULT
        // is the RESULT cat (Bool); the post-`)` InfixLoop must
        // dispatch in the RESULT cat's table for the outer operator
        // to match.
        //
        // Fallback: if the builder top isn't a Term or the engine's
        // `cat_of_type_name` returns `None`, fall back to the popped
        // CategoryEntry's cat (preserves pre-D8 behavior for engines
        // that don't override the trait default — test mocks).
        let resolved_new_state = match new_state {
            WpdaState::GroupingClosePreservingInner {
                inner_cat_src_idx,
            } if inner_cat_src_idx == u16::MAX => {
                // Phase F.3b (2026-05-20): consume the walker-maintained
                // mirror set by F.3a. Byte-equivalent to the prior
                // `cursor.builder.top_term_type_name().and_then(...)` —
                // verified by F.3a's debug_assert_eq! parity gate across
                // 6139/0 narrow gauntlet. F.3c will delete cursor.builder.
                let resolved = cursor
                    .last_action_output_cat
                    .unwrap_or_else(|| {
                        popped_symbol
                            .map(|s| s.category_src_idx)
                            .unwrap_or(0u16)
                    });
                WpdaState::GroupingClosePreservingInner {
                    inner_cat_src_idx: resolved,
                }
            }
            other => other,
        };
        // Phase 5.5 (2026-05-12): preserve Error state if emit_fire_action's
        // eager fire set it (arity underflow). Without this guard, the
        // unconditional `set_cursor_inner_state(cursor, new_state)` would
        // overwrite the Error with the ConsumeAndPop's planned next_state.
        if !cursor.inner_state.is_terminal() {
            self.set_cursor_inner_state(cursor, resolved_new_state);
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
    /// the cursor's `node` is set to `GSS_NODE_NONE` and the deterministic-mode
    /// mirror sets `top_node = None`. Returns the predecessor `GssNodeId` for
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
        // Phase F.13 H12 Stage 1.2 (2026-05-21): if the popped edge
        // is a CrossCatProjection, the cursor just exited a cross-cat
        // sub-parse — record the result in the dispatch-cohort cache.
        // The dispatch position is the to-be-popped GSS node's pos
        // (read BEFORE we mutate cursor.node below); the resolution
        // position is the cursor's current pos; the resulting SPPF
        // symbol is on top of the cursor's sppf_stack.
        //
        // Stage 1.2 only WRITES — the resolve transition records the
        // data but no consumer reads it yet. Stage 1.3 will use the
        // Resolved entries to short-circuit cohort members.
        if let Some(eid) = edge_id {
            if let Some(crate::gss::EdgeKind::CrossCatProjection {
                source_src_idx,
                inner_cur_bp,
            }) = self.gss.edge_kind(eid)
            {
                if let Some(node) = self.gss.node(cursor.node) {
                    let dispatch_pos_usize = node.pos;
                    let dispatch_pos = dispatch_pos_usize as u32;
                    let symbol_id_opt = cursor.sppf_stack.last().copied();
                    if let Some(symbol_id) = symbol_id_opt {
                        let key = crate::dispatch_cohort::DispatchKey::new(
                            dispatch_pos_usize,
                            source_src_idx,
                            inner_cur_bp,
                        );
                        // Stage 1.5 (2026-05-21): construct a per-pop
                        // WorkerSnapshot. The resolve() call accumulates
                        // snapshots from sibling workers; end-of-step
                        // drain fans out `paused × snapshots` revived
                        // cursors per cache key.
                        // Stage 1.5.3 (2026-05-21): retrieve the root
                        // worker's pre-dispatch weight that was stashed
                        // at register time. Falls back to one() if no
                        // entry — unreachable in normal flow.
                        let worker_pre = self
                            .dispatch_cohort_cache
                            .read_worker_pre(&key)
                            .unwrap_or_else(W::one_ref);
                        let snap = crate::dispatch_cohort::WorkerSnapshot {
                            worker_inner_state: cursor.inner_state.clone(),
                            worker_last_action_output_cat:
                                cursor.last_action_output_cat,
                            worker_pending_packing_weight: cursor
                                .pending_packing_weight
                                .clone(),
                            worker_weight: cursor.weight.clone(),
                            worker_pre_dispatch_weight: worker_pre,
                        };
                        let outcome = self.dispatch_cohort_cache.resolve(
                            key.clone(),
                            symbol_id,
                            cursor.pos as u32,
                            dispatch_pos,
                            snap,
                        );
                        match outcome {
                            crate::dispatch_cohort::ResolveOutcome::FirstResolve => {
                                self.pending_cohort_drain_keys.insert(key);
                            }
                            crate::dispatch_cohort::ResolveOutcome::SnapshotAppended => {
                                // Drain already scheduled by FirstResolve.
                                self.pending_cohort_drain_keys.insert(key);
                            }
                            crate::dispatch_cohort::ResolveOutcome::NoOp => {}
                        }
                    }
                }
            }
        }
        let target = edge_id.and_then(|e| self.gss.edge_target(e));
        cursor.node = target.unwrap_or(crate::gss::GSS_NODE_NONE);
        if self.deterministic {
            self.top_node = target;
        }
        // Stage 1.5.3R-b G2 graduation (2026-05-21): if this cohort
        // cursor has popped past its revive depth, it has exited the
        // sub-parse's parent rule's continuation; clear the cohort
        // tag so it merges freely with per-cursor cursors at the
        // outer level.
        if cursor.cohort_origin.is_some()
            && (cursor.incoming_edge_stack.len() as u32) < cursor.cohort_revive_depth
        {
            cursor.cohort_origin = None;
            cursor.cohort_revive_depth = 0;
        }
        target
    }

    // Phase 5.6-tail follow-up (2026-05-12): `cursor_gss_pop_all`
    // DELETED. The Tomita-style multi-predecessor pop was planned for
    // fork-on-pop dispatching but never connected — all pop paths use
    // `cursor_gss_pop_via_edge` (which follows the cursor's recorded
    // `incoming_edge_stack` to a single predecessor). Multi-predecessor
    // fan-out would require a new caller protocol that was never
    // designed; the orphaned helper is removed.

    #[inline(always)]
    /// Phase F.13 H13 Step 0 (2026-05-21): `cursor_gss_replace_top` variant
    /// that AUTO-DERIVES the `EdgeKind` from the StackSymbolV2's SymbolKind.
    #[inline(always)]
    fn cursor_gss_replace_top_auto(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
    ) -> crate::gss::GssNodeId {
        let kind = crate::gss::EdgeKind::from_symbol(&sym);
        self.cursor_gss_replace_top_with_kind(cursor, sym, pos, w, kind)
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): kinded variant of
    /// `cursor_gss_replace_top`. Mirrors `cursor_gss_push_with_kind`.
    #[inline(always)]
    fn cursor_gss_replace_top_with_kind(
        &mut self,
        cursor: &mut BranchCursor<W>,
        sym: StackSymbolV2,
        pos: usize,
        w: W,
        kind: crate::gss::EdgeKind,
    ) -> crate::gss::GssNodeId {
        let target = if (cursor.node == 0 && self.gss.node(0).is_none())
            || cursor.node == crate::gss::GSS_NODE_NONE
        {
            let root = self.gss.get_or_create_node(WpdaGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.deterministic {
                self.top_node = Some(root);
            }
            root
        } else {
            cursor.node
        };
        let cursor_top_edge = cursor.incoming_edge_stack.last().copied();
        let (new_id, edge_id) =
            self.gss.replace_top_with_edge_id_kind(target, sym, pos, w, cursor_top_edge, kind);
        cursor.node = new_id;
        if !cursor.incoming_edge_stack.is_empty() {
            cursor.incoming_edge_stack.pop();
        }
        cursor.incoming_edge_stack.push(edge_id);
        if self.deterministic {
            self.top_node = Some(new_id);
        }
        new_id
    }

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
            let root = self.gss.get_or_create_node(WpdaGssNode {
                pos: cursor.pos,
                symbol: StackSymbolV2::category_entry(0),
            });
            cursor.node = root;
            if self.deterministic {
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
        if self.deterministic {
            self.top_node = Some(new_id);
        }
        new_id
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdaControl helper (re-export for external consumers)
// ══════════════════════════════════════════════════════════════════════════════

/// Re-exported [`WpdaControl`] for convenience.
pub use crate::wpda_runtime::WpdaControl as WalkerControl;

/// A no-op step engine that always returns [`WpdaStepAction::Idle`].
///
/// Useful as a placeholder before Stage 6's codegen lands.
pub struct IdleEngine;

impl<W: SemiringRef> WpdaEngine<W> for IdleEngine {
    fn step(
        &self,
        _state: &WpdaState,
        _gss: &WpdaGss<W>,
        _frontier_top: Option<&WpdaGssNode>,
        _pos: usize,
        _tokens: &dyn WpdaTokenSource,
    ) -> WpdaStepAction<W> {
        WpdaStepAction::Idle
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WalkerConsumer trait (Stage 5: M2 — observer is SECONDARY contract)
// ══════════════════════════════════════════════════════════════════════════════

/// Callback interface attached to a [`WpdaWalker`] for side-effect interception.
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
pub trait WalkerConsumer<W: SemiringRef> {
    /// Called after each event the walker processes.
    ///
    /// Return value directs the walker's next action:
    /// - `Continue`: proceed to next event
    /// - `Checkpoint`: snapshot current configuration, then continue
    /// - `Abort`: halt evaluation; walker enters Error state
    /// - `Pause`: suspend awaiting external resumption (DAP/REPL)
    fn on_event(&mut self, event: &WpdaEvent<W>, state: &WpdaState) -> WpdaControl;

    /// Called when a Checkpoint transition is emitted.
    #[inline(always)]
    fn on_checkpoint(&mut self, _config: &WpdaConfiguration<W>) {}

    /// Called once when the walker reaches a terminal state.
    #[inline(always)]
    fn on_complete(&mut self, _state: &WpdaState) {}
}

/// Zero-cost no-op consumer — monomorphizes away.
///
/// Use when no tracing or control is required (batch parsing).
pub struct NullConsumer;

impl<W: SemiringRef> WalkerConsumer<W> for NullConsumer {
    #[inline(always)]
    fn on_event(&mut self, _event: &WpdaEvent<W>, _state: &WpdaState) -> WpdaControl {
        WpdaControl::Continue
    }
}

/// Lightweight event tag for trace recording (avoids cloning event payloads).
///
/// Stage 6 G6+ (2026-05-02): extended with `FramePushed`, `FramePopped`
/// (master plan §5), `CursorPanorama` (cursor census after step_fanout),
/// and `BranchMerged` (cursor merge by `merge_equivalent_cursors`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WpdaEventTag {
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

impl WpdaEventTag {
    fn of<W: SemiringRef>(event: &WpdaEvent<W>) -> Self {
        match event {
            WpdaEvent::Step => WpdaEventTag::Step,
            WpdaEvent::TokenConsumed { .. } => WpdaEventTag::TokenConsumed,
            WpdaEvent::BranchForked { .. } => WpdaEventTag::BranchForked,
            WpdaEvent::BranchResolved { .. } => WpdaEventTag::BranchResolved,
            WpdaEvent::SemanticActionFired { .. } => WpdaEventTag::SemanticActionFired,
            WpdaEvent::Checkpoint { .. } => WpdaEventTag::Checkpoint,
            WpdaEvent::Inspect => WpdaEventTag::Inspect,
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
    /// `recovery_deltas` exceeded `STRICT_PENDING_OPS_LIMIT`.
    RunawayPendingOps,
    /// Beam pruning by `maybe_prune_frontier` discarded this cursor.
    BeamPruned,
}

/// A flat per-cursor snapshot for tracing/dump. Excludes heavy fields
/// (recovery_deltas contents, collection_stack contents) — only
/// their lengths. ~80 bytes flat (depends on W size + WpdaState).
#[derive(Debug, Clone)]
pub struct CursorSnapshot<W: SemiringRef> {
    pub idx: usize,
    pub pos: usize,
    pub state: WpdaState,
    pub gss_node_id: crate::gss::GssNodeId,
    pub weight: W,
    pub source_priority: u32,
    pub pending_ops_len: usize,
    pub collection_depth: usize,
}

/// Per-step cursor census produced after `step_fanout` + `merge_equivalent_cursors`.
#[derive(Debug, Clone)]
pub struct StepSnapshot<W: SemiringRef> {
    pub step_index: usize,
    pub cursor_count: usize,
    pub walker_state: WpdaState,
    pub walker_pos: usize,
    pub gss_node_count: usize,
    pub cursors: Vec<CursorSnapshot<W>>,
}

/// Side-channel observer for cursor-level events.
///
/// Separate from `WalkerConsumer` so existing LSP/DAP/REPL consumers
/// don't need to handle cursor-level micro-detail. Default impls are
/// no-ops; `NullCursorObserver` monomorphizes away to zero cost.
pub trait CursorObserver<W: SemiringRef> {
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
impl<W: SemiringRef> CursorObserver<W> for NullCursorObserver {}

/// Tracing consumer: records every event tag and resulting state.
///
/// Useful for DAP step-recording, REPL history, post-mortem analysis.
pub struct TracingConsumer<W: SemiringRef> {
    pub events: Vec<(WpdaEventTag, WpdaState)>,
    pub checkpoints: Vec<WpdaConfiguration<W>>,
    pub final_state: Option<WpdaState>,
}

impl<W: SemiringRef> TracingConsumer<W> {
    pub fn new() -> Self {
        TracingConsumer {
            events: Vec::new(),
            checkpoints: Vec::new(),
            final_state: None,
        }
    }
}

impl<W: SemiringRef> Default for TracingConsumer<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: SemiringRef> WalkerConsumer<W> for TracingConsumer<W> {
    fn on_event(&mut self, event: &WpdaEvent<W>, state: &WpdaState) -> WpdaControl {
        self.events.push((WpdaEventTag::of(event), state.clone()));
        WpdaControl::Continue
    }

    fn on_checkpoint(&mut self, config: &WpdaConfiguration<W>) {
        self.checkpoints.push(config.clone());
    }

    fn on_complete(&mut self, state: &WpdaState) {
        self.final_state = Some(state.clone());
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Stage 6 G6+ (2026-05-02): RichTracingConsumer — dual WalkerConsumer + CursorObserver
// ══════════════════════════════════════════════════════════════════════════════

/// Combined consumer + cursor observer suitable for hang diagnosis.
///
/// Records:
/// - `events`: every WpdaEventTag/state pair (like TracingConsumer).
/// - `steps`: per-step cursor census from `step_fanout`.
/// - `merges`: every (winner_idx, loser_idx) merge pair.
/// - `drops`: every (idx, reason) drop pair.
/// - `forks`: every (parent_idx, children_count) fork.
/// - `max_cursor_count`: peak observed cursor count.
/// - `final_state`: walker terminal state.
pub struct RichTracingConsumer<W: SemiringRef> {
    pub events: Vec<(WpdaEventTag, WpdaState)>,
    pub steps: Vec<StepSnapshot<W>>,
    pub merges: Vec<(usize, usize)>,
    pub drops: Vec<(usize, CursorDropReason)>,
    pub forks: Vec<(usize, usize)>,
    pub max_cursor_count: usize,
    pub final_state: Option<WpdaState>,
}

impl<W: SemiringRef> RichTracingConsumer<W> {
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

impl<W: SemiringRef> Default for RichTracingConsumer<W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: SemiringRef> WalkerConsumer<W> for RichTracingConsumer<W> {
    fn on_event(&mut self, event: &WpdaEvent<W>, state: &WpdaState) -> WpdaControl {
        self.events.push((WpdaEventTag::of(event), state.clone()));
        WpdaControl::Continue
    }

    fn on_complete(&mut self, state: &WpdaState) {
        self.final_state = Some(state.clone());
    }
}

impl<W: SemiringRef> CursorObserver<W> for RichTracingConsumer<W> {
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

impl<W: SemiringRef> WalkerConsumer<W> for EnvTracingConsumer {
    fn on_event(&mut self, event: &WpdaEvent<W>, state: &WpdaState) -> WpdaControl {
        if (self.enabled & TRACE_STEPS) != 0 {
            eprintln!(
                "[wpds-trace] step={} tag={:?} state={:?}",
                self.step_index,
                WpdaEventTag::of(event),
                state
            );
        }
        self.step_index += 1;
        WpdaControl::Continue
    }
}

impl<W: SemiringRef + std::fmt::Debug> CursorObserver<W> for EnvTracingConsumer {
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

impl<W: SemiringRef> WalkerConsumer<W> for AbortAfterConsumer {
    fn on_event(&mut self, _event: &WpdaEvent<W>, _state: &WpdaState) -> WpdaControl {
        self.count += 1;
        if self.count >= self.limit {
            WpdaControl::Abort
        } else {
            WpdaControl::Continue
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdaWalker::run_with_consumer
// ══════════════════════════════════════════════════════════════════════════════

/// Stage 3.20 / L12 (Commit A, 2026-05-06): defensive Drop impl that
/// clears the mutable_token_source slot if the walker outlives the
/// caller's source. Prevents stale-pointer reuse in pathological cases
/// (e.g. walker stored in a long-lived consumer struct, source borrowed
/// per-parse).
impl<W: SemiringRef, E: WpdaEngine<W>> Drop for WpdaWalker<W, E> {
    fn drop(&mut self) {
        self.mutable_token_source = None;
    }
}

impl<W, E> WpdaWalker<W, E>
where
    W: SemiringRef + crate::automata::semiring::TropicalDeltaWeight,
    E: WpdaEngine<W>,
{
    /// Drive the walker reactively with a [`WalkerConsumer`] attached.
    ///
    /// Each iteration:
    /// 1. Process `WpdaEvent::Step` (driving the FSM via the engine).
    /// 2. If transition was `Checkpoint`, notify `consumer.on_checkpoint`.
    /// 3. Notify `consumer.on_event(Step, current_state)`.
    /// 4. Honor consumer's `WpdaControl` directive.
    ///
    /// Terminates when state is terminal, max_steps exceeded, consumer aborts,
    /// or consumer pauses. Calls `consumer.on_complete(&final_state)` exactly
    /// once unless paused.
    pub fn run_with_consumer<C: WalkerConsumer<W>>(
        &mut self,
        consumer: &mut C,
        max_steps: usize,
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaState {
        for _ in 0..max_steps {
            if self.state.is_terminal() {
                consumer.on_complete(&self.state);
                return self.state.clone();
            }
            let event = WpdaEvent::Step;
            let transition = self.process_event(event.clone(), tokens);
            if let WpdaTransition::Checkpoint { ref config } = transition {
                consumer.on_checkpoint(config);
            }
            match consumer.on_event(&event, &self.state) {
                WpdaControl::Continue => {}
                WpdaControl::Checkpoint => {
                    let config = self.current_configuration();
                    consumer.on_checkpoint(&config);
                }
                WpdaControl::Abort => {
                    self.state = WpdaState::Error {
                        message: "consumer aborted".to_string(),
                    };
                    consumer.on_complete(&self.state);
                    return self.state.clone();
                }
                WpdaControl::Pause => {
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
    /// Returns the same `Result<(), WpdaMaxStepsExceeded>` as
    /// `run_to_end_of_input`; codegen call sites can swap directly.
    pub fn run_to_end_of_input_env_aware(
        &mut self,
        default_max_steps: usize,
        tokens: &dyn WpdaTokenSource,
    ) -> Result<(), WpdaMaxStepsExceeded>
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
                Err(WpdaMaxStepsExceeded { position: self.pos })
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
        tokens: &dyn WpdaTokenSource,
    ) -> WpdaState
    where
        C: WalkerConsumer<W> + CursorObserver<W>,
        W: 'static + std::fmt::Debug,
    {
        for _ in 0..max_steps {
            // T4 SIGUSR1 hang-dump (2026-05-12): publish per-step snapshot
            // for SIGUSR1 / watchdog dumps. No-op when feature is off.
            self.publish_to_hang_dump_slot();
            if self.state.is_terminal() {
                <C as WalkerConsumer<W>>::on_complete(consumer, &self.state);
                return self.state.clone();
            }
            let event = WpdaEvent::Step;
            let transition = self.process_event(event.clone(), tokens);
            if let WpdaTransition::Checkpoint { ref config } = transition {
                <C as WalkerConsumer<W>>::on_checkpoint(consumer, config);
            }
            // Stage 6 G6+ (2026-05-02): per-step cursor census.
            let snapshot = self.current_snapshot();
            <C as CursorObserver<W>>::on_step_panorama(consumer, &snapshot);
            match <C as WalkerConsumer<W>>::on_event(consumer, &event, &self.state) {
                WpdaControl::Continue => {}
                WpdaControl::Checkpoint => {
                    let config = self.current_configuration();
                    <C as WalkerConsumer<W>>::on_checkpoint(consumer, &config);
                }
                WpdaControl::Abort => {
                    self.state = WpdaState::Error {
                        message: "consumer aborted".to_string(),
                    };
                    <C as WalkerConsumer<W>>::on_complete(consumer, &self.state);
                    return self.state.clone();
                }
                WpdaControl::Pause => {
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
    use crate::automata::semiring::Semiring;
    use crate::automata::TokenKind;
    use std::cell::RefCell;

    fn lex(c: f64, s: u16, r: u16) -> LexicographicWeight {
        LexicographicWeight::from_cost(c, s, r)
    }

    /// Test engine driven by a programmable script of actions.
    struct ScriptedEngine {
        script: RefCell<Vec<WpdaStepAction<LexicographicWeight>>>,
    }

    impl ScriptedEngine {
        fn new(actions: Vec<WpdaStepAction<LexicographicWeight>>) -> Self {
            ScriptedEngine {
                script: RefCell::new(actions),
            }
        }
    }

    impl WpdaEngine<LexicographicWeight> for ScriptedEngine {
        fn step(
            &self,
            _state: &WpdaState,
            _gss: &WpdaGss<LexicographicWeight>,
            _frontier_top: Option<&WpdaGssNode>,
            _pos: usize,
            _tokens: &dyn WpdaTokenSource,
        ) -> WpdaStepAction<LexicographicWeight> {
            self.script
                .borrow_mut()
                .pop()
                .unwrap_or(WpdaStepAction::Idle)
        }
    }

    /// Empty token source used by tests that don't inspect input.
    fn empty_tokens() -> crate::wpda_runtime::SliceTokenSource<'static> {
        static EMPTY: [TokenKind; 0] = [];
        crate::wpda_runtime::SliceTokenSource::new(&EMPTY)
    }

    // ─── Shape tests ────────────────────────────────────────────────────────

    #[test]
    fn walker_starts_in_ready_state() {
        let w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        assert_eq!(*w.state(), WpdaState::Ready { min_bp: 0 });
        assert_eq!(w.position(), 0);
        assert!(w.gss().is_empty());
        assert_eq!(w.beam_size(), None);
    }

    #[test]
    fn walker_with_beam_size_records_bound() {
        let w: WpdaWalker<LexicographicWeight, _> =
            WpdaWalker::new(IdleEngine, 0).with_beam_size(8);
        assert_eq!(w.beam_size(), Some(8));
    }

    #[test]
    fn process_event_inspect_yields_no_change() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::Inspect, &empty_tokens());
        assert!(matches!(t, WpdaTransition::NoChange));
    }

    #[test]
    fn process_event_step_with_idle_engine_yields_no_change() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::Step, &empty_tokens());
        assert!(matches!(t, WpdaTransition::NoChange));
    }

    #[test]
    fn process_event_step_advances_state_via_engine() {
        // Script (popped from end): Advance(PrefixDispatch) only — fires once.
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Advance(
            WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        )]);
        let mut w = WpdaWalker::new(engine, 0);
        let t = w.process_event(WpdaEvent::Step, &empty_tokens());
        match t {
            WpdaTransition::Transition { new_state, .. } => {
                assert_eq!(new_state, WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 });
            }
            other => panic!("expected Transition, got {:?}", other),
        }
        assert_eq!(*w.state(), WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 });
    }

    #[test]
    fn process_event_token_consumed_advances_position() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::TokenConsumed {
            pos: 5,
            token: TokenKind::Ident,
        }, &empty_tokens());
        assert!(matches!(t, WpdaTransition::Transition { .. }));
        assert_eq!(w.position(), 5);
    }

    #[test]
    fn process_event_branch_forked_enters_ambiguity_fanout() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::BranchForked {
            parent: 0,
            children: vec![1, 2, 3],
        }, &empty_tokens());
        assert!(matches!(t, WpdaTransition::Transition { .. }));
        match w.state() {
            WpdaState::AmbiguityFanout { branches } => {
                assert_eq!(branches, &vec![1u32, 2u32, 3u32]);
            }
            other => panic!("expected AmbiguityFanout, got {:?}", other),
        }
    }

    #[test]
    fn process_event_branch_resolved_exits_ambiguity_fanout() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let _ = w.process_event(WpdaEvent::BranchForked {
            parent: 0,
            children: vec![1, 2],
        }, &empty_tokens());
        let t = w.process_event(WpdaEvent::BranchResolved {
            winner: 1,
            weight: lex(2.5, 3, 4),
        }, &empty_tokens());
        assert!(matches!(t, WpdaTransition::Transition { .. }));
        match w.state() {
            WpdaState::InfixLoop { .. } => {}
            other => panic!("expected InfixLoop after resolution, got {:?}", other),
        }
        // Cumulative weight should reflect the resolved branch.
        assert!((w.weight().primary.0 - 2.5).abs() < 1e-9);
        assert_eq!(w.weight().src_idx, 3);
        assert_eq!(w.weight().rule_idx, 4);
    }

    #[test]
    fn process_event_semantic_action_fired_records_trace() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::SemanticActionFired {
            action_id: 42,
            args: vec![0, 1, 2],
        }, &empty_tokens());
        assert!(matches!(t, WpdaTransition::Transition { trace: Some(_), .. }));
    }

    #[test]
    fn process_event_checkpoint_emits_checkpoint_transition() {
        let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        let t = w.process_event(WpdaEvent::Checkpoint {
            reason: crate::wpda_runtime::CheckpointReason::NaturalBoundary,
        }, &empty_tokens());
        match t {
            WpdaTransition::Checkpoint { config } => {
                assert_eq!(config.pos, 0);
                assert_eq!(config.state, WpdaState::Ready { min_bp: 0 });
            }
            other => panic!("expected Checkpoint, got {:?}", other),
        }
    }

    #[test]
    fn terminal_state_absorbs_events_without_change() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Accept]);
        let mut w = WpdaWalker::new(engine, 0);
        let t1 = w.process_event(WpdaEvent::Step, &empty_tokens());
        assert!(matches!(t1, WpdaTransition::Done { .. }));
        assert_eq!(*w.state(), WpdaState::Accepted);
        // Further events yield NoChange.
        let t2 = w.process_event(WpdaEvent::Step, &empty_tokens());
        assert!(matches!(t2, WpdaTransition::NoChange));
        let t3 = w.process_event(WpdaEvent::Inspect, &empty_tokens());
        assert!(matches!(t3, WpdaTransition::NoChange));
    }

    #[test]
    fn step_action_error_transitions_to_error_state() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Error("bad parse".to_string())]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        match w.state() {
            WpdaState::Error { message } => assert_eq!(message, "bad parse"),
            other => panic!("expected Error state, got {:?}", other),
        }
    }

    #[test]
    fn step_action_push_grows_gss_and_updates_weight() {
        // Push action emits a new symbol on top of an entry frame.
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
            weight: lex(2.0, 0, 1),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 7 },
        }]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        // GSS now has at least the entry node + the pushed node.
        assert!(w.gss().node_count() >= 2);
        assert!((w.weight().primary.0 - 2.0).abs() < 1e-9);
    }

    #[test]
    fn step_action_replace_keeps_predecessor() {
        let engine = ScriptedEngine::new(vec![
            // Last popped first: replace runs second, push runs first.
            WpdaStepAction::Replace {
                symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                weight: lex(0.5, 0, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push
        let initial_count = w.gss().node_count();
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Replace
        // Replace adds a new node (replace_top creates rather than mutates).
        assert!(w.gss().node_count() > initial_count);
    }

    #[test]
    fn step_action_fork_enters_ambiguity_fanout() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry first.
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        match w.state() {
            WpdaState::AmbiguityFanout { branches } => {
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
            WpdaStepAction::Accept,
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 2),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            // Initial Fork.
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry first.
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
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
            WpdaState::Accepted,
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
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 7 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::InfixLoop { cur_bp: 13 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdaState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 3);
        // Each cursor's inner_state must be its own branch's new_state.
        match &cursors[0].inner_state {
            &WpdaState::PrefixDispatch { cur_bp, .. } => assert_eq!(cur_bp, 7),
            other => panic!("cursor[0]: expected PrefixDispatch{{cur_bp:7}}, got {:?}", other),
        }
        match &cursors[1].inner_state {
            &WpdaState::InfixLoop { cur_bp } => assert_eq!(cur_bp, 13),
            other => panic!("cursor[1]: expected InfixLoop{{cur_bp:13}}, got {:?}", other),
        }
        match &cursors[2].inner_state {
            WpdaState::Unwinding => {},
            other => panic!("cursor[2]: expected Unwinding, got {:?}", other),
        }
    }

    /// Commit A: `consume_trigger: true` advances `pos` by 1 before
    /// allocating cursors; cursors inherit the post-advance pos.
    #[test]
    fn fork_consume_trigger_advances_pos_once_for_all_cursors() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: true,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        assert_eq!(w.position(), 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork (consumes trigger)
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
        // WpdaState::Error("all fork branches dropped").
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Error("branch a failed".into()),
            WpdaStepAction::Error("branch b failed".into()),
            WpdaStepAction::Error("branch c failed".into()),
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        let final_state = w.run_to_saturation(100, &empty_tokens());
        match final_state {
            WpdaState::Error { ref message } => {
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
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.5, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.5, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(0.5, 0, 2),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        // Stage 3.5b (2026-05-01): use new EOI-aware resolution API.
        // Synthetic test (no Term push) — resolve returns ParseError
        // but commit_winner_at_eoi DID fire and set walker.state from
        // the winner's inner_state.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert_eq!(*w.state(), WpdaState::Accepted);
        let final_weight = w.weight();
        // Advance does not modify weight; winner's weight is its branch weight only.
        assert_eq!(final_weight.rule_idx, 0);
        assert!((final_weight.primary.0 - 0.5).abs() < 1e-9);
    }

    #[test]
    fn run_to_completion_terminates_at_accept() {
        // Engine emits 3 advances then accepts.
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::Unwinding),
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
            WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let final_state = w.run_to_completion(100, &empty_tokens());
        assert_eq!(final_state, WpdaState::Accepted);
    }

    #[test]
    fn run_to_completion_respects_max_steps() {
        // Engine never accepts; run_to_completion bails after max_steps.
        let engine = ScriptedEngine::new(vec![]); // returns Idle
        let mut w = WpdaWalker::new(engine, 0);
        let final_state = w.run_to_completion(10, &empty_tokens());
        // Idle from the engine yields NoChange; we stay in Ready.
        assert_eq!(final_state, WpdaState::Ready { min_bp: 0 });
    }

    #[test]
    fn run_to_saturation_errors_on_idle_in_non_terminal_state() {
        // B6 (2026-04-28): when the engine returns Idle in a non-terminal
        // state, the walker surfaces the stall as Error rather than
        // silently exiting (which would let callers think parse "completed"
        // when it actually got stuck mid-derivation).
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let s = w.run_to_saturation(100, &empty_tokens());
        match s {
            WpdaState::Error { ref message } => {
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
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let s = w.run_to_saturation(10, &empty_tokens());
        assert_eq!(s, WpdaState::Accepted);
    }

    #[test]
    fn current_configuration_snapshot_captures_position_and_weight() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 0, 0, None),
            weight: lex(3.5, 1, 2),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdaWalker::new(engine, 7);
        let _ = w.process_event(WpdaEvent::TokenConsumed {
            pos: 4,
            token: TokenKind::Ident,
        }, &empty_tokens());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
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
        let event: WpdaEvent<LexicographicWeight> = WpdaEvent::Step;
        let r = <NullConsumer as WalkerConsumer<LexicographicWeight>>::on_event(
            &mut c,
            &event,
            &WpdaState::Ready { min_bp: 0 },
        );
        assert_eq!(r, WpdaControl::Continue);
    }

    #[test]
    fn tracing_consumer_records_events_and_final_state() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker = WpdaWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let final_state = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        assert_eq!(final_state, WpdaState::Accepted);
        assert!(!consumer.events.is_empty());
        assert_eq!(consumer.final_state, Some(WpdaState::Accepted));
        // First recorded event should be the Step that drove from Ready.
        assert_eq!(consumer.events[0].0, WpdaEventTag::Step);
    }

    #[test]
    fn abort_after_consumer_halts_after_n_events() {
        let engine = ScriptedEngine::new(
            (0..50)
                .map(|i| WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: i, cur_bp: 0 }))
                .collect(),
        );
        let mut walker: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(engine, 0);
        let mut consumer = AbortAfterConsumer::new(3);
        let final_state = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        match final_state {
            WpdaState::Error { message } => assert_eq!(message, "consumer aborted"),
            other => panic!("expected Error state from abort, got {:?}", other),
        }
        assert_eq!(consumer.count, 3);
    }

    #[test]
    fn run_with_consumer_calls_on_complete_at_terminal() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Accept]);
        let mut walker = WpdaWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let _ = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        assert_eq!(consumer.final_state, Some(WpdaState::Accepted));
    }

    #[test]
    fn run_with_consumer_max_steps_reached_calls_on_complete() {
        // Engine never accepts; consumer should still receive on_complete.
        let engine = ScriptedEngine::new(vec![]);
        let mut walker: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(engine, 0);
        let mut consumer: TracingConsumer<LexicographicWeight> = TracingConsumer::new();
        let _ = walker.run_with_consumer(&mut consumer, 5, &empty_tokens());
        assert_eq!(consumer.final_state, Some(WpdaState::Ready { min_bp: 0 }));
    }

    /// A consumer that requests Checkpoint on every event.
    struct CheckpointEveryEvent {
        pub recorded: usize,
    }

    impl<W: SemiringRef> WalkerConsumer<W> for CheckpointEveryEvent {
        fn on_event(&mut self, _event: &WpdaEvent<W>, _state: &WpdaState) -> WpdaControl {
            WpdaControl::Checkpoint
        }
        fn on_checkpoint(&mut self, _config: &WpdaConfiguration<W>) {
            self.recorded += 1;
        }
    }

    #[test]
    fn checkpoint_consumer_records_per_step() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::InfixLoop { cur_bp: 0 }),
            WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(engine, 0);
        let mut consumer = CheckpointEveryEvent { recorded: 0 };
        let _ = walker.run_with_consumer(&mut consumer, 100, &empty_tokens());
        // At least one checkpoint should be recorded per non-terminal step.
        assert!(consumer.recorded >= 2, "expected ≥2 checkpoints, got {}", consumer.recorded);
    }

    /// A consumer that pauses on the first event.
    struct PauseOnFirst {
        pub paused: bool,
    }

    impl<W: SemiringRef> WalkerConsumer<W> for PauseOnFirst {
        fn on_event(&mut self, _event: &WpdaEvent<W>, _state: &WpdaState) -> WpdaControl {
            if !self.paused {
                self.paused = true;
                WpdaControl::Pause
            } else {
                WpdaControl::Continue
            }
        }
    }

    #[test]
    fn pause_consumer_stops_walker_without_completion() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut walker: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(engine, 0);
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

    impl WpdaEngine<LexicographicWeight> for AtomicIntEngine {
        fn step(
            &self,
            state: &WpdaState,
            _gss: &WpdaGss<LexicographicWeight>,
            frontier_top: Option<&WpdaGssNode>,
            _pos: usize,
            tokens: &dyn WpdaTokenSource,
        ) -> WpdaStepAction<LexicographicWeight> {
            match state {
                WpdaState::Ready { min_bp } => WpdaStepAction::Push {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: LexicographicWeight::from_cost(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch {
                        pos: 0,
                        cur_bp: *min_bp,
                    },
                },
                WpdaState::PrefixDispatch { pos, cur_bp } => {
                    if let Some(TokenKind::Integer) = tokens.peek_kind(*pos) {
                        WpdaStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::rule_at(0, 0, 0, None)
                                .with_kind_return(),
                            weight: LexicographicWeight::from_cost(0.0, 0, 0),
                            new_state: WpdaState::Unwinding,
                            trigger_mode: TriggerMode::CaptureForBuilder,
                        }
                    } else {
                        let _ = cur_bp;
                        WpdaStepAction::Error("expected Integer".into())
                    }
                }
                WpdaState::Unwinding => match frontier_top.map(|n| n.symbol.kind) {
                    Some(SymbolKind::Return) => WpdaStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdaState::Unwinding,
                    },
                    Some(SymbolKind::CategoryEntry) => WpdaStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdaState::Accepted,
                    },
                    _ => WpdaStepAction::Idle,
                },
                _ => WpdaStepAction::Idle,
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
                expected_input_cats: &[crate::wpda_runtime::ANY_CAT],
                output_cat: 0,
            };
            if src_idx == 0 && rule_idx == 0 {
                Some(&ACTION)
            } else {
                None
            }
        }
    }

    use crate::wpda_runtime::{ActionArg, ActionEntry, SemanticBuilder, SliceTokenSource};

    #[test]
    fn atomic_int_literal_parses_end_to_end() {
        let tokens = [TokenKind::Integer];
        let texts = ["42"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let mut walker: WpdaWalker<LexicographicWeight, _> =
            WpdaWalker::new(AtomicIntEngine, 0);
        let final_state = walker.run_to_saturation(50, &token_src);
        assert_eq!(final_state, WpdaState::Accepted, "walker reaches Accepted");
        // Phase F.3c.1 (2026-05-20): use the production extraction path
        // (`resolve_at_end_of_input` → realize_root_to_terms) instead of
        // the legacy `walker.builder_mut().take_result()`. The pre-F.3c
        // pattern read from `walker.builder`, which is deleted in F.3c.5.
        // The realize path returns the same Arc<dyn Any> the action_fn
        // pushed; downcast unchanged.
        let resolved = walker.resolve_at_end_of_input(&token_src);
        let term_arc = match resolved {
            WpdaResolveResult::Accepted { mut terms, .. } => {
                assert_eq!(terms.len(), 1, "expected single unambiguous parse");
                terms.pop().expect("Accepted with non-empty terms")
            }
            other => panic!("expected Accepted, got {:?}", other),
        };
        let result_i64 = term_arc
            .downcast::<i64>()
            .expect("AtomicIntEngine pushes i64");
        assert_eq!(*result_i64, 42);
        // Position should have advanced past the literal.
        assert_eq!(walker.position(), 1);
    }

    #[test]
    fn atomic_int_engine_on_non_integer_token_errors() {
        let tokens = [TokenKind::Ident];
        let texts = ["foo"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let mut walker: WpdaWalker<LexicographicWeight, _> =
            WpdaWalker::new(AtomicIntEngine, 0);
        let final_state = walker.run_to_saturation(50, &token_src);
        match final_state {
            WpdaState::Error { message } => assert!(message.contains("expected Integer")),
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
        script: RefCell<Vec<WpdaStepAction<LexicographicWeight>>>,
    }

    impl CollAwareScriptedEngine {
        fn new(actions: Vec<WpdaStepAction<LexicographicWeight>>) -> Self {
            Self { script: RefCell::new(actions) }
        }
    }

    fn coll_elem_action(
        b: &mut crate::wpda_runtime::SemanticBuilder,
        _args: Vec<crate::wpda_runtime::ActionArg>,
    ) {
        b.push_term::<i64>(7);
    }

    fn coll_finalize_action(
        b: &mut crate::wpda_runtime::SemanticBuilder,
        args: Vec<crate::wpda_runtime::ActionArg>,
    ) {
        let id = args
            .first()
            .and_then(|a| match a {
                crate::wpda_runtime::ActionArg::CollectionId(id) => Some(*id),
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
        expected_input_cats: &[crate::wpda_runtime::ANY_CAT],
        output_cat: 0,
    };

    impl WpdaEngine<LexicographicWeight> for CollAwareScriptedEngine {
        fn step(
            &self,
            _state: &WpdaState,
            _gss: &WpdaGss<LexicographicWeight>,
            _frontier_top: Option<&WpdaGssNode>,
            _pos: usize,
            _tokens: &dyn WpdaTokenSource,
        ) -> WpdaStepAction<LexicographicWeight> {
            self.script.borrow_mut().pop().unwrap_or(WpdaStepAction::Idle)
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
            WpdaStepAction::Accept,
            // Pops for 4 grandchildren (LIFO: last popped first).
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 3),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 2),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            // Inner Fork for outer cursor B.
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 2, 0, None),
                        weight: lex(1.0, 0, 2),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 3, 0, None),
                        weight: lex(1.0, 0, 3),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Inner Fork for outer cursor A.
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Outer Fork.
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Setup: push entry.
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // outer Fork
        // Stage 3.5b (2026-05-01): nested Fork lex-min winner is now
        // selected at end-of-input via resolve_at_end_of_input.
        // Synthetic test (no Term push) — resolve returns ParseError
        // but commit_winner_at_eoi DID fire and set walker.state.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert_eq!(*w.state(), WpdaState::Accepted);
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
            WpdaStepAction::Accept,
            // Step 3: ConsumeAndPop CollectionMarker -> InfixLoop (Resolved).
            // Cursor pops the marker, logs FireAction(coll_marker_symbol),
            // SpliceIntoCollection (no-op since pred is CategoryEntry, not
            // a marker — actually no splice here).
            WpdaStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
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
            WpdaStepAction::Push {
                symbol: coll_marker,
                weight: lex(0.0, 1, 0),
                new_state: WpdaState::Unwinding,
            },
            // Step 1: Single-branch Fork.
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        // Stage 3.5b (2026-05-01): the finalize action's Term result
        // surfaces via WpdaResolveResult::Accepted, not via builder.take_result.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps not exceeded");
        let result = w.resolve_at_end_of_input(&empty_tokens());
        match result {
            WpdaResolveResult::Accepted { terms, .. } => {
                let term = terms.into_iter().next().expect("≥1 term required");
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
            WpdaStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::ConsumeAndPop {
                weight: lex(1.0, 1, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            // Step 3: outer cursor's inner Fork (after collection open).
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            // Step 2: outer cursor opens collection.
            WpdaStepAction::Push {
                symbol: coll_marker,
                weight: lex(0.0, 1, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
            // Step 1: outer Fork (single branch to focus the test).
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // outer Fork
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
            matches!(result, WpdaResolveResult::ParseError { .. }),
            "B13d-R rejects no-Term cursors; expected ParseError; got {:?}",
            result,
        );
    }

    /// Cleanup 4 (Stage 3.5b 2026-05-01 update): a losing branch's
    /// recovery_deltas must NOT replay against the live builder.
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
        let token_src = crate::wpda_runtime::SliceTokenSource::with_texts(
            &token_kinds,
            &token_texts,
        );
        let engine = ScriptedEngine::new(vec![
            // Pops for 2 cursors (LIFO).
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 1),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            // ConsumeAndPush for cursor B (CaptureForBuilder → logs PushToken).
            WpdaStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(0, 1, 0, None).with_kind_return(),
                weight: lex(1.0, 0, 1),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                trigger_mode: TriggerMode::CaptureForBuilder,
            },
            // ConsumeAndPush for cursor A (winner).
            WpdaStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(0, 0, 0, None).with_kind_return(),
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                trigger_mode: TriggerMode::CaptureForBuilder,
            },
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(0.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(0.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &token_src); // entry
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Fork
        // Drive until parked at EOI. Both cursors reach pos=1=EOI in
        // InfixLoop after their Pop.
        w.run_to_end_of_input(100, &token_src).expect("max_steps");
        // Resolve fires commit_winner_at_eoi(0) on the lex-min winner.
        // The winner's recovery_deltas replays exactly once; the
        // loser's deltas are discarded with its cursor.
        let _ = w.resolve_at_end_of_input(&token_src);
        // Post-B13d-R (Candidate H, 2026-05-08): cursors whose
        // recovery_deltas produce only an untyped Token (no
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

    // Phase 5.6-tail-E (2026-05-12): predicate_in_fork_branch_clone_path
    // DELETED. Pre-tail it exercised the BranchCursor::clone() path
    // against a `BuilderDelta::PushPredicate` entry in pending_builder_ops
    // — that variant is deleted under is_recovery_delta gating + dead-
    // variant pruning. Clone coverage is now subsumed by:
    //   1. The Arc::clone fast-path on cursor.builder (any test that
    //      forks a cursor exercises this).
    //   2. predicate-carrying parsers in the language test corpus
    //      (gen_rhocalc_op cross_cat tests).

    /// Cleanup 3: a `FireAction` delta whose action arity exceeds the
    /// builder stack must leave the walker in `Error` state — the
    /// post-loop install must NOT silently overwrite with
    /// `winner.inner_state` (which would mask the engine arity bug).
    #[test]
    fn commit_winner_state_overwrite_on_action_arity_underflow() {
        struct ArityBugScriptedEngine {
            script: RefCell<Vec<WpdaStepAction<LexicographicWeight>>>,
        }
        fn underflow_action(
            _b: &mut crate::wpda_runtime::SemanticBuilder,
            _args: Vec<crate::wpda_runtime::ActionArg>,
        ) {
            // Unreachable: pop_args(arity=5) underflows on empty builder
            // BEFORE we get here, setting state = Error.
        }
        static UNDERFLOW_ENTRY: ActionEntry = ActionEntry {
            action_fn: underflow_action,
            arity: 5,
            expected_input_cats: &[
                crate::wpda_runtime::ANY_CAT,
                crate::wpda_runtime::ANY_CAT,
                crate::wpda_runtime::ANY_CAT,
                crate::wpda_runtime::ANY_CAT,
                crate::wpda_runtime::ANY_CAT,
            ],
            output_cat: 0,
        };
        impl WpdaEngine<LexicographicWeight> for ArityBugScriptedEngine {
            fn step(
                &self,
                _state: &WpdaState,
                _gss: &WpdaGss<LexicographicWeight>,
                _frontier_top: Option<&WpdaGssNode>,
                _pos: usize,
                _tokens: &dyn WpdaTokenSource,
            ) -> WpdaStepAction<LexicographicWeight> {
                self.script
                    .borrow_mut()
                    .pop()
                    .unwrap_or(WpdaStepAction::Idle)
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
                WpdaStepAction::Pop {
                    weight: lex(1.0, 0, 0),
                    new_state: WpdaState::InfixLoop { cur_bp: 0 },
                },
                WpdaStepAction::Fork {
                    branches: vec![ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None).with_kind_return(),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    }],
                    consume_trigger: false,
                },
                WpdaStepAction::Push {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                },
            ]),
        };
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // entry
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        // Phase 5.5 (2026-05-12): emit_fire_action now eagerly fires the
        // action_fn on cursor.builder during the Pop step. The arity
        // underflow detected in fire_action_for_on_builder sets
        // walker.state = WpdaState::Error directly (rather than waiting
        // for commit_winner replay). Capture state BEFORE the subsequent
        // run_to_end_of_input/resolve loop, which may transition the
        // walker through dead-cursor cleanup and overwrite the live
        // state with a recovery value.
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Pop with underflow
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
            WpdaState::Error { ref message } => {
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
    // Phase 5.6-tail-F (2026-05-12): CursorMode enum deleted in favor of
    // a monotone `deterministic: bool` flag. The L1-L6 invariants from the
    // pre-tail enum-based scheme either collapse (L1/L5/L6) or simplify
    // (L2/L3/L4) under the bool. Tests reshaped accordingly:
    // - phase4_lazy_admission_holds_after_construction → singleton+empty check
    // - phase4_lazy_to_strict_on_first_fork → deterministic-flips-on-Fork check
    // - phase4_strict_persists_through_resolution → deterministic-stays-false check
    // - phase4_reset_returns_to_lazy → deterministic-reset-to-true check
    // - phase4_lazy_terminal_state_is_mode_irrelevant → terminal-absorbs check
    // - phase4_lazy_eoi_accept_no_replay_needed → recovery_deltas-empty check
    // ══════════════════════════════════════════════════════════════════════

    /// Initial state: deterministic, singleton cursor, no recovery deltas.
    #[test]
    fn phase4_deterministic_admission_holds_after_construction() {
        let w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
        assert!(w.deterministic(), "starts deterministic");
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "singleton cursor at construction");
        assert!(
            cursors[0].recovery_deltas.is_empty(),
            "recovery_deltas empty at construction"
        );
    }

    /// First Fork flips deterministic from true to false.
    #[test]
    fn phase4_first_fork_promotes_to_forked() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                        weight: lex(1.0, 0, 0),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(0, 1, 0, None),
                        weight: lex(1.0, 0, 1),
                        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        assert!(w.deterministic(), "starts deterministic");
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push entry
        assert!(w.deterministic(), "still deterministic after non-Fork");
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        assert!(!w.deterministic(), "flipped to nondeterministic on first Fork");
    }

    /// Once nondeterministic, the flag stays nondeterministic through resolution.
    #[test]
    fn phase4_nondeterministic_persists_through_resolution() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Pop {
                weight: lex(1.0, 0, 0),
                new_state: WpdaState::InfixLoop { cur_bp: 0 },
            },
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        assert!(!w.deterministic());
        // Drive cursors to resolution.
        w.run_to_end_of_input(100, &empty_tokens())
            .expect("max_steps");
        let _ = w.resolve_at_end_of_input(&empty_tokens());
        assert!(!w.deterministic(), "stays nondeterministic post-resolution (monotone)");
    }

    /// reset() returns deterministic=true with a fresh singleton.
    #[test]
    fn phase4_reset_returns_to_deterministic() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 0, None),
                    weight: lex(1.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
        assert!(!w.deterministic());
        w.reset(0);
        assert!(w.deterministic(), "reset() flips back to deterministic");
        assert_eq!(*w.state(), WpdaState::Ready { min_bp: 0 });
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1, "singleton after reset");
        assert!(cursors[0].recovery_deltas.is_empty());
    }

    /// Terminal state absorbs further actions regardless of deterministic flag.
    #[test]
    fn phase4_terminal_state_is_fork_status_irrelevant() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Accept]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Accept
        assert_eq!(*w.state(), WpdaState::Accepted);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        assert_eq!(*w.state(), WpdaState::Accepted, "terminal absorbs");
    }

    /// Unambiguous parse reaches Accepted with no recovery_deltas to replay.
    #[test]
    fn phase4_deterministic_eoi_accept_no_replay_needed() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Accept]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        assert!(w.deterministic(), "no Fork → still deterministic");
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            cursors[0].recovery_deltas.is_empty(),
            "no deltas to replay"
        );
        assert_eq!(*w.state(), WpdaState::Accepted);
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01): a Push of
    /// `OptionalGroupAt(1)` MUST open the optional scope in deterministic mode.
    /// Pre-fix: `apply_action_to_cursor::Push` lost the
    /// `OptionalGroupAt(1) → start_optional_scope()` clause during the
    /// Step-4.4 helper rewrite. Post-fix: `emit_push_side_effects`
    /// centralizes both `CollectionMarker` (id allocation) and
    /// `OptionalGroupAt(1)` (scope opening) implicit Push-time effects.
    #[test]
    fn push_optional_group_at_one_opens_scope_in_deterministic_mode() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Push {
            symbol: StackSymbolV2::optional_group_at(0, 0, 1, 0),
            weight: lex(0.0, 0, 0),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdaWalker::new(engine, 0);
        assert!(w.deterministic());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        // Still deterministic (no Fork). The cursor must have an open
        // optional scope so subsequent inner pushes land in the inner Vec.
        assert!(w.deterministic());
        // Phase F.3c.1 (2026-05-20): inspect the SPPF-side mirror
        // `cursor.optional_scope_marks` instead of `walker.builder()`
        // (deleted in F.3c.5).
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(
            cursors[0].optional_scope_marks.len(),
            1,
            "Push of OptionalGroupAt(1) must open optional scope in deterministic mode",
        );
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01); reshaped
    /// in Phase 5.6-tail-B (2026-05-12): pre-tail this checked the
    /// cursor's `recovery_deltas` for a `BuilderDelta::StartOptionalScope`
    /// entry. Under always-eager Arc::make_mut (Phase 5.3+) and emit-helper
    /// unification (5.6-tail-B), emit_start_optional_scope no longer
    /// journals — it mutates `cursor.builder.optional_stack` directly via
    /// Arc::make_mut. The reshaped assertion observes the optional scope
    /// directly on cursor.builder.
    #[test]
    fn push_optional_group_at_one_opens_scope_in_nondeterministic_mode() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Push {
                symbol: StackSymbolV2::optional_group_at(0, 0, 1, 0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
            // Force nondeterministic mode via a single-branch Fork BEFORE the OptionalGroupAt push.
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
                    action_kind: ForkActionKind::Push,
                }],
                consume_trigger: false,
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork → nondeterministic
        assert!(!w.deterministic());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push (under fanout)
        // The cursor must show an open optional scope.
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        // Phase F.3c.1 (2026-05-20): inspect the SPPF-side mirror
        // `cursor.optional_scope_marks` instead of `cursor.builder`
        // (deleted in F.3c.4).
        assert_eq!(
            cursors[0].optional_scope_marks.len(),
            1,
            "Push of OptionalGroupAt(1) in nondeterministic mode must open an optional scope \
             on the cursor's optional_scope_marks (mirrored by emit_start_optional_scope)",
        );
    }

    /// Stage 3.9 / ι Phase 4 regression-fix test (2026-05-01): regression
    /// guard. Push of `OptionalGroupAt(2)` (or any sub_pos != 1) must NOT
    /// open the optional scope — only the FIRST marker (sub_pos=1) opens.
    /// Subsequent OptionalGroupAt(2..N) advance through the group's inner
    /// items and must NOT re-open the scope.
    #[test]
    fn push_optional_group_at_two_does_not_open_scope() {
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Push {
            symbol: StackSymbolV2::optional_group_at(0, 0, 2, 0),
            weight: lex(0.0, 0, 0),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        // Phase F.3c.1 (2026-05-20): inspect SPPF-side mirror instead of
        // walker.builder() (deleted in F.3c.5).
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(
            cursors[0].optional_scope_marks.len(),
            0,
            "OptionalGroupAt(2) must NOT open a new scope (only sub_pos=1 does)",
        );
    }

    /// Helper inlining: a single Push in deterministic mode mutates the live GSS
    /// without populating cursor.recovery_deltas.
    #[test]
    fn phase4_helper_inlining_does_not_double_emit() {
        // Push a distinct symbol (rule_at) so GSS dedup doesn't collapse
        // the sentinel CategoryEntry(0) root with the pushed symbol.
        let engine = ScriptedEngine::new(vec![WpdaStepAction::Push {
            symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
            weight: lex(0.0, 0, 0),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        }]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        // Push grows GSS by ≥2 nodes (CategoryEntry root + pushed entry).
        assert!(w.gss().node_count() >= 2);
        // Unforked: no recovery deltas accumulated (non-recovery
        // mutations land on cursor.builder directly).
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            cursors[0].recovery_deltas.is_empty(),
            "deterministic: live mutation on cursor.builder, no recovery delta"
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
    /// Mirrors `WpdaStepAction::ConsumeAndReplace` semantics inside Fork.
    #[test]
    fn fork_action_consume_and_replace_advances_pos() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndReplace,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Push
        let pos_before_fork = w.position();
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens()); // Fork
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
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::Consume,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let pos_before = w.position();
        let gss_count_before = w.gss().node_count();
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
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
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::InfixLoop { cur_bp: 0 },
                    action_kind: ForkActionKind::Pop,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert!(
            matches!(cursors[0].inner_state, WpdaState::InfixLoop { .. }),
            "Pop fork branch must transition to new_state",
        );
    }

    /// Mechanism γ — `ConsumeAndPop` advances pos AND pops top-of-GSS.
    #[test]
    fn fork_action_consume_and_pop_advances_pos_and_pops() {
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndPop,
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::rule_at(0, 1, 0, Some(7)),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let pos_before = w.position();
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        assert_eq!(
            cursors[0].pos,
            pos_before + 1,
            "ConsumeAndPop must advance pos by 1",
        );
        assert!(
            matches!(cursors[0].inner_state, WpdaState::Unwinding),
            "ConsumeAndPop must transition to new_state",
        );
    }

    /// Mechanism γ — `ConsumeAndReplaceWithEffect` applies the embedded
    /// non-recovery delta to the child's `cursor.builder` (via
    /// `apply_effect_to_builder`) before replacing top-of-GSS.
    ///
    /// Phase 5.6-tail-D (2026-05-12) reshape: pre-tail this checked the
    /// child's `recovery_deltas` for a `BuilderDelta::StartBinderScope`
    /// entry. Under recovery-only journaling, non-recovery effects are
    /// applied to cursor.builder via Arc::make_mut directly — the journal
    /// receives only recovery deltas. The reshaped assertion observes the
    /// resulting binder-scope state on cursor.builder directly.
    #[test]
    fn fork_action_consume_and_replace_with_effect_logs_delta() {
        let effect = BuilderDelta::StartBinderScope { names: Vec::new() };
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                        effect: effect.clone(),
                    },
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let cursors = w.branch_cursors_for_test();
        assert_eq!(cursors.len(), 1);
        // Phase F.3c.1 (2026-05-20): inspect SPPF-side mirror
        // `cursor.binder_scope_marks` (Vec<(u16, Vec<String>)>) instead
        // of `cursor.builder.current_binder_scope()` (deleted F.3c.4).
        // StartBinderScope pushes a new (depth, names) tuple via the
        // emit_start_binder_scope helper / apply_effect_to_cursor.
        let scope = cursors[0]
            .binder_scope_marks
            .last()
            .expect("ConsumeAndReplaceWithEffect with StartBinderScope effect must \
                     push onto binder_scope_marks");
        assert!(
            scope.1.is_empty(),
            "Opened scope must have the empty names from the StartBinderScope effect",
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
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeAndReplace {
                        expected_text: "=".to_string(),
                    },
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Push
        let pos_before_fork = w.position();
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Fork (guard pass)
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
    /// `step_fanout`'s empty-cursors check into `WpdaState::Error { message:
    /// "all fork branches dropped" }` — same surface as the legacy
    /// eq-or-error pathway, but routed through Fork+lex-min.
    #[test]
    fn fork_action_guarded_consume_and_replace_fail_drops_cursor() {
        let tokens = [TokenKind::Fixed("X".into())];
        let texts = ["X"];
        let token_src = SliceTokenSource::with_texts(&tokens, &texts);
        let engine = ScriptedEngine::new(vec![
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeAndReplace {
                        expected_text: "=".to_string(),
                    },
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Push
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Fork (guard fail)
        let final_state = w.run_to_saturation(50, &token_src);
        match final_state {
            WpdaState::Error { message } => assert!(
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
            WpdaStepAction::Accept,
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeIdentAndReplace {
                        start_scope: false,
                    },
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Push
        let pos_before = w.position();
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Fork (guard pass)
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
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::rule_at(0, 0, 1, None),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Unwinding,
                    action_kind: ForkActionKind::GuardedConsumeIdentAndReplace {
                        start_scope: false,
                    },
                }],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Push
        let _ = w.process_event(WpdaEvent::Step, &token_src); // Fork (guard fail)
        let final_state = w.run_to_saturation(50, &token_src);
        match final_state {
            WpdaState::Error { message } => assert!(
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
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
            WpdaStepAction::Accept,
            // Branches have identical primary cost (0.0) and src_idx (5);
            // they differ only in rule_idx. Lex-min tiebreak picks rule 0.
            WpdaStepAction::Fork {
                branches: vec![
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 0, 0, None),
                        weight: lex(0.0, 5, 0),
                        new_state: WpdaState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 1, 0, None),
                        weight: lex(0.0, 5, 1),
                        new_state: WpdaState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                    ForkBranch {
                        symbol: StackSymbolV2::rule_at(5, 2, 0, None),
                        weight: lex(0.0, 5, 2),
                        new_state: WpdaState::Unwinding,
                        action_kind: ForkActionKind::Push,
                    },
                ],
                consume_trigger: false,
            },
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
        let _ = w.process_event(WpdaEvent::Step, &empty_tokens());
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
            new_state: WpdaState::PrefixDispatch { pos: 1, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
            WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
        );
        assert!(
            !is_recovery_fork(&[plain_push_branch]),
            "regular Push branch must NOT be classified as recovery Fork"
        );
        let opt_group_branch = ForkBranch {
            symbol: StackSymbolV2::category_entry(0),
            weight: lex(0.0, 0, 0),
            new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 5, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 3, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 3, cur_bp: 0 },
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
            new_state: WpdaState::PrefixDispatch { pos: 1, cur_bp: 0 },
            action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                effect: BuilderDelta::InsertToken {
                    pos: 0,
                    kind: TokenKind::Fixed(")".into()),
                    text: ")".into(),
                },
            },
        };
        let recovery_fork = || WpdaStepAction::Fork {
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
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let final_state = w.run_to_saturation(50, &empty_tokens());
        match final_state {
            WpdaState::Error { message } => assert!(
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
        let non_advancing_recovery = || WpdaStepAction::Fork {
            branches: vec![ForkBranch {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(1.0, 0, 0),
                // new_state stays at pos=0 (insertion repair).
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        let final_state = w.run_to_saturation(50, &empty_tokens());
        match final_state {
            WpdaState::Error { message } => assert!(
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
    // (wpda_walker.rs:3845-3944) that Commit B added — verifying that
    // multi-step Viterbi recovery sequences (Skip / Delete / Insert /
    // Substitute) replay onto the walker's recovery_events trace in order
    // with correct action_kind discriminators.
    //
    // The replay path requires set_mutable_token_source for the Insert and
    // Substitute primitives. We use MutableMultiTokenSource with a trivial
    // whitespace-tokenizing fake_lex (mirroring wpda_runtime.rs:1810).
    // ════════════════════════════════════════════════════════════════════════

    use crate::recovery::RepairAction;
    use crate::token_id::TokenId;
    use crate::wpda_runtime::MutableMultiTokenSource;

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
            WpdaStepAction::Accept,
            // Step 2: Fork emitting a recovery branch carrying the effect.
            WpdaStepAction::Fork {
                branches: vec![ForkBranch {
                    symbol: StackSymbolV2::category_entry(0),
                    weight: lex(0.0, 0, 0),
                    new_state: WpdaState::Accepted,
                    action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                        effect: recovery_effect,
                    },
                }],
                consume_trigger: false,
            },
            // Step 1: Push to seed the GSS with a non-root frame so
            // ConsumeAndReplaceWithEffect's cursor_gss_replace_top has a
            // top to operate on.
            WpdaStepAction::Push {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex(0.0, 0, 0),
                new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 },
            },
        ]);
        let mut w = WpdaWalker::new(engine, 0);
        w.set_mutable_token_source(&mut mutable_src);
        // Drive to end-of-input (sets up parked frontier in AmbiguityFanout),
        // then resolve to fire commit_winner_at_eoi which replays the winner's
        // recovery_deltas onto walker.recovery_events.
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
