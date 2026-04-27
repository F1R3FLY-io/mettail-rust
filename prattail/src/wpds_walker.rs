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

use crate::automata::semiring::Semiring;
use crate::gss::{WpdsGss, WpdsGssNode};
use crate::wpds_runtime::{
    pack_action_id, ActionEntry, CheckpointReason, SemanticBuilder, StackSymbolV2, SymbolKind,
    WpdsConfiguration, WpdsControl, WpdsEvent, WpdsState, WpdsTokenSource, WpdsTraceEntry,
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
    /// Fork into multiple branches; each becomes an independent frontier.
    Fork {
        branches: Vec<(StackSymbolV2, W)>,
        new_state: WpdsState,
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
                break;
            }
            self.apply_action(action, tokens);
        }
        self.state.clone()
    }

    // ─── Internal step handler ──────────────────────────────────────────────

    fn handle_step(&mut self, tokens: &dyn WpdsTokenSource) -> WpdsTransition<W> {
        let from = self.state.clone();
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
            WpdsStepAction::Fork { branches, new_state } => {
                let prev = self.top_node;
                let mut child_ids = Vec::with_capacity(branches.len());
                for (symbol, w) in branches {
                    if let Some(p) = prev {
                        let id = self.gss.push_symbol(p, symbol, self.pos, w);
                        child_ids.push(id);
                    }
                }
                self.state = WpdsState::AmbiguityFanout { branches: child_ids };
                self.maybe_prune_frontier();
                // The new_state passed in is the "post-fork" target; consumers
                // typically resolve via BranchResolved later. We retain
                // AmbiguityFanout until then.
                let _ = new_state;
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
                    (StackSymbolV2::rule_at(0, 0, 0, None), lex(1.0, 0, 0)),
                    (StackSymbolV2::rule_at(0, 1, 0, None), lex(1.0, 0, 1)),
                ],
                new_state: WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 },
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
    fn run_to_saturation_stops_on_idle() {
        let engine = ScriptedEngine::new(vec![
            WpdsStepAction::Advance(WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 }),
        ]);
        let mut w = WpdsWalker::new(engine, 0);
        let s = w.run_to_saturation(100, &empty_tokens());
        // After one advance, engine returns Idle; we stop.
        assert_eq!(s, WpdsState::PrefixDispatch { pos: 0, cur_bp: 0 });
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
}
