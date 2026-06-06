//! WPDS runtime types: reactive FSM, stack symbols, control directives.
//!
//! Stage 1 of W7 plan v5.1 (originally) — extended by Stage 6 Phase A.1 with
//! semantic-action machinery (`SemanticBuilder`, `ActionArg`, `ActionEntry`,
//! `WpdaTokenSource`, `BinderHandle`) that the codegen and walker share.
//!
//! ## Recovery note
//!
//! Recovery is walker-level: generated engines can emit weighted
//! Skip/Delete/Substitute/Insert Fork branches at PrefixDispatch dead-ends.
//! Strict parse facades disable those branches with
//! `RecoveryConfig.max_recovery_depth = 0`; explicit recovering facades keep
//! the default recovery budget and surface the committed recovery trail.
//!
//! ## Reactive contract
//!
//! `WpdaState × WpdaEvent → WpdaTransition` (pure function), per the
//! MeTTaTron-style mandate. External consumers (LSP/DAP/REPL/nREPL) drive
//! `WpdaWalker::process_event` (Stage 4) at their own pace; the
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
use std::sync::Arc;

use crate::automata::semiring::SemiringRef;
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
    /// B7 Pattern 2: marker pushed at a grouping `(` so the engine knows
    /// we're inside a precedence-reset sub-parse. The symbol's
    /// `category_src_idx` is the result category (so when Unwinding
    /// returns to this marker, we know which category's InfixLoop to
    /// resume); `bp` carries the saved outer Pratt cur_bp for restoration
    /// on `)` consumption. `rule_index_in_category` is unused (grouping
    /// is transparent — no AST node, no action fires when this marker
    /// pops).
    GroupingMarker,
    /// B7 Pattern 1 mixfix continuation marker. Pushed after an InfixLoop
    /// dispatch consumes a mixfix operator's trigger token (e.g., `?` for
    /// ternary). Carries `(category_src_idx = result_cat, rule_index = mixfix_rule)`
    /// and uses `bp` as the "operand count completed so far" — initially 0
    /// (we're about to parse parts[0]'s operand), incremented via Replace
    /// each time an inner operand returns. When count == parts.len(), the
    /// marker is ConsumeAndPop'd, firing the rule's action with arity =
    /// 1 + parts.len (LHS already on builder + parts.len inner operands).
    MixfixMarker,
    /// Opt-Group (2026-04-29): marker for the inner-position walk of a
    /// taken `OptionalGroup`. The `u8` payload is the `sub_pos` (1..=inner.len()+1)
    /// indicating which inner position to walk next. Pushed when entering
    /// a taken optional group at sub_pos=1; replaced via Replace as
    /// inner positions advance; popped at sub_pos = inner.len()+1 by
    /// `OptGroupFinalize`. `category_src_idx` and `rule_index_in_category`
    /// identify the parent rule. `bp` carries the OUTER rule's outer_bp
    /// (so the parent BinderRule's outer_bp is recoverable on group exit).
    /// On Unwinding when this is on top, the engine transitions to
    /// `WpdaState::OptionalGroup { sub_pos: payload }`.
    OptionalGroupAt(u8),
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
    pub fn infix_continuation(category_src_idx: u16, rule_index_in_category: u16, bp: u8) -> Self {
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
    pub fn collection_marker(result_src_idx: u16, rule_idx: u16, accumulator_id: u8) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(accumulator_id),
            kind: SymbolKind::CollectionMarker,
        }
    }

    /// B7 Pattern 2: construct a grouping-marker symbol. `outer_bp` is
    /// the saved Pratt cur_bp at the open `(`; on close `)`, the engine
    /// transitions to `WpdaState::InfixLoop { cur_bp: outer_bp }` so
    /// surrounding operators continue at the original precedence level.
    pub fn grouping_marker(result_src_idx: u16, outer_bp: u8) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: 0,
            bp: Some(outer_bp),
            kind: SymbolKind::GroupingMarker,
        }
    }

    /// B7 Pattern 1: construct a mixfix continuation marker. `bp` carries
    /// the count of inner operands already parsed (0..=parts.len). On
    /// each Unwinding back to this marker, the engine reads `bp`, demands
    /// the corresponding `parts[bp].following_terminal`, increments via
    /// Replace, and pushes the next operand's CategoryEntry. When `bp`
    /// equals `parts.len`, the marker is ConsumeAndPop'd (firing the
    /// mixfix rule's action with arity = 1 + parts.len).
    pub fn mixfix_marker(result_src_idx: u16, rule_idx: u16, operands_completed: u8) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(operands_completed),
            kind: SymbolKind::MixfixMarker,
        }
    }

    /// Opt-Group: construct an `OptionalGroupAt(sub_pos)` marker for the
    /// inner-position walk of a taken optional group. `outer_bp` is the
    /// outer rule's outer_bp, preserved across the group so on group exit
    /// the parent `BinderRule` resumes at the correct precedence level.
    pub fn optional_group_at(
        result_src_idx: u16,
        rule_idx: u16,
        sub_pos: u8,
        outer_bp: u8,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(outer_bp),
            kind: SymbolKind::OptionalGroupAt(sub_pos),
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
        StackSymbolV2 { kind: SymbolKind::Return, ..self }
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
            },
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
            SymbolKind::GroupingMarker => {
                write!(f, "⟨cat#{}.group⟩{}", self.category_src_idx, bp_suffix)
            },
            SymbolKind::MixfixMarker => write!(
                f,
                "⟨cat#{}.rule#{}.mixfix⟩{}",
                self.category_src_idx, self.rule_index_in_category, bp_suffix
            ),
            SymbolKind::OptionalGroupAt(sub_pos) => write!(
                f,
                "⟨cat#{}.rule#{}.opt@{}⟩{}",
                self.category_src_idx, self.rule_index_in_category, sub_pos, bp_suffix
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
/// External consumers inspect this via [`WpdaWalker::state`] (Stage 4).
///
/// Stage 3.5b (2026-05-01): adds `Hash` derive so cursor configurations
/// `(state, gss_node_id, pos)` can be the key for `merge_equivalent_cursors`
/// — the WPDS ⊕-merging step that collapses paths reaching the same
/// configuration via `Semiring::plus`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WpdaState {
    /// Initial state at category entry; parser awaits its first event.
    Ready { min_bp: u8 },
    /// Matching on the current token to choose a prefix rule.
    PrefixDispatch { pos: usize, cur_bp: u8 },
    /// Looking for an infix/postfix operator with binding power > `cur_bp`.
    InfixLoop { cur_bp: u8 },
    /// Phase F.13 chain_10000 Exp 6 (Plan A first substage, 2026-05-26):
    /// iterative absorption of an iterative-eligible infix operator's
    /// RHS. Entered after `WpdaStepAction::IterativeChainAbsorb`
    /// consumes the operator token; the engine dispatches the RHS
    /// prefix and immediately re-enters `InfixChainIterative` on
    /// RHS-return rather than re-pushing a per-iteration Return RuleAt
    /// onto the GSS. Witness for chain continuation:
    /// `frontier_top.kind == Return` AND
    /// `frontier_top.label == (result_src_idx, rule_idx)`. See
    /// `prattail/docs/design/plans/chain-10000-experiments-ledger.md`
    /// row 6 and the Plan A design doc.
    ///
    /// Engine codegen emits this state for iterative-eligible same-category
    /// operators when the chain recognizer elects the iterative path.
    InfixChainIterative {
        /// Result category index — same as the original `InfixLoop`'s
        /// `state_cat_src_idx` since iterative-eligible operators are
        /// same-category (`!is_cross_category`).
        result_src_idx: u16,
        /// Operator rule index within the result category.
        rule_idx: u16,
        /// `cur_bp` at chain entry. Restored on chain exit.
        outer_bp: u8,
        /// Right binding power of the operator. RHS sub-parses dispatch
        /// at `cur_bp: rhs_bp` per Plan A invariant (I3).
        rhs_bp: u8,
    },
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
        /// Phase 4 #1.B (2026-05-11): codegen-stamped slot identifier
        /// within the rule. For Class-5 single-slot rules and Phase-4-
        /// #1 multi-slot rules without outer collection nesting,
        /// `slot_idx == accumulator_id`. The CollectionMarker's `bp`
        /// field carries this value at push time. Used by the
        /// 3-tuple-keyed `(close, sep)` lookup in
        /// `emit_collection_loop_arm` to disambiguate sibling slots
        /// within the same rule.
        slot_idx: u8,
        /// Phase 4 #5b (2026-05-12): key/value dispatch phase for
        /// HashMap collections. Three values:
        /// - `0`: outer dispatch — 3-branch Fork (close / inter-pair-sep
        ///   / first-key element). Vec/HashBag/HashSet always stay at
        ///   `0`. For HashMap, also the state after a value parses
        ///   (the pair is complete; expect close or `,`).
        /// - `1`: just parsed a key (HashMap only); expect the
        ///   key/value separator `:`. Single-arm Consume → `kv_phase: 2`.
        /// - `2`: just consumed `:` (HashMap only); Push CategoryEntry
        ///   for the value parse → PrefixDispatch. After the value
        ///   returns, walker restores `kv_phase: 0` based on the
        ///   slot's collection_stack parity.
        ///
        /// For non-HashMap slots, `kv_phase` is always `0` and the
        /// dispatch is identical to pre-Phase-4-#5b behavior.
        ///
        /// The walker patches `kv_phase` on every transition into
        /// `CollectionLoop` based on `cursor.collection_stack[acc_id].len()`
        /// parity AND the per-slot `kv_separator_for_collection`
        /// engine query — keeping the engine's `step` function pure.
        kv_phase: u8,
    },
    /// B7 (2-token open delimiter): after the prefix arm consumed the
    /// open keyword (e.g. `"list"`) and pushed the `CollectionMarker`,
    /// this state demands the literal `(` next, consumes it, and
    /// transitions to `PrefixDispatch` to parse the first element. The
    /// state exists because the lexer tokenizes `list(` as two separate
    /// `Fixed` tokens (whitespace between them is allowed), so a single
    /// `ConsumeAndPush` cannot atomically consume both. For 3-element
    /// synthetic patterns (no synthetic paren — e.g. RhoCalc's `"{" ... "}"`),
    /// the prefix arm transitions directly to `PrefixDispatch` and skips
    /// this state.
    CollectionOpenParen {
        /// Result category index (the collection's category).
        result_src_idx: u16,
        /// Rule index within the result category (selects finalize action).
        rule_idx: u16,
        /// Element category index — what the first (and subsequent)
        /// element(s) are parsed as. For self-collections this equals
        /// `result_src_idx`; for cross-cat collections (e.g. Calculator's
        /// `![Vec<Proc>] as List`) it differs and the engine must push
        /// a `CategoryEntry(element_src_idx)` after consuming `(`.
        element_src_idx: u16,
        /// Outer Pratt cur_bp to restore on close-delimiter consumption.
        outer_bp: u8,
    },
    // (B7 Pattern 2 grouping uses no dedicated state — the prefix arm
    // emits ConsumeAndPush(GroupingMarker, new_state=PrefixDispatch{cur_bp:0})
    // directly. The marker's `bp` field carries the saved outer cur_bp
    // for restoration. When Unwinding sees a GroupingMarker on top, the
    // engine demands `)`, ConsumeAndPops, and resumes
    // InfixLoop{cur_bp: marker.bp}.)
    /// B7 Pattern 1 mixfix continuation. After Unwinding-MixfixMarker
    /// consumes the per-operand following separator, the engine transitions
    /// here to ReplaceAndPush the next operand's CategoryEntry. The state
    /// carries `completed_idx` (= number of inner operands fully parsed
    /// AND whose separator just got consumed) so the next step can index
    /// into `mixfix_parts(result_src, rule_idx)` to find the next operand
    /// category. Marker on the GSS is updated to reflect the new
    /// `completed_idx` via Replace.
    MixfixContinuation {
        /// Result category index (the mixfix rule's result cat).
        result_src_idx: u16,
        /// Rule index within the result category.
        rule_idx: u16,
        /// Number of inner operands whose separator has been consumed
        /// (i.e., index of the NEXT inner operand to parse).
        completed_idx: u8,
    },
    /// L12 follow-up B6 step 3 (2026-05-07): walk the literal sequences
    /// between mixfix operands. After an inner operand `completed_idx`
    /// returns to Unwinding-MixfixMarker, the walker transitions here
    /// with `kind = 0` to consume each literal in
    /// `parts[completed_idx].following_terminals` in order. Once
    /// exhausted: if `completed_idx + 1 == parts_len`, Pop (rule done);
    /// else transition to `kind = 1` to consume each literal in
    /// `parts[completed_idx + 1].preceding_terminals`. Once those are
    /// exhausted, transition to MixfixContinuation { completed_idx + 1 }
    /// to push the next operand's CategoryEntry.
    ///
    /// Generalizes over the entire class of postfix-mixfix shapes
    /// (POutput-class) — supports any number of literals between/around
    /// operands. Single-literal sequences (Tern's `:` between `b` and
    /// `c`) are the degenerate case (kind=0, sub_pos=0..1).
    MixfixLiteralRun {
        /// Result category index.
        result_src_idx: u16,
        /// Rule index within the result category.
        rule_idx: u16,
        /// Index of the just-completed inner operand. `following_terminals`
        /// of `parts[completed_idx]` are consumed when `kind == 0`;
        /// `preceding_terminals` of `parts[completed_idx + 1]` are
        /// consumed when `kind == 1`.
        completed_idx: u8,
        /// 0 = consuming following_terminals; 1 = consuming
        /// preceding_terminals.
        kind: u8,
        /// Index into the literal vector being walked.
        sub_pos: u8,
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
    /// Opt-Group (2026-04-29): mid-optional-group dispatch. The engine
    /// transitioned here from `BinderRule` upon encountering a
    /// `BinderPosition::OptionalGroup`; on entry (`sub_pos == 0`), it
    /// peeks the group's FIRST-set:
    /// - If matched → the group is taken: `sub_pos := 1`, the
    ///   action accumulator records `is_present := true`, and dispatch
    ///   walks the inner positions identically to BinderRule (each
    ///   ParamParse pushes an `ActionArg::Term` to the standard arg
    ///   collection; at sub-position past the inner positions list,
    ///   the engine ConsumeAndReplaces back into the OUTER BinderRule
    ///   at `outer_next_pos` with an `ActionArg::Optional(Some(args))`
    ///   pushed for the action body to extract).
    /// - If not matched → the group is skipped: an
    ///   `ActionArg::Optional(None)` is pushed, and the engine
    ///   ConsumeAndReplaces back into the OUTER BinderRule at
    ///   `outer_next_pos` (no token consumed).
    ///
    /// `group_idx` indexes into per-rule FIRST-set tables emitted as
    /// `FIRST_SET_GROUP_<cat>_<rule>_<group_idx>` so the engine can
    /// look up which tokens trigger entry. Inner positions are stored
    /// in the rule's `BinderShape.positions` as recursive
    /// `BinderPosition::OptionalGroup` entries — the engine resolves
    /// them by indexing into the outer rule's positions list.
    OptionalGroup {
        /// Result category index (parent rule's result cat).
        result_src_idx: u16,
        /// Rule index within the result category (parent rule).
        rule_idx: u16,
        /// Index of this Optional group within the parent rule's
        /// positions list. Used to look up the per-group FIRST-set
        /// and inner-position list.
        group_idx: u8,
        /// Sub-position within the optional group's inner positions.
        /// `0` = peek FIRST-set; `1..=inner.len()` = walk inner
        /// positions (literals, params, guards, nested optionals).
        sub_pos: u8,
        /// Outer Pratt cur_bp to restore when the group completes.
        outer_bp: u8,
    },
    /// Phase 5b: mid-binder-list-loop (`^[xs]`). Captures `Ident,
    /// separator, Ident, separator, ..., close` into the active binder
    /// scope, then transitions back to BinderRule at `next_pos`.
    ///
    /// B8 / Class 3 ZIP-MAP-SEP (2026-05-08): `sub_pos` indexes the
    /// per-iteration inner walk:
    /// - 0 = peek close/sep/first-inner — choose between close-branch,
    ///   sep-branch (next iteration), or first-inner-position dispatch.
    /// - 1..=inner_positions.len() = walking inner_positions[sub_pos-1].
    /// - inner_positions.len()+1 = end-of-iteration, dispatch back to
    ///   sub_pos:0 to peek close/sep/next-iteration.
    /// For PNew-style rules (single BinderIdent inner) the dispatch
    /// collapses to the legacy 3-branch fork at sub_pos=0.
    BinderListLoop {
        result_src_idx: u16,
        rule_idx: u16,
        body_src_idx: u16,
        outer_bp: u8,
        /// Position of the BinderListLoop slot in the rule's positions list.
        marker_pos: u8,
        /// Position to advance to after the close delim is consumed.
        next_pos: u8,
        /// B8: sub_pos indexes the per-iteration inner walk; 0 for the
        /// PNew-style legacy fast path (no inner walk).
        sub_pos: u8,
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
        /// Precedence floor for the sub-parse's `PrefixDispatch`/`InfixLoop`.
        ///
        /// Set per-emission-context:
        /// - InfixLoop cross-cat infix dispatch (`engine_impl.rs:920-925`)
        ///   sets this to the operator's `r_bp` so the cross-cat operand
        ///   sub-parse respects the outer Pratt precedence (e.g.
        ///   `LtStr: Str < Str : Bool` with r_bp=7 prevents `==` at l_bp=2
        ///   from leaking into the RHS sub-parse).
        /// - PrefixDispatch CrossCatProjection/ImplicitCast/CrossCatPrefixUnary
        ///   arms set this to `0` because they're at the start of a fresh
        ///   operand (no enclosing Pratt precedence to enforce inside the
        ///   sub-parse).
        ///
        /// Renamed from `outer_bp` 2026-05-13 (D-strings fix). The prior
        /// semantics — "the outer Pratt cur_bp to restore after delegation"
        /// — was an obsolete description: the outer cur_bp is restored via
        /// the wrapping Return symbol's `bp` field at Return-pop time, not
        /// via this state. This field is now the SUB-PARSE's cur_bp.
        inner_cur_bp: u8,
    },
    /// Multiple GSS branches active simultaneously; awaiting resolution.
    /// The `branches: Vec<GssNodeId>` field lists the GSS-tip node ids of
    /// every live branch. Per-branch micro-state (pos, weight, inner
    /// state) is stored out-of-band on the walker as
    /// `WpdaWalker::branch_cursors: Vec<BranchCursor<W>>` parallel to
    /// this vector — the i-th `branches` entry corresponds to the i-th
    /// `branch_cursors` entry. The reason for the split is that `WpdaState`
    /// is non-generic but per-branch weight requires the walker's `W`
    /// parameter; storing weights inside the state enum would force
    /// `WpdaState` to be generic and cascade through every consumer.
    AmbiguityFanout { branches: Vec<GssNodeId> },
    /// WPDS poststar/prestar saturation in progress; `delta_size` frontier size.
    Saturating { delta_size: usize },
    /// Popping continuation frames after a value was produced.
    Unwinding,
    /// F1 follow-up Cluster A (paren+postfix+cross-cat infix, 2026-05-10):
    /// after a cross-cat-grouping inner CategoryEntry has been popped, the
    /// next step demands `)` and ConsumeAndReplaces the GroupingMarker on
    /// top with a CategoryEntry of the inner cat. This preserves the
    /// cross-cat dispatch context after `)` so subsequent infix dispatch
    /// (e.g., `==` for `Bool::parse("(3!) == 6")`) finds the operator in
    /// the inner cat's table. The GroupingMarker's `bp` field carries
    /// outer_bp (saved cur_bp at the open paren); we restore that BP for
    /// the post-`)` InfixLoop.
    ///
    /// State transition: `Unwinding-CategoryEntry` (when pred=GroupingMarker)
    /// → here (CategoryEntry popped) → `InfixLoop { cur_bp: outer_bp }`
    /// (after `)` is consumed and CategoryEntry(inner_cat) replaces the
    /// GroupingMarker on the GSS).
    GroupingClosePreservingInner {
        /// The inner category whose CategoryEntry was just popped. Re-pushed
        /// as the new GSS top so subsequent infix dispatch sees the inner
        /// cat (typically the cross-cat infix's LHS source category).
        inner_cat_src_idx: u16,
    },
    /// Parse complete; result available via the walker's accept hook.
    Accepted,
    /// Parse failed; recovery may repair via the walker's recovery hook.
    Error { message: String },
}

impl WpdaState {
    /// Whether this state is terminal (Accepted or Error).
    pub fn is_terminal(&self) -> bool {
        matches!(self, WpdaState::Accepted | WpdaState::Error { .. })
    }
}

/// Stage 3.5b (2026-05-01): the result of `WpdaWalker::resolve_at_end_of_input`,
/// the WPDS-correct end-of-stream resolution path. Replaces the prior
/// mid-stream `commit_winner` semantics where the Walker would commit any
/// time `branch_cursors` collapsed to one alive cursor — that was
/// architecturally a bug (Bug 1: mid-stream commit). The new contract:
/// configurations carry through to EOI, ⊕-merge en route, and the answer
/// is the lex-min weighted Accepted configuration at `pos == tokens.len()`.
///
/// Source-order tiebreak applies when ≥2 configurations tie on
/// `LexicographicWeight`'s 4-tuple (which is structurally rare: equal
/// `primary, lex_alt_idx, src_idx, rule_idx`). When that tiebreak fires,
/// emit ambiguity warning + commit earliest source-ordered branch +
/// return `AcceptedAmbiguous`.
#[derive(Debug)]
pub enum WpdaResolveResult<W: SemiringRef> {
    /// M7c (2026-05-13): one or more Accepted configurations at EOI.
    ///
    /// `weights` and `terms` are parallel vectors of length ≥ 1; index
    /// `i` is the i-th derivation's weight and term. Length 1 = single
    /// unambiguous parse; length N > 1 = N preserved derivations (the
    /// `Ambiguous(Vec<Term>)` end-state of the user's mandate
    /// "ambiguity preserved to EOI unless ruled out by evidence").
    ///
    /// **Replaces** the pre-M7c single-result `Accepted{weight, term}`
    /// + `AcceptedAmbiguous{weight, term, equivalence_class_size}` pair
    /// — the M7c semantics carry ALL derivations end-to-end rather
    /// than collapsing to one via lex-min.
    Accepted {
        weights: Vec<W>,
        terms: Vec<Arc<dyn std::any::Any + Send + Sync>>,
        /// Option C / C6 (2026-05-15): each accepting cursor's SPPF root
        /// id. Parallel to `weights` and `terms` (same length). Used by
        /// the SPPF realization path (`sppf_realize::realize_all`) in
        /// C7+ once the facade switches over. Through C6-C8 the SPPF
        /// path coexists with `terms`; C9 removes `terms` entirely.
        ///
        /// `crate::sppf::SPPF_ID_NONE` sentinel here means the cursor
        /// had no SPPF root (e.g., empty sppf_stack at EOI), which
        /// indicates a dual-mode bootstrap gap rather than a structural
        /// problem.
        roots: Vec<crate::sppf::SppfId>,
    },
    /// Cluster H (2026-05-29): the walker reached a VALID prefix parse —
    /// at least one cursor is `is_accepting_config` — but parked at a
    /// position STRICTLY BEFORE logical EOI, and NO cursor reached
    /// logical EOI. This is the "trailing tokens" case: the grammar
    /// accepts a proper prefix of the input but the remaining tokens
    /// cannot be consumed.
    ///
    /// Distinguished from the Phase E Fix A "premature lex-Fork
    /// acceptance" drop: that drop fires when a SHORT prefix-accept
    /// COEXISTS with a longer full-EOI parse (the short one is genuinely
    /// premature and is discarded so the full parse wins). This variant
    /// fires ONLY when there is NO full-EOI parse at all — so the prefix
    /// is the best (and only) accepting derivation, and the facade must
    /// surface it as `Ok(term)` with `*pos = position` so the wrapper's
    /// `pos < tokens.len()` check emits a structured
    /// `ParseError::TrailingTokens` (carrying the partial AST in
    /// recovering mode) rather than a misleading `UnexpectedToken`.
    ///
    /// `weights`/`terms`/`roots` are parallel (length ≥ 1), mirroring
    /// `Accepted`; `position` is the prefix boundary (the first
    /// unconsumed token index). Disambiguation is preserved: if multiple
    /// prefix-accepting cursors tie at the same furthest position, ALL
    /// are carried (the `Ambiguous` end-state still applies to the
    /// prefix).
    AcceptedWithTrailing {
        weights: Vec<W>,
        terms: Vec<Arc<dyn std::any::Any + Send + Sync>>,
        roots: Vec<crate::sppf::SppfId>,
        position: usize,
    },
    /// Zero accepting configurations at EOI — input cannot be parsed by
    /// the grammar. `position` is where the cursor stalled (max position
    /// reached among dead cursors).
    ParseError { message: String, position: usize },
    /// Driver hit `max_steps` budget before reaching EOI. Caller may
    /// resume by extending the budget.
    MaxStepsExceeded { position: usize },
    /// The walker was configured with a cursor-count bound and the live
    /// frontier exceeded that bound during a `step_fanout` iteration.
    ///
    /// The walker fails loudly instead of dropping cursors by weight. Callers
    /// can react: relax the budget, switch to a less-ambiguous grammar
    /// variant, surface a structured "input too ambiguous" error to the user,
    /// etc.
    ///
    /// `budget` is the configured limit; `actual` is the frontier size
    /// that triggered the overflow; `position` is the input position when
    /// the overflow was detected.
    AmbiguityBudget {
        budget: usize,
        actual: usize,
        position: usize,
    },
}

/// M11.7 (2026-05-14): cursor-count bounding policy for the walker.
///
/// Replaces the M11.4-era `WpdaWalker::beam_size: Option<usize>` field
/// with an explicit enum that makes the possible bounding modes mutually
/// exclusive at the type level.
///
/// **Default**: `Unbounded` — pure ambiguity preservation, no cursor
/// dropping. This is the M11 mandate-compliant baseline.
///
/// **Bounded modes** (opt-in):
/// - `BeamSize(k)`: compatibility name for the older beam-size API. It now
///   has the same structured-overflow semantics as `AmbiguityBudget(k)`:
///   when the frontier would exceed `k`, the walker emits an
///   `AmbiguityBudget` error instead of pruning the frontier.
/// - `AmbiguityBudget(n)`: check the frontier size against `n` cursors. If
///   the frontier would exceed `n`, the walker emits a structured
///   `WpdaResolveResult::AmbiguityBudget` error rather than silently
///   dropping cursors. Caller can detect the overflow and react (relax
///   budget, switch strategy, surface to user).
///
/// **Mutual exclusion**: the enum constructor enforces that exactly one
/// mode is active at a time. `WpdaWalker::with_bounding_mode(mode)`
/// replaces the prior `with_beam_size(k)` API; the legacy methods are
/// retained as compatibility shims.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CursorBoundingMode {
    /// Default — pure ambiguity preservation; no cursor dropping.
    Unbounded,
    /// Compatibility name for the older beam-size API. This does not prune:
    /// it reports structured `AmbiguityBudget` overflow when the frontier
    /// exceeds the configured size.
    BeamSize(usize),
    /// Mandate-compliant cursor-count bounding. When the live frontier
    /// would exceed the budget, emit a structured `AmbiguityBudget`
    /// error rather than silently dropping cursors.
    AmbiguityBudget(usize),
}

impl Default for CursorBoundingMode {
    fn default() -> Self {
        CursorBoundingMode::Unbounded
    }
}

/// Stage 3.5b (2026-05-01): error returned by `WpdaWalker::run_to_end_of_input`
/// when the driver exhausts its `max_steps` budget before reaching EOI
/// or a terminal state. Caller may extend the budget and resume by
/// calling `run_to_end_of_input` again with a larger `max_steps`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WpdaMaxStepsExceeded {
    pub position: usize,
}

impl std::fmt::Display for WpdaMaxStepsExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "WPDS walker exceeded max_steps before reaching end of input (position={})",
            self.position
        )
    }
}

impl std::error::Error for WpdaMaxStepsExceeded {}

/// Events that drive the reactive FSM forward.
///
/// Generic over the weight type `W` so consumers can read resolved branch
/// weights. The `LexicographicWeight` of Stage 2 will be the canonical
/// instantiation; until then any [`Semiring`] suffices.
#[derive(Debug, Clone)]
pub enum WpdaEvent<W: SemiringRef> {
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
    BranchResolved { winner: GssNodeId, weight: W },
    /// A semantic action fired during AST assembly.
    /// `action_id` is the codegen-assigned identifier; `args` are token positions
    /// captured by the action.
    SemanticActionFired { action_id: u32, args: Vec<usize> },
    /// Request the walker to record a checkpoint at the current configuration.
    Checkpoint { reason: CheckpointReason },
    /// Inspect the current state without mutating it.
    Inspect,
}

/// Reason a checkpoint is being recorded.
///
/// Used by `WpdaIncrementalSession` (Stage 5) to decide which checkpoints to
/// retain when memory pressure rises.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckpointReason {
    /// Periodic checkpoint at fixed interval (LSP token-level snapshots).
    PeriodicInterval,
    /// Natural boundary (end of category, top of stack empty).
    NaturalBoundary,
    /// Consumer requested via `WalkerConsumer::on_event` returning `Checkpoint`.
    ConsumerRequest,
    /// Pre-pause snapshot before halting (paired with `WpdaControl::Pause`).
    PrePause,
}

/// Output of one [`WpdaState`] × [`WpdaEvent`] transition.
#[derive(Debug, Clone)]
pub enum WpdaTransition<W: SemiringRef> {
    /// `Inspect` event; no state change.
    NoChange,
    /// State changed; optional trace entry recorded.
    Transition {
        new_state: WpdaState,
        trace: Option<WpdaTraceEntry>,
    },
    /// Checkpoint recorded at the current configuration.
    Checkpoint { config: WpdaConfiguration<W> },
    /// Parse complete; result is available via the walker.
    Done { state: WpdaState },
}

/// A WPDS configuration snapshot suitable for checkpointing or replay.
///
/// Generic over weight type `W`. Stage 5's `WpdaIncrementalSession` uses
/// `BTreeMap<usize, WpdaConfiguration<LexicographicWeight>>` for its
/// checkpoint cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WpdaConfiguration<W: SemiringRef> {
    /// Token position at the time of snapshot.
    pub pos: usize,
    /// State at the time of snapshot.
    pub state: WpdaState,
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
pub struct WpdaTraceEntry {
    /// Position when the transition fired.
    pub pos: usize,
    /// State before the transition.
    pub from_state: WpdaState,
    /// State after the transition.
    pub to_state: WpdaState,
    /// Stack depth after the transition.
    pub stack_depth: usize,
}

// ══════════════════════════════════════════════════════════════════════════════
// Control directives (M6: WpdaControl::Pause exists per Rholang §13.1)
// ══════════════════════════════════════════════════════════════════════════════

/// Control directive returned by a [`WalkerConsumer`] (Stage 5) after each
/// event. Determines whether the walker continues, snapshots, halts, or
/// awaits external resumption.
///
/// Mirrors `CekControl` from the surveyed `cek.rs` API and adds the `Pause`
/// variant promised by `docs/design/made/rholang-target/design.md` §13.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WpdaControl {
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
/// during `WpdaEngine::step`.
///
/// The walker holds a reference to a concrete impl during a parse session
/// (via `WpdaWalker::attach_token_source`). The engine's `step()` peeks
/// the next token to decide BP gating, cross-cat dispatch, etc.
pub trait WpdaTokenSource {
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

    /// L4 (2026-04-28): non-primary alternative interpretations of position
    /// `pos`. Returns the alternatives BEYOND the primary `peek_kind`. The
    /// default is empty (no lex ambiguity); concrete sources backed by a
    /// `LexStream` (see `MultiTokenSource`) override this.
    fn peek_alternatives(&self, _pos: usize) -> &[crate::lexer_types::LexAlternative] {
        &[]
    }

    /// Whether position `pos` has multiple alternatives — i.e., the lex
    /// substrate found 2+ accepting `TokenKind` interpretations at this
    /// byte position.
    fn is_ambiguous_at(&self, pos: usize) -> bool {
        !self.peek_alternatives(pos).is_empty()
    }

    /// Per-position end byte for alternative `alt_idx`. Returns `None` for
    /// sources that don't track byte offsets (the default `SliceTokenSource`).
    fn end_byte(&self, _pos: usize, _alt_idx: usize) -> Option<usize> {
        None
    }

    /// M3 (2026-05-13): return the target token-position after consuming
    /// alternative `alt_idx` from `pos`.
    ///
    /// For LINEAR sources (`SliceTokenSource`, `MultiTokenSource`,
    /// `MutableMultiTokenSource`), the default `Some(pos + 1)` is correct:
    /// all alternatives at the same position share the same downstream
    /// timeline.
    ///
    /// For LATTICE sources (`LatticeTokenSource`, M3 below), `pos` is a
    /// DAG node-id and each alt's `target_node` may differ — so the
    /// override returns the alt's `target_node`. This is the mechanism
    /// that lets the WPDS walker advance Fork branches to DIFFERENT
    /// downstream positions purely via `cursor.pos`, with NO per-cursor
    /// sidecar state.
    fn next_pos(&self, pos: usize, _alt_idx: usize) -> Option<usize> {
        if pos < self.len() {
            Some(pos + 1)
        } else {
            None
        }
    }

    /// Whether token positions form a linear token-index space where every
    /// consumed token advances from `pos` to `pos + 1`.
    ///
    /// Linear sources can soundly interpret a range `[start, finish)` as a
    /// contiguous token window. DAG/lattice sources use node ids instead of
    /// token indices, so callers must not scan numeric ranges as token
    /// windows unless this returns `true`.
    fn positions_are_linear_tokens(&self) -> bool {
        true
    }

    /// M6c.8.2 (2026-05-14): index of the canonical EOF position the
    /// walker must reach for a parse to be Accepted.
    ///
    /// Default: `self.len().saturating_sub(1)` — for slice and
    /// `MultiTokenSource` sources, the EOF sentinel is the last token
    /// in the flat sequence.
    ///
    /// `LatticeTokenSource` overrides to return `self.dag.eof_node`,
    /// the DAG node anchored at `byte_start = input.len()`. The DAG
    /// may contain orphan nodes (allocated by `lex_dag_core`'s
    /// M6c.7.1 soft-fail for secondary-alt dead-ends) at indices
    /// AFTER the EOF sentinel, so `len() - 1` is NOT generally the
    /// EOF index for lattice sources.
    ///
    /// Used by `is_logical_eoi` (walker) and the facade's
    /// trailing-token check.
    fn eof_node(&self) -> usize {
        self.len().saturating_sub(1)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// M6c.6.4 (2026-05-14): LexAltRuleInfo + LexForkSite
// ══════════════════════════════════════════════════════════════════════════════

/// M6c.6.4: the codegen-baked classification of which grammar rule
/// (if any) consumes a given `TokenKind` at a given dispatch site for
/// a given category.
///
/// The lex-Fork (`emit_lex_fork_at_prefix_dispatch` /
/// `emit_lex_fork_at_infix_loop`) consults the per-grammar
/// `lex_alt_rule_for_prefix` / `lex_alt_rules_for_infix` functions
/// against each alternative kind in the lex DAG at the current
/// position. A `None` result drops the alt branch (rule-out by
/// evidence — no rule in this cat consumes this kind at this site).
/// Prefix dispatch returns at most one rule, while infix dispatch
/// may return multiple same-token operator candidates. Each
/// `LexAltRuleInfo { rule_idx, kind }` emits a Fork branch whose
/// shape is determined by `kind`:
///
/// - `Atomic`: atomic-literal consumption via `LexAlt` + `with_kind_return`
///   + `Unwinding` (M6c.3).
/// - `PrefixOp { body_src_idx }`: unary prefix via `LexAltPrefixOp` +
///   plain `rule_at(slot=1)` + `BinderRule { body_src_idx, outer_bp }`.
/// - `PostfixOp { l_bp, result_src_idx }`: unary postfix via
///   `LexAltPostfixOp` + `rule_at(slot=0).with_kind_return()` + `Unwinding`,
///   gated by `l_bp >= cur_bp`.
/// - `InfixOp { l_bp, r_bp, result_src_idx }`: binary infix via
///   `LexAltInfixOp` + `rule_at(slot=0).with_kind_return()` +
///   `PrefixDispatch { cur_bp: r_bp }` (same-cat) or
///   `CrossCatDelegate { inner_cur_bp: r_bp }` (cross-cat).
/// - `MixfixFirstTrigger { l_bp, result_src_idx }`: mixfix first
///   trigger via `LexAltMixfixOp` + `mixfix_marker` symbol +
///   `PrefixDispatch { cur_bp: 0 }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexAltRuleInfo {
    /// Per-category rule index (stable indexing matching the
    /// codegen's per-cat rule Vec).
    pub rule_idx: u16,
    /// Shape of the rule + dispatch site, drives the walker apply
    /// arm choice.
    pub kind: LexAltRuleKind,
}

/// M6c.6.4: classification of which lex-Fork branch shape to emit
/// for a `(cat, kind)` match at a given dispatch site.
///
/// See [`LexAltRuleInfo`] for the per-kind dispatch semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexAltRuleKind {
    /// Atomic-literal rule (e.g., `NumLit`, `BoolLit`). M6c.3 path.
    Atomic,
    /// Same-cat unary prefix rule (e.g., `Neg . a:Int |- "-" a : Int`).
    /// `body_src_idx` = operand cat index (= cat_src_idx for same-cat).
    PrefixOp { body_src_idx: u16 },
    /// Unary postfix rule (e.g., `Fact . a:Int |- a "!" : Int`).
    /// `l_bp` = left binding power (operand priority gate).
    /// `result_src_idx` carried for cross-cat-postfix completeness.
    PostfixOp { l_bp: u8, result_src_idx: u16 },
    /// Binary infix rule (e.g., `AddInt . a, b:Int |- a "+" b : Int`,
    /// or cross-cat `EqInt . a, b:Int |- a "==" b : Bool`).
    /// `l_bp`/`r_bp` are the Pratt binding powers. `result_src_idx`
    /// differs from `state_cat` for cross-cat infix.
    InfixOp { l_bp: u8, r_bp: u8, result_src_idx: u16 },
    /// Mixfix rule's first trigger only (e.g., `Tern . c, t, e:Int |-
    /// c "?" t ":" e : Int` — only the `?` trigger goes through
    /// InfixLoop dispatch; subsequent triggers are handled by
    /// `MixfixLiteralRun` state machine).
    MixfixFirstTrigger { l_bp: u8, result_src_idx: u16 },
}

/// M6c.6.4: dispatch-site discriminator for `lex_alt_rule_for_*`
/// table lookup. The same `(cat, TokenKind)` pair may bind to
/// DIFFERENT rules depending on whether the walker is in
/// PrefixDispatch (looking for atomic literals or prefix
/// operators) or InfixLoop (looking for postfix/infix/mixfix-first-
/// trigger operators).
///
/// Splitting the lookup by site cleanly resolves cases like
/// `Fixed("-")`: at PrefixDispatch it binds to the cat's unary `Neg`
/// rule; at InfixLoop it binds to the cat's binary `SubInt` rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexForkSite {
    /// Dispatch happens in `WpdaState::PrefixDispatch`. Atomic
    /// literals + unary prefix operators are valid here.
    PrefixDispatch,
    /// Dispatch happens in `WpdaState::InfixLoop`. Unary postfix +
    /// binary infix + mixfix-first-trigger operators are valid here.
    InfixLoop,
}

// M4 (2026-05-13): `LexOverride` and `CursorViewSource` DELETED.
// These were the per-cursor sidecar mechanism for lex-alternative
// commitment (commits 3290e05 + ed53ea3). Under the WPDS-stack-purity
// principle (`feedback_never_disambiguate_early.md`), per-cursor
// state outside `(p, w, pos, builder, recovery_deltas)` violates the
// WPDS model. Replaced by `LatticeTokenSource` (M3) where alt identity
// lives in the SHARED input DAG and the cursor's `pos: usize` (= DAG
// node-id) suffices to distinguish alt timelines.

/// L10 (2026-04-28): a token source that supports incremental edits.
///
/// LSP integrations and lex-fork commit (L6) need to mutate the lex stream
/// after parsing has begun:
/// - **`replace_range`**: replace a byte range with new bytes and re-lex
///   the affected token positions.
/// - **`commit_alternative`**: collapse a lex-ambiguous position to a
///   specific alternative, re-lexing downstream positions if the chosen
///   alternative consumes a different number of bytes than the primary.
///
/// All methods return `(token_pos_start, token_pos_end)` indicating which
/// token positions were rewritten — the walker uses this to invalidate
/// any in-flight state that depends on those positions.
pub trait WpdaMutableTokenSource: WpdaTokenSource {
    /// Replace the byte range `[byte_start..byte_end)` with `new_bytes`,
    /// then re-lex from the affected position. Returns the new
    /// `(token_pos_start, token_pos_end)` range that was rewritten.
    fn replace_range(
        &mut self,
        byte_start: usize,
        byte_end: usize,
        new_bytes: &str,
    ) -> Result<(usize, usize), std::string::String>;

    /// Commit a specific lex alternative at position `pos`. Useful for
    /// the walker after a lex-fork commits the winner: the alternate
    /// interpretation becomes the canonical primary, and downstream
    /// positions get re-lexed if the alt's `end_byte` differs from the
    /// previous primary's `end_byte`.
    ///
    /// Returns `(token_pos_start, token_pos_end)` indicating the range
    /// of positions that were rewritten (always at least `(pos, pos+1)`
    /// since the primary at `pos` is replaced; downstream positions may
    /// also be rewritten if the byte-end changed).
    fn commit_alternative(
        &mut self,
        pos: usize,
        alt_idx: u16,
    ) -> Result<(usize, usize), std::string::String>;

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): substitute the token at
    /// `pos` with new (kind, text). Default implementation looks up the
    /// token's byte span via `byte_span_of(pos)` and calls
    /// `replace_range(start, end, &text)`. Sources without byte-range
    /// tracking should override `byte_span_of` to return `None` — that
    /// surfaces as a clear `Err` rather than a silent no-op.
    ///
    /// `kind` is recorded for diagnostics; the actual TokenKind after
    /// re-lexing is determined by the lexer applied to `new_bytes`.
    fn substitute_token(
        &mut self,
        pos: usize,
        kind: TokenKind,
        text: std::string::String,
    ) -> Result<(usize, usize), std::string::String> {
        let _ = kind; // recorded by walker; lexer determines actual kind
        let (start, end) = self
            .byte_span_of(pos)
            .ok_or_else(|| format!("substitute_token: no byte span at pos {}", pos))?;
        self.replace_range(start, end, &text)
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): insert a synthetic token
    /// before `pos`. Default implementation: locates the byte position for
    /// `pos` (start byte) and calls `replace_range(start, start, text + " ")`
    /// so the lexer re-segments with proper word boundary.
    fn insert_token(
        &mut self,
        pos: usize,
        kind: TokenKind,
        text: std::string::String,
    ) -> Result<(usize, usize), std::string::String> {
        let _ = kind;
        let (start, _) = self
            .byte_span_of(pos)
            .ok_or_else(|| format!("insert_token: no byte span at pos {}", pos))?;
        let with_sep = format!("{} ", text);
        self.replace_range(start, start, &with_sep)
    }

    /// Swap two adjacent tokens in the underlying source text and re-lex
    /// the affected range. The default implementation uses token byte
    /// spans, preserves the original separator bytes between the tokens,
    /// and rejects non-adjacent or overlapping positions.
    fn swap_tokens(
        &mut self,
        pos_a: usize,
        pos_b: usize,
    ) -> Result<(usize, usize), std::string::String> {
        let (lo, hi) = if pos_a <= pos_b {
            (pos_a, pos_b)
        } else {
            (pos_b, pos_a)
        };
        if hi != lo + 1 {
            return Err(
                format!("swap_tokens: positions {} and {} are not adjacent", pos_a, pos_b,),
            );
        }
        let (start_a, end_a) = self
            .byte_span_of(lo)
            .ok_or_else(|| format!("swap_tokens: no byte span at pos {}", lo))?;
        let (start_b, end_b) = self
            .byte_span_of(hi)
            .ok_or_else(|| format!("swap_tokens: no byte span at pos {}", hi))?;
        if start_a > end_a || end_a > start_b || start_b > end_b {
            return Err(format!(
                "swap_tokens: positions {} and {} have non-adjacent byte spans [{:?}..{:?}) and [{:?}..{:?})",
                lo, hi, start_a, end_a, start_b, end_b,
            ));
        }
        let text_a = self.source_slice(start_a, end_a).ok_or_else(|| {
            format!("swap_tokens: no source slice for token at byte {}..{}", start_a, end_a,)
        })?;
        let text_b = self.source_slice(start_b, end_b).ok_or_else(|| {
            format!("swap_tokens: no source slice for token at byte {}..{}", start_b, end_b,)
        })?;
        let separator = self.source_slice(end_a, start_b).ok_or_else(|| {
            format!("swap_tokens: no source slice between byte {} and {}", end_a, start_b,)
        })?;
        let replacement = format!("{}{}{}", text_b, separator, text_a);
        self.replace_range(start_a, end_b, &replacement)
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): lookup byte span for the
    /// token at `pos`. Required for the default `substitute_token` /
    /// `insert_token` implementations. Returns `None` for sources that
    /// don't track byte spans (e.g. synthetic kinds-only test inputs);
    /// such sources cannot support byte-level recovery and the caller
    /// surfaces a clean `Err`.
    fn byte_span_of(&self, pos: usize) -> Option<(usize, usize)> {
        let _ = pos;
        None
    }

    /// Borrow a source-text byte slice. Required by the default
    /// `swap_tokens` implementation to preserve the separator between two
    /// adjacent tokens. Sources without source-text tracking can override
    /// `swap_tokens` directly instead.
    fn source_slice(&self, byte_start: usize, byte_end: usize) -> Option<&str> {
        let _ = (byte_start, byte_end);
        None
    }
}

/// L10 (2026-04-28): a `WpdaMutableTokenSource` that wraps a
/// [`MultiTokenSource`] and a re-lex callback.
///
/// The callback `lex_fn` is the per-grammar lexer (typically a generated
/// `lex_stream(input: &str) -> LexStream`). On `replace_range` /
/// `commit_alternative`, the impl mutates `source_text` and calls
/// `lex_fn(&source_text)` to rebuild the stream, then updates the cached
/// primary kinds/texts.
///
/// The current implementation re-lexes the **entire** source on every
/// edit. Downstream optimizations could lex only a subrange and splice
/// the result; the trait surface supports this since it returns the
/// rewritten range.
pub struct MutableMultiTokenSource<L>
where
    L: Fn(&str) -> Result<crate::lexer_types::LexStream, std::string::String>,
{
    inner: MultiTokenSource,
    source_text: std::string::String,
    lex_fn: L,
}

impl<L> MutableMultiTokenSource<L>
where
    L: Fn(&str) -> Result<crate::lexer_types::LexStream, std::string::String>,
{
    /// Construct from an initial source string and a re-lex callback.
    pub fn new(source: std::string::String, lex_fn: L) -> Result<Self, std::string::String> {
        let stream = lex_fn(&source)?;
        let inner = MultiTokenSource::new(stream);
        Ok(Self { inner, source_text: source, lex_fn })
    }

    /// Borrow the underlying source text.
    pub fn source(&self) -> &str {
        &self.source_text
    }
}

impl<L> WpdaTokenSource for MutableMultiTokenSource<L>
where
    L: Fn(&str) -> Result<crate::lexer_types::LexStream, std::string::String>,
{
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        self.inner.peek_kind(pos)
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        self.inner.peek_text(pos)
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn peek_alternatives(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        self.inner.peek_alternatives(pos)
    }

    fn end_byte(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.inner.end_byte(pos, alt_idx)
    }
}

impl<L> WpdaMutableTokenSource for MutableMultiTokenSource<L>
where
    L: Fn(&str) -> Result<crate::lexer_types::LexStream, std::string::String>,
{
    fn replace_range(
        &mut self,
        byte_start: usize,
        byte_end: usize,
        new_bytes: &str,
    ) -> Result<(usize, usize), std::string::String> {
        if byte_start > byte_end || byte_end > self.source_text.len() {
            return Err(format!(
                "replace_range out of bounds: [{}..{}) of source len {}",
                byte_start,
                byte_end,
                self.source_text.len(),
            ));
        }
        // Locate token positions whose byte range overlaps the edit, so
        // the caller knows what was rewritten. Compute BEFORE the edit so
        // the positions reference the OLD stream.
        let prev_token_start = self
            .inner
            .stream
            .entries
            .iter()
            .position(|e| e.byte_start >= byte_start)
            .unwrap_or(self.inner.stream.entries.len());
        let prev_token_end = self
            .inner
            .stream
            .entries
            .iter()
            .position(|e| e.byte_start >= byte_end)
            .unwrap_or(self.inner.stream.entries.len());
        // Mutate source.
        self.source_text
            .replace_range(byte_start..byte_end, new_bytes);
        // Re-lex.
        let new_stream = (self.lex_fn)(&self.source_text)?;
        let new_inner = MultiTokenSource::new(new_stream);
        // Compute new end position by mapping byte_start + new_bytes.len()
        // through the new stream.
        let new_byte_end = byte_start + new_bytes.len();
        let new_token_end = new_inner
            .stream
            .entries
            .iter()
            .position(|e| e.byte_start >= new_byte_end)
            .unwrap_or(new_inner.stream.entries.len());
        self.inner = new_inner;
        Ok((prev_token_start, prev_token_end.max(new_token_end)))
    }

    fn commit_alternative(
        &mut self,
        pos: usize,
        alt_idx: u16,
    ) -> Result<(usize, usize), std::string::String> {
        let entry = self
            .inner
            .stream
            .entries
            .get(pos)
            .ok_or_else(|| format!("commit_alternative: pos {} out of bounds", pos))?;
        let alt = entry
            .alternatives
            .get(alt_idx as usize)
            .ok_or_else(|| {
                format!("commit_alternative: alt_idx {} out of bounds at pos {}", alt_idx, pos,)
            })?
            .clone();
        let prev_end = entry.alternatives[0].end_byte;
        let new_end = alt.end_byte;
        // Replace the primary alternative in place.
        self.inner.stream.entries[pos].alternatives[0] = alt.clone();
        // Refresh the primary caches for `pos`. We rebuild the inner
        // wholesale to keep the primary_kinds/texts in sync — simpler
        // than mutating in place and easier to reason about.
        let stream = std::mem::take(&mut self.inner.stream);
        self.inner = MultiTokenSource::new(stream);
        if new_end != prev_end {
            // Downstream bytes may now lex differently; re-lex from
            // `new_end` to end of source. We model this as a no-op
            // replace_range that triggers a full re-lex of the tail.
            let tail_start = new_end.min(self.source_text.len());
            let original_tail: std::string::String = self.source_text[tail_start..].to_string();
            let (tail_s, tail_e) =
                self.replace_range(tail_start, self.source_text.len(), &original_tail)?;
            // Union with (pos, pos+1) — the primary at `pos` was always
            // rewritten by the alternative swap, even if `replace_range`
            // reports an empty tail range.
            Ok((pos.min(tail_s), (pos + 1).max(tail_e)))
        } else {
            Ok((pos, pos + 1))
        }
    }

    /// Stage 3.20 / L12 (Commit A, 2026-05-06): MutableMultiTokenSource has
    /// real byte-span tracking — entries carry `byte_start` and the entry's
    /// primary alternative carries `end_byte`. Returns the byte range of
    /// the token at `pos`. Used by the default `substitute_token` /
    /// `insert_token` implementations.
    fn byte_span_of(&self, pos: usize) -> Option<(usize, usize)> {
        let entry = self.inner.stream.entries.get(pos)?;
        let primary = entry.alternatives.first()?;
        Some((entry.byte_start, primary.end_byte))
    }

    fn source_slice(&self, byte_start: usize, byte_end: usize) -> Option<&str> {
        self.source_text.get(byte_start..byte_end)
    }
}

/// A slice-backed `WpdaTokenSource` for tests and simple batch consumers.
///
/// Holds a slice of `TokenKind` plus an optional parallel slice of text
/// strings. Production consumers may implement `WpdaTokenSource` directly
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

impl<'a> WpdaTokenSource for SliceTokenSource<'a> {
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

/// A vector-backed mutable token source for generated recovering facades.
///
/// The public WPDA parse wrappers receive already-tokenized `kinds` and
/// `texts`, not the original source bytes or a lexer callback. Recovery replay
/// still needs a mutable source for insert/substitute/swap repairs, so this
/// adapter applies those repairs directly to the token vectors.
pub struct MutableSliceTokenSource {
    kinds: Vec<TokenKind>,
    texts: Vec<String>,
}

impl MutableSliceTokenSource {
    pub fn with_texts(kinds: &[TokenKind], texts: &[&str]) -> Self {
        assert_eq!(kinds.len(), texts.len(), "kinds/texts length mismatch");
        Self {
            kinds: kinds.to_vec(),
            texts: texts.iter().map(|text| (*text).to_string()).collect(),
        }
    }
}

impl WpdaTokenSource for MutableSliceTokenSource {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        self.kinds.get(pos).cloned()
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        self.texts.get(pos).map(String::as_str)
    }

    fn len(&self) -> usize {
        self.kinds.len()
    }
}

impl WpdaMutableTokenSource for MutableSliceTokenSource {
    fn replace_range(
        &mut self,
        byte_start: usize,
        byte_end: usize,
        _new_bytes: &str,
    ) -> Result<(usize, usize), std::string::String> {
        Err(format!(
            "MutableSliceTokenSource is token-addressed, not byte-addressed: \
             replace_range({}..{}) requires MutableMultiTokenSource",
            byte_start, byte_end,
        ))
    }

    fn commit_alternative(
        &mut self,
        pos: usize,
        alt_idx: u16,
    ) -> Result<(usize, usize), std::string::String> {
        if pos >= self.kinds.len() {
            return Err(format!("commit_alternative: pos {} out of bounds", pos));
        }
        if alt_idx != 0 {
            return Err(format!(
                "commit_alternative: MutableSliceTokenSource has no alternate \
                 lex interpretations at pos {}",
                pos,
            ));
        }
        Ok((pos, pos + 1))
    }

    fn substitute_token(
        &mut self,
        pos: usize,
        kind: TokenKind,
        text: std::string::String,
    ) -> Result<(usize, usize), std::string::String> {
        let slot_kind = self
            .kinds
            .get_mut(pos)
            .ok_or_else(|| format!("substitute_token: pos {} out of bounds", pos))?;
        let slot_text = self
            .texts
            .get_mut(pos)
            .ok_or_else(|| format!("substitute_token: pos {} out of bounds", pos))?;
        *slot_kind = kind;
        *slot_text = text;
        Ok((pos, pos + 1))
    }

    fn insert_token(
        &mut self,
        pos: usize,
        kind: TokenKind,
        text: std::string::String,
    ) -> Result<(usize, usize), std::string::String> {
        if pos > self.kinds.len() {
            return Err(format!("insert_token: pos {} out of bounds", pos));
        }
        self.kinds.insert(pos, kind);
        self.texts.insert(pos, text);
        Ok((pos, pos + 1))
    }

    fn swap_tokens(
        &mut self,
        pos_a: usize,
        pos_b: usize,
    ) -> Result<(usize, usize), std::string::String> {
        let (lo, hi) = if pos_a <= pos_b {
            (pos_a, pos_b)
        } else {
            (pos_b, pos_a)
        };
        if hi != lo + 1 {
            return Err(
                format!("swap_tokens: positions {} and {} are not adjacent", pos_a, pos_b,),
            );
        }
        if hi >= self.kinds.len() {
            return Err(format!(
                "swap_tokens: positions {} and {} out of bounds for len {}",
                pos_a,
                pos_b,
                self.kinds.len(),
            ));
        }
        self.kinds.swap(lo, hi);
        self.texts.swap(lo, hi);
        Ok((lo, hi + 1))
    }
}

/// L4 (2026-04-28): a `WpdaTokenSource` backed by a [`LexStream`].
///
/// Each entry carries one or more alternatives; the primary (lowest-weight)
/// alternative is exposed via `peek_kind`/`peek_text`, and the remaining
/// alternatives surface via `peek_alternatives` so the walker can fork at
/// lex-ambiguous positions.
///
/// `MultiTokenSource` caches the primary `kind`/`text` slices to keep
/// `peek_kind`/`peek_text` allocation-free during the parse loop.
pub struct MultiTokenSource {
    pub stream: crate::lexer_types::LexStream,
    primary_kinds: Vec<TokenKind>,
    primary_texts: Vec<String>,
    /// Empty slice cache used when `peek_alternatives` would return more
    /// than the single non-ambiguous primary.
    empty_alts: Vec<crate::lexer_types::LexAlternative>,
}

impl MultiTokenSource {
    /// Construct from a `LexStream`. Caches per-position primary kind/text.
    pub fn new(stream: crate::lexer_types::LexStream) -> Self {
        let primary_kinds = stream
            .entries
            .iter()
            .map(|e| e.primary().kind.clone())
            .collect();
        let primary_texts = stream
            .entries
            .iter()
            .map(|e| e.primary().text.clone())
            .collect();
        Self {
            stream,
            primary_kinds,
            primary_texts,
            empty_alts: Vec::new(),
        }
    }
}

impl WpdaTokenSource for MultiTokenSource {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        self.primary_kinds.get(pos).cloned()
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        self.primary_texts.get(pos).map(|s| s.as_str())
    }

    fn len(&self) -> usize {
        self.stream.entries.len()
    }

    fn peek_alternatives(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        match self.stream.entries.get(pos) {
            Some(e) if e.alternatives.len() > 1 => &e.alternatives[1..],
            _ => &self.empty_alts,
        }
    }

    fn end_byte(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.stream
            .entries
            .get(pos)?
            .alternatives
            .get(alt_idx)
            .map(|a| a.end_byte)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LatticeTokenSource — M3 (2026-05-13): WpdaTokenSource over a LexDag
// ══════════════════════════════════════════════════════════════════════════════

/// A `WpdaTokenSource` backed by a [`crate::lexer_types::LexDag`].
///
/// The cursor's `pos: usize` is interpreted as a **DAG node-id** (not a
/// flat token index). `peek_kind(pos)` returns the kind of the primary
/// (longest-match) outgoing edge of node `pos`; `peek_alternatives(pos)`
/// returns the secondary edges; `next_pos(pos, alt_idx)` returns the
/// `target_node` of the chosen edge.
///
/// **Why this matters**: under the LEGACY linear sources (SliceTokenSource,
/// MultiTokenSource), all alternatives at the same position share the
/// same downstream — the cursor's `pos + 1` after consuming any alt
/// lands at the same token. Under multi-LENGTH ambiguity (e.g., `Minus@end=1`
/// vs `Integer@end=2` at byte 0 of `-3`), different alts have DIFFERENT
/// downstream positions. The DAG encodes this: each cursor's `pos` (a
/// DAG node) naturally identifies its alt-timeline. NO per-cursor sidecar
/// is needed — alt identity lives in the SHARED input structure.
///
/// This replaces the `pending_lex_alts: BTreeMap` sidecar (commits
/// `3290e05` / `ed53ea3`, reverted at M4) per the WPDS-stack-purity
/// principle in `~/.claude/plans/wpds-ambiguity-preserving-redesign.md`.
pub struct LatticeTokenSource {
    /// The underlying DAG.
    pub dag: crate::lexer_types::LexDag,
    /// Cached per-node primary kind (= `edges[0].kind`) for O(1)
    /// `peek_kind`. Indexed by node id.
    primary_kinds: Vec<TokenKind>,
    /// Cached per-node primary text. Indexed by node id. Empty string
    /// for the EOF sentinel (no edges).
    primary_texts: Vec<String>,
    /// Cached per-node secondary `LexAlternative` slice (= `edges[1..]`
    /// converted to `LexAlternative` records). The walker's lex-fork
    /// emitter at PrefixDispatch consults this via `peek_alternatives`.
    secondary_alts: Vec<Vec<crate::lexer_types::LexAlternative>>,
}

impl LatticeTokenSource {
    /// Construct from a [`crate::lexer_types::LexDag`]. Pre-computes the
    /// per-node primary-kind/text caches for O(1) accessors.
    pub fn new(dag: crate::lexer_types::LexDag) -> Self {
        let n = dag.nodes.len();
        let mut primary_kinds = Vec::with_capacity(n);
        let mut primary_texts = Vec::with_capacity(n);
        let mut secondary_alts: Vec<Vec<crate::lexer_types::LexAlternative>> =
            Vec::with_capacity(n);
        for node in &dag.nodes {
            match node.edges.first() {
                Some(primary) => {
                    primary_kinds.push(primary.kind.clone());
                    primary_texts.push(primary.text.clone());
                },
                None => {
                    // EOF sentinel: emit Eof so callers can detect end.
                    primary_kinds.push(TokenKind::Eof);
                    primary_texts.push(String::new());
                },
            }
            // Secondaries: edges[1..] converted to LexAlternative.
            let secs: Vec<crate::lexer_types::LexAlternative> = node
                .edges
                .iter()
                .skip(1)
                .map(|e| crate::lexer_types::LexAlternative {
                    kind: e.kind.clone(),
                    text: e.text.clone(),
                    end_byte: e.end_byte,
                    weight: e.weight,
                })
                .collect();
            secondary_alts.push(secs);
        }
        LatticeTokenSource {
            dag,
            primary_kinds,
            primary_texts,
            secondary_alts,
        }
    }

    /// Returns the target node of edge `alt_idx` (0 = primary; 1+ =
    /// secondaries) from node `pos`. Used by the walker (M5+) to advance
    /// LexAlt Fork children to the alt's target node.
    pub fn target_node(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.dag
            .nodes
            .get(pos)?
            .edges
            .get(alt_idx)
            .map(|e| e.target_node)
    }
}

impl WpdaTokenSource for LatticeTokenSource {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        self.primary_kinds.get(pos).cloned()
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        self.primary_texts.get(pos).map(|s| s.as_str())
    }

    fn len(&self) -> usize {
        self.dag.nodes.len()
    }

    fn peek_alternatives(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        self.secondary_alts
            .get(pos)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    fn is_ambiguous_at(&self, pos: usize) -> bool {
        self.dag
            .nodes
            .get(pos)
            .map(|n| n.edges.len() > 1)
            .unwrap_or(false)
    }

    fn end_byte(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.dag
            .nodes
            .get(pos)?
            .edges
            .get(alt_idx)
            .map(|e| e.end_byte)
    }

    /// M3: return the target NODE INDEX after consuming edge `alt_idx`
    /// from node `pos`. Replaces the default linear `pos + 1` advance —
    /// the LATTICE source's `pos` is a DAG node and the next position
    /// depends on which alt is chosen.
    fn next_pos(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.dag
            .nodes
            .get(pos)?
            .edges
            .get(alt_idx)
            .map(|e| e.target_node)
    }

    fn positions_are_linear_tokens(&self) -> bool {
        false
    }

    /// M6c.8.2 (2026-05-14): the canonical EOF sentinel index from the
    /// DAG. Orphan nodes (allocated by `lex_dag_core`'s soft-fail
    /// mechanism for secondary-alt dead-ends) may sit at indices
    /// AFTER the EOF sentinel, so `nodes.len() - 1` is NOT the EOF
    /// index in general.
    fn eof_node(&self) -> usize {
        self.dag.eof_node
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
/// [`WpdaEngine::action_for`].
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
///
/// Stage 3.6 / ι Phase 1 (2026-05-01): `Term`, `Collection`, and
/// `Predicate` payloads are `Arc<dyn Any + Send + Sync>` (was
/// `Box<dyn Any + Send>`) so `ActionArg` derives `Clone`. This unblocks
/// `BranchCursor::clone` for cursors with populated `collection_stack`
/// accumulators (the pre-3.6 `debug_assert!` panic at line 416 of
/// `wpda_walker.rs` is no longer needed). AST types are `Clone` (manual
/// impls via `iterative_clone.rs`); primitives are `Clone`. Accessors
/// `into_term::<T>` / `into_collection::<T>` / `into_predicate::<T>`
/// gain a `T: Clone` bound so they can deep-clone out of the Arc when
/// the value is shared.
#[derive(Clone)]
pub enum ActionArg {
    /// A raw token kind + its text + position.
    Token {
        kind: TokenKind,
        text: String,
        pos: usize,
    },
    /// An identifier captured from the token stream.
    Ident { name: String, pos: usize },
    /// A fully-constructed sub-term (downcast via `Any`).
    Term {
        value: Arc<dyn Any + Send + Sync>,
        /// Static type-name tag for debug rendering and mismatch detection.
        type_name: &'static str,
    },
    /// A completed binder scope (ready for `Scope::new`).
    BinderScope(BinderHandle),
    /// A completed collection (List, Bag, Map — downcast via `Any`).
    Collection {
        value: Arc<dyn Any + Send + Sync>,
        type_name: &'static str,
    },
    /// Phase 4: identifier of an in-flight collection accumulator. Pushed by
    /// the walker when a `CollectionMarker` symbol is pushed onto the GSS;
    /// consumed by the collection-finalize action via `as_collection_id`.
    CollectionId(u8),
    /// Phase 6: a parsed behavioral predicate. Pushed by the walker after
    /// invoking `parse_predicate_from_tokens`; consumed by the rule's action
    /// to wire the predicate into the constructed AST.
    Predicate(Arc<dyn Any + Send + Sync>),
    /// Opt-Group (2026-04-29): a captured optional-group result.
    ///
    /// `Some(inner_args)` when the syntax-pattern Opt block matched
    /// at parse time: `inner_args` is the sequence of `ActionArg`s
    /// captured inside the group, in the order their corresponding
    /// inner `BinderPosition` produced them. Each inner Simple param's
    /// `ActionArg::Term` lives in `inner_args[i]` for the i-th non-
    /// literal inner param.
    ///
    /// `None` when the Opt block was not taken (parser advanced past
    /// the group without consuming).
    ///
    /// The rule's action body extracts `Optional(Option<Vec<ActionArg>>)`
    /// and produces `Some(...)` / `None` for each inner-bound `Option<T>`
    /// field of the AST variant. Nested Optional flattens — the engine
    /// never produces `Some(Some(...))`; nested groups contribute their
    /// inner args directly to the outer group's inner_args list.
    Optional(Option<Vec<ActionArg>>),
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
            ActionArg::Optional(Some(args)) => f
                .debug_struct("Optional")
                .field("present", &true)
                .field("len", &args.len())
                .finish(),
            ActionArg::Optional(None) => {
                f.debug_struct("Optional").field("present", &false).finish()
            },
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
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): `T: Clone` bound added. The
    /// payload is `Arc<dyn Any + Send + Sync>`; `Arc::try_unwrap` moves
    /// out when the Arc is uniquely owned (zero-copy fast path); falls
    /// back to `(*arc).clone()` when the Arc has been cloned for fanout.
    pub fn into_term<T: 'static + Send + Sync + Clone>(self) -> Option<T> {
        match self {
            ActionArg::Term { value, .. } => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            _ => None,
        }
    }
    /// Extract the SHARED `Arc<T>` from a `Term` arg WITHOUT cloning the
    /// pointee (O(1) `Arc::downcast` — just a refcount bump on success).
    ///
    /// ARC refactor (2026-05-28): the generated semantic actions store
    /// recursive AST children as `Arc<Cat>` fields (was `Box<Cat>`). They
    /// pop child operands via this method and place the shared `Arc`
    /// directly into the constructed node, so building `Add(left, right)`
    /// is O(1) — it shares `left`'s subtree instead of deep-cloning it.
    /// This collapses the former O(N²) chain construction (every chain step
    /// deep-cloned the whole accumulated left operand via `into_term`;
    /// heaptrack attributed 96% of chain_1000 peak heap to that clone) to
    /// O(N) structural sharing. Unlike `into_term`, NO `T: Clone` bound is
    /// required — the value is never cloned, only shared.
    pub fn into_term_arc<T: 'static + Send + Sync>(self) -> Option<Arc<T>> {
        match self {
            ActionArg::Term { value, .. } => Arc::downcast::<T>(value).ok(),
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
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): see `into_term` for Arc/Clone
    /// rationale.
    pub fn into_collection<T: 'static + Send + Sync + Clone>(self) -> Option<T> {
        match self {
            ActionArg::Collection { value, .. } => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
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
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): see `into_term` for Arc/Clone
    /// rationale.
    pub fn into_predicate<T: 'static + Send + Sync + Clone>(self) -> Option<T> {
        match self {
            ActionArg::Predicate(value) => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            _ => None,
        }
    }
    /// Opt-Group: consume this `Optional` arg, returning the inner
    /// `Option<Vec<ActionArg>>` for the action body to destructure.
    /// Returns `None` if the arg is not an `Optional` variant
    /// (mismatched action arity / kind would be a codegen bug).
    pub fn into_optional(self) -> Option<Option<Vec<ActionArg>>> {
        match self {
            ActionArg::Optional(value) => Some(value),
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
///
/// B13c / Candidate H (2026-05-08): extended with per-arg expected-input
/// category indices and the action's output category. Used by
/// `cursor_will_produce_term` (in `wpda_walker.rs`) to dry-run the
/// FireAction sequence on a cursor's `recovery_deltas` and decide
/// whether the cursor would produce a valid Term term at EOI commit.
/// Cursors whose dry-run lands on empty/underflow/type-mismatched
/// state are filtered from the accepting set BEFORE lex-min runs,
/// preventing the post-B7 failure mode where atomic-home cursors at
/// the wrong category reach `Accepted` with empty / half-consumed
/// builder state.
///
/// `expected_input_cats`: per-arg category index (matching
/// `category_src_idx` used elsewhere). Length equals `arity`. Sentinel
/// `u16::MAX` means "any category" (e.g., for token / ident slots
/// where the action accepts any token regardless of category).
///
/// `output_cat`: the category the action's `push_term` lands in.
/// Used as the type-tag for the cursor's projected arg-stack after
/// the FireAction.
#[derive(Clone, Copy)]
pub struct ActionEntry {
    pub action_fn: SemanticActionFn,
    pub arity: u8,
    pub expected_input_cats: &'static [u16],
    pub output_cat: u16,
}

/// B13c / Candidate H: sentinel category index meaning "any category
/// accepted" — used for non-Term arg slots (Ident, Token, Predicate,
/// CollectionId, BinderScope) where category matching doesn't apply.
pub const ANY_CAT: u16 = u16::MAX;

impl fmt::Debug for ActionEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActionEntry")
            .field("action_fn", &"fn(...)")
            .field("arity", &self.arity)
            .field("expected_input_cats", &self.expected_input_cats)
            .field("output_cat", &self.output_cat)
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
///
/// Phase 5.3 (2026-05-12): `Clone` enables `Arc::make_mut(&mut
/// cursor.builder)` clone-on-write semantics — all four fields are
/// `im::Vector`s (HAMT-backed; Clone is O(1) Arc-bump on the root).
/// BinderHandle and ActionArg both derive Clone. Cloning is cheap and only
/// occurs when a child cursor first mutates its parent-shared builder.
#[derive(Clone)]
pub struct SemanticBuilder {
    /// Phase 5.1 (2026-05-12): migrated from `Vec<ActionArg>` to
    /// `im::Vector<ActionArg>` (HAMT-backed persistent vector). O(log N)
    /// clone via Arc-shared internal nodes prepares this field for
    /// Phase 5.2's `Arc<SemanticBuilder>` cursor-shared builder. ActionArg
    /// derives Clone (Stage 3.6 / ι Phase 1) so this migration is
    /// type-safe. Method signatures returning `Vec<ActionArg>` are
    /// preserved; internal conversion bridges the API.
    stack: im::Vector<ActionArg>,
    binder_scopes: im::Vector<BinderHandle>,
    /// Phase 4: in-flight collection accumulators, indexed by id. Each
    /// entry collects `ActionArg::Term` values pushed during element
    /// parsing; the collection-finalize action drains the entry and
    /// constructs the final container (HashBag / Vec / etc.).
    ///
    /// Phase 5.1 (2026-05-12): both outer and inner containers migrated
    /// to `im::Vector` for Phase 5.2's structural sharing across cursor
    /// clones during Fork fanout. The inner per-slot accumulator is also
    /// `im::Vector<ActionArg>` so a cursor-clone shares the slot's
    /// internal HAMT nodes until a write triggers copy-on-write.
    collection_stack: im::Vector<im::Vector<ActionArg>>,
    /// Opt-Group (2026-04-29): in-flight inner-arg accumulators for
    /// taken optional groups. When `start_optional_scope()` is called
    /// (auto-triggered when the walker pushes an
    /// `OptionalGroupAt(1)` marker), a fresh inner buffer is pushed
    /// onto this stack. While the stack top is non-empty, every
    /// subsequent `push_xxx` call routes through `push_arg_internal`
    /// to the top inner buffer instead of `stack`. On
    /// `finalize_optional_scope_present()`, the inner buffer is popped
    /// and wrapped as `ActionArg::Optional(Some(inner))` — pushed
    /// either to `stack` (if no outer optional scope is active) or to
    /// the next-outer scope's buffer (nested-Optional flattening).
    ///
    /// On the skip path, no scope is opened; `push_optional_absent()`
    /// pushes `ActionArg::Optional(None)` directly via the same routing.
    ///
    /// Phase 5.1 (2026-05-12): migrated to `im::Vector`-of-`im::Vector`
    /// (see `collection_stack` rationale). Each push/pop scope creation
    /// is O(log N).
    optional_stack: im::Vector<im::Vector<ActionArg>>,
}

impl SemanticBuilder {
    pub fn new() -> Self {
        SemanticBuilder {
            stack: im::Vector::new(),
            binder_scopes: im::Vector::new(),
            collection_stack: im::Vector::new(),
            optional_stack: im::Vector::new(),
        }
    }

    /// Opt-Group: route an `ActionArg` push to the top of `optional_stack`
    /// if a scope is open, otherwise to the main `stack`. Nested Optional
    /// chains correctly because the innermost scope is the routing target.
    ///
    /// Phase 5.1 (2026-05-12): uses `push_back` (im::Vector's append-end).
    #[inline]
    fn push_arg_internal(&mut self, arg: ActionArg) {
        self.active_arg_stack_mut().push_back(arg);
    }

    /// Opt-Group: routing-aware mutable accessor for the active argument
    /// cursor. Returns the innermost open optional scope when one is open,
    /// else the main `stack`. All arg-stack reads/writes during a parse
    /// MUST funnel through this so push/pop stay symmetric — the original
    /// bug (TAKE-path EmptyResult) was that pushes routed into the optional
    /// scope but pops drained `self.stack` directly, so a literal captured
    /// inside `*opt(...)` was popped from the wrong cursor when its
    /// `LiteralPatterned` action fired.
    ///
    /// Phase 5.1 (2026-05-12): return type migrated from `&mut Vec` to
    /// `&mut im::Vector` (HAMT-backed). API parity: `push_back` /
    /// `pop_back` / `back` / `back_mut` mirror `Vec::push` / `pop` /
    /// `last` / `last_mut`.
    #[inline]
    fn active_arg_stack_mut(&mut self) -> &mut im::Vector<ActionArg> {
        if let Some(top) = self.optional_stack.back_mut() {
            top
        } else {
            &mut self.stack
        }
    }

    /// Read-only counterpart to `active_arg_stack_mut`.
    ///
    /// Phase 5.1 (2026-05-12): return type migrated to `&im::Vector`.
    #[inline]
    fn active_arg_stack(&self) -> &im::Vector<ActionArg> {
        if let Some(top) = self.optional_stack.back() {
            top
        } else {
            &self.stack
        }
    }

    /// Opt-Group: open a new optional-scope inner-arg accumulator. Called
    /// by the walker when pushing `OptionalGroupAt(1)` (the take-path
    /// entry into an optional group).
    ///
    /// Phase 5.1 (2026-05-12): pushes an empty `im::Vector` (O(1)) onto
    /// the outer `im::Vector` (O(log N) push_back).
    pub fn start_optional_scope(&mut self) {
        self.optional_stack.push_back(im::Vector::new());
    }

    /// Stage 3.9 / ι Phase 4 (2026-05-01): introspection accessor for
    /// regression tests verifying optional-scope opener fires correctly
    /// on `OptionalGroupAt(1)` push (`emit_push_side_effects` clause).
    pub fn optional_stack_depth(&self) -> usize {
        self.optional_stack.len()
    }

    /// Opt-Group: close the innermost optional scope, wrapping its
    /// inner-arg buffer as `ActionArg::Optional(Some(inner))` and pushing
    /// to the surrounding scope (next-outer optional scope OR main stack).
    ///
    /// Phase 5.1 (2026-05-12): `pop_back` returns `Option<im::Vector<...>>`;
    /// convert to `Vec<ActionArg>` via `into_iter().collect()` to satisfy
    /// `ActionArg::Optional`'s `Option<Vec<ActionArg>>` payload type. The
    /// conversion is O(N) (walks the HAMT once) — typical inner-arg
    /// buffers hold 1–8 elements, so cost is negligible.
    pub fn finalize_optional_scope_present(&mut self) {
        let inner = self.optional_stack.pop_back().unwrap_or_default();
        let arg = ActionArg::Optional(Some(inner.into_iter().collect()));
        self.push_arg_internal(arg);
    }

    /// Opt-Group: skip path — the FIRST set didn't match, no scope was
    /// opened. Push `ActionArg::Optional(None)` directly via the same
    /// routing (so a skipped-Optional inside a taken-Optional correctly
    /// lands in the outer's inner-arg buffer).
    pub fn push_optional_absent(&mut self) {
        self.push_arg_internal(ActionArg::Optional(None));
    }

    /// Current stack depth (of the active argument cursor — the innermost
    /// open optional scope, or the main stack if no scope is open).
    pub fn len(&self) -> usize {
        self.active_arg_stack().len()
    }

    /// Whether the active argument cursor is empty.
    pub fn is_empty(&self) -> bool {
        self.active_arg_stack().is_empty()
    }

    /// Phase 5.6-tail-A (2026-05-12): EOI-gate accessor. Returns `true`
    /// iff the builder is in a terminal accepting shape: either (a) no
    /// open optional scopes AND the main stack is empty (vacuously
    /// viable — e.g. synthetic-engine recovery cursors that journal
    /// effects but never push args), or (b) exactly one
    /// `ActionArg::Term` on the main stack with no open optional scopes
    /// (the normal Accepted shape).
    ///
    /// Used by `WpdaWalker::is_accepting_config` to filter cursors whose
    /// live state would not yield a single Term at `take_dyn_result`.
    /// Replaces the pre-5.6-tail `cursor_will_produce_term` dry-run that
    /// simulated the same property against `recovery_deltas`; under
    /// always-eager (Phase 5.3+), the live builder IS the authoritative
    /// state. The empty-stack arm mirrors the pre-tail "empty pending =
    /// deterministic-singleton short-circuit" branch — a cursor with no
    /// recorded activity has no falsifying evidence and is conservatively
    /// viable.
    pub fn is_accepting_terminal(&self) -> bool {
        if !self.optional_stack.is_empty() {
            return false;
        }
        if self.stack.is_empty() {
            return true;
        }
        if self.stack.len() != 1 {
            return false;
        }
        matches!(self.stack.back(), Some(ActionArg::Term { .. }))
    }

    /// D8 fix (2026-05-13): return the `type_name` string of the topmost
    /// `ActionArg::Term` on the main stack, if any.
    ///
    /// Used by the WPDS walker's `GroupingClosePreservingInner`
    /// resolution to identify the actual inner-expression RESULT
    /// category, which may differ from the popped CategoryEntry's
    /// OPERAND category in cross-cat infix patterns (e.g.,
    /// `LtFloat: Float "<" Float : Bool` — operand cat is `Float`
    /// but result cat is `Bool`).
    ///
    /// Reads from `self.stack` (the main arg stack), NOT
    /// `active_arg_stack` routing — at `GroupingClosePreservingInner`
    /// resolution time the inner expression's action has already
    /// fired and pushed its result onto the main stack (no open
    /// optional scopes can be active at `)`-close time).
    pub fn top_term_type_name(&self) -> Option<&'static str> {
        match self.stack.back() {
            Some(ActionArg::Term { type_name, .. }) => Some(*type_name),
            _ => None,
        }
    }

    /// Push a raw token onto the stack.
    pub fn push_token(&mut self, kind: TokenKind, text: String, pos: usize) {
        self.push_arg_internal(ActionArg::Token { kind, text, pos });
    }

    /// Push an identifier (Ident-token's text canonicalised).
    pub fn push_ident(&mut self, name: String, pos: usize) {
        self.push_arg_internal(ActionArg::Ident { name, pos });
    }

    /// Push a constructed sub-term.
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): `T: Sync` bound added (was `Send`
    /// only). The payload is `Arc<dyn Any + Send + Sync>`; `Sync` is
    /// required for the trait object. AST types satisfy `Send + Sync`
    /// (verified — no interior mutability in any AST variant).
    pub fn push_term<T: 'static + Send + Sync>(&mut self, value: T) {
        self.push_arg_internal(ActionArg::Term {
            value: Arc::new(value),
            type_name: std::any::type_name::<T>(),
        });
    }

    /// Option C / C7 (2026-05-15): push an already-`Arc`'d Term arg.
    /// Used by `WpdaWalker::realize_root_to_terms` to thread realized
    /// child terms into a fresh `SemanticBuilder` before calling
    /// `action_fn`. The `type_name` is preserved as a debug tag only
    /// (downcasting at the facade keys on the concrete `Cat` type).
    pub fn push_term_arc(&mut self, value: Arc<dyn Any + Send + Sync>) {
        self.push_arg_internal(ActionArg::Term { value, type_name: "RealizedTerm" });
    }

    /// Option C / C7: push a raw `ActionArg` directly. Used during
    /// realization to forward already-constructed args (e.g.
    /// `Optional`, `BinderScope`) without re-wrapping.
    pub fn push_raw_arg(&mut self, arg: ActionArg) {
        self.push_arg_internal(arg);
    }

    /// Push a completed collection (already of the language's native
    /// collection type, e.g., `HashBag<Proc>` or `Vec<Int>`).
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): `T: Sync` bound added.
    pub fn push_collection<T: 'static + Send + Sync>(&mut self, value: T) {
        self.push_arg_internal(ActionArg::Collection {
            value: Arc::new(value),
            type_name: std::any::type_name::<T>(),
        });
    }

    /// Push a completed binder scope.
    pub fn push_binder_scope(&mut self, handle: BinderHandle) {
        self.push_arg_internal(ActionArg::BinderScope(handle));
    }

    /// Phase 4: push a CollectionId arg onto the stack. Used by the walker
    /// when a `CollectionMarker` symbol is pushed onto the GSS so the
    /// finalize action can identify which accumulator to drain.
    pub fn push_collection_id(&mut self, id: u8) {
        self.push_arg_internal(ActionArg::CollectionId(id));
    }

    /// Phase 6: push a parsed behavioral predicate onto the stack.
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): `T: Sync` bound added.
    pub fn push_predicate<T: 'static + Send + Sync>(&mut self, pred: T) {
        self.push_arg_internal(ActionArg::Predicate(Arc::new(pred)));
    }

    /// Stage 3.6 / ι Phase 1 (2026-05-01) simplification: now that
    /// `ActionArg::Predicate` is `Arc<dyn Any + Send + Sync>` natively,
    /// the Arc-erased replay path stores the Arc directly without
    /// downcast/clone/re-box. The pre-3.6 cascade (downcast to
    /// BehavioralPred → clone → Box) is no longer needed.
    pub fn push_predicate_arc(&mut self, pred: Arc<dyn Any + Send + Sync>) {
        self.push_arg_internal(ActionArg::Predicate(pred));
    }

    /// Pop the top N args (returned in push order: result[0] was
    /// pushed first). Panics if fewer than N args are available — a
    /// programming error in the engine's arity table.
    ///
    /// Drains from the **active argument cursor** so a sub-rule's action
    /// firing inside an open optional scope pops the inner-scope args its
    /// pushes targeted, not the outer main stack.
    ///
    /// Phase 5.1 (2026-05-12): the active stack is now `im::Vector`. We
    /// `split_off` at the underflow-checked index — returning the tail as
    /// a new `im::Vector` (O(log N)) — then convert to `Vec<ActionArg>`
    /// via `into_iter().collect()`. The signature still returns
    /// `Vec<ActionArg>` for codegen action_fn compatibility (downstream
    /// actions iterate / pattern-match args in array form). Typical N
    /// for a single action is 1–6, so the conversion is cheap.
    pub fn pop_args(&mut self, n: usize) -> Vec<ActionArg> {
        let active = self.active_arg_stack_mut();
        let start = active
            .len()
            .checked_sub(n)
            .expect("SemanticBuilder::pop_args: stack underflow (engine arity bug)");
        let tail = active.split_off(start);
        tail.into_iter().collect()
    }

    /// Begin a binder scope — used by binder rules before parsing the body.
    ///
    /// Phase 5.1 (2026-05-12): `push_back` against `im::Vector<BinderHandle>`.
    pub fn start_binder_scope(&mut self, names: Vec<String>) {
        let depth = self.binder_scopes.len() as u16;
        self.binder_scopes
            .push_back(BinderHandle::new(names, depth));
    }

    /// B8 / Issue C followup (2026-05-09): append a binder name to the
    /// innermost open binder scope. Used by multi-binder loops where the
    /// scope opens once at bootstrap with an empty names list, and each
    /// iteration's BinderIdent capture extends the names list with the
    /// captured ident. Without this, subsequent idents (start_scope=false)
    /// only got pushed to the args stack as `ActionArg::Ident`, never
    /// reaching the BinderHandle.names that the action's BinderScope
    /// arg extraction reads.
    ///
    /// Phase 5.1 (2026-05-12): `back_mut` returns `Option<&mut BinderHandle>`
    /// — same shape as the old `last_mut`. The inner `handle.names: Vec<String>`
    /// is unchanged (BinderHandle is unmigrated in 5.1).
    pub fn extend_binder_scope(&mut self, name: String) {
        if let Some(handle) = self.binder_scopes.back_mut() {
            handle.names.push(name);
        }
    }

    /// End the innermost binder scope and leave a `BinderScope` arg on the
    /// active argument cursor (so a binder fired inside `*opt(...)` lands
    /// in the inner scope just like other captures).
    ///
    /// Phase 5.1 (2026-05-12): `pop_back` against `im::Vector<BinderHandle>`.
    pub fn end_binder_scope(&mut self) {
        if let Some(handle) = self.binder_scopes.pop_back() {
            self.push_arg_internal(ActionArg::BinderScope(handle));
        }
    }

    /// Phase 5: end the innermost binder scope WITHOUT pushing a
    /// `BinderScope` arg back onto the stack. Used by binder-rule actions
    /// where the action body already has the binder name as a captured
    /// `Ident` arg and doesn't need a `BinderScope` slot.
    ///
    /// Phase 5.1 (2026-05-12): `pop_back` against `im::Vector<BinderHandle>`.
    pub fn pop_binder_scope_silent(&mut self) {
        self.binder_scopes.pop_back();
    }

    /// View the innermost binder scope without popping it (for binder-aware
    /// inner parses that need to know which names are in scope).
    ///
    /// Phase 5.1 (2026-05-12): `back` returns `Option<&BinderHandle>` —
    /// same shape as the old `last`.
    pub fn current_binder_scope(&self) -> Option<&BinderHandle> {
        self.binder_scopes.back()
    }

    /// At parse completion, extract the single remaining term as the
    /// parse result. Returns `None` if the stack is empty, has more than
    /// one entry, or the top entry is not a term of type `T`.
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): `T: Clone` bound added (Arc
    /// move-or-clone fast path).
    pub fn take_result<T: 'static + Send + Sync + Clone>(&mut self) -> Option<T> {
        debug_assert!(
            self.optional_stack.is_empty(),
            "take_result: optional_stack is non-empty at Accepted state — \
             a Push(OptionalGroupAt) was not paired with OptGroupFinalize \
             or OptGroupAbsent. Engine bug.",
        );
        if self.stack.len() != 1 {
            return None;
        }
        match self.stack.pop_back()? {
            ActionArg::Term { value, .. } => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            _ => None,
        }
    }

    /// Stage 3.5b (2026-05-01): type-erased variant of `take_result` used by
    /// `WpdaWalker::resolve_at_end_of_input`. The walker is generic over
    /// the semiring W but does not know the parsed term type T at the
    /// resolution surface — `WpdaResolveResult` carries the term as
    /// `Arc<dyn Any + Send + Sync>` (post-Stage-3.6) and downstream callers
    /// downcast.
    pub fn take_dyn_result(&mut self) -> Option<Arc<dyn std::any::Any + Send + Sync>> {
        debug_assert!(
            self.optional_stack.is_empty(),
            "take_dyn_result: optional_stack is non-empty — engine bug",
        );
        if self.stack.len() != 1 {
            return None;
        }
        match self.stack.pop_back()? {
            ActionArg::Term { value, .. } => Some(value),
            _ => None,
        }
    }

    // ─── Phase 4: collection-literal accumulator helpers ──────────────────

    /// Start a fresh collection accumulator. Returns the id (8-bit) to
    /// embed in the `CollectionMarker` symbol's `bp` field.
    ///
    /// Phase 5.1 (2026-05-12): pushes an empty inner `im::Vector` onto
    /// the outer `im::Vector<im::Vector<ActionArg>>` (both O(log N)).
    pub fn start_collection(&mut self) -> u8 {
        let id = self.collection_stack.len() as u8;
        self.collection_stack.push_back(im::Vector::new());
        id
    }

    /// Pop the top of the active argument cursor (must be a `Term`) and
    /// append it into the collection identified by `id`. Called by the
    /// walker when transitioning to `CollectionLoop` after a per-element
    /// parse. Scope-aware so that a `[a, b, c]` collection literal nested
    /// inside `*opt(...)` correctly drains the inner-scope cursor.
    ///
    /// Phase 5.1 (2026-05-12): `pop_back` from active stack, `push_back`
    /// onto inner `im::Vector` at the slot.
    pub fn push_to_collection(&mut self, id: u8) {
        if let Some(arg) = self.active_arg_stack_mut().pop_back() {
            if let Some(acc) = self.collection_stack.get_mut(id as usize) {
                acc.push_back(arg);
            }
        }
    }

    /// Drain the collection identified by `id`, returning its elements
    /// in push order. Called by the collection-finalize action.
    ///
    /// **Lifecycle (Stage 3.5 / γ.1, 2026-04-30):** the slot at `id` is
    /// REMOVED from `collection_stack` — mirroring
    /// `finalize_optional_scope_present`'s `optional_stack.pop()` pattern.
    /// Without the pop, slot accumulation grows unboundedly across nested
    /// collection finalizes and breaks the `adopt_collection_stack`
    /// invariant at fanout boundaries (see Class C panic at
    /// `wpda_runtime.rs::adopt_collection_stack`). LIFO invariant: every
    /// `drain_collection(id)` call should match the top of the stack
    /// because grammars can only close collections in the reverse order
    /// they opened (the close-delim of an inner collection always
    /// precedes the close-delim of an outer collection that contains it).
    ///
    /// Phase 5.1 (2026-05-12): `pop_back` returns the inner `im::Vector`
    /// in O(log N); the result is converted to `Vec<ActionArg>` via
    /// `into_iter().collect()` to preserve the public signature. The
    /// release-build fallback path uses `std::mem::replace` to swap an
    /// empty `im::Vector` into the slot (mirroring legacy `mem::take`
    /// semantics on `Vec`); the drained inner Vector is then converted
    /// in-place. Collection elements are typically small (1–50 items),
    /// so the `into_iter().collect()` walk is cheap.
    pub fn drain_collection(&mut self, id: u8) -> Vec<ActionArg> {
        let id_usize = id as usize;
        debug_assert!(
            id_usize < self.collection_stack.len(),
            "drain_collection: id {} out of range (collection_stack.len() = {})",
            id,
            self.collection_stack.len(),
        );
        debug_assert_eq!(
            id_usize + 1,
            self.collection_stack.len(),
            "drain_collection: LIFO violation — id {} is not the top of \
             collection_stack (len = {}). Collections must finalize in \
             reverse open order.",
            id,
            self.collection_stack.len(),
        );
        if id_usize + 1 == self.collection_stack.len() {
            self.collection_stack
                .pop_back()
                .map(|v| v.into_iter().collect())
                .unwrap_or_default()
        } else if let Some(acc) = self.collection_stack.get_mut(id_usize) {
            // Defensive fallback in release builds when LIFO is violated:
            // drain the slot in place (legacy mem::take behavior). Slot
            // remains, leaving an empty husk — but better than panicking
            // on a non-LIFO grammar (none ship today; future grammars
            // would surface via the debug_assert above).
            std::mem::replace(acc, im::Vector::new())
                .into_iter()
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Option A (2026-04-28): donate cursor-local collection accumulators
    /// to the live builder en bloc. Called by `commit_winner` before delta
    /// replay so that `MaybeSpliceCollection` deltas (which call
    /// `push_to_collection(id)`) and `FireAction` deltas (whose action
    /// calls `drain_collection(id)`) find populated slots.
    ///
    /// Invariant: live builder's `collection_stack` MUST be empty at call
    /// time — Fork is only emitted at PrefixDispatch boundaries where no
    /// in-flight collection state exists on the live builder. The cursor's
    /// `collection_stack` carries all accumulators allocated during fanout;
    /// after donate, the cursor's mirror is empty (moved here).
    ///
    /// Phase 5.1 (2026-05-12): the public signature still accepts
    /// `Vec<Vec<ActionArg>>` (so walker call sites stay unchanged); we
    /// convert the outer Vec into `im::Vector` via `into_iter().map().collect()`,
    /// promoting each inner `Vec` to an `im::Vector`. Cost is O(N + Σ inner-len)
    /// — at fanout boundaries N is typically 0–3.
    pub fn adopt_collection_stack(&mut self, accs: Vec<Vec<ActionArg>>) {
        debug_assert!(
            self.collection_stack.is_empty(),
            "adopt_collection_stack: live builder collection_stack must be \
             empty at fanout boundary; got {} in-flight accumulators",
            self.collection_stack.len(),
        );
        self.collection_stack = accs
            .into_iter()
            .map(|inner| inner.into_iter().collect::<im::Vector<_>>())
            .collect();
    }

    /// Stage 3.12.8 (2026-05-03): collection_stack length accessor for
    /// the `BuilderDelta::FinalizeCollection` replay invariant check.
    pub fn collection_stack_len(&self) -> usize {
        self.collection_stack.len()
    }

    /// Phase 4 #5b (2026-05-12): per-slot length accessor used by the
    /// walker's `set_cursor_inner_state` to compute `kv_phase` parity
    /// for HashMap collection slots. Returns 0 if the `acc_id` is out of
    /// range (defensive — should not happen under correct push/pop
    /// pairing).
    pub fn collection_slot_len(&self, acc_id: usize) -> usize {
        self.collection_stack
            .get(acc_id)
            .map(|s| s.len())
            .unwrap_or(0)
    }

    /// Stage 3.16 collection-slot transfer helper (Mechanism γ closure,
    /// 2026-05-05) —
    /// remove the live builder's collection_stack and return ownership.
    /// Pre-tail this was used at the deterministic→nondeterministic
    /// promotion in `apply_action::Fork` to transfer slots allocated
    /// during the deterministic-singleton phase into the parent cursor's
    /// `collection_stack` so children inherited aligned slot ownership.
    /// Phase 5.6-tail-C deleted the Fork prologue that called this; the
    /// method is preserved for the recovery-replay path and any future
    /// snapshot/restore caller. After this call the live builder's
    /// collection_stack is empty.
    ///
    /// Phase 5.1 (2026-05-12): swap out the inner `im::Vector<im::Vector<...>>`
    /// via `std::mem::take` (yields the populated im::Vector and leaves
    /// an empty one in place — analogous to old Vec behavior). Convert the
    /// outer to Vec; each inner `im::Vector<ActionArg>` becomes `Vec<ActionArg>`.
    /// Public signature still returns `Vec<Vec<ActionArg>>` for walker
    /// call sites.
    pub fn take_collection_stack(&mut self) -> Vec<Vec<ActionArg>> {
        let taken = std::mem::take(&mut self.collection_stack);
        taken
            .into_iter()
            .map(|inner| inner.into_iter().collect::<Vec<_>>())
            .collect()
    }

    /// Stage 3.12.8 (2026-05-03): re-push a previously-drained
    /// collection slot. Used by `BuilderDelta::FinalizeCollection`
    /// replay to restore the LIFO top so the subsequent
    /// `FireAction → drain_collection(id)` succeeds.
    ///
    /// The slot's elements are the `drained` Vec from the delta —
    /// captured at the cursor-side pop time when grammar logically
    /// closed the collection. After replay's re-push, the live
    /// builder's stack length matches the cursor's logical snapshot.
    ///
    /// Phase 5.1 (2026-05-12): the public signature still accepts
    /// `Vec<ActionArg>` (so delta-replay call sites stay unchanged); we
    /// convert into `im::Vector` via `into_iter().collect()` before
    /// `push_back` onto the outer `im::Vector<im::Vector<ActionArg>>`.
    pub fn push_collection_slot(&mut self, drained: Vec<ActionArg>) {
        self.collection_stack
            .push_back(drained.into_iter().collect());
    }
}

impl Default for SemanticBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// C11.3 (2026-05-16): the M7b `DerivationSnapshot` newtype (an
// Arc<SemanticBuilder> wrapper that fed the M11 multiset semiring) was
// deleted alongside the C10 W revert. With W = LexicographicWeight,
// builder snapshots are no longer carried in weight entries; the SPPF
// arena's Symbol-dedup at `(nt, lo, hi)` is the structural ambiguity
// substrate.

// ══════════════════════════════════════════════════════════════════════════════
// M11.3 (2026-05-14): codegen weight-construction helpers
// ══════════════════════════════════════════════════════════════════════════════
//
// The codegen lifts walker `W` from `LexicographicWeight` to
// `DerivationWeight<LexicographicWeight, DerivationSnapshot>` (M11.4). Every
// `LexicographicWeight::from_cost(...)` emit site in the codegen wraps the
// resulting weight in a singleton `DerivationWeight` carrying the unit
// derivation snapshot (the walker's Fork-arm sites inject the parent's
// real snapshot via `with_snapshot` at apply time — see M11.5).
//
// These helpers live in `wpda_runtime` (not `automata::derivation_weight`)
// because they specialize on `DerivationSnapshot` — keeping the algebra
// crate (`automata::derivation_weight`) `DerivationSnapshot`-agnostic.

/// Construct a `DerivationWeight` carrying a single `LexicographicWeight`
/// with `lex_alt_idx = 0` (the default — no lex ambiguity at this site).
///
/// The derivation component is `DerivationSnapshot::unit()` — codegen has
/// no cursor scope. Walker Fork-arm sites inject the parent's real
/// snapshot via `with_snapshot` before merging into the child cursor's
/// accumulated weight.
#[inline]
pub fn lex_w(
    cost: f64,
    src_idx: u16,
    rule_idx: u16,
) -> crate::automata::lex_weight::LexicographicWeight {
    // Phase 3.1.7 (C10, 2026-05-15): per Option C plan §8 C10 the walker
    // `W` reverts from `DerivationWeight<LexicographicWeight,
    // DerivationSnapshot>` (M11 multiset semiring) to plain
    // `LexicographicWeight`. The SPPF arena carries derivation ambiguity
    // (Tomita 1986 §6.3 / Scott-Johnstone 2010 §3 — packed parse forest
    // is a *set* of derivations with structural dedup); `W` carries only
    // path-cost tiebreak. Eliminates M11's O(merges²) multiset blow-up.
    crate::automata::lex_weight::LexicographicWeight::from_cost(cost, src_idx, rule_idx)
}

/// Construct a `LexicographicWeight` with explicit `lex_alt_idx`. Used
/// by lex-Fork emission paths where a lex DAG position has multiple
/// `TokenKind` alternatives.
#[inline]
pub fn lex_w_alt(
    cost: f64,
    src_idx: u16,
    rule_idx: u16,
    lex_alt_idx: u16,
) -> crate::automata::lex_weight::LexicographicWeight {
    crate::automata::lex_weight::LexicographicWeight::from_cost_with_lex(
        cost,
        src_idx,
        rule_idx,
        lex_alt_idx,
    )
}

/// Construct the multiplicative identity `LexicographicWeight::one()`.
///
/// Imported via `use mettail_prattail::wpda_runtime::lex_one;` in the
/// emitted step() body.
#[inline]
pub fn lex_one() -> crate::automata::lex_weight::LexicographicWeight {
    use crate::automata::semiring::Semiring;
    crate::automata::lex_weight::LexicographicWeight::one()
}

// C11.3+C11.2 (2026-05-16): the M11.4 `From<LexicographicWeight> for
// DerivationWeight<...>` impl + M11.5 `SnapshotWeight` trait + 3 impls
// were deleted alongside the C10 W revert. Structural ambiguity now
// lives in the SPPF arena (Symbol-dedup at `(nt, lo, hi)`); the walker
// no longer needs to lift LexicographicWeight into a multiset semiring,
// nor inject builder snapshots into weight entries.

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
    use crate::automata::semiring::{Semiring, TropicalWeight};
    use crate::lexer_types::{LexAlternative, LexEntry, LexStream};

    fn ascii_alt(text: &str, end: usize, weight: f64) -> LexAlternative {
        LexAlternative {
            kind: TokenKind::Ident,
            text: text.to_string(),
            end_byte: end,
            weight: TropicalWeight::new(weight),
        }
    }

    fn fake_lex(input: &str) -> Result<LexStream, std::string::String> {
        // Trivial whitespace-tokenizing lexer: each non-empty whitespace-
        // separated word becomes an `Ident` LexEntry. Used only for
        // MutableMultiTokenSource unit tests.
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
            entries.push(LexEntry {
                byte_start: start,
                alternatives: vec![ascii_alt(text, i, 1.0)],
            });
        }
        Ok(LexStream { entries })
    }

    #[test]
    fn mutable_token_source_initial_lex() {
        let m =
            MutableMultiTokenSource::new("foo bar baz".to_string(), fake_lex).expect("construct");
        assert_eq!(m.len(), 3);
        assert_eq!(m.peek_text(0), Some("foo"));
        assert_eq!(m.peek_text(1), Some("bar"));
        assert_eq!(m.peek_text(2), Some("baz"));
    }

    #[test]
    fn mutable_token_source_replace_range_relexes() {
        let mut m =
            MutableMultiTokenSource::new("foo bar".to_string(), fake_lex).expect("construct");
        let (start, end) = m.replace_range(4, 7, "qux qux2").expect("replace_range");
        // Replacement of "bar" with "qux qux2" — old token start=1, end=2;
        // new tokens cover 1..=2 (qux, qux2).
        assert!(start <= 1);
        assert!(end >= 3);
        assert_eq!(m.peek_text(0), Some("foo"));
        assert_eq!(m.peek_text(1), Some("qux"));
        assert_eq!(m.peek_text(2), Some("qux2"));
    }

    #[test]
    fn mutable_token_source_commit_alternative_swaps_primary() {
        // Construct via direct stream injection so we control the
        // alternatives. The `fake_lex` produces single-alt entries; for
        // commit_alternative we need an entry with two alts.
        let stream = LexStream {
            entries: vec![LexEntry {
                byte_start: 0,
                alternatives: vec![ascii_alt("foo", 3, 1.0), ascii_alt("foobar", 6, 2.0)],
            }],
        };
        let inner = MultiTokenSource::new(stream);
        let mut m = MutableMultiTokenSource {
            inner,
            source_text: "foobar".to_string(),
            lex_fn: fake_lex,
        };
        assert_eq!(m.peek_text(0), Some("foo"));
        // Commit alt 1 (foobar, end=6).
        let (s, e) = m.commit_alternative(0, 1).expect("commit");
        assert_eq!(s, 0);
        assert!(e >= 1);
        // After commit, primary is the 6-byte form.
        assert_eq!(m.peek_text(0), Some("foobar"));
    }

    #[test]
    fn mutable_token_source_swap_tokens_preserves_separator_and_relexes() {
        let mut m =
            MutableMultiTokenSource::new("foo   bar baz".to_string(), fake_lex).expect("construct");
        let (start, end) = m.swap_tokens(0, 1).expect("swap tokens");
        assert_eq!(start, 0);
        assert!(end >= 2);
        assert_eq!(m.source(), "bar   foo baz");
        assert_eq!(m.peek_text(0), Some("bar"));
        assert_eq!(m.peek_text(1), Some("foo"));
        assert_eq!(m.peek_text(2), Some("baz"));
    }

    #[test]
    fn mutable_token_source_swap_tokens_rejects_non_adjacent_positions() {
        let mut m =
            MutableMultiTokenSource::new("foo bar baz".to_string(), fake_lex).expect("construct");
        let err = m.swap_tokens(0, 2).expect_err("non-adjacent swap");
        assert!(err.contains("not adjacent"), "unexpected swap_tokens error: {}", err,);
    }

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
        assert!(WpdaState::Accepted.is_terminal());
        assert!(WpdaState::Error { message: "x".into() }.is_terminal());
        assert!(!WpdaState::Ready { min_bp: 0 }.is_terminal());
        assert!(!WpdaState::Unwinding.is_terminal());
        assert!(!WpdaState::PrefixDispatch { pos: 0, cur_bp: 0 }.is_terminal());
    }

    #[test]
    fn mutable_slice_token_source_applies_token_edits() {
        let kinds = [TokenKind::Ident, TokenKind::Fixed("+".into()), TokenKind::Ident];
        let texts = ["lhs", "+", "rhs"];
        let mut src = MutableSliceTokenSource::with_texts(&kinds, &texts);

        src.substitute_token(1, TokenKind::Fixed("-".into()), "-".into())
            .expect("substitute");
        assert_eq!(src.peek_kind(1), Some(TokenKind::Fixed("-".into())));
        assert_eq!(src.peek_text(1), Some("-"));

        src.insert_token(3, TokenKind::Fixed(";".into()), ";".into())
            .expect("insert at eof boundary");
        assert_eq!(src.len(), 4);
        assert_eq!(src.peek_text(3), Some(";"));

        src.swap_tokens(0, 1).expect("adjacent swap");
        assert_eq!(src.peek_text(0), Some("-"));
        assert_eq!(src.peek_text(1), Some("lhs"));
    }

    #[test]
    fn mutable_slice_token_source_rejects_unavailable_byte_edits() {
        let kinds = [TokenKind::Ident];
        let texts = ["x"];
        let mut src = MutableSliceTokenSource::with_texts(&kinds, &texts);

        let err = src
            .replace_range(0, 1, "y")
            .expect_err("slice source has no byte-addressed backing text");
        assert!(err.contains("token-addressed"), "unexpected error: {}", err);
    }

    #[test]
    fn wpds_event_constructible_with_tropical_weight() {
        let _step: WpdaEvent<TropicalWeight> = WpdaEvent::Step;
        let _tok: WpdaEvent<TropicalWeight> =
            WpdaEvent::TokenConsumed { pos: 0, token: TokenKind::Ident };
        let _fork: WpdaEvent<TropicalWeight> =
            WpdaEvent::BranchForked { parent: 0, children: vec![1, 2] };
        let _resolved: WpdaEvent<TropicalWeight> =
            WpdaEvent::BranchResolved { winner: 1, weight: TropicalWeight::one() };
        let _action: WpdaEvent<TropicalWeight> =
            WpdaEvent::SemanticActionFired { action_id: 7, args: vec![0, 1] };
        let _cp: WpdaEvent<TropicalWeight> = WpdaEvent::Checkpoint {
            reason: CheckpointReason::NaturalBoundary,
        };
        let _ins: WpdaEvent<TropicalWeight> = WpdaEvent::Inspect;
    }

    #[test]
    fn wpds_transition_variants_constructible() {
        let _no: WpdaTransition<TropicalWeight> = WpdaTransition::NoChange;
        let _t: WpdaTransition<TropicalWeight> = WpdaTransition::Transition {
            new_state: WpdaState::Accepted,
            trace: None,
        };
        let _cp: WpdaTransition<TropicalWeight> = WpdaTransition::Checkpoint {
            config: WpdaConfiguration {
                pos: 5,
                state: WpdaState::Ready { min_bp: 0 },
                stack: vec![StackSymbolV2::category_entry(0)],
                weight: TropicalWeight::one(),
            },
        };
        let _done: WpdaTransition<TropicalWeight> =
            WpdaTransition::Done { state: WpdaState::Accepted };
    }

    #[test]
    fn wpds_control_pause_exists() {
        // M6: WpdaControl::Pause must exist for Rholang §13.1 compatibility.
        let _c = WpdaControl::Continue;
        let _h = WpdaControl::Checkpoint;
        let _a = WpdaControl::Abort;
        let _p = WpdaControl::Pause;
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
        let cfg: WpdaConfiguration<TropicalWeight> = WpdaConfiguration {
            pos: 42,
            state: WpdaState::InfixLoop { cur_bp: 7 },
            stack: vec![StackSymbolV2::category_entry(0), StackSymbolV2::rule_at(0, 3, 1, Some(7))],
            weight: TropicalWeight::one(),
        };
        let cloned = cfg.clone();
        assert_eq!(cfg, cloned);
    }

    #[test]
    fn wpds_state_ambiguity_fanout_holds_branches() {
        let s = WpdaState::AmbiguityFanout { branches: vec![10, 20, 30] };
        match s {
            WpdaState::AmbiguityFanout { branches } => {
                assert_eq!(branches, vec![10u32, 20u32, 30u32]);
            },
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
        // Ensures Debug doesn't try to print the dyn Any internals.
        // Stage 3.6 / ι Phase 1 (2026-05-01): Box → Arc.
        let a = ActionArg::Term { value: Arc::new(42i32), type_name: "i32" };
        let s = format!("{:?}", a);
        assert!(s.contains("Term"));
        assert!(s.contains("i32"));
    }

    #[test]
    fn action_entry_debug_hides_fn_body() {
        fn my_action(_b: &mut SemanticBuilder, _a: Vec<ActionArg>) {}
        let e = ActionEntry {
            action_fn: my_action,
            arity: 3,
            expected_input_cats: &[ANY_CAT, ANY_CAT, ANY_CAT],
            output_cat: 0,
        };
        let s = format!("{:?}", e);
        assert!(s.contains("arity: 3"));
    }

    #[test]
    fn action_entry_is_copy() {
        fn my_action(_b: &mut SemanticBuilder, _a: Vec<ActionArg>) {}
        let e = ActionEntry {
            action_fn: my_action,
            arity: 2,
            expected_input_cats: &[ANY_CAT, ANY_CAT],
            output_cat: 0,
        };
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
        let collected: Vec<i32> = args
            .into_iter()
            .next()
            .unwrap()
            .into_collection()
            .expect("Vec<i32>");
        assert_eq!(collected, vec![1, 2, 3]);
    }

    // ──────────────────────────────────────────────────────────────────
    // M3 (2026-05-13): LatticeTokenSource + next_pos
    // ──────────────────────────────────────────────────────────────────

    /// Build a small LexDag for `-3` to exercise LatticeTokenSource.
    /// The DFA recognizes `-?\d+` (Integer) AND `-` (Minus). See the
    /// `runtime_types::tests::make_test_dfa` for the recipe.
    fn make_minus3_dag() -> crate::lexer_types::LexDag {
        let mut char_class = [2u8; 256];
        char_class[b'-' as usize] = 0;
        for c in b'0'..=b'9' {
            char_class[c as usize] = 1;
        }
        let dfa_next = |s: u32, c: u8| -> u32 {
            match (s, c) {
                (0, 0) => 1,
                (0, 1) => 2,
                (1, 1) => 2,
                (2, 1) => 2,
                _ => u32::MAX,
            }
        };
        let is_accepting = |s: u32| -> bool { s == 1 || s == 2 };
        let accept_alternatives = |s: u32, _text: &str| -> Vec<(crate::automata::TokenKind, f64)> {
            match s {
                1 => vec![(crate::automata::TokenKind::Fixed("-".to_string()), 0.0)],
                2 => vec![(crate::automata::TokenKind::Integer, 0.0)],
                _ => Vec::new(),
            }
        };
        let token_to_kind =
            |t: &crate::automata::TokenKind| -> crate::automata::TokenKind { t.clone() };
        crate::runtime_types::lex_dag_core(
            "-3",
            None,
            &char_class,
            dfa_next,
            is_accepting,
            accept_alternatives,
            token_to_kind,
        )
        .expect("lex_dag should succeed")
    }

    #[test]
    fn lattice_source_peek_kind_returns_primary() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        // Node 0 is at byte 0; primary edge = Integer (longest, end=2).
        assert!(matches!(src.peek_kind(0), Some(TokenKind::Integer)));
    }

    #[test]
    fn lattice_source_peek_text_returns_primary_text() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        // Primary edge from node 0 consumes "-3".
        assert_eq!(src.peek_text(0), Some("-3"));
    }

    #[test]
    fn lattice_source_is_ambiguous_at_node_0() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        // Node 0 has 2 edges (Integer + Minus).
        assert!(src.is_ambiguous_at(0));
        let alts = src.peek_alternatives(0);
        // Secondaries only (primary is at edges[0]; alts = edges[1..]).
        assert_eq!(alts.len(), 1);
        assert!(matches!(alts[0].kind, TokenKind::Fixed(ref s) if s == "-"));
    }

    #[test]
    fn lattice_source_next_pos_returns_alt_target() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        // Primary edge (alt_idx=0) targets the node at byte 2 (end of "-3").
        let primary_target = src.next_pos(0, 0).expect("primary edge must exist");
        // Secondary edge (alt_idx=1) targets the node at byte 1 (end of "-").
        let secondary_target = src.next_pos(0, 1).expect("secondary edge must exist");
        assert_ne!(primary_target, secondary_target);
        // Verify the byte_start of each target node.
        assert_eq!(src.dag.nodes[primary_target].byte_start, 2);
        assert_eq!(src.dag.nodes[secondary_target].byte_start, 1);
    }

    #[test]
    fn lattice_source_end_byte_matches_edge() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        assert_eq!(src.end_byte(0, 0), Some(2)); // Integer ends at byte 2
        assert_eq!(src.end_byte(0, 1), Some(1)); // Minus ends at byte 1
    }

    #[test]
    fn slice_source_next_pos_default_linear() {
        // SliceTokenSource uses the default `next_pos = pos + 1` impl.
        // Verify it advances linearly regardless of alt_idx.
        let kinds = vec![TokenKind::Integer, TokenKind::Eof];
        let src = SliceTokenSource::new(&kinds);
        assert_eq!(src.next_pos(0, 0), Some(1));
        assert_eq!(src.next_pos(0, 5), Some(1)); // ignores alt_idx
        assert_eq!(src.next_pos(2, 0), None); // past end
    }
}
