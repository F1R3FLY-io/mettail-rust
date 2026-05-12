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
use std::sync::Arc;

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
    /// `WpdsState::OptionalGroup { sub_pos: payload }`.
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

    /// B7 Pattern 2: construct a grouping-marker symbol. `outer_bp` is
    /// the saved Pratt cur_bp at the open `(`; on close `)`, the engine
    /// transitions to `WpdsState::InfixLoop { cur_bp: outer_bp }` so
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
    pub fn mixfix_marker(
        result_src_idx: u16,
        rule_idx: u16,
        operands_completed: u8,
    ) -> Self {
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
            SymbolKind::GroupingMarker => {
                write!(f, "⟨cat#{}.group⟩{}", self.category_src_idx, bp_suffix)
            }
            SymbolKind::MixfixMarker => write!(
                f,
                "⟨cat#{}.rule#{}.mixfix⟩{}",
                self.category_src_idx, self.rule_index_in_category, bp_suffix
            ),
            SymbolKind::OptionalGroupAt(sub_pos) => write!(
                f,
                "⟨cat#{}.rule#{}.opt@{}⟩{}",
                self.category_src_idx,
                self.rule_index_in_category,
                sub_pos,
                bp_suffix
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
///
/// Stage 3.5b (2026-05-01): adds `Hash` derive so cursor configurations
/// `(state, gss_node_id, pos)` can be the key for `merge_equivalent_cursors`
/// — the WPDS ⊕-merging step that collapses paths reaching the same
/// configuration via `Semiring::plus`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        /// Outer Pratt cur_bp to restore after the delegation completes.
        outer_bp: u8,
    },
    /// Multiple GSS branches active simultaneously; awaiting resolution.
    /// The `branches: Vec<GssNodeId>` field lists the GSS-tip node ids of
    /// every live branch. Per-branch micro-state (pos, weight, inner
    /// state) is stored out-of-band on the walker as
    /// `WpdsWalker::branch_cursors: Vec<BranchCursor<W>>` parallel to
    /// this vector — the i-th `branches` entry corresponds to the i-th
    /// `branch_cursors` entry. The reason for the split is that `WpdsState`
    /// is non-generic but per-branch weight requires the walker's `W`
    /// parameter; storing weights inside the state enum would force
    /// `WpdsState` to be generic and cascade through every consumer.
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

impl WpdsState {
    /// Whether this state is terminal (Accepted or Error).
    pub fn is_terminal(&self) -> bool {
        matches!(self, WpdsState::Accepted | WpdsState::Error { .. })
    }
}

/// Stage 3.5b (2026-05-01): the result of `WpdsWalker::resolve_at_end_of_input`,
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
pub enum WpdsResolveResult<W: Semiring> {
    /// Single Accepted configuration at EOI.
    Accepted {
        weight: W,
        term: Arc<dyn std::any::Any + Send + Sync>,
    },
    /// ≥2 Accepted configurations tied on weight after `LexicographicWeight`
    /// 4-tuple comparison. `equivalence_class_size` reports how many
    /// branches tied; the chosen `term` is the source-order earliest.
    AcceptedAmbiguous {
        weight: W,
        term: Arc<dyn std::any::Any + Send + Sync>,
        equivalence_class_size: usize,
    },
    /// Zero accepting configurations at EOI — input cannot be parsed by
    /// the grammar. `position` is where the cursor stalled (max position
    /// reached among dead cursors).
    ParseError { message: String, position: usize },
    /// Driver hit `max_steps` budget before reaching EOI. Caller may
    /// resume by extending the budget.
    MaxStepsExceeded { position: usize },
}

/// Stage 3.5b (2026-05-01): error returned by `WpdsWalker::run_to_end_of_input`
/// when the driver exhausts its `max_steps` budget before reaching EOI
/// or a terminal state. Caller may extend the budget and resume by
/// calling `run_to_end_of_input` again with a larger `max_steps`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WpdsMaxStepsExceeded {
    pub position: usize,
}

impl std::fmt::Display for WpdsMaxStepsExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "WPDS walker exceeded max_steps before reaching end of input (position={})",
            self.position
        )
    }
}

impl std::error::Error for WpdsMaxStepsExceeded {}

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
}

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
pub trait WpdsMutableTokenSource: WpdsTokenSource {
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
        let (start, end) = self.byte_span_of(pos).ok_or_else(|| {
            format!("substitute_token: no byte span at pos {}", pos)
        })?;
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
        let (start, _) = self.byte_span_of(pos).ok_or_else(|| {
            format!("insert_token: no byte span at pos {}", pos)
        })?;
        let with_sep = format!("{} ", text);
        self.replace_range(start, start, &with_sep)
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
}

/// L10 (2026-04-28): a `WpdsMutableTokenSource` that wraps a
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
        Ok(Self {
            inner,
            source_text: source,
            lex_fn,
        })
    }

    /// Borrow the underlying source text.
    pub fn source(&self) -> &str {
        &self.source_text
    }
}

impl<L> WpdsTokenSource for MutableMultiTokenSource<L>
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

impl<L> WpdsMutableTokenSource for MutableMultiTokenSource<L>
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
        self.source_text.replace_range(byte_start..byte_end, new_bytes);
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
                format!(
                    "commit_alternative: alt_idx {} out of bounds at pos {}",
                    alt_idx, pos,
                )
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
            let original_tail: std::string::String =
                self.source_text[tail_start..].to_string();
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

/// L4 (2026-04-28): a `WpdsTokenSource` backed by a [`LexStream`].
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

impl WpdsTokenSource for MultiTokenSource {
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
///
/// Stage 3.6 / ι Phase 1 (2026-05-01): `Term`, `Collection`, and
/// `Predicate` payloads are `Arc<dyn Any + Send + Sync>` (was
/// `Box<dyn Any + Send>`) so `ActionArg` derives `Clone`. This unblocks
/// `BranchCursor::clone` for cursors with populated `collection_stack`
/// accumulators (the pre-3.6 `debug_assert!` panic at line 416 of
/// `wpds_walker.rs` is no longer needed). AST types are `Clone` (manual
/// impls via `iterative_clone.rs`); primitives are `Clone`. Accessors
/// `into_term::<T>` / `into_collection::<T>` / `into_predicate::<T>`
/// gain a `T: Clone` bound so they can deep-clone out of the Arc when
/// the value is shared.
#[derive(Clone)]
pub enum ActionArg {
    /// A raw token kind + its text + position.
    Token { kind: TokenKind, text: String, pos: usize },
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
            ActionArg::Optional(None) => f
                .debug_struct("Optional")
                .field("present", &false)
                .finish(),
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
/// `cursor_will_produce_term` (in `wpds_walker.rs`) to dry-run the
/// FireAction sequence on a cursor's `pending_builder_ops` and decide
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
pub struct SemanticBuilder {
    stack: Vec<ActionArg>,
    binder_scopes: Vec<BinderHandle>,
    /// Phase 4: in-flight collection accumulators, indexed by id. Each
    /// entry collects `ActionArg::Term` values pushed during element
    /// parsing; the collection-finalize action drains the entry and
    /// constructs the final container (HashBag / Vec / etc.).
    collection_stack: Vec<Vec<ActionArg>>,
    /// Opt-Group (2026-04-29): in-flight inner-arg accumulators for
    /// taken optional groups. When `start_optional_scope()` is called
    /// (auto-triggered when the walker pushes an
    /// `OptionalGroupAt(1)` marker), a fresh `Vec<ActionArg>` is
    /// pushed onto this stack. While the stack top is non-empty, every
    /// subsequent `push_xxx` call routes through `push_arg_internal`
    /// to the top inner Vec instead of `stack`. On
    /// `finalize_optional_scope_present()`, the inner Vec is popped
    /// and wrapped as `ActionArg::Optional(Some(inner))` — pushed
    /// either to `stack` (if no outer optional scope is active) or to
    /// the next-outer scope's Vec (nested-Optional flattening).
    ///
    /// On the skip path, no scope is opened; `push_optional_absent()`
    /// pushes `ActionArg::Optional(None)` directly via the same routing.
    optional_stack: Vec<Vec<ActionArg>>,
}

impl SemanticBuilder {
    pub fn new() -> Self {
        SemanticBuilder {
            stack: Vec::new(),
            binder_scopes: Vec::new(),
            collection_stack: Vec::new(),
            optional_stack: Vec::new(),
        }
    }

    /// Opt-Group: route an `ActionArg` push to the top of `optional_stack`
    /// if a scope is open, otherwise to the main `stack`. Nested Optional
    /// chains correctly because the innermost scope is the routing target.
    #[inline]
    fn push_arg_internal(&mut self, arg: ActionArg) {
        self.active_arg_stack_mut().push(arg);
    }

    /// Opt-Group: routing-aware mutable accessor for the active argument
    /// cursor. Returns the innermost open optional scope when one is open,
    /// else the main `stack`. All arg-stack reads/writes during a parse
    /// MUST funnel through this so push/pop stay symmetric — the original
    /// bug (TAKE-path EmptyResult) was that pushes routed into the optional
    /// scope but pops drained `self.stack` directly, so a literal captured
    /// inside `*opt(...)` was popped from the wrong cursor when its
    /// `LiteralPatterned` action fired.
    #[inline]
    fn active_arg_stack_mut(&mut self) -> &mut Vec<ActionArg> {
        if let Some(top) = self.optional_stack.last_mut() {
            top
        } else {
            &mut self.stack
        }
    }

    /// Read-only counterpart to `active_arg_stack_mut`.
    #[inline]
    fn active_arg_stack(&self) -> &Vec<ActionArg> {
        if let Some(top) = self.optional_stack.last() {
            top
        } else {
            &self.stack
        }
    }

    /// Opt-Group: open a new optional-scope inner-arg accumulator. Called
    /// by the walker when pushing `OptionalGroupAt(1)` (the take-path
    /// entry into an optional group).
    pub fn start_optional_scope(&mut self) {
        self.optional_stack.push(Vec::new());
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
    pub fn finalize_optional_scope_present(&mut self) {
        let inner = self.optional_stack.pop().unwrap_or_default();
        let arg = ActionArg::Optional(Some(inner));
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
    pub fn pop_args(&mut self, n: usize) -> Vec<ActionArg> {
        let active = self.active_arg_stack_mut();
        let start = active
            .len()
            .checked_sub(n)
            .expect("SemanticBuilder::pop_args: stack underflow (engine arity bug)");
        active.drain(start..).collect()
    }

    /// Begin a binder scope — used by binder rules before parsing the body.
    pub fn start_binder_scope(&mut self, names: Vec<String>) {
        let depth = self.binder_scopes.len() as u16;
        self.binder_scopes.push(BinderHandle::new(names, depth));
    }

    /// B8 / Issue C followup (2026-05-09): append a binder name to the
    /// innermost open binder scope. Used by multi-binder loops where the
    /// scope opens once at bootstrap with an empty names list, and each
    /// iteration's BinderIdent capture extends the names list with the
    /// captured ident. Without this, subsequent idents (start_scope=false)
    /// only got pushed to the args stack as `ActionArg::Ident`, never
    /// reaching the BinderHandle.names that the action's BinderScope
    /// arg extraction reads.
    pub fn extend_binder_scope(&mut self, name: String) {
        if let Some(handle) = self.binder_scopes.last_mut() {
            handle.names.push(name);
        }
    }

    /// End the innermost binder scope and leave a `BinderScope` arg on the
    /// active argument cursor (so a binder fired inside `*opt(...)` lands
    /// in the inner scope just like other captures).
    pub fn end_binder_scope(&mut self) {
        if let Some(handle) = self.binder_scopes.pop() {
            self.push_arg_internal(ActionArg::BinderScope(handle));
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
        match self.stack.pop()? {
            ActionArg::Term { value, .. } => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            _ => None,
        }
    }

    /// Stage 3.5b (2026-05-01): type-erased variant of `take_result` used by
    /// `WpdsWalker::resolve_at_end_of_input`. The walker is generic over
    /// the semiring W but does not know the parsed term type T at the
    /// resolution surface — `WpdsResolveResult` carries the term as
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
        match self.stack.pop()? {
            ActionArg::Term { value, .. } => Some(value),
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

    /// Pop the top of the active argument cursor (must be a `Term`) and
    /// append it into the collection identified by `id`. Called by the
    /// walker when transitioning to `CollectionLoop` after a per-element
    /// parse. Scope-aware so that a `[a, b, c]` collection literal nested
    /// inside `*opt(...)` correctly drains the inner-scope cursor.
    pub fn push_to_collection(&mut self, id: u8) {
        if let Some(arg) = self.active_arg_stack_mut().pop() {
            if let Some(acc) = self.collection_stack.get_mut(id as usize) {
                acc.push(arg);
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
    /// `wpds_runtime.rs::adopt_collection_stack`). LIFO invariant: every
    /// `drain_collection(id)` call should match the top of the stack
    /// because grammars can only close collections in the reverse order
    /// they opened (the close-delim of an inner collection always
    /// precedes the close-delim of an outer collection that contains it).
    pub fn drain_collection(&mut self, id: u8) -> Vec<ActionArg> {
        let id_usize = id as usize;
        debug_assert!(
            id_usize < self.collection_stack.len(),
            "drain_collection: id {} out of range (collection_stack.len() = {})",
            id, self.collection_stack.len(),
        );
        debug_assert_eq!(
            id_usize + 1,
            self.collection_stack.len(),
            "drain_collection: LIFO violation — id {} is not the top of \
             collection_stack (len = {}). Collections must finalize in \
             reverse open order.",
            id, self.collection_stack.len(),
        );
        if id_usize + 1 == self.collection_stack.len() {
            self.collection_stack.pop().unwrap_or_default()
        } else if let Some(acc) = self.collection_stack.get_mut(id_usize) {
            // Defensive fallback in release builds when LIFO is violated:
            // drain the slot in place (legacy mem::take behavior). Slot
            // remains, leaving an empty husk — but better than panicking
            // on a non-LIFO grammar (none ship today; future grammars
            // would surface via the debug_assert above).
            std::mem::take(acc)
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
    pub fn adopt_collection_stack(&mut self, accs: Vec<Vec<ActionArg>>) {
        debug_assert!(
            self.collection_stack.is_empty(),
            "adopt_collection_stack: live builder collection_stack must be \
             empty at fanout boundary; got {} in-flight accumulators",
            self.collection_stack.len(),
        );
        self.collection_stack = accs;
    }

    /// Stage 3.12.8 (2026-05-03): collection_stack length accessor for
    /// the `BuilderDelta::FinalizeCollection` replay invariant check.
    pub fn collection_stack_len(&self) -> usize {
        self.collection_stack.len()
    }

    /// Phase 4 #5b (2026-05-12): per-slot length accessor used by the
    /// walker's `set_cursor_inner_state` to compute `kv_phase` parity
    /// for HashMap collection slots in Lazy mode. Returns 0 if the
    /// `acc_id` is out of range (defensive — should not happen under
    /// correct push/pop pairing).
    pub fn collection_slot_len(&self, acc_id: usize) -> usize {
        self.collection_stack.get(acc_id).map(|s| s.len()).unwrap_or(0)
    }

    /// Stage 3.16 / Hack #7 walker fix (Mechanism γ closure, 2026-05-05) —
    /// remove the live builder's collection_stack and return ownership.
    /// Used at the Lazy→Strict mode promotion in `apply_action::Fork` to
    /// transfer Lazy-time-allocated collection slots into the parent
    /// cursor's `collection_stack` so children inherit aligned slot
    /// ownership. After this call the live builder's stack is empty —
    /// `adopt_collection_stack` can subsequently re-populate it from the
    /// winning cursor.
    pub fn take_collection_stack(&mut self) -> Vec<Vec<ActionArg>> {
        std::mem::take(&mut self.collection_stack)
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
    pub fn push_collection_slot(&mut self, drained: Vec<ActionArg>) {
        self.collection_stack.push(drained);
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
        let m = MutableMultiTokenSource::new("foo bar baz".to_string(), fake_lex)
            .expect("construct");
        assert_eq!(m.len(), 3);
        assert_eq!(m.peek_text(0), Some("foo"));
        assert_eq!(m.peek_text(1), Some("bar"));
        assert_eq!(m.peek_text(2), Some("baz"));
    }

    #[test]
    fn mutable_token_source_replace_range_relexes() {
        let mut m = MutableMultiTokenSource::new("foo bar".to_string(), fake_lex)
            .expect("construct");
        let (start, end) = m
            .replace_range(4, 7, "qux qux2")
            .expect("replace_range");
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
                alternatives: vec![
                    ascii_alt("foo", 3, 1.0),
                    ascii_alt("foobar", 6, 2.0),
                ],
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
        // Ensures Debug doesn't try to print the dyn Any internals.
        // Stage 3.6 / ι Phase 1 (2026-05-01): Box → Arc.
        let a = ActionArg::Term {
            value: Arc::new(42i32),
            type_name: "i32",
        };
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
        let collected: Vec<i32> = args.into_iter().next().unwrap().into_collection().expect("Vec<i32>");
        assert_eq!(collected, vec![1, 2, 3]);
    }
}
