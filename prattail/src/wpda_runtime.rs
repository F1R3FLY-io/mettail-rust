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
// Collection slot spec (Stage 2 consolidation, 2026-06-27)
// ══════════════════════════════════════════════════════════════════════════════

/// One collection slot's compile-time descriptor, keyed at runtime by
/// `(result_src_idx, rule_idx, slot_idx)` through
/// [`crate::wpda_walker::WpdaEngine::collection_spec`].
///
/// This single record supersedes the five former per-field lookups the
/// codegen emitted (close, `(close, sep)`, element-src, kv-separator, and the
/// inline `(close, sep, kv_sep, is_binder_internal)` tuple the
/// `CollectionLoop` arm built). Each consumer now reads the field it needs:
///
/// - `close` / `sep` — always present for a collection slot.
/// - `min_elements` — the lower cardinality bound of the repetition.  The
///   generated `.*sep(..)` and declared collection literals use zero; carrying
///   the bound in the descriptor keeps the empty-entry decision structural
///   rather than inferred from delimiters.
/// - `kv_sep` — `Some(..)` iff the slot is a key/value map (`HashMap` /
///   `PathMap`), else `None`.
/// - `element_src_idx` — the element category's `src_idx`, `Some(..)` iff it
///   resolves to a declared category, else `None`.
/// - `close_resumes_via_unwinding` — `true` for binder-internal collection
///   slots (their close resumes the binder continuation via `Unwinding`),
///   `false` for Class-5 Pratt-primary literals (their close resumes the
///   enclosing `InfixLoop`). This is the former loop-arm `is_binder_internal`
///   selector; it is distinct from the 2-tuple
///   [`crate::wpda_walker::WpdaEngine::is_binder_internal_collection`]
///   FireAction-suppression query, which is keyed `(src, rule)` without a slot.
/// - `open` / `has_synth_paren` — the Class-5 open delimiter (the first
///   `Fixed` token, and whether a synthetic `(` follows). Binder-internal
///   slots carry `""` / `false`; their open side is driven by the binder rule
///   machinery, not this record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CollectionSpec {
    /// First-token slice of the open delimiter (Class-5 literals only;
    /// `""` for binder-internal slots).
    pub open: &'static str,
    /// Whether a synthetic `"("` token follows the open keyword (Class-5
    /// 4-element default form; `false` for binder-internal slots).
    pub has_synth_paren: bool,
    /// Close delimiter literal.
    pub close: &'static str,
    /// Element/pair separator literal.
    pub sep: &'static str,
    /// Minimum number of elements admitted by this collection occurrence.
    pub min_elements: u8,
    /// Key/value separator for kv-maps (`Some(":")`), else `None`.
    pub kv_sep: Option<&'static str>,
    /// Whether the per-entry value is OPTIONAL for this kv-collection
    /// (Pathmap set-form `{| k |}` ≡ `{| k : k |}`, value = key). `true`
    /// ONLY for Pathmap; `false` for HashMap (whose values are mandatory)
    /// and for every non-kv container. When `true`, a `kv_phase == 1` entry
    /// whose next token is the close/separator (not the `kv_sep`) is
    /// finalized as a bare path with value = key instead of erroring.
    pub kv_value_optional: bool,
    /// The element category's `src_idx`, when it resolves to a declared
    /// category; `None` otherwise.
    pub element_src_idx: Option<u16>,
    /// `true` ⇒ close resumes via `Unwinding` (binder-internal); `false` ⇒
    /// close resumes the enclosing `InfixLoop` (Class-5 Pratt primary).
    pub close_resumes_via_unwinding: bool,
}

/// Stage 4 (Lever-1, "emit-both" delimiter precedence): the structural-delimiter
/// context of the **innermost enclosing collection frame**, computed by the
/// walker from a cursor/shell's incoming-edge stack and threaded into
/// [`crate::wpda_walker::WpdaEngine::step`].
///
/// ## Why it exists
/// A collection element/value is parsed by a *fresh* sub-parse (`CategoryEntry`
/// frame on top of the GSS), whose `InfixLoop` does not, by itself, know the
/// delimiters of the collection frame **below** it. On a lattice-ambiguous
/// multi-char close (e.g. the Pathmap close `|}`, whose leading `|` collides
/// with the `PParInfix` operator), the lex-fork
/// ([`crate::wpda_walker`]-emitted `emit_lex_fork_at_infix_loop`) forks the
/// colliding operator branch and *pre-empts* the no-candidate
/// `Advance(Unwinding)` fall-through that a non-ambiguous close would have taken
/// — so the element never yields back to the `CollectionMarker` and the close
/// never resumes. `FrameCtx` carries the innermost collection's
/// `close`/`sep`/`kv_sep` so the lex-fork can re-add that yield branch
/// **alongside** (never instead of) the operator branches ("emit-both"): the
/// doomed operator fork dies under the ambiguity budget, the yield pops the
/// element, and the `CollectionMarker` resumes its close.
///
/// ## Faithfulness contract (red-team RT3-MINOR7)
/// `FrameCtx` describes the **innermost** frame only — never the union of all
/// enclosing frames. The existence-only union fast-reject lives in the
/// `EdgeStackScopeFlags::STRUCTURAL_DELIM` bit; the *delimiter values* here come
/// from the nearest `CollectionMarker`'s [`CollectionSpec`]. Keeping it
/// innermost-only is what makes the forward sub-parse member-independent (the
/// `parse_pure` read-set argument): cohort members of one worker share the
/// innermost structural frame, so this may be computed once per merged frontier
/// and broadcast.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FrameCtx {
    /// Innermost enclosing collection's close delimiter (`""` when there is no
    /// enclosing collection frame — see [`FrameCtx::has_frame`]).
    pub close: &'static str,
    /// Innermost enclosing collection's element/pair separator (`""` when none).
    pub sep: &'static str,
    /// Innermost enclosing collection's key/value separator (`Some(":")` for
    /// kv-maps), `None` otherwise.
    pub kv_sep: Option<&'static str>,
    /// `true` iff there is an enclosing structural (collection) frame. When
    /// `false`, the delimiter fields are inert and the lex-fork emits no yield.
    pub has_frame: bool,
}

impl FrameCtx {
    /// The empty context: no enclosing structural frame.
    pub const EMPTY: FrameCtx = FrameCtx {
        close: "",
        sep: "",
        kv_sep: None,
        has_frame: false,
    };

    /// Whether there is an enclosing structural (collection) frame (the
    /// existence-only fast-reject result).
    #[inline]
    pub fn has_structural_frame(&self) -> bool {
        self.has_frame
    }

    /// `true` iff `text` equals one of the innermost frame's required structural
    /// delimiters (`close` / `sep` / `kv_sep`). Always `false` when there is no
    /// enclosing frame, so it is safe to call unconditionally.
    #[inline]
    pub fn matches_delim(&self, text: &str) -> bool {
        self.has_frame
            && (text == self.close || text == self.sep || self.kv_sep.is_some_and(|k| k == text))
    }
}

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
    /// collection rule; `bp` carries the rule-local collection slot id used
    /// by generated close/separator/element lookup tables. The live runtime
    /// accumulator id is allocated by the walker and carried through the
    /// associated CollectionId action argument.
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
    /// Marker for a taken `OptionalGroup` inner-position walk. Its dense
    /// marker ID is packed into `StackSymbolV2`'s existing category/rule
    /// fields; generated metadata recovers the exact rule, group, and next
    /// sub-position. `bp` carries the outer Pratt binding power.
    OptionalGroupAt,
    /// Class-3 binder-list continuation marker. It uses the same dense-ID
    /// packing as `OptionalGroupAt`, but its distinct kind prevents optional
    /// and binder continuations from aliasing. It never opens or finalizes an
    /// optional-argument scope.
    BinderListLoopAt,
}

/// A WPDS stack symbol indexed by integer category and rule position.
///
/// Designed for runtime hot-path use: at most 14 bytes (vs. ~96 bytes for
/// [`crate::wpds::StackSymbol`] which uses two `String`s). Indices reference
/// the language's source-order arrays:
///
/// - `category_src_idx`: position in `language!`'s declared categories.
/// - `rule_index_in_category`: position within that category's `rules { … }` block.
///
/// Both indices are stable across compilation; tiebreak ordering uses them
/// directly (lower index wins).
///
/// `OptionalGroupAt` and `BinderListLoopAt` are the deliberate exception:
/// those kinds reuse the two u16 fields as the high/low halves of a dense
/// generated traversal-marker ID. Their generated unwind table restores the
/// source category, rule, frame, and sub-position without adding a hot-symbol
/// payload.
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
    /// Result-category continuation floor for a closed primary whose ordinary
    /// `bp` slot already carries local control data. `CollectionMarker` uses
    /// `bp` for its static slot and `MixfixMarker` uses it for the completed
    /// operand count, so both preserve the caller's Pratt floor here. `None`
    /// for every other symbol kind keeps unrelated symbol identity unchanged.
    /// This field participates in `Eq`/`Hash`/`Ord`, preventing GSS nodes with
    /// incompatible result continuations from merging.
    pub continuation_bp: Option<u8>,
    /// Cross-cat operand/element GOAL category: `Some(g)` for a STRICT
    /// `category_entry_goal(g)` symbol — the source category index that the
    /// sub-parse rooted at this `CategoryEntry` must ultimately yield. `None`
    /// for every other symbol kind and for every non-strict `category_entry`,
    /// so it never alters their `Eq`/`Hash`/`Ord`/GSS identity (None == None).
    ///
    /// Consumed by the engine's `InfixLoop`: when the frontier-top symbol
    /// carries `Some(g)`, an infix/postfix/mixfix candidate whose RESULT
    /// category `r` provably cannot reach `g` in the post-built cross-cat
    /// extension graph (`cat_can_reach(r, g) == false`) is dropped BEFORE
    /// weighting — bounding an operand to its goal category so a cross-cat-out
    /// operator (`POutput` `Name → Proc`, `InputBindPolyadic` `Name →
    /// InputBind`, …) cannot over-extend a Name operand past `Name`. A `None`
    /// goal (top-level `CrossCatLhs`, all legacy ctors) admits every candidate
    /// ⇒ the gate is inert. See `category_entry_goal` and the goal-gate design
    /// (`scratchpad/crosscat-operand-design.md`).
    pub goal_src_idx: Option<u16>,
}

impl StackSymbolV2 {
    /// Construct a category entry symbol (just before the first prefix dispatch).
    pub fn category_entry(category_src_idx: u16) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category: 0,
            bp: None,
            kind: SymbolKind::CategoryEntry,
            continuation_bp: None,
            goal_src_idx: None,
        }
    }

    /// Construct a STRICT category-entry symbol that carries a GOAL category
    /// (`goal_src_idx = Some(category_src_idx)`). Identical to
    /// [`Self::category_entry`] in every other field, so a strict symbol is
    /// `Eq`/`Hash`/`Ord`-distinct from the corresponding non-strict
    /// `category_entry(c)` ONLY by the goal slot (the GSS therefore treats a
    /// goal-bounded operand frame as its own node — intended: the goal changes
    /// which InfixLoop candidates are admissible). Pushed at cross-cat operand
    /// (mixfix) and element (collection) sites so the operand sub-parse is
    /// bounded to category `c`; see `goal_src_idx`.
    pub fn category_entry_goal(category_src_idx: u16) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category: 0,
            bp: None,
            kind: SymbolKind::CategoryEntry,
            continuation_bp: None,
            goal_src_idx: Some(category_src_idx),
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
            continuation_bp: None,
            goal_src_idx: None,
        }
    }

    /// Construct an infix-continuation symbol (RHS of an infix operator pending).
    pub fn infix_continuation(category_src_idx: u16, rule_index_in_category: u16, bp: u8) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category,
            bp: Some(bp),
            kind: SymbolKind::InfixContinuation,
            continuation_bp: None,
            goal_src_idx: None,
        }
    }

    /// Phase 4: construct a collection-marker symbol. `slot_idx` is packed
    /// into the 8-bit `bp` field. Runtime accumulator ids are allocated by
    /// the walker when this marker is pushed, not stored on the symbol.
    /// `dispatch_bp` is the enclosing Pratt
    /// `cur_bp` at which the collection's open delimiter was dispatched as a
    /// primary; it is preserved in `continuation_bp` so the collection close
    /// resumes `InfixLoop { cur_bp: dispatch_bp }` (a finalized collection
    /// participates in the enclosing Pratt loop just like an atomic primary).
    pub fn collection_marker(
        result_src_idx: u16,
        rule_idx: u16,
        slot_idx: u8,
        dispatch_bp: u8,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(slot_idx),
            kind: SymbolKind::CollectionMarker,
            continuation_bp: Some(dispatch_bp),
            goal_src_idx: None,
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
            continuation_bp: None,
            goal_src_idx: None,
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
        continuation_bp: u8,
    ) -> Self {
        StackSymbolV2 {
            category_src_idx: result_src_idx,
            rule_index_in_category: rule_idx,
            bp: Some(operands_completed),
            kind: SymbolKind::MixfixMarker,
            continuation_bp: Some(continuation_bp),
            goal_src_idx: None,
        }
    }

    /// Opt-Group: construct an `OptionalGroupAt(sub_pos)` marker for the
    /// inner-position walk of a taken optional group. `outer_bp` is the
    /// outer rule's outer_bp, preserved across the group so on group exit
    /// the parent `BinderRule` resumes at the correct precedence level.
    pub fn optional_group_at(marker_id: u32, outer_bp: u8) -> Self {
        StackSymbolV2 {
            category_src_idx: (marker_id >> 16) as u16,
            rule_index_in_category: marker_id as u16,
            bp: Some(outer_bp),
            kind: SymbolKind::OptionalGroupAt,
            continuation_bp: None,
            goal_src_idx: None,
        }
    }

    /// Construct a Class-3 binder-list inner-walk marker. This carries the
    /// same payload shape as `optional_group_at`, but its distinct
    /// `SymbolKind` prevents real `*opt(...)` groups and binder-loop inner
    /// walks from aliasing in rules that contain both.
    pub fn binder_list_loop_at(marker_id: u32, outer_bp: u8) -> Self {
        StackSymbolV2 {
            category_src_idx: (marker_id >> 16) as u16,
            rule_index_in_category: marker_id as u16,
            bp: Some(outer_bp),
            kind: SymbolKind::BinderListLoopAt,
            continuation_bp: None,
            goal_src_idx: None,
        }
    }

    /// Dense codegen identity carried by traversal markers. These marker
    /// kinds repurpose the ordinary category/rule fields as the high/low
    /// halves of one `u32`; generated metadata recovers the rule and frame.
    pub fn traversal_marker_id(&self) -> Option<u32> {
        matches!(self.kind, SymbolKind::OptionalGroupAt | SymbolKind::BinderListLoopAt)
            .then_some(((self.category_src_idx as u32) << 16) | self.rule_index_in_category as u32)
    }

    /// Construct a return symbol (pop pending).
    pub fn return_symbol(category_src_idx: u16, rule_index_in_category: u16) -> Self {
        StackSymbolV2 {
            category_src_idx,
            rule_index_in_category,
            bp: None,
            kind: SymbolKind::Return,
            continuation_bp: None,
            goal_src_idx: None,
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
                "⟨cat#{}.rule#{}.coll⟩{}{}",
                self.category_src_idx,
                self.rule_index_in_category,
                bp_suffix,
                match self.continuation_bp {
                    Some(d) => format!("@d{}", d),
                    None => String::new(),
                }
            ),
            SymbolKind::GroupingMarker => {
                write!(f, "⟨cat#{}.group⟩{}", self.category_src_idx, bp_suffix)
            },
            SymbolKind::MixfixMarker => write!(
                f,
                "⟨cat#{}.rule#{}.mixfix⟩{}{}",
                self.category_src_idx,
                self.rule_index_in_category,
                bp_suffix,
                match self.continuation_bp {
                    Some(d) => format!("@d{}", d),
                    None => String::new(),
                }
            ),
            SymbolKind::OptionalGroupAt => write!(
                f,
                "⟨opt-marker#{}⟩{}",
                ((self.category_src_idx as u32) << 16) | self.rule_index_in_category as u32,
                bp_suffix
            ),
            SymbolKind::BinderListLoopAt => write!(
                f,
                "⟨binder-marker#{}⟩{}",
                ((self.category_src_idx as u32) << 16) | self.rule_index_in_category as u32,
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
        /// Legacy state-carried accumulator field. Generated engines seed
        /// this from the marker's static slot id; cursor-aware walker paths
        /// recover the live runtime accumulator from active collection depth.
        /// It is retained for compatibility with existing state constructors.
        accumulator_id: u8,
        /// Phase 4 #1.B (2026-05-11): codegen-stamped slot identifier
        /// within the rule. The CollectionMarker's `bp` field carries this
        /// value at push time. Used by the 3-tuple-keyed `(close, sep)` lookup in
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
    /// synthetic patterns (no synthetic paren — e.g. Rholang's `"{" ... "}"`),
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
    /// Phase 5: selected binder-rule control state.  With a
    /// `CategoryEntry` on the GSS top it is the cross-category trigger
    /// prelude: the generated engine validates and consumes the rule's
    /// declared leading literal, then pushes `RuleAt(1)`.  With a
    /// `RuleAt(position)` on top it progresses through the remaining
    /// `syntax_pattern` items (literals, binder ident slot, body parse).
    /// After the body returns to Unwinding, the rule's action fires
    /// (constructing `Scope::new(Binder, body)`).  Keeping both phases in one
    /// control state avoids duplicating the rule identity in an extra state;
    /// the pushdown symbol makes the phases disjoint.
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
        /// Dense preorder identity of this Optional group in the rule's
        /// recursive position forest.
        group_idx: u32,
        /// Sub-position within the optional group's inner positions.
        /// `0` = peek FIRST-set; `1..=inner.len()` = walk inner
        /// positions (literals, params, guards, nested optionals).
        sub_pos: u32,
        /// Outer Pratt cur_bp to restore when the group completes.
        outer_bp: u8,
    },
    /// Phase 5b: mid-binder-list-loop (`^[xs]`). Captures `Ident,
    /// separator, Ident, separator, ..., close` into the active binder
    /// scope, then unwinds to the caller continuation stored in the GSS.
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
        /// Preorder identity of this binder-list frame within the rule.
        frame_idx: u32,
        outer_bp: u8,
        /// Position in this frame's per-iteration walk. The caller's
        /// continuation remains in the GSS, so nested loops do not duplicate
        /// caller-specific position metadata here.
        sub_pos: u32,
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
    /// `weights` and `roots` are parallel vectors of length ≥ 1; index
    /// `i` is the i-th accepting root's cursor weight and SPPF root.
    /// Each root may realize to multiple derivation terms through
    /// `WpdaWalker::realize_root_to_terms_with_weights`; generated
    /// `parse_all` facades use that lazy realization path to preserve the
    /// full `Ambiguous(Vec<Term>)` end-state without forcing the whole
    /// forest at resolution time.
    ///
    /// `terms` is a legacy representative cache for direct walker callers
    /// that still expect a term in the resolve result. It is not the
    /// authoritative ambiguity surface; `roots` is.
    ///
    /// **Replaces** the pre-M7c single-result `Accepted{weight, term}`
    /// + `AcceptedAmbiguous{weight, term, equivalence_class_size}` pair
    /// — the M7c semantics carry ALL derivations end-to-end rather
    /// than collapsing to one via lex-min.
    Accepted {
        weights: Vec<W>,
        terms: Vec<Arc<dyn std::any::Any + Send + Sync>>,
        /// Option C / C6 (2026-05-15): each accepting cursor's SPPF root
        /// id. Parallel to `weights` (same length). Used by
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
    /// `weights`/`roots` are parallel (length ≥ 1), mirroring
    /// `Accepted`; `terms` is a legacy representative cache. `position`
    /// is the prefix boundary (the first unconsumed token index).
    /// Disambiguation is preserved: if multiple prefix-accepting cursors
    /// tie at the same furthest position, ALL are carried (the
    /// `Ambiguous` end-state still applies to the prefix).
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
    /// SPPF realization failed before any term was published.
    ///
    /// Reconstruction faults and semantic-key cache exhaustion are distinct
    /// from invalid syntax and from ambiguity exhaustion. The realization boundary
    /// discards every candidate accumulated by the failed call.
    RealizationFailed { error: RealizationError, position: usize },
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
        /// EP-P4 (Stage E): the frontier effective-sample-size ×1000 at the
        /// overflow point (Kish ESS over the live frontier's primary
        /// likelihood mass; see `WpdaWalker::frontier_ess_x1000`). Lets the
        /// surfaced error distinguish "1 winner + noise" (ESS≈1000) from
        /// genuine k-way ambiguity (ESS≈k·1000). `0` marks "not computed at
        /// the emission site" (e.g. a pre-walker raw-probe cap, or a
        /// cohort-overflow that carried no live frontier).
        frontier_ess_x1000: u32,
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
///
/// **Enforcement — the distinct-reading budget** (R-D A1, task #18,
/// 2026-07-15; supersedes the R-D v3 first-fork-window scope):
///
/// The budget is enforced by the descriptor-pure engine (`step_canonical_pure`,
/// the sole parser) WHOLE-RUN at resolve (`cgll_resolve_binarized`) as the count
/// of DISTINCT REALIZED TERMS the goal admits — `|R|_distinct`, the number of
/// observationally-inequivalent readings the `_all` facade would return (same
/// semantic-key surface: `WpdaEngine::semantic_fingerprint` ≡ the facade's
/// `__mettail_wpda_semantic_key`, the output-identity theorem). The parse runs
/// to completion; the resolve loop folds every accepting root's realized terms
/// into ONE shared dedup set and emits a structured
/// `WpdaResolveResult::AmbiguityBudget` the moment `|R|_distinct > n` (strict
/// `>`). There is NO window and NO frontier estimate: an input with a wide
/// TRANSIENT fan that reconverges to `k <= n` readings is Ok (e.g. a cast tower
/// whose ~110 derivations collapse to one term), and an input whose ambiguity
/// emerges only late is still caught (no post-window gap). `actual` on the error
/// is therefore a READING count, not a cursor count; `frontier_ess_x1000` is 0
/// (no live frontier to weight).
///
/// (Historical: before the S1-S6 single-engine re-platform, 2026-07-15, a
/// classic diagnostic engine enforced this budget MID-PARSE against a live
/// cursor/cohort frontier length — a genuinely different quantity, so the two
/// engines could disagree on the same input. That engine and its recompile-free
/// lever were removed; the distinct-reading semantics above are now the sole
/// definition.)
///
/// The overflow is surfaced through the `WpdaResolveResult::AmbiguityBudget {
/// budget, actual, position, frontier_ess_x1000 }` variant and the render
/// "ambiguity budget {budget} exceeded (actual {actual})".
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

/// Reason a checkpoint is being recorded.
///
/// Tags why a checkpoint was taken so a checkpoint cache can decide which to
/// retain under memory pressure. (The Stage-5 `WpdaIncrementalSession` that
/// consumed this was removed in the S1-S6 single-engine re-platform; the enum
/// is retained for the checkpoint API.)
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

/// A WPDS configuration snapshot suitable for checkpointing or replay.
///
/// Generic over weight type `W`. Still produced live by
/// `WpdaWalker::current_configuration`. (The Stage-5 `WpdaIncrementalSession`
/// checkpoint cache that keyed these by position in a
/// `BTreeMap<usize, WpdaConfiguration<LexicographicWeight>>` was removed in the
/// S1-S6 single-engine re-platform.)
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
/// Adds the `Pause` variant promised by
/// `docs/design/made/rholang-target/design.md` §13.1.
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

    /// Source-order key for comparing accepted prefix boundaries.
    ///
    /// Linear token sources use the token index. DAG-backed lattice sources
    /// override this with the node's byte position because node ids are
    /// allocation order, not source order.
    fn position_order_key(&self, pos: usize) -> Option<usize> {
        if pos <= self.len() {
            Some(pos)
        } else {
            None
        }
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

/// One lexer-lattice edge that satisfies a grammar token-family capture.
///
/// A capture such as `name@Ident` is evidence about a token *family*, not
/// permission to collapse the lattice to its primary edge.  Contextual
/// keywords therefore need to retain their secondary `Ident` edge when the
/// enclosing grammar asks for an identifier.  The edge index is preserved so
/// generated engines can attach the same deterministic lexical weight used by
/// ordinary lex-fork branches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenCaptureEdge {
    pub alt_idx: u16,
    pub kind: TokenKind,
    pub text: String,
    pub next_pos: usize,
}

/// Return every distinct outgoing edge at `pos` belonging to `kind_name`.
///
/// The result is primary-first and then lexer order.  Duplicate DFA accepts
/// with the same kind, text, and target are collapsed to the lowest
/// alternative index; they are the same lexical proof and must not multiply
/// parser branches.
pub fn matching_token_capture_edges(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    kind_name: &str,
) -> Vec<TokenCaptureEdge> {
    let mut edges = Vec::new();
    let mut push_distinct = |alt_idx: usize, kind: TokenKind, text: String, next_pos: usize| {
        if !crate::automata::token_kind_matches_capture_name(kind_name, &kind) {
            return;
        }
        if edges.iter().any(|edge: &TokenCaptureEdge| {
            edge.kind == kind && edge.text == text && edge.next_pos == next_pos
        }) {
            return;
        }
        let Ok(alt_idx) = u16::try_from(alt_idx) else {
            return;
        };
        edges.push(TokenCaptureEdge { alt_idx, kind, text, next_pos });
    };

    if let (Some(kind), Some(next_pos)) = (tokens.peek_kind(pos), tokens.next_pos(pos, 0)) {
        push_distinct(0, kind, tokens.peek_text(pos).unwrap_or("").to_string(), next_pos);
    }
    for (secondary_idx, alternative) in tokens.peek_alternatives(pos).iter().enumerate() {
        if let Some(next_pos) = tokens.next_pos(pos, secondary_idx + 1) {
            push_distinct(
                secondary_idx + 1,
                alternative.kind.clone(),
                alternative.text.clone(),
                next_pos,
            );
        }
    }
    edges
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
/// `lex_alt_rules_for_prefix` / `lex_alt_rules_for_infix` functions
/// against each alternative kind in the lex DAG at the current
/// position. An empty result drops the alt branch (rule-out by
/// evidence — no rule in this cat consumes this kind at this site).
/// Prefix and infix dispatch may both return multiple same-token
/// candidates. Each `LexAltRuleInfo { rule_idx, kind }` emits a Fork
/// branch whose shape is determined by `kind`:
///
/// - `Atomic`: atomic-literal consumption via `LexAlt` + `with_kind_return`
///   + `Unwinding` (M6c.3).
/// - `PrefixOp { body_src_idx }`: literal-leading binder trigger via
///   `LexAltPrefixOp` + plain `rule_at(slot=1)` +
///   `BinderRule { body_src_idx, outer_bp }`.
/// - `LeadingCategory { source_src_idx }`: nonterminal-leading composite via
///   ordinary `ReplaceAndPush`: replace the requested category entry with the
///   outer rule's `rule_at(slot=1)`, push the source category entry, and let
///   that source consume the still-current token lattice. Same-category Pratt
///   led rules are excluded and appear only in the infix table.
/// - `CrossCatProjection { source_src_idx }`: transparent wrapper via
///   `rule_at(slot=0).with_kind_return()` + `CrossCatDelegate`.
/// - `CrossCatLhs { source_src_idx }`: source-category LHS delegation via
///   `category_entry(source)` + `CrossCatLhs` GSS edge. This is not a
///   rule-backed branch; `rule_idx` is a stable synthetic discriminator.
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
    /// Literal-leading binder trigger (e.g., unary `Neg` or
    /// `FloatBin . a:Proc, w:Int |- "float" "(" a "," w ")" : Float`).
    /// `body_src_idx` is the initial parsed parameter/body category.
    PrefixOp { body_src_idx: u16 },
    /// Literal-triggered unary rule whose operand belongs to a different
    /// category from the result. Unlike a transparent projection, this rule
    /// consumes the trigger before delegating to `source_src_idx` at
    /// `operand_bp`. Keeping this shape in the lexical-alternative table is
    /// necessary when the trigger also has another reading, such as an
    /// identifier: the WPDA must retain both readings until syntax supplies
    /// enough evidence to choose one.
    CrossCatPrefixUnary { source_src_idx: u16, operand_bp: u8 },
    /// Composite rule whose first syntax item is a category-valued parameter.
    /// This is ordinary child descent, not a transparent projection: after the
    /// child returns, the rule resumes at syntax position 1 and eventually
    /// fires its own constructor action.
    ///
    /// Same-category Pratt led rules are deliberately absent: they belong to
    /// led dispatch, where both left and right powers are enforced.
    LeadingCategory { source_src_idx: u16 },
    /// Transparent cross-category projection (e.g.,
    /// `ProcFloat . a:Float |- a : Proc`) whose source category can consume
    /// the matched token kind.
    CrossCatProjection { source_src_idx: u16 },
    /// Cross-category LHS delegation available at PrefixDispatch through a
    /// source category's FIRST set. The branch does not consume the current
    /// lexical edge in the requesting category; it pushes the source category
    /// and lets that source PrefixDispatch consume whichever lexical
    /// alternative survives by evidence.
    CrossCatLhs { source_src_idx: u16 },
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
    /// GAP-3 (2026-06-28) — 0-operand multi-literal keyword-PREFIX rule
    /// (`MapEmpty . |- "Map" "(" ")"`, `PathmapEmpty`, `NQuoteNil`) whose
    /// trigger ALSO lexes as an identifier (collection category names lex as
    /// a `{Fixed(trigger), Ident}` lattice). At a PrefixDispatch lex-fork the
    /// `Fixed(trigger)` lattice reading binds here so it is NOT dropped in
    /// favour of the `Ident → Var` reading. The walker apply (modelled on
    /// `LexAltPrefixOp`) mirrors the trigger as a `TriggerTerminal`, pushes
    /// `mixfix_marker(cat, rule_idx, 0, continuation_bp)`, and transitions to
    /// `MixfixLiteralRun { kind: 2, parts_len == 0 }` — the SAME runtime arm
    /// the singleton/unified-Fork prefix dispatch uses for non-lattice
    /// triggers. `rule_idx` is carried by the enclosing `LexAltRuleInfo`.
    NullaryPrefixRun,
    /// L9-4 — a LEADING `*flt(node, open, close)` GuestBody capture whose
    /// OPENER token kind (`Custom(open_kind)`) is the PrefixDispatch trigger.
    /// Registering it in `lex_alt_rules_for_prefix` (rather than only in the
    /// legacy peek-match fall-through) makes the FLT reading a FIRST-CLASS
    /// prefix branch that is explored ALONGSIDE any lex-ambiguous alternative
    /// of the opener (e.g. `` lam` `` also lexing as `Ident("lam") -> Var`),
    /// preserving disambiguation instead of dropping the FLT reading. The
    /// walker apply (`forks.rs`) emits the SAME branch as the singleton
    /// `UnifiedDescriptor::LeadingGuestBody` dispatch: push `RuleAt(1)`, enter
    /// `BinderRule`, carry `ConsumeGuestBodyAndPush { open_kind, close_kind }`.
    LeadingGuestBody {
        body_src_idx: u16,
        open_kind: &'static str,
        nested_open_kinds: &'static [&'static str],
        close_kind: &'static str,
    },
    /// L9-3 — a LEADING `b@Tok` builtin/custom token-family capture whose
    /// matching runtime token kind is the PrefixDispatch trigger. The lattice-safe
    /// twin of the legacy `UnifiedDescriptor::LeadingTokenKindCapture` peek-arm
    /// (see `LeadingGuestBody` for why registration here is required). The
    /// walker apply emits: push `RuleAt(1)`, enter `BinderRule`, carry
    /// `GuardedConsumeTokenKindAndPush { kind_name }`.
    LeadingTokenKindCapture {
        body_src_idx: u16,
        kind_name: &'static str,
    },
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
    /// Lazily materialized secondary `LexAlternative` slices. The DAG
    /// already owns all lexical evidence; this cache exists only because
    /// the `WpdaTokenSource` trait returns a borrowed slice of the
    /// legacy `LexAlternative` shape for non-primary alternatives.
    secondary_alts: Vec<std::sync::OnceLock<Vec<crate::lexer_types::LexAlternative>>>,
}

impl LatticeTokenSource {
    /// Construct from a [`crate::lexer_types::LexDag`].
    ///
    /// Primary token observations read directly from the DAG. Secondary
    /// alternatives are converted on first demand per node, so constructing
    /// a lattice source does not eagerly duplicate every ambiguous edge.
    pub fn new(dag: crate::lexer_types::LexDag) -> Self {
        let secondary_alts = (0..dag.nodes.len())
            .map(|_| std::sync::OnceLock::new())
            .collect();
        LatticeTokenSource { dag, secondary_alts }
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

    fn secondary_alts_for(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        let Some(cell) = self.secondary_alts.get(pos) else {
            return &[];
        };
        cell.get_or_init(|| {
            self.dag
                .nodes
                .get(pos)
                .map(|node| {
                    node.edges
                        .iter()
                        .skip(1)
                        .map(|e| crate::lexer_types::LexAlternative {
                            kind: e.kind.clone(),
                            text: e.text.clone(),
                            end_byte: e.end_byte,
                            weight: e.weight,
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .as_slice()
    }

    #[cfg(test)]
    fn materialized_secondary_alt_nodes(&self) -> usize {
        self.secondary_alts
            .iter()
            .filter(|alts| alts.get().is_some())
            .count()
    }
}

impl WpdaTokenSource for LatticeTokenSource {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        let node = self.dag.nodes.get(pos)?;
        Some(
            node.edges
                .first()
                .map(|edge| edge.kind.clone())
                .unwrap_or(TokenKind::Eof),
        )
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        let node = self.dag.nodes.get(pos)?;
        Some(
            node.edges
                .first()
                .map(|edge| edge.text.as_str())
                .unwrap_or(""),
        )
    }

    fn len(&self) -> usize {
        self.dag.nodes.len()
    }

    fn peek_alternatives(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        self.secondary_alts_for(pos)
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

    fn position_order_key(&self, pos: usize) -> Option<usize> {
        self.dag.nodes.get(pos).map(|node| node.byte_start)
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
// LazyLatticeTokenSource — M2L (2026-06-17): on-demand lattice token source
// ══════════════════════════════════════════════════════════════════════════════

/// A type-erased single-node expander: wraps
/// [`crate::runtime_types::expand_lex_node`] with the language-specific lexer
/// closures (`char_class`/`dfa_next`/`is_accepting`/`accept_alternatives`/
/// `token_to_kind`) baked in, erasing the grammar's `Token` type `T`. Given a
/// byte `start` and `start_is_primary`, it returns the expanded node.
type NodeExpander =
    Box<dyn Fn(usize, bool) -> Result<crate::runtime_types::ExpandedLexNode, String>>;

/// A [`WpdaTokenSource`] that materializes lex-DAG nodes ON DEMAND, lazily,
/// instead of building the whole DAG upfront like [`LatticeTokenSource`].
///
/// ## Why
///
/// Eager [`crate::runtime_types::lex_dag_core`] worklist-builds the ENTIRE
/// token DAG (every node + every lex-ambiguous alternative) before the parser
/// reads a single token. For inputs the parser abandons early (a parse error
/// near the start of a long input), most of that lexing work — and the node
/// storage it produces — is never observed. This source defers each node's
/// DFA walk + edge construction until the walker first reads that node id.
///
/// ## Observational equivalence to [`LatticeTokenSource`]
///
/// This source drives the EXACT SAME worklist discipline as
/// [`crate::runtime_types::lex_dag_core`] — seed byte 0, FIFO pops, skip
/// already-allocated `start`s, global `byte_to_node` enqueue dedup,
/// M6c.7.1 primary-chain propagation, M6c.8.1 EOF-first-writer-wins — but
/// PAUSED at the frontier: it only pumps the worklist far enough to answer
/// the queries the walker actually makes. Because the algorithm and FIFO
/// order are identical, the node-id assignment is identical, so every
/// [`WpdaTokenSource`] observation (`peek_kind`, `peek_text`,
/// `peek_alternatives`, `is_ambiguous_at`, `end_byte`, `next_pos`,
/// `position_order_key`, `eof_node`) matches what an eager
/// [`LatticeTokenSource`] over the same input would return — for every
/// position the walker can reach. Positions the walker never reaches are
/// simply never materialized.
///
/// ## Node storage / borrow strategy
///
/// The number of distinct DAG nodes is bounded by `input.len() + 1` (node ids
/// are assigned one per distinct worklist `start`, and every `start` is either
/// byte 0 or an accept `end_byte` in `1..=len`). So node CONTENTS live in a
/// pre-sized `Vec<OnceLock<LexDagNode>>` of length `len + 1`, allocated once at
/// construction and never resized — giving stable addresses so `peek_text` /
/// `peek_alternatives` can return borrowed slices (the same trick the eager
/// `LatticeTokenSource` uses for its per-node secondary-alt cache). The mutable
/// worklist bookkeeping (`byte_to_node`, the pending queue, `primary_targets`,
/// the EOF index, the id high-water mark) lives behind `RefCell`s, mutated only
/// transiently while pumping and released before any borrowed slice is handed
/// out.
///
/// Edges stored in the materialized nodes carry their `end_byte`; their
/// `target_node` field is left as the [`Self::UNRESOLVED`] sentinel and
/// resolved on demand by `next_pos` / `target_node` via `byte_to_node` (which
/// pumps the worklist until the successor at `end_byte` is allocated, in the
/// same FIFO order eager would). Lazy never reads `edge.target_node`.
pub struct LazyLatticeTokenSource {
    /// Owned input bytes (so the source is self-contained; the expander
    /// closure captures only `'static` lexer tables/functions).
    input: String,
    /// Type-erased per-node expander (wraps `expand_lex_node` + closures).
    expander: NodeExpander,
    /// Materialized node contents, indexed by node id. Pre-sized to
    /// `input.len() + 1`; each cell is filled exactly once when its id is
    /// assigned. Stable addresses → borrowed `peek_text`/`peek_alternatives`.
    nodes: Vec<std::sync::OnceLock<crate::lexer_types::LexDagNode>>,
    /// Lazily materialized secondary-alt slices per node id (mirrors the
    /// eager `LatticeTokenSource.secondary_alts`). Same length as `nodes`.
    secondary_alts: Vec<std::sync::OnceLock<Vec<crate::lexer_types::LexAlternative>>>,
    /// Worklist state, mutated only while pumping (then released).
    worklist_state: std::cell::RefCell<LazyWorklistState>,
}

/// The mutable worklist bookkeeping for [`LazyLatticeTokenSource`], mirroring
/// the local state of [`crate::runtime_types::lex_dag_core`].
struct LazyWorklistState {
    /// Map from raw worklist `start` byte → assigned node id (keyed on the
    /// PRE-WS-skip `start`, identical to eager).
    byte_to_node: std::collections::BTreeMap<usize, usize>,
    /// Pending byte positions to allocate (FIFO).
    worklist: std::collections::VecDeque<usize>,
    /// M6c.7.1 primary maximal-munch chain targets (soft-fail discriminator).
    primary_targets: std::collections::HashSet<usize>,
    /// M6c.8.1 canonical EOF sentinel node id (first writer wins), once seen.
    eof_node_idx: Option<usize>,
    /// Number of node ids assigned so far (the high-water mark; equals the
    /// count of materialized nodes — every assigned id fills its cell).
    allocated: usize,
    /// Whether the worklist has drained (no more nodes can ever be allocated).
    drained: bool,
}

impl LazyLatticeTokenSource {
    /// Sentinel `target_node` for stored edges whose successor has not been
    /// resolved through `byte_to_node` yet. Lazy never reads `edge.target_node`
    /// (it resolves successors via `end_byte`), so this value is inert.
    pub const UNRESOLVED: usize = usize::MAX;

    /// Construct a lazy lattice source from the input plus the grammar's lexer
    /// closures — the SAME closures passed to
    /// [`crate::runtime_types::lex_dag_core`] / the generated `lex_dag`. The
    /// generic `T` (the grammar's `Token` type) is erased into the boxed
    /// expander, so the resulting source has no type parameter.
    ///
    /// **Lifetime note**: this convenience constructor requires `T: 'static`,
    /// which fits test/simple lexers whose token type is owned (e.g. the
    /// `lex_dag_core` unit-test DFAs use `T = TokenKind`). Generated lexers
    /// whose `Token<'a>` BORROWS the input cannot satisfy `T: 'static`; they
    /// build the boxed expander themselves and call [`Self::from_expander`]
    /// (the generated `lex_dag_lazy` does exactly this — the closure owns its
    /// input copy and the borrowed `Token<'a>` never escapes a single
    /// `expand_lex_node` call).
    pub fn from_lexer<T: Clone + 'static>(
        input: &str,
        char_class: &'static [u8; 256],
        dfa_next: impl Fn(u32, u8) -> u32 + 'static,
        is_accepting: impl Fn(u32) -> bool + 'static,
        accept_alternatives: impl for<'b> Fn(u32, &'b str) -> Vec<(T, f64)> + 'static,
        token_to_kind: impl Fn(&T) -> TokenKind + 'static,
    ) -> Self {
        let owned: String = input.to_string();
        // The expander owns its own copy of the input so the boxed closure is
        // `'static` (it does not borrow the `LazyLatticeTokenSource.input`
        // field — that would be a self-referential borrow). `expand_lex_node`
        // reads `input[start..]`; passing the owned copy keeps byte offsets
        // identical to the eager DAG over the same bytes.
        let expander_input: String = owned.clone();
        let expander: NodeExpander = Box::new(move |start: usize, start_is_primary: bool| {
            crate::runtime_types::expand_lex_node(
                expander_input.as_str(),
                start,
                char_class,
                &dfa_next,
                &is_accepting,
                &accept_alternatives,
                &token_to_kind,
                start_is_primary,
            )
        });
        Self::from_expander(owned, expander)
    }

    /// Construct a lazy lattice source from an owned `input` and a pre-built,
    /// type-erased per-node `expander`. This is the constructor generated code
    /// uses (its `Token<'a>` cannot satisfy `from_lexer`'s `T: 'static`): the
    /// generated `lex_dag_lazy` builds the boxed `NodeExpander` itself, owning
    /// its own copy of the input so the borrowed `Token<'a>` produced inside
    /// each `expand_lex_node` call never escapes.
    ///
    /// `input` MUST be the same bytes the `expander` lexes, so node
    /// `byte_start`s / `position_order_key`s line up with the eager DAG.
    pub fn from_expander(input: String, expander: NodeExpander) -> Self {
        let owned = input;
        let capacity = owned.len() + 1;
        let mut nodes = Vec::with_capacity(capacity);
        let mut secondary_alts = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            nodes.push(std::sync::OnceLock::new());
            secondary_alts.push(std::sync::OnceLock::new());
        }
        let mut worklist = std::collections::VecDeque::new();
        worklist.push_back(0usize);
        let mut primary_targets = std::collections::HashSet::new();
        primary_targets.insert(0usize);
        LazyLatticeTokenSource {
            input: owned,
            expander,
            nodes,
            secondary_alts,
            worklist_state: std::cell::RefCell::new(LazyWorklistState {
                byte_to_node: std::collections::BTreeMap::new(),
                worklist,
                primary_targets,
                eof_node_idx: None,
                allocated: 0,
                drained: false,
            }),
        }
    }

    /// Borrow the owned input.
    pub fn input(&self) -> &str {
        &self.input
    }

    /// Number of nodes materialized so far (the lazy SPACE metric:
    /// `lex_nodes_materialized`). Equals the eager DAG's node count only after
    /// the parser has driven the lazy source to full saturation.
    pub fn nodes_materialized(&self) -> usize {
        self.worklist_state.borrow().allocated
    }

    /// Force full materialization (drive the worklist to drain). Used by tests
    /// and the equivalence harness to compare the fully-expanded lazy DAG to
    /// the eager DAG node-by-node; NOT called on the parse hot path.
    pub fn force_full_materialization(&self) {
        while self.pump_one() {}
    }

    /// Pump the worklist one step: pop the next pending `start`, expand it, and
    /// materialize its node (assigning the next id). Returns `true` if a node
    /// was allocated, `false` if the worklist drained. Errors propagate the
    /// hard-fail (primary dead-end) surface, recorded by setting `drained` and
    /// stashing the message (the walker observes the resulting missing nodes as
    /// `peek_kind = None`, identical to how an eager hard-fail aborts the parse
    /// facade before the walker runs — see equivalence note below).
    fn pump_one(&self) -> bool {
        // Pop under a short borrow; release before calling the expander (which
        // must not hold the RefCell, and does not need it).
        let start = {
            let mut st = self.worklist_state.borrow_mut();
            if st.drained {
                return false;
            }
            loop {
                match st.worklist.pop_front() {
                    Some(s) => {
                        if st.byte_to_node.contains_key(&s) {
                            // Already allocated by a sibling enqueue — skip,
                            // exactly like the eager `continue`.
                            continue;
                        }
                        break s;
                    },
                    None => {
                        st.drained = true;
                        return false;
                    },
                }
            }
        };
        let start_is_primary = self
            .worklist_state
            .borrow()
            .primary_targets
            .contains(&start);
        let expanded = match (self.expander)(start, start_is_primary) {
            Ok(e) => e,
            Err(_msg) => {
                // M6c.7.1 hard-fail (primary dead-end). Eager `lex_dag_core`
                // returns `Err` here and the generated parse facade aborts
                // BEFORE constructing any token source / running the walker.
                // The lazy source is used in the same facade position, so a
                // hard-fail means "this input does not lex" — we mark the
                // source drained at the current frontier. The pre-frontier
                // nodes already materialized stay observationally identical;
                // the abandoned tail is exactly what eager would have refused
                // to produce. (The equivalence test drives lazy through the
                // walker directly and asserts identical accept/error verdicts.)
                self.worklist_state.borrow_mut().drained = true;
                return false;
            },
        };
        let mut st = self.worklist_state.borrow_mut();
        // Re-check: another nested pump (impossible here — single-threaded,
        // no re-entrancy) could have allocated `start`. Guard defensively.
        if st.byte_to_node.contains_key(&start) {
            return true;
        }
        let node_idx = st.allocated;
        st.byte_to_node.insert(start, node_idx);
        st.allocated += 1;

        if expanded.is_eof {
            if st.eof_node_idx.is_none() {
                st.eof_node_idx = Some(node_idx);
            }
            // Materialize an empty (EOF sentinel) node.
            let _ = self.nodes[node_idx].set(crate::lexer_types::LexDagNode {
                byte_start: expanded.byte_start,
                edges: Vec::new(),
            });
            return true;
        }

        // Build the node's resolved-on-demand edges (target_node = UNRESOLVED).
        let edges: Vec<crate::lexer_types::LexDagEdge> = expanded
            .edges
            .iter()
            .map(|e| crate::lexer_types::LexDagEdge {
                kind: e.kind.clone(),
                text: e.text.clone(),
                end_byte: e.end_byte,
                target_node: Self::UNRESOLVED,
                weight: e.weight,
                alt_idx: e.alt_idx,
            })
            .collect();
        let _ = self.nodes[node_idx]
            .set(crate::lexer_types::LexDagNode { byte_start: expanded.byte_start, edges });

        // Enqueue successors in edge order, applying the GLOBAL byte_to_node
        // dedup and M6c.7.1 primary propagation — identical to eager.
        for succ in expanded.successors.into_iter() {
            if !st.byte_to_node.contains_key(&succ.byte) {
                st.worklist.push_back(succ.byte);
                if succ.is_primary {
                    st.primary_targets.insert(succ.byte);
                }
            }
        }
        true
    }

    /// Pump the worklist until node id `idx` is materialized (or the worklist
    /// drains). After this returns, `self.nodes[idx]` is `Some` iff `idx` is a
    /// real node id of the eager DAG over the same input.
    fn ensure_node(&self, idx: usize) {
        loop {
            let allocated = self.worklist_state.borrow().allocated;
            if allocated > idx {
                return;
            }
            if !self.pump_one() {
                return;
            }
        }
    }

    /// Pump the worklist until the node at byte position `end_byte` is
    /// allocated (so its id is known), returning that id. Used to resolve an
    /// edge's `target_node` on demand. Returns `None` if the position is never
    /// allocated (worklist drained without reaching it).
    fn ensure_byte_allocated(&self, end_byte: usize) -> Option<usize> {
        loop {
            if let Some(&id) = self.worklist_state.borrow().byte_to_node.get(&end_byte) {
                return Some(id);
            }
            if !self.pump_one() {
                // Final check after the last pump.
                return self
                    .worklist_state
                    .borrow()
                    .byte_to_node
                    .get(&end_byte)
                    .copied();
            }
        }
    }

    /// Read a materialized node by id, materializing it first. Returns `None`
    /// for out-of-range / never-allocated ids (mirrors
    /// `LatticeTokenSource`'s `dag.nodes.get(pos)` returning `None`).
    fn node(&self, pos: usize) -> Option<&crate::lexer_types::LexDagNode> {
        self.ensure_node(pos);
        self.nodes.get(pos)?.get()
    }

    /// Lazily materialize and cache the secondary-alt slice for node `pos`
    /// (edges beyond the primary), mirroring
    /// `LatticeTokenSource::secondary_alts_for`.
    fn secondary_alts_for(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        // Materialize the node first (separate borrow that ends before the
        // OnceLock init closure runs).
        let node_exists = self.node(pos).is_some();
        let Some(cell) = self.secondary_alts.get(pos) else {
            return &[];
        };
        if !node_exists {
            return &[];
        }
        cell.get_or_init(|| {
            self.nodes
                .get(pos)
                .and_then(|n| n.get())
                .map(|node| {
                    node.edges
                        .iter()
                        .skip(1)
                        .map(|e| crate::lexer_types::LexAlternative {
                            kind: e.kind.clone(),
                            text: e.text.clone(),
                            end_byte: e.end_byte,
                            weight: e.weight,
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .as_slice()
    }

    /// Returns the target node of edge `alt_idx` (0 = primary; 1+ =
    /// secondaries) from node `pos`, resolving it on demand via `byte_to_node`.
    /// Symmetric with `LatticeTokenSource::target_node`.
    pub fn target_node(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        let end_byte = {
            let node = self.node(pos)?;
            node.edges.get(alt_idx)?.end_byte
        };
        self.ensure_byte_allocated(end_byte)
    }
}

impl WpdaTokenSource for LazyLatticeTokenSource {
    fn peek_kind(&self, pos: usize) -> Option<TokenKind> {
        let node = self.node(pos)?;
        Some(
            node.edges
                .first()
                .map(|edge| edge.kind.clone())
                .unwrap_or(TokenKind::Eof),
        )
    }

    fn peek_text(&self, pos: usize) -> Option<&str> {
        let node = self.node(pos)?;
        Some(
            node.edges
                .first()
                .map(|edge| edge.text.as_str())
                .unwrap_or(""),
        )
    }

    fn len(&self) -> usize {
        // The eager `LatticeTokenSource::len()` returns the FULL node count
        // (`dag.nodes.len()`), and — crucially — GENERATED lookahead scans rely
        // on this. In particular `prefix_crosscat_lhs_trigger_ahead`
        // (codegen, the cross-cat-LHS cast disambiguator) scans
        // `for i in pos+1 .. tokens.len()` looking ahead for a comparison
        // trigger (e.g. `==` in `int(3) == 3`); if `len()` under-reports, the
        // scan stops early, the cast branch is never taken, and the parse
        // diverges (e.g. `int` collapses to a bare `PVar`). So `len()` MUST
        // equal the eager full node count.
        //
        // Lazy therefore fully materializes the DAG here (memoized — the
        // worklist drains exactly once; subsequent calls are O(1)). This is the
        // unavoidable cost of observational equivalence for any `len()`-bounded
        // consumer: a sound `len()` requires knowing every node. The full lex
        // is linear in the input (the cheap part of parsing — see the
        // "Phase 2L STOP by measurement" verdict), so this is bounded; what
        // STILL stays lazy is every parse that the walker abandons BEFORE any
        // `len()`-bounded scan runs (the cast disambiguator only fires at a
        // cross-cat-LHS keyword such as `int`/`float`; inputs whose prefix
        // never hits one — and whose deterministic frontier never parks at a
        // `pos >= len()` check — never trigger this drain).
        self.force_full_materialization();
        self.worklist_state.borrow().allocated
    }

    fn peek_alternatives(&self, pos: usize) -> &[crate::lexer_types::LexAlternative] {
        self.secondary_alts_for(pos)
    }

    fn is_ambiguous_at(&self, pos: usize) -> bool {
        self.node(pos).map(|n| n.edges.len() > 1).unwrap_or(false)
    }

    fn end_byte(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        let node = self.node(pos)?;
        node.edges.get(alt_idx).map(|e| e.end_byte)
    }

    /// M3 semantics: the next NODE INDEX after consuming edge `alt_idx` from
    /// node `pos`. Lazy resolves the successor on demand via `byte_to_node`.
    fn next_pos(&self, pos: usize, alt_idx: usize) -> Option<usize> {
        self.target_node(pos, alt_idx)
    }

    fn positions_are_linear_tokens(&self) -> bool {
        false
    }

    fn position_order_key(&self, pos: usize) -> Option<usize> {
        self.node(pos).map(|node| node.byte_start)
    }

    /// M6c.8.2: the canonical EOF sentinel node id.
    ///
    /// Eager returns `dag.eof_node` directly. Lazy discovers the EOF id when
    /// the worklist first allocates a node at `byte_start == input.len()`. The
    /// walker reaches EOI only by advancing (`next_pos`) along the primary
    /// chain to that node, so by the time a cursor's `pos` could equal the EOF
    /// id, that node has been materialized and `eof_node_idx` is set. Until
    /// then we return [`Self::UNRESOLVED`] (`usize::MAX`), which never equals a
    /// reached `pos` — so `pos == eof_node()` is correctly `false` for cursors
    /// not yet at EOF, identical to eager. (We do NOT eagerly walk the primary
    /// chain to EOF here: that would defeat the space savings on early-failure
    /// inputs, where the cursor never approaches EOF.)
    fn eof_node(&self) -> usize {
        self.worklist_state
            .borrow()
            .eof_node_idx
            .unwrap_or(Self::UNRESOLVED)
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
    /// A reconstructed collection occurrence with all selected items intact.
    /// Remapped to a fresh action-local slot immediately before invocation.
    SelectedCollection(SelectedCollection),
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
    /// L9-4: a fully-assembled FLT guest body, produced by the walker's
    /// `ConsumeGuestBody*` action (which scans opener → GuestChunk/Hole run →
    /// closer, using the verbatim `source_slice` for `body_src` — No-Injection).
    /// Carries PRIMITIVES ([`GuestBodyData`]) — prattail's lib does NOT depend
    /// on `runtime`, so it cannot name `FltNode`; the generated `PFlt`-style
    /// action reads this via [`ActionArg::as_guest_body`] and builds the
    /// `Arc<FltNode>` variant field itself.
    GuestBody(Arc<GuestBodyData>),
    /// #74 (2026-07-29): the value slot of a **value-optional** kv-collection
    /// entry that the source left EMPTY — the `{| k |}` shape, where the key is
    /// present and bound to nothing.
    ///
    /// This variant occurs ONLY inside a collection accumulator, at an odd
    /// (value) index of a `kv_value_optional` slot. It is produced by
    /// [`crate::wpda_walker::BuilderDelta::PushUnsetCollectionValue`] at parse
    /// time and by the UNSET-marker arm of the realize-side collection-item loop.
    ///
    /// ⚠ It is deliberately NOT an `ActionArg::Term`: the generated finalize
    /// action must be unable to mistake it for a value the user wrote. It has no
    /// `into_term` and no downcast — the only thing an action can do with it is
    /// recognise it and select homogeneous set mode for the collection.
    ///
    /// Before this variant existed, a bare entry was materialised by
    /// *duplicating the key into the value slot*, which destroyed the
    /// distinction inside the SPPF before any action could see it. See
    /// `runtime/src/pathmap_lit.rs` for the homogeneous representation.
    UnsetCollectionValue,
}

#[path = "wpda_runtime/action_arg_lifecycle.rs"]
mod action_arg_lifecycle;

#[path = "wpda_runtime/action_collection_frame.rs"]
mod action_collection_frame;
pub use action_collection_frame::{ActionInvocationError, SelectedCollection};

#[path = "wpda_runtime/realization_error.rs"]
mod realization_error;
pub use realization_error::{RealizationError, ReconstructionFailure};

#[path = "wpda_runtime/cartesian_cursor.rs"]
mod cartesian_cursor;
pub(crate) use cartesian_cursor::CartesianCursor;

/// #151 (2026-07-29): why a collection flat was refused at the close.
///
/// The walker's `CollectionMarker` close is the single point at which a flat
/// becomes a `CollectionId` — "the only place flats become CollectionIds". Every
/// gate at that site now returns one of these values instead of falling out of a
/// bare `continue`, so the refusal carries its reason and the resolver can render
/// a diagnostic instead of whatever generic error the dying frontier last
/// produced.
///
/// The `kv` flag on [`FlatDisposition::ArityUncovered`] records which item law
/// was applied. The separator policy comes from the collection specification:
///
/// ```text
/// explicit separator, non-kv: items == seps + 1
/// explicit separator, kv:     items even ∧ items == 2·(seps + 1)
/// epsilon separator, non-kv:  seps == 0
/// epsilon separator, kv:      seps == 0 ∧ items even
/// ```
///
/// A key/value separator such as `:` is not an entry separator and therefore
/// never contributes a separator witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlatDisposition {
    /// The flat is a well-formed reading of this collection slot.
    Accepted,
    /// The item/separator counts do not satisfy the slot's arity law.
    ArityUncovered {
        items: usize,
        seps: usize,
        /// `true` when the kv law was applied (the slot carries a `kv_sep`).
        kv: bool,
    },
    /// An item's category tag is not the slot's declared element category. This
    /// is a raw cross-category inner `Symbol` spliced pre-wrap: the finalize
    /// action's downcast would map it to ∅ and silently emit a SHORTER container
    /// — the sub-multiset ghost. Refused at the source instead.
    CrossCategory {
        /// Index into the flat's `items` (kv flats: even = key, odd = value).
        index: usize,
        /// The slot's declared element category `src_idx`.
        expected_src_idx: u16,
        /// The offending item's category tag.
        found_tag: u32,
    },
    /// An UNSET marker landed in a KEY slot (an even index of a kv flat). A key
    /// is never optional in any container kind.
    UnsetInKeySlot { index: usize },
    /// An UNSET marker landed in a value slot of a container whose values are
    /// MANDATORY (`HashMap`; `kv_value_optional == false`).
    UnsetValueForbidden { index: usize },
}

impl FlatDisposition {
    /// `true` when the flat may be interned as a `CollectionId`.
    #[inline]
    pub fn is_accepted(&self) -> bool {
        matches!(self, FlatDisposition::Accepted)
    }
}

/// Decide whether a flattened collection has a complete item/separator shape.
///
/// Concrete entry separators are represented by one witness between adjacent
/// entries. An epsilon entry separator consumes no token and emits no witness,
/// so its proof obligation is instead that no separator witness exists. A
/// key/value collection additionally requires an even item count because each
/// logical entry contains exactly one key and one value.
pub(crate) fn collection_arity_is_covered(
    items: usize,
    separator_witnesses: usize,
    is_kv: bool,
    separator_is_epsilon: bool,
) -> bool {
    if separator_is_epsilon {
        separator_witnesses == 0 && (!is_kv || items.is_multiple_of(2))
    } else if items == 0 && separator_witnesses == 0 {
        true
    } else if is_kv {
        items.is_multiple_of(2)
            && separator_witnesses
                .checked_add(1)
                .and_then(|entries| entries.checked_mul(2))
                == Some(items)
    } else {
        separator_witnesses.checked_add(1) == Some(items)
    }
}

/// The mismatch an [`ActionArg`] downcast rejected, preserved instead of
/// discarded.
///
/// [`ActionArg::into_term`] returns a bare `Option`, which loses *why* the
/// downcast failed. The generated collection-finalize actions used to convert
/// that `None` into "skip this element", which is precisely how a reading that is
/// not in the language became "an accepted, shorter container". They now abandon
/// the whole term instead, and this struct names what went wrong so the abandon
/// is a measurement rather than a silence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionArgMismatch {
    /// `std::any::type_name::<T>()` for the type the caller asked for.
    pub requested: &'static str,
    /// The arg's own `type_name` tag, or its variant name for non-`Term` args.
    pub found: &'static str,
}

/// Process-global census of collection-finalize actions that abandoned a term
/// because an element failed to downcast.
///
/// The walker's close-time classifier is supposed to have refuted every such flat
/// already, so this counter is an INVARIANT WITNESS: a test asserts it stays `0`
/// across the matrix. It is a counter rather than a `panic!` because the
/// generated actions run inside cranelift-compiled parse workers where a panic is
/// not an available failure mode; `debug_assert!` carries the invariant in debug
/// builds and this counter carries it in release.
pub static COLL_ACTION_DOWNCAST_ABANDON: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Record one collection-finalize abandon (see [`COLL_ACTION_DOWNCAST_ABANDON`]).
#[inline]
pub fn note_coll_action_downcast_abandon() {
    COLL_ACTION_DOWNCAST_ABANDON.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Read the abandon census (see [`COLL_ACTION_DOWNCAST_ABANDON`]).
#[inline]
pub fn coll_action_downcast_abandon_count() -> u64 {
    COLL_ACTION_DOWNCAST_ABANDON.load(std::sync::atomic::Ordering::Relaxed)
}

/// Reset the abandon census to `0` (test scaffolding).
#[inline]
pub fn reset_coll_action_downcast_abandon() {
    COLL_ACTION_DOWNCAST_ABANDON.store(0, std::sync::atomic::Ordering::Relaxed);
}

/// L9-4: the primitive contents of an assembled FLT guest body, carried by
/// [`ActionArg::GuestBody`]. The generated action lowers this to a
/// `mettail_runtime::FltNode` (a 1:1 field map — `holes` → `FltHole`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuestBodyData {
    /// Explicit lexical handle reference before the category separator.
    pub selector_name: String,
    /// Explicit result category before the delimiter.
    pub category: String,
    /// The exact opener token text. This is retained independently from `tag`
    /// so generalized, structurally delimited host forms can preserve their
    /// complete header without reconstructing it from semantic fields.
    pub open_src: String,
    /// The verbatim guest-body source `source_slice(open.end, close.start)`.
    pub body_src: String,
    /// The `${…}` telescope, in first-occurrence order.
    pub holes: Vec<GuestBodyHole>,
    /// Ordered guest-text and hole terminals. This, not `body_src`, is the
    /// parser input for structural FLTs.
    pub pieces: Vec<GuestBodyPiece>,
    /// The exact closer token text.
    pub close_src: String,
    /// The opener's start position in the original source.
    pub position: usize,
}

/// L9-4: one `${name}` / `${name:Cat}` hole (see [`GuestBodyData`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuestBodyHole {
    pub id: u32,
    pub name: String,
    pub category: Option<String>,
    pub first_occurrence: GuestBodySourceRange,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GuestBodyPiece {
    Text {
        text: String,
        range: GuestBodySourceRange,
    },
    Hole {
        id: u32,
        range: GuestBodySourceRange,
    },
}

/// Half-open byte range relative to the beginning of `body_src`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GuestBodySourceRange {
    pub start: usize,
    pub end: usize,
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
            ActionArg::SelectedCollection(selected) => f
                .debug_struct("SelectedCollection")
                .field("len", &selected.items().len())
                .finish(),
            ActionArg::Predicate(_) => f.debug_struct("Predicate").finish(),
            ActionArg::Optional(Some(args)) => f
                .debug_struct("Optional")
                .field("present", &true)
                .field("len", &args.len())
                .finish(),
            ActionArg::Optional(None) => {
                f.debug_struct("Optional").field("present", &false).finish()
            },
            ActionArg::GuestBody(node) => f
                .debug_struct("GuestBody")
                .field("selector_name", &node.selector_name)
                .field("category", &node.category)
                .field("body_src", &node.body_src)
                .field("holes", &node.holes.len())
                .finish(),
            ActionArg::UnsetCollectionValue => f.write_str("UnsetCollectionValue"),
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
    /// L9-4: extract an assembled FLT guest body's primitive [`GuestBodyData`].
    pub fn as_guest_body(&self) -> Option<&GuestBodyData> {
        match self {
            ActionArg::GuestBody(data) => Some(data),
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
        self.try_into_term().ok()
    }

    /// The reason-preserving sibling of [`ActionArg::into_term`].
    ///
    /// #151 (2026-07-29): the generated collection-finalize actions switched to
    /// this form so that an element which does not downcast ABANDONS the whole
    /// term (naming the mismatch) instead of being filtered out of the container.
    /// A `filter_map(into_term)` is the machinery that turns "this reading is not
    /// in the language" into "an accepted, shorter container" — the sub-multiset
    /// ghost. `into_term` is retained verbatim as `try_into_term().ok()` so its
    /// existing callers are untouched.
    pub fn try_into_term<T: 'static + Send + Sync + Clone>(self) -> Result<T, ActionArgMismatch> {
        let requested = std::any::type_name::<T>();
        match self.into_term_parts() {
            Ok((value, type_name)) => match Arc::downcast::<T>(value) {
                Ok(arc) => Ok(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => Err(ActionArgMismatch { requested, found: type_name }),
            },
            Err(other) => Err(ActionArgMismatch { requested, found: other.variant_name() }),
        }
    }

    /// Convert an ordered collection without dropping a mismatched element.
    ///
    /// Success preserves every occurrence and its position. Failure returns
    /// the first mismatch and publishes no partially converted collection.
    /// The loop refines `convert_all` in `OccurrenceCollectionAssembly.v`.
    pub fn try_into_terms<T: 'static + Send + Sync + Clone>(
        args: Vec<Self>,
    ) -> Result<Vec<T>, ActionArgMismatch> {
        let mut terms = Vec::with_capacity(args.len());
        for arg in args {
            terms.push(arg.try_into_term::<T>()?);
        }
        Ok(terms)
    }

    /// The arg's variant name, for [`ActionArgMismatch::found`] on non-`Term`
    /// args (whose `type_name` tag does not exist).
    pub fn variant_name(&self) -> &'static str {
        match self {
            ActionArg::Token { .. } => "ActionArg::Token",
            ActionArg::Ident { .. } => "ActionArg::Ident",
            ActionArg::Term { .. } => "ActionArg::Term",
            ActionArg::BinderScope(_) => "ActionArg::BinderScope",
            ActionArg::Collection { .. } => "ActionArg::Collection",
            ActionArg::CollectionId(_) => "ActionArg::CollectionId",
            ActionArg::SelectedCollection(_) => "ActionArg::SelectedCollection",
            ActionArg::Predicate(_) => "ActionArg::Predicate",
            ActionArg::Optional(_) => "ActionArg::Optional",
            ActionArg::GuestBody(_) => "ActionArg::GuestBody",
            ActionArg::UnsetCollectionValue => "ActionArg::UnsetCollectionValue",
        }
    }

    /// #74: `true` for the value slot of a bare `{| k |}` entry.
    #[inline]
    pub fn is_unset_collection_value(&self) -> bool {
        matches!(self, ActionArg::UnsetCollectionValue)
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
        self.into_dyn_term()
            .and_then(|value| Arc::downcast::<T>(value).ok())
    }

    /// Consume a `Term` argument without downcasting its type-erased payload.
    ///
    /// This crate-internal form lets realization and result-extraction paths
    /// move the `Arc` out while [`ActionArg`]'s explicit iterative destructor
    /// remains responsible for every non-matching variant.
    pub(crate) fn into_dyn_term(self) -> Option<Arc<dyn Any + Send + Sync>> {
        self.into_term_parts().ok().map(|(value, _)| value)
    }
    /// Borrow the BinderScope handle.
    pub fn as_binder_scope(&self) -> Option<&BinderHandle> {
        match self {
            ActionArg::BinderScope(h) => Some(h),
            _ => None,
        }
    }
    /// Consume a `BinderScope` argument without cloning its handle.
    ///
    /// `ActionArg` has an explicit iterative destructor, so callers must use this accessor
    /// instead of destructuring the enum by value.
    pub fn into_binder_scope(self) -> Option<BinderHandle> {
        self.into_binder_scope_value().ok()
    }
    /// Consume an `Ident` argument and move out its name.
    pub fn into_ident_name(self) -> Option<String> {
        self.into_ident_name_value().ok()
    }
    /// Consume this `Collection` arg and downcast to `T`.
    ///
    /// Stage 3.6 / ι Phase 1 (2026-05-01): see `into_term` for Arc/Clone
    /// rationale.
    pub fn into_collection<T: 'static + Send + Sync + Clone>(self) -> Option<T> {
        match self.into_collection_parts() {
            Ok(value) => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            Err(_) => None,
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
        match self.into_predicate_value() {
            Ok(value) => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            Err(_) => None,
        }
    }
    /// Opt-Group: consume this `Optional` arg, returning the inner
    /// `Option<Vec<ActionArg>>` for the action body to destructure.
    /// Returns `None` if the arg is not an `Optional` variant
    /// (mismatched action arity / kind would be a codegen bug).
    pub fn into_optional(self) -> Option<Option<Vec<ActionArg>>> {
        self.into_optional_value().ok()
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
    /// Reconstruction-only indexed slots. Absent during ordinary parsing;
    /// its collection stack and cursor sharing remain unchanged.
    action_collections: Option<Box<action_collection_frame::ActionCollectionFrame>>,
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
            action_collections: None,
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
        match self.stack.pop_back()?.into_dyn_term() {
            Some(value) => match Arc::downcast::<T>(value) {
                Ok(arc) => Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())),
                Err(_) => None,
            },
            None => None,
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
        self.stack.pop_back()?.into_dyn_term()
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
        if let Some(frame) = self.action_collections.as_mut() {
            return frame.drain(id);
        }
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

#[inline]
pub fn lex_w(
    cost: f64,
    src_idx: u16,
    rule_idx: u16,
) -> crate::automata::lex_weight::LexicographicWeight {
    crate::automata::lex_weight::LexicographicWeight::from_cost(cost, src_idx, rule_idx)
}

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

#[inline]
pub fn lex_w_with_len(
    open_len: u16,
    cost: f64,
    src_idx: u16,
    rule_idx: u16,
) -> crate::automata::lex_weight::LexicographicWeight {
    crate::automata::lex_weight::LexicographicWeight::from_cost(cost, src_idx, rule_idx)
        .with_open_len(open_len)
}

#[inline]
pub fn lex_w_alt_with_len(
    open_len: u16,
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
    .with_open_len(open_len)
}

#[inline]
pub fn lex_one() -> crate::automata::lex_weight::LexicographicWeight {
    use crate::automata::semiring::Semiring;
    crate::automata::lex_weight::LexicographicWeight::one()
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
    use crate::automata::semiring::{Semiring, TropicalWeight};
    use crate::lexer_types::{LexAlternative, LexEntry, LexStream};

    fn collection_test_term<T: 'static + Send + Sync>(value: T) -> ActionArg {
        ActionArg::Term {
            value: Arc::new(value),
            type_name: std::any::type_name::<T>(),
        }
    }

    #[test]
    fn exact_collection_conversion_preserves_order_and_repeated_occurrences() {
        let shared = collection_test_term(7_i32);
        let args = vec![shared.clone(), collection_test_term(3_i32), shared];
        assert_eq!(ActionArg::try_into_terms::<i32>(args), Ok(vec![7, 3, 7]));
        assert_eq!(ActionArg::try_into_terms::<i32>(Vec::new()), Ok(Vec::new()));
    }

    #[test]
    fn exact_collection_conversion_rejects_a_mismatch_at_every_position() {
        for position in 0..=2 {
            let mut args = vec![collection_test_term(1_i32), collection_test_term(2_i32)];
            args.insert(position, collection_test_term(String::from("wrong category")));
            assert_eq!(
                ActionArg::try_into_terms::<i32>(args),
                Err(ActionArgMismatch {
                    requested: std::any::type_name::<i32>(),
                    found: std::any::type_name::<String>(),
                }),
            );
        }
    }

    #[test]
    fn exact_collection_conversion_rejects_nonterms_and_forged_type_tags() {
        let unset = vec![collection_test_term(1_i32), ActionArg::UnsetCollectionValue];
        assert!(ActionArg::try_into_terms::<i32>(unset).is_err());
        let forged = vec![ActionArg::Term {
            value: Arc::new(String::from("not an integer")),
            type_name: std::any::type_name::<i32>(),
        }];
        assert!(ActionArg::try_into_terms::<i32>(forged).is_err());
    }

    #[test]
    fn explicit_separator_collection_arity_requires_one_witness_between_entries() {
        assert!(collection_arity_is_covered(0, 0, false, false));
        assert!(collection_arity_is_covered(1, 0, false, false));
        assert!(collection_arity_is_covered(3, 2, false, false));
        assert!(!collection_arity_is_covered(2, 0, false, false));

        assert!(collection_arity_is_covered(0, 0, true, false));
        assert!(collection_arity_is_covered(2, 0, true, false));
        assert!(collection_arity_is_covered(6, 2, true, false));
        assert!(!collection_arity_is_covered(3, 0, true, false));
        assert!(!collection_arity_is_covered(4, 0, true, false));
    }

    #[test]
    fn epsilon_separator_collection_arity_uses_no_separator_witnesses() {
        for items in 0..=8 {
            assert!(collection_arity_is_covered(items, 0, false, true));
            assert_eq!(collection_arity_is_covered(items, 0, true, true), items % 2 == 0,);
        }
        assert!(!collection_arity_is_covered(2, 1, false, true));
        assert!(!collection_arity_is_covered(2, 1, true, true));
    }

    #[test]
    fn collection_arity_rejects_overflowed_witness_counts() {
        assert!(!collection_arity_is_covered(1, usize::MAX, false, false));
        assert!(!collection_arity_is_covered(2, usize::MAX, true, false));
    }

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
        // The str-cast collection-infix fix (2026-06-18) added the
        // `continuation_bp: Option<u8>` carrier (the Pratt dispatch bp at which
        // a finalized Class-5 collection resumes InfixLoop), taking the struct
        // from 8 to 10 bytes.
        //
        // GEN-1 goal-gate G0 (2026-06-28) added `goal_src_idx: Option<u16>`
        // (the cross-cat operand/element goal category). `Option<u16>` has no
        // niche (all u16 bit patterns are valid), so it occupies 4 bytes
        // (1 discriminant byte + 1 pad + 2 payload, struct align 2), taking the
        // struct from 10 to 14 bytes. The growth is the deliberate cost of
        // threading the goal onto the GSS symbol (mirrors the `continuation_bp`
        // precedent); it is `None` for every non-strict symbol so GSS identity
        // is preserved. Assert it does not regress beyond 14 bytes.
        // (Actual size depends on enum layout; assert it stays small.)
        let actual = std::mem::size_of::<StackSymbolV2>();
        assert!(actual <= 14, "StackSymbolV2 grew to {actual} bytes");
    }

    #[test]
    fn traversal_markers_round_trip_dense_ids_without_growing_the_symbol() {
        let marker_id = 0xA17E_C35Du32;
        let optional = StackSymbolV2::optional_group_at(marker_id, 37);
        let binder = StackSymbolV2::binder_list_loop_at(marker_id, 37);

        assert_eq!(optional.traversal_marker_id(), Some(marker_id));
        assert_eq!(binder.traversal_marker_id(), Some(marker_id));
        assert_eq!(optional.category_src_idx, 0xA17E);
        assert_eq!(optional.rule_index_in_category, 0xC35D);
        assert_eq!(optional.bp, Some(37));
        assert_eq!(binder.bp, Some(37));
        assert_ne!(optional, binder, "typed marker kinds must remain disjoint");
        assert_eq!(std::mem::size_of_val(&optional), std::mem::size_of::<StackSymbolV2>());
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
    fn lattice_source_materializes_secondary_alts_on_demand() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        assert_eq!(src.materialized_secondary_alt_nodes(), 0);

        assert!(matches!(src.peek_kind(0), Some(TokenKind::Integer)));
        assert_eq!(src.peek_text(0), Some("-3"));
        assert_eq!(
            src.materialized_secondary_alt_nodes(),
            0,
            "primary observations must not force secondary alternatives"
        );

        {
            let alts = src.peek_alternatives(0);
            assert_eq!(alts.len(), 1);
            assert!(matches!(alts[0].kind, TokenKind::Fixed(ref s) if s == "-"));
        }
        assert_eq!(src.materialized_secondary_alt_nodes(), 1);
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
    fn lattice_source_position_order_key_uses_byte_start_not_node_id() {
        let src = LatticeTokenSource::new(make_minus3_dag());
        let primary_target = src.next_pos(0, 0).expect("primary edge must exist");
        let secondary_target = src.next_pos(0, 1).expect("secondary edge must exist");

        assert_eq!(src.position_order_key(primary_target), Some(2));
        assert_eq!(src.position_order_key(secondary_target), Some(1));
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
