use crate::automata::semiring::SemiringRef;
use crate::gss::WpdaGssNode;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::WpdaStepAction;

/// Original non-atomic prefix query; later readers run only after earlier
/// evidence fails. The table callbacks are not assumed pure.
pub fn prefix_token_has_non_atom_start(
    cat_src_idx: u16,
    kind: &crate::automata::TokenKind,
    lex_alt_rules_for_prefix: impl FnOnce(
        u16,
        &crate::automata::TokenKind,
    ) -> Vec<crate::wpda_runtime::LexAltRuleInfo>,
    prefix_primary_has_non_atom_dispatch_rule: impl FnOnce(u16, &crate::automata::TokenKind) -> bool,
    prefix_crosscat_lhs_has_dispatch_rule: impl FnOnce(u16, &crate::automata::TokenKind) -> bool,
) -> bool {
    lex_alt_rules_for_prefix(cat_src_idx, kind)
        .into_iter()
        .any(|info| !matches!(info.kind, crate::wpda_runtime::LexAltRuleKind::Atomic))
        || prefix_primary_has_non_atom_dispatch_rule(cat_src_idx, kind)
        || prefix_crosscat_lhs_has_dispatch_rule(cat_src_idx, kind)
}

/// Original operator-table query shared by grouping continuation and the walker.
pub fn operator_recognized<'a>(
    infix: impl FnOnce() -> &'a [(u8, u8, u16, u16)],
    postfix: impl FnOnce() -> &'a [(u8, u16, u16)],
    mixfix: impl FnOnce() -> &'a [(u8, u16, u16)],
) -> bool {
    !infix().is_empty() || !postfix().is_empty() || !mixfix().is_empty()
}

/// Original per-category Pratt-floor query, with lazy table observations.
pub fn operator_at_floor<'a>(
    floor: u8,
    infix: impl FnOnce() -> &'a [(u8, u8, u16, u16)],
    postfix: impl FnOnce() -> &'a [(u8, u16, u16)],
    mixfix: impl FnOnce() -> &'a [(u8, u16, u16)],
) -> bool {
    infix().iter().any(|&(left_bp, ..)| left_bp >= floor)
        || postfix().iter().any(|&(left_bp, ..)| left_bp >= floor)
        || mixfix().iter().any(|&(left_bp, ..)| left_bp >= floor)
}

#[allow(clippy::too_many_arguments)]
pub fn ready<W: SemiringRef>(
    primary_src_idx: u16,
    min_bp: &u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    let primary = StackSymbolV2::category_entry(primary_src_idx);
    WpdaStepAction::Push {
        symbol: primary,
        weight: lex_w(0.0, primary_src_idx, 0),
        new_state: WpdaState::PrefixDispatch { pos: 0, cur_bp: *min_bp },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn infix_chain_iterative<W: SemiringRef>(rhs_bp: &u8, _pos: usize) -> WpdaStepAction<W> {
    // Phase F.13 chain_10000 Exp 6 Substage 6b
    // (2026-05-26): dispatch the RHS sub-parse at
    // `cur_bp: rhs_bp` per Plan A invariant I3.
    //
    // STRUCTURAL NOTE (Substage 6b implementation
    // judgment): the user's plan suggested a
    // chain-continuation probe here that peeks the
    // NEXT token for another iterative-eligible
    // operator. That probe would fire BEFORE the
    // RHS is parsed (the next token after `+` is
    // the RHS literal `2`, not another `+`), so
    // the probe always yields zero candidates and
    // the RHS would never be dispatched — the
    // chain would terminate after the first
    // iteration. The structurally-correct flow is:
    //
    //   1. InfixLoop singleton emits
    //      `IterativeChainAbsorb` (this commit's
    //      step 2 change).
    //   2. Walker consumes `+`, pushes Return
    //      RuleAt on first iteration (elides on
    //      subsequent iterations per invariant I2),
    //      sets state = `InfixChainIterative`.
    //   3. THIS ARM dispatches RHS sub-parse via
    //      `PrefixDispatch { cur_bp: rhs_bp }`.
    //   4. RHS completes; Unwinding-Return pops
    //      the Return symbol → InfixLoop {
    //      cur_bp: outer_bp } via the standard
    //      Return-pop path (engine_impl.rs:457-464).
    //   5. InfixLoop re-enters; singleton
    //      fast-path re-detects iterative-
    //      eligible operator and emits
    //      IterativeChainAbsorb — walker's chain-
    //      extension elision (invariant I2)
    //      avoids the second push.
    //
    // Per-chain GSS-push elision is the entire
    // win: O(N) chain steps → O(1) Return frames.
    // Action fires once on chain terminate via the
    // standard Unwinding-Return → Pop path with
    // all accumulated RHS SPPF nodes attached.
    WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: _pos, cur_bp: *rhs_bp })
}

#[allow(clippy::too_many_arguments)]
pub fn collection_open_paren<W: SemiringRef>(
    result_src_idx: &u16,
    rule_idx: &u16,
    element_src_idx: &u16,
    outer_bp: &u8,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    // B7: 2-token open delimiter — the prefix arm
    // already consumed `list` (or `bag` / `map`) and
    // pushed the CollectionMarker. Demand `(` next,
    // consume it, and transition to PrefixDispatch
    // with the CollectionMarker still on top.
    // PrefixDispatch then handles three sub-cases:
    //   (a) empty-collection — peek == close delim →
    //       ConsumeAndPop (existing close_lookup path);
    //   (b) cross-cat element (result_src ≠ element_src)
    //       → Push CategoryEntry(element_src) and
    //       recurse PrefixDispatch (handled in
    //       PrefixDispatch's CollectionMarker branch);
    //   (c) self-collection — fall through to normal
    //       per-category prefix dispatch.
    let _ = (result_src_idx, rule_idx, element_src_idx, outer_bp);
    match tokens.peek_text(_pos) {
        Some("(") => WpdaStepAction::Consume {
            weight: lex_one(),
            new_state: WpdaState::PrefixDispatch {
                pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                cur_bp: 0,
            },
        },
        other => WpdaStepAction::Error(format!(
            "expected `(` after collection-open keyword at pos {}, found {:?}",
            _pos, other
        )),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn cross_category_delegate<W: SemiringRef>(
    source_src_idx: &u16,
    inner_cur_bp: &u8,
    _pos: usize,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    // Stage 1.1: cross-cat projection delegation.
    // Push a CategoryEntry for the source category;
    // PrefixDispatch will route the engine to source's
    // rules. After source parses + its Return pops +
    // its action fires (pushing source Term to
    // builder), the cross-cat Return (already on the
    // stack below the source CategoryEntry) becomes
    // top → its wrap-action fires, wrapping the
    // source Term as `Cat::Wrapper(Box::new(t))`.
    //
    // D-strings fix (2026-05-13): use `*inner_cur_bp`
    // (set by the emission site) as the sub-parse's
    // cur_bp, NOT a hardcoded 0. For cross-cat infix
    // RHS dispatch (`engine_impl.rs:920-925`), the
    // emitter passes `r_bp` so the sub-parse rejects
    // lower-precedence operators leaking in from the
    // enclosing Pratt context. For PrefixDispatch
    // CrossCatProjection/ImplicitCast/CrossCatPrefixUnary
    // arms, the emitter passes the active operand-context
    // floor. The outer cur_bp is restored via the
    // wrapping `Return(..., bp=Some(outer_cur_bp))`
    // symbol when that Return is later popped, not via
    // this state.
    WpdaStepAction::Push {
        symbol: StackSymbolV2::category_entry(*source_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: *inner_cur_bp },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn grouping_close<W: SemiringRef>(
    inner_cat_src_idx: &u16,
    frontier_top: Option<&WpdaGssNode>,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    // Plan A (paren+postfix redesign, 2026-05-11):
    // top is now the GroupingMarker (the inner CategoryEntry
    // was just popped via the Unwinding-CategoryEntry
    // lookahead-conditional branch). Demand `)`,
    // ConsumeAndReplace the GroupingMarker on top with
    // a CategoryEntry of the inner cat so subsequent
    // InfixLoop dispatch uses the inner-cat tables.
    //
    // The GroupingMarker's `bp` field carries outer_bp
    // (saved cur_bp at the open paren — established by
    // the codegen invariant in StackSymbolV2::grouping_marker).
    // Restore that BP for the post-`)` InfixLoop.
    if let Some(node) = frontier_top {
        if node.symbol.kind == crate::wpda_runtime::SymbolKind::GroupingMarker {
            let outer_bp = node.symbol.bp.expect(
                "GroupingMarker invariant: bp must be Some(outer_bp) — \
                 saved cur_bp at the open paren",
            );
            return match tokens.peek_text(_pos) {
                Some(")") => WpdaStepAction::ConsumeAndReplace {
                    symbol: StackSymbolV2::category_entry(*inner_cat_src_idx),
                    weight: lex_one(),
                    new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
                },
                other => WpdaStepAction::Error(format!(
                    "GroupingClosePreservingInner: expected `)` to close \
                     grouping (preserving inner cat={}) at pos {}, found {:?}",
                    inner_cat_src_idx, _pos, other,
                )),
            };
        }
    }
    WpdaStepAction::Error(format!(
        "GroupingClosePreservingInner: expected GroupingMarker on top at \
         pos {}, found {:?}",
        _pos,
        frontier_top.map(|n| n.symbol.kind),
    ))
}
