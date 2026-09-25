//! Original prefix transition bodies available to generated and owned engines.
//! Static pattern dispatch, factoring gates, and branch order remain at callers.
//!
//! Source correspondence: `macros/src/gen/runtime/wpda_codegen/prefix.rs` at
//! `fb0fbed5`, under the original emission gates:
//! - `emit_paren_dispatch_arms`: singleton grouping, grouping/binder branch
//!   construction, and the ordered fork wrapper become the four `paren_*` bodies.
//! - `emit_unified_arm`: the eight non-atomic singleton bodies and nine descriptor
//!   branch bodies become `singleton_*` and `push_*`; its fork wrapper becomes
//!   `unified_fork`. `GroupFirst`/`GroupRest` and ordinal collection stay in codegen.
//! - `emit_atomic_arm_singleton`: the atomic body becomes `singleton_atomic`.
//!
//! Descriptor constants retain their original bindings. Weight callbacks run at
//! the original weight fields, before token advancement or action construction.
//! Parenthesis symbol/weight/action callbacks retain that field order; guest
//! opener allocation precedes the nested-opener callback and closer allocation.
//! The cross-category keep callback retains its original short-circuit predicate
//! before any branch construction. Fork builders append in the original order.
//! These are the source obligations of `TransitionBodyRelocation.v`; that theorem
//! does not establish equality of different token readers, callbacks, or weights.

// Keep the original emitted return statements for source-body correspondence.
#![allow(clippy::needless_return)]

use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{ForkActionKind, ForkBranch, WpdaStepAction};

pub fn paren_singleton<W: SemiringRef>(
    grouping_src_idx: u16,
    cur_bp: &u8,
    pos: &usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    return WpdaStepAction::ConsumeAndPush {
        symbol: StackSymbolV2::grouping_marker(grouping_src_idx, *cur_bp),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch {
            pos: tokens.next_pos(*pos, 0).unwrap_or(*pos + 1),
            cur_bp: 0,
        },
        // Phase F.8: `(` grouping discards the trigger token.
        trigger_mode: crate::wpda_walker::TriggerMode::Discard,
    };
}

#[allow(clippy::too_many_arguments)]
pub fn paren_grouping_branch<W: SemiringRef>(
    grouping_src_idx: u16,
    cur_bp: &u8,
    pos: &usize,
    tokens: &dyn WpdaTokenSource,
    mut grouping_weight: impl FnMut() -> W,
    action_kind: impl FnOnce() -> ForkActionKind,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::grouping_marker(grouping_src_idx, *cur_bp),
        weight: grouping_weight(),
        new_state: WpdaState::PrefixDispatch {
            pos: tokens.next_pos(*pos, 0).unwrap_or(*pos + 1),
            cur_bp: 0,
        },
        action_kind: action_kind(),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn paren_binder_branch<W: SemiringRef>(
    owner_src_idx_lit: u16,
    rule_idx_lit: u16,
    body_src_idx: u16,
    _outer_bp: u8,
    branch_symbol: impl FnOnce() -> StackSymbolV2,
    mut branch_weight: impl FnMut() -> W,
    action_kind: impl FnOnce() -> ForkActionKind,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: branch_symbol(),
        weight: branch_weight(),
        new_state: WpdaState::BinderRule {
            result_src_idx: owner_src_idx_lit,
            rule_idx: rule_idx_lit,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        action_kind: action_kind(),
    }
}

pub fn paren_fork<W: SemiringRef>(
    branch_count: usize,
    build: impl FnOnce(&mut Vec<ForkBranch<W>>),
) -> WpdaStepAction<W> {
    let mut __paren_branches = ::std::vec::Vec::with_capacity(branch_count);
    build(&mut __paren_branches);
    return WpdaStepAction::Fork {
        branches: __paren_branches,
        // Each branch owns its consume semantics.  Grouping and
        // same-category rules consume immediately; a
        // cross-category concrete rule first pushes its source
        // CategoryEntry, then consumes through BinderRule's
        // trigger prelude.  A fork-global consume would erase
        // that required intermediate continuation frame.
        consume_trigger: false,
    };
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_crosscat_lhs<W: SemiringRef>(
    pos: &usize,
    source_src_idx: u16,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    {
        // Cross-category LHS delegation parses a source-category
        // atom that may later produce the target category via a
        // category-changing infix. The target Pratt floor is
        // captured by the runtime edge; the source parse starts
        // at its own root floor so target-context precedence
        // does not reject source-internal operators.
        return WpdaStepAction::PushWithEdgeKind {
            symbol: StackSymbolV2::category_entry(source_src_idx),
            weight: lex_one(),
            new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
            edge_kind: crate::gss::EdgeKind::CrossCatLhs { source_src_idx },
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_binder_prefix<W: SemiringRef>(
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::ConsumeAndPush {
            symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::BinderRule {
                result_src_idx: category_src_idx,
                rule_idx,
                body_src_idx,
                outer_bp: _outer_bp,
            },
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_leading_category<W: SemiringRef>(
    _outer_bp: u8,
    pos: &usize,
    category_src_idx: u16,
    rule_idx: u16,
    source_src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::ReplaceAndPush {
            replace_symbol: StackSymbolV2::rule_at(
                category_src_idx,
                rule_idx,
                1u8,
                Some(_outer_bp),
            ),
            push_symbol: StackSymbolV2::category_entry(source_src_idx),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_token_capture<W: SemiringRef>(
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    kind_name: &str,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::Fork {
            branches: vec![crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
                weight: lex_w(0.0, category_src_idx, rule_idx),
                new_state: WpdaState::BinderRule {
                    result_src_idx: category_src_idx,
                    rule_idx,
                    body_src_idx,
                    outer_bp: _outer_bp,
                },
                action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndPush {
                    kind_name: kind_name.to_string(),
                },
            }],
            consume_trigger: false,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_guest_body<W: SemiringRef>(
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    open_kind: &str,
    nested_open_kinds: impl FnOnce() -> Vec<String>,
    close_kind: &str,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::Fork {
            branches: vec![crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
                weight: lex_w(0.0, category_src_idx, rule_idx),
                new_state: WpdaState::BinderRule {
                    result_src_idx: category_src_idx,
                    rule_idx,
                    body_src_idx,
                    outer_bp: _outer_bp,
                },
                action_kind: crate::wpda_walker::ForkActionKind::ConsumeGuestBodyAndPush {
                    open_kind: open_kind.to_string(),
                    nested_open_kinds: nested_open_kinds(),
                    close_kind: close_kind.to_string(),
                },
            }],
            consume_trigger: false,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_crosscat_unary<W: SemiringRef>(
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    source_src_idx: u16,
    operand_bp: u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::ConsumeAndPush {
            symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 0, Some(_outer_bp))
                .with_kind_return(),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp: operand_bp },
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_crosscat_projection<W: SemiringRef>(
    _outer_bp: u8,
    cur_bp: &u8,
    category_src_idx: u16,
    rule_idx: u16,
    source_src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        // B10 / Option κ Fix B (2026-05-07): cross-cat
        // projection singleton — Push the rule's Return
        // marker and route to CrossCatDelegate so the
        // source-cat sub-parse fires; on return, the
        // projection's action wraps the source term.
        // Transparent projection delegates into a source
        // category while remaining inside the caller's Pratt
        // operand slot. Carry the active floor through so
        // the source parse respects the caller's binding
        // context.
        return WpdaStepAction::Push {
            symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 0, Some(_outer_bp))
                .with_kind_return(),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp: *cur_bp },
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_nullary_literal_run<W: SemiringRef>(
    cur_bp: &u8,
    category_src_idx: u16,
    rule_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        // GAP-3: 0-operand multi-literal keyword prefix. Consume
        // the trigger (ConsumeAsTriggerOnly mirrors it to the
        // SPPF as a TriggerTerminal — the SOLE child under the
        // marker, anchoring its span lo; Discard would leave 0
        // children → span realization fail), push the mixfix
        // marker, and enter the REUSED MixfixLiteralRun(kind=2,
        // parts_len==0) arm, which consumes the trailing literals
        // then pops the marker to fire the arity-0 action.
        return WpdaStepAction::ConsumeAndPush {
            symbol: StackSymbolV2::mixfix_marker(category_src_idx, rule_idx, 0u8, *cur_bp),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::MixfixLiteralRun {
                result_src_idx: category_src_idx,
                rule_idx,
                completed_idx: 0u8,
                kind: 2u8,
                sub_pos: 0u8,
            },
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn push_crosscat_lhs<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    pos: &usize,
    category_src_idx: u16,
    src_idx: u16,
    __keep_guard: impl FnOnce() -> bool,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    // The runtime edge stores the caller's target floor;
    // the delegated source parse starts at source root.
    if __keep_guard() {
        __pd_branches.push(crate::wpda_walker::ForkBranch {
            symbol: StackSymbolV2::category_entry(src_idx),
            weight: lex_w(
                crate::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                category_src_idx,
                src_idx,
            ),
            new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
            action_kind: crate::wpda_walker::ForkActionKind::PushCrossCatLhs,
        });
    }
}

#[allow(clippy::too_many_arguments)]
pub fn push_atomic<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    csi: u16,
    rule_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(csi, rule_idx, 0, Some(_outer_bp)).with_kind_return(),
        weight: lex_w(0.0, csi, rule_idx),
        new_state: WpdaState::Unwinding,
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndCaptureAndPush,
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_binder_prefix<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx: category_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndPush {
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        },
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_leading_category<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    pos: &usize,
    category_src_idx: u16,
    rule_idx: u16,
    source_src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::category_entry(source_src_idx),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
        action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
            replace_symbol: StackSymbolV2::rule_at(
                category_src_idx,
                rule_idx,
                1u8,
                Some(_outer_bp),
            ),
        },
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_token_capture<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    kind_name: &str,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx: category_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndPush {
            kind_name: kind_name.to_string(),
        },
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_guest_body<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    open_kind: &str,
    nested_open_kinds: impl FnOnce() -> Vec<String>,
    close_kind: &str,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx: category_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeGuestBodyAndPush {
            open_kind: open_kind.to_string(),
            nested_open_kinds: nested_open_kinds(),
            close_kind: close_kind.to_string(),
        },
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_crosscat_unary<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    source_src_idx: u16,
    operand_bp: u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 0, Some(_outer_bp))
            .with_kind_return(),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp: operand_bp },
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndPush {
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        },
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_crosscat_projection<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    _outer_bp: u8,
    cur_bp: &u8,
    category_src_idx: u16,
    rule_idx: u16,
    src_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 0, Some(_outer_bp))
            .with_kind_return(),
        weight: lex_w(
            crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
            category_src_idx,
            rule_idx,
        ),
        new_state: WpdaState::CrossCatDelegate {
            source_src_idx: src_idx,
            inner_cur_bp: *cur_bp,
        },
        action_kind: crate::wpda_walker::ForkActionKind::Push,
    });
}

#[allow(clippy::too_many_arguments)]
pub fn push_nullary_literal_run<W: SemiringRef>(
    __pd_branches: &mut Vec<ForkBranch<W>>,
    cur_bp: &u8,
    category_src_idx: u16,
    rule_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) {
    // GAP-3: nullary multi-literal keyword prefix Fork branch
    // (e.g. `@ Nil` co-bucketed with `@ ( p )` / `@ p`).
    // Consume the trigger as a TriggerTerminal, push the
    // mixfix marker, enter MixfixLiteralRun(kind=2). Tier 0.0
    // (atomic-home) so lex-min picks the lowest-rule_idx branch
    // (declaration order) on a parse-success tie — NQuoteNil
    // (declared before NQuoteShort) wins for `@Nil`.
    __pd_branches.push(crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::mixfix_marker(category_src_idx, rule_idx, 0u8, *cur_bp),
        weight: lex_w(0.0, category_src_idx, rule_idx),
        new_state: WpdaState::MixfixLiteralRun {
            result_src_idx: category_src_idx,
            rule_idx,
            completed_idx: 0u8,
            kind: 2u8,
            sub_pos: 0u8,
        },
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndPush {
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        },
    });
}

pub fn unified_fork<W: SemiringRef>(
    n_descs: usize,
    build: impl FnOnce(&mut Vec<ForkBranch<W>>),
) -> WpdaStepAction<W> {
    {
        let mut __pd_branches: Vec<crate::wpda_walker::ForkBranch<_>> = Vec::with_capacity(n_descs);
        build(&mut __pd_branches);
        return WpdaStepAction::Fork {
            branches: __pd_branches,
            consume_trigger: false,
        };
    }
}

#[allow(clippy::too_many_arguments)]
pub fn singleton_atomic<W: SemiringRef>(
    _outer_bp: u8,
    category_src_idx: u16,
    rule_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    {
        return WpdaStepAction::ConsumeAndPush {
            symbol: StackSymbolV2::rule_at(category_src_idx, rule_idx, 0, Some(_outer_bp))
                .with_kind_return(),
            weight: lex_w(0.0, category_src_idx, rule_idx),
            new_state: WpdaState::Unwinding,
            // Phase F.8: atomic literal arm — the consumed token IS
            // the action arg (CaptureForBuilder). Not a unary-prefix
            // trigger (no operand sub-parse).
            trigger_mode: crate::wpda_walker::TriggerMode::CaptureForBuilder,
        };
    }
}
