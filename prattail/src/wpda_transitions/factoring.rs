//! Original factoring transition bodies; trie construction and static routing stay with callers.
//!
//! Symbol, state, weight, and ordered branch callbacks run at the original sites.
use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{StackSymbolV2, WpdaState};
use crate::wpda_walker::{ForkBranch, WpdaStepAction};

#[allow(clippy::too_many_arguments)]
pub fn child_literal<W: SemiringRef>(
    symbol: impl FnOnce() -> StackSymbolV2,
    state: impl FnOnce() -> WpdaState,
    text: &str,
    required_top_cat: Option<u16>,
    mut lex_one: impl FnMut() -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: symbol(),
        weight: lex_one(),
        new_state: state(),
        action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
            expected_text: text.to_string(),
            required_top_cat,
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn parameter_replace_branch<W: SemiringRef>(
    cat_src_idx: u16,
    _pos: usize,
    cur_bp: u8,
    symbol: impl FnOnce() -> StackSymbolV2,
    mut lex_one: impl FnMut() -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp },
        action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
            replace_symbol: symbol(),
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn literal_chain<W: SemiringRef>(branch: impl FnOnce() -> ForkBranch<W>) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![branch()],
        consume_trigger: false,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn parameter_replace<W: SemiringRef>(
    symbol: impl FnOnce() -> StackSymbolV2,
    cat_src_idx: u16,
    _pos: usize,
    cur_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ReplaceAndPush {
        replace_symbol: symbol(),
        push_symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn divergence<W: SemiringRef>(
    branch_count: usize,
    build: impl FnOnce(&mut Vec<ForkBranch<W>>),
) -> WpdaStepAction<W> {
    let mut __spine_branches = ::std::vec::Vec::with_capacity(branch_count);
    build(&mut __spine_branches);
    return WpdaStepAction::Fork {
        branches: __spine_branches,
        consume_trigger: false,
    };
}

#[allow(clippy::too_many_arguments)]
pub fn mixfix_group_branch<W: SemiringRef>(
    result_src: u16,
    spine_id: u16,
    cur_bp: u8,
    min_member: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::mixfix_marker(result_src, spine_id, 0, cur_bp),
        weight: lex_w(crate::automata::lex_weight::BP_TIER_MIXFIX, result_src, min_member),
        new_state: WpdaState::MixfixLiteralRun {
            result_src_idx: result_src,
            rule_idx: spine_id,
            completed_idx: 0,
            kind: 2,
            sub_pos: 0,
        },
        action_kind: crate::wpda_walker::ForkActionKind::Push,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn parameter_push<W: SemiringRef>(
    cat_src_idx: u16,
    _pos: usize,
    cur_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Push {
        symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn literal_singleton<W: SemiringRef>(
    targets: &[usize],
    symbol: impl FnOnce() -> StackSymbolV2,
    state: impl FnOnce() -> WpdaState,
    mut lex_one: impl FnMut() -> W,
) -> Option<WpdaStepAction<W>> {
    if let Some(&__spine_np) = targets.first() {
        return Some(WpdaStepAction::ConsumeAtAndReplace {
            symbol: symbol(),
            weight: lex_one(),
            new_state: state(),
            next_pos: __spine_np,
        });
    }
    None
}

#[allow(clippy::too_many_arguments)]
pub fn append_literal_targets<W: SemiringRef>(
    targets: &[usize],
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut state: impl FnMut() -> WpdaState,
    mut lex_one: impl FnMut() -> W,
    __spine_branches: &mut Vec<ForkBranch<W>>,
) {
    for __spine_np in targets {
        __spine_branches.push(crate::wpda_walker::ForkBranch {
            symbol: symbol(),
            weight: lex_one(),
            new_state: state(),
            action_kind: crate::wpda_walker::ForkActionKind::ConsumeAtAndReplace {
                next_pos: *__spine_np,
            },
        });
    }
}

#[allow(clippy::too_many_arguments)]
pub fn parameter_push_branch<W: SemiringRef>(
    cat_src_idx: u16,
    _pos: usize,
    cur_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp },
        action_kind: crate::wpda_walker::ForkActionKind::Push,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn zero_literal_only<W: SemiringRef>(
    __spine_lit_total: usize,
    _pos: usize,
    result_src: u16,
    spine_id: u16,
) -> Option<WpdaStepAction<W>> {
    if __spine_lit_total == 0 {
        return Some(WpdaStepAction::Error(format!(
            "mixfix spine divergence mismatch at pos {} (spine {}:{}) — \
             no lattice edge matches any commit literal",
            _pos, result_src, spine_id,
        )));
    }
    None
}

#[allow(clippy::too_many_arguments)]
pub fn zero_one_operand<W: SemiringRef>(
    __spine_lit_total: usize,
    nonfork: impl FnOnce() -> WpdaStepAction<W>,
) -> Option<WpdaStepAction<W>> {
    if __spine_lit_total == 0 {
        return Some(nonfork());
    }
    None
}

#[allow(clippy::too_many_arguments)]
pub fn singleton<W: SemiringRef>(
    __spine_lit_total: usize,
    choose: impl FnOnce() -> Option<WpdaStepAction<W>>,
) -> Option<WpdaStepAction<W>> {
    if __spine_lit_total == 1 {
        return choose();
    }
    None
}

#[allow(clippy::too_many_arguments)]
pub fn mixfix_divergence<W: SemiringRef>(
    n_uncond_lit: usize,
    __spine_lit_total: usize,
    build: impl FnOnce(&mut Vec<ForkBranch<W>>),
) -> WpdaStepAction<W> {
    let mut __spine_branches: Vec<ForkBranch<W>> =
        Vec::with_capacity(n_uncond_lit + __spine_lit_total);
    build(&mut __spine_branches);
    return WpdaStepAction::Fork {
        branches: __spine_branches,
        consume_trigger: false,
    };
}

#[allow(clippy::too_many_arguments)]
pub fn prefix_spine_trigger<W: SemiringRef>(
    category_src_idx: u16,
    spine_id: u16,
    body_src_idx: u16,
    _outer_bp: u8,
    weight_rule_idx: u16,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(category_src_idx, spine_id, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, category_src_idx, weight_rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx: category_src_idx,
            rule_idx: spine_id,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndPush {
            trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
        },
    }
}
