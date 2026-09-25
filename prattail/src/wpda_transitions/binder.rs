//! Shared bodies of the original generated binder transition leaves.
//!
//! Callers retain rule/position dispatch and supply the original constants.
//! Weight and capture callbacks execute at their original observation sites.

use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{ForkActionKind, ForkBranch, WpdaStepAction};

/// Complete a rule at its generated final position.
pub fn rule_complete<W: SemiringRef>(
    outer_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Pop {
        weight: lex_one(),
        new_state: WpdaState::InfixLoop { cur_bp: outer_bp },
    }
}

/// Replace the caller marker and enter the declared strict child category.
#[allow(clippy::too_many_arguments)]
pub fn rule_parameter<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    next_pos: u8,
    outer_bp: u8,
    cat_src_idx: u16,
    pos: usize,
    cur_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ReplaceAndPush {
        replace_symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, next_pos, Some(outer_bp)),
        push_symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos, cur_bp },
    }
}

/// Enter the existing binder-internal collection slot.
#[allow(clippy::too_many_arguments)]
pub fn rule_collection_parameter<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    next_pos: u8,
    outer_bp: u8,
    slot_idx: u8,
    pos: usize,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ReplaceAndPush {
        replace_symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, next_pos, Some(outer_bp)),
        push_symbol: StackSymbolV2::collection_marker(result_src_idx, rule_idx, slot_idx, 0u8),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos, cur_bp: 0u8 },
    }
}

/// Delegate the existing predicate action to the walker.
pub fn rule_guard<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    next_pos: u8,
    outer_bp: u8,
    body_src_idx: u16,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ParsePredicate {
        replace_symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, next_pos, Some(outer_bp)),
        weight: lex_one(),
        new_state: WpdaState::BinderRule {
            result_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp,
        },
    }
}

/// Enter the original optional-group state at sub-position zero.
pub fn rule_optional<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    group_idx: u32,
    outer_bp: u8,
) -> WpdaStepAction<W> {
    WpdaStepAction::Advance(WpdaState::OptionalGroup {
        result_src_idx,
        rule_idx,
        group_idx,
        sub_pos: 0,
        outer_bp,
    })
}

/// Preserve every matching lexical edge for a mid-rule token capture.
pub fn token_capture_and_replace<W: SemiringRef>(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    kind_name: &str,
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut new_state: impl FnMut() -> WpdaState,
    mut lex_w_alt_with_len: impl FnMut(u16, f64, u16, u16, u16) -> W,
) -> WpdaStepAction<W> {
    let capture_branches =
        crate::wpda_runtime::matching_token_capture_edges(tokens, pos, kind_name)
            .into_iter()
            .map(|edge| {
                let open_len = u16::try_from(edge.text.len()).expect("token length exceeds u16");
                let capture_symbol = symbol();
                ForkBranch {
                    weight: lex_w_alt_with_len(
                        open_len,
                        0.0,
                        capture_symbol.category_src_idx,
                        capture_symbol.rule_index_in_category,
                        edge.alt_idx,
                    ),
                    symbol: capture_symbol,
                    new_state: new_state(),
                    action_kind: ForkActionKind::ConsumeTokenKindAtAndReplace {
                        alt_idx: edge.alt_idx,
                        kind_name: kind_name.to_string(),
                        kind: edge.kind,
                        text: edge.text,
                        next_pos: edge.next_pos,
                    },
                }
            })
            .collect();
    WpdaStepAction::Fork {
        branches: capture_branches,
        consume_trigger: false,
    }
}

/// Emit the original single guarded literal branch; the walker checks it.
#[allow(clippy::too_many_arguments)]
pub fn rule_literal<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    next_pos: u8,
    outer_bp: u8,
    body_src_idx: u16,
    text: &str,
    required_top_cat: Option<u16>,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![ForkBranch {
            symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, next_pos, Some(outer_bp)),
            weight: lex_one(),
            new_state: WpdaState::BinderRule {
                result_src_idx,
                rule_idx,
                body_src_idx,
                outer_bp,
            },
            action_kind: ForkActionKind::GuardedConsumeAndReplace {
                expected_text: text.to_string(),
                required_top_cat,
            },
        }],
        consume_trigger: false,
    }
}

/// Emit the original guest-region capture branch without parsing its body.
#[allow(clippy::too_many_arguments)]
pub fn rule_guest_body<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    next_pos: u8,
    outer_bp: u8,
    body_src_idx: u16,
    open_kind: &str,
    nested_open_kinds: impl FnOnce() -> Vec<String>,
    close_kind: &str,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![ForkBranch {
            symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, next_pos, Some(outer_bp)),
            weight: lex_one(),
            new_state: WpdaState::BinderRule {
                result_src_idx,
                rule_idx,
                body_src_idx,
                outer_bp,
            },
            action_kind: ForkActionKind::ConsumeGuestBodyAndReplace {
                open_kind: open_kind.to_string(),
                nested_open_kinds: nested_open_kinds(),
                close_kind: close_kind.to_string(),
            },
        }],
        consume_trigger: false,
    }
}

/// Original generated list plain head transition.
#[allow(clippy::too_many_arguments)]
pub fn list_plain_head<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    tokens: &dyn WpdaTokenSource,
    _pos: usize,
    close: &str,
    separator: &str,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    let _ = tokens.peek_text(_pos);
    WpdaStepAction::Fork {
        branches: vec![
            crate::wpda_walker::ForkBranch {
                symbol: resume_symbol(),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind:
                    crate::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                        expected_text: close.to_string(),
                        effect: crate::wpda_walker::BuilderDelta::EndBinderScope,
                    },
            },
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 0u32,
                },
                action_kind: crate::wpda_walker::ForkActionKind::GuardedConsume {
                    expected_text: separator.to_string(),
                },
            },
            crate::wpda_walker::ForkBranch {
                symbol: resume_symbol(),
                weight: lex_w(
                    crate::automata::lex_weight::EPSILON_OPT_SKIP,
                    result_src_idx,
                    rule_idx,
                ),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 0u32,
                },
                action_kind:
                    crate::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                        start_scope: false,
                    },
            },
        ],
        consume_trigger: false,
    }
}

/// Original generated list collection head transition.
#[allow(clippy::too_many_arguments)]
pub fn list_collection_head<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    tokens: &dyn WpdaTokenSource,
    _pos: usize,
    close: &str,
    separator: &str,
    first_marker_id: u32,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    let _ = tokens.peek_text(_pos);
    WpdaStepAction::Fork {
        branches: vec![
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeAndPopWithEffect {
                    expected_text: close.to_string(),
                    effect: crate::wpda_walker::BuilderDelta::EndBinderScope,
                },
            },
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::category_entry(0),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 0u32,
                },
                action_kind: crate::wpda_walker::ForkActionKind::GuardedConsume {
                    expected_text: separator.to_string(),
                },
            },
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::binder_list_loop_at(first_marker_id, outer_bp),
                weight: lex_w(
                    crate::automata::lex_weight::EPSILON_OPT_SKIP,
                    result_src_idx,
                    rule_idx,
                ),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 1u32,
                },
                action_kind: crate::wpda_walker::ForkActionKind::Push,
            },
        ],
        consume_trigger: false,
    }
}

/// Original generated position literal transition.
#[allow(clippy::too_many_arguments)]
pub fn position_literal<W: SemiringRef>(
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut new_state: impl FnMut() -> WpdaState,
    text: &str,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: symbol(),
            weight: lex_one(),
            new_state: new_state(),
            action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
                expected_text: text.to_string(),
                required_top_cat: None,
            },
        }],
        consume_trigger: false,
    }
}

/// Original generated position guest body transition.
#[allow(clippy::too_many_arguments)]
pub fn position_guest_body<W: SemiringRef>(
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut new_state: impl FnMut() -> WpdaState,
    open_kind: &str,
    nested_open_kinds: impl FnOnce() -> Vec<String>,
    close_kind: &str,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: symbol(),
            weight: lex_one(),
            new_state: new_state(),
            action_kind: crate::wpda_walker::ForkActionKind::ConsumeGuestBodyAndReplace {
                open_kind: open_kind.to_string(),
                nested_open_kinds: nested_open_kinds(),
                close_kind: close_kind.to_string(),
            },
        }],
        consume_trigger: false,
    }
}

/// Original generated position binder ident transition.
#[allow(clippy::too_many_arguments)]
pub fn position_binder_ident<W: SemiringRef>(
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut new_state: impl FnMut() -> WpdaState,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: symbol(),
            weight: lex_one(),
            new_state: new_state(),
            action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                start_scope: false,
            },
        }],
        consume_trigger: false,
    }
}

/// Original generated position parameter transition.
#[allow(clippy::too_many_arguments)]
pub fn position_parameter<W: SemiringRef>(
    mut symbol: impl FnMut() -> StackSymbolV2,
    cat_src_idx: u16,
    _pos: usize,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ReplaceAndPush {
        replace_symbol: symbol(),
        push_symbol: StackSymbolV2::category_entry_goal(cat_src_idx),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0u8 },
    }
}

/// Original generated position guard transition.
#[allow(clippy::too_many_arguments)]
pub fn position_guard<W: SemiringRef>(
    mut symbol: impl FnMut() -> StackSymbolV2,
    mut new_state: impl FnMut() -> WpdaState,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ParsePredicate {
        replace_symbol: symbol(),
        weight: lex_one(),
        new_state: new_state(),
    }
}

/// Original generated list complete transition.
#[allow(clippy::too_many_arguments)]
pub fn list_complete<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Pop {
        weight: lex_one(),
        new_state: WpdaState::BinderListLoop {
            result_src_idx,
            rule_idx,
            frame_idx,
            outer_bp,
            sub_pos: 0u32,
        },
    }
}

/// Original generated optional start transition.
#[allow(clippy::too_many_arguments)]
pub fn optional_start<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    group_idx_value: u32,
    outer_bp: u8,
    take_marker_id: u32,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut resume_state: impl FnMut() -> WpdaState,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![
            // TAKE branch (push OptionalGroupAt(1) →
            // walker auto-opens optional scope via
            // emit_push_side_effects).
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::optional_group_at(take_marker_id, outer_bp),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::OptionalGroup {
                    result_src_idx,
                    rule_idx,
                    group_idx: group_idx_value,
                    sub_pos: 1,
                    outer_bp,
                },
                action_kind: crate::wpda_walker::ForkActionKind::Push,
            },
            // SKIP branch (mirror OptGroupAbsent: log
            // PushOptionalAbsent + pop outer RuleAt +
            // push advanced outer RuleAt).
            crate::wpda_walker::ForkBranch {
                // `symbol` is unused for OptGroupAbsent
                // action_kind — the cursor-side Fork
                // arm uses `replace_symbol` from
                // `action_kind`. We supply a stable
                // sentinel to satisfy the field.
                symbol: StackSymbolV2::category_entry(0),
                weight: lex_w(
                    crate::automata::lex_weight::EPSILON_OPT_SKIP,
                    result_src_idx,
                    rule_idx,
                ),
                new_state: resume_state(),
                action_kind: crate::wpda_walker::ForkActionKind::OptGroupAbsent {
                    replace_symbol: resume_symbol(),
                },
            },
        ],
        consume_trigger: false,
    }
}

/// Original generated optional collection transition.
#[allow(clippy::too_many_arguments)]
pub fn optional_collection<W: SemiringRef>(
    next_marker_id: u32,
    outer_bp: u8,
    result_src_idx: u16,
    rule_idx: u16,
    slot_idx: u8,
    _pos: usize,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::ReplaceAndPush {
        replace_symbol: StackSymbolV2::optional_group_at(next_marker_id, outer_bp),
        push_symbol: StackSymbolV2::collection_marker(
            // binder-internal collection: dispatch_bp=0.
            result_src_idx,
            rule_idx,
            slot_idx,
            0u8,
        ),
        weight: lex_one(),
        new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0u8 },
    }
}

/// Original generated optional ident transition.
#[allow(clippy::too_many_arguments)]
pub fn optional_ident<W: SemiringRef>(
    next_marker_id: u32,
    outer_bp: u8,
    result_src_idx: u16,
    rule_idx: u16,
    group_idx_value: u32,
    next_sp: u32,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: StackSymbolV2::optional_group_at(next_marker_id, outer_bp),
            weight: lex_one(),
            new_state: WpdaState::OptionalGroup {
                result_src_idx,
                rule_idx,
                group_idx: group_idx_value,
                sub_pos: next_sp,
                outer_bp,
            },
            action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                start_scope: true,
            },
        }],
        consume_trigger: false,
    }
}

/// Original generated optional complete transition.
#[allow(clippy::too_many_arguments)]
pub fn optional_complete<W: SemiringRef>(
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut resume_state: impl FnMut() -> WpdaState,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::OptGroupFinalize {
        replace_symbol: resume_symbol(),
        weight: lex_one(),
        new_state: resume_state(),
    }
}

/// Enter the original singleton binder scope and close it on consumption.
pub fn list_entry_single<W: SemiringRef>(
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: resume_symbol(),
            weight: lex_one(),
            new_state: WpdaState::Unwinding,
            action_kind:
                crate::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplaceWithEffect {
                    start_scope: true,
                    effect: crate::wpda_walker::BuilderDelta::EndBinderScope,
                },
        }],
        consume_trigger: false,
    }
}
/// Enter the original nonempty collection-backed binder list.
#[allow(clippy::too_many_arguments)]
pub fn list_entry_collection<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    _close: &str,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    slot_idx: u8,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: StackSymbolV2::collection_marker(result_src_idx, rule_idx, slot_idx, 0u8),
            weight: lex_w(crate::automata::lex_weight::EPSILON_OPT_SKIP, result_src_idx, rule_idx),
            new_state: WpdaState::BinderListLoop {
                result_src_idx,
                rule_idx,
                frame_idx,
                outer_bp,
                sub_pos: 0u32,
            },
            action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
                replace_symbol: resume_symbol(),
            },
        }],
        consume_trigger: false,
    }
}

/// Enter the original collection-backed binder list, empty branch first.
#[allow(clippy::too_many_arguments)]
pub fn list_entry_collection_allow_empty<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    close: &str,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    slot_idx: u8,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![
            crate::wpda_walker::ForkBranch {
                symbol: resume_symbol(),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind:
                    crate::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                        expected_text: close.to_string(),
                        effects: vec![
                            crate::wpda_walker::BuilderDelta::StartCollection,
                            crate::wpda_walker::BuilderDelta::PushCollectionId { id: slot_idx },
                            crate::wpda_walker::BuilderDelta::StartBinderScope { names: Vec::new() },
                            crate::wpda_walker::BuilderDelta::EndBinderScope,
                        ],
                    },
            },
            crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::collection_marker(result_src_idx, rule_idx, slot_idx, 0u8),
                weight: lex_w(crate::automata::lex_weight::EPSILON_OPT_SKIP, result_src_idx, rule_idx),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 0u32,
                },
                action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
                    replace_symbol: resume_symbol(),
                },
            },
        ],
        consume_trigger: false,
    }
}

/// Enter the original nonempty ordinary binder list.
#[allow(clippy::too_many_arguments)]
pub fn list_entry_plain<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    _close: &str,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: resume_symbol(),
            weight: lex_w(crate::automata::lex_weight::EPSILON_OPT_SKIP, result_src_idx, rule_idx),
            new_state: WpdaState::BinderListLoop {
                result_src_idx,
                rule_idx,
                frame_idx,
                outer_bp,
                sub_pos: 0u32,
            },
            action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                start_scope: true,
            },
        }],
        consume_trigger: false,
    }
}

/// Enter the original ordinary binder list, empty branch first.
#[allow(clippy::too_many_arguments)]
pub fn list_entry_plain_allow_empty<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    frame_idx: u32,
    outer_bp: u8,
    close: &str,
    mut resume_symbol: impl FnMut() -> StackSymbolV2,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: vec![
            crate::wpda_walker::ForkBranch {
                symbol: resume_symbol(),
                weight: lex_w(0.0, result_src_idx, rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind:
                    crate::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                        expected_text: close.to_string(),
                        effects: vec![
                            crate::wpda_walker::BuilderDelta::StartBinderScope { names: Vec::new() },
                            crate::wpda_walker::BuilderDelta::EndBinderScope,
                        ],
                    },
            },
            crate::wpda_walker::ForkBranch {
                symbol: resume_symbol(),
                weight: lex_w(crate::automata::lex_weight::EPSILON_OPT_SKIP, result_src_idx, rule_idx),
                new_state: WpdaState::BinderListLoop {
                    result_src_idx,
                    rule_idx,
                    frame_idx,
                    outer_bp,
                    sub_pos: 0u32,
                },
                action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                    start_scope: true,
                },
            },
        ],
        consume_trigger: false,
    }
}

/// Consume the selected binder trigger with the original rule continuation.
pub fn trigger_singleton<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    _outer_bp: u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    trigger_mode: impl FnOnce() -> crate::wpda_walker::TriggerMode,
) -> WpdaStepAction<W> {
    return WpdaStepAction::ConsumeAndPush {
        symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, result_src_idx, rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        trigger_mode: trigger_mode(),
    };
}

/// Preserve one same-trigger branch's rule identity and trigger ownership.
pub fn trigger_branch<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    body_src_idx: u16,
    _outer_bp: u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(result_src_idx, rule_idx, 1u8, Some(_outer_bp)),
        weight: lex_w(0.0, result_src_idx, rule_idx),
        new_state: WpdaState::BinderRule {
            result_src_idx,
            rule_idx,
            body_src_idx,
            outer_bp: _outer_bp,
        },
        // Mirror the singleton ConsumeAndPush structural
        // trigger path: each ambiguous trigger branch owns
        // the consumed keyword under its rule identity.
        action_kind: crate::wpda_walker::ForkActionKind::PushWithTriggerTerminal,
    }
}

/// Allocate the original trigger vector before the caller's ordered pushes.
pub fn trigger_fork<W: SemiringRef>(
    branch_count: usize,
    build: impl FnOnce(&mut Vec<ForkBranch<W>>),
) -> WpdaStepAction<W> {
    let mut __binder_trigger_branches = ::std::vec::Vec::with_capacity(branch_count);
    build(&mut __binder_trigger_branches);
    return WpdaStepAction::Fork {
        branches: __binder_trigger_branches,
        consume_trigger: true,
    };
}

/// Validate and consume the existing cross-category binder-rule prelude.
#[allow(clippy::too_many_arguments)]
pub fn category_entry_prelude<'a, W: SemiringRef>(
    __entry: &crate::gss::WpdaGssNode,
    result_src_idx: &u16,
    rule_idx: &u16,
    _body_src_idx: &u16,
    outer_bp: &u8,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    expected_trigger: impl FnOnce() -> Option<&'a str>,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    if __entry.symbol.category_src_idx != *result_src_idx {
        return WpdaStepAction::Error(format!(
            "binder-rule source category mismatch: expected {}, found {}",
            result_src_idx, __entry.symbol.category_src_idx,
        ));
    }
    let __expected_trigger: Option<&'a str> = expected_trigger();
    let Some(__expected_trigger) = __expected_trigger else {
        return WpdaStepAction::Error(format!(
            "binder rule {}:{} has no literal trigger for category-entry dispatch",
            result_src_idx, rule_idx,
        ));
    };
    if tokens.peek_text(_pos) != Some(__expected_trigger) {
        return WpdaStepAction::Error(format!(
            "expected binder-rule trigger {:?} at pos {}, found {:?}",
            __expected_trigger,
            _pos,
            tokens.peek_text(_pos),
        ));
    }
    return WpdaStepAction::ConsumeAndPush {
        symbol: StackSymbolV2::rule_at(*result_src_idx, *rule_idx, 1u8, Some(*outer_bp)),
        weight: lex_one(),
        new_state: WpdaState::BinderRule {
            result_src_idx: *result_src_idx,
            rule_idx: *rule_idx,
            body_src_idx: *_body_src_idx,
            outer_bp: *outer_bp,
        },
        trigger_mode: crate::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::automata::TokenKind;
    use crate::lexer_types::{LexAlternative, LexEntry, LexStream};
    use crate::wpda_runtime::{lex_one, lex_w, lex_w_alt_with_len, MultiTokenSource};
    use std::cell::RefCell;

    #[test]
    fn list_entry_variants_preserve_effects_and_lazy_branch_schedule() {
        use crate::wpda_walker::BuilderDelta;
        let marker = StackSymbolV2::optional_group_at(91, 5);
        let WpdaStepAction::Fork { branches, consume_trigger } =
            list_entry_single(|| marker, lex_one)
        else {
            panic!("singleton entry must fork")
        };
        assert!(!consume_trigger);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].symbol, marker);
        assert!(matches!(
            branches[0].action_kind,
            ForkActionKind::GuardedConsumeBinderIdentAndReplaceWithEffect {
                start_scope: true,
                effect: BuilderDelta::EndBinderScope
            }
        ));
        for allow_empty in [false, true] {
            let trace = RefCell::new(Vec::new());
            let collection_entry = if allow_empty {
                list_entry_collection_allow_empty
            } else {
                list_entry_collection
            };
            let WpdaStepAction::Fork { branches, consume_trigger } = collection_entry(
                2,
                3,
                1000,
                5,
                ")",
                || {
                    trace.borrow_mut().push("symbol");
                    marker
                },
                |cost, cat, rule| {
                    trace.borrow_mut().push("weight");
                    lex_w(cost, cat, rule)
                },
                9,
            ) else {
                panic!("collection entry must fork")
            };
            assert!(!consume_trigger);
            assert_eq!(branches.len(), 1 + usize::from(allow_empty));
            assert_eq!(
                *trace.borrow(),
                if allow_empty {
                    vec!["symbol", "weight", "weight", "symbol"]
                } else {
                    vec!["weight", "symbol"]
                }
            );
            let last = branches.last().expect("nonempty entry branch");
            assert_eq!(last.symbol, StackSymbolV2::collection_marker(2, 3, 9, 0));
            assert!(
                matches!(last.action_kind,ForkActionKind::ReplaceAndPush {replace_symbol} if replace_symbol==marker)
            );
            if allow_empty {
                let ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                    expected_text,
                    effects,
                } = &branches[0].action_kind
                else {
                    panic!("empty collection entry has all original effects")
                };
                assert_eq!(expected_text, ")");
                assert!(matches!(effects.as_slice(),[
                    BuilderDelta::StartCollection,BuilderDelta::PushCollectionId {id:9},
                    BuilderDelta::StartBinderScope {names},BuilderDelta::EndBinderScope
                ] if names.is_empty()));
            }
            trace.borrow_mut().clear();
            let plain_entry = if allow_empty {
                list_entry_plain_allow_empty
            } else {
                list_entry_plain
            };
            let WpdaStepAction::Fork { branches, .. } = plain_entry(
                2,
                3,
                1000,
                5,
                ")",
                || {
                    trace.borrow_mut().push("symbol");
                    marker
                },
                |cost, cat, rule| {
                    trace.borrow_mut().push("weight");
                    lex_w(cost, cat, rule)
                },
            ) else {
                panic!("plain entry must fork")
            };
            assert_eq!(
                *trace.borrow(),
                if allow_empty {
                    vec!["symbol", "weight", "symbol", "weight"]
                } else {
                    vec!["symbol", "weight"]
                }
            );
            assert_eq!(branches.len(), 1 + usize::from(allow_empty));
            assert!(matches!(
                branches.last().expect("plain nonempty branch").action_kind,
                ForkActionKind::GuardedConsumeBinderIdentAndReplace { start_scope: true }
            ));
        }
    }

    #[test]
    fn optional_take_skip_and_completion_preserve_continuations_and_order() {
        let trace = RefCell::new(Vec::new());
        let resume = StackSymbolV2::binder_list_loop_at(92, 5);
        let WpdaStepAction::Fork { branches, consume_trigger } = optional_start(
            2,
            3,
            1000,
            5,
            91,
            || {
                trace.borrow_mut().push("symbol");
                resume
            },
            || {
                trace.borrow_mut().push("state");
                WpdaState::Unwinding
            },
            |cost, cat, rule| {
                trace.borrow_mut().push("weight");
                lex_w(cost, cat, rule)
            },
        ) else {
            panic!("optional start must fork")
        };
        assert!(!consume_trigger);
        assert_eq!(branches.len(), 2);
        assert_eq!(*trace.borrow(), ["weight", "weight", "state", "symbol"]);
        assert_eq!(branches[0].symbol, StackSymbolV2::optional_group_at(91, 5));
        assert!(matches!(branches[0].action_kind, ForkActionKind::Push));
        assert!(
            matches!(branches[1].action_kind,ForkActionKind::OptGroupAbsent {replace_symbol} if replace_symbol==resume)
        );
        assert_eq!(branches[0].weight, lex_w(0.0, 2, 3));
        assert_eq!(branches[1].weight, lex_w(crate::automata::lex_weight::EPSILON_OPT_SKIP, 2, 3));
        let WpdaStepAction::OptGroupFinalize { replace_symbol, .. } =
            optional_complete(|| resume, || WpdaState::Unwinding, lex_one)
        else {
            panic!("optional completion must finalize, not plain-pop")
        };
        assert_eq!(replace_symbol, resume);
        let WpdaStepAction::Pop { new_state, .. } = list_complete(2, 3, 1000, 5, lex_one) else {
            panic!("list completion must pop")
        };
        assert!(matches!(
            new_state,
            WpdaState::BinderListLoop {
                result_src_idx: 2,
                rule_idx: 3,
                frame_idx: 1000,
                outer_bp: 5,
                sub_pos: 0
            }
        ));
        let WpdaStepAction::Fork { branches, .. } = optional_ident(91, 5, 2, 3, 1000, 4, lex_one)
        else {
            panic!("optional ident must fork")
        };
        assert!(matches!(
            branches[0].action_kind,
            ForkActionKind::GuardedConsumeIdentAndReplace { start_scope: true }
        ));
        let WpdaStepAction::Fork { branches, .. } =
            position_binder_ident(|| resume, || WpdaState::Unwinding, lex_one)
        else {
            panic!("list ident must fork")
        };
        assert!(matches!(
            branches[0].action_kind,
            ForkActionKind::GuardedConsumeBinderIdentAndReplace { start_scope: false }
        ));
    }

    #[test]
    fn original_rule_continuations_and_strict_child_goal_are_retained() {
        let expected_marker = StackSymbolV2::rule_at(2, 3, 4, Some(5));
        let WpdaStepAction::ReplaceAndPush {
            replace_symbol,
            push_symbol,
            weight,
            new_state,
        } = rule_parameter(2, 3, 4, 5, 6, 7, 8, lex_one)
        else {
            panic!("original parameter leaf must replace and push")
        };
        assert_eq!(replace_symbol, expected_marker);
        assert_eq!(push_symbol, StackSymbolV2::category_entry_goal(6));
        assert_eq!(weight, lex_one());
        assert!(matches!(new_state, WpdaState::PrefixDispatch { pos: 7, cur_bp: 8 }));
        let WpdaStepAction::ReplaceAndPush {
            replace_symbol,
            push_symbol,
            weight,
            new_state,
        } = rule_collection_parameter(2, 3, 4, 5, 9, 7, lex_one)
        else {
            panic!("original collection leaf must replace and push")
        };
        assert_eq!(replace_symbol, expected_marker);
        assert_eq!(push_symbol, StackSymbolV2::collection_marker(2, 3, 9, 0));
        assert_eq!(weight, lex_one());
        assert!(matches!(new_state, WpdaState::PrefixDispatch { pos: 7, cur_bp: 0 }));
        let WpdaStepAction::ParsePredicate { replace_symbol, weight, new_state } =
            rule_guard(2, 3, 4, 5, 6, lex_one)
        else {
            panic!("original guard leaf must parse a predicate")
        };
        assert_eq!(replace_symbol, expected_marker);
        assert_eq!(weight, lex_one());
        assert!(matches!(
            new_state,
            WpdaState::BinderRule {
                result_src_idx: 2,
                rule_idx: 3,
                body_src_idx: 6,
                outer_bp: 5
            }
        ));
        assert!(matches!(
            rule_optional::<TropicalWeight>(2, 3, 1000, 5),
            WpdaStepAction::Advance(WpdaState::OptionalGroup {
                result_src_idx: 2,
                rule_idx: 3,
                group_idx: 1000,
                sub_pos: 0,
                outer_bp: 5
            })
        ));
        let WpdaStepAction::Pop { weight, new_state } = rule_complete(5, lex_one) else {
            panic!("original terminal leaf must pop")
        };
        assert_eq!(weight, lex_one());
        assert!(matches!(new_state, WpdaState::InfixLoop { cur_bp: 5 }));
    }

    #[test]
    fn literal_and_guest_capture_preserve_branch_payload_and_callback_order() {
        let WpdaStepAction::Fork { branches, consume_trigger } =
            rule_literal(2, 3, 4, 5, 6, "literal", Some(7), lex_one)
        else {
            panic!("original literal leaf must fork")
        };
        assert!(!consume_trigger);
        assert_eq!(branches.len(), 1);
        let branch = &branches[0];
        assert_eq!(branch.symbol, StackSymbolV2::rule_at(2, 3, 4, Some(5)));
        assert_eq!(branch.weight, lex_one());
        assert!(matches!(&branch.action_kind,
            ForkActionKind::GuardedConsumeAndReplace { expected_text, required_top_cat: Some(7) }
            if expected_text == "literal"));
        let trace = RefCell::new(Vec::new());
        let WpdaStepAction::Fork { branches, consume_trigger } = rule_guest_body(
            2,
            3,
            4,
            5,
            6,
            "Open",
            || {
                trace.borrow_mut().push("nested");
                vec!["Nested".into(), "Nested".into()]
            },
            "Close",
            || {
                trace.borrow_mut().push("weight");
                lex_one()
            },
        ) else {
            panic!("original guest leaf must fork")
        };
        assert_eq!(*trace.borrow(), ["weight", "nested"]);
        assert!(!consume_trigger);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].symbol, branch.symbol);
        assert!(matches!(&branches[0].action_kind,
            ForkActionKind::ConsumeGuestBodyAndReplace { open_kind, nested_open_kinds, close_kind }
            if open_kind == "Open" && nested_open_kinds == &["Nested", "Nested"] && close_kind == "Close"));
    }

    #[test]
    fn token_capture_retains_all_matching_edges_and_original_per_edge_schedule() {
        let tokens = MultiTokenSource::new(LexStream {
            entries: vec![LexEntry {
                byte_start: 0,
                alternatives: vec![
                    LexAlternative {
                        kind: TokenKind::Fixed("if".into()),
                        text: "if".into(),
                        end_byte: 2,
                        weight: TropicalWeight::new(0.0),
                    },
                    LexAlternative {
                        kind: TokenKind::Ident,
                        text: "if".into(),
                        end_byte: 2,
                        weight: TropicalWeight::new(1.0),
                    },
                    LexAlternative {
                        kind: TokenKind::Ident,
                        text: "i".into(),
                        end_byte: 1,
                        weight: TropicalWeight::new(2.0),
                    },
                ],
            }],
        });
        let trace = RefCell::new(Vec::new());
        let WpdaStepAction::Fork { branches, consume_trigger } = token_capture_and_replace(
            &tokens,
            0,
            "Ident",
            || {
                trace.borrow_mut().push("symbol");
                StackSymbolV2::rule_at(2, 3, 4, Some(5))
            },
            || {
                trace.borrow_mut().push("state");
                WpdaState::InfixLoop { cur_bp: 5 }
            },
            |len, cost, cat, rule, alt| {
                trace.borrow_mut().push("weight");
                lex_w_alt_with_len(len, cost, cat, rule, alt)
            },
        ) else {
            panic!("original token capture must fork")
        };
        assert!(!consume_trigger);
        assert_eq!(*trace.borrow(), ["symbol", "weight", "state", "symbol", "weight", "state"]);
        assert_eq!(branches.len(), 2);
        for (branch, (alt_idx, text)) in branches.iter().zip([(1, "if"), (2, "i")]) {
            assert!(matches!(&branch.action_kind,
                ForkActionKind::ConsumeTokenKindAtAndReplace { alt_idx: actual, kind_name, kind: TokenKind::Ident, text: actual_text, next_pos: 1 }
                if *actual == alt_idx && kind_name == "Ident" && actual_text == text));
            assert_eq!(branch.weight, lex_w_alt_with_len(text.len() as u16, 0.0, 2, 3, alt_idx));
        }
        trace.borrow_mut().clear();
        let WpdaStepAction::Fork { branches, .. } = token_capture_and_replace(
            &tokens,
            0,
            "Integer",
            || panic!("no unmatched symbol callback"),
            || panic!("no unmatched state callback"),
            |_, _, _, _, _| {
                trace.borrow_mut().push("unexpected");
                lex_one()
            },
        ) else {
            panic!("empty token capture remains an empty fork")
        };
        assert!(branches.is_empty());
        assert!(trace.borrow().is_empty());
    }
}
