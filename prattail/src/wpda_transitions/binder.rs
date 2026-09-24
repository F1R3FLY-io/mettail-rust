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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::automata::TokenKind;
    use crate::lexer_types::{LexAlternative, LexEntry, LexStream};
    use crate::wpda_runtime::{lex_one, lex_w_alt_with_len, MultiTokenSource};
    use std::cell::RefCell;

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
