//! Original collection-open transition bodies from the generated WPDA frontend.
//!
//! Static collision selection and token guards stay at their original callers.
//! State construction is lazy so weight and token observations keep their order.
use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{StackSymbolV2, WpdaState};
use crate::wpda_walker::{ForkBranch, WpdaStepAction};

pub fn singleton<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    cur_bp: &u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    new_state: impl FnOnce() -> WpdaState,
) -> WpdaStepAction<W> {
    WpdaStepAction::ConsumeAndPush {
        symbol: StackSymbolV2::collection_marker(
            // str-cast collection-infix fix (2026-06-18): capture the
            // enclosing Pratt dispatch bp (*cur_bp) on the marker so
            // the collection close resumes InfixLoop at that precedence
            // (a finalized collection joins the enclosing Pratt loop
            // like an atomic primary). Covers both the synth-paren and
            // direct-delimited open paths (shared ConsumeAndPush).
            result_src_idx,
            rule_idx,
            0,
            *cur_bp,
        ),
        weight: lex_w(0.0, result_src_idx, rule_idx),
        new_state: new_state(),
        // Phase F.8: collection open delimiter discards
        // the trigger token.
        trigger_mode: crate::wpda_walker::TriggerMode::Discard,
    }
}

pub fn projection<W: SemiringRef>(
    result_src_idx: u16,
    proj_rule: u16,
    source_src_idx: u16,
    cur_bp: &u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::rule_at(result_src_idx, proj_rule, 0, Some(*cur_bp))
            .with_kind_return(),
        weight: lex_w(
            crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
            result_src_idx,
            proj_rule,
        ),
        new_state: WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp: *cur_bp },
        // Unified Fix A (ROOT C): route the Map cross-cat
        // projection through the SINGLETON uncached push so
        // it reconciles in its OWN binder frame (not the
        // cohort broadcast that drops it). FV:
        // ForkSurvivorBinderPop.v.
        action_kind: crate::wpda_walker::ForkActionKind::PushProjectionInline,
    }
}

pub fn primary<W: SemiringRef>(
    result_src_idx: u16,
    rule_idx: u16,
    cur_bp: &u8,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    new_state: impl FnOnce() -> WpdaState,
) -> ForkBranch<W> {
    crate::wpda_walker::ForkBranch {
        symbol: StackSymbolV2::collection_marker(result_src_idx, rule_idx, 0, *cur_bp),
        weight: lex_w(0.0, result_src_idx, rule_idx),
        new_state: new_state(),
        action_kind: crate::wpda_walker::ForkActionKind::ConsumeAndPush {
            trigger_mode: crate::wpda_walker::TriggerMode::Discard,
        },
    }
}

pub fn collision<W: SemiringRef>(
    branches: impl FnOnce() -> Vec<ForkBranch<W>>,
) -> WpdaStepAction<W> {
    WpdaStepAction::Fork {
        branches: branches(),
        consume_trigger: false,
    }
}
