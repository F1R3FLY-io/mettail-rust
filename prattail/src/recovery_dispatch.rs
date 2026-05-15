//! Stage 3.20 / L12 (Commit C, 2026-05-06): WPDS-edge-driven recovery dispatch.
//!
//! Replaces the wrapper-level `MAX_RECOVERY_ROUNDS=4` skip-to-sync retry
//! loop in facade.rs (which Commit E deletes) with intrinsic Walker
//! recovery: at every PrefixDispatch dead-end (engine_impl.rs:254
//! `_ => Idle` orphan, rewired in Commit D), `emit_recovery_fork`
//! constructs up to K=8 recovery branches by calling the existing
//! `RecoveryWfst::find_best_recovery_contextual` and `viterbi_multi_step`
//! functions. Each branch carries a `LexicographicWeight` for lex-min
//! tiebreak; the winning branch's `BuilderDelta::RecoveryEvent` /
//! `SubstituteToken` / `InsertToken` deltas replay onto the walker's
//! `recovery_events` and `WpdaMutableTokenSource` at commit_winner time.
//!
//! Per `feedback_use_wpds_disambiguation_not_heuristics.md`: every
//! recovery decision is made by Fork + lex-min, never by ad-hoc
//! sync-token heuristics or wrapper-level retry loops.

use crate::automata::TokenKind;
use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::SemiringRef;
use crate::gss::WpdaGss;
use crate::recovery::{
    FrameKind, RecoveryConfig, RecoveryContext, RecoveryWfst, RepairAction,
    viterbi_multi_step,
};
use crate::token_id::{TokenId, TokenIdMap};
use crate::gss::WpdaGssNode;
use crate::wpda_runtime::{StackSymbolV2, SymbolKind, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{
    BuilderDelta, ForkActionKind, ForkBranch, WpdaStepAction,
};
use std::collections::BTreeSet;

/// Maximum recovery branches per Fork. Bounds the cursor-explosion risk
/// at 8^N where N is recursive recovery depth (`config.max_recovery_depth`).
pub const RECOVERY_FORK_MAX_BRANCHES: usize = 8;

/// Per-grammar recovery infrastructure. Built lazily once per category
/// via `build_recovery_infra_for_category` (called from a `LazyLock` in
/// the codegen-emitted `recovery_infra_<cat>()` accessor).
pub struct RecoveryInfra {
    pub recovery_wfst: RecoveryWfst,
    pub config: RecoveryConfig,
    pub token_id_map: TokenIdMap,
    pub bracket_pairs: Vec<(String, String)>,
    pub sync_tokens: BTreeSet<TokenId>,
    pub category_name: String,
    pub category_src_idx: u16,
}

/// Walker-side runtime view. Constructed at `engine_impl.rs::step` from
/// `(_gss, frontier_top, pos, state_cat_src_idx, cur_bp)`. Used by
/// `build_recovery_context` to seed the RecoveryContext's
/// depth/frame_kind/bracket fields.
pub struct WalkerRuntimeView<'a, W: SemiringRef> {
    pub gss: &'a WpdaGss<W>,
    pub frontier_top: Option<&'a WpdaGssNode>,
    pub pos: usize,
    pub state_cat_src_idx: u16,
    pub cur_bp: u8,
}

impl<'a, W: SemiringRef> WalkerRuntimeView<'a, W> {
    /// Construct from engine_impl.rs::step parameters.
    pub fn new(
        gss: &'a WpdaGss<W>,
        frontier_top: Option<&'a WpdaGssNode>,
        pos: usize,
        state_cat_src_idx: u16,
        cur_bp: u8,
    ) -> Self {
        Self {
            gss,
            frontier_top,
            pos,
            state_cat_src_idx,
            cur_bp,
        }
    }

    /// Compute parse depth via gss.frontier_size; map frontier_top.symbol.kind
    /// to a FrameKind. Bracket counts are best-effort zero (cold-path; the
    /// Tier 2 multipliers in find_best_recovery_contextual are permissive
    /// for zero-bracket counts).
    pub fn build_recovery_context(
        &self,
        _tokens: &dyn WpdaTokenSource,
    ) -> RecoveryContext {
        let depth = self.gss.frontier_size();
        let frame_kind = derive_frame_kind(self.frontier_top);
        RecoveryContext {
            depth,
            binding_power: self.cur_bp,
            frame_kind,
            open_parens: 0,
            open_braces: 0,
            open_brackets: 0,
            dispatch_context: None,
        }
    }
}

fn derive_frame_kind(frontier_top: Option<&WpdaGssNode>) -> FrameKind {
    match frontier_top {
        None => FrameKind::Other,
        Some(node) => match node.symbol.kind {
            SymbolKind::CategoryEntry => FrameKind::Prefix,
            SymbolKind::Return => FrameKind::InfixRHS,
            SymbolKind::CollectionMarker => FrameKind::Collection,
            SymbolKind::OptionalGroupAt(_) => FrameKind::Other,
            SymbolKind::MixfixMarker => FrameKind::Mixfix,
            SymbolKind::GroupingMarker => FrameKind::Group,
            _ => FrameKind::Other,
        },
    }
}

/// Build a per-category RecoveryInfra. Invoked from codegen-emitted
/// `LazyLock<RecoveryInfra>` accessors per category.
pub fn build_recovery_infra_for_category(
    category_name: &str,
    category_src_idx: u16,
    follow_set_tokens: &[&str],
    grammar_terminals: &[&str],
    is_recursive_scc: bool,
) -> RecoveryInfra {
    let mut all_tokens: Vec<String> =
        follow_set_tokens.iter().map(|s| s.to_string()).collect();
    for t in grammar_terminals {
        all_tokens.push(t.to_string());
    }
    all_tokens.push("Eof".into());
    all_tokens.push("Ident".into());
    all_tokens.push("Integer".into());
    all_tokens.push("Float".into());
    all_tokens.push("StringLit".into());
    all_tokens.push("Boolean".into());
    all_tokens.sort();
    all_tokens.dedup();
    let token_id_map = TokenIdMap::from_names(all_tokens);

    let sync_names: Vec<String> = follow_set_tokens
        .iter()
        .filter(|t| matches!(**t, ")" | "}" | "]" | ";" | "," | "Eof"))
        .map(|s| s.to_string())
        .collect();

    let mut wfst = RecoveryWfst::new(
        category_name.to_string(),
        &sync_names,
        &token_id_map,
    );
    wfst.set_recursive_category(is_recursive_scc);

    let sync_tokens: BTreeSet<TokenId> = sync_names
        .iter()
        .filter_map(|s| token_id_map.get(s.as_str()))
        .collect();

    let bracket_pairs = vec![
        ("(".into(), ")".into()),
        ("{".into(), "}".into()),
        ("[".into(), "]".into()),
    ];

    RecoveryInfra {
        recovery_wfst: wfst,
        config: RecoveryConfig::default(),
        token_id_map,
        bracket_pairs,
        sync_tokens,
        category_name: category_name.to_string(),
        category_src_idx,
    }
}

/// Project peek'd tokens [pos..len) into TokenIds for recovery analysis.
fn project_tokens_to_ids(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    token_id_map: &TokenIdMap,
) -> Vec<TokenId> {
    let mut ids = Vec::with_capacity(tokens.len().saturating_sub(pos));
    for i in pos..tokens.len() {
        let name = match tokens.peek_kind(i) {
            Some(TokenKind::Eof) => "Eof".to_string(),
            Some(TokenKind::Ident) => "Ident".to_string(),
            Some(TokenKind::Integer) | Some(TokenKind::IntegerLit(_)) => {
                "Integer".to_string()
            }
            Some(TokenKind::Float) => "Float".to_string(),
            Some(TokenKind::True) | Some(TokenKind::False) => "Boolean".to_string(),
            Some(TokenKind::StringLit) => "StringLit".to_string(),
            Some(TokenKind::Fixed(s)) => s,
            Some(other) => format!("{:?}", other),
            None => "Eof".to_string(),
        };
        ids.push(token_id_map.get(&name).unwrap_or(TokenId::MAX));
    }
    ids
}

/// Top-level entry: emit a Fork of recovery branches at PrefixDispatch
/// dead-end. Returns `WpdaStepAction::Fork { branches }` if any recovery
/// is viable; returns `WpdaStepAction::Error(msg)` if recovery cannot
/// proceed. NEVER returns `Idle` — Idle here would loop.
pub fn emit_recovery_fork<W>(
    runtime_view: WalkerRuntimeView<'_, W>,
    tokens: &dyn WpdaTokenSource,
    infra: &RecoveryInfra,
) -> WpdaStepAction<W>
where
    W: SemiringRef + Clone + From<LexicographicWeight>,
{
    let pos = runtime_view.pos;
    let cur_bp = runtime_view.cur_bp;
    let state_cat_src_idx = runtime_view.state_cat_src_idx;

    // 1. Build RecoveryContext.
    let ctx = runtime_view.build_recovery_context(tokens);

    // 2. Project peek'd tokens to TokenIds.
    let token_ids = project_tokens_to_ids(tokens, pos, &infra.token_id_map);

    // 3. Tier 1+2+3+4 single-action via find_best_recovery_contextual.
    let single = infra.recovery_wfst.find_best_recovery_contextual(
        &token_ids,
        0,
        &ctx,
        None,
        &infra.category_name,
    );

    // 4. Multi-step Viterbi over the same windowed lattice.
    let multi = viterbi_multi_step(
        &token_ids,
        0,
        &infra.sync_tokens,
        &infra.config,
    );

    // 5. Collect candidate branches.
    let mut branches: Vec<ForkBranch<W>> = Vec::with_capacity(RECOVERY_FORK_MAX_BRANCHES);

    if let Some(s) = single {
        if let Some(b) = repair_result_to_fork_branch::<W>(
            s,
            pos,
            cur_bp,
            state_cat_src_idx,
        ) {
            branches.push(b);
        }
    }
    if let Some(seq) = multi {
        if let Some(b) = repair_sequence_to_fork_branch::<W>(
            seq,
            pos,
            cur_bp,
            state_cat_src_idx,
        ) {
            branches.push(b);
        }
    }

    if branches.is_empty() {
        // Genuinely no recovery available — surface the original parse
        // error rather than continuing in an undefined state.
        let token_text = tokens.peek_text(pos).unwrap_or("<eof>");
        return WpdaStepAction::Error(format!(
            "no recovery available at pos {}: unexpected token {:?}",
            pos, token_text
        ));
    }

    // Bounded recovery (Stage 3.20 / L12, 2026-05-06): synthesis-side
    // forward-progress filter (defense in depth — the walker's
    // apply_action::Fork mirrors this filter on the consuming side).
    // A recovery branch is allowed if either:
    //   (a) Its new_state is `PrefixDispatch { pos, .. }` with
    //       `pos > base_pos` (the cursor advances past the dead-end), OR
    //   (b) The branch carries a `BuilderDelta::InsertToken` effect
    //       (the only legitimate non-advancing repair — synthetic
    //       token splice; the live stream is mutated at commit time
    //       so the cursor's view of the world changes even though
    //       synthesis-time pos doesn't).
    let pre_count = branches.len();
    branches.retain(|b| {
        let advances = match &b.new_state {
            WpdaState::PrefixDispatch { pos: bp, .. } => *bp > pos,
            _ => true,
        };
        advances
            || matches!(
                &b.action_kind,
                ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect: BuilderDelta::InsertToken { .. }
                }
            )
    });
    if branches.is_empty() {
        return WpdaStepAction::Error(format!(
            "all {} recovery branches at pos {} violate forward-progress \
             invariant — bounded recovery refusing to dispatch",
            pre_count, pos,
        ));
    }

    branches.truncate(RECOVERY_FORK_MAX_BRANCHES);
    WpdaStepAction::Fork {
        branches,
        consume_trigger: false,
    }
}

/// Map a `RepairAction` to a `RepairAction` discriminator (mirrors
/// `RecoveryEvent::action_kind` encoding).
fn action_kind_discriminator(a: &RepairAction) -> u8 {
    match a {
        RepairAction::SkipToSync { .. } => 0,
        RepairAction::DeleteToken => 1,
        RepairAction::InsertToken { .. } => 2,
        RepairAction::SubstituteToken { .. } => 3,
        RepairAction::SwapTokens { .. } => 4,
        RepairAction::Composite { .. } => 5,
        RepairAction::CategorySwitch { .. } => 6,
    }
}

/// Build a ForkBranch from a single `crate::recovery::RepairResult`.
fn repair_result_to_fork_branch<W>(
    result: crate::recovery::RepairResult,
    base_pos: usize,
    cur_bp: u8,
    state_cat_src_idx: u16,
) -> Option<ForkBranch<W>>
where
    W: SemiringRef + From<LexicographicWeight>,
{
    let cost_tropical = result.cost.left.value();
    let action_kind_disc = action_kind_discriminator(&result.action);
    let lex_w = LexicographicWeight::from_cost(
        cost_tropical,
        state_cat_src_idx,
        action_kind_disc as u16,
    );
    let weight: W = W::from(lex_w);

    match result.action {
        RepairAction::SkipToSync { .. } => {
            let effect = BuilderDelta::RecoveryEvent {
                action_kind: action_kind_disc,
                pos: base_pos,
                cost_tropical,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch {
                    pos: base_pos + result.new_pos,
                    cur_bp,
                },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect,
                },
            })
        }
        RepairAction::DeleteToken => {
            let effect = BuilderDelta::RecoveryEvent {
                action_kind: action_kind_disc,
                pos: base_pos,
                cost_tropical,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch {
                    pos: base_pos + result.new_pos,
                    cur_bp,
                },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect,
                },
            })
        }
        RepairAction::InsertToken { token } => {
            let kind = TokenKind::Fixed(format!("{}", token));
            let text = format!("{}", token);
            let effect = BuilderDelta::InsertToken {
                pos: base_pos,
                kind,
                text,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch {
                    pos: base_pos,
                    cur_bp,
                },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect,
                },
            })
        }
        RepairAction::SubstituteToken { replacement } => {
            let kind = TokenKind::Fixed(format!("{}", replacement));
            let text = format!("{}", replacement);
            let effect = BuilderDelta::SubstituteToken {
                pos: base_pos,
                kind,
                text,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch {
                    pos: base_pos + 1,
                    cur_bp,
                },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect {
                    effect,
                },
            })
        }
        // SwapTokens / Composite / CategorySwitch are leaf actions in
        // single-step branches; not yet wired (would require additional
        // BuilderDelta variants). Skip — `find_best_recovery_contextual`
        // doesn't generate these in practice for shipped grammars.
        RepairAction::SwapTokens { .. }
        | RepairAction::Composite { .. }
        | RepairAction::CategorySwitch { .. } => None,
    }
}

/// Build a ForkBranch from a multi-step Viterbi `RepairSequence` via
/// `BuilderDelta::ApplyRecoverySequence`.
fn repair_sequence_to_fork_branch<W>(
    seq: crate::recovery::RepairSequence,
    base_pos: usize,
    cur_bp: u8,
    state_cat_src_idx: u16,
) -> Option<ForkBranch<W>>
where
    W: SemiringRef + From<LexicographicWeight>,
{
    if seq.actions.is_empty() {
        return None;
    }
    let cost_tropical = seq.total_cost.left.value();
    let final_pos = seq.new_pos;
    let weight: W = W::from(LexicographicWeight::from_cost(
        cost_tropical,
        state_cat_src_idx,
        5, // Composite discriminator
    ));
    let effect = BuilderDelta::ApplyRecoverySequence {
        actions: std::sync::Arc::from(seq.actions.into_boxed_slice()),
        base_pos,
        total_cost_tropical: cost_tropical,
    };
    Some(ForkBranch {
        symbol: StackSymbolV2::category_entry(state_cat_src_idx),
        weight,
        new_state: WpdaState::PrefixDispatch {
            pos: base_pos + final_pos,
            cur_bp,
        },
        action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
    })
}
