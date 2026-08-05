//! Stage 3.20 / L12 (Commit C, 2026-05-06): WPDS-edge-driven recovery dispatch.
//!
//! Replaces the wrapper-level `MAX_RECOVERY_ROUNDS=4` skip-to-sync retry
//! loop in facade.rs (which Commit E deletes) with intrinsic Walker
//! recovery: at every PrefixDispatch dead-end (engine_impl.rs:254
//! `_ => Idle` orphan, rewired in Commit D), `emit_recovery_fork`
//! constructs up to K=8 recovery branches by calling the existing
//! `RecoveryWfst::find_best_recovery_contextual_with_config` and
//! `viterbi_multi_step`
//! functions. Each branch carries a `LexicographicWeight` for lex-min
//! tiebreak; the winning branch's recovery `BuilderDelta`
//! (`RecoveryEvent`, `SubstituteToken`, `InsertToken`, `SwapTokens`, or
//! `ApplyRecoverySequence`) replays onto the walker's `recovery_events`
//! and `WpdaMutableTokenSource` at commit_winner time.
//!
//! Per `feedback_use_wpds_disambiguation_not_heuristics.md`: every
//! recovery decision is made by Fork + lex-min, never by ad-hoc
//! sync-token heuristics or wrapper-level retry loops.

use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::SemiringRef;
use crate::automata::TokenKind;
use crate::gss::WpdaGss;
use crate::gss::WpdaGssNode;
use crate::recovery::{
    viterbi_multi_step, FrameKind, RecoveryConfig, RecoveryContext, RecoveryWfst, RepairAction,
    RepairResult,
};
use crate::token_id::{TokenId, TokenIdMap};
use crate::wpda_runtime::{StackSymbolV2, SymbolKind, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{
    BuilderDelta, ForkActionKind, ForkBranch, ResolvedRepairAction, WpdaStepAction,
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
    pub is_recursive_scc: bool,
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
    /// configured contextual recovery multipliers are permissive for
    /// zero-bracket counts).
    ///
    /// The generated WPDA recovery-dispatch path does not currently expose
    /// the active rule-set `ContextWeight`, and
    /// `build_recovery_infra_for_category` constructs WFSTs with neutral
    /// follow contexts. If that context is wired into this path later, the
    /// cohort cache key must gain the same finite observation before
    /// `dispatch_context` is set here.
    pub fn build_recovery_context(&self, _tokens: &dyn WpdaTokenSource) -> RecoveryContext {
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
            SymbolKind::BinderListLoopAt(_) => FrameKind::Other,
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
    let mut all_tokens: Vec<String> = follow_set_tokens.iter().map(|s| s.to_string()).collect();
    for t in grammar_terminals {
        all_tokens.push(t.to_string());
    }
    all_tokens.push("Eof".into());
    all_tokens.push("Ident".into());
    all_tokens.push("Integer".into());
    all_tokens.push("Float".into());
    all_tokens.push("StringLit".into());
    all_tokens.push("Boolean".into());
    all_tokens.push("Rational".into());
    all_tokens.push("FixedPoint".into());
    all_tokens.push("Dollar".into());
    all_tokens.push("DoubleDollar".into());
    all_tokens.sort();
    all_tokens.dedup();
    let token_id_map = TokenIdMap::from_names(all_tokens);

    let sync_names: Vec<String> = follow_set_tokens
        .iter()
        .filter(|t| matches!(**t, ")" | "}" | "]" | ";" | "," | "Eof"))
        .map(|s| s.to_string())
        .collect();

    let mut wfst = RecoveryWfst::new(category_name.to_string(), &sync_names, &token_id_map);
    wfst.set_recursive_category(is_recursive_scc);

    let sync_tokens: BTreeSet<TokenId> = sync_names
        .iter()
        .filter_map(|s| token_id_map.get(s.as_str()))
        .collect();

    let bracket_pairs =
        vec![("(".into(), ")".into()), ("{".into(), "}".into()), ("[".into(), "]".into())];

    RecoveryInfra {
        recovery_wfst: wfst,
        config: RecoveryConfig::default(),
        token_id_map,
        bracket_pairs,
        sync_tokens,
        category_name: category_name.to_string(),
        category_src_idx,
        is_recursive_scc,
    }
}

/// Project peek'd tokens [pos..len) into TokenIds for recovery analysis.
fn project_tokens_to_ids(
    tokens: &dyn WpdaTokenSource,
    pos: usize,
    token_id_map: &TokenIdMap,
) -> Option<Vec<TokenId>> {
    let token_count = tokens.len();
    if pos > token_count {
        return None;
    }

    let mut ids = Vec::with_capacity(token_count - pos);
    for i in pos..token_count {
        let name = tokens
            .peek_kind(i)
            .map(recovery_token_name)
            .unwrap_or_else(|| "Eof".to_string());
        ids.push(token_id_map.get(&name).unwrap_or(TokenId::MAX));
    }
    Some(ids)
}

fn recovery_token_name(kind: TokenKind) -> String {
    match kind {
        TokenKind::Eof => "Eof".to_string(),
        TokenKind::Ident => "Ident".to_string(),
        TokenKind::Integer | TokenKind::IntegerLit(_) => "Integer".to_string(),
        TokenKind::RationalLit(_) => "Rational".to_string(),
        TokenKind::FixedPointLit(_) => "FixedPoint".to_string(),
        TokenKind::Float => "Float".to_string(),
        TokenKind::True | TokenKind::False | TokenKind::BooleanLit => "Boolean".to_string(),
        TokenKind::StringLit => "StringLit".to_string(),
        TokenKind::Fixed(text) => text,
        TokenKind::Dollar => "Dollar".to_string(),
        TokenKind::DoubleDollar => "DoubleDollar".to_string(),
        TokenKind::Custom(name) => name,
        TokenKind::LexError(kind) => format!("LexError::{:?}", kind),
    }
}

/// Exact finite identity of the recovery infrastructure inputs observed by
/// branch synthesis. The generated path uses one static infra per category,
/// but the public cached API accepts `&RecoveryInfra`; including this in the
/// cache key prevents manual or future callers from reusing entries computed
/// under a different observed token map, sync set, WFST recursive flag, or
/// recovery cost configuration. Inputs that are neutral in the generated path
/// (`dispatch_context`-gated follow contexts, simulator-only cost knobs,
/// diagnostic category names, and category-source mirrors already validated
/// in the top-level key) are intentionally omitted to avoid unnecessary cache
/// partitions.
pub fn recovery_infra_signature(
    infra: &RecoveryInfra,
) -> crate::recovery_cohort::RecoveryInfraSignature {
    recovery_infra_signature_with_config(infra, &infra.config)
}

pub fn recovery_infra_signature_with_config(
    infra: &RecoveryInfra,
    config: &RecoveryConfig,
) -> crate::recovery_cohort::RecoveryInfraSignature {
    let normalized_config = config.normalized_for_recovery_search();
    crate::recovery_cohort::RecoveryInfraSignature {
        token_ids: infra
            .token_id_map
            .iter()
            .map(|(name, id)| (name.to_string(), id))
            .collect(),
        sync_tokens: infra.sync_tokens.iter().copied().collect(),
        config: crate::recovery_cohort::RecoveryConfigSignature::from_config(&normalized_config),
        wfst: recovery_wfst_signature(&infra.recovery_wfst),
    }
}

fn recovery_wfst_signature(wfst: &RecoveryWfst) -> crate::recovery_cohort::RecoveryWfstSignature {
    let mut prediction_discounts: Vec<(TokenId, u64)> = wfst
        .prediction_discounts()
        .iter()
        .map(|(&token, &discount)| (token, discount.to_bits()))
        .collect();
    prediction_discounts.sort_by_key(|&(token, _)| token);

    crate::recovery_cohort::RecoveryWfstSignature {
        token_ids: wfst
            .token_map()
            .iter()
            .map(|(name, id)| (name.to_string(), id))
            .collect(),
        sync_tokens: wfst.sync_tokens().iter().copied().collect(),
        prediction_discounts,
        bracket_mismatch_ids: wfst.bracket_mismatch_ids().iter().copied().collect(),
        recursive_category: wfst.is_recursive_category(),
    }
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
    emit_recovery_fork_with_config(runtime_view, tokens, infra, &infra.config)
}

pub fn emit_recovery_fork_with_config<W>(
    runtime_view: WalkerRuntimeView<'_, W>,
    tokens: &dyn WpdaTokenSource,
    infra: &RecoveryInfra,
    config: &RecoveryConfig,
) -> WpdaStepAction<W>
where
    W: SemiringRef + Clone + From<LexicographicWeight>,
{
    let normalized_config = config.normalized_for_recovery_search();
    let config = &normalized_config;
    if let Err(msg) = validate_recovery_infra_matches_view(&runtime_view, infra) {
        return WpdaStepAction::Error(msg);
    }
    if config.max_recovery_depth == 0 {
        return WpdaStepAction::Error(format!(
            "recovery disabled for category {} at pos {}",
            infra.category_name, runtime_view.pos,
        ));
    }

    let pos = runtime_view.pos;
    let cur_bp = runtime_view.cur_bp;
    let state_cat_src_idx = runtime_view.state_cat_src_idx;

    // 1. Build RecoveryContext.
    let ctx = runtime_view.build_recovery_context(tokens);

    // 2. Project peek'd tokens to TokenIds.
    let Some(token_ids) = project_tokens_to_ids(tokens, pos, &infra.token_id_map) else {
        return WpdaStepAction::Error(format!(
            "recovery dispatch position {} is past token window length {}",
            pos,
            tokens.len(),
        ));
    };

    // 3. Tier 1+2+3+4 single-action via configured contextual recovery.
    // Select the cheapest candidate that can survive the bounded-recovery
    // forward-progress gate. Otherwise a zero-token SkipToSync at an
    // already-synchronizing token can suppress a valid advancing repair and
    // then be discarded by the gate below.
    let single = infra
        .recovery_wfst
        .find_best_recovery_contextual_with_config_filtered(
            &token_ids,
            0,
            &ctx,
            None,
            &infra.category_name,
            config,
            |result| repair_result_allows_recovery_dispatch(result, 0),
        );

    // 4. Multi-step Viterbi over the same windowed lattice.
    let multi = viterbi_multi_step(&token_ids, 0, &infra.sync_tokens, config);

    // 5. Collect candidate branches.
    let mut branches: Vec<ForkBranch<W>> = Vec::with_capacity(RECOVERY_FORK_MAX_BRANCHES);

    if let Some(s) = single {
        if let Some(b) = repair_result_to_fork_branch::<W>(
            s,
            pos,
            cur_bp,
            state_cat_src_idx,
            &infra.token_id_map,
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
            &infra.token_id_map,
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
    //   (b) The branch carries a direct `BuilderDelta::InsertToken` effect
    //       or an `ApplyRecoverySequence` containing an insert (the only
    //       legitimate non-advancing repair — synthetic token splice; the
    //       live stream is mutated at commit time so the cursor's view of
    //       the world changes even though synthesis-time pos doesn't).
    let pre_count = branches.len();
    branches.retain(|b| {
        let advances = match &b.new_state {
            WpdaState::PrefixDispatch { pos: bp, .. } => *bp > pos,
            _ => true,
        };
        advances
            || matches!(
                &b.action_kind,
                ForkActionKind::ConsumeAndReplaceWithEffect { effect }
                    if recovery_effect_allows_non_advancing(effect)
            )
    });
    if branches.is_empty() {
        return WpdaStepAction::Error(format!(
            "all {} recovery branches at pos {} violate forward-progress \
             invariant — bounded recovery refusing to dispatch",
            pre_count, pos,
        ));
    }

    debug_assert!(
        branches.len() <= RECOVERY_FORK_MAX_BRANCHES,
        "current recovery synthesis emits at most single-step and multi-step \
         candidates; extending it requires an explicit ranking policy before \
         the formal branch cap is reachable",
    );
    branches.truncate(RECOVERY_FORK_MAX_BRANCHES);
    WpdaStepAction::Fork { branches, consume_trigger: false }
}

fn recovery_effect_allows_non_advancing(effect: &BuilderDelta) -> bool {
    match effect {
        BuilderDelta::InsertToken { .. } => true,
        BuilderDelta::ApplyRecoverySequence { actions, .. } => actions
            .iter()
            .any(|action| matches!(action, ResolvedRepairAction::InsertToken { .. })),
        _ => false,
    }
}

fn repair_result_allows_recovery_dispatch(
    result: &RepairResult,
    recovery_window_pos: usize,
) -> bool {
    result.new_pos > recovery_window_pos || repair_action_contains_insert(&result.action)
}

fn repair_action_contains_insert(action: &RepairAction) -> bool {
    match action {
        RepairAction::InsertToken { .. } => true,
        RepairAction::Composite { steps } => steps.iter().any(repair_action_contains_insert),
        _ => false,
    }
}

/// Phase F.13 Task #117 (2026-05-23): cohort-shared variant of
/// `emit_recovery_fork`.
///
/// On a cache hit, reuses the prior cohort member's branches without
/// re-running the WFST search; on a miss, computes via
/// `emit_recovery_fork` then inserts into the cache.
///
/// **Soundness:** the recovery work depends only on inputs represented by
/// the `RecoveryDispatchKey` or on parse-stable globals. The key records
/// `(pos, state_cat_src_idx, cur_bp)`, the configured recovery-depth class,
/// and the cursor-specific `runtime_view.frontier_top` cost observation via
/// `frame_kind_class`; `tokens` and `infra` are shared for a single parse.
/// Cohort members may still differ in their per-cursor `recovery_depth` and
/// `visited_recovery` sets, both gated by the existing
/// `apply_action_to_cursor::Fork` arm AFTER the recovery fork is
/// constructed. The generated path also keeps `dispatch_context` absent; if
/// active-rule context filtering is integrated later, the cache key must be
/// widened first. See `recovery_cohort` module docs for the full
/// equivalence-class argument.
pub fn emit_recovery_fork_cached<W>(
    runtime_view: WalkerRuntimeView<'_, W>,
    tokens: &dyn WpdaTokenSource,
    infra: &RecoveryInfra,
    cache: &mut crate::recovery_cohort::RecoveryCohortCache<W>,
) -> WpdaStepAction<W>
where
    W: SemiringRef + Clone + From<LexicographicWeight>,
{
    emit_recovery_fork_cached_with_config(runtime_view, tokens, infra, &infra.config, cache)
}

pub fn emit_recovery_fork_cached_with_config<W>(
    runtime_view: WalkerRuntimeView<'_, W>,
    tokens: &dyn WpdaTokenSource,
    infra: &RecoveryInfra,
    config: &RecoveryConfig,
    cache: &mut crate::recovery_cohort::RecoveryCohortCache<W>,
) -> WpdaStepAction<W>
where
    W: SemiringRef + Clone + From<LexicographicWeight>,
{
    let normalized_config = config.normalized_for_recovery_search();
    let config = &normalized_config;
    if let Err(msg) = validate_recovery_infra_matches_view(&runtime_view, infra) {
        return WpdaStepAction::Error(msg);
    }

    // Mirror the inputs `build_recovery_context` and the WFST search
    // observe. The WFST never uses exact depth directly; it only asks
    // threshold questions from `RecoveryConfig`, so the key records the
    // finite configured depth class instead of raw frontier size.
    let frame_kind = derive_frame_kind(runtime_view.frontier_top);
    let frame_kind_class = crate::recovery_cohort::recovery_frame_kind_class(frame_kind);
    let depth_class =
        crate::recovery_cohort::recovery_depth_class(runtime_view.gss.frontier_size(), config);
    let infra_signature = recovery_infra_signature_with_config(infra, config);
    let key = crate::recovery_cohort::RecoveryDispatchKey::new(
        runtime_view.pos,
        runtime_view.state_cat_src_idx,
        runtime_view.cur_bp,
        frame_kind_class,
        depth_class,
        infra_signature,
    );
    use crate::recovery_cohort::RecoveryCacheLookup;
    match cache.lookup(&key) {
        RecoveryCacheLookup::Hit { branches } => {
            WpdaStepAction::Fork { branches, consume_trigger: false }
        },
        RecoveryCacheLookup::ErrorHit { msg } => WpdaStepAction::Error(msg),
        RecoveryCacheLookup::Miss => {
            let result = emit_recovery_fork_with_config(runtime_view, tokens, infra, config);
            match &result {
                WpdaStepAction::Fork { branches, .. } => {
                    cache.insert(key, branches.clone(), None);
                },
                WpdaStepAction::Error(msg) => {
                    cache.insert(key, Vec::new(), Some(msg.clone()));
                },
                _ => {
                    // emit_recovery_fork only returns Fork|Error per its
                    // documented contract; this arm is unreachable. We
                    // deliberately do NOT insert on the unexpected
                    // result so subsequent cohort members re-attempt.
                },
            }
            result
        },
    }
}

fn validate_recovery_infra_matches_view<W>(
    runtime_view: &WalkerRuntimeView<'_, W>,
    infra: &RecoveryInfra,
) -> Result<(), String>
where
    W: SemiringRef,
{
    if runtime_view.state_cat_src_idx == infra.category_src_idx {
        return Ok(());
    }

    Err(format!(
        "recovery infra/category mismatch: PrefixDispatch category {} but infra {} ({})",
        runtime_view.state_cat_src_idx, infra.category_src_idx, infra.category_name
    ))
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

fn validate_direct_repair_result_target(action: &RepairAction, new_pos: usize) -> Option<()> {
    let expected_target = match action {
        RepairAction::SkipToSync { skip_count, .. } => *skip_count,
        RepairAction::DeleteToken => 1,
        RepairAction::InsertToken { .. } => 0,
        RepairAction::SubstituteToken { .. } => 1,
        RepairAction::SwapTokens { pos_a, pos_b } => {
            if (*pos_a).min(*pos_b) != 0 || (*pos_a).max(*pos_b) != 1 {
                return None;
            }
            2
        },
        RepairAction::Composite { .. } | RepairAction::CategorySwitch { .. } => return Some(()),
    };

    (new_pos == expected_target).then_some(())
}

fn recovery_token_payload(
    token_id_map: &TokenIdMap,
    token: TokenId,
) -> Option<(TokenKind, String)> {
    let name = token_id_map.name(token)?;
    let kind = match name {
        "Eof" => TokenKind::Eof,
        "Ident" => TokenKind::Ident,
        "Integer" => TokenKind::Integer,
        "Rational" => TokenKind::RationalLit("Rational".to_string()),
        "FixedPoint" => TokenKind::FixedPointLit("FixedPoint".to_string()),
        "Float" => TokenKind::Float,
        "StringLit" => TokenKind::StringLit,
        "Boolean" => TokenKind::True,
        "Dollar" => TokenKind::Dollar,
        "DoubleDollar" => TokenKind::DoubleDollar,
        other => TokenKind::Fixed(other.to_string()),
    };
    let text = match name {
        "Eof" => String::new(),
        "Ident" => "_".to_string(),
        "Integer" => "0".to_string(),
        "Rational" => "0r".to_string(),
        "FixedPoint" => "0.0p".to_string(),
        "Float" => "0.0".to_string(),
        "StringLit" => "\"\"".to_string(),
        "Boolean" => "true".to_string(),
        "Dollar" => "$_".to_string(),
        "DoubleDollar" => "$$_(".to_string(),
        _ => name.to_string(),
    };
    Some((kind, text))
}

/// Build a ForkBranch from a single `crate::recovery::RepairResult`.
fn repair_result_to_fork_branch<W>(
    result: crate::recovery::RepairResult,
    base_pos: usize,
    cur_bp: u8,
    state_cat_src_idx: u16,
    token_id_map: &TokenIdMap,
) -> Option<ForkBranch<W>>
where
    W: SemiringRef + From<LexicographicWeight>,
{
    validate_direct_repair_result_target(&result.action, result.new_pos)?;

    let cost_tropical = result.cost.left.value();
    let action_kind_disc = action_kind_discriminator(&result.action);
    let lex_w =
        LexicographicWeight::from_cost(cost_tropical, state_cat_src_idx, action_kind_disc as u16);
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
                new_state: WpdaState::PrefixDispatch { pos: base_pos + result.new_pos, cur_bp },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
            })
        },
        RepairAction::DeleteToken => {
            let effect = BuilderDelta::RecoveryEvent {
                action_kind: action_kind_disc,
                pos: base_pos,
                cost_tropical,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch { pos: base_pos + result.new_pos, cur_bp },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
            })
        },
        RepairAction::InsertToken { token } => {
            let (kind, text) = recovery_token_payload(token_id_map, token)?;
            let effect = BuilderDelta::InsertToken { pos: base_pos, kind, text };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch { pos: base_pos, cur_bp },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
            })
        },
        RepairAction::SubstituteToken { replacement } => {
            let (kind, text) = recovery_token_payload(token_id_map, replacement)?;
            let effect = BuilderDelta::SubstituteToken { pos: base_pos, kind, text };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch { pos: base_pos + 1, cur_bp },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
            })
        },
        RepairAction::SwapTokens { pos_a, pos_b } => {
            let effect = BuilderDelta::SwapTokens {
                pos_a: base_pos + pos_a,
                pos_b: base_pos + pos_b,
                cost_tropical,
            };
            Some(ForkBranch {
                symbol: StackSymbolV2::category_entry(state_cat_src_idx),
                weight,
                new_state: WpdaState::PrefixDispatch { pos: base_pos + result.new_pos, cur_bp },
                action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
            })
        },
        action @ RepairAction::Composite { .. } => composite_steps_to_fork_branch::<W>(
            action
                .into_composite_steps()
                .expect("matched composite action without steps"),
            base_pos,
            result.new_pos,
            cur_bp,
            state_cat_src_idx,
            cost_tropical,
            weight,
            token_id_map,
        ),
        // CategorySwitch needs a real category-transition edge from the
        // generated engine. This recovery-dispatch module cannot synthesize
        // that transition without an action entry, so it does not emit an
        // unreplayable branch.
        RepairAction::CategorySwitch { .. } => None,
    }
}

fn flatten_repair_steps(
    action: RepairAction,
    token_id_map: &TokenIdMap,
    out: &mut Vec<ResolvedRepairAction>,
) -> Option<()> {
    match action {
        action @ RepairAction::Composite { .. } => {
            for step in action
                .into_composite_steps()
                .expect("matched composite action without steps")
            {
                flatten_repair_steps(step, token_id_map, out)?;
            }
        },
        RepairAction::SkipToSync { skip_count, .. } => {
            out.push(ResolvedRepairAction::SkipToSync { skip_count });
        },
        RepairAction::DeleteToken => out.push(ResolvedRepairAction::DeleteToken),
        RepairAction::InsertToken { token } => {
            let (kind, text) = recovery_token_payload(token_id_map, token)?;
            out.push(ResolvedRepairAction::InsertToken { kind, text });
        },
        RepairAction::SubstituteToken { replacement } => {
            let (kind, text) = recovery_token_payload(token_id_map, replacement)?;
            out.push(ResolvedRepairAction::SubstituteToken { kind, text });
        },
        RepairAction::SwapTokens { pos_a, pos_b } => {
            out.push(ResolvedRepairAction::SwapTokens { pos_a, pos_b });
        },
        RepairAction::CategorySwitch { .. } => return None,
    }
    Some(())
}

fn resolved_repair_sequence_target(actions: &[ResolvedRepairAction]) -> Option<usize> {
    let mut cur_pos = 0usize;
    for action in actions {
        match action {
            ResolvedRepairAction::SkipToSync { skip_count } => {
                cur_pos = cur_pos.checked_add(*skip_count)?;
            },
            ResolvedRepairAction::DeleteToken | ResolvedRepairAction::SubstituteToken { .. } => {
                cur_pos = cur_pos.checked_add(1)?;
            },
            ResolvedRepairAction::InsertToken { .. } => {},
            ResolvedRepairAction::SwapTokens { pos_a, pos_b } => {
                let swap_target = pos_a.max(pos_b).checked_add(1)?;
                cur_pos = cur_pos.max(swap_target);
            },
        }
    }
    Some(cur_pos)
}

fn composite_steps_to_fork_branch<W>(
    steps: Vec<RepairAction>,
    base_pos: usize,
    new_pos: usize,
    cur_bp: u8,
    state_cat_src_idx: u16,
    cost_tropical: f64,
    weight: W,
    token_id_map: &TokenIdMap,
) -> Option<ForkBranch<W>>
where
    W: SemiringRef,
{
    let mut flat = Vec::new();
    for step in steps {
        flatten_repair_steps(step, token_id_map, &mut flat)?;
    }
    if flat.is_empty() {
        return None;
    }
    if resolved_repair_sequence_target(&flat)? != new_pos {
        return None;
    }
    let target_pos = base_pos + new_pos;
    let effect = BuilderDelta::ApplyRecoverySequence {
        actions: std::sync::Arc::from(flat.into_boxed_slice()),
        base_pos,
        target_pos,
        total_cost_tropical: cost_tropical,
    };
    Some(ForkBranch {
        symbol: StackSymbolV2::category_entry(state_cat_src_idx),
        weight,
        new_state: WpdaState::PrefixDispatch { pos: target_pos, cur_bp },
        action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
    })
}

/// Build a ForkBranch from a multi-step Viterbi `RepairSequence` via
/// `BuilderDelta::ApplyRecoverySequence`.
fn repair_sequence_to_fork_branch<W>(
    seq: crate::recovery::RepairSequence,
    base_pos: usize,
    cur_bp: u8,
    state_cat_src_idx: u16,
    token_id_map: &TokenIdMap,
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
    let mut actions = Vec::with_capacity(seq.actions.len());
    for action in seq.actions {
        flatten_repair_steps(action, token_id_map, &mut actions)?;
    }
    if actions.is_empty() {
        return None;
    }
    if resolved_repair_sequence_target(&actions)? != final_pos {
        return None;
    }
    let target_pos = base_pos + final_pos;
    let effect = BuilderDelta::ApplyRecoverySequence {
        actions: std::sync::Arc::from(actions.into_boxed_slice()),
        base_pos,
        target_pos,
        total_cost_tropical: cost_tropical,
    };
    Some(ForkBranch {
        symbol: StackSymbolV2::category_entry(state_cat_src_idx),
        weight,
        new_state: WpdaState::PrefixDispatch { pos: target_pos, cur_bp },
        action_kind: ForkActionKind::ConsumeAndReplaceWithEffect { effect },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wpda_runtime::SliceTokenSource;

    #[test]
    fn recovery_token_payload_resolves_fixed_and_eof_tokens() {
        let map = TokenIdMap::from_names(vec![")".to_string(), "Eof".to_string()]);
        let close = map.get(")").expect("close token");
        let eof = map.get("Eof").expect("eof token");

        let (close_kind, close_text) =
            recovery_token_payload(&map, close).expect("resolved close token");
        assert_eq!(close_kind, TokenKind::Fixed(")".into()));
        assert_eq!(close_text, ")");

        let (eof_kind, eof_text) = recovery_token_payload(&map, eof).expect("resolved eof token");
        assert_eq!(eof_kind, TokenKind::Eof);
        assert_eq!(eof_text, "");
    }

    #[test]
    fn recovery_token_payload_resolves_builtin_literal_texts() {
        let map = TokenIdMap::from_names(vec![
            "Ident".to_string(),
            "Integer".to_string(),
            "Rational".to_string(),
            "FixedPoint".to_string(),
            "Float".to_string(),
            "StringLit".to_string(),
            "Boolean".to_string(),
            "Dollar".to_string(),
            "DoubleDollar".to_string(),
        ]);

        let cases = [
            ("Ident", TokenKind::Ident, "_"),
            ("Integer", TokenKind::Integer, "0"),
            ("Rational", TokenKind::RationalLit("Rational".into()), "0r"),
            ("FixedPoint", TokenKind::FixedPointLit("FixedPoint".into()), "0.0p"),
            ("Float", TokenKind::Float, "0.0"),
            ("StringLit", TokenKind::StringLit, "\"\""),
            ("Boolean", TokenKind::True, "true"),
            ("Dollar", TokenKind::Dollar, "$_"),
            ("DoubleDollar", TokenKind::DoubleDollar, "$$_("),
        ];

        for (name, expected_kind, expected_text) in cases {
            let token = map.get(name).expect("token id");
            let (kind, text) = recovery_token_payload(&map, token).expect("resolved token");
            assert_eq!(kind, expected_kind, "kind for {}", name);
            assert_eq!(text, expected_text, "text for {}", name);
        }
    }

    #[test]
    fn project_tokens_to_ids_normalizes_builtin_families() {
        let map = TokenIdMap::from_names(vec![
            "Boolean".to_string(),
            "Rational".to_string(),
            "FixedPoint".to_string(),
            "Dollar".to_string(),
            "DoubleDollar".to_string(),
            "CustomName".to_string(),
        ]);
        let kinds = [
            TokenKind::BooleanLit,
            TokenKind::RationalLit("BigRat".into()),
            TokenKind::FixedPointLit("Fixed".into()),
            TokenKind::Dollar,
            TokenKind::DoubleDollar,
            TokenKind::Custom("CustomName".into()),
        ];
        let texts = ["yeap", "1r/2r", "3.14p", "$x", "$$x(", "payload"];
        let src = SliceTokenSource::with_texts(&kinds, &texts);

        let ids = project_tokens_to_ids(&src, 0, &map).expect("in-bounds token window");

        assert_eq!(ids[0], map.get("Boolean").expect("Boolean"));
        assert_eq!(ids[1], map.get("Rational").expect("Rational"));
        assert_eq!(ids[2], map.get("FixedPoint").expect("FixedPoint"));
        assert_eq!(ids[3], map.get("Dollar").expect("Dollar"));
        assert_eq!(ids[4], map.get("DoubleDollar").expect("DoubleDollar"));
        assert_eq!(ids[5], map.get("CustomName").expect("CustomName"));
    }

    #[test]
    fn project_tokens_to_ids_rejects_positions_past_input() {
        let map = TokenIdMap::from_names(vec!["Ident".to_string(), "Eof".to_string()]);
        let kinds = [TokenKind::Ident];
        let texts = ["x"];
        let src = SliceTokenSource::with_texts(&kinds, &texts);

        let eof_window = project_tokens_to_ids(&src, src.len(), &map)
            .expect("pos == len is a valid empty recovery window");
        assert!(eof_window.is_empty());

        assert!(
            project_tokens_to_ids(&src, src.len() + 1, &map).is_none(),
            "positions past the token window must not be normalized to EOF",
        );
    }

    #[test]
    fn generated_recovery_infra_has_neutral_follow_contexts() {
        let infra =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnly"], true);

        assert!(
            infra.recovery_wfst.follow_contexts().is_empty(),
            "generated recovery infra does not currently provide active-rule \
             follow contexts; cache equivalence relies on dispatch_context \
             staying absent in WalkerRuntimeView",
        );
    }

    #[test]
    fn recovery_infra_signature_observes_branch_synthesis_inputs() {
        let base =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        let token_map_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyB"], true);
        let recursion_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], false);
        let mut config_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        config_changed.config.insert_cost += 1.0;
        let mut max_depth_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        max_depth_changed.config.max_recovery_depth = 0;
        let mut wfst_recursion_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        wfst_recursion_changed
            .recovery_wfst
            .set_recursive_category(false);
        let mut prediction_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        let eof = prediction_changed
            .token_id_map
            .get("Eof")
            .expect("Eof token");
        let mut discounts = std::collections::HashMap::new();
        discounts.insert(eof, 0.5);
        prediction_changed
            .recovery_wfst
            .set_prediction_discounts(discounts);
        let mut bracket_mismatch_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        let mut bracket_mismatch_ids = std::collections::BTreeSet::new();
        bracket_mismatch_ids.insert(eof);
        bracket_mismatch_changed
            .recovery_wfst
            .set_bracket_mismatch_ids(bracket_mismatch_ids);

        let base_signature = recovery_infra_signature(&base);

        assert_ne!(base_signature, recovery_infra_signature(&token_map_changed));
        assert_ne!(base_signature, recovery_infra_signature(&recursion_changed));
        assert_ne!(base_signature, recovery_infra_signature(&config_changed));
        assert_ne!(base_signature, recovery_infra_signature(&max_depth_changed));
        assert_ne!(base_signature, recovery_infra_signature(&wfst_recursion_changed));
        assert_ne!(base_signature, recovery_infra_signature(&prediction_changed));
        assert_ne!(base_signature, recovery_infra_signature(&bracket_mismatch_changed));
    }

    #[test]
    fn recovery_infra_signature_ignores_branch_neutral_inputs() {
        let base =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        let mut neutral_config_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        neutral_config_changed.config.simulation_valid_mult += 1.0;
        neutral_config_changed.config.simulation_fail_penalty += 1.0;
        neutral_config_changed.config.cascade_window += 1;
        neutral_config_changed.config.adaptive_weight_threshold += 1.0;
        neutral_config_changed.config.deterministic_skip_discount += 1.0;
        neutral_config_changed.config.ambiguous_insert_discount += 1.0;
        let mut bracket_policy_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        bracket_policy_changed
            .bracket_pairs
            .push(("<".to_string(), ">".to_string()));
        let mut follow_context_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        let eof = follow_context_changed
            .token_id_map
            .get("Eof")
            .expect("Eof token");
        let mut follow_contexts = std::collections::HashMap::new();
        follow_contexts.insert(eof, crate::automata::semiring::ContextWeight::singleton(2));
        follow_context_changed
            .recovery_wfst
            .set_follow_contexts(follow_contexts);
        let category_name_changed = build_recovery_infra_for_category(
            "RenamedExpr",
            0,
            &[";", "Eof"],
            &["__TestOnlyA"],
            true,
        );
        let mut outer_recursive_mirror_changed =
            build_recovery_infra_for_category("Expr", 0, &[";", "Eof"], &["__TestOnlyA"], true);
        outer_recursive_mirror_changed.is_recursive_scc = false;

        let base_signature = recovery_infra_signature(&base);

        assert_eq!(
            base_signature,
            recovery_infra_signature(&neutral_config_changed),
            "simulator-only, adaptive, cascade, and consumer-side depth fields \
             other than max_recovery_depth do not influence emit_recovery_fork \
             branch synthesis",
        );
        assert_eq!(
            base_signature,
            recovery_infra_signature(&bracket_policy_changed),
            "RecoveryInfra.bracket_pairs is not read by branch synthesis",
        );
        assert_eq!(
            base_signature,
            recovery_infra_signature(&follow_context_changed),
            "WFST follow contexts are neutral while WalkerRuntimeView keeps \
             dispatch_context absent",
        );
        assert_eq!(
            base_signature,
            recovery_infra_signature(&category_name_changed),
            "category names are diagnostic-only in the generated recovery path \
             because no simulator is supplied",
        );
        assert_eq!(
            base_signature,
            recovery_infra_signature(&outer_recursive_mirror_changed),
            "branch synthesis reads the inner WFST recursive flag; the outer \
             construction-time mirror must not split the cache",
        );
    }

    #[test]
    fn walker_runtime_view_recovery_context_observes_frame_without_dispatch_context() {
        let mut gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let top_id = gss.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(11),
        });
        gss.push_frontier(top_id);
        let frontier_top = gss.node(top_id);
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);

        let view = WalkerRuntimeView::new(&gss, frontier_top, 3, 11, 7);
        let ctx = view.build_recovery_context(&tokens);

        assert_eq!(ctx.depth, 1);
        assert_eq!(ctx.binding_power, 7);
        assert_eq!(ctx.frame_kind, FrameKind::Prefix);
        assert!(
            ctx.dispatch_context.is_none(),
            "the generated WPDA path must not set dispatch_context unless the \
             recovery cohort cache key also records its observation",
        );
    }

    #[test]
    fn emit_recovery_fork_cached_reuses_neutral_frame_kind_class() {
        let mut gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let top_id = gss.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        gss.push_frontier(top_id);
        let frontier_top = gss.node(top_id);
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let infra = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let prefix_view = WalkerRuntimeView::new(&gss, frontier_top, 0, 0, 0);
        let _ = emit_recovery_fork_cached::<LexicographicWeight>(
            prefix_view,
            &tokens,
            &infra,
            &mut cache,
        );
        assert_eq!(cache.registrations_total, 1);

        let other_view = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ = emit_recovery_fork_cached::<LexicographicWeight>(
            other_view, &tokens, &infra, &mut cache,
        );
        assert_eq!(
            cache.registrations_total, 1,
            "Prefix and Other frame kinds have identical generated-path recovery \
             cost observations and should share the recovery cache entry",
        );
        assert_eq!(cache.cache_hits_total, 1);
    }

    #[test]
    fn emit_recovery_fork_rejects_category_infra_mismatch() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let view = WalkerRuntimeView::new(&gss, None, 0, 7, 0);
        let infra = build_recovery_infra_for_category("Other", 8, &["Eof"], &["Ident"], true);
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);

        let action = emit_recovery_fork::<LexicographicWeight>(view, &tokens, &infra);

        let WpdaStepAction::Error(msg) = action else {
            panic!("category/infra mismatch must reject before recovery synthesis");
        };
        assert!(
            msg.contains("recovery infra/category mismatch"),
            "unexpected mismatch error: {msg}",
        );
    }

    #[test]
    fn emit_recovery_fork_cached_rejects_category_infra_mismatch_without_cache_insert() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let view = WalkerRuntimeView::new(&gss, None, 0, 7, 0);
        let infra = build_recovery_infra_for_category("Other", 8, &["Eof"], &["Ident"], true);
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let action =
            emit_recovery_fork_cached::<LexicographicWeight>(view, &tokens, &infra, &mut cache);

        let WpdaStepAction::Error(msg) = action else {
            panic!("category/infra mismatch must reject before recovery cache lookup");
        };
        assert!(
            msg.contains("recovery infra/category mismatch"),
            "unexpected mismatch error: {msg}",
        );
        assert!(cache.entries.is_empty());
        assert_eq!(cache.registrations_total, 0);
    }

    #[test]
    fn emit_recovery_fork_with_config_respects_disabled_recovery() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let view = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let infra = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["Ident"], true);
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let mut config = infra.config.clone();
        config.max_recovery_depth = 0;

        let action =
            emit_recovery_fork_with_config::<LexicographicWeight>(view, &tokens, &infra, &config);

        let WpdaStepAction::Error(msg) = action else {
            panic!("max_recovery_depth=0 must disable recovery synthesis");
        };
        assert!(msg.contains("recovery disabled"), "unexpected disabled-recovery error: {msg}",);
    }

    #[test]
    fn emit_recovery_fork_rejects_position_past_input() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Ident], &["x"]);
        let infra = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["Ident"], true);
        let view = WalkerRuntimeView::new(&gss, None, tokens.len() + 1, 0, 0);

        let action = emit_recovery_fork::<LexicographicWeight>(view, &tokens, &infra);

        let WpdaStepAction::Error(msg) = action else {
            panic!("past-input recovery dispatch must reject instead of synthesizing EOF recovery");
        };
        assert!(msg.contains("past token window"), "unexpected past-input recovery error: {msg}",);
    }

    #[test]
    fn emit_recovery_fork_cached_rejects_position_past_input() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Ident], &["x"]);
        let infra = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["Ident"], true);
        let view = WalkerRuntimeView::new(&gss, None, tokens.len() + 1, 0, 0);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let action =
            emit_recovery_fork_cached::<LexicographicWeight>(view, &tokens, &infra, &mut cache);

        let WpdaStepAction::Error(msg) = action else {
            panic!("cached past-input recovery dispatch must reject");
        };
        assert!(
            msg.contains("past token window"),
            "unexpected cached past-input recovery error: {msg}",
        );
        assert_eq!(cache.registrations_total, 1);
        assert_eq!(cache.entries.len(), 1);
    }

    #[test]
    fn emit_recovery_fork_cached_separates_active_config_override() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let infra = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["Ident"], true);
        let mut disabled_config = infra.config.clone();
        disabled_config.max_recovery_depth = 0;
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let default_view = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ = emit_recovery_fork_cached_with_config::<LexicographicWeight>(
            default_view,
            &tokens,
            &infra,
            &infra.config,
            &mut cache,
        );
        assert_eq!(cache.registrations_total, 1);

        let disabled_view = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let action = emit_recovery_fork_cached_with_config::<LexicographicWeight>(
            disabled_view,
            &tokens,
            &infra,
            &disabled_config,
            &mut cache,
        );
        let WpdaStepAction::Error(msg) = action else {
            panic!("disabled config must produce an error tombstone");
        };
        assert!(msg.contains("recovery disabled"), "unexpected disabled-recovery error: {msg}",);
        assert_eq!(
            cache.registrations_total, 2,
            "active config override must be part of the recovery cache key",
        );
    }

    #[test]
    fn emit_recovery_fork_cached_separates_distinct_infra_signatures() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        // Built-in recovery token families such as Ident/Integer are added
        // to every generated infra. Use sentinel fixed terminals so the
        // token-map component of the signature actually differs.
        let infra_a =
            build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnlyA"], true);
        let infra_b =
            build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnlyB"], true);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let view_a = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_a, &tokens, &infra_a, &mut cache);
        assert_eq!(cache.registrations_total, 1);
        assert_eq!(cache.entries.len(), 1);

        let view_b = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_b, &tokens, &infra_b, &mut cache);
        assert_eq!(
            cache.registrations_total, 2,
            "distinct infra signatures must not reuse the prior cached result",
        );
        assert_eq!(cache.entries.len(), 2);

        let view_b_again = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ = emit_recovery_fork_cached::<LexicographicWeight>(
            view_b_again,
            &tokens,
            &infra_b,
            &mut cache,
        );
        assert_eq!(
            cache.registrations_total, 2,
            "same infra signature should still reuse the cached result",
        );
    }

    #[test]
    fn emit_recovery_fork_cached_separates_mutated_wfst_signatures() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let infra_a = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        let mut infra_b =
            build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        infra_b.recovery_wfst.set_recursive_category(false);
        assert_eq!(
            infra_b.is_recursive_scc, true,
            "this regression mutates only the inner WFST flag; the outer \
             construction-time field stays identical",
        );
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let view_a = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_a, &tokens, &infra_a, &mut cache);
        assert_eq!(cache.registrations_total, 1);

        let view_b = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_b, &tokens, &infra_b, &mut cache);
        assert_eq!(
            cache.registrations_total, 2,
            "a WFST-local recursive-category mutation affects recovery costs \
             and must not reuse the previously cached branch set",
        );
        assert_eq!(cache.entries.len(), 2);
    }

    #[test]
    fn emit_recovery_fork_cached_reuses_follow_context_only_mutation() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let infra_a = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        let mut infra_b =
            build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        let eof = infra_b.token_id_map.get("Eof").expect("Eof token");
        let mut follow_contexts = std::collections::HashMap::new();
        follow_contexts.insert(eof, crate::automata::semiring::ContextWeight::singleton(1));
        infra_b.recovery_wfst.set_follow_contexts(follow_contexts);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let view_a = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_a, &tokens, &infra_a, &mut cache);
        assert_eq!(cache.registrations_total, 1);

        let view_b = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_b, &tokens, &infra_b, &mut cache);
        assert_eq!(
            cache.registrations_total, 1,
            "follow contexts are not cache-key inputs until dispatch_context \
             becomes part of WalkerRuntimeView",
        );
        assert_eq!(cache.entries.len(), 1);
    }

    #[test]
    fn emit_recovery_fork_cached_reuses_diagnostic_category_name_changes() {
        let gss: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let tokens = SliceTokenSource::with_texts(&[TokenKind::Eof], &[""]);
        let infra_a = build_recovery_infra_for_category("Expr", 0, &["Eof"], &["__TestOnly"], true);
        let infra_b =
            build_recovery_infra_for_category("RenamedExpr", 0, &["Eof"], &["__TestOnly"], true);
        let mut cache = crate::recovery_cohort::RecoveryCohortCache::new();

        let view_a = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_a, &tokens, &infra_a, &mut cache);
        assert_eq!(cache.registrations_total, 1);

        let view_b = WalkerRuntimeView::new(&gss, None, 0, 0, 0);
        let _ =
            emit_recovery_fork_cached::<LexicographicWeight>(view_b, &tokens, &infra_b, &mut cache);
        assert_eq!(
            cache.registrations_total, 1,
            "category names do not influence generated-path recovery branches \
             when the category source index already matches",
        );
        assert_eq!(cache.entries.len(), 1);
    }

    #[test]
    fn flatten_repair_steps_resolves_token_bearing_actions() {
        let map = TokenIdMap::from_names(vec![")".to_string(), ";".to_string()]);
        let close = map.get(")").expect("close token");
        let semi = map.get(";").expect("semi token");
        let action = RepairAction::Composite {
            steps: vec![
                RepairAction::InsertToken { token: close },
                RepairAction::SubstituteToken { replacement: semi },
                RepairAction::SkipToSync { skip_count: 2, sync_token: semi },
            ],
        };
        let mut resolved = Vec::new();

        flatten_repair_steps(action, &map, &mut resolved).expect("resolve action sequence");

        assert_eq!(
            resolved,
            vec![
                ResolvedRepairAction::InsertToken {
                    kind: TokenKind::Fixed(")".into()),
                    text: ")".into(),
                },
                ResolvedRepairAction::SubstituteToken {
                    kind: TokenKind::Fixed(";".into()),
                    text: ";".into(),
                },
                ResolvedRepairAction::SkipToSync { skip_count: 2 },
            ],
        );
    }

    #[test]
    fn repair_result_dispatch_predicate_rejects_zero_skip_without_insert() {
        let zero_skip = crate::recovery::RepairResult {
            action: RepairAction::SkipToSync { skip_count: 0, sync_token: 0 },
            new_pos: 0,
            cost: crate::recovery::costs::joint(0.0, 0),
        };
        assert!(
            !repair_result_allows_recovery_dispatch(&zero_skip, 0),
            "zero-token sync repair would be dropped by the branch gate",
        );

        let advancing_delete = crate::recovery::RepairResult {
            action: RepairAction::DeleteToken,
            new_pos: 1,
            cost: crate::recovery::costs::joint(1.0, 1),
        };
        assert!(repair_result_allows_recovery_dispatch(&advancing_delete, 0));

        let non_advancing_insert = crate::recovery::RepairResult {
            action: RepairAction::InsertToken { token: 0 },
            new_pos: 0,
            cost: crate::recovery::costs::joint(2.0, 2),
        };
        assert!(repair_result_allows_recovery_dispatch(&non_advancing_insert, 0));
    }

    #[test]
    fn repair_result_branch_rejects_inconsistent_direct_target() {
        let map = TokenIdMap::from_names(vec![")".to_string()]);
        let close = map.get(")").expect("close token");
        let malformed = crate::recovery::RepairResult {
            action: RepairAction::SubstituteToken { replacement: close },
            new_pos: 2,
            cost: crate::recovery::costs::joint(1.0, 1),
        };

        let branch: Option<ForkBranch<LexicographicWeight>> =
            repair_result_to_fork_branch(malformed, 5, 0, 7, &map);

        assert!(
            branch.is_none(),
            "direct substitute recovery must consume exactly one token; \
             mismatched RepairResult.new_pos is rejected before branch emission",
        );
    }

    #[test]
    fn repair_result_branch_rejects_non_head_direct_swap() {
        let map = TokenIdMap::from_names(vec!["Eof".to_string()]);
        let malformed = crate::recovery::RepairResult {
            action: RepairAction::SwapTokens { pos_a: 2, pos_b: 3 },
            new_pos: 4,
            cost: crate::recovery::costs::joint(1.25, 1),
        };

        let branch: Option<ForkBranch<LexicographicWeight>> =
            repair_result_to_fork_branch(malformed, 5, 0, 7, &map);

        assert!(
            branch.is_none(),
            "direct swap recovery must transpose the first two tokens of \
             the recovery window; later swaps require an explicit sequence",
        );
    }

    #[test]
    fn repair_result_branch_accepts_head_direct_swap_target() {
        let map = TokenIdMap::from_names(vec!["Eof".to_string()]);
        let swap = crate::recovery::RepairResult {
            action: RepairAction::SwapTokens { pos_a: 0, pos_b: 1 },
            new_pos: 2,
            cost: crate::recovery::costs::joint(1.25, 1),
        };

        let branch: ForkBranch<LexicographicWeight> =
            repair_result_to_fork_branch(swap, 5, 0, 7, &map).expect("direct swap branch");

        assert_eq!(branch.new_state, WpdaState::PrefixDispatch { pos: 7, cur_bp: 0 });
        let ForkActionKind::ConsumeAndReplaceWithEffect {
            effect: BuilderDelta::SwapTokens { pos_a, pos_b, .. },
        } = branch.action_kind
        else {
            panic!("expected direct swap delta");
        };
        assert_eq!((pos_a, pos_b), (5, 6));
    }

    #[test]
    fn non_advancing_recovery_effect_accepts_insert_sequence() {
        let insert_sequence = BuilderDelta::ApplyRecoverySequence {
            actions: std::sync::Arc::from(
                vec![ResolvedRepairAction::InsertToken {
                    kind: TokenKind::Fixed(";".into()),
                    text: ";".into(),
                }]
                .into_boxed_slice(),
            ),
            base_pos: 4,
            target_pos: 4,
            total_cost_tropical: 1.0,
        };
        assert!(
            recovery_effect_allows_non_advancing(&insert_sequence),
            "insert-only Viterbi sequences are non-consuming repairs and \
             must survive synthesis-side forward-progress filtering",
        );

        let delete_sequence = BuilderDelta::ApplyRecoverySequence {
            actions: std::sync::Arc::from(
                vec![ResolvedRepairAction::DeleteToken].into_boxed_slice(),
            ),
            base_pos: 4,
            target_pos: 4,
            total_cost_tropical: 1.0,
        };
        assert!(
            !recovery_effect_allows_non_advancing(&delete_sequence),
            "non-advancing sequences without an insert still violate the \
             forward-progress filter",
        );
    }

    #[test]
    fn repair_sequence_branch_carries_explicit_target_pos() {
        let map = TokenIdMap::from_names(vec![";".to_string()]);
        let semi = map.get(";").expect("semi token");
        let seq = crate::recovery::RepairSequence {
            actions: vec![
                RepairAction::DeleteToken,
                RepairAction::SkipToSync { skip_count: 1, sync_token: semi },
            ],
            new_pos: 2,
            total_cost: crate::recovery::costs::joint(1.5, 2),
            total_edits: crate::automata::semiring::EditWeight::new(2),
        };

        let branch: ForkBranch<LexicographicWeight> =
            repair_sequence_to_fork_branch(seq, 5, 0, 7, &map).expect("sequence branch");

        assert_eq!(
            branch.new_state,
            WpdaState::PrefixDispatch { pos: 7, cur_bp: 0 },
            "branch target must be base_pos + sequence.new_pos",
        );
        let ForkActionKind::ConsumeAndReplaceWithEffect {
            effect: BuilderDelta::ApplyRecoverySequence { actions, base_pos, target_pos, .. },
        } = branch.action_kind
        else {
            panic!("expected ApplyRecoverySequence branch");
        };
        assert_eq!(base_pos, 5);
        assert_eq!(target_pos, 7, "delta target_pos must mirror branch.new_state.pos",);
        assert_eq!(
            actions.as_ref(),
            &[
                ResolvedRepairAction::DeleteToken,
                ResolvedRepairAction::SkipToSync { skip_count: 1 },
            ],
        );
    }

    #[test]
    fn repair_sequence_branch_keeps_swap_positions_sequence_local() {
        let map = TokenIdMap::from_names(vec!["Eof".to_string()]);
        let seq = crate::recovery::RepairSequence {
            actions: vec![RepairAction::SwapTokens { pos_a: 0, pos_b: 1 }],
            new_pos: 2,
            total_cost: crate::recovery::costs::joint(1.25, 1),
            total_edits: crate::automata::semiring::EditWeight::new(1),
        };

        let branch: ForkBranch<LexicographicWeight> =
            repair_sequence_to_fork_branch(seq, 4, 3, 9, &map).expect("swap branch");

        assert_eq!(branch.new_state, WpdaState::PrefixDispatch { pos: 6, cur_bp: 3 },);
        let ForkActionKind::ConsumeAndReplaceWithEffect {
            effect: BuilderDelta::ApplyRecoverySequence { actions, base_pos, target_pos, .. },
        } = branch.action_kind
        else {
            panic!("expected ApplyRecoverySequence branch");
        };
        assert_eq!(base_pos, 4);
        assert_eq!(target_pos, 6);
        assert_eq!(
            actions.as_ref(),
            &[ResolvedRepairAction::SwapTokens { pos_a: 0, pos_b: 1 }],
            "ApplyRecoverySequence swap coordinates remain sequence-local; \
             replay adds base_pos exactly once",
        );
    }

    #[test]
    fn composite_branch_rejects_mismatched_replay_target() {
        let map = TokenIdMap::from_names(vec![")".to_string()]);
        let close = map.get(")").expect("close token");
        let steps = vec![
            RepairAction::DeleteToken,
            RepairAction::SkipToSync { skip_count: 1, sync_token: close },
        ];

        let branch: Option<ForkBranch<LexicographicWeight>> = composite_steps_to_fork_branch(
            steps,
            5,
            1,
            0,
            7,
            1.5,
            LexicographicWeight::from_cost(1.5, 7, 5),
            &map,
        );

        assert!(
            branch.is_none(),
            "composite branch emission must reject a supplied new_pos that \
             does not match replay of the flattened action list",
        );
    }

    #[test]
    fn composite_branch_accepts_nonadvancing_insert_target() {
        let map = TokenIdMap::from_names(vec![")".to_string()]);
        let close = map.get(")").expect("close token");
        let steps = vec![RepairAction::InsertToken { token: close }];

        let branch: ForkBranch<LexicographicWeight> = composite_steps_to_fork_branch(
            steps,
            5,
            0,
            0,
            7,
            2.0,
            LexicographicWeight::from_cost(2.0, 7, 5),
            &map,
        )
        .expect("insert-only composite branch");

        assert_eq!(branch.new_state, WpdaState::PrefixDispatch { pos: 5, cur_bp: 0 });
    }

    #[test]
    fn repair_sequence_branch_rejects_mismatched_replay_target() {
        let map = TokenIdMap::from_names(vec![";".to_string()]);
        let semi = map.get(";").expect("semi token");
        let seq = crate::recovery::RepairSequence {
            actions: vec![
                RepairAction::DeleteToken,
                RepairAction::SkipToSync { skip_count: 1, sync_token: semi },
            ],
            new_pos: 1,
            total_cost: crate::recovery::costs::joint(1.5, 2),
            total_edits: crate::automata::semiring::EditWeight::new(2),
        };

        let branch: Option<ForkBranch<LexicographicWeight>> =
            repair_sequence_to_fork_branch(seq, 5, 0, 7, &map);

        assert!(
            branch.is_none(),
            "Viterbi RepairSequence branch emission must reject a new_pos \
             that disagrees with flattened action replay",
        );
    }

    #[test]
    fn repair_sequence_branch_accepts_swap_replay_target() {
        let map = TokenIdMap::from_names(vec!["Eof".to_string()]);
        let seq = crate::recovery::RepairSequence {
            actions: vec![RepairAction::SwapTokens { pos_a: 0, pos_b: 1 }],
            new_pos: 2,
            total_cost: crate::recovery::costs::joint(1.25, 1),
            total_edits: crate::automata::semiring::EditWeight::new(1),
        };

        let branch: ForkBranch<LexicographicWeight> =
            repair_sequence_to_fork_branch(seq, 5, 0, 7, &map).expect("swap sequence branch");

        assert_eq!(branch.new_state, WpdaState::PrefixDispatch { pos: 7, cur_bp: 0 });
    }
}
