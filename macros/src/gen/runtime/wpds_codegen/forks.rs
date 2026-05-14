//! Unified Fork-emission framework — Stage 3.16/3.17/3.18 (Commit 2,
//! 2026-05-05).
//!
//! Replaces deterministic peek-and-decide patterns in WPDS codegen with
//! `WpdsStepAction::Fork` over multiple branches, letting lex-min disambiguate
//! per `feedback_use_wpds_disambiguation_not_heuristics.md`. Branches are
//! emitted unconditionally; the walker prunes branches whose subsequent steps
//! fail (matching the existing F7 multi-rule binder, F8 cross-cat projection,
//! and A.i Opt-Group Fork patterns already shipped).
//!
//! Three already-shipped Forks prove the pattern works:
//! - F7 multi-rule binder (`binder.rs:556-596`)
//! - F8 cross-cat projection (`prefix.rs:932-971`)
//! - A.i Opt-Group sub_pos:0 (`binder.rs:992-1046`)
//!
//! This module unifies the 11 remaining hacks (Cluster 1: 5 sites; Cluster 2:
//! 2 sites; Cluster 3: 3 sites — Cluster 4 #18/#19 is Commit 3, Cluster 5 is
//! Commit 4) under a small helper API.
//!
//! ## Design notes
//!
//! - **Source-order tiebreak via rule_idx.** Load-bearing per Class A.i
//!   precedent. All Forks must use rule_idx for deterministic disambiguation.
//! - **Lex-min weighting.**
//!   `LexicographicWeight::from_cost(bias, src, rule)` is the standard weight
//!   constructor for new Fork branches; per-tier bias offsets enforce
//!   inter-tier ordering on weight ties.
//! - **Cursor explosion mitigation.** Each Fork emission grows the cursor
//!   count by N; nested call sites multiply. The walker's
//!   `beam_size: Option<usize>` (already shipped at `wpds_walker.rs:289`)
//!   defaults to `Some(64)` when Cluster 3 lands.
//! - **Unconditional branch emission.** Following the F7/F8/A.i pattern,
//!   branches are pushed into the Fork unconditionally; per-branch runtime
//!   correctness is enforced when the cursor's subsequent step against the
//!   token stream either matches or transitions to Error. This is simpler
//!   than codegen-time guard evaluation and matches the WPDS principle of
//!   "emit all valid branches, let lex-min pick the survivor."

#![allow(dead_code)]

use proc_macro2::TokenStream;
use quote::quote;

// ─────── Per-cluster constants ───────────────────────────────────────────

/// Cluster 1 SKIP-branch weight bias. Reused from `EPSILON_OPT_SKIP` for
/// consistency with the canonical Opt-Group A.i Fork.
pub(crate) const SKIP_BIAS: f64 = 0.5;

/// Cluster 5 (Commit 4) base offset for recovery branches.
pub(crate) const RECOVERY_BASE: u16 = 0xFE00;

/// Cluster 3 BP-tier biases. Lower wins on lex-min; tier 0 (infix) is
/// preferred over postfix/mixfix when l_bp ties.
pub(crate) const BP_TIER_INFIX: f64 = 0.00;
pub(crate) const BP_TIER_CROSSCAT_LHS: f64 = 0.05;
pub(crate) const BP_TIER_POSTFIX: f64 = 0.10;
pub(crate) const BP_TIER_MIXFIX: f64 = 0.20;

// ─────── Branch descriptors ──────────────────────────────────────────────

/// A single Fork branch in a Cluster 1 emission. Stringly-typed via
/// TokenStream so callers retain full control of the symbol/state/action
/// expressions.
pub(crate) struct FirstSetBranch {
    /// Branch identifier for diagnostics (e.g., "close", "sep", "ident").
    pub name: &'static str,
    /// Weight bias offset (0.0 = preferred; SKIP_BIAS = deprioritized).
    pub weight_bias: f64,
    /// `result_src_idx` for the branch's weight (lex-min tiebreak component).
    pub result_src_idx: u16,
    /// `rule_idx` for the branch's weight (source-order tiebreak — load-bearing).
    pub rule_idx: u16,
    /// `StackSymbolV2` expression to push onto the GSS for this branch.
    pub symbol: TokenStream,
    /// `WpdsState` expression for the branch's `new_state`.
    pub new_state: TokenStream,
    /// `ForkActionKind` expression. Default for most Cluster 1 branches:
    /// `ForkActionKind::Push`.
    pub action_kind: TokenStream,
}

// ─────── Cluster 1 helper ────────────────────────────────────────────────

/// Cluster 1 helper. Emits a `WpdsStepAction::Fork` over the given branches
/// with `consume_trigger` semantics specified by the caller. Following the
/// F7/F8/A.i pattern, branches are emitted unconditionally — the walker
/// prunes branches whose subsequent steps fail.
///
/// Source-order tiebreak: branches are emitted in the same order as
/// `branches` parameter; per-branch `rule_idx` weight component gives
/// lower-index branches lex-min preference on tier-bias ties (see
/// `wpds_walker.rs::ForkBranch.weight`).
///
/// **Cursor-explosion mitigation.** When `branches.len() >= 2`, the emit
/// site grows the cursor count by N; nested call sites multiply. The
/// walker's `beam_size: Option<usize>` (default `Some(64)`) caps the live
/// cursor population.
pub(crate) fn emit_first_set_fork(
    branches: &[FirstSetBranch],
    consume_trigger: bool,
) -> TokenStream {
    let branch_exprs: Vec<TokenStream> = branches
        .iter()
        .map(|b| {
            let bias = b.weight_bias;
            let src = b.result_src_idx;
            let rule = b.rule_idx;
            let symbol = &b.symbol;
            let new_state = &b.new_state;
            let action_kind = &b.action_kind;
            let _name = b.name;
            quote! {
                mettail_prattail::wpds_walker::ForkBranch {
                    symbol: #symbol,
                    weight: LexicographicWeight::from_cost(#bias, #src, #rule),
                    new_state: #new_state,
                    action_kind: #action_kind,
                }
            }
        })
        .collect();

    quote! {
        WpdsStepAction::Fork {
            branches: vec![ #( #branch_exprs ),* ],
            consume_trigger: #consume_trigger,
        }
    }
}

// ─────── Cluster 2 #12 helper (lex-fork) ─────────────────────────────────

/// Cluster 2 #12 — emit a lex-Fork at PrefixDispatch top.
///
/// Wires `WpdsTokenSource::peek_alternatives(*pos)` into a Fork whose
/// branches each commit one lex alternative. Each branch's weight is
/// `from_cost_with_lex(0.0, src, rule, alt_idx)` so lex-min over alt_idx
/// preserves source-order tiebreak. Walker's existing
/// `MutableMultiTokenSource::commit_alternative` is invoked at commit_winner
/// time via `BuilderDelta::CommitLexAlternative`.
///
/// **Production semantics.** The default `SliceTokenSource::peek_alternatives`
/// returns `&[]`, so the lex-fork is dispatched only when a multi-alt token
/// source is in use (e.g., `MutableMultiTokenSource` after Stage 3.20 recovery
/// edge work in Commit 4). For default lexers, this emission is inert.
pub(crate) fn emit_lex_fork_at_prefix_dispatch(primary_src_idx: u16) -> TokenStream {
    quote! {
        // Cluster 2 #12 (Stage 3.14 / 2026-05-05): lex-Fork dispatch.
        //
        // When the active token source has multiple lex alternatives at
        // *pos, emit a Fork over them so lex-min picks the canonical
        // interpretation. `peek_alternatives` returns `&[]` for sources
        // without ambiguity (the default `SliceTokenSource`); only
        // `MutableMultiTokenSource` populates non-empty alts.
        if tokens.is_ambiguous_at(*pos) {
            let alts = tokens.peek_alternatives(*pos);
            let primary_src_for_fork: u16 = #primary_src_idx;
            let primary_src = frontier_top
                .map(|n| n.symbol.category_src_idx)
                .unwrap_or(primary_src_for_fork);
            let mut __branches: Vec<mettail_prattail::wpds_walker::ForkBranch<
                LexicographicWeight,
            >> = Vec::with_capacity(alts.len());
            for (alt_idx, alt) in alts.iter().enumerate() {
                // Mechanism γ (Stage 3.16, 2026-05-05): LexAlt action_kind
                // carries the alt's kind/text payload so the walker's
                // apply_action::Fork dispatch logs
                // BuilderDelta::CommitLexAlternative with the right
                // arguments.
                //
                // L-substrate (2026-05-13): `(alt_idx + 1) as u16` so
                // the first secondary alt gets `lex_alt_idx = 1` — the
                // primary cursor (fall-through, no Fork branch)
                // defaults to `lex_alt_idx = 0` per from_cost, so
                // tying primary-cost cursors prefer the canonical
                // longest-match (lex_alt_idx=0) over secondaries
                // (lex_alt_idx>=1) via LexicographicWeight::lex_cmp.
                //
                // M5 (2026-05-13): `next_pos` replaces `end_byte`. The
                // walker's apply uses `next_pos` to set the child's
                // `cursor.pos` directly. For LatticeTokenSource this is
                // the alt's DAG `target_node`; for linear sources the
                // trait default returns `pos + 1`. Calling
                // `tokens.next_pos(*pos, alt_idx + 1)` runs through the
                // active source's impl — correct in both cases.
                let alt_next_pos = tokens
                    .next_pos(*pos, alt_idx + 1)
                    .unwrap_or(*pos + 1);
                __branches.push(mettail_prattail::wpds_walker::ForkBranch {
                    symbol: StackSymbolV2::category_entry(primary_src),
                    weight: LexicographicWeight::from_cost_with_lex(
                        0.0, primary_src, 0, (alt_idx + 1) as u16,
                    ),
                    new_state: WpdsState::PrefixDispatch {
                        pos: alt_next_pos,
                        cur_bp: *cur_bp,
                    },
                    action_kind: mettail_prattail::wpds_walker::ForkActionKind::LexAlt {
                        alt_idx: (alt_idx + 1) as u16,
                        kind: alt.kind.clone(),
                        text: alt.text.to_string(),
                        next_pos: alt_next_pos,
                    },
                });
            }
            if !__branches.is_empty() {
                return WpdsStepAction::Fork {
                    branches: __branches,
                    consume_trigger: false,
                };
            }
        }
    }
}

// ─────── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emit_first_set_fork_three_branches_yields_fork_arm() {
        let branches = vec![
            FirstSetBranch {
                name: "close",
                weight_bias: 0.0,
                result_src_idx: 1,
                rule_idx: 0,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdsState::Unwinding },
                action_kind: quote! {
                    mettail_prattail::wpds_walker::ForkActionKind::CollectionClose
                },
            },
            FirstSetBranch {
                name: "sep",
                weight_bias: 0.0,
                result_src_idx: 1,
                rule_idx: 1,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdsState::PrefixDispatch { pos: *pos + 1, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpds_walker::ForkActionKind::Push },
            },
            FirstSetBranch {
                name: "ident",
                weight_bias: SKIP_BIAS,
                result_src_idx: 1,
                rule_idx: 2,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdsState::PrefixDispatch { pos: *pos, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpds_walker::ForkActionKind::Push },
            },
        ];
        let ts = emit_first_set_fork(&branches, true);
        let s = ts.to_string();
        assert!(s.contains("WpdsStepAction :: Fork"), "missing Fork arm: {}", s);
        assert!(s.contains("CollectionClose"), "missing CollectionClose: {}", s);
        assert!(s.contains("from_cost"), "missing from_cost weight: {}", s);
        // 3 branches => 3 ForkBranch literals.
        assert_eq!(s.matches("ForkBranch").count(), 3);
    }

    #[test]
    fn emit_first_set_fork_single_branch_ok() {
        let branches = vec![FirstSetBranch {
            name: "only",
            weight_bias: 0.0,
            result_src_idx: 0,
            rule_idx: 0,
            symbol: quote! { StackSymbolV2::category_entry(0) },
            new_state: quote! { WpdsState::Accepted },
            action_kind: quote! { mettail_prattail::wpds_walker::ForkActionKind::Push },
        }];
        let ts = emit_first_set_fork(&branches, false);
        let s = ts.to_string();
        assert!(s.contains("WpdsStepAction :: Fork"));
        assert_eq!(s.matches("ForkBranch").count(), 1);
        assert!(s.contains("consume_trigger : false"));
    }

    #[test]
    fn emit_lex_fork_emits_peek_alternatives_check() {
        let ts = emit_lex_fork_at_prefix_dispatch(0);
        let s = ts.to_string();
        assert!(s.contains("is_ambiguous_at"), "missing is_ambiguous_at: {}", s);
        assert!(s.contains("LexAlt"), "missing LexAlt action_kind: {}", s);
        assert!(s.contains("peek_alternatives"), "missing peek_alternatives: {}", s);
    }

    #[test]
    fn cluster3_bp_tier_constants_are_strictly_increasing() {
        // Tier biases must be strictly increasing so lex-min picks lower
        // tiers on weight ties (infix < cross-cat-LHS < postfix < mixfix).
        assert!(BP_TIER_INFIX < BP_TIER_CROSSCAT_LHS);
        assert!(BP_TIER_CROSSCAT_LHS < BP_TIER_POSTFIX);
        assert!(BP_TIER_POSTFIX < BP_TIER_MIXFIX);
    }
}
