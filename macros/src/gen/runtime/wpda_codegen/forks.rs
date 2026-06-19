//! Unified Fork-emission framework — Stage 3.16/3.17/3.18 (Commit 2,
//! 2026-05-05).
//!
//! Replaces deterministic peek-and-decide patterns in WPDS codegen with
//! `WpdaStepAction::Fork` over multiple branches, letting lex-min disambiguate
//! per `feedback_use_wpds_disambiguation_not_heuristics.md`. Branches are
//! emitted unconditionally; branches whose per-branch guards or subsequent
//! steps fail naturally transition to Error/Idle and are discarded as failed
//! derivations. The walker never drops a live cursor solely to satisfy a
//! cursor-count bound.
//!
//! Three already-shipped Forks prove the pattern works:
//! - F7 multi-rule binder (`binder.rs:556-596`)
//! - F8 cross-cat projection (`prefix.rs:932-971`)
//! - A.i Opt-Group sub_pos:0 (`binder.rs:992-1046`)
//!
//! This module unifies the 11 remaining fork sites (Cluster 1: 5 sites; Cluster 2:
//! 2 sites; Cluster 3: 3 sites — Cluster 4 #18/#19 is Commit 3, Cluster 5 is
//! Commit 4) under a small helper API.
//!
//! ## Design notes
//!
//! - **Source-order tiebreak via rule_idx.** Load-bearing per Class A.i
//!   precedent. All Forks must use rule_idx for deterministic disambiguation.
//! - **Lex-min weighting.**
//!   `lex_w(bias, src, rule)` is the standard weight
//!   constructor for new Fork branches; per-tier bias offsets enforce
//!   inter-tier ordering on weight ties.
//! - **Cursor explosion mitigation.** Each Fork emission grows the cursor
//!   count by N; nested call sites multiply. Cursor-count bounds are explicit
//!   opt-in overflow checks (`CursorBoundingMode::BeamSize` compatibility
//!   mode or `AmbiguityBudget`) that report structured ambiguity-budget
//!   overflow instead of silently truncating the frontier.
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
    /// `WpdaState` expression for the branch's `new_state`.
    pub new_state: TokenStream,
    /// `ForkActionKind` expression. Default for most Cluster 1 branches:
    /// `ForkActionKind::Push`.
    pub action_kind: TokenStream,
}

// ─────── Cluster 1 helper ────────────────────────────────────────────────

/// Cluster 1 helper. Emits a `WpdaStepAction::Fork` over the given branches
/// with `consume_trigger` semantics specified by the caller. Following the
/// F7/F8/A.i pattern, branches are emitted unconditionally — the walker
/// discards only branches whose own guard/subsequent step fails.
///
/// Source-order tiebreak: branches are emitted in the same order as
/// `branches` parameter; per-branch `rule_idx` weight component gives
/// lower-index branches lex-min preference on tier-bias ties (see
/// `wpda_walker.rs::ForkBranch.weight`).
///
/// **Cursor-explosion mitigation.** When `branches.len() >= 2`, the emit
/// site grows the cursor count by N; nested call sites multiply. If a caller
/// installs a cursor-count bound, the walker reports structured
/// ambiguity-budget overflow when the live frontier exceeds it; it does not
/// silently prune by branch weight.
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
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: #symbol,
                    weight: lex_w(#bias, #src, #rule),
                    new_state: #new_state,
                    action_kind: #action_kind,
                }
            }
        })
        .collect();

    quote! {
        WpdaStepAction::Fork {
            branches: vec![ #( #branch_exprs ),* ],
            consume_trigger: #consume_trigger,
        }
    }
}

// ─────── Cluster 2 #12 helper (lex-fork) ─────────────────────────────────

/// Cluster 2 #12 — emit a lex-Fork at PrefixDispatch top.
///
/// Wires `WpdaTokenSource::peek_alternatives(*pos)` into a Fork whose
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
        // M6c.3 (2026-05-14): lex-Fork emits ALL alternatives — primary
        // (branch[0]) + each secondary that has a literal rule in the
        // requesting cat. Each branch is bound to its categorical
        // literal rule(s) via `lex_alt_rules_for_prefix(state_cat, kind)`; the
        // walker's LexAlt apply arm uses the rule's Return marker
        // symbol to flow the token through FireAction and produce an
        // AST term.
        //
        // Mandate compliance: pure rule-out by evidence. A branch is
        // dropped iff `lex_alt_rules_for_prefix` returns an empty Vec (no rule in the
        // requesting cat for that kind). No weight-based pre-filter.
        //
        // Primary cursor preserved: pre-M6c the Fork emitted only
        // secondaries and `return`ed, replacing the primary cursor.
        // Now branch[0] IS the primary alt (`alt_idx=0`,
        // `lex_alt_idx=0`); secondaries are `alt_idx=1..` with
        // `lex_alt_idx>=1`.
        //
        // Fast path: when `__branches.len() < 2` (no actual ambiguity
        // surviving the rule-out filter, or only the primary has a
        // rule), the function FALLS THROUGH to the normal per-cat
        // PrefixDispatch arms — byte-identical to non-ambiguous lex.
        if tokens.is_ambiguous_at(*pos) {
            let alts = tokens.peek_alternatives(*pos);
            let primary_src_for_fork: u16 = #primary_src_idx;
            let primary_src = frontier_top
                .map(|n| n.symbol.category_src_idx)
                .unwrap_or(primary_src_for_fork);
            let mut __branches: Vec<mettail_prattail::wpda_walker::ForkBranch<
                __DwW,
            >> = Vec::with_capacity(alts.len() + 1);
            // M6c.8.5 (2026-05-14): track whether the primary alt
            // survived the `lex_alt_rules_for_prefix` evidence filter. The
            // fall-through optimization (skip Fork when only the
            // primary survives → defer to standard PrefixDispatch
            // arms) is ONLY safe when the survivor IS the primary —
            // standard PrefixDispatch dispatches on `peek_kind` which
            // returns the primary's kind. When only a SECONDARY
            // survives, fall-through would silently dispatch the
            // primary kind (wrong rule), violating "never
            // disambiguate early". In that case we MUST Fork (even
            // for a single branch).
            let mut __primary_survived: bool = false;
            // Cross-category projection does not consume a lexical edge at
            // this site. It delegates to the source category, whose own
            // PrefixDispatch/lex-fork will consume the primary or secondary
            // edge by evidence. Emitting one projection branch per matching
            // lex alternative duplicates the same delegate and encodes a
            // false early alt choice in the branch weight, inflating the
            // frontier without adding evidence.
            let mut __crosscat_projection_seen: std::collections::BTreeSet<(u16, u16)> =
                std::collections::BTreeSet::new();
            let mut __crosscat_lhs_seen: std::collections::BTreeSet<u16> =
                std::collections::BTreeSet::new();

            // Branch[0] — PRIMARY (lex_alt_idx = 0).
            // M6c.6.4.d (2026-05-14): activated PrefixOp branch — same-cat
            // unary prefix rules (e.g., `Neg`) now emit lex-Fork branches
            // with `LexAltPrefixOp` action_kind, mirroring the standard
            // `Fixed(trigger) → ConsumeAndPush(BinderRule)` arm shape.
            if let Some(primary_kind) = tokens.peek_kind(*pos) {
                for info in lex_alt_rules_for_prefix(primary_src, &primary_kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic => {
                            let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                            let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                            ).with_kind_return();
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt(
                                    0.0, primary_src, info.rule_idx, 0u16,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: mettail_prattail::wpda_walker::ForkActionKind::LexAlt {
                                    alt_idx: 0u16,
                                    kind: primary_kind.clone(),
                                    text: primary_text,
                                    next_pos: primary_next_pos,
                                    rule_idx: info.rule_idx,
                                },
                            });
                            __primary_survived = true;
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                            body_src_idx,
                        } => {
                            let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                            let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                            // Symbol shape: rule_at(cat, rule_idx, slot=1,
                            // Some(*cur_bp)) — NO with_kind_return. Mirror
                            // of standard `Fixed("-")` ConsumeAndPush arm.
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 1u8, Some(*cur_bp),
                            );
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt(
                                    0.0, primary_src, info.rule_idx, 0u16,
                                ),
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    body_src_idx,
                                    outer_bp: *cur_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                        alt_idx: 0u16,
                                        trigger: primary_text,
                                        rule_idx: info.rule_idx,
                                        body_src_idx,
                                        next_pos: primary_next_pos,
                                        outer_bp: *cur_bp,
                                    },
                            });
                            __primary_survived = true;
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatProjection {
                            source_src_idx,
                        } => {
                            if __crosscat_projection_seen.insert((info.rule_idx, source_src_idx)) {
                                let sym = StackSymbolV2::rule_at(
                                    primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                                ).with_kind_return();
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: sym,
                                    weight: lex_w(
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                        primary_src,
                                        info.rule_idx,
                                    ),
                                    new_state: WpdaState::CrossCatDelegate {
                                        source_src_idx,
                                        inner_cur_bp: *cur_bp,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                                });
                            }
                            __primary_survived = true;
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatLhs {
                            source_src_idx,
                        } => {
                            if __crosscat_lhs_seen.insert(source_src_idx) {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(source_src_idx),
                                    weight: lex_w(
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                        primary_src,
                                        source_src_idx,
                                    ),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: *pos,
                                        cur_bp: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs,
                                });
                            }
                            __primary_survived = true;
                        }
                        // Other variants are InfixLoop-site only;
                        // shouldn't appear here.
                        _ => {}
                    }
                }
            }

            // Branches[1..] — SECONDARIES (lex_alt_idx = 1..).
            for (sec_idx, alt) in alts.iter().enumerate() {
                let alt_idx = (sec_idx + 1) as u16;
                for info in lex_alt_rules_for_prefix(primary_src, &alt.kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic => {
                            let alt_next_pos = tokens
                                .next_pos(*pos, sec_idx + 1)
                                .unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                            ).with_kind_return();
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt(
                                    0.0, primary_src, info.rule_idx, alt_idx,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: mettail_prattail::wpda_walker::ForkActionKind::LexAlt {
                                    alt_idx,
                                    kind: alt.kind.clone(),
                                    text: alt.text.to_string(),
                                    next_pos: alt_next_pos,
                                    rule_idx: info.rule_idx,
                                },
                            });
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                            body_src_idx,
                        } => {
                            let alt_next_pos = tokens
                                .next_pos(*pos, sec_idx + 1)
                                .unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 1u8, Some(*cur_bp),
                            );
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt(
                                    0.0, primary_src, info.rule_idx, alt_idx,
                                ),
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    body_src_idx,
                                    outer_bp: *cur_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                        alt_idx,
                                        trigger: alt.text.to_string(),
                                        rule_idx: info.rule_idx,
                                        body_src_idx,
                                        next_pos: alt_next_pos,
                                        outer_bp: *cur_bp,
                                    },
                            });
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatProjection {
                            source_src_idx,
                        } => {
                            if __crosscat_projection_seen.insert((info.rule_idx, source_src_idx)) {
                                let sym = StackSymbolV2::rule_at(
                                    primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                                ).with_kind_return();
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: sym,
                                    weight: lex_w(
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                        primary_src,
                                        info.rule_idx,
                                    ),
                                    new_state: WpdaState::CrossCatDelegate {
                                        source_src_idx,
                                        inner_cur_bp: *cur_bp,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                                });
                            }
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatLhs {
                            source_src_idx,
                        } => {
                            if __crosscat_lhs_seen.insert(source_src_idx) {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(source_src_idx),
                                    weight: lex_w(
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                        primary_src,
                                        source_src_idx,
                                    ),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: *pos,
                                        cur_bp: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs,
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }

            // Phase 5A keyword-reservation fix (2026-06-10): wire the
            // long-generated-but-never-called `prefix_primary_has_dispatch_rule`
            // into the fall-through decision. `lex_alt_rules_for_prefix` only
            // represents `Atomic | PrefixOp | CrossCatProjection`; it DROPS
            // collection-literal rules (ListLit/BagLit/MapLit) and multi-token
            // keyword-prefix rules (ElemList `at(...)`, DeleteList `delete(...)`,
            // …). For a keyword that ALSO matches the ident regex
            // (`list`/`at`/`error`/`int`/…) the lattice surfaces a SAME-LENGTH
            // `{Fixed("kw"), Ident}` ambiguity, so the lex-fork would Fork into
            // only the secondary `Ident -> Var` branch — making the keyword parse
            // as a bare variable (collections/keyword-prefix ops fail with
            // trailing `(`; `error op error` blows the cursor budget via the
            // 11-way cross-cat Var fan-out). When the PRIMARY token has a real
            // PrefixDispatch arm (`prefix_primary_has_dispatch_rule`) AND every
            // lexical alternative is the SAME LENGTH as the primary, fall through
            // to the normal `match peek` dispatch: it owns the collection/
            // keyword-prefix/terminal arms and dispatches the explicitly-declared
            // keyword. The same-length guard preserves genuine MULTI-length
            // disambiguation (e.g. `-3` = `{Minus@1, Integer@2}` must keep
            // forking both). Keyword-reservation at a same-length lexical tie: a
            // grammar-declared keyword beats the auto-injected `Var` fallback —
            // evidence-based (the grammar declares the literal), not a heuristic.
            let __primary_has_dispatch = tokens
                .peek_kind(*pos)
                .map(|pk| prefix_primary_has_dispatch_rule(primary_src, &pk))
                .unwrap_or(false);
            // Phase 5A cast-then-compare d1 (2026-06-10; FV:
            // CastLexForkCrossCatLhsGap — d1_restores_hosting +
            // extension_preserves_189_behavior + multilength_unaffected +
            // d1_fanout_constant, all zero-admission): the SECOND fall-through
            // evidence source. A keyword/ident-ambiguous token whose keyword
            // heads rules in a SOURCE category of a category-changing infix
            // RESULTING in the current state cat (e.g. `int` — cat-Int casts —
            // in a Bool-seeking context entered via the ProcBool projection;
            // Bool's Pass-0 owns a CrossCatLhs{Int} arm for it) may fall
            // through to the normal dispatch when the primary token carries
            // that evidence. Secondary keyword alternatives are represented
            // directly above by LexAltRuleKind::CrossCatLhs, because normal
            // dispatch can only inspect the primary token kind.
            // Same-length keyword reservation applies, identically to the
            // primary-rule fall-through above; inner cast levels are
            // owner-context (same-cat primaries), so the fan-out stays
            // depth-independent (the falsified per-level routing is the
            // 2^depth shape fenced by fix_strictly_below_falsified).
            // TRIGGER-PRESENCE GATE (FV: gate_no_loss /
            // gate_zero_overhead_when_absent / gate_kills_tower_blowup): the
            // delegate can host a result ONLY via an infix that CONSUMES its
            // trigger from the remaining input, so absence is definite,
            // monotone refutation — gate the fall-through on presence. This
            // collapses trigger-free nested-cast towers (str(float(int(...)))
            // — the cast arm's Bool-body branch is a SourceCtx at EVERY level,
            // each delegate re-parsing its suffix = 2^depth WORK, observed as
            // 18s/30s/>120s-timeout) back to owner-only work, while every
            // input that can actually host a category-changing infix keeps
            // its delegate.
            // EP-P1 Step-0 (2026-06-11, plan §P1 commit 2): the kind
            // predicate and the trigger gate are bound SEPARATELY so the
            // diagnostic hook below can distinguish "gated off by
            // trigger absence" from "kind miss" — the `&&` chain is
            // semantically identical to the original single binding
            // (short-circuit preserved).
            let __ccl_kind_hit = tokens
                .peek_kind(*pos)
                .map(|pk| prefix_crosscat_lhs_has_dispatch_rule(primary_src, &pk))
                .unwrap_or(false);
            let __primary_has_crosscat_lhs = __ccl_kind_hit
                && prefix_crosscat_lhs_trigger_ahead(primary_src, tokens, *pos);
            let __primary_next_pos = tokens.next_pos(*pos, 0);
            let __all_alts_same_length = alts
                .iter()
                .enumerate()
                .all(|(__i, _)| tokens.next_pos(*pos, __i + 1) == __primary_next_pos);
            // M6c.8.5 (2026-05-14): Fork when ≥2 branches survive OR
            // when the sole survivor is a SECONDARY (not the primary).
            // Fall-through only when 0 branches survived (standard
            // arm handles dispatch / fails naturally) OR when exactly
            // the primary survived (standard PrefixDispatch dispatches
            // on `peek_kind = primary` — byte-identical to non-
            // ambiguous lex, optimization preserved) OR when the primary
            // keyword owns a normal dispatch arm that the lex-alt table
            // cannot represent and all alternatives are same-length
            // (Phase 5A keyword-reservation above).
            let __fall_through =
                __branches.is_empty()
                    || (__branches.len() == 1 && __primary_survived)
                    || ((__primary_has_dispatch || __primary_has_crosscat_lhs)
                        && __all_alts_same_length);
            // EP-P1 Step-0 diagnostic hook (no-op without the
            // `walker-stats` feature). `crosscat_load_bearing` = the
            // fall-through decided true, would have been FALSE without
            // the crosscat disjunct, and ≥ 1 lex-alt branch was
            // bypassed — the runtime witness of the FV `d1_d2_delta`
            // (CastLexForkCrossCatLhsGap), counted as
            // `crosscat_lhs_d2_only_hits`.
            mettail_prattail::walker_stats::ep_p1::note_crosscat_lhs_fallthrough(
                __ccl_kind_hit,
                __primary_has_crosscat_lhs,
                __fall_through
                    && (__primary_has_crosscat_lhs && __all_alts_same_length)
                    && !(__branches.is_empty()
                        || (__branches.len() == 1 && __primary_survived)
                        || (__primary_has_dispatch && __all_alts_same_length)),
            );
            if !__fall_through {
                return WpdaStepAction::Fork {
                    branches: __branches,
                    consume_trigger: false,
                };
            }
        }
    }
}

/// Emit a lex-Fork at InfixLoop top.
///
/// This mirrors the normal InfixLoop candidate construction, but runs it for
/// every surviving lexical alternative at the current token position. Each
/// branch carries the alternative-specific `next_pos`, so lattice token
/// sources advance along the chosen DAG edge.
pub(crate) fn emit_lex_fork_at_infix_loop(_primary_src_idx: u16) -> TokenStream {
    quote! {
        if tokens.is_ambiguous_at(_pos) {
            let alts = tokens.peek_alternatives(_pos);
            let primary_src = state_cat_src_idx;
            let mut __branches: Vec<mettail_prattail::wpda_walker::ForkBranch<
                __DwW,
            >> = Vec::with_capacity(alts.len() + 1);
            let mut __primary_survived: bool = false;
            let mut __primary_floor_blocked: bool = false;

            if let Some(primary_kind) = tokens.peek_kind(_pos) {
                let primary_text = tokens.peek_text(_pos).unwrap_or("").to_string();
                let primary_next_pos = tokens.next_pos(_pos, 0).unwrap_or(_pos + 1);
                for info in lex_alt_rules_for_infix(primary_src, &primary_kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PostfixOp {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    new_state: WpdaState::Unwinding,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltPostfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::InfixOp {
                            l_bp,
                            r_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                let new_state =
                                    if result_src_idx != primary_src {
                                        WpdaState::CrossCatDelegate {
                                            source_src_idx: primary_src,
                                            inner_cur_bp: r_bp,
                                        }
                                    } else {
                                        WpdaState::PrefixDispatch {
                                            pos: primary_next_pos,
                                            cur_bp: r_bp,
                                        }
                                    };
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    new_state,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltInfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            r_bp,
                                            result_src_idx,
                                            source_cat_src_idx: primary_src,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::mixfix_marker(
                                        result_src_idx, info.rule_idx, 0,
                                    ),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    // #307 ROOT-A D2: enter the pre-operand
                                    // literal run (kind=2) — this lex-fork site
                                    // previously jumped straight to the operand
                                    // (PrefixDispatch), resurrecting the part-0
                                    // skip on lattice-ambiguous triggers. The
                                    // child is allocated at the action_kind's
                                    // next_pos, so the pos-less state reads the
                                    // post-trigger position.
                                    new_state: WpdaState::MixfixLiteralRun {
                                        result_src_idx,
                                        rule_idx: info.rule_idx,
                                        completed_idx: 0,
                                        kind: 2,
                                        sub_pos: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        _ => {},
                    }
                }
            }

            if __primary_floor_blocked && !__primary_survived {
                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::category_entry(primary_src),
                    weight: lex_one(),
                    new_state: WpdaState::Unwinding,
                    action_kind: mettail_prattail::wpda_walker::ForkActionKind::Advance,
                });
            }

            for (sec_idx, alt) in alts.iter().enumerate() {
                let alt_idx = (sec_idx + 1) as u16;
                let alt_next_pos = tokens
                    .next_pos(_pos, sec_idx + 1)
                    .unwrap_or(_pos + 1);
                for info in lex_alt_rules_for_infix(primary_src, &alt.kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PostfixOp {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    new_state: WpdaState::Unwinding,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltPostfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::InfixOp {
                            l_bp,
                            r_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                let new_state =
                                    if result_src_idx != primary_src {
                                        WpdaState::CrossCatDelegate {
                                            source_src_idx: primary_src,
                                            inner_cur_bp: r_bp,
                                        }
                                    } else {
                                        WpdaState::PrefixDispatch {
                                            pos: alt_next_pos,
                                            cur_bp: r_bp,
                                        }
                                    };
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    new_state,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltInfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            r_bp,
                                            result_src_idx,
                                            source_cat_src_idx: primary_src,
                                        },
                                });
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::mixfix_marker(
                                        result_src_idx, info.rule_idx, 0,
                                    ),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    // #307 ROOT-A D2: enter the pre-operand
                                    // literal run (kind=2) — see the primary
                                    // MixfixFirstTrigger site above; the child
                                    // is allocated at the action_kind's
                                    // next_pos (alt_next_pos).
                                    new_state: WpdaState::MixfixLiteralRun {
                                        result_src_idx,
                                        rule_idx: info.rule_idx,
                                        completed_idx: 0,
                                        kind: 2,
                                        sub_pos: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                            }
                        },
                        _ => {},
                    }
                }
            }

            let __fall_through =
                __branches.is_empty()
                    || (__branches.len() == 1 && __primary_survived);
            if !__fall_through {
                return WpdaStepAction::Fork {
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
                new_state: quote! { WpdaState::Unwinding },
                action_kind: quote! {
                    mettail_prattail::wpda_walker::ForkActionKind::CollectionClose
                },
            },
            FirstSetBranch {
                name: "sep",
                weight_bias: 0.0,
                result_src_idx: 1,
                rule_idx: 1,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdaState::PrefixDispatch { pos: *pos + 1, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
            },
            FirstSetBranch {
                name: "ident",
                weight_bias: SKIP_BIAS,
                result_src_idx: 1,
                rule_idx: 2,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
            },
        ];
        let ts = emit_first_set_fork(&branches, true);
        let s = ts.to_string();
        assert!(s.contains("WpdaStepAction :: Fork"), "missing Fork arm: {}", s);
        assert!(s.contains("CollectionClose"), "missing CollectionClose: {}", s);
        // Phase C (2026-05-17) drift fix: emit_first_set_fork now produces
        // `lex_w(...)` per-branch weights (the canonical
        // LexicographicWeight constructor for Fork branches). The
        // previous assertion checked for `from_cost`, the older constructor
        // name; the underlying generator changed to `lex_w` without
        // updating this assertion. Test was a pre-existing failure unrelated
        // to Phase C — fixed here as part of the Phase C gauntlet sweep.
        assert!(s.contains("lex_w"), "missing lex_w weight: {}", s);
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
            new_state: quote! { WpdaState::Accepted },
            action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
        }];
        let ts = emit_first_set_fork(&branches, false);
        let s = ts.to_string();
        assert!(s.contains("WpdaStepAction :: Fork"));
        assert_eq!(s.matches("ForkBranch").count(), 1);
        assert!(s.contains("consume_trigger : false"));
    }

    #[test]
    fn emit_lex_fork_emits_peek_alternatives_check() {
        let ts = emit_lex_fork_at_prefix_dispatch(0);
        let s = ts.to_string();
        assert!(s.contains("is_ambiguous_at"), "missing is_ambiguous_at: {}", s);
        assert!(s.contains("LexAlt"), "missing LexAlt action_kind: {}", s);
        assert!(
            s.contains("LexAltRuleKind :: CrossCatLhs"),
            "missing cross-cat LHS lex-alt kind: {}",
            s
        );
        assert!(
            s.contains("ForkActionKind :: PushCrossCatLhs"),
            "missing cross-cat LHS lex-alt action: {}",
            s
        );
        assert!(s.contains("peek_alternatives"), "missing peek_alternatives: {}", s);
    }

    #[test]
    fn emit_infix_lex_fork_emits_operator_action_variants() {
        let ts = emit_lex_fork_at_infix_loop(0);
        let s = ts.to_string();
        assert!(s.contains("lex_alt_rules_for_infix"), "missing infix lookup: {}", s);
        assert!(s.contains("LexAltPostfixOp"), "missing postfix action: {}", s);
        assert!(s.contains("LexAltInfixOp"), "missing infix action: {}", s);
        assert!(s.contains("LexAltMixfixOp"), "missing mixfix action: {}", s);
        assert!(
            s.contains("__primary_floor_blocked") && s.contains("ForkActionKind :: Advance"),
            "missing max-munch Pratt-floor boundary branch: {}",
            s
        );
        assert!(
            s.contains("consume_trigger : false"),
            "lex-alt operator actions consume intrinsically: {}",
            s
        );
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
