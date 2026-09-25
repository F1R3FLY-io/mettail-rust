//! Original lexical-fork bodies shared with generated engines.
//!
//! Callers retain codegen policy choices. Readers and policy fragments are
//! invoked at their original observation sites, including on fall-through.
use crate::automata::{semiring::SemiringRef, TokenKind};
use crate::gss::WpdaGssNode;
use crate::lexer_types::LexAlternative;
use crate::wpda_runtime::{
    CollectionSpec, FrameCtx, LexAltRuleInfo, StackSymbolV2, WpdaState, WpdaTokenSource,
};
use crate::wpda_walker::WpdaStepAction;

/// Run the original prefix lexical fork; None retains the caller's fall-through.
#[allow(clippy::too_many_arguments)]
pub fn prefix<W: SemiringRef, K: Copy>(
    primary_src_idx: u16,
    pos: &usize,
    cur_bp: &u8,
    frontier_top: Option<&WpdaGssNode>,
    tokens: &dyn WpdaTokenSource,
    frame_ctx: FrameCtx,
    mut collection_spec: impl FnMut(u16, u16, u8) -> Option<CollectionSpec>,
    mut lex_alt_rules_for_prefix: impl FnMut(u16, &TokenKind) -> Vec<LexAltRuleInfo>,
    mut prefix_crosscat_lhs_trigger_ahead_scoped: impl FnMut(u16, &dyn WpdaTokenSource, usize) -> bool,
    kwambig_observation: impl FnOnce() -> K,
    mut primary_projection_keep: impl FnMut(bool, u16, u16, &TokenKind, K) -> bool,
    mut secondary_projection_keep: impl FnMut(bool, u16, u16, &LexAlternative, K) -> bool,
    mut crosscat_lhs_has_projection_fallback: impl FnMut(u16, u16) -> bool,
    mut prefix_primary_has_dispatch_rule: impl FnMut(u16, &TokenKind) -> bool,
    primary_is_contextual_keyword: impl FnOnce() -> bool,
    mut prefix_crosscat_lhs_has_dispatch_rule: impl FnMut(u16, &TokenKind) -> bool,
    mut prefix_crosscat_lhs_trigger_ahead: impl FnMut(u16, &dyn WpdaTokenSource, usize) -> bool,
    mut lex_one: impl FnMut() -> W,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    mut lex_w_with_len: impl FnMut(u16, f64, u16, u16) -> W,
    mut lex_w_alt_with_len: impl FnMut(u16, f64, u16, u16, u16) -> W,
    mut prefixop_weight_primary: impl FnMut(u16, u16, &LexAltRuleInfo) -> W,
    mut prefixop_weight_secondary: impl FnMut(u16, u16, &LexAltRuleInfo, u16) -> W,
) -> Option<WpdaStepAction<W>> {
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
        let primary_src_for_fork: u16 = primary_src_idx;
        // GEN-2 cross-cat collection-element lex-fork category fix
        // (2026-07-02): the dispatch category for this lex-fork is
        // normally the frontier-top symbol's category. BUT when the
        // frontier top is a `CollectionMarker` whose CollectionSpec
        // declares a cross-category element (`element_src_idx != result
        // (owning) category`), the token at `*pos` is a COLLECTION
        // ELEMENT that must be dispatched in the ELEMENT category, NOT
        // the owning-rule category. This mirrors the non-ambiguous
        // CollectionMarker cross-cat redirect in the `PrefixDispatch`
        // arm (engine_impl.rs: `category_entry_goal(element_src_idx)`),
        // which the lex-fork otherwise PRE-EMPTS: without this, a
        // lex-ambiguous keyword-led element (e.g. rholang `Nil`/`Map`/
        // `Set`/`Pathmap`/`str`/`bigrat`, each `Fixed(kw) | Ident`) in a
        // cross-cat collection slot (InputBindQuery `args:Vec(Proc)`
        // owned by `InputBind`) is looked up in the OWNING category, so
        // only the `Ident` secondary (a metavariable rule) survives and
        // the keyword's element-category rule (Proc `PZero`/`MapEmpty`/
        // `CastSet`/…) is never dispatched — the fork returns a lone
        // wrong-category branch and never falls through to the redirect.
        // A same-category collection element (`element == owning`, e.g. a
        // Proc send's `bs:Vec(Proc)` rest) has `element_src_idx == rs` so
        // this override is inert (byte-identical). Grammar-derived from
        // CollectionSpec — no per-rule/per-language hardcode. The
        // `COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED` const is the LIFO
        // kill-switch (flip to `false` to restore pre-fix behavior).
        const COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED: bool = true;
        let primary_src = {
            let __ft_cat = frontier_top
                .map(|n| n.symbol.category_src_idx)
                .unwrap_or(primary_src_for_fork);
            if COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED {
                match frontier_top {
                    Some(__ft)
                        if __ft.symbol.kind
                            == crate::wpda_runtime::SymbolKind::CollectionMarker =>
                    {
                        let __rs = __ft.symbol.category_src_idx;
                        let __ri = __ft.symbol.rule_index_in_category;
                        let __slot = __ft.symbol.bp.unwrap_or(0u8);
                        match collection_spec(__rs, __ri, __slot)
                            .and_then(|__s| __s.element_src_idx)
                        {
                            Some(__e) if __e != __rs => __e,
                            _ => __ft_cat,
                        }
                    },
                    _ => __ft_cat,
                }
            } else {
                __ft_cat
            }
        };
        let mut __branches: Vec<crate::wpda_walker::ForkBranch<W>> =
            Vec::with_capacity(alts.len() + 1);
        let __open_len: u16 = tokens
            .peek_text(*pos)
            .map(|__t| u16::try_from(__t.len()).expect("token length exceeds u16"))
            .unwrap_or(0);
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
        let mut __secondary_survived: bool = false;
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
        let mut __leading_category_seen: std::collections::BTreeSet<(u16, u16)> =
            std::collections::BTreeSet::new();

        // ForRow Part-1 push-gate (F0, 2026-06-28): row-scoped trigger
        // lookahead for the cross-cat-LHS EXTENSION delegates pushed below.
        // Computed ONCE (depends only on `primary_src` + `*pos`, not on the
        // per-alt rule info). Each `CrossCatLhs` arm keeps its push iff
        // `__ccl_trigger_scoped OR NOT crosscat_lhs_has_projection_fallback`
        // (H1) — i.e. it is suppressed ONLY when both (a) no scoped trigger
        // binds this LHS in-row AND (b) a transparent projection
        // source→result exists to carry the triggerless derivation. So a
        // triggerless in-row bind WITH a projection (`@[1]<-c` → ForRow via
        // `ForRowSingleNoWhere`) drops to projection-only, a genuine in-row
        // `&`/`where`/`<=` trigger still forks the extension, and a cross-cat
        // pair with NO projection fallback (LedTest `Num→Pred` via `==`)
        // keeps the delegate unconditionally — byte-identical to baseline.
        // The EOF fall-through predicate below
        // (`prefix_crosscat_lhs_trigger_ahead`) is UNCHANGED — this gates
        // only the PUSH sites. FV: CastLexForkCrossCatLhsGap.gate_no_loss
        // extended to the push site, conditioned on the projection fallback
        // (one-sided monotone refutation: when a projection carries the
        // triggerless case, scoped-absence ⇒ the delegate dies by evidence
        // anyway, so dropping it removes no admitting parse).
        let __ccl_trigger_scoped: bool =
            prefix_crosscat_lhs_trigger_ahead_scoped(primary_src, tokens, *pos);
        let __pos_has_ident_reading = kwambig_observation();

        // Branch[0] — PRIMARY (lex_alt_idx = 0).
        // M6c.6.4.d (2026-05-14): activated PrefixOp branch — same-cat
        // unary prefix rules (e.g., `Neg`) now emit lex-Fork branches
        // with `LexAltPrefixOp` action_kind, mirroring the standard
        // `Fixed(trigger) → ConsumeAndPush(BinderRule)` arm shape.
        if let Some(primary_kind) = tokens.peek_kind(*pos) {
            for info in lex_alt_rules_for_prefix(primary_src, &primary_kind) {
                match info.kind {
                    crate::wpda_runtime::LexAltRuleKind::Atomic => {
                        let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                        let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 0u8, Some(*cur_bp))
                                .with_kind_return();
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                0u16,
                            ),
                            new_state: WpdaState::Unwinding,
                            action_kind: crate::wpda_walker::ForkActionKind::LexAlt {
                                alt_idx: 0u16,
                                kind: primary_kind.clone(),
                                text: primary_text,
                                next_pos: primary_next_pos,
                                rule_idx: info.rule_idx,
                            },
                        });
                        __primary_survived = true;
                    },
                    // GAP-3 route (a) (2026-06-28): the PRIMARY lattice
                    // reading is the Fixed(trigger) of a nullary
                    // multi-literal keyword rule (e.g. `Map`/`Pathmap`).
                    // Push the mixfix marker + enter MixfixLiteralRun(kind=2)
                    // — the trigger is mirrored as a TriggerTerminal by the
                    // LexAltNullaryRun apply (modelled on LexAltPrefixOp).
                    crate::wpda_runtime::LexAltRuleKind::NullaryPrefixRun => {
                        let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                        let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::mixfix_marker(primary_src, info.rule_idx, 0u8, *cur_bp);
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                0u16,
                            ),
                            new_state: WpdaState::MixfixLiteralRun {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                completed_idx: 0u8,
                                kind: 2u8,
                                sub_pos: 0u8,
                            },
                            action_kind: crate::wpda_walker::ForkActionKind::LexAltNullaryRun {
                                alt_idx: 0u16,
                                trigger: primary_text,
                                rule_idx: info.rule_idx,
                                next_pos: primary_next_pos,
                            },
                        });
                        __primary_survived = true;
                    },
                    crate::wpda_runtime::LexAltRuleKind::PrefixOp { body_src_idx } => {
                        let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                        let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                        // Symbol shape: rule_at(cat, rule_idx, slot=1,
                        // Some(*cur_bp)) — NO with_kind_return. Mirror
                        // of standard `Fixed("-")` ConsumeAndPush arm.
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 1u8, Some(*cur_bp));
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: prefixop_weight_primary(__open_len, primary_src, &info),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                outer_bp: *cur_bp,
                            },
                            action_kind: crate::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                alt_idx: 0u16,
                                trigger: primary_text,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                next_pos: primary_next_pos,
                                outer_bp: *cur_bp,
                            },
                        });
                        __primary_survived = true;
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatPrefixUnary {
                        source_src_idx,
                        operand_bp,
                    } => {
                        let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                        let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 0u8, Some(*cur_bp))
                                .with_kind_return();
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                0u16,
                            ),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx,
                                inner_cur_bp: operand_bp,
                            },
                            action_kind:
                                crate::wpda_walker::ForkActionKind::LexAltCrossCatPrefixUnary {
                                    alt_idx: 0u16,
                                    trigger: primary_text,
                                    rule_idx: info.rule_idx,
                                    next_pos: primary_next_pos,
                                },
                        });
                        __primary_survived = true;
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatProjection { source_src_idx } => {
                        // ForRow F3 (2026-06-28): symmetric projection-
                        // suppression gate — the exact DUAL of the F0
                        // extension push-gate (the `CrossCatLhs` arm below).
                        // Keep the transparent PROJECTION delegate UNLESS a
                        // row-scoped EXTENSION trigger (`&`/`where`/`<=`)
                        // binds this LHS AND a transparent projection
                        // source→result fallback exists. Under a trigger the
                        // projection is FUTILE: its ForRow result leaves the
                        // trigger unconsumable before the row delimiter, so it
                        // never reaches an accepting root, yet keeping it
                        // re-parses `b` in a 2nd GSS lineage the merge/subsume
                        // key rightly cannot fold (distinct sppf_stack) = the
                        // F2 `2^N` `&`-join frontier leak. Suppressing it
                        // leaves EXACTLY ONE delegate per dispatch (extension
                        // when triggered, projection otherwise), the logical
                        // complement of F0 (extension kept iff
                        // `trigger ∨ ¬proj`; projection kept iff
                        // `¬trigger ∨ ¬proj`). NON-ForRow projections (Pathmap
                        // `{|`, casts) carry no `&`/`where`/`<=` trigger ⇒
                        // `__ccl_trigger_scoped` false ⇒ guard folds to
                        // `__proj_keep == true` ⇒ BYTE-IDENTICAL. Behind
                        // `FORROW_PROJ_GATE` (this module) for A/B. FV:
                        // CastLexForkCrossCatLhsGap proj_gate_no_loss (dual of
                        // gate_no_loss; one-sided monotone refutation).
                        let __proj_keep = primary_projection_keep(
                            __ccl_trigger_scoped,
                            primary_src,
                            source_src_idx,
                            &primary_kind,
                            __pos_has_ident_reading,
                        );
                        if __proj_keep
                            && __crosscat_projection_seen.insert((info.rule_idx, source_src_idx))
                        {
                            let sym = StackSymbolV2::rule_at(
                                primary_src,
                                info.rule_idx,
                                0u8,
                                Some(*cur_bp),
                            )
                            .with_kind_return();
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_with_len(
                                    __open_len,
                                    crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                    primary_src,
                                    info.rule_idx,
                                ),
                                new_state: WpdaState::CrossCatDelegate {
                                    source_src_idx,
                                    inner_cur_bp: *cur_bp,
                                },
                                // Stage 4 (Lever-1 emit-both supersedes Fix A,
                                // 2026-06-27): route the cross-cat projection
                                // delegate (e.g. Pathmap `{|`) through the NORMAL
                                // cohort fork-push (`Push`), NOT Fix A's singleton
                                // `PushProjectionInline`. The Pathmap `{|…|}`
                                // close residual is closed by the InfixLoop
                                // emit-both delimiter yield (frame_ctx); with that
                                // close fix in place the OPEN-side projection
                                // resolves the KV literals (`{|1:2|}`,
                                // `{|["k"]:1|}`, `*@{|1:2|}`) through the ordinary
                                // cohort push (empirically verified 2026-06-27), so
                                // the singleton hack is no longer needed. FV:
                                // ForkSurvivorBinderPop.v +
                                // CollectionDelegateDispatch.v.
                                action_kind: crate::wpda_walker::ForkActionKind::Push,
                            });
                            // GEN-1 GAP-4 (2026-06-28): survival flag set INSIDE
                            // the `if __proj_keep` gate — symmetric with the
                            // secondary projection arm and the F0 `CrossCatLhs`
                            // arm. Previously this was a sibling statement AFTER
                            // the gate, so a SUPPRESSED primary projection still
                            // flipped `__primary_survived`, which could force the
                            // `__branches.len() == 1 && __primary_survived`
                            // fall-through (line ~709) into the normal dispatch —
                            // whose un-suppressed projection arm re-introduced the
                            // futile branch F3 had removed. Audit §GAP-4.
                            __primary_survived = true;
                        }
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatLhs { source_src_idx } => {
                        // F0 push-gate (H1): suppress the EXTENSION delegate
                        // only when (a) no row-scoped trigger binds this LHS
                        // AND (b) a transparent projection source→result
                        // exists to carry the triggerless derivation. Where
                        // NO projection fallback exists (e.g. LedTest
                        // Num→Pred via `==`), the delegate is the ONLY
                        // source→result path, so it MUST stay — keep
                        // unconditionally (byte-identical to baseline).
                        let __ccl_keep = __ccl_trigger_scoped
                            || !crosscat_lhs_has_projection_fallback(primary_src, source_src_idx);
                        if __ccl_keep && __crosscat_lhs_seen.insert(source_src_idx) {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(source_src_idx),
                                weight: lex_w_with_len(
                                    __open_len,
                                    crate::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                    primary_src,
                                    source_src_idx,
                                ),
                                new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
                                action_kind: crate::wpda_walker::ForkActionKind::PushCrossCatLhs,
                            });
                            __primary_survived = true;
                        }
                    },
                    crate::wpda_runtime::LexAltRuleKind::LeadingCategory { source_src_idx } => {
                        if __leading_category_seen.insert((info.rule_idx, source_src_idx)) {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(source_src_idx),
                                weight: lex_w(0.0, primary_src, info.rule_idx),
                                new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
                                action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
                                    replace_symbol: StackSymbolV2::rule_at(
                                        primary_src,
                                        info.rule_idx,
                                        1u8,
                                        Some(*cur_bp),
                                    ),
                                },
                            });
                            __primary_survived = true;
                        }
                    },
                    // L9-4 — a LEADING `*flt(node, open, close)` GuestBody
                    // capture triggered by its opener kind. The opener is
                    // ALWAYS the longest-match PRIMARY reading (its delimiter
                    // makes it strictly longer than any competing lex-alt such
                    // as a bare `Ident`), so it can only appear here, never as
                    // a secondary. Emit the SAME branch as the singleton
                    // `UnifiedDescriptor::LeadingGuestBody` peek-arm — push
                    // `RuleAt(1)`, enter `BinderRule`, carry
                    // `ConsumeGuestBodyAndPush`. Because this branch is now in
                    // `__branches`, the FLT reading is explored alongside the
                    // opener's `Ident -> Var` secondary instead of being
                    // dropped when the legacy fall-through is suppressed.
                    crate::wpda_runtime::LexAltRuleKind::LeadingGuestBody {
                        body_src_idx,
                        open_kind,
                        nested_open_kinds,
                        close_kind,
                    } => {
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 1u8, Some(*cur_bp));
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w(0.0, primary_src, info.rule_idx),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                outer_bp: *cur_bp,
                            },
                            action_kind:
                                crate::wpda_walker::ForkActionKind::ConsumeGuestBodyAndPush {
                                    open_kind: open_kind.to_string(),
                                    nested_open_kinds: nested_open_kinds
                                        .iter()
                                        .map(|kind| (*kind).to_string())
                                        .collect(),
                                    close_kind: close_kind.to_string(),
                                },
                        });
                        __primary_survived = true;
                    },
                    // L9-3 — a LEADING `b@Tok` custom-kind capture triggered
                    // by its token kind (same PRIMARY-only rationale as
                    // LeadingGuestBody). Emit the singleton
                    // `LeadingTokenKindCapture` branch:
                    // `GuardedConsumeTokenKindAndPush`.
                    crate::wpda_runtime::LexAltRuleKind::LeadingTokenKindCapture {
                        body_src_idx,
                        kind_name,
                    } => {
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 1u8, Some(*cur_bp));
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w(0.0, primary_src, info.rule_idx),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                outer_bp: *cur_bp,
                            },
                            action_kind:
                                crate::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndPush {
                                    kind_name: kind_name.to_string(),
                                },
                        });
                        __primary_survived = true;
                    },
                    // Other variants are InfixLoop-site only;
                    // shouldn't appear here.
                    _ => {},
                }
            }
        }

        // Branches[1..] — SECONDARIES (lex_alt_idx = 1..).
        for (sec_idx, alt) in alts.iter().enumerate() {
            let alt_idx = (sec_idx + 1) as u16;
            let __open_len: u16 = u16::try_from(alt.text.len()).expect("token length exceeds u16");
            for info in lex_alt_rules_for_prefix(primary_src, &alt.kind) {
                match info.kind {
                    crate::wpda_runtime::LexAltRuleKind::Atomic => {
                        let alt_next_pos = tokens.next_pos(*pos, sec_idx + 1).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 0u8, Some(*cur_bp))
                                .with_kind_return();
                        __secondary_survived = true;
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                alt_idx,
                            ),
                            new_state: WpdaState::Unwinding,
                            action_kind: crate::wpda_walker::ForkActionKind::LexAlt {
                                alt_idx,
                                kind: alt.kind.clone(),
                                text: alt.text.to_string(),
                                next_pos: alt_next_pos,
                                rule_idx: info.rule_idx,
                            },
                        });
                    },
                    // GAP-3 route (a) (2026-06-28): the CRITICAL path —
                    // `Map`/`Pathmap` lex with `Ident` as PRIMARY and
                    // `Fixed(trigger)` as a SECONDARY. This arm keeps the
                    // Fixed reading alive (pushes the mixfix marker + enters
                    // MixfixLiteralRun(kind=2)) so it competes with the
                    // `Ident → Var` primary; for `Map()` the marker run
                    // consumes `( )` (longer parse) and wins by lex-min,
                    // while bare `Map` still parses as a Var.
                    crate::wpda_runtime::LexAltRuleKind::NullaryPrefixRun => {
                        let alt_next_pos = tokens.next_pos(*pos, sec_idx + 1).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::mixfix_marker(primary_src, info.rule_idx, 0u8, *cur_bp);
                        __secondary_survived = true;
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                alt_idx,
                            ),
                            new_state: WpdaState::MixfixLiteralRun {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                completed_idx: 0u8,
                                kind: 2u8,
                                sub_pos: 0u8,
                            },
                            action_kind: crate::wpda_walker::ForkActionKind::LexAltNullaryRun {
                                alt_idx,
                                trigger: alt.text.to_string(),
                                rule_idx: info.rule_idx,
                                next_pos: alt_next_pos,
                            },
                        });
                    },
                    crate::wpda_runtime::LexAltRuleKind::PrefixOp { body_src_idx } => {
                        let alt_next_pos = tokens.next_pos(*pos, sec_idx + 1).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 1u8, Some(*cur_bp));
                        __secondary_survived = true;
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: prefixop_weight_secondary(
                                __open_len,
                                primary_src,
                                &info,
                                alt_idx,
                            ),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                outer_bp: *cur_bp,
                            },
                            action_kind: crate::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                alt_idx,
                                trigger: alt.text.to_string(),
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                next_pos: alt_next_pos,
                                outer_bp: *cur_bp,
                            },
                        });
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatPrefixUnary {
                        source_src_idx,
                        operand_bp,
                    } => {
                        let alt_next_pos = tokens.next_pos(*pos, sec_idx + 1).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 0u8, Some(*cur_bp))
                                .with_kind_return();
                        __secondary_survived = true;
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                alt_idx,
                            ),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx,
                                inner_cur_bp: operand_bp,
                            },
                            action_kind:
                                crate::wpda_walker::ForkActionKind::LexAltCrossCatPrefixUnary {
                                    alt_idx,
                                    trigger: alt.text.to_string(),
                                    rule_idx: info.rule_idx,
                                    next_pos: alt_next_pos,
                                },
                        });
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatProjection { source_src_idx } => {
                        // ForRow F3 (2026-06-28): symmetric projection-
                        // suppression gate (secondary arm; same DUAL of the F0
                        // extension push-gate as the primary arm above — see
                        // that comment). Suppression here also withholds
                        // `__secondary_survived` (it sits inside the gated
                        // `if`, mirroring the F0 `CrossCatLhs` survival flag),
                        // so a suppressed projection cannot keep a fork alive.
                        let __proj_keep = secondary_projection_keep(
                            __ccl_trigger_scoped,
                            primary_src,
                            source_src_idx,
                            alt,
                            __pos_has_ident_reading,
                        );
                        if __proj_keep
                            && __crosscat_projection_seen.insert((info.rule_idx, source_src_idx))
                        {
                            __secondary_survived = true;
                            let sym = StackSymbolV2::rule_at(
                                primary_src,
                                info.rule_idx,
                                0u8,
                                Some(*cur_bp),
                            )
                            .with_kind_return();
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_with_len(
                                    __open_len,
                                    crate::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                    primary_src,
                                    info.rule_idx,
                                ),
                                new_state: WpdaState::CrossCatDelegate {
                                    source_src_idx,
                                    inner_cur_bp: *cur_bp,
                                },
                                // Stage 4 (Lever-1 emit-both supersedes Fix A,
                                // 2026-06-27): route the cross-cat projection
                                // delegate (e.g. Pathmap `{|`) through the NORMAL
                                // cohort fork-push (`Push`), NOT Fix A's singleton
                                // `PushProjectionInline`. The Pathmap `{|…|}`
                                // close residual is closed by the InfixLoop
                                // emit-both delimiter yield (frame_ctx); with that
                                // close fix in place the OPEN-side projection
                                // resolves the KV literals (`{|1:2|}`,
                                // `{|["k"]:1|}`, `*@{|1:2|}`) through the ordinary
                                // cohort push (empirically verified 2026-06-27), so
                                // the singleton hack is no longer needed. FV:
                                // ForkSurvivorBinderPop.v +
                                // CollectionDelegateDispatch.v.
                                action_kind: crate::wpda_walker::ForkActionKind::Push,
                            });
                        }
                    },
                    crate::wpda_runtime::LexAltRuleKind::CrossCatLhs { source_src_idx } => {
                        // F0 push-gate (secondary, H1): same combined guard
                        // as the primary arm — suppress only when no scoped
                        // trigger AND a projection fallback exists.
                        let __ccl_keep = __ccl_trigger_scoped
                            || !crosscat_lhs_has_projection_fallback(primary_src, source_src_idx);
                        if __ccl_keep && __crosscat_lhs_seen.insert(source_src_idx) {
                            __secondary_survived = true;
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(source_src_idx),
                                weight: lex_w_with_len(
                                    __open_len,
                                    crate::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                    primary_src,
                                    source_src_idx,
                                ),
                                new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
                                action_kind: crate::wpda_walker::ForkActionKind::PushCrossCatLhs,
                            });
                        }
                    },
                    crate::wpda_runtime::LexAltRuleKind::LeadingCategory { source_src_idx } => {
                        if __leading_category_seen.insert((info.rule_idx, source_src_idx)) {
                            __secondary_survived = true;
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(source_src_idx),
                                weight: lex_w(0.0, primary_src, info.rule_idx),
                                new_state: WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 },
                                action_kind: crate::wpda_walker::ForkActionKind::ReplaceAndPush {
                                    replace_symbol: StackSymbolV2::rule_at(
                                        primary_src,
                                        info.rule_idx,
                                        1u8,
                                        Some(*cur_bp),
                                    ),
                                },
                            });
                        }
                    },
                    crate::wpda_runtime::LexAltRuleKind::LeadingTokenKindCapture {
                        body_src_idx,
                        kind_name,
                    } => {
                        let alt_next_pos = tokens.next_pos(*pos, sec_idx + 1).unwrap_or(*pos + 1);
                        let sym =
                            StackSymbolV2::rule_at(primary_src, info.rule_idx, 1u8, Some(*cur_bp));
                        __secondary_survived = true;
                        __branches.push(crate::wpda_walker::ForkBranch {
                            symbol: sym,
                            weight: lex_w_alt_with_len(
                                __open_len,
                                0.0,
                                primary_src,
                                info.rule_idx,
                                alt_idx,
                            ),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: primary_src,
                                rule_idx: info.rule_idx,
                                body_src_idx,
                                outer_bp: *cur_bp,
                            },
                            action_kind:
                                crate::wpda_walker::ForkActionKind::ConsumeTokenKindAtAndPush {
                                    alt_idx,
                                    kind_name: kind_name.to_string(),
                                    kind: alt.kind.clone(),
                                    text: alt.text.to_string(),
                                    next_pos: alt_next_pos,
                                },
                        });
                    },
                    _ => {},
                }
            }
        }

        // Stage 4 (Lever-1 emit-both) — prefix-dispatch site (mirrors the
        // InfixLoop emit-both): when a peeked lattice alternative's text
        // equals a required structural delimiter of the INNERMOST enclosing
        // collection frame (`frame_ctx`), ensure the category_entry
        // `Advance(Unwinding)` yield is present ALONGSIDE the operator/atomic
        // branches so an element sub-parse dispatched directly at a delimiter
        // (an absent/closing element) yields to its `CollectionMarker` rather
        // than being lost. When this fires it forces a `Fork` (the
        // `!__delim_yield` guard on `__fall_through` below) so the yield is
        // never swallowed by the keyword-reservation / crosscat-lhs
        // fall-throughs. Byte-identical on existing inputs: the prefix lex-
        // fork runs only at lattice-ambiguous positions, and a collection
        // delimiter appears at an element-START only in absent-element cases
        // that the corpus does not currently exercise.
        let __delim_yield = frame_ctx.has_structural_frame()
            && (frame_ctx.matches_delim(tokens.peek_text(*pos).unwrap_or(""))
                || alts.iter().any(|__a| frame_ctx.matches_delim(&__a.text)));
        if __delim_yield {
            let __dy_sym = StackSymbolV2::category_entry(primary_src);
            let __dy_present = __branches.iter().any(|b| {
                b.symbol == __dy_sym
                    && matches!(b.new_state, WpdaState::Unwinding)
                    && matches!(b.action_kind, crate::wpda_walker::ForkActionKind::Advance)
            });
            if !__dy_present {
                __branches.push(crate::wpda_walker::ForkBranch {
                    symbol: __dy_sym,
                    weight: lex_one(),
                    new_state: WpdaState::Unwinding,
                    action_kind: crate::wpda_walker::ForkActionKind::Advance,
                });
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
        // A contextual keyword deliberately retains its identifier reading.
        // Keep the lex fork only when it also represents the PRIMARY fixed
        // reading. Collection literals and other multi-token prefix rules
        // are owned only by normal PrefixDispatch; when their primary branch
        // is absent here, falling through is the sole route to the declared
        // syntax. Reserved keywords retain the normal same-length path.
        let __primary_is_contextual_keyword = primary_is_contextual_keyword();
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
        // A surviving secondary branch is also evidence. Normal dispatch
        // can only inspect the primary token, so cross-cat fall-through is
        // valid only when it does not erase a secondary lexical path. This
        // preserves inputs such as a keyword/Ident tie where the keyword
        // can host a cross-cat operand and the Ident can satisfy the
        // requested category directly.
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
        let __primary_has_crosscat_lhs =
            __ccl_kind_hit && prefix_crosscat_lhs_trigger_ahead(primary_src, tokens, *pos);
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
        let __fall_through = !__delim_yield
            && (__branches.is_empty()
                || (__branches.len() == 1 && __primary_survived)
                || (__primary_has_dispatch
                    && __all_alts_same_length
                    && (!__primary_is_contextual_keyword || !__primary_survived))
                || (__primary_has_crosscat_lhs && __all_alts_same_length && !__secondary_survived));
        // EP-P1 Step-0 diagnostic hook (no-op without the
        // `walker-stats` feature). `crosscat_load_bearing` = the
        // fall-through decided true, would have been FALSE without
        // the crosscat disjunct, and ≥ 1 lex-alt branch was
        // bypassed — the runtime witness of the FV `d1_d2_delta`
        // (CastLexForkCrossCatLhsGap), counted as
        // `crosscat_lhs_d2_only_hits`.
        crate::walker_stats::ep_p1::note_crosscat_lhs_fallthrough(
            __ccl_kind_hit,
            __primary_has_crosscat_lhs,
            __fall_through
                && (__primary_has_crosscat_lhs && __all_alts_same_length && !__secondary_survived)
                && !(__branches.is_empty()
                    || (__branches.len() == 1 && __primary_survived)
                    || (__primary_has_dispatch
                        && __all_alts_same_length
                        && (!__primary_is_contextual_keyword || !__primary_survived))),
        );
        if !__fall_through {
            return Some(WpdaStepAction::Fork {
                branches: __branches,
                consume_trigger: false,
            });
        }
    }
    None
}

/// Run the original infix lexical fork; None retains the caller's fall-through.
#[allow(clippy::too_many_arguments)]
pub fn infix<W: SemiringRef>(
    state_cat_src_idx: u16,
    cur_bp: &u8,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    frame_ctx: FrameCtx,
    mut lex_alt_rules_for_infix: impl FnMut(u16, &TokenKind) -> Vec<LexAltRuleInfo>,
    mut mixfix_identity_rule: impl FnMut(u16, &LexAltRuleInfo) -> u16,
    mut lex_w_alt: impl FnMut(f64, u16, u16, u16) -> W,
    mut lex_one: impl FnMut() -> W,
) -> Option<WpdaStepAction<W>> {
    if tokens.is_ambiguous_at(_pos) {
        let alts = tokens.peek_alternatives(_pos);
        let primary_src = state_cat_src_idx;
        let mut __branches: Vec<crate::wpda_walker::ForkBranch<W>> =
            Vec::with_capacity(alts.len() + 1);
        let mut __primary_survived: bool = false;
        let mut __primary_floor_blocked: bool = false;

        if let Some(primary_kind) = tokens.peek_kind(_pos) {
            let primary_text = tokens.peek_text(_pos).unwrap_or("").to_string();
            let primary_next_pos = tokens.next_pos(_pos, 0).unwrap_or(_pos + 1);
            for info in lex_alt_rules_for_infix(primary_src, &primary_kind) {
                match info.kind {
                    crate::wpda_runtime::LexAltRuleKind::PostfixOp { l_bp, result_src_idx } => {
                        if l_bp >= *cur_bp {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    Some(*cur_bp),
                                )
                                .with_kind_return(),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_POSTFIX,
                                    result_src_idx,
                                    info.rule_idx,
                                    0u16,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltPostfixOp {
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
                    crate::wpda_runtime::LexAltRuleKind::InfixOp { l_bp, r_bp, result_src_idx } => {
                        if l_bp >= *cur_bp {
                            let new_state = if result_src_idx != primary_src {
                                WpdaState::CrossCatDelegate {
                                    source_src_idx: primary_src,
                                    inner_cur_bp: r_bp,
                                }
                            } else {
                                WpdaState::PrefixDispatch { pos: primary_next_pos, cur_bp: r_bp }
                            };
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    Some(*cur_bp),
                                )
                                .with_kind_return(),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_INFIX,
                                    result_src_idx,
                                    info.rule_idx,
                                    0u16,
                                ),
                                new_state,
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltInfixOp {
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
                    crate::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                        l_bp,
                        result_src_idx,
                    } => {
                        if l_bp >= *cur_bp {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::mixfix_marker(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    *cur_bp,
                                ),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_MIXFIX,
                                    result_src_idx,
                                    mixfix_identity_rule(result_src_idx, &info),
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
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                    alt_idx: 0u16,
                                    trigger: primary_text.clone(),
                                    rule_idx: mixfix_identity_rule(result_src_idx, &info),
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

        // Stage 4 (Lever-1 emit-both): emit the category_entry
        // `Advance(Unwinding)` yield branch when EITHER the Pratt floor
        // blocked every primary operator (the original max-munch boundary)
        // OR a peeked lattice alternative's text equals a required structural
        // delimiter of the INNERMOST enclosing collection frame
        // (`frame_ctx`). The second trigger restores the no-candidate
        // fall-through that this lex-fork otherwise PRE-EMPTS on a
        // lattice-ambiguous multi-char close (e.g. the Pathmap `|}` close,
        // whose leading `|` collides with the `PParInfix` operator): the
        // element/value sub-parse never yields back to its `CollectionMarker`
        // and the close never resumes. The yield is ADDED ALONGSIDE the
        // operator branches (never instead) — the doomed operator fork dies
        // under the runtime ambiguity budget while the yield pops the element
        // to its `CollectionMarker`, which resumes its close. The match
        // ranges over primary ∪ peek_alternatives. A single push DEDUPs the
        // two triggers by `(symbol, new_state, action_kind)` — both produce
        // the identical `category_entry(primary_src)` + `Advance` +
        // `Unwinding` branch. Byte-identical on every existing passing input:
        // single-char seps are non-ambiguous (lex-fork never runs at them);
        // marker-framed elements are pre-empted by the CollectionMarker
        // reroute BEFORE this lex-fork; the only ambiguous category_entry
        // close with an operator secondary in the corpus is the Pathmap
        // `|}` residual.
        let __delim_yield = frame_ctx.has_structural_frame()
            && (frame_ctx.matches_delim(tokens.peek_text(_pos).unwrap_or(""))
                || alts.iter().any(|__a| frame_ctx.matches_delim(&__a.text)));
        if (__primary_floor_blocked && !__primary_survived) || __delim_yield {
            __branches.push(crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::category_entry(primary_src),
                weight: lex_one(),
                new_state: WpdaState::Unwinding,
                action_kind: crate::wpda_walker::ForkActionKind::Advance,
            });
        }

        for (sec_idx, alt) in alts.iter().enumerate() {
            let alt_idx = (sec_idx + 1) as u16;
            let alt_next_pos = tokens.next_pos(_pos, sec_idx + 1).unwrap_or(_pos + 1);
            for info in lex_alt_rules_for_infix(primary_src, &alt.kind) {
                match info.kind {
                    crate::wpda_runtime::LexAltRuleKind::PostfixOp { l_bp, result_src_idx } => {
                        if l_bp >= *cur_bp {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    Some(*cur_bp),
                                )
                                .with_kind_return(),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_POSTFIX,
                                    result_src_idx,
                                    info.rule_idx,
                                    alt_idx,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltPostfixOp {
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
                    crate::wpda_runtime::LexAltRuleKind::InfixOp { l_bp, r_bp, result_src_idx } => {
                        if l_bp >= *cur_bp {
                            let new_state = if result_src_idx != primary_src {
                                WpdaState::CrossCatDelegate {
                                    source_src_idx: primary_src,
                                    inner_cur_bp: r_bp,
                                }
                            } else {
                                WpdaState::PrefixDispatch { pos: alt_next_pos, cur_bp: r_bp }
                            };
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    Some(*cur_bp),
                                )
                                .with_kind_return(),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_INFIX,
                                    result_src_idx,
                                    info.rule_idx,
                                    alt_idx,
                                ),
                                new_state,
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltInfixOp {
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
                    crate::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                        l_bp,
                        result_src_idx,
                    } => {
                        if l_bp >= *cur_bp {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::mixfix_marker(
                                    result_src_idx,
                                    info.rule_idx,
                                    0,
                                    *cur_bp,
                                ),
                                weight: lex_w_alt(
                                    crate::automata::lex_weight::BP_TIER_MIXFIX,
                                    result_src_idx,
                                    mixfix_identity_rule(result_src_idx, &info),
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
                                action_kind: crate::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                    alt_idx,
                                    trigger: alt.text.to_string(),
                                    rule_idx: mixfix_identity_rule(result_src_idx, &info),
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

        let __fall_through = __branches.is_empty() || (__branches.len() == 1 && __primary_survived);
        if !__fall_through {
            return Some(WpdaStepAction::Fork {
                branches: __branches,
                consume_trigger: false,
            });
        }
    }
    None
}
