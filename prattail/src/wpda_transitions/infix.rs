//! Original InfixLoop body from engine_impl.rs at cc139b1c.
//!
//! Static table routers and grouped/plain mixfix fan emission remain callbacks.
//! The original collection lookups, lexical preemption, token observations,
//! repeated goal/method predicates, fresh absorption table lookups, and branch
//! order are preserved. MIXFIX_ANY is the original codegen eligibility gate for
//! the forced spine fork, which remains after both absorption probes.
//!
//! TransitionBodyRelocation.v applies to these original bodies and equal complete
//! observations, including callback state. No callbacks or token reads are cached
//! or replayed when lexical dispatch falls through.

use super::mixfix::MixfixPart;
use crate::automata::semiring::SemiringRef;
use crate::binding_power::IterAbsorbSpec;
use crate::gss::WpdaGssNode;
use crate::wpda_runtime::{CollectionSpec, StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{ForkBranch, WpdaStepAction};

#[allow(clippy::too_many_arguments)]
pub fn infix_loop<'a, W: SemiringRef, const MIXFIX_ANY: bool>(
    primary_src_idx: u16,
    cur_bp: &u8,
    frontier_top: Option<&WpdaGssNode>,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut collection_spec: impl FnMut(u16, u16, u8) -> Option<CollectionSpec>,
    cat_can_reach: impl Fn(u16, u16) -> bool,
    lex_fork: impl FnOnce(u16) -> Option<WpdaStepAction<W>>,
    mut infix_table: impl FnMut(u16, &str) -> &'a [(u8, u8, u16, u16)],
    mut postfix_table: impl FnMut(u16, &str) -> &'a [(u8, u16, u16)],
    mut mixfix_table: impl FnMut(u16, &str) -> &'a [(u8, u16, u16)],
    mixfix_part: impl Fn(u16, u16, u8) -> Option<MixfixPart<'a>>,
    mixfix_nullary_literals: impl Fn(u16, u16) -> Option<&'a [&'a str]>,
    mut iter_eligible: impl FnMut(u16, u16, u16) -> Option<IterAbsorbSpec>,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    mixfix_fan: impl FnOnce(
        u16,
        &str,
        &[(u8, u16, u16)],
        bool,
        &dyn Fn(u16) -> bool,
        &dyn Fn(u16, u16) -> bool,
        &mut Vec<ForkBranch<W>>,
    ) -> bool,
) -> WpdaStepAction<W> {
    // Phase 4/5/B7: if frontier_top is a marker symbol
    // for a mid-rule context, skip infix dispatch and
    // fall through to Unwinding. Each marker has its
    // own Unwinding handler.
    //
    // F5 fix (2026-05-10): `CollectionMarker` REMOVED
    // from this skip list. After a cross-cat sub-parse
    // returns to a CollectionMarker top, the next
    // tokens may be Pratt infix/postfix/mixfix operators
    // extending the current element (e.g., `+ 2` after
    // `1` inside `{1 + 2 + 3}`). The infix dispatch
    // below uses state_cat_src_idx =
    // CollectionMarker.category_src_idx = the
    // collection's RESULT category (e.g., Proc for
    // PPar) — exactly the category whose operators
    // (Add, Mul, ==, etc.) should fire. If no operator
    // matches, the standard 0-cands fallthrough below
    // advances to Unwinding-CollectionMarker → routes
    // to CollectionLoop for close/sep/bare dispatch —
    // preserving the close-on-`}` and sep-on-`|`
    // semantics. The marker-skip remains for RuleAt /
    // OptionalGroupAt / BinderListLoopAt because those
    // indicate mid-rule contexts where the next tokens
    // are rule-internal literals.
    //
    // F1 follow-up Cluster B (2026-05-10): `MixfixMarker`
    // REMOVED from this skip list. Mixfix inner operands
    // must allow infix/postfix extension (e.g.,
    // `1 ? 3! : 0` requires `!` to bind to `3` BEFORE
    // the mixfix advances to consume `:`). The InfixLoop
    // dispatch reads state_cat_src_idx from the marker
    // (= result_src_idx of the mixfix rule, which is the
    // operand's category for traditional mixfix shapes).
    // If no candidate matches, cands is empty and we
    // fall through to Unwinding-MixfixMarker, which
    // routes to MixfixLiteralRun for the next
    // separator/operand transition.
    if let Some(node) = frontier_top {
        match node.symbol.kind {
            crate::wpda_runtime::SymbolKind::RuleAt(_)
            | crate::wpda_runtime::SymbolKind::OptionalGroupAt
            | crate::wpda_runtime::SymbolKind::BinderListLoopAt => {
                // Rule/optional/binder-list inner markers
                // indicate a mid-rule context; defer to
                // Unwinding so the appropriate state
                // resumes at the recorded sub_pos.
                return WpdaStepAction::Advance(WpdaState::Unwinding);
            },
            crate::wpda_runtime::SymbolKind::CollectionMarker => {
                // Plan B (F5 close/sep filter, 2026-05-11):
                // when frontier_top is CollectionMarker, only
                // proceed with infix/postfix/mixfix dispatch
                // if the next token is actually an operator
                // candidate. If the next token is the
                // collection's close or separator, skip
                // infix dispatch immediately — falling
                // through to Unwinding-CollectionMarker
                // routes to CollectionLoop which handles
                // close/sep/bare correctly.
                //
                // Without this gating, the F5 fix's removal
                // of CollectionMarker from the skip list
                // causes Fork branches that diverge on
                // collection_stack depth, leading to
                // "builder result was empty" failures and
                // degenerate AST (e.g., `{1+2+3}` → ["3"]).
                let result_src_idx = node.symbol.category_src_idx;
                let rule_idx = node.symbol.rule_index_in_category;
                let slot_idx = node.symbol.bp.unwrap_or(0u8);
                let close_sep: Option<(&'static str, &'static str)> =
                    collection_spec(result_src_idx, rule_idx, slot_idx)
                        .map(|__s| (__s.close, __s.sep));
                if let Some((close, sep)) = close_sep {
                    // #307 ROOT-F G2 site-3 (2026-06-11):
                    // close/sep DETECTION is edge
                    // MEMBERSHIP over the complete
                    // alternative set. The reroute stays
                    // SINGLE (round-2 D-C: longest-match
                    // lexing orders multi-char closes as
                    // the primary, so a live close/sep on
                    // a secondary alternative with a
                    // live primary operand is
                    // unrealizable in shipped grammars;
                    // if a future grammar realizes it,
                    // BOTH routes must be forked).
                    let token_text = tokens.peek_text(_pos).unwrap_or("");
                    let __hit = token_text == close
                        || token_text == sep
                        || tokens
                            .peek_alternatives(_pos)
                            .iter()
                            .any(|a| a.text == close || a.text == sep);
                    if __hit {
                        return WpdaStepAction::Advance(WpdaState::Unwinding);
                    }
                }
                // Otherwise fall through to infix dispatch
                // below — the F5 fix behavior for genuine
                // operator extension of the current element.
            },
            _ => {},
        }
    }
    // Stage 3.18 / Fixes #17+#20 (Cluster 3, Mechanism γ,
    // 2026-05-05): collect ALL tier candidates whose
    // l_bp >= cur_bp, then emit a Fork over them with
    // BP_TIER_INFIX < BP_TIER_POSTFIX < BP_TIER_MIXFIX
    // bias offsets so lex-min picks the lower tier on
    // weight ties. Source-order tiebreak via rule_idx
    // within tier. Singleton fast-path emits
    // ConsumeAndPush directly to preserve zero-overhead
    // dispatch for the deterministic case (one tier
    // matches at l_bp >= cur_bp).
    // Gap-2 collection-element InfixLoop category redirect
    // (2026-07-03): when the InfixLoop frontier is a
    // `CollectionMarker` whose declared `element_src_idx`
    // differs from the marker's own (result) category — a
    // CROSS-CATEGORY collection literal (rholang `[…]` List
    // (cat 10) / `#{…}#` Bag (11) / `{|…|}` Pathmap (14),
    // each carrying `Vec<Proc>`/`HashBag<Proc>`/… i.e.
    // `element_src_idx = Proc(0)`) — the operator-dispatch
    // category MUST be the ELEMENT category, not the marker's
    // result category. A completed element sits on the SPPF
    // stack in the element category (e.g. `Map()` = MapEmpty :
    // Proc), and an operator extending it (`* c`, `.values()`,
    // `== c`) is an ELEMENT-category (Proc) operator. Reading
    // `state_cat_src_idx` straight off the marker selects the
    // marker's category (List) whose infix/postfix/mixfix
    // tables are EMPTY, so the operator is never dispatched and
    // the element is spliced prematurely at its first-completion
    // (the Gap-2 bug: `[Map() * c]` strands `*`). Same-category
    // collections (PPar `{…}` : Proc with Proc elements,
    // `element_src_idx == result`) are unaffected — the redirect
    // is a no-op there (byte-identical). Grammar-derived from
    // `CollectionSpec.element_src_idx`; no per-rule/keyword
    // hardcode. NOTE: the close/sep detection above already
    // reads the marker's `collection_spec` directly, so the
    // redirect changes ONLY the operator-dispatch category,
    // never the close/sep routing — an element with no operator
    // continuation still falls through to Unwinding-
    // CollectionMarker exactly as before.
    let state_cat_src_idx: u16 = {
        let __raw = frontier_top
            .map(|n| n.symbol.category_src_idx)
            .unwrap_or(primary_src_idx);
        match frontier_top {
            Some(__ft) if __ft.symbol.kind == crate::wpda_runtime::SymbolKind::CollectionMarker => {
                let __rs = __ft.symbol.category_src_idx;
                let __ri = __ft.symbol.rule_index_in_category;
                let __slot = __ft.symbol.bp.unwrap_or(0u8);
                match collection_spec(__rs, __ri, __slot).and_then(|__s| __s.element_src_idx) {
                    Some(__e) if __e != __rs => __e,
                    _ => __raw,
                }
            },
            _ => __raw,
        }
    };
    // GEN-1 goal-gate (2026-06-28): read the STRICT goal off
    // the frontier-top symbol (Some only for a
    // `category_entry_goal` pushed at a cross-cat operand /
    // element site). `__goal_admits(r)` drops an
    // infix/postfix/mixfix candidate whose RESULT category
    // `r` provably cannot reach the goal `g`
    // (`!cat_can_reach(r, g)`) — bounding the operand to its
    // category so a cross-cat-out operator cannot
    // over-extend it. `None` goal (top-level CrossCatLhs,
    // every legacy `category_entry`) admits all candidates ⇒
    // the gate is inert (G0 byte-identical). `GOAL_GATE_ENABLED`
    // is the compile-time kill-switch (LIFO-revert: flip to
    // `false`).
    const GOAL_GATE_ENABLED: bool = true;
    let __goal = frontier_top.and_then(|n| n.symbol.goal_src_idx);
    let __goal_admits = |result_src: u16| -> bool {
        if !GOAL_GATE_ENABLED {
            true
        } else {
            match __goal {
                None => true,
                Some(g) => cat_can_reach(result_src, g),
            }
        }
    };
    if let Some(__action) = lex_fork(state_cat_src_idx) {
        return __action;
    }
    let token_text = tokens.peek_text(_pos).unwrap_or("");
    let _ = token_text;

    let mut __cands: Vec<crate::wpda_walker::ForkBranch<W>> = Vec::new();

    // Infix tier (BP_TIER_INFIX = 0.00).
    // GEN-1 B-2 (Stage S0) §2.3: PER-RULE gating. Iterate the
    // infix-tier slice (≤ GEN1_MAX_SLICE elems; 1 at S0 ⇒ this
    // runs at most once on the legacy single-winner) and gate
    // each rule individually on `l_bp >= cur_bp`. Identical
    // ForkBranch shape/weight/state as the pre-slice path.
    let __infix_slice: &'a [(u8, u8, u16, u16)] = infix_table(state_cat_src_idx, token_text);
    for &(l_bp, r_bp, result_src, rule_idx) in __infix_slice {
        if l_bp >= *cur_bp && __goal_admits(result_src) {
            let new_state = if result_src != state_cat_src_idx {
                // D-strings fix (2026-05-13): pass r_bp
                // as the sub-parse's `inner_cur_bp` so
                // the cross-cat operand sub-parse
                // enforces the outer Pratt precedence
                // (e.g. `Str < Str : Bool` at r_bp=7
                // prevents `==` at l_bp=2 from leaking
                // into the RHS sub-parse).
                WpdaState::CrossCatDelegate {
                    source_src_idx: state_cat_src_idx,
                    inner_cur_bp: r_bp,
                }
            } else {
                WpdaState::PrefixDispatch {
                    pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                    cur_bp: r_bp,
                }
            };
            __cands.push(crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::rule_at(result_src, rule_idx, 0, Some(*cur_bp))
                    .with_kind_return(),
                weight: lex_w(crate::automata::lex_weight::BP_TIER_INFIX, result_src, rule_idx),
                new_state,
                action_kind: crate::wpda_walker::ForkActionKind::Push,
            });
        }
    }

    // Postfix tier (BP_TIER_POSTFIX = 0.10).
    // F1 fix (2026-05-10): new_state must be Unwinding, not InfixLoop.
    // Postfix has no RHS to parse, so the Return symbol it pushes must
    // be popped immediately to fire the action. Going to InfixLoop
    // instead leaves the Return on the GSS while subsequent operator
    // dispatches push more symbols on top — the action then fires in
    // the wrong order (after the surrounding operator's action), with
    // wrong types and wrong values on the builder stack. Unwinding
    // pops the Return → fires the action → transitions to
    // InfixLoop { cur_bp: outer_bp } via the standard Return-pop path
    // at engine_impl.rs:357-360.
    // GEN-1 B-2 (Stage S0) §2.3: PER-RULE gating, postfix tier.
    let __postfix_slice: &'a [(u8, u16, u16)] = postfix_table(state_cat_src_idx, token_text);
    for &(l_bp, result_src, rule_idx) in __postfix_slice {
        if l_bp >= *cur_bp && __goal_admits(result_src) {
            __cands.push(crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::rule_at(result_src, rule_idx, 0, Some(*cur_bp))
                    .with_kind_return(),
                weight: lex_w(crate::automata::lex_weight::BP_TIER_POSTFIX, result_src, rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind: crate::wpda_walker::ForkActionKind::Push,
            });
        }
    }

    // Mixfix tier (BP_TIER_MIXFIX = 0.20).
    // #307 ROOT-A D1/D2 (2026-06-11; FV:
    // MixfixLiteralAccounting.accounting_gap): the trigger
    // previously dispatched the part-0 OPERAND directly
    // (PrefixDispatch), skipping the part's PRECEDING
    // literals (POutput's "(") — the part-0 accounting
    // gap. It now enters the pre-operand literal run
    // (kind=2), which consumes parts[0].preceding by
    // membership-checked steps and then dispatches the
    // operand. Empty preceding (Tern/PAmb) passes through
    // with zero consumes (empty_pre_passthrough). The
    // state is pos-less: every entry path (singleton
    // ConsumeAndPush, engine Fork{consume_trigger:true},
    // lex-fork next_pos child allocation) advances
    // cursor.pos past the trigger BEFORE it activates.
    // GEN-1 B-2 (Stage S0) §2.3: PER-RULE gating, mixfix tier.
    let __mixfix_slice: &'a [(u8, u16, u16)] = mixfix_table(state_cat_src_idx, token_text);
    // ─────────────────────────────────────────────────────────
    // Fix-B (2026-06-28): METHOD-NAME PRE-FORK PRUNE.
    //
    // The `.`-method mixfix slice shares ONE trigger across ~40
    // rules (`m "." "get" "(" …`, `m "." "set" "(" …`, `m "."
    // "size" "(" ")"`, …). Under S1 (`GEN1_MAX_SLICE` uncapped)
    // EVERY `.` forks the WHOLE slice; the wrong ~39 die ONE step
    // later at their method-name literal-run
    // (`__checked_literal_consume!` → 0-edge `Error`). The
    // transient ×40 peak per `.` COMPOUNDS across an N-method chain
    // and overflows the 4096 ambiguity budget (ESS≈0.000 — pure
    // dead-weight, not genuine ambiguity).
    //
    // This prunes that dead-weight ONE STEP EARLIER, at the fork
    // point, using the SAME evidence the literal-run already uses:
    // a rule's FIRST post-trigger literal `L` (= its method name —
    // `mixfix_part(rs,ri,0).preceding[0]` for an arg method,
    // `mixfix_nullary_literals(rs,ri)[0]` for a 0-arg method; `None`
    // for an operand-/rep-leading part-0 such as ternary or
    // ForRow's `&`-join, which is ALWAYS kept). A method-name rule
    // is admitted iff `L` matches the post-trigger token EXACTLY as
    // `__mixfix_literal_targets` (the literal-run's first step)
    // would: primary `peek_text` OR any lattice alternative.
    //
    // SOUNDNESS (observational equivalence — NO-LOSS, NO-SPURIOUS):
    // a dropped rule has `L` mismatching the post-trigger token, so
    // after consuming the trigger it would enter
    // `MixfixLiteralRun { kind:2, sub_pos:0 }` and its FIRST step
    // `__checked_literal_consume!(L)` yields an EMPTY target set ⇒
    // `Error` ⇒ the cursor drops, realizing NO AST. The post-prune
    // cursor set therefore equals the post-1-step set ⇒ realized
    // AST unchanged. Genuine ambiguity is preserved: if >1 rule
    // shares the same method name, ALL of them match `L` and STILL
    // fork (only provably-non-matching names are dropped). This is
    // maximal-munch on a TERMINAL (the method-name literal), NOT
    // operand commitment — it does NOT disambiguate early.
    //
    // FALLBACK: if the prune would empty an OTHERWISE-non-empty
    // mixfix contribution AND no infix/postfix candidate exists
    // (`__cands` empty), restore the full slice. This keeps the
    // trigger-consumption decision byte-identical to pre-Fix-B in
    // the degenerate all-mismatch case (where unpruned would
    // consume-the-trigger-then-die rather than unwind); it never
    // fires on the chained-method hot path (which always has a
    // matching method). `METHOD_NAME_PRUNE_ENABLED=false` is the
    // LIFO kill-switch (reverts to exact pre-Fix-B behavior).
    // The `&'static` slice is NEVER mutated — this is a runtime
    // evidence filter, so the GEN-1 NO-LOSS slice-multiset
    // invariant is untouched.
    const METHOD_NAME_PRUNE_ENABLED: bool = true;
    // Position the literal-run inspects after the trigger is
    // consumed (`advance_cursor_pos` is alt-0-hardwired — mirror it).
    let __post_trigger_pos = tokens.next_pos(_pos, 0);
    let __method_name_admits = |result_src: u16, rule_idx: u16| -> bool {
        if !METHOD_NAME_PRUNE_ENABLED {
            true
        } else {
            // #131: the 4th element is the capture kind, which this
            // prune does not consult — its evidence is the part's
            // FIRST PRECEDING LITERAL, and a capture part carries
            // preceding literals exactly as an operand part does.
            // A capture part with none (Rholang's collapsed method
            // name, `Call`'s `m`) yields `None` ⇒ ALWAYS KEEP, which
            // is the sound direction: the prune may only drop a rule
            // it can PROVE dead one step early.
            let __lit: Option<&'a str> = match mixfix_part(result_src, rule_idx, 0) {
                Some((_, preceding, _, _)) => preceding.first().copied(),
                None => {
                    mixfix_nullary_literals(result_src, rule_idx).and_then(|l| l.first().copied())
                },
            };
            match (__lit, __post_trigger_pos) {
                // No distinguishing method-name literal
                // (operand-/rep-leading part-0) OR no token after
                // the trigger (EOF) ⇒ cannot prove dead; KEEP.
                (None, _) | (Some(_), None) => true,
                // Method-name rule: KEEP iff its literal matches the
                // post-trigger token (= __mixfix_literal_targets
                // non-empty: primary text OR any lattice alternative).
                (Some(l), Some(p)) => {
                    tokens.peek_text(p) == Some(l)
                        || tokens.peek_alternatives(p).iter().any(|a| a.text == l)
                },
            }
        }
    };
    let __mixfix_no_survivor = !__mixfix_slice.iter().any(|&(l_bp, result_src, rule_idx)| {
        l_bp >= *cur_bp && __goal_admits(result_src) && __method_name_admits(result_src, rule_idx)
    });
    let __mixfix_fallback_full = __mixfix_no_survivor && __cands.is_empty();
    // S1-FACTORING F5-2: `#mixfix_fan_tokens` is the
    // VERBATIM per-member loop for languages without
    // factored mixfix cohorts, and the loop-v2 group
    // match (spine push on full admission; `_` arm =
    // the same verbatim loop) otherwise — see the
    // `mixfix_member_fan_loop` extraction above.
    let __mixfix_spine_pushed = mixfix_fan(
        state_cat_src_idx,
        token_text,
        __mixfix_slice,
        __mixfix_fallback_full,
        &__goal_admits,
        &__method_name_admits,
        &mut __cands,
    );

    // C1-M (WALK-S2, 2026-05-28): pre-fork MIXFIX ternary
    // absorption trigger. Mixfix operators (`Tern`,
    // `c "?" t ":" e`, right-recursive in the else slot)
    // enter the mixfix tier above (pushing a MixfixMarker
    // then a PrefixDispatch for the inner operand) and
    // NEVER re-iterate to the InfixLoop singleton (mixfix
    // associativity is hard-coded Left; plan D2/V5), so the
    // singleton fast-path below cannot reach them.
    // Intercept HERE — after `__cands` is built (which now
    // holds the MixfixMarker candidate), before the
    // singleton-vs-fork branch — for the LEADING mixfix-tier
    // candidate: if it is the canonical iterative-eligible
    // op for its trigger (`iter_eligible_<cat>` → Some) AND
    // mixfix AND a forward peek confirms a deterministic
    // >= 2-level ternary chain, emit `IterativeChainAbsorb`
    // with `new_state = Unwinding` and SUPPRESS the fork
    // (the MixfixMarker push is bypassed by the early
    // `return`). The peek proves the region is a single
    // ternary-shape run, so the normal mixfix descent would
    // only re-walk the (about-to-be-absorbed) interior.
    // `_pos` is ON the trigger (`?`); the head cond c0
    // (parsed at `_pos - 1`) is on `cursor.sppf_stack_id`.
    // On peek-failure this block is inert and control falls
    // through to the unchanged `match __cands.len()` (other
    // languages' mixfix ops won't have `Some(spec)` — the
    // `right_recursive_tail` + exact-shape gate in
    // `is_iterative_candidate` restricts eligibility to
    // Tern-shaped ops — so they are bit-identical).
    // GEN-1 B-2 (Stage S0) §2.4: pre-fork absorption reads the
    // LEADING (rule_idx-min) mixfix candidate via `.first()`.
    // Inert when the slice has >1 elem (S1+); at S0 the slice
    // is ≤1 ⇒ identical to the legacy `Some(..)` head.
    if let Some(&(_pmx_l_bp, _pmx_result_src, _pmx_rule_idx)) =
        mixfix_table(state_cat_src_idx, token_text).first()
    {
        if _pmx_l_bp >= *cur_bp && __goal_admits(_pmx_result_src) {
            let symbol_rs = _pmx_result_src;
            let symbol_ri = _pmx_rule_idx;
            let _pmx_spec: Option<crate::binding_power::IterAbsorbSpec> =
                iter_eligible(state_cat_src_idx, symbol_rs, symbol_ri);
            if let Some(spec) = _pmx_spec {
                if spec.is_mixfix
                    && crate::wpda_walker::peek_ternary_chain(
                        tokens,
                        _pos,
                        spec.trigger,
                        spec.sep,
                        2,
                    )
                {
                    return WpdaStepAction::IterativeChainAbsorb {
                        symbol: StackSymbolV2::rule_at(
                            _pmx_result_src,
                            _pmx_rule_idx,
                            0,
                            Some(*cur_bp),
                        )
                        .with_kind_return(),
                        weight: lex_w(
                            crate::automata::lex_weight::BP_TIER_MIXFIX,
                            _pmx_result_src,
                            _pmx_rule_idx,
                        ),
                        new_state: WpdaState::Unwinding,
                        spec,
                    };
                }
            }
        }
    }

    // C1-R (WALK-S1, 2026-05-28): pre-fork right-assoc
    // absorption trigger. Right-associative binary
    // operators (`^`) recurse via the RHS sub-parse and
    // NEVER re-iterate to the InfixLoop singleton (plan
    // D2), so the left-assoc singleton fast-path below
    // can't reach them. Intercept HERE — after `__cands`
    // is built, before the singleton-vs-fork branch — for
    // the LEADING infix-tier candidate: if it is the
    // canonical iterative-eligible op for its terminal
    // (`iter_eligible_<cat>` → Some) AND right-assoc AND a
    // forward peek confirms a deterministic >= 5-atom
    // (>= 4 remaining after the head) chain of that
    // op-kind, emit `IterativeChainAbsorb` with
    // `new_state = Unwinding` and SUPPRESS the fork. The
    // peek proves the region is a single-op-kind run, so a
    // fork at the chain head would only spawn cursors that
    // either can't complete the chain or redundantly
    // re-walk the (already-absorbed) interior. `_pos` is
    // ON the operator; the head atom (parsed at `_pos - 1`)
    // is on `cursor.sppf_stack_id`. On peek-failure this
    // block is inert and control falls through to the
    // unchanged `match __cands.len()` (non-chain /
    // short-chain workloads bit-identical). LEFT-assoc
    // (AddInt) is NOT routed here — it keeps the existing
    // singleton path (minimal blast radius).
    // GEN-1 B-2 (Stage S0) §2.4: pre-fork absorption reads the
    // LEADING (rule_idx-min) infix candidate via `.first()`.
    // Inert when the slice has >1 elem (S1+); at S0 the slice
    // is ≤1 ⇒ identical to the legacy `Some(..)` head.
    if let Some(&(_pf_l_bp, _pf_r_bp, _pf_result_src, _pf_rule_idx)) =
        infix_table(state_cat_src_idx, token_text).first()
    {
        if _pf_l_bp >= *cur_bp && __goal_admits(_pf_result_src) {
            let symbol_rs = _pf_result_src;
            let symbol_ri = _pf_rule_idx;
            let _pf_spec: Option<crate::binding_power::IterAbsorbSpec> =
                iter_eligible(state_cat_src_idx, symbol_rs, symbol_ri);
            if let Some(spec) = _pf_spec {
                // S1 scope: right-assoc binary only. (S2
                // adds `|| spec.is_mixfix` for ternary.)
                if spec.assoc_right && crate::wpda_walker::peek_binary_chain(tokens, _pos, 5) {
                    return WpdaStepAction::IterativeChainAbsorb {
                        symbol: StackSymbolV2::rule_at(
                            _pf_result_src,
                            _pf_rule_idx,
                            0,
                            Some(*cur_bp),
                        )
                        .with_kind_return(),
                        weight: lex_w(
                            crate::automata::lex_weight::BP_TIER_INFIX,
                            _pf_result_src,
                            _pf_rule_idx,
                        ),
                        new_state: WpdaState::Unwinding,
                        spec,
                    };
                }
            }
        }
    }

    // S1-FACTORING F5-2 D-2: `#mixfix_forced_fork_tokens`
    // (grouped languages only) forces the Fork family
    // when the mixfix spine branch is the lone
    // candidate — see the extraction above. Empty for
    // every other language.
    if MIXFIX_ANY {
        if __mixfix_spine_pushed && __cands.len() == 1 {
            return WpdaStepAction::Fork { branches: __cands, consume_trigger: true };
        }
    }
    match __cands.len() {
        0 => {
            // No tier matched — fall through to Unwinding.
            WpdaStepAction::Advance(WpdaState::Unwinding)
        },
        1 => {
            // Singleton fast-path: only one tier matched,
            // so emit ConsumeAndPush directly. Preserves
            // zero-overhead dispatch for shipped grammars
            // (typical case — only one operator at any
            // given (token, l_bp >= cur_bp) pair).
            //
            // Phase F.13 chain_10000 Exp 6 Substage 6b
            // (2026-05-26): if the singleton candidate
            // refers to an iterative-eligible operator
            // AND its (terminal, l_bp) is unique in the
            // dispatched category (per Plan A invariant
            // I1, codegen-checked in `iter_eligible_<cat>`),
            // route through `IterativeChainAbsorb`
            // instead so the per-chain Return RuleAt
            // push is shared across all `+` iterations.
            // First iteration pushes; subsequent
            // iterations skip the push via the walker
            // arm's chain-extension witness (Plan A
            // invariant I2). RHS sub-parse is dispatched
            // by the `InfixChainIterative` engine arm.
            let b = __cands.into_iter().next().unwrap();
            let symbol_rs = b.symbol.category_src_idx;
            let symbol_ri = b.symbol.rule_index_in_category;
            let iter_lookup: Option<crate::binding_power::IterAbsorbSpec> =
                iter_eligible(state_cat_src_idx, symbol_rs, symbol_ri);
            if let Some(spec) = iter_lookup {
                // C1: only LEFT-associative binary operators
                // absorb via this singleton fast-path (the
                // existing iterative chain path). Right-assoc
                // and mixfix operators recurse / enter the
                // mixfix tier and never re-iterate to a
                // singleton, so they are handled by the
                // pre-fork absorption trigger below; here
                // they fall through to ConsumeAndPush.
                if !spec.assoc_right && !spec.is_mixfix {
                    return WpdaStepAction::IterativeChainAbsorb {
                        symbol: b.symbol,
                        weight: b.weight,
                        new_state: WpdaState::InfixChainIterative {
                            result_src_idx: symbol_rs,
                            rule_idx: symbol_ri,
                            outer_bp: *cur_bp,
                            rhs_bp: spec.right_bp,
                        },
                        spec,
                    };
                }
            }
            WpdaStepAction::ConsumeAndPush {
                symbol: b.symbol,
                weight: b.weight,
                new_state: b.new_state,
                // Phase F.8: infix-tier singleton
                // discards the operator token at the
                // SPPF layer (the operator's LHS/RHS
                // terms are already on the SPPF stack).
                trigger_mode: crate::wpda_walker::TriggerMode::Discard,
            }
        },
        _ => {
            // Multi-tier ambiguity (G5: e.g. infix and
            // postfix sharing a token at the same
            // l_bp >= cur_bp) — emit a Fork. Lex-min
            // picks the lower BP tier on ties.
            WpdaStepAction::Fork { branches: __cands, consume_trigger: true }
        },
    }
}
