//! Shared original collection-loop transition body.

use crate::automata::semiring::SemiringRef;
use crate::automata::TokenKind;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::{WpdaEngine, WpdaStepAction};

/// Execute the original generated collection-loop body with caller-supplied
/// weight construction and the original element-category FIRST predicate.
/// Both callbacks run at their original observation sites and in source order.
#[allow(clippy::too_many_arguments)]
pub fn collection_loop_step<W, E>(
    engine: &E,
    result_src_idx: &u16,
    rule_idx: &u16,
    _element_src_idx: &u16,
    _outer_bp: &u8,
    _accumulator_id: &u8,
    slot_idx: &u8,
    kv_phase: &u8,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    mut element_can_start: impl FnMut(u16, &TokenKind) -> bool,
) -> WpdaStepAction<W>
where
    W: SemiringRef,
    E: WpdaEngine<W> + ?Sized,
{
    {
        // Stage 2: the single per-slot CollectionSpec (was the inline
        // (close, sep, kv_sep, is_binder_internal) lookup match).
        let lookup = engine.collection_spec(*result_src_idx, *rule_idx, *slot_idx);
        let token_text = tokens.peek_text(_pos).unwrap_or("");
        match lookup {
            Some(__spec) => {
                // Project the fields the kv_phase dispatch below reads.
                // `is_binder_internal` is the former loop-arm selector
                // (`close_resumes_via_unwinding`).
                let close = __spec.close;
                let sep = __spec.sep;
                let kv_sep = __spec.kv_sep;
                // Pathmap optional-value (2026-06-27): `true` ⇒ a bare path
                // `{| k |}` (no `: v`) is finalized as `k → k` rather than
                // erroring on the missing `kv_sep` (read in the kv_phase==1
                // arm). `false` for HashMap and every non-kv container.
                let kv_value_optional = __spec.kv_value_optional;
                let is_binder_internal = __spec.close_resumes_via_unwinding;
                // Phase 4 #5b (2026-05-12): three-phase dispatch
                // keyed on kv_phase. For Vec/HashBag/HashSet
                // (kv_sep == None), only phase 0 ever runs (the
                // walker's parity-driven patch keeps kv_phase=0).
                let _ = (close, sep, kv_sep);
                let element_src_idx = *_element_src_idx;
                match *kv_phase {
                    0u8 => {
                        // #307 ROOT-F G1-G4 (2026-06-11; FV:
                        // CollectionForkEvidence.v, 13 thms zero-admission;
                        // design red-team CONVERGED round 2): the
                        // post-element fork emits ONLY evidence-licensed
                        // branches. The Stage-3.16 unconditional three-way
                        // fork over-generated: BRANCH-1 consumed ANY token
                        // as a pseudo-close ({0|1} finalized {0} after
                        // eating `|` — pseudo_close_overgenerates) and
                        // BRANCH-3 split elements separator-free
                        // ({c d} parsed; {c!(p)} shredded into c, p —
                        // bare_element_overgenerates). The realize layer
                        // cannot refute the junk (min_terminal_span = 0
                        // for collections + zero-width symbol span), so
                        // the fix is at GENERATION: gated_run_iff_loop_lang
                        // proves the gated machine accepts EXACTLY the
                        // collection continuation language (no-loss).
                        //
                        // G1 close: membership over the COMPLETE out-edge
                        //   set (peek_text primary + peek_alternatives,
                        //   deduped — the ROOT-A __mixfix_literal_targets
                        //   discipline); one branch per matching edge,
                        //   each a ConsumeAtAndPop carrying the MATCHED
                        //   edge's target (R2-1: the post-close position
                        //   feeds the splice/re-host reads inside
                        //   apply_pop_body_to_cursor; alt-0 advance is the
                        //   alt0_close_lands_on_wrong_target defect).
                        // G2 sep: the consume branch is emitted iff a sep
                        //   edge is PRESENT (membership detection). The
                        //   consume itself resolves the PRIMARY edge
                        //   (R2-2 constraint: safe while detection stays a
                        //   presence test and shipped seps are primary-
                        //   resolved — longest-match orders multi-char
                        //   delimiters first; if sep detection ever forks
                        //   per matched edge, the consume needs next_pos
                        //   carriage like G1).
                        // G3 bare-element: licensed ONLY for separator-free
                        //   (whitespace-joined) collection grammars —
                        //   sep.is_empty() is a per-slot compile-time
                        //   constant from the lookup (the ENTRY separator;
                        //   Map kv_sep never governs this fork).
                        // G4 advance-or-recover: zero licensed normal
                        //   branches means the collection continuation
                        //   cannot consume the live token. For explicit
                        //   close-delimited slots, synthesize a bounded
                        //   recovery close insertion and pop the marker
                        //   through the same finalize path as a real
                        //   close. Empty-close grammars still error:
                        //   there is no concrete token to insert.
                        let mut __branches: Vec<crate::wpda_walker::ForkBranch<_>> =
                            Vec::with_capacity(3);
                        // G1: close branches by edge membership.
                        if token_text == close {
                            if let Some(np) = tokens.next_pos(_pos, 0) {
                                __branches.push(crate::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                    // str-cast collection-infix fix (2026-06-18):
                                    // resume the enclosing Pratt InfixLoop at the
                                    // dispatch bp (CollectionLoop.outer_bp, carried
                                    // from the marker's continuation_bp) so a
                                    // finalized collection can attach a following
                                    // infix operator with l_bp > outer_bp — exactly
                                    // mirroring the atomic Return-pop path. When no
                                    // higher-bp operator follows (close/sep/lower-bp
                                    // op next), InfixLoop falls through to Unwinding
                                    // (engine_impl CollectionMarker reroute) — no-loss.
                                    // Binder-internal collections (is_binder_internal)
                                    // are NOT Pratt primaries: they resume the binder
                                    // rule continuation via Unwinding (their pre-fix
                                    // behavior), so a following token is never wrongly
                                    // consumed as an infix on the collection.
                                    new_state: if is_binder_internal {
                                        WpdaState::Unwinding
                                    } else {
                                        WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                    },
                                    action_kind:
                                        crate::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                            next_pos: np,
                                        },
                                });
                            }
                        }
                        for (__i, __alt) in tokens.peek_alternatives(_pos).iter().enumerate() {
                            if __alt.text == close {
                                if let Some(np) = tokens.next_pos(_pos, __i + 1) {
                                    let __dup = __branches.iter().any(|b| {
                                        matches!(
                                            b.action_kind,
                                            crate::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                next_pos,
                                            } if next_pos == np
                                        )
                                    });
                                    if !__dup {
                                        __branches.push(
                                            crate::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::category_entry(0),
                                                weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                                // str-cast collection-infix fix
                                                // (2026-06-18): same as the primary close
                                                // branch — resume InfixLoop at the dispatch
                                                // bp; no-loss fall-through to Unwinding.
                                                // Binder-internal collections stay Unwinding.
                                                new_state: if is_binder_internal {
                                                    WpdaState::Unwinding
                                                } else {
                                                    WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                                },
                                                action_kind:
                                                    crate::wpda_walker::ForkActionKind::ConsumeAtAndPop {
                                                        next_pos: np,
                                                    },
                                            },
                                        );
                                    }
                                }
                            }
                        }
                        // G2: sep branch, presence-gated.
                        let __sep_present = !sep.is_empty()
                            && (token_text == sep
                                || tokens.peek_alternatives(_pos).iter().any(|a| a.text == sep));
                        if __sep_present {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(0),
                                weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                new_state: WpdaState::PrefixDispatch {
                                    pos: tokens.next_pos(_pos, 0).unwrap_or(_pos + 1),
                                    cur_bp: 0,
                                },
                                // #307 ROOT-F coverage backstop: the
                                // dedicated separator-consume kind
                                // increments the child's per-slot sep
                                // count (the fire-time accounting
                                // witness).
                                action_kind:
                                    crate::wpda_walker::ForkActionKind::ConsumeCollectionSep,
                            });
                        }
                        // G3: a delimiter-free continuation exists only
                        // when the complete lexical lattice at this
                        // position intersects FIRST(element).  The old
                        // unconditional branch attempted to parse every
                        // following token as an element, so an open-ended
                        // `xs.*sep("")` could never yield to its enclosing
                        // continuation.
                        let __element_can_start = tokens
                            .peek_kind(_pos)
                            .as_ref()
                            .is_some_and(|kind| element_can_start(element_src_idx, kind))
                            || tokens.peek_alternatives(_pos).iter().any(|alternative| {
                                element_can_start(element_src_idx, &alternative.kind)
                            });
                        if sep.is_empty() && (!close.is_empty() || __element_can_start) {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                // GEN-1 goal-gate G2 (2026-06-28): strict
                                // GOAL = the element's category so a
                                // cross-cat element cannot over-extend
                                // past its category into a cross-cat-out
                                // operator that cannot reach the goal.
                                symbol: StackSymbolV2::category_entry_goal(element_src_idx),
                                weight: lex_w(
                                    crate::automata::lex_weight::EPSILON_OPT_SKIP,
                                    *result_src_idx,
                                    *rule_idx,
                                ),
                                new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                                action_kind: crate::wpda_walker::ForkActionKind::Push,
                            });
                        }
                        // G4: an empty close denotes an open-ended EBNF
                        // repetition.  Stopping is a real epsilon branch,
                        // not a fallback after the element branch fails:
                        // when FIRST(element) overlaps FOLLOW(repetition),
                        // both interpretations must remain live and the
                        // enclosing continuation decides.  At this point at
                        // least one element has returned, so every supported
                        // lower bound (zero or one) is satisfied.
                        if close.is_empty() {
                            __branches.push(crate::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(0),
                                weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                new_state: if is_binder_internal {
                                    WpdaState::Unwinding
                                } else {
                                    WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                },
                                action_kind: crate::wpda_walker::ForkActionKind::Pop,
                            });
                        }
                        if __branches.is_empty() {
                            WpdaStepAction::Fork {
                                branches: vec![crate::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: lex_w(
                                        crate::recovery::costs::INSERT.value(),
                                        *result_src_idx,
                                        *rule_idx,
                                    ),
                                    new_state: if is_binder_internal {
                                        WpdaState::Unwinding
                                    } else {
                                        WpdaState::InfixLoop { cur_bp: *_outer_bp }
                                    },
                                    action_kind:
                                        crate::wpda_walker::ForkActionKind::PopWithEffect {
                                            effect: crate::wpda_walker::BuilderDelta::InsertToken {
                                                pos: _pos,
                                                kind: crate::automata::TokenKind::Fixed(
                                                    close.to_string(),
                                                ),
                                                text: close.to_string(),
                                            },
                                        },
                                }],
                                consume_trigger: false,
                            }
                        } else {
                            WpdaStepAction::Fork {
                                branches: __branches,
                                // Each branch's action_kind encodes its own
                                // consume semantics (or no-consume for Push/Pop).
                                consume_trigger: false,
                            }
                        }
                    },
                    1u8 => {
                        // Phase 4 #5b (2026-05-12): just parsed a key.
                        // Consume the key/value separator `:` (or
                        // user-overridden equivalent). On mismatch,
                        // error — the cursor's collection_stack parity
                        // is odd, so we MUST consume `:` to proceed.
                        //
                        // Pathmap optional-value (2026-06-27; #74 fix
                        // 2026-07-29): for a value-optional kv-collection
                        // (Pathmap), a key followed DIRECTLY by the close or
                        // an entry separator (not the `kv_sep`) is a bare
                        // path `{| k |}` — the key is present and bound to
                        // NOTHING. Record that with
                        // `PushUnsetCollectionValue` and re-dispatch as
                        // kv_phase=0 WITHOUT consuming: the arena is now
                        // even so the walker's parity patch lands
                        // kv_phase=0, and the phase-0 dispatch resolves the
                        // close (finalize) or separator (next key) exactly
                        // as a value-ful entry would. HashMap
                        // (kv_value_optional=false) keeps the strict
                        // error — its values are mandatory.
                        //
                        // ⚠ This delta USED to be
                        // `DuplicateLastCollectionElement`, which made
                        // `{| k |}` ≡ `{| k : k |}` by re-folding the key's
                        // own SPPF node into the value slot. That is not a
                        // representation of absence but a fabricated
                        // presence: it collapsed `{|1|}` and `{|1:1|}` into
                        // one term and made `Display` print `{|1:1|}` for
                        // `{|1|}`, so the surface was not a fixpoint of
                        // `parse ∘ display`.
                        match kv_sep {
                            Some(expected_kv_sep) => {
                                // Membership-detect the close / entry
                                // separator across the COMPLETE lattice
                                // edge set (primary peek + alternatives),
                                // mirroring the phase-0 G1 close discipline
                                // — the Pathmap close `|}` is lattice-
                                // ambiguous with the `|` operator.
                                let __bare_path = kv_value_optional
                                    && token_text != expected_kv_sep
                                    && (token_text == close
                                        || token_text == sep
                                        || tokens
                                            .peek_alternatives(_pos)
                                            .iter()
                                            .any(|a| a.text == close || a.text == sep));
                                if token_text == expected_kv_sep {
                                    WpdaStepAction::Consume {
                                        weight: lex_w(0.0, *result_src_idx, *rule_idx),
                                        // Transition to kv_phase=2 to
                                        // Push the value's CategoryEntry
                                        // on the next step. We use
                                        // explicit `2u8` here (not 0):
                                        // the walker's parity-patch
                                        // only overrides kv_phase==0,
                                        // so this `2` survives.
                                        new_state: WpdaState::CollectionLoop {
                                            result_src_idx: *result_src_idx,
                                            rule_idx: *rule_idx,
                                            element_src_idx: *_element_src_idx,
                                            outer_bp: *_outer_bp,
                                            accumulator_id: *_accumulator_id,
                                            slot_idx: *slot_idx,
                                            kv_phase: 2u8,
                                        },
                                    }
                                } else if __bare_path {
                                    // Bare path: record that NO value was
                                    // written for the just-parsed key
                                    // (keeps the arena even-length), then
                                    // re-enter the loop at kv_phase=0 with
                                    // the SAME position (non-consuming) so
                                    // phase-0 handles the close / separator
                                    // uniformly.
                                    WpdaStepAction::AdvanceWithEffect {
                                        effect:
                                            crate::wpda_walker::BuilderDelta::PushUnsetCollectionValue {
                                                id: *slot_idx,
                                            },
                                        new_state: WpdaState::CollectionLoop {
                                            result_src_idx: *result_src_idx,
                                            rule_idx: *rule_idx,
                                            element_src_idx: *_element_src_idx,
                                            outer_bp: *_outer_bp,
                                            accumulator_id: *_accumulator_id,
                                            slot_idx: *slot_idx,
                                            kv_phase: 0u8,
                                        },
                                    }
                                } else {
                                    WpdaStepAction::Error(format!(
                                        "expected key/value separator `{}` after \
                                         HashMap key at pos {}, found {:?}",
                                        expected_kv_sep, _pos, token_text,
                                    ))
                                }
                            },
                            None => {
                                // Defensive: kv_phase=1 reached but
                                // slot has no kv_sep — invariant
                                // violation (parity-patch should not
                                // have set kv_phase=1 for non-HashMap).
                                WpdaStepAction::Error(format!(
                                    "kv_phase=1 reached at (src={}, rule={}, slot={}) \
                                     but slot has no key/value separator — invariant \
                                     violation",
                                    *result_src_idx, *rule_idx, *slot_idx,
                                ))
                            },
                        }
                    },
                    2u8 => {
                        // Phase 4 #5b (2026-05-12): just consumed `:`.
                        // Push CategoryEntry(element_src) onto GSS
                        // and dispatch value parse via PrefixDispatch.
                        // When the value returns, splice happens in
                        // apply_pop_body_to_cursor; the next state
                        // (CollectionLoop with engine-emitted kv_phase=0)
                        // gets parity-patched to phase 0 since the
                        // slot's len is now even.
                        WpdaStepAction::Push {
                            // GEN-1 goal-gate G2 (2026-06-28): strict GOAL =
                            // the kv-collection value element's category.
                            symbol: StackSymbolV2::category_entry_goal(element_src_idx),
                            weight: lex_w(0.0, *result_src_idx, *rule_idx),
                            new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                        }
                    },
                    other => WpdaStepAction::Error(format!(
                        "invalid kv_phase {} at (src={}, rule={}, slot={})",
                        other, *result_src_idx, *rule_idx, *slot_idx,
                    )),
                }
            },
            None => WpdaStepAction::Idle,
        }
    }
}
