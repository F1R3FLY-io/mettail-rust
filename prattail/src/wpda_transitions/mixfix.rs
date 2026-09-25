use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{StackSymbolV2, WpdaState, WpdaTokenSource};
use crate::wpda_walker::WpdaStepAction;

pub type MixfixPart<'a> = (u16, &'a [&'a str], &'a [&'a str], Option<&'a str>);
pub type MixfixRepetition<'a> = (u16, &'a [&'a str], &'a str, &'a [&'a str], u8);

/// Original per-member mixfix fan, also used by the factored dispatch fallback.
/// Rule order, short-circuit admission and weight evaluation are unchanged.
#[allow(clippy::too_many_arguments)]
pub fn member_fan<W: SemiringRef>(
    __mixfix_slice: &[(u8, u16, u16)],
    cur_bp: &u8,
    __mixfix_fallback_full: bool,
    mut __goal_admits: impl FnMut(u16) -> bool,
    mut __method_name_admits: impl FnMut(u16, u16) -> bool,
    mut lex_w: impl FnMut(f64, u16, u16) -> W,
    __cands: &mut Vec<crate::wpda_walker::ForkBranch<W>>,
) {
    for &(l_bp, result_src, rule_idx) in __mixfix_slice {
        if l_bp >= *cur_bp
            && __goal_admits(result_src)
            && (__mixfix_fallback_full || __method_name_admits(result_src, rule_idx))
        {
            __cands.push(crate::wpda_walker::ForkBranch {
                symbol: StackSymbolV2::mixfix_marker(result_src, rule_idx, 0, *cur_bp),
                weight: lex_w(crate::automata::lex_weight::BP_TIER_MIXFIX, result_src, rule_idx),
                new_state: WpdaState::MixfixLiteralRun {
                    result_src_idx: result_src,
                    rule_idx,
                    completed_idx: 0,
                    kind: 2,
                    sub_pos: 0,
                },
                action_kind: crate::wpda_walker::ForkActionKind::Push,
            });
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn continuation<'a, W: SemiringRef>(
    result_src_idx: &u16,
    rule_idx: &u16,
    completed_idx: &u8,
    frontier_top: Option<&crate::gss::WpdaGssNode>,
    _pos: usize,
    mut mixfix_part: impl FnMut(u16, u16, u8) -> Option<MixfixPart<'a>>,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    let __mixfix_continuation_bp = frontier_top
        .filter(|node| node.symbol.kind == crate::wpda_runtime::SymbolKind::MixfixMarker)
        .and_then(|node| node.symbol.continuation_bp)
        .expect(
            "MixfixContinuation invariant: frontier top must be a \
             MixfixMarker carrying its result continuation floor",
        );
    // B7 Pattern 1: between-operand transition. The
    // separator was consumed in Unwinding-MixfixMarker;
    // now ReplaceAndPush so the marker's bp updates to
    // `completed_idx` (= next operand index) AND a new
    // CategoryEntry(operand_src_idx) goes on top to
    // route the sub-parse to the correct element cat.
    // L12 follow-up B6 (2026-05-07): widened tuple.
    // mixfix_part returns
    //   Option<(operand_src, preceding, following)>
    // where preceding/following are &[&str].
    // The MixfixContinuation path uses operand_src to
    // route the sub-parse; preceding/following are
    // consumed by Unwinding-MixfixMarker and
    // MixfixLiteralRun (when needed).
    match mixfix_part(*result_src_idx, *rule_idx, *completed_idx) {
        // #131: a CAPTURE part has no category to enter, and its
        // `operand_src_idx` is the `MIXFIX_PART_NO_OPERAND` poison.
        // This arm exists so that reaching here with a capture part
        // SAYS SO instead of pushing a `CategoryEntry` for a
        // non-category. The capture is driven entirely by
        // `MixfixLiteralRun` (kinds 2 and 1), which is the state
        // every mixfix rule actually transits — nothing in the
        // emitted engine enters `MixfixContinuation` today — so this
        // is a guard on an unused route, not a second driver.
        Some((_, _preceding, _following, Some(capture_kind))) => WpdaStepAction::Error(format!(
            "mixfix part {} of (result={}, rule={}) is a `{}` token \
                 capture, which MixfixContinuation cannot dispatch — a \
                 capture consumes a token and has no category to enter. \
                 Report this as a macro bug.",
            completed_idx, result_src_idx, rule_idx, capture_kind,
        )),
        Some((operand_src_idx, _preceding, _following, None)) => {
            WpdaStepAction::ReplaceAndPush {
                replace_symbol: StackSymbolV2::mixfix_marker(
                    *result_src_idx,
                    *rule_idx,
                    *completed_idx,
                    __mixfix_continuation_bp,
                ),
                // GEN-1 goal-gate G1 (2026-06-28): strict
                // GOAL = the operand's category, so a
                // cross-cat Name operand (e.g. InputBindQuery
                // `n`) cannot over-extend past Name via `!`
                // (POutput Name→Proc) — Proc cannot reach
                // Name (prefix `@` edge excluded), so it is
                // dropped and the mixfix continuation matches.
                push_symbol: StackSymbolV2::category_entry_goal(operand_src_idx),
                weight: lex_one(),
                new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
            }
        },
        None => WpdaStepAction::Error(format!(
            "mixfix part {} not found for (result={}, rule={})",
            completed_idx, result_src_idx, rule_idx
        )),
    }
}

pub fn literal_targets(tokens: &dyn WpdaTokenSource, pos: usize, expected: &str) -> Vec<usize> {
    let mut targets: Vec<usize> = Vec::with_capacity(2);
    if tokens.peek_text(pos) == Some(expected) {
        if let Some(np) = tokens.next_pos(pos, 0) {
            targets.push(np);
        }
    }
    for (i, alt) in tokens.peek_alternatives(pos).iter().enumerate() {
        if alt.text == expected {
            if let Some(np) = tokens.next_pos(pos, i + 1) {
                if !targets.contains(&np) {
                    targets.push(np);
                }
            }
        }
    }
    targets
}

pub fn capture_consume<W: SemiringRef>(
    result_src_idx: &u16,
    rule_idx: &u16,
    __mixfix_continuation_bp: u8,
    capture_kind: &str,
    part_idx: u8,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    let __capture_kind: &str = capture_kind;
    let __part_idx: u8 = part_idx;
    WpdaStepAction::Fork {
        branches: vec![crate::wpda_walker::ForkBranch {
            symbol: StackSymbolV2::mixfix_marker(
                *result_src_idx,
                *rule_idx,
                __part_idx,
                __mixfix_continuation_bp,
            ),
            weight: lex_one(),
            new_state: WpdaState::MixfixLiteralRun {
                result_src_idx: *result_src_idx,
                rule_idx: *rule_idx,
                completed_idx: __part_idx,
                kind: 0,
                sub_pos: 0,
            },
            action_kind: crate::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndReplace {
                kind_name: __capture_kind.to_string(),
            },
        }],
        consume_trigger: false,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn checked_literal_consume<W: SemiringRef>(
    tokens: &dyn WpdaTokenSource,
    _pos: usize,
    result_src_idx: &u16,
    rule_idx: &u16,
    completed_idx: &u8,
    __mixfix_continuation_bp: u8,
    expected: &str,
    next_state: WpdaState,
    mut lex_one: impl FnMut() -> W,
) -> WpdaStepAction<W> {
    let __expected: &str = expected;
    let __next_state = next_state;
    let __targets = literal_targets(tokens, _pos, __expected);
    match __targets.len() {
        0 => WpdaStepAction::Error(format!(
            "mixfix literal mismatch: expected {:?} at pos {} \
                             (rule {}:{}) — no lattice edge matches",
            __expected, _pos, result_src_idx, rule_idx,
        )),
        1 => WpdaStepAction::ConsumeAtAndReplace {
            symbol: StackSymbolV2::mixfix_marker(
                *result_src_idx,
                *rule_idx,
                *completed_idx,
                __mixfix_continuation_bp,
            ),
            weight: lex_one(),
            new_state: __next_state,
            next_pos: __targets[0],
        },
        _ => WpdaStepAction::Fork {
            branches: __targets
                .iter()
                .map(|np| crate::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::mixfix_marker(
                        *result_src_idx,
                        *rule_idx,
                        *completed_idx,
                        __mixfix_continuation_bp,
                    ),
                    weight: lex_one(),
                    new_state: __next_state.clone(),
                    action_kind: crate::wpda_walker::ForkActionKind::ConsumeAtAndReplace {
                        next_pos: *np,
                    },
                })
                .collect(),
            consume_trigger: false,
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub fn literal_run<'a, W: SemiringRef>(
    result_src_idx: &u16,
    rule_idx: &u16,
    completed_idx: &u8,
    kind: &u8,
    sub_pos: &u8,
    __mixfix_continuation_bp: u8,
    _pos: usize,
    tokens: &dyn WpdaTokenSource,
    mut lex_one: impl FnMut() -> W,
    mut mixfix_part: impl FnMut(u16, u16, u8) -> Option<MixfixPart<'a>>,
    mut mixfix_parts_len: impl FnMut(u16, u16) -> Option<u8>,
    mut mixfix_rep: impl FnMut(u16, u16, u8) -> Option<MixfixRepetition<'a>>,
    mut mixfix_nullary_literals: impl FnMut(u16, u16) -> Option<&'a [&'a str]>,
) -> WpdaStepAction<W> {
    let part = mixfix_part(*result_src_idx, *rule_idx, *completed_idx);
    let parts_len = match mixfix_parts_len(*result_src_idx, *rule_idx) {
        Some(n) => n,
        None => {
            return WpdaStepAction::Error(format!(
                "mixfix_parts_len(result={}, rule={}) returned None — \
             codegen invariant violated",
                result_src_idx, rule_idx,
            ))
        },
    };
    // #307 ROOT-A D3 (2026-06-11; FV:
    // MixfixLiteralAccounting.{checked_run_iff_spells,
    // primary_equality_loses, unchecked_accepts_mismatch,
    // checked_never_fabricates, fork_completeness}):
    // membership-checked literal consume. A rule literal
    // matches iff its TEXT equals some out-edge of the
    // position (primary OR lattice alternative — single-
    // token primary equality would lose multi-length
    // lattice parses, e.g. the `-3` node). The consume
    // advances along the MATCHED edge's target, carried
    // explicitly (the generic advance is alt-0-hardwired).
    // No match (incl. vacuously at edge-less EOF/orphan
    // nodes — lattice peek SYNTHESIZES Some(Eof), never
    // None) ⇒ pure Error before any mutation
    // (advance-or-die). Multiple distinct targets (soft-
    // fail orphan duplication only) ⇒ Fork, never
    // pick-one. The PREVIOUS code consumed UNCHECKED
    // (`_expected` unused) — stealing enclosing
    // delimiters or fabricating positions: the ROOT-A
    // defect (rholang `x!(0)` never parsed).
    //
    // S1-FACTORING F5-2 (A-M3): the helper fn + macro
    // are extracted to `mixfix_literal_helpers` above —
    // `#mixfix_mlr_helpers_site_tokens` re-interpolates
    // them HERE (byte-identical) for languages without
    // factored mixfix cohorts; grouped languages hoist
    // them above the spine prelude instead (this site
    // is then empty).
    macro_rules! __mixfix_capture_consume {
        ($capture_kind:expr, $part_idx:expr) => {{
            let __capture_kind: &str = $capture_kind;
            let __part_idx: u8 = $part_idx;
            crate::wpda_transitions::mixfix::capture_consume(
                result_src_idx,
                rule_idx,
                __mixfix_continuation_bp,
                __capture_kind,
                __part_idx,
                || lex_one(),
            )
        }};
    }
    macro_rules! __checked_literal_consume {
        ($expected:expr, $next_state:expr) => {{
            let __expected: &str = $expected;
            let __next_state = $next_state;
            crate::wpda_transitions::mixfix::checked_literal_consume(
                tokens,
                _pos,
                result_src_idx,
                rule_idx,
                completed_idx,
                __mixfix_continuation_bp,
                __expected,
                __next_state,
                || lex_one(),
            )
        }};
    }
    match (*kind, part) {
        // ★ #131: the PRE-CAPTURE literal run. Structurally the
        // kind-2 arm below, except that when the preceding literals
        // are exhausted the part is satisfied by CONSUMING ONE TOKEN
        // rather than by dispatching an operand.
        //
        // This is the arm `Call . recv:Num, m:Ident, args:Vec(Num)
        // |- recv "." m "(" args.*sep(",") ")"` enters right after
        // its `.` trigger: part 0 is `m`, whose preceding run is
        // EMPTY, so control arrives here and demands one `Ident`.
        // Before it existed the same state fell through to the
        // operand dispatch and sub-parsed the non-category `Ident`,
        // which is why the rule had no realizable reading at ANY
        // arity — including arity zero, where no separator is ever
        // scanned and the `*sep` part is therefore not implicated.
        (2, Some((_, preceding, _following, Some(capture_kind)))) => {
            if (*sub_pos as usize) < preceding.len() {
                let expected = preceding[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 2,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else {
                __mixfix_capture_consume!(capture_kind, *completed_idx)
            }
        },
        // #307 ROOT-A D1: the NEW pre-operand literal run
        // — consumes parts[completed_idx].PRECEDING before
        // the operand dispatch; the marker stays at
        // completed_idx (the bump is owed only after the
        // operand completes). Empty preceding (Tern/PAmb)
        // passes straight through to the operand
        // (empty_pre_passthrough: zero blast radius).
        (2, Some((operand_src_idx, preceding, _following, None))) => {
            if (*sub_pos as usize) < preceding.len() {
                let expected = preceding[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 2,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else if operand_src_idx == *result_src_idx {
                // Part-0 operand under the marker — the
                // shipped convention, correct exactly when
                // the operand category equals the result
                // category (all shipped part-0 rules:
                // POutput q:Proc→Proc, PAmb, Tern); the
                // marker is the frontier top, so
                // PrefixDispatch derives the dispatch
                // category from it.
                WpdaStepAction::Advance(WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 })
            } else {
                // Cross-category part-0 operand: explicit
                // CategoryEntry push (the kind=1 proven
                // pattern) — closes the latent
                // wrong-category hole; the marker is NOT
                // bumped (bp counts completed operands).
                // GEN-1 goal-gate G1 (2026-06-28): strict
                // GOAL = the cross-cat operand's category
                // (e.g. InputBindQuery `lhs`:Name) so it
                // cannot over-extend past its category via a
                // cross-cat-out operator that cannot reach
                // back to the goal.
                WpdaStepAction::Push {
                    symbol: StackSymbolV2::category_entry_goal(operand_src_idx),
                    weight: lex_one(),
                    new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                }
            }
        },
        // #131: the POST-part literal run is IDENTICAL for a capture
        // part and an operand part — both have completed part
        // `completed_idx` and both owe its `following` literals, then
        // either the marker Pop or the hand-off to part
        // `completed_idx + 1`. `Call` arrives here with the method
        // name consumed and `following == ["("]`, then hands off to
        // the `*sep` repetition. So the capture kind is deliberately
        // NOT matched: there is nothing left to distinguish.
        (0, Some((_, _preceding, following, _))) => {
            if (*sub_pos as usize) < following.len() {
                // Consume following[sub_pos] — CHECKED.
                let expected = following[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 0,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else if *completed_idx + 1 == parts_len {
                // Last operand done; Pop the marker.
                WpdaStepAction::Pop {
                    weight: lex_one(),
                    new_state: WpdaState::InfixLoop { cur_bp: __mixfix_continuation_bp },
                }
            } else {
                // Transition to kind=1 to consume
                // preceding_terminals of the next operand.
                WpdaStepAction::Advance(WpdaState::MixfixLiteralRun {
                    result_src_idx: *result_src_idx,
                    rule_idx: *rule_idx,
                    completed_idx: *completed_idx,
                    kind: 1,
                    sub_pos: 0,
                })
            }
        },
        // GEN-1 B-3 (Stage S3): POST-REPETITION. The just-
        // completed part `completed_idx` was a `*sep` rep whose
        // CollectionLoop already consumed its close and popped
        // the CollectionMarker via Unwinding (leaving the
        // CollectionId in THIS marker's args). `mixfix_part` is
        // None for a rep slot, so we land here. The rep owns its
        // close (no `following` of its own): if it was the last
        // part, Pop the marker → FireAction (drains the
        // CollectionId); otherwise advance to kind=1 to set up
        // the next operand.
        (0, None) if mixfix_rep(*result_src_idx, *rule_idx, *completed_idx).is_some() => {
            if *completed_idx + 1 == parts_len {
                WpdaStepAction::Pop {
                    weight: lex_one(),
                    new_state: WpdaState::InfixLoop { cur_bp: __mixfix_continuation_bp },
                }
            } else {
                WpdaStepAction::Advance(WpdaState::MixfixLiteralRun {
                    result_src_idx: *result_src_idx,
                    rule_idx: *rule_idx,
                    completed_idx: *completed_idx,
                    kind: 1,
                    sub_pos: 0,
                })
            }
        },
        // GEN-1 B-3 (Stage S3): the repetition operand is PART 0
        // (the FIRST part, e.g. InputBindPolyadic
        // `lhs "," lhss.*sep(",") "<-" n`). The initial marker
        // push lands here (kind=2, completed_idx=0) and
        // `mixfix_part(.., 0)` is None. Enter the rep loop (see
        // the kind=1 rep arm below for the field rationale).
        (2, None) if mixfix_rep(*result_src_idx, *rule_idx, *completed_idx).is_some() => {
            let rep_idx = *completed_idx;
            let (_, preceding, _, _, _) = mixfix_rep(*result_src_idx, *rule_idx, rep_idx)
                .expect("guarded by mixfix_rep.is_some()");
            if (*sub_pos as usize) < preceding.len() {
                let expected = preceding[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 2,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else {
                WpdaStepAction::ReplaceAndPush {
                    replace_symbol: StackSymbolV2::mixfix_marker(
                        *result_src_idx,
                        *rule_idx,
                        rep_idx,
                        __mixfix_continuation_bp,
                    ),
                    push_symbol: StackSymbolV2::collection_marker(
                        *result_src_idx,
                        *rule_idx,
                        rep_idx,
                        0u8,
                    ),
                    weight: lex_one(),
                    new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                }
            }
        },
        // GEN-1 B-3 (Stage S3): the NEXT part is a `*sep`
        // repetition (e.g. POutput2Plus's `bs` after `a`). A rep
        // part may own preceding literals that are not part of a
        // prior operand (for example the `{` in a postfix DDL
        // builder). Consume that checked prelude before entering
        // the repetition. Then bump the marker to the rep part
        // index and push its CollectionMarker — the
        // runtime's `emit_push_side_effects` allocates the
        // accumulator and pushes the `CollectionId` arg into THIS
        // marker's frame; the rule action drains it when the
        // marker pops. PrefixDispatch (under a CollectionMarker
        // top) handles the empty rep (token == close →
        // ConsumeAtAndPop) and the first element (self- or
        // cross-cat) via the per-slot `collection_spec`.
        (1, _) if mixfix_rep(*result_src_idx, *rule_idx, *completed_idx + 1).is_some() => {
            let rep_idx = *completed_idx + 1;
            let (_, preceding, _, _, _) = mixfix_rep(*result_src_idx, *rule_idx, rep_idx)
                .expect("guarded by mixfix_rep.is_some()");
            if (*sub_pos as usize) < preceding.len() {
                let expected = preceding[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 1,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else {
                WpdaStepAction::ReplaceAndPush {
                    replace_symbol: StackSymbolV2::mixfix_marker(
                        *result_src_idx,
                        *rule_idx,
                        rep_idx,
                        __mixfix_continuation_bp,
                    ),
                    push_symbol: StackSymbolV2::collection_marker(
                        *result_src_idx,
                        *rule_idx,
                        rep_idx,
                        0u8,
                    ),
                    weight: lex_one(),
                    new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                }
            }
        },
        (1, _) => {
            let next_part = mixfix_part(*result_src_idx, *rule_idx, *completed_idx + 1);
            match next_part {
                // ★ #131: the NEXT part is a token capture. Same
                // between-part literal run as the operand case, but
                // the hand-off consumes one token instead of pushing
                // a `CategoryEntry` — and, exactly as the operand
                // hand-off does, it BUMPS the marker to
                // `completed_idx + 1` so the post-part run
                // (`kind: 0`) and the eventual action-arg accounting
                // both see the capture as a completed part.
                //
                // ⚠ Not reached by `Call`, whose capture is part 0
                // and therefore arrives via `kind: 2`. It IS the arm
                // a mid-rule capture after another operand needs
                // (`a "." m "." b`), and omitting it would have left
                // that shape falling into the operand branch below —
                // sub-parsing the poison `MIXFIX_PART_NO_OPERAND` as
                // a category. The two arms are written together
                // because the gap between them is exactly the class
                // of defect this change exists to remove.
                Some((_, preceding, _following, Some(capture_kind))) => {
                    if (*sub_pos as usize) < preceding.len() {
                        let expected = preceding[*sub_pos as usize];
                        __checked_literal_consume!(
                            expected,
                            WpdaState::MixfixLiteralRun {
                                result_src_idx: *result_src_idx,
                                rule_idx: *rule_idx,
                                completed_idx: *completed_idx,
                                kind: 1,
                                sub_pos: sub_pos + 1,
                            }
                        )
                    } else {
                        __mixfix_capture_consume!(capture_kind, *completed_idx + 1)
                    }
                },
                Some((operand_src_idx, preceding, _following, None)) => {
                    if (*sub_pos as usize) < preceding.len() {
                        // Consume preceding[sub_pos] — CHECKED (#307 D3).
                        let expected = preceding[*sub_pos as usize];
                        __checked_literal_consume!(
                            expected,
                            WpdaState::MixfixLiteralRun {
                                result_src_idx: *result_src_idx,
                                rule_idx: *rule_idx,
                                completed_idx: *completed_idx,
                                kind: 1,
                                sub_pos: sub_pos + 1,
                            }
                        )
                    } else {
                        // All literals consumed; push the next
                        // operand's CategoryEntry.
                        // GEN-1 goal-gate G1 (2026-06-28):
                        // strict GOAL = the next operand's
                        // category so a cross-cat Name operand
                        // (InputBindQuery `n`) stays bounded to
                        // Name and the `!?(` mixfix
                        // continuation matches instead of `!`
                        // (POutput) over-extending it.
                        WpdaStepAction::ReplaceAndPush {
                            replace_symbol: StackSymbolV2::mixfix_marker(
                                *result_src_idx,
                                *rule_idx,
                                *completed_idx + 1,
                                __mixfix_continuation_bp,
                            ),
                            push_symbol: StackSymbolV2::category_entry_goal(operand_src_idx),
                            weight: lex_one(),
                            new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: 0 },
                        }
                    }
                },
                None => WpdaStepAction::Error(format!(
                    "mixfix part {} not found for (result={}, rule={})",
                    completed_idx + 1,
                    result_src_idx,
                    rule_idx,
                )),
            }
        },
        // GEN-1 B-1 (Stage S2): 0-operand (nullary) mixfix
        // literal run. `part` is None (no inner operands)
        // and `parts_len == 0` distinguishes this from a
        // suppressed `*sep` repetition slot (parts_len >= 1,
        // which falls to the catch-all Error below until the
        // S3 handling lands). Consume the post-trigger
        // literals (`("`, `)"` for POutputEmpty; `size ( )`
        // for `.size()`) via membership-checked steps; when
        // exhausted, Pop the marker — firing the arity-1
        // (LHS-only) action (e.g. POutputEmpty(n), MSize(m)).
        (2, None) if parts_len == 0 => {
            let lits = mixfix_nullary_literals(*result_src_idx, *rule_idx).unwrap_or(&[]);
            if (*sub_pos as usize) < lits.len() {
                let expected = lits[*sub_pos as usize];
                __checked_literal_consume!(
                    expected,
                    WpdaState::MixfixLiteralRun {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        completed_idx: *completed_idx,
                        kind: 2,
                        sub_pos: sub_pos + 1,
                    }
                )
            } else {
                WpdaStepAction::Pop {
                    weight: lex_one(),
                    new_state: WpdaState::InfixLoop { cur_bp: __mixfix_continuation_bp },
                }
            }
        },
        _ => WpdaStepAction::Error(format!(
            "MixfixLiteralRun: invalid kind={} or missing part \
             for (result={}, rule={}, completed_idx={})",
            kind, result_src_idx, rule_idx, completed_idx,
        )),
    }
}
