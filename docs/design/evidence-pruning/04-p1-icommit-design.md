# EP-P1 I-commit design: share EquivKey-identical CrossCatLhs delegate dispatches

> Status: v1 REFUTED (red-team round 5, 2 critics CONVERGED on REDESIGN — see 03-red-team-ledger.md
> Round 5). Salvage corrections R5-1..R5-8 required for any v2. DO NOT IMPLEMENT v1.
> Measured basis: ledger 02-program-ledger.md §P1 Step-0 (share gate saturated: idx4
> 3504 spawns / 3500 dup / key (6,5) = 3311x; waste baseline 149,645; target <= 59,858).

## 0. Headline finding

The CrossCatLhs route is NOT a `CrossCatDelegate` dispatch, and the shipped cohort cache never
touches it. Reusing the cohort path is possible and correct, but it CANNOT be done by
"generalizing one engagement condition" at the existing register site, because CrossCatLhs
registers, resolves, and revives at different sites and via different GSS edges than
CrossCatDelegate. Reuse = `DispatchCohortCache` / `DispatchKey` / `EquivKey` / `register` /
`resolve` / `take_pending_for_drain_all` / `revive_cohort_member_with_snapshot` unchanged,
wired via three new hooks on the CrossCatLhs edge. No new merge machinery (I7 discharged).

### The two routes, side by side

| | CrossCatDelegate (cohort-shared today) | CrossCatLhs (the measured waste) |
|---|---|---|
| Emitted by | prefix.rs Pass-2a singleton `Push{rule_at(...).with_kind_return(), CrossCatDelegate{src,bp}}` (prefix.rs:1341-1352) + Fork branch (CrossCatProjection desc) | prefix.rs Pass-0 singleton `PushWithEdgeKind{category_entry(src), PrefixDispatch{pos,cur_bp:0}, EdgeKind::CrossCatLhs{src}}` (prefix.rs:1301-1324) + Fork branch `ForkActionKind::PushCrossCatLhs` |
| Pushed symbol | a `Return` marker (`with_kind_return`) | `category_entry(source_src_idx)` directly |
| New state | `CrossCatDelegate{source, inner_cur_bp}` | `PrefixDispatch{pos, cur_bp:0}` |
| Register site | `allocate_fork_push_child` (wpda_walker.rs:15192), guarded `matches!(new_state, CrossCatDelegate)` | NONE — singleton is a bare PushWithEdgeKind arm (wpda_walker.rs:6920); the Fork path fails the guard and falls to `allocate_uncached_push_child` |
| Edge kind on GSS | `CrossCatProjection{src,bp,wrap_cat,wrap_rule}` | `CrossCatLhs{source_src_idx}` |
| Resolve site | `cursor_gss_pop_via_edge` (16365-16431): popping CrossCatProjection calls `dispatch_cohort_cache.resolve(...)` | popping CrossCatLhs does the REENTRY (16186-16208: re-push CrossCatLhsReentry + InfixLoop{cur_bp:0}), NOT a cohort resolve |
| Result flow-back | end-of-step drain `take_pending_for_drain_all` -> `revive_cohort_member_with_snapshot` (10836-10885) | same cursor continues in place; no broadcast |

### What the 3311 duplicates ARE

The D-commit spawn counter sits in the singleton PushWithEdgeKind arm, firing once per
`apply_action_to_cursor` call = once per drained Tomita arc. The 3311 spawns at (6,5) are 3311
DISTINCT cursor-steps: cursors arriving in `PrefixDispatch{pos:6, cur_bp:0}` that differ in a
TomitaKey axis (node / incoming_edge_stack top / collection_stack_depth) — distinct GSS return
contexts from the K^depth fan. Cross-cursor duplicates with distinct continuations; NOT one
cursor re-pushing; NOT members of an existing cohort. The sub-parse above the dispatch
(category_entry(src) + PrefixDispatch{pos}) is byte-identical across all (engine.step reads
only (state, gss-top, pos, tokens)); the return frames below differ — exactly the invariant
the cohort cache exploits.

### The FULL sound identity key

```
DispatchKey { pos: <dispatch pos>, source_src_idx, inner_cur_bp: 0, wrap_cat, wrap_rule }
```
- pos = cursor.pos at the push (cache axis; equiv() drops it)
- source_src_idx, inner_cur_bp=0 (merge axes — the EquivKey; prefix.rs hard-codes cur_bp:0 at 1317/1376)
- wrap_cat, wrap_rule = REQUIRED cache discriminators (M4 tombstone). CrossCatLhs has no
  Return marker to read these from; the sound source is the HOST category whose PrefixDispatch
  arm fired (the arm's own #category_src_idx) — thread via widening EdgeKind::CrossCatLhs to
  carry (wrap_cat, wrap_rule). If a faithful wrap_rule is unavailable, use a per-arm constant
  sentinel — over-discrimination reduces sharing (safe); under-discrimination re-conflates
  (unsound, the M4 failure).
- GSS return node / continuation identity is NOT in the key — it is the per-member divergence
  the cohort PRESERVES (CohortMember.return_frame / CohortMemberState).
- Weight is NOT a key axis — recomputed per member at revive (weight_at_dispatch (x) symbol_weight_sum).

## 1. Kill switch

`EpP1Mode { Off, Shadow, On }`, `from_env()` reading PRATTAIL_EP_P1 (default Off for the
I-commit; L-commit flips after Welch). Walker FIELD set in all 3 constructors (struct literals
at wpda_walker.rs ~3428/3509/3589) — read once per construction, NOT a process OnceLock (tests
run both arms in one process). `ep_p1_recovery_enabled()` derived from recovery_config for the
shadow partition index.

## 2. Shadow counters (walker_stats.rs, I4 convention, [u64; WPDA_STATE_CLASS_COUNT*2])

- `ep_p1_shadow_would_share_total` — 2nd+ EquivKey/cache arrival that =on would coalesce.
- `ep_p1_shadow_share_divergent_total` — would-shared dispatch whose broadcast SPPF body would
  DIFFER from the per-cursor re-parse. MUST stay all-0 (the integrity gate; =shadow hard stop).
- `ep_p1_shadow_steps_after_would_share` — apply_action steps re-parsing under a would-shared
  frame after the would-share point (the direct waste the flip removes).
Index = wpda_state_class*2 + recovery_enabled. Non-zero-slot Display printing.
SHADOW MUST NOT MUTATE the shared dispatch_cohort_cache (it would perturb the CrossCatDelegate
resolve path): use an observation-only `ep_p1_shadow_seen: FxHashMap<DispatchKey,u32>` on the
walker, cleared per parse; would-share = count > 1. Sanity: shadow total ~= 3500 on idx4.

## 3. The three hooks

### Hook A — REGISTER at the CrossCatLhs push
In the PushWithEdgeKind arm (wpda_walker.rs:6920) inside the existing
`if let EdgeKind::CrossCatLhs` block; the Fork path (`ForkActionKind::PushCrossCatLhs`,
~8012-8064 -> allocate_fork_push_child) routes through the SAME helper:

```
fn crosscat_lhs_cohort_decision(&mut self, cursor, source_src_idx, wrap_cat, wrap_rule,
                                dispatch_pos) -> CrosscatLhsCohortAction<W>
```
- Off  -> Proceed (push as today; ZERO cache mutation; byte-identical hot path).
- Shadow -> observation map increment; would-share counter when count>1; then Proceed.
- On -> `dispatch_cohort_cache.register(key, worker_pre)`:
  - WorkerInserted -> Proceed (this cursor is the worker).
  - InflightCollision -> pause_cohort_member(key, member from pre-push cursor); Suppress (Drop).
  - ResolvedHit -> pause synthetic member + mark drain key (mirror 15355-15399); Drop. Revival
    happens at the unified end-of-step drain (keeps the arm returning a single CursorOutcome).
  - FailedHit -> Suppress.
worker_pre weight: cursor.weight (x) branch weight (lex_one() singleton / BP_TIER_CROSSCAT_LHS fork).

### Hook B — RESOLVE at the CrossCatLhs pop
In `cursor_gss_pop_via_edge` (~16340), sibling to the CrossCatProjection resolve (16365-16431):
when popped edge is CrossCatLhs and mode==On: symbol_id = sppf_stack top; category guard
(symbol cat == source); reconstruct the FULL key from the popped node's pos + the WIDENED edge
payload (wrap_cat/wrap_rule); `resolve(key, symbol_id, cursor.pos, dispatch_pos, snap)`;
FirstResolve|SnapshotAppended -> mark `pending_crosscat_lhs_drain_keys`.
THE ONE STRUCTURAL DIVERGENCE from CrossCatProjection: `WorkerSnapshot.worker_inner_state`
must encode the REENTRY entry point = InfixLoop{cur_bp:0} (the state the reentry block sets at
16207), and the revive must use the CrossCatLhsReentry edge kind, so a revived member
reproduces the post-reentry configuration (re-pushed category_entry/CrossCatLhsReentry frame +
source SPPF on its sppf_stack + pos=hi_pos) without re-parsing. Reentry guard (16189-16194:
popped.kind==CategoryEntry, pred_id != NONE, effective_new_state in {InfixLoop, Unwinding})
must be satisfied by the revived configuration on its NEXT pop.

### Hook C — REVIVE via the existing end-of-step drain
Drain loop (10833-10921) reused; add `revive_edge_kind` (or is_crosscat_lhs) param to
`revive_cohort_member_with_snapshot` (15665) — CrossCatDelegate drain passes CrossCatProjection
(unchanged); CrossCatLhs drain passes CrossCatLhsReentry{source_src_idx}. Everything else in
revive identical (weight at 15705-06, sppf_stack push 15711-13, pos=hi_pos, cohort_origin
tagging 15694-15700 with the EquivKey-narrow merge projection). Drain routing: separate
`pending_crosscat_lhs_drain_keys` set + second drain loop, runs only when mode==On and
non-empty (empty on cast-free inputs -> byte-identical hot path; CrossCatDelegate loop untouched).

## 4. Change list

1. wpda_walker.rs: EpP1Mode (~80); walker fields (ep_p1_mode, ep_p1_shadow_seen,
   pending_crosscat_lhs_drain_keys) + 3 constructor literals + per-parse resets;
   PushWithEdgeKind arm engagement; crosscat_lhs_cohort_decision (~15167 vicinity);
   allocate_fork_push_child routing for the Fork branch; Hook B in cursor_gss_pop_via_edge;
   revive_cohort_member_with_snapshot signature; second drain loop; shadow instrumentation.
2. gss.rs: widen EdgeKind::CrossCatLhs {source_src_idx} -> {source_src_idx, wrap_cat, wrap_rule}
   (match sites: wpda_walker.rs 6578, 6933, 8032, 16119, 16186; prefix.rs 1319, 1363; most bind
   via {source_src_idx, ..}).
3. macros prefix.rs: emit wrap_cat: #category_src_idx + wrap_rule sentinel at both emit sites.
4. walker_stats.rs: 3 shadow fields + default + Display.
5. dispatch_cohort.rs: NO structural change (doc note only).

## 5. Verification

Build gate both cfgs + languages ws examples. Battery with PRATTAIL_EP_P1 UNSET and =on:
ledtest 220/0 SENTINEL; edge 229/0 byte-identical OFF/ON (comparison_after_cast_results +
operator_chains_after_casts); rhocalc_tests 126/0 BOTH STATES (the {c!(p)} reentry family =
most sensitive CrossCatLhs consumer); calc 1330/0; rhocalc_op 530/1; prattail-lib 3980/0;
-3! canary; rocq-prattail-wpda green (M-commit already landed).
SHADOW GATE before enabling: =shadow + walker-stats, full battery + corpus;
ep_p1_shadow_share_divergent_total all-0 HARD; would_share_total ~3500 on idx4 (cross-check).
=off vs =shadow byte-identical battery.
FLIP EXPERIMENT: idx4 =on: key (6,5) 3311 -> ~1, spawned 3504 -> ~4, cast_then_infix_steps
149,645 -> <= 59,858; if <60% record residue + attribution -> P2/P3 (plan-sanctioned).
NEUTRAL: chain_50/100/200 byte-identical (CrossCatLhs is cast-only; drain set empty on chains).
Trigger-free inputs (idx 1/2/3/5): OFF==ON (gate already suppresses; share is identity —
equiv_dedup_identity_when_singleton made observable).
L-commit: Welch N>=15 cast_tower_bench release, p<0.05, treatment<control, zero behavioral
diffs both states; idx6 SHOULD complete under =on (depth-independence acceptance evidence);
flip from_env default to On.

## 6. Risks

1. Reentry-state fidelity (THE structural-difference risk): revived member must re-fire the
   reentry semantics; falsify via edge clusters + rhocalc_tests both states; shadow divergent
   counter must be 0 first.
2. Wrap-discriminator under-population (M4 re-conflation): sentinel wrap_rule must never be
   LESS discriminating than per-(host,source)-arm; over-discrimination safe.
3. AmbiguityBudget shifts: revived-member fanout vs per-cursor fanout could shift frontier
   budget decisions; reuses worker_snapshot_observationally_eq dedup; assert no budget-error delta.
4. Lex-fork blast radius: -3 canary byte-identical (extension_preserves_189_behavior).
5. Shadow inertness: shadow must use the observation map, NEVER the real cache.

## 7. Verdict on mechanism

It IS the cohort path (same cache/key/quotient) wired to a second producer, with one deliberate
divergence (reentry-state snapshot + CrossCatLhsReentry revive edge). Evidence does NOT point
to a cohort-member-level fix or sequential re-push artifact. I7 discharged: only edge-payload
widening + three call sites + drain routing are new.
