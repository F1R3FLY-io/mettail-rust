# EP-P1 v3.1: synchronous resolved-body consumption (+ bounded in-flight parking)

> Status: v3.1 — Round-7 CONVERGED (2 critics: IMPLEMENT-WITH-CORRECTIONS, R7-1..R7-12) with
> ALL corrections folded in. The contract amendment (R7-6) landed @ f51ecb74; the mechanism
> was measured-in @ 79753c4b (idx 4: 3,476/3,504 = 99.2% post-resolution; in-flight 24;
> tail_divergent 0 under the CORRECTED post-reentry tail). This document is the
> implementation authority for the I-commit. Supersedes v1 (04-, REFUTED), v2 (05-,
> REFUTED-AS-SPECIFIED), and the pre-Round-7 v3 draft.

## 0. The mechanism

The first CrossCatLhs arrival at a `DispatchKey` (route=CrossCatLhs) is the WORKER: it
proceeds exactly as today; its pop resolves the body into the cohort cache (the Measure
resolve site, promoted to On — it additionally inserts the drain key when parked members
exist and the key is quiescent). An arrival at a RESOLVED ∧ QUIESCENT key consumes
synchronously IN PLACE (no push, no parking, zero materialization). Pre-quiescent arrivals
PARK (cap-checked, overflow→Proceed). Parked members revive at the end-of-step drain via the
SAME consume function. Un-resolved keys at EOI orphan-re-drive (re-injection re-launches the
pre-dispatch frame).

## 1. The consume function (R7-1..R7-4 folded)

```rust
/// Apply one resolved source body to a cursor sitting AT its CrossCatLhs
/// dispatch decision (the pre-push configuration). Realizes the amended
/// CrossCatLhsParking.v member_tail_config (T2): final state is
/// InfixLoop (constant — final_state_constant); the member-varying axis
/// is the REENTRY bit (pred != NONE); nothing of the worker's CONTROL
/// state is read (T3) — the snapshot supplies only the body and the two
/// DATA fields the body's sub-parse owns (R7-1/R7-2).
fn consume_crosscat_lhs_body(
    &mut self,
    cursor: &mut BranchCursor<W>,
    source_src_idx: u16,
    symbol_id: SppfId,
    hi_pos: usize,
    // R7-3: the push weight the per-cursor flow would have multiplied
    // (lex_one() singleton / BP_TIER_CROSSCAT_LHS fork) — explicit.
    push_weight: &W,
    // R7-1: the body's result category at the worker's pop (captured in
    // the WorkerSnapshot at the resolve site). The LATER Return-pop
    // D-strings re-sync + GroupingClose resolve read it; the arriving
    // cursor's own value is stale.
    worker_last_action_output_cat: Option<u16>,
    // R7-2: the worker's pending packing weight at pop (the body's
    // FireAction consumed it; the arriving cursor's own is stale —
    // the `-3!` per-packing distinction).
    worker_pending_packing_weight: W,
) {
    // (1) weight: weight_at_dispatch ⊗ symbol_weight_sum, push weight
    //     EXPLICIT (R7-3) — identical to the proven projection revive.
    let weight_at_dispatch = cursor.weight.times_ref(push_weight);
    let body_w = self.sppf.symbol_weight_sum(symbol_id);
    cursor.weight = weight_at_dispatch.times_ref(&body_w);
    // (2) the body onto the cursor's OWN sppf stack; position to hi.
    cursor.sppf_stack_id = self.sppf_stack_arena.intern_push(cursor.sppf_stack_id, symbol_id);
    cursor.pos = hi_pos;
    // (3) the data fields (R7-1/R7-2).
    cursor.last_action_output_cat = worker_last_action_output_cat;
    cursor.pending_packing_weight = worker_pending_packing_weight;
    // (4) the member tail (amended model): reentry iff pred != NONE,
    //     guarded VERBATIM like the real code (R7-4): the pre-reentry
    //     effective state must be in {InfixLoop, Unwinding} — total
    //     over the predecessor kinds (effective_state_total_in_guard),
    //     mirrored anyway so the code cannot drift from :16313-16366.
    let pred = cursor.node;
    let pred_present = pred != crate::gss::GSS_NODE_NONE && self.gss.node(pred).is_some();
    let effective = /* the :16313-16344 table over pred's symbol kind:
                       CategoryEntry→InfixLoop, GroupingMarker→Unwinding,
                       NONE/missing→InfixLoop, other→Unwinding */;
    if pred_present && matches!(effective, WpdaState::InfixLoop { .. } | WpdaState::Unwinding)
    {
        // the reentry (mirrors :16359-16366): category_entry(source) at
        // hi_pos, weight one, CrossCatLhsReentry edge, InfixLoop{0}.
        let _ = self.cursor_gss_push_with_kind(
            cursor,
            StackSymbolV2::category_entry(source_src_idx),
            hi_pos,
            W::one_ref(),
            crate::gss::EdgeKind::CrossCatLhsReentry { source_src_idx },
        );
        self.set_cursor_inner_state(cursor, WpdaState::InfixLoop { cur_bp: 0 });
    } else {
        self.set_cursor_inner_state(cursor, effective);
    }
    // NO dstrings_resync call (R7-1 finding: that block is
    // Return-pop-gated and never runs at a CrossCatLhs pop — the real
    // obligation is field (3) above, which the FUTURE Return pop reads).
}
```

Caller contract (R7-4): the in-place consume ends with
`return self.cursor_resolution_check(cursor);` (InfixLoop → Resolved — matching the
per-cursor arm's outcome; a bare Alive would re-step the cursor). The fidelity tests must
include a **pred=CollectionMarker member** (the `{c!(p)}` in-collection family — Round-7
critic A's splice-adjacent case).

## 2. Quiescence (R7-9 restated)

A key is CONSUMABLE iff `resolved ∧ no live body-producing lineage under the key`. A
body-producing lineage = a frontier cursor whose `incoming_edge_stack` CONTAINS one of the
key's CrossCatLhs edges — decidable by the EXISTING memoized `crosscat_lhs_stack_memo`
membership scan (one walk per distinct interned stack; already shipping at the attribution
memo). Do NOT use push−pop counting: it inverts under fork-above-push (1 push, N sibling
pops via inherited interned stacks — corpus-masked today because every duplicate is its own
push, but that is Off/Measure topology, not structure).

Realization: per-key live-lineage tracking via a small per-step refresh over the frontier
(piggybacking the attribution memo's scan results), OR lazily at the consume decision
(scan-on-demand with the memo). `registered_at_step: u64` is ADDED to the cache entry
(`step_counter` exists at wpda_walker.rs:871) for the age-timeout fallback:
`step_counter − registered_at_step > K ⇒ Proceed` (never park forever). Budget-Error
short-circuits quiescence trivially — the frontier freezes and the terminal-state check ends
the parse (R7-12; stated, not relied on silently).

**Validation obligation (R7-9):** the late-body case is ABSENT from the acceptance corpus
(0 alternate_bodies measured; resolved_transitions 50→53). A SEEDED multi-body-source input
(an ambiguous-span source operand — the short-ident vs longer-body shape of
dispatch_cohort.rs:346's alternate_bodies doc) is MANDATORY in the I-commit's test set, or
the quiescence rule ships unvalidated.

## 3. The On-mode decision at the push arm (non-cfg; R7-7 counter truth)

- `WorkerInserted` → Proceed (push; wrap side table; the lineage starts).
- `FailedHit` → Proceed (per-cursor failure path preserved; corpus failed_hits = 0).
- `InflightCollision` ∨ (resolved ∧ ¬quiescent) → `pause_cohort_member` with the singleton
  member shape (pre-push `cursor.clone()`, `weight_at_dispatch = cursor.weight ⊗ push_w`);
  bool=false (cap) → Proceed (counted `ep_p1_park_overflow_fallbacks`). Parked → Drop.
- `ResolvedHit{bodies}` ∧ quiescent → consume. Single body: in place + return
  `cursor_resolution_check`. Multi-body: clones of the PRE-consume cursor, one per body,
  ALL in the `ForkInto` vec (successors-replace semantics — verified), and **in
  deterministic mode set `self.deterministic = false` first** (R7-5, the :7812 precedent).
- Fork-path producer: the same decision inside `allocate_fork_push_child`'s new CrossCatLhs
  branch; member shape via `parent_frame_with_fork_metadata`; a consumed fork child is built
  WITHOUT the push and returned in the children Vec (plumbing verified trivial). Corpus-cold
  (0 fork spawns measured) — a seeded fork-path input is cheap insurance.

**Expected counters under On (R7-7 — state BEFORE the flip run):**
- `resolved_hits` ≈ UNCHANGED (~3,476 on idx 4) — consume happens ON register's ResolvedHit.
- `crosscat_lhs_delegates_spawned` → ≈ workers (~4); `dup_at_pos_source` (6,5): 3311 → ~0.
- `cast_then_infix_steps` (WIDENED memo, re-baselined OFF — §5 Step-0) → the ≥60% gate.

## 4. The drain + orphan

Parked members revive at the end-of-step drain: OWN set (`pending_crosscat_lhs_drain_keys`,
inserted by the worker's pop-resolve when parked members exist ∧ quiescent) + OWN loop that
revives **one cursor per (body, member) — NO ×snapshot axis** (R7-11; consume is
snapshot-independent), pushing into the drain's local `new_cursors` BEFORE the
`branch_cursors` replacement (R6-4). Drain-before-`resolve_at_end_of_input` ordering is
verified (the drain is inside step_fanout; revived members get their continuation step via
progress_made). EOI orphans: the existing origin-agnostic re-drive re-launches the
pre-dispatch frame (verified end-to-end); the orphan probe is LOAD-BEARING (idx 4 has a real
unresolved CrossCatLhs worker).

## 5. Gates (corrected)

**Step-0 (R7-8, PREREQUISITE):** widen the `cast_then_infix_steps` memo to also match
`CrossCatLhsReentry`; re-run OFF on idx 4; RE-PIN the ledger baseline (the 149,645/≤59,858
figures are stale — CrossCatLhs-only memo; 149,685 observed under Measure). The gate is
≤40% of the re-baselined OFF figure. Without Step-0 the On drop is a rename artifact.

Then: battery OFF + ON byte-identical (9 suites; rhocalc_tests 126/0 BOTH states; -3!
canary; chain neutrality); the NEW cast-then-compare AmbiguityBudget test **targeting the
mid-park frontier dip** (k near Off's peak where On's parking would hide an overflow Off
reports — byte-identical or a recorded justified delta) (R7-10); the multi-body seed input
(§2); the orphan probe; the pred=CollectionMarker fidelity test (§1); fork-path seed
(optional insurance). Flip experiment with the §3 counter shapes. L-commit: Welch N≥15
release `cast_tower_bench`; idx 6 completing under On = the depth-independence evidence;
flip the env default.

## 6. Risk register (post-Round-7 residual)

| # | Risk | Falsification |
|---|---|---|
| 1 | Quiescence live-lineage scan cost or staleness | the age-timeout→Proceed fallback bounds it; measure the scan count under On |
| 2 | The late-body seed input reveals consume-vs-quiescence ordering bugs | the seeded input IS the test (R7-9) |
| 3 | Budget semantics at the mid-park dip | the R7-10 test |
| 4 | Fork-path consume (corpus-cold) | seeded fork-path input |
| 5 | The Return-pop D-strings re-sync reading the consumed cursor's fields | the pred=CollectionMarker + `{c!(p)}` family tests; rhocalc_tests both states |
