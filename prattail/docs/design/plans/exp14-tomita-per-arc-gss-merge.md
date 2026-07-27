# Exp 14 — Tomita Per-Arc GSS-Cursor Merging (REDESIGNED)

**Status:** Plan agent redesign, 2026-05-27. Supersedes prior plan (commit `cd48071` tree). The prior plan had a soundness gap: arbitrary cursors at the same coarsened TomitaKey are NOT guaranteed to share the heavy `CohortShell` fields (`recovery_deltas`, `visited_dispatch`, `visited_recovery`, `binder_scope_marks`, `optional_scope_marks`, `sppf_collection_arena`) that the L1-L6 dispatch-site cohort enforced **by construction**. This redesign moves those 6 fields **per-arc** (Option A), keeping the `CohortShell` only for the truly TomitaKey-invariant axes plus the constructed L1-L6 dispatch cohorts.

**Tip at design time:** `cd48071` on `feature/wfst-architecture`.

**Status of shipped substages (under the prior plan):**
- **Substage 0 (`9662b81`)** — TomitaKey projection instrumentation. SHIPPED, dead code, **retained verbatim** (the 5-tuple TomitaKey is still the correct merge key; the soundness fix lives in the arc/shell partition, not the key).
- **Substage 1 (`ea63fc6`)** — `tomita_frontier.rs` data structure module. SHIPPED, dead code, **requires a Substage 1.5 follow-up** to move 6 heavy fields from `FrontierNode.shell` to `FrontierArc`. The current shipped shape is unsound under arbitrary-cursor ingest.
- **Substage 2 (`19f04f9`)** — `classify_for_tomita` + `apply_obs_invariant_to_frontier`. SHIPPED, dead code, **requires update under Substage 2.5** so the shell mutation does not mask divergent per-arc heavy fields.

**Cross-references**
- `prattail/docs/design/plans/chain-10000-experiments-ledger.md`
- `prattail/docs/design/plans/cohort-lazy-materialization.md` (L1-L6 foundational doc — `~_obs` definition at §1.2; the construction-time guarantee that justifies shell sharing is at `dispatch_cohort.rs:597-604` `pause_cohort_member`)
- `prattail/docs/design/plans/exp15-cps-trampolined-walker.md` (alternative architecture; see Executive Summary discussion of structural complexity)
- `~/.claude/projects/-home-dylon-Workspace-f1r3fly-io-mettail-rust/memory/2026-05-27-exp14-exp15-multi-session-pickup.md` (shipped Substage 0/1/2 retrospective)

---

## 1. Goal and non-goals

### Goals

- **G1 (load-bearing):** Close the chain_10000 24 GB ceiling architecturally by collapsing per-cursor branching at its source. Target: chain_500 LEFT-assoc walker peak ≤ 1.0 GB (≥ 4.8× reduction vs current 4.87 GB), with `edge_stack_arena` ≤ 30 MB (vs 3.44 GB) and `visited_dispatch` ≤ 80 MB (vs 1.14 GB). Note: the original plan's ≤ 600 MB (8×) target is now relaxed because Option A's per-arc heavy-field storage costs ~80 B additional per arc.
- **G2:** Reduce `cohort_cursors_emitted` from 28.9 M to ≤ 10 M on left_assoc_500 (≥ 2.9× reduction; matches the empirical 3.0× merge factor from Substage 0 measurement at commit `9662b81`).
- **G3:** Preserve every passing test at tip `cd48071`: `cargo test --release -p prattail --lib` = **4198/0**, `trampoline_tests` skip-chain = **18/0/6**, PLUS chain_500 LEFT-assoc previously-passing test continues to pass.
- **G4:** Preserve full ambiguity: SPPF dedup at `(nt, lo, hi)` Symbol and `(rule_idx, children)` Packing must continue to expose **every** derivation a per-cursor baseline would have exposed. The `-3!` multi-packing test family must survive every substage.
- **G5:** All N+R derived-test panels (LEFT-assoc 50/100/200; RIGHT-assoc 50/100/200/1000) pass Welch's two-sample t-test at p<0.05 with treatment_mean ≤ baseline_mean + 1 SE on every substage commit.
- **G6:** Generalize over the mettail-rust feature set (binders, mixfix, cross-cat, recovery, optional groups, collections, predicates, lex-Fork, cohort sharing). No grammar-specific overfitting.
- **G7 (NEW):** **Soundness invariant**: at every TomitaKey collision, ingest preserves each absorbed cursor's complete observable state. Specifically, the 6 heavy fields (`recovery_deltas`, `visited_dispatch`, `visited_recovery`, `binder_scope_marks`, `optional_scope_marks`, `sppf_collection_arena`) live PER-ARC, not on the shell. Materializing an arc back to a `BranchCursor` reconstructs the ORIGINAL cursor's state, not a shell-overwritten approximation.

### Non-goals

- **N1:** Does NOT migrate the runtime semiring (LexicographicWeight stays).
- **N2:** Does NOT change SPPF layout.
- **N3:** Does NOT remove `merge_equivalent_cursors` — retained as a post-step cleanup pass.
- **N4:** Does NOT replace L1-L6 cohort-lazy infrastructure. The existing `CohortShell` continues to back **H12 dispatch cohorts** (which DO satisfy the construction-time `~_obs` equivalence). Tomita uses a **reduced `TomitaShell`** containing only the truly key-invariant axes plus a slim 6-field per-arc payload.
- **N5:** Does NOT introduce feature gates, env vars, or runtime flags.
- **N6:** Does NOT change the engine.
- **N7:** Does NOT alter the recovery state machine.
- **N8:** Does NOT touch `cesk_store.rs`, `green_thread.rs`, `logict.rs`.

---

## 2. Theoretical foundation

### 2.1 Tomita (1985), Scott-Johnstone (2010), Esparza-Kiefer-Luttenberger (2007)

**Tomita (1985)**, *An Efficient Augmented-Context-Free Parsing Algorithm*. The GLR parser shares stack-tip identity via the **graph-structured stack (GSS)**. When `N` parsers reach the same LR(0) state at the same input position, they coalesce into **one** stack node with `N` outgoing arcs representing the divergent histories.

**Scott-Johnstone (2010)**, *GLL Parsing*. The 4-tuple **descriptor** `(L, u, i, w)` makes equivalent parsers merge.

**Esparza-Kiefer-Luttenberger (2007)**. Weighted GLR is sound iff the weight aggregator is a closed semiring with `⊕` idempotent. `LexicographicWeight` satisfies this.

### 2.2 PraTTaIL's existing equivalence relation

The current `ConfigKey` (`wpda_walker.rs:1827-1929`) is the Scott-Johnstone descriptor augmented with PraTTaIL-specific provenance:

```
ConfigKey = (state, node, pos, incoming_edge, collection_depth,
             cohort_origin, sppf_top,
             lex_alt_idx, weight_src_idx, weight_rule_idx, lex_fork_stamp)
```

Two cursors with the same `ConfigKey` already merge inside `merge_equivalent_cursors`. The chain_10000 problem is that Fork-arm sites synthesize cursors with distinct ConfigKey histories that never reach merge in a collapsible form.

### 2.3 Tomita merge in PraTTaIL terms

Define the **Tomita merge predicate** as a coarsening of `ConfigKey`:

```
TomitaKey = (state, node, pos, incoming_edge_top, collection_depth)
```

This drops the four per-cursor lex provenance axes plus `cohort_origin` plus `sppf_top`. Cursors with the same `TomitaKey` but distinct ConfigKey are **arc-mergeable**: they share a **frontier shell** (the 5 TomitaKey axes), with all per-cursor-divergent fields living **on the arcs**.

### 2.4 Soundness lemma

**Claim:** For `LexicographicWeight: IdempotentSemiring`, the Tomita-merge representation under the **per-arc heavy-field layout (§3.1 Option A)** is observationally equivalent to today's per-cursor representation.

**Proof sketch:**

1. The engine's `step` function is pure of cursor state at every dispatch site.
2. Two cursors with the same `TomitaKey` therefore receive the same `WpdaStepAction` from the engine.
3. The 5 TomitaKey axes are what the engine reads from the cursor to compute the next action; therefore the next action is identical across all arcs at the same frontier.
4. For an action whose effect is observation-invariant on the per-arc state (Advance / Accept / Error / Idle — the shell-mutation-only family):
   - Apply the action to the **frontier shell** once (mutates `state` field). The arcs are unchanged (no per-arc mutation needed).
   - Re-key each arc into the next-generation frontier map.
5. For an action that requires per-arc work (Push/Pop/Replace/ConsumeAndPush — anything that multiplies into `weight` or mutates per-arc state):
   - **Materialize** each arc to a Concrete `BranchCursor` via `materialize_branch_cursor_from_arc(shell, arc)` (the redesigned primitive — see §3.4). This reconstructs the cursor's COMPLETE state from `(shell, arc)`, with all 6 heavy fields read from the ARC, not from the shell.
   - Step each concrete cursor; resulting cursors re-enter the frontier map at next-gen ingest.

### 2.4.1 Soundness fix — addresses the L1-L6-to-arbitrary-cursor generalization gap

**The gap (the prior plan's blind spot).** The prior plan's §2.4 claimed:

> 4. For an action observation-divergent ... Materialize the frontier shell to N Concrete cursors via `cohort_lazy::materialize_branch_cursor`; step each; results re-enter the merge at next step.

But `materialize_branch_cursor(shell, member_state)` at `cohort_lazy.rs:593-628` reads ALL 6 heavy fields (`recovery_deltas`, `visited_dispatch`, `visited_recovery`, `binder_scope_marks`, `optional_scope_marks`, `sppf_collection_arena`) **from the shell**, not from the per-member state. This is sound for H12 dispatch cohorts because the H12 construction site (`dispatch_cohort.rs:571-640` `pause_cohort_member`) sets the shell ONCE from the first member's `BranchCursor`, and only admits subsequent members that **already satisfy `~_obs`** (per the `dispatch_cohort::DispatchKey` equivalence and the cohort-lazy-materialization.md §1.2 definition: same `node`, `incoming_edge_stack`, `collection_depth`, ... AND same `recovery_deltas` journal, `visited_dispatch ⊆`, etc.).

The TomitaKey is a 5-tuple that captures only `(state, node, pos, edge_top, collection_depth)`. Two cursors at the same TomitaKey can have:
- Different `recovery_deltas` (one pushed `BuilderDelta::PushIdent("foo")` upstream; another pushed `BuilderDelta::PushIdent("bar")` — same TomitaKey, different journals).
- Different `visited_dispatch` / `visited_recovery` (one already attempted dispatch at `(pos=5, cat=Int, bp=10)`; another has a clean defense set).
- Different `binder_scope_marks` / `optional_scope_marks` (one opened a binder scope upstream; another didn't).
- Different `sppf_collection_arena` (one accumulated 3 SPPF children into slot 0; another accumulated 2 different children into slot 0).

Under the prior plan's ingest (`tomita_frontier.rs:292-312` `register_arc`), the FIRST registration sets the shell; subsequent registrations **drop their `shell_if_new`** and absorb their arc onto the existing node. Materializing back via `materialize_branch_cursor(shell, arc.to_member_state())` would reconstruct EVERY cursor with the FIRST cursor's heavy fields. This is **observationally unsound** in two ways:

1. **AdvanceWithEffect dropping deltas**: cursor A pushed `BuilderDelta::PushIdent("foo")`; cursor B pushed `BuilderDelta::PushIdent("bar")`. After Tomita ingest, both materialize with cursor A's deltas; on commit_winner, cursor B's recovery actions never execute. The AST surface is silently corrupted (the wrong ident appears in the final tree).
2. **Cycle defense corruption**: cursor C has empty `visited_dispatch`; cursor D has visited `(pos=5, cat=Int, bp=10)`. After Tomita ingest, both materialize with cursor C's defense set OR cursor D's defense set. The clean cursor inherits the dirty cursor's prior visits (false-positive cycle defense → premature Drop, dropping valid derivations) or the dirty cursor inherits the clean defense (false-negative → infinite recursion + OOM).

Both failure modes are silent — they manifest as derivation loss or OOM, not as a panic or test failure unless the specific multi-cursor heavy-field-divergent fixture happens to be in the test suite. The `-3!` multi-packing fixture and the recovery/binder fixtures (LedTest, rholang) would surface (1); the chain workloads with cross-cat would surface (2).

**The fix (Option A — per-arc storage; chosen for reasons in §2.5).** Move the 6 heavy fields from `CohortShell` to `FrontierArc`. Specifically:

```rust
pub struct TomitaShell<W: SemiringRef> {
    // The 5 TomitaKey axes (genuinely TomitaKey-invariant by ingest construction).
    pub node: GssNodeId,
    pub pos: usize,
    pub inner_state: WpdaState,
    pub incoming_edge_stack_id: EdgeStackId,
    pub collection_depth: u8,
    // The 4 dispatch-derived axes (genuinely TomitaKey-invariant — these
    // are derived from the engine's reading of the 5-tuple, and the engine
    // is pure of cursor state per the §2.4.1 step purity argument).
    pub dispatch_key: DispatchKey,
    pub sppf_stack_baseline_id: StackId,
    pub recovery_depth: u8,
    // NOTE: lex_alt_idx / weight_src_idx / weight_rule_idx / lex_fork_stamp
    // moved to FrontierArc (they are per-arc divergent — different lex
    // provenance can land on the same TomitaKey).
    pub _phantom: PhantomData<W>,
}

pub struct FrontierArc<W: SemiringRef> {
    // Existing per-arc divergent axes (Substage 1 shipped these).
    pub weight: W,
    pub pending_packing_weight: W,
    pub sppf_stack_id: StackId,
    pub source_priority: u32,
    pub cohort_origin: Option<DispatchKey>,
    pub last_action_output_cat: Option<u16>,
    pub cohort_revive_depth: u32,
    pub lex_fork_path: Arc<Vec<LexForkStamp>>,
    pub lex_alt_idx: u16,
    pub weight_src_idx: u16,
    pub weight_rule_idx: u16,
    // NEW (Substage 1.5 — Option A soundness fix):
    pub recovery_deltas: Arc<Vec<BuilderDelta>>,
    pub visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
    pub visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
    pub binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
    pub optional_scope_marks: Arc<Vec<usize>>,
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
}
```

Each `Arc<...>` is an O(1) refcount bump at ingest — it does NOT deep-clone. When two cursors land on the same TomitaKey, their arcs each carry their own Arc handles; if those handles point to the same underlying object (because the cursors share a Fork ancestor), Rust's Arc refcounting makes both arcs cheaply share storage. If they point to different objects (because the cursors diverged upstream), each arc keeps its own.

**Correctness walkthrough.**

For ingest: when cursor C at TomitaKey T arrives at the frontier:
- If T is new: allocate `FrontierNode { shell: TomitaShell::from(C), arcs: vec![FrontierArc::from(C)] }`. The shell captures C's `(state, node, pos, edge_top, collection_depth)`; the arc captures C's 6 heavy field Arcs + 11 other per-arc fields.
- If T exists: push `FrontierArc::from(C)` onto the existing node's arcs. Shell unchanged (no mutation of any heavy field).

For ObsInvariantOverArcs step (Advance / Accept / Error / Idle):
- One `engine.step(shell.inner_state, ...)` call produces one action.
- Apply via `apply_obs_invariant_to_frontier(node, action)`: mutates `shell.inner_state` only. The 6 heavy fields per arc are untouched.
- Re-ingest each arc into the next-generation map with new TomitaKey `(action.new_state, shell.node, shell.pos, shell.edge_top, shell.collection_depth)`. Heavy fields ride along verbatim per arc.

For ObsDivergentOverArcs step (Push / Pop / Replace / ConsumeAndPush / Fork / AdvanceWithEffect / ...):
- Materialize each arc via `materialize_branch_cursor_from_arc(shell, arc)`:
  ```rust
  BranchCursor {
      node: shell.node,
      pos: shell.pos,
      inner_state: shell.inner_state.clone(),
      incoming_edge_stack_id: shell.incoming_edge_stack_id,
      collection_stack_depth: shell.collection_depth,
      recovery_depth: shell.recovery_depth,
      sppf_stack_id: arc.sppf_stack_id,
      weight: arc.weight.clone(),
      pending_packing_weight: arc.pending_packing_weight.clone(),
      source_priority: arc.source_priority,
      cohort_origin: arc.cohort_origin.clone(),
      last_action_output_cat: arc.last_action_output_cat,
      cohort_revive_depth: arc.cohort_revive_depth,
      lex_fork_path: Arc::clone(&arc.lex_fork_path),
      // THE FIX: all 6 heavy fields read from arc, not from shell:
      recovery_deltas: Arc::clone(&arc.recovery_deltas),
      visited_dispatch: Arc::clone(&arc.visited_dispatch),
      visited_recovery: Arc::clone(&arc.visited_recovery),
      binder_scope_marks: (*arc.binder_scope_marks).clone(),
      optional_scope_marks: (*arc.optional_scope_marks).clone(),
      sppf_collection_arena: Arc::clone(&arc.sppf_collection_arena),
  }
  ```
- Each materialized cursor's heavy fields match what THAT cursor originally had. The reconstruction is observationally identical to the original cursor.

This restores soundness while preserving the 5-tuple TomitaKey merge benefit (the empirical 3× factor from Substage 0).

### 2.5 The merge equivalence as a quotient — restated under Option A

`BranchCursor / TomitaKey` partitions the frontier into equivalence classes. The Tomita representation is `|{T}|` frontier shells (~ 500 at chain_500 = one per chain element) × the arc set per shell. Per Exp 16 r3 attribution and Substage 0 measurement, the average arc-count per TomitaKey is ~3 at chain_500 (the empirical merge factor from `experiment_id=4`).

Per-arc size budget under Option A:
- 11 light fields (~52 B): weight, pending_packing_weight, sppf_stack_id, source_priority, cohort_origin, last_action_output_cat, cohort_revive_depth, lex_fork_path (Arc), lex_alt_idx, weight_src_idx, weight_rule_idx.
- 6 heavy field Arcs (~48 B = 6 × 8 B Arc pointer): recovery_deltas, visited_dispatch, visited_recovery, binder_scope_marks, optional_scope_marks, sppf_collection_arena.
- Total: ~100 B per arc.

Per-shell size budget (~48 B): 5 TomitaKey axes + dispatch_key + sppf_stack_baseline_id + recovery_depth + phantom.

**Why Option A is the right choice** (decision rationale per §3.0):

| Criterion | Option A (per-arc heavy) | Option B (key-discriminated) | Option C (gated ingest) |
|-----------|--------------------------|------------------------------|-------------------------|
| Soundness | TRIVIAL (per-arc state) | TRIVIAL (Arc pointer-eq required for merge) | TRIVIAL (gated by pointer-eq) |
| Merge factor preserved | 3.0× (Substage 0 measurement preserved verbatim) | ~1.1-1.5× (Arc-pointer-eq is rare across genuinely independent cursors) | ~1.1-1.5× (same Arc-pointer-eq rarity) |
| Per-arc cost | ~100 B (vs 52 B prior) | ~52 B + ~80 B key overhead | ~52 B + dual-storage overhead |
| Implementation complexity | LOW — extend FrontierArc with 6 Arcs; update materialize | HIGH — key hashing on 6 Arc pointers; Hash impl on Arc is unusual | MEDIUM — gated insertion with fallback path |
| Memory at chain_500 (Option A) | 28.9M × 100 B = 2.9 GB arcs + 500 × 48 B shells = 24 KB shells; net ≈ 2.9 GB. vs current 28.9M × 512 B = 14.8 GB. **5.1× reduction** preserved. |
| Memory at chain_500 (Option B/C, conservative ~1.3× merge) | Most cursors would not merge → minimal reduction; close to baseline 14.8 GB. **0.0-1.3× reduction** = not viable. |

Under Option A, the projected merge benefit is the FULL Substage 0 figure of 3.0× (because every cursor at the same TomitaKey merges, regardless of upstream Arc divergence). Under Options B/C, only cursors that genuinely share Arcs would merge — and Fork-arm siblings IMMEDIATELY diverge on most heavy fields after the first `Arc::make_mut` in either sibling (recovery_deltas push, visited_dispatch insert, binder scope open). Empirically Fork-arm siblings rarely share `visited_dispatch` Arcs more than 1-2 steps after their fork; the Arc-pointer-eq merge benefit would converge to ~1.0× quickly.

**Hybrid considered + rejected.** A hybrid "Option A for `recovery_deltas` + `binder_scope_marks` (mutation-heavy); Option B for `visited_dispatch` + `visited_recovery` (read-heavy)" was considered. Rejected because it requires bifurcating the merge predicate by field, which (i) doubles the maintenance burden of the ingest classifier, (ii) introduces a partial-merge state that the materialize path must handle separately, and (iii) the visited_* sets are the LARGEST heavy fields (~712× content dedup factor per Exp 16 r3) — keying on them defeats the merge before it starts. Option A clean per-arc storage with Arc-refcount sharing achieves the same hot-path sharing without the predicate bifurcation.

**Memory accounting recap.**

| State | chain_500 LEFT-assoc peak (estimated) |
|-------|----------------------------------------|
| Pre-Exp-14 baseline (tip `cd48071`) | 4.87 GB walker peak, 14.8 GB cohort_cursors_emitted footprint |
| Post-Exp-14 Option A redesigned plan | ≤ 1.0 GB walker peak (target G1), ~2.9 GB cohort_cursors_emitted footprint with 3× arc merge |
| Comparison: Option A relative to prior plan's projected 1.5 GB | +0.4 GB cost from per-arc heavy Arcs |
| Comparison: Option A relative to baseline | 4.87× reduction (vs prior plan's projected 8×; the extra cost buys soundness) |

The original plan's 8× target was unsound (soundness gap would have caused silent derivation loss); the redesigned 4.87× target is sound and still architecturally significant.

---

## 3. Architecture changes

### 3.0 Option choice

**Option A (per-arc heavy-field storage) is chosen** for the reasons summarized in §2.5. Decision rationale: preserves the empirical 3× merge factor; trivially sound; simplest implementation (one struct extension + one materialize update); per-arc cost increase is ~80 B (Arc pointers are 8 B; deep-clone is deferred to actual mutation).

### 3.1 Frontier merge map data structure (REDESIGNED)

**Module:** `prattail/src/tomita_frontier.rs` (already shipped at `ea63fc6`; **Substage 1.5 extends it**).

The redesigned struct definitions:

```rust
/// The Tomita-merge key. UNCHANGED from Substage 1 shipped form.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct TomitaKey {
    pub state: WpdaState,
    pub node: GssNodeId,
    pub pos: usize,
    pub incoming_edge_top: Option<GssEdgeId>,
    pub collection_depth: u8,
}

/// The redesigned (Option A) frontier shell. Strictly the TomitaKey-
/// invariant axes — anything per-arc divergent lives on FrontierArc.
///
/// vs. the prior shipped Substage 1 `Arc<CohortShell<W>>` reuse: this
/// type is DISTINCT from CohortShell. The L1-L6 CohortShell continues
/// to back H12 dispatch cohorts (which are construction-time guaranteed
/// to share heavy fields). TomitaShell is the strictly-soundness-safe
/// 5-tuple-invariant subset for general-purpose frontier merging.
pub struct TomitaShell<W: SemiringRef> {
    // The 5 TomitaKey axes (cached for materialize/step):
    pub node: GssNodeId,
    pub pos: usize,
    pub inner_state: WpdaState,
    pub incoming_edge_stack_id: EdgeStackId,
    pub collection_depth: u8,
    // The 3 dispatch-derived axes (TomitaKey-invariant by step purity):
    pub dispatch_key: DispatchKey,
    pub sppf_stack_baseline_id: StackId,
    pub recovery_depth: u8,
    pub _phantom: PhantomData<W>,
}

/// One arc into a frontier shell. Carries ALL per-cursor-divergent
/// state (Substage 1's 11 light fields + the 6 heavy field Arcs that
/// the Option A soundness fix moves from shell to arc).
pub struct FrontierArc<W: SemiringRef> {
    // Substage 1 shipped fields (light, ~52 B):
    pub weight: W,
    pub pending_packing_weight: W,
    pub sppf_stack_id: StackId,
    pub source_priority: u32,
    pub cohort_origin: Option<DispatchKey>,
    pub last_action_output_cat: Option<u16>,
    pub cohort_revive_depth: u32,
    pub lex_fork_path: Arc<Vec<LexForkStamp>>,
    pub lex_alt_idx: u16,
    pub weight_src_idx: u16,
    pub weight_rule_idx: u16,
    // Substage 1.5 NEW fields (Option A soundness fix; 6 Arcs = ~48 B):
    pub recovery_deltas: Arc<Vec<BuilderDelta>>,
    pub visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
    pub visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
    pub binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
    pub optional_scope_marks: Arc<Vec<usize>>,
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
}

/// Frontier node: one TomitaShell + N FrontierArcs.
pub struct FrontierNode<W: SemiringRef> {
    pub shell: Arc<TomitaShell<W>>,
    pub arcs: Vec<FrontierArc<W>>,
    pub generation: u32,
}
```

**Where the heavy fields live.** Each `FrontierArc<W>` holds 6 `Arc<...>` handles. At ingest, each `Arc<...>` is cloned via `Arc::clone` from the source cursor's field (O(1) refcount bump). If two cursors land on the same TomitaKey AND happen to have the same Arc handle (i.e., they share a Fork ancestor and neither has mutated the field since the fork), both arcs hold the same Arc pointer — physical memory shared. If they differ, each holds its own Arc — physical memory separate. This is the natural Rust Arc-CoW pattern; no special handling required.

**Map module (UNCHANGED from Substage 1 shipped):** `TomitaFrontierMap<W>` API is preserved verbatim. The only change is the `register_arc` signature accepts the new `TomitaShell<W>` instead of `CohortShell<W>` for fresh-node allocation.

### 3.2 step_fanout becomes "iterate frontier nodes" (UPDATED for Option A)

**Tomita (Substage 3+):**

```
// Phase 1: ingest every frame into the Tomita frontier map.
self.tomita_frontier_map.begin_generation();
for frame in drained:
    match frame {
        Frame::Concrete(c) => {
            let key = TomitaKey::from_cursor(&c);
            let shell = TomitaShell::from_cursor(&c);
            let arc = FrontierArc::from_cursor(&c);  // CLONES 6 heavy Arcs (O(1) each).
            self.tomita_frontier_map.register_arc(key, shell, arc);
        }
        Frame::Cohort(cf) => {
            // Each member becomes a fresh arc; the H12 cohort's CohortShell
            // is "deflated" into a TomitaShell + per-member FrontierArc.
            // The H12 cohort's `recovery_deltas` (etc.) are read from
            // CohortShell — sound because H12 already enforced ~_obs.
            for member in &cf.members {
                let cursor = materialize_branch_cursor(&cf.shell, member);
                let key = TomitaKey::from_cursor(&cursor);
                let shell = TomitaShell::from_cursor(&cursor);
                let arc = FrontierArc::from_cursor(&cursor);
                self.tomita_frontier_map.register_arc(key, shell, arc);
            }
        }
    }

// Phase 2: iterate frontier NODES.
for (key, node) in self.tomita_frontier_map.drain_current_generation():
    // One engine.step per shell (per frontier).
    let action = self.engine.step(&node.shell.inner_state, ...);
    match TomitaDivergence::classify(&action):
        ObsInvariantOverArcs => {
            // Apply once to shell; arcs unchanged.
            apply_obs_invariant_to_frontier(&mut node, action.clone());
            // Re-ingest at the next generation under the new TomitaKey
            // (shell.inner_state has been mutated by the apply).
            let new_key = TomitaKey::from_shell(&node.shell);
            // Move the shell into the next gen as-is (Arc unchanged); push
            // arcs onto the next-gen node verbatim.
            for arc in node.arcs:
                self.tomita_frontier_map.register_arc(new_key.clone(), node.shell.as_ref().clone(), arc);
        }
        ObsDivergentOverArcs => {
            // Materialize each arc to a Concrete cursor using the
            // per-arc heavy fields. Step each via the existing path;
            // results re-enter the frontier map at next-gen ingest.
            for arc in node.arcs:
                let cursor = materialize_branch_cursor_from_arc(&node.shell, &arc);
                let outcome = self.apply_action_to_cursor(&mut cursor, action.clone(), ...);
                // outcome's resulting cursors go into new_cursors (which is
                // re-ingested into the frontier map on the next iteration).
                emit_outcome_to_new_cursors(outcome, &mut new_cursors);
        }
        DispatchResolved => {
            // The H12 cross-cat dispatch has resolved; fan out per
            // (arc, snapshot) pair. Each fan-out registers as a fresh
            // arc at the next-gen frontier map.
            handle_dispatch_resolved(...);
        }
```

**N-to-1 reduction.** Per the Substage 0 measurement, the average arc-count per TomitaKey is 3 (range 2.7-3.1×). For the ObsInvariant majority (Advance / Accept / Error / Idle dominate the chain interior), per-frontier-step count drops from N cursors to 1 shell-mutation + N arc re-ingests. For the ObsDivergent minority (Push/Pop/Replace/ConsumeAndPush at structural boundaries), per-arc materialize cost is N × `materialize_branch_cursor_from_arc` calls (each is a struct copy with 6 Arc clones + 2 small Vec clones — ~100 B per call, no deep-clones since the Arcs are refcounted).

### 3.3 SPPF emission stays correct (UNCHANGED — already addressed by Substage 1)

The redesigned data model does not change SPPF dedup. Per-arc `weight` and `pending_packing_weight` are consumed verbatim by `emit_fire_action` at materialize-then-step time; the SPPF Symbol/Packing dedup at `(nt, lo, hi)` / `(rule_idx, children)` keys works as before. Per-arc divergent `sppf_stack_id` is preserved.

### 3.4 Weight aggregation across merged frontier arcs (UNCHANGED)

Per-arc `weight ← arc.weight ⊗ action.weight` and `pending_packing_weight ← arc.pending_packing_weight ⊗ action.weight` are computed at materialize-then-step time (ObsDivergent path) OR at re-ingest time (ObsInvariant path that includes a weight component — though Substage 4's ObsInvariant scope intentionally excludes weight-carrying actions).

### 3.5 visited_dispatch / visited_recovery handling — per-arc Arc with refcount sharing

The 1.14 GB `visited_dispatch` dominator at chain_500 LEFT-assoc remains the largest target. Under Option A:
- Each arc carries `visited_dispatch: Arc<FxHashSet<...>>`.
- When cursor A at TomitaKey T forks to children A1, A2 (each becoming an arc at the next frontier), both A1 and A2 hold `Arc::clone(&A.visited_dispatch)` — refcount = 2 + arc-storage of original.
- When A1 or A2 mutates (via `Arc::make_mut` at the apply_action_to_cursor call from the ObsDivergent materialize path), only THAT arc's Arc-pointer gets the deep-clone; sibling's Arc-pointer is untouched.
- For two cursors at the same TomitaKey that DIDN'T share a Fork ancestor (e.g., two distinct chain-interior paths reaching the same state), their `visited_dispatch` Arcs are distinct. Each arc carries its own Arc-pointer. Storage is NOT shared between them.

**Storage estimate.** Each arc's 6 heavy field Arcs occupy ~48 B (six 8-byte pointers). The underlying HashSet/Vec storage is reference-counted: if two arcs share the same Arc (via Fork ancestry), the underlying storage is single-copy. If they don't share, both copies exist. The empirical Arc-sharing rate is a function of the workload's Fork structure.

**Comparison to original 8× target.** The prior plan claimed `visited_dispatch` would collapse to ~50 MB total (23× reduction) by hosting one Arc on the shell. Under Option A, each arc holds its own Arc — total storage is bounded by (number of distinct content snapshots) × (snapshot size). At chain_500 LEFT-assoc with 28.9M cursors and the Exp 16 r3 712× content dedup factor, there are ~40K distinct snapshot identities. Each snapshot held by N arcs costs (snapshot size × 1) + (N × 8 B Arc pointer). For 40K snapshots × ~720 cursors-per-snapshot mean × ~16 B HashSet header overhead × shared underlying buckets, storage is ~40 K × ~3 KB ≈ 120 MB for the underlying sets + ~28.9M × 8 B = 230 MB for the per-arc Arc pointers = **~350 MB**. This is HIGHER than the prior plan's claimed ~50 MB but is the correct sound figure. Target G1 (≤ 1.0 GB walker peak) absorbs this.

### 3.6 Interaction with L1-L6 cohort-lazy infrastructure (REDESIGNED)

**Decision: KEEP L1-L6 for H12 dispatch cohorts; ADD TomitaShell + FrontierArc for general-purpose Tomita merging.**

The two layers are now clearly distinct:

| Layer | Purpose | Shell type | Members type | ~_obs guarantee |
|-------|---------|------------|--------------|-----------------|
| L1-L6 (H12 dispatch) | Cross-cat-projection sub-parse dedup | `CohortShell<W>` (15 axes) | `CohortMemberState<W>` (7 axes) | YES — `pause_cohort_member` only admits members matching DispatchKey, which implies `~_obs` per cohort-lazy-materialization.md §1.2 |
| Tomita frontier (Exp 14) | General-purpose per-step merge | `TomitaShell<W>` (8 axes — 5 key + 3 dispatch-derived) | `FrontierArc<W>` (17 axes — 11 light + 6 heavy Arcs) | NO general guarantee — heavy fields stored per-arc |

At step_fanout's per-frame ingest:
- `Frame::Concrete(c)` → flatten to one FrontierArc at TomitaKey(c).
- `Frame::Cohort(cf)` → materialize each member of cf via existing `materialize_branch_cursor` (sound under H12 ~_obs), then flatten each resulting cursor to a FrontierArc at TomitaKey(cursor).

**The H12 cohort layer is upstream of the Tomita layer.** H12 dedups sub-parse work; Tomita dedups frontier cursor state. They compose orthogonally.

The shipped Substage 1 code reuses `Arc<CohortShell<W>>` in `FrontierNode.shell`. Substage 1.5 introduces `TomitaShell<W>` as a separate type to clarify the soundness boundary AND to drop the 6 heavy field storage from the shell. The `Arc<CohortShell<W>>` retained in `dispatch_cohort.rs::DispatchCacheEntry::InFlight.cohort_shell` is unchanged.

### 3.7 Interaction with merge_equivalent_cursors (UNCHANGED)

`merge_equivalent_cursors` retained as the concrete-cursor residual collapse pass on the post-materialize cursors. The pre-materialize Tomita layer subsumes most of the merge work; the post-materialize residual handles cursors that emerge from ObsDivergent materialization in the same step.

### 3.8 IterativeChainAbsorb special-case (UNCHANGED scope; same as prior plan)

`IterativeChainAbsorb` continues to be classified `ObsDivergentOverArcs` initially. Substage 5 graduates it to `ObsInvariantOverArcs` IF the `already_chained` shortcut applies AND the action is weight-only-divergent.

---

## 4. API and data model changes

### 4.1 `prattail/src/tomita_frontier.rs` (Substage 1 SHIPPED ~677 LOC; Substage 1.5 extends ~+150 LOC)

**Substage 1.5 changes:**
- Add `TomitaShell<W>` struct with the 8 axes per §3.1.
- Extend `FrontierArc<W>` with the 6 NEW heavy field Arcs per §3.1.
- Change `FrontierNode<W>.shell` from `Arc<CohortShell<W>>` to `Arc<TomitaShell<W>>`.
- Update `register_arc` signature to take `TomitaShell<W>` instead of `CohortShell<W>` for fresh-node alloc.
- Add `TomitaShell::from_cursor(c: &BranchCursor<W>) -> Self` constructor.
- Add `FrontierArc::from_cursor(c: &BranchCursor<W>) -> Self` constructor (the 6 NEW fields use `Arc::clone(&c.recovery_deltas)`, etc.).
- Add `materialize_branch_cursor_from_arc(shell: &TomitaShell<W>, arc: &FrontierArc<W>) -> BranchCursor<W>` per §2.4.1.
- Extend the test suite with ~8 NEW tests covering: heavy-field ingest preserves Arc identity; materialize round-trip restores all 6 heavy fields verbatim; two cursors with distinct `recovery_deltas` Arcs land at same TomitaKey produce 2 arcs each preserving its own `recovery_deltas`; round-trip from cursor → arc → cursor produces observationally equivalent cursor.

**Substage 1 shipped fields (UNCHANGED):** TomitaKey, TomitaFrontierMap, TomitaDivergence enum. All preserved verbatim.

### 4.2 `prattail/src/cohort_lazy.rs` (Substage 2 SHIPPED extensions; Substage 2.5 updates ~+50 LOC)

**Substage 2.5 changes:**
- Update `apply_obs_invariant_to_frontier(node: &mut FrontierNode<W>, action: ...)` to use the new `TomitaShell<W>` (not `CohortShell<W>`). Logic unchanged: still `Arc::make_mut(&mut node.shell).inner_state = new_state` for the Advance arm.
- `classify_for_tomita` is unchanged (Substage 2 shipped this; the classification predicate operates on action shape, not shell content).
- Add documentation note linking to §2.4.1 explaining why TomitaShell is distinct from CohortShell.

### 4.3 `prattail/src/wpda_walker.rs` (Substage 3 onward; +400-500 LOC total)

**Field block:** add `tomita_frontier_map: TomitaFrontierMap<W>`. ~10 LOC.

**reset():** add `self.tomita_frontier_map.clear()`. ~3 LOC.

**step_fanout:** restructure per §3.2. ~150-200 LOC.

**No change to BranchCursor struct, no change to ConfigKey, no change to apply_action_to_cursor.** These are all preserved verbatim. Tomita is additive — the cursor representation is the "expanded form" of an arc.

### 4.4 `prattail/src/walker_stats.rs` (Substage 3 add fields; ~+75 LOC)

Add `TomitaFrontierStats` substruct: `frontier_nodes_peak`, `arcs_per_node_peak`, `arc_dedup_hits`, `shell_invariant_steps`, `arc_divergent_materializations`, `tomita_key_distinct_count`, `arcs_to_cursors_ratio`. Display impl + Default + reset hook.

### 4.5 `prattail/src/dispatch_cohort.rs` (UNCHANGED)

H12 cohort cache operates as the cross-cat-projection dispatch dedup. Tomita is the post-dispatch-cohort layer.

### 4.6-4.10 (UNCHANGED from prior plan)

`automata/semiring.rs`, `sppf.rs`, `path_tree_arena.rs`, `gss.rs`, `trampoline_tests.rs` all unchanged (test re-enables at Substage 7).

---

## 5. Substage breakdown

### Substage 0 — Walker-stats instrumentation (SHIPPED, retrospective)

**Status:** Shipped at commit `9662b81`. UNCHANGED by the redesign — the 5-tuple TomitaKey instrumentation correctly measures the merge factor for the redesigned data model (Option A preserves the same TomitaKey predicate).

**Empirical measurement (preserved):**
- LEFT-assoc chain_50/100/200: 2.85× / 3.05× / 3.11× merge factor.
- RIGHT-assoc chain_50/100/200/1000: 2.68× / 2.70× / 2.70× / 2.71× merge factor.
- Welch ACCEPT at p=9.2e-8, Cohen's d = 14.2.
- pgmcp experiment_id=4 decision_id=3.

**Retrospective under the redesigned data model.** The 3× merge factor figure is preserved verbatim under Option A. Reasoning: the redesign does NOT change the TomitaKey predicate or the ingest collision logic; it changes only what GETS STORED at each arc (the 6 heavy field Arcs move from shell to arc). The empirical merge benefit (3 arcs per frontier shell on average) is preserved. What changes is the per-arc memory cost (~52 B → ~100 B) — but at chain_500 LEFT-assoc this still yields ~5× reduction vs the per-cursor baseline (14.8 GB cohort_cursors_emitted footprint → 2.9 GB under Option A vs 1.5 GB under the unsound prior plan). The unsound 8× target was not achievable WITHOUT silently dropping derivations; the redesigned 5× target IS achievable with full soundness.

### Substage 1 — TomitaFrontierMap data structure (SHIPPED, status reviewed)

**Status:** Shipped at commit `ea63fc6`. Dead code in tree. The FrontierArc carries 11 light fields (52 B); FrontierNode reuses `Arc<CohortShell<W>>` for the shell.

**Soundness sanity-check under redesign.** The shipped Substage 1 module is structurally unsound as-shipped (it would drop heavy-field divergence at the first cursor ingest). However, because the module is dead code (no walker integration), no production behavior is affected.

**Required follow-up: Substage 1.5** is INSERTED into the substage sequence (see below). This is the gate that the user-mandated "no soundness violation" check imposes: Substage 1.5 must complete BEFORE Substage 3 (the ingest pass).

### Substage 1.5 — TomitaShell + per-arc heavy-field FrontierArc extension (NEW — soundness fix)

**Goal**: Implement the Option A redesign: introduce `TomitaShell<W>` distinct from `CohortShell<W>`; extend `FrontierArc<W>` with the 6 heavy field Arcs; update `materialize_branch_cursor_from_arc` to read heavy fields from the arc, not the shell. Dead code (no walker integration yet).

**LOC budget**: ~200 (struct extensions + ~8 NEW tests).

**Code paths touched**:
- `prattail/src/tomita_frontier.rs:50-72` extend (no changes to TomitaKey).
- `prattail/src/tomita_frontier.rs:98-122` extend `FrontierArc<W>` with 6 NEW fields.
- `prattail/src/tomita_frontier.rs:175-218` change `FrontierNode<W>.shell` type; update constructors.
- `prattail/src/tomita_frontier.rs:~220-380` add `TomitaShell<W>` definition + `from_cursor` constructor + `materialize_branch_cursor_from_arc` function.
- `prattail/src/tomita_frontier.rs:~410-680` extend tests (+8 NEW: heavy-field preservation under ingest dedup; materialize round-trip restores heavy fields; 2 arcs with distinct recovery_deltas at same TomitaKey survive ingest; etc.).
- `prattail/src/cohort_lazy.rs:691-704` update `apply_obs_invariant_to_frontier` signature to take `TomitaShell` not `CohortShell`.
- `prattail/src/cohort_lazy.rs:~365-395` update `classify_for_tomita` (no logic change; documentation note).

**Welch-gate**: not applicable (no behavior change). Run the 7-arm Welch panel anyway to capture noise baseline.

**Welch falsifier**: any arm LOSS at p<0.05 → REVERT.

**Gauntlet falsifier**: 4198 + 8 new = **4206/0** target. Substage 1 added 18 tests; Substage 1.5 adds 8 more.

**pgmcp lifecycle**:
- `experiment_open(title="Exp 14 Substage 1.5 — TomitaShell + per-arc heavy fields (soundness fix)", kind="design_correction", primary_metric="left_assoc_chain_50_wall_time_ms", lower_is_better=true)`.
- ACCEPT iff Welch NEUTRAL on all 7 arms AND gauntlet 4206/0 AND the 8 new tests all pass.

**Memory falsifier**: not applicable.

**Estimated wall time**: 1 day (4h LOC + 2h tests + 2h Welch+commit).

### Substage 2 — TomitaDivergence::classify (SHIPPED, status reviewed)

**Status:** Shipped at commit `19f04f9`. Dead code. The classifier itself is shape-only (depends on action variant, not on shell content) — UNCHANGED by the redesign.

**Substage 2.5 follow-up**: update `apply_obs_invariant_to_frontier` to use TomitaShell (~20 LOC).

### Substage 2.5 — Update apply_obs_invariant_to_frontier for TomitaShell (NEW — bundled with 1.5)

**Goal**: trivial signature update to accept `&mut FrontierNode<W>` whose shell is `Arc<TomitaShell<W>>` (not `Arc<CohortShell<W>>`).

**LOC budget**: ~20.

**Bundling**: Substage 1.5 and Substage 2.5 ship as ONE commit titled "Phase F.13 chain_10000 Exp 14 Substage 1.5+2.5: TomitaShell + per-arc heavy fields (soundness fix)". This is because the type change requires both files updated simultaneously to compile.

### Substage 3 — step_fanout Tomita ingest pass (rewritten under Option A)

**Goal**: Wire the Tomita ingest at `step_fanout` entry. Every drained frame becomes an arc in `TomitaFrontierMap`. The produce path drains the map immediately via `materialize_branch_cursor_from_arc` per arc, routes through existing `apply_action_to_cursor`. **Round-trip preserves observational semantics** because the per-arc heavy fields are reconstructed verbatim into each materialized cursor.

**LOC budget**: ~250.

**Code paths touched** (UNCHANGED from prior plan):
- `prattail/src/wpda_walker.rs:7618-7900` restructured (~150 LOC delta).
- `prattail/src/wpda_walker.rs:~2745` reset() add `tomita_frontier_map.clear()` (~3 LOC).
- Field at 621-720 (~10 LOC).
- Constructor parity at 2556/2630/2699 (~20 LOC).
- Use `FrontierArc::from_cursor` + `TomitaShell::from_cursor` at ingest sites.
- Use `materialize_branch_cursor_from_arc` at materialize sites.

**Welch-gate**: full 7-arm panel.

**Welch falsifier**: any arm LOSS at p<0.05 → REVERT.

**Gauntlet falsifier**: 4206/0 (no new tests).

**pgmcp lifecycle**:
- `experiment_open(title="Exp 14 Substage 3 — ingest pass (Option A round-trip)", kind="optimization", primary_metric="left_assoc_chain_50_wall_time_ms", lower_is_better=true)`.
- Record per-arm samples (N=15 hyperfine).
- `experiment_decide` per arm.

**Memory falsifier** (separate pgmcp experiment):
- `experiment_open(primary_metric="chain_500_left_assoc_rss_mb_peak", lower_is_better=true)`.
- N=3 RSS-curve runs. ACCEPT iff RSS ≤ baseline RSS + 5% (round-trip is expected to be RSS-neutral; small overhead from per-arc Arc cloning is acceptable up to 5%).

**Estimated wall time**: 1.5 days.

### Substages 4-6 (substantively UNCHANGED scope; minor wording updates)

**Substage 4** — ObsInvariantOverArcs fast path for Advance/Accept/Error/Idle. ~200 LOC. First memory win. The shell-mutation-once + no-arc-mutation pattern is sound under Option A (the heavy fields per arc are not touched). Target: chain_500 LEFT-assoc RSS -30%.

**Substage 5** — Graduate Push/Pop/Replace/ConsumeAndPush to ObsInvariantOverArcs when EdgeKind is convergent. ~350 LOC. THE CHAIN-INTERIOR PAYOFF. Sound under Option A IFF the action's per-arc effect is ONLY the weight multiply (no per-arc heavy-field mutation). Push/Pop with convergent EdgeKind satisfies this (weight multiply only). Target: chain_500 LEFT-assoc RSS -55% (revised down from -60% to account for per-arc heavy-field storage cost).

**Substage 6** — Arc weight ⊕-aggregation on TomitaKey collision (inline at register_arc). ~200 LOC. **CRITICAL UPDATE under Option A**: arcs may have distinct heavy-field Arc identities even at the same TomitaKey + same lex provenance. The merge_disambiguator (already in Substage 1: `(sppf_stack_id, cohort_origin, lex_alt_idx, weight_src_idx, weight_rule_idx)`) MUST be extended to include `(Arc::as_ptr(&recovery_deltas), Arc::as_ptr(&visited_dispatch), ...)` Arc-pointer identities of all 6 heavy fields. Arcs with matching disambiguator AND matching 6-Arc-pointer-identity merge weights via `⊕ = lex_min`; otherwise stay distinct arcs. Target: chain_500 LEFT-assoc RSS -70% cumulative; chain_10000 ATTEMPT in 24G.

**Substage 7** — Re-enable chain_500 + chain_10000 tests. ~10 LOC. UNCHANGED.

**Substage 8 (optional)** — DispatchResolved broadcast collapse. UNCHANGED. Skip if S7 closes chain_10000 with margin.

---

## 6. Memory falsifier per substage (UNCHANGED methodology)

Every substage from 3 onward opens a separate pgmcp memory experiment per the prior plan's methodology. The acceptance criterion is unchanged: Welch verdict accepted (treatment ≤ control + 0 SE) OR inconclusive (p≥0.05).

---

## 7. Risk register (UPDATED for Option A)

| # | Risk | Probability | Impact | Mitigation | Detection |
|---|------|-------------|--------|------------|-----------|
| R1 | TomitaKey is too coarse — silently drops derivations | LOW | CRITICAL | Option A per-arc heavy-field storage restores soundness; arc merge disambiguator includes Arc-pointer identity of all 6 heavy fields | `-3!` multi-packing test + recovery/binder test fixtures + gauntlet 4206+ on every commit |
| R2 | Welch right-assoc regression from ingest overhead | MEDIUM | HIGH | Substage 3 gates this; round-trip overhead is per-arc clone of 6 Arc handles (~48 B copy) which is cheap | Welch panel on every substage; right_assoc arms are 4 of 7 |
| R3 | Arc materialization on ObsDivergent steps is slower | MEDIUM | MEDIUM | `materialize_branch_cursor_from_arc` is 1 struct copy + 6 Arc::clone + 2 small Vec clones — O(1) | Welch panel |
| R4 | `Arc::make_mut` on per-arc `visited_dispatch` deep-clones | LOW | MEDIUM | The mutation happens at apply_action_to_cursor in the materialize-then-step path; behavior is identical to today's per-cursor mutation — no NEW deep clones introduced | Memory experiment per substage |
| R5 | TomitaFrontierMap key hashing dominates step cost | LOW | MEDIUM | FxHashMap; 5-field key is ~24 B; lookup is O(1) | Welch panel + cargo-flamegraph if regression |
| R6 | IterativeChainAbsorb classifier interferes with already_chained shortcut | MEDIUM | HIGH | Substage 5 explicit IterativeChainAbsorb arm | Welch LEFT-assoc + chain_10000 attempt at S7 |
| R7 | Generation eviction GC leaves stale frontier nodes | LOW | LOW | Eager evict in drain_current_generation | Walker-stats counter |
| R8 | Multi-snapshot revive paths fail to find cohort | LOW | CRITICAL | dispatch_cohort_cache and tomita_frontier_map are orthogonal | Gauntlet on every commit |
| R9 | merge_equivalent_cursors + Tomita ingest double-merge | LOW | MEDIUM | Separate code paths (Vec<Concrete> vs Vec<Frame>) | Per-substage gauntlet |
| **R10 (NEW)** | Per-arc heavy-field storage offsets the merge benefit | MEDIUM | MEDIUM | Per-arc cost is ~100 B (vs 52 B prior unsound plan); merge benefit is 3× → net storage is ~33 B per cursor-equivalent (vs 512 B baseline). Still 15× per-cursor reduction. | Memory experiment per substage |
| **R11 (NEW)** | Substage 6 arc disambiguator on Arc-pointer identity over-discriminates (kills the merge) | MEDIUM | HIGH | Arc-pointer-eq is necessary for soundness (two arcs with distinct heavy-field Arcs cannot merge their weights without dropping one set of heavy fields). The merge benefit at Substage 6 will be conditional on Arc-sharing rate, which is empirically measurable | Walker-stats arc_dedup_hits counter; if <10% of TomitaKey collisions also share Arc-pointer-identity, Substage 6 graduates to NO-OP and the win is purely from Substages 4-5 |

---

## 8. Rollback strategy (UPDATED)

**Per-substage revert protocol** unchanged. The Substage 1.5+2.5 commit is the soundness baseline; it must remain in tree if any of Substages 3-8 are reverted.

| Substage failed | Revert commits |
|-----------------|----------------|
| 1.5+2.5 (soundness fix) | revert the 1.5+2.5 commit. Substage 1 (`ea63fc6`) stays in tree as dead-code precedent. |
| 3 (ingest pass) | revert C3; 1.5+2.5 retained. |
| 4 (ObsInvariant fast path) | revert C4; ingest pass retained. |
| ... | as prior plan |

**Cross-revert.** If user abandons Exp 14 entirely: revert in reverse from C8 to C3 to C2.5+C1.5. Substages 0, 1, 2 (instrumentation + dead-code modules) retained as future-proof scaffolding.

---

## 9. Out-of-scope deferrals — with prior-art citations

(Existing items UNCHANGED.)

**NEW item:**

| Item | Decision | Why deferred — with experiment citation |
|------|----------|------------------------------------------|
| Original Exp 14 plan's "shell-shared heavy fields" data model | REPLACED — documented as soundness gap | The prior plan (commit `cd48071` tree) placed `recovery_deltas`, `visited_dispatch`, `visited_recovery`, `binder_scope_marks`, `optional_scope_marks`, `sppf_collection_arena` on the FrontierNode shell. This is sound only when the ingest predicate enforces `~_obs` equivalence (as H12 does at `dispatch_cohort.rs:597-604`). The Tomita 5-tuple TomitaKey does NOT enforce `~_obs` — it captures only `(state, node, pos, edge_top, collection_depth)`. Two cursors at the same TomitaKey can have different `recovery_deltas` (different recovery histories), `visited_dispatch` (different defense sets), etc. Under the prior data model, ingest would silently drop one cursor's heavy-field divergence by absorbing it into the shell. This redesign Option A moves all 6 heavy fields per-arc, restoring soundness at the cost of ~80 B per arc. See §2.4.1 for the full gap walkthrough. The shipped Substage 1 + 2 code (commits `ea63fc6`, `19f04f9`) is dead code and the soundness gap never reached production behavior; the gap is closed by the Substage 1.5+2.5 follow-up before Substage 3 ingest enables production behavior. |

---

## 10. Multi-session execution plan

Sessions of ≤ ~1 working day each. Each ends with commits pushed + pgmcp experiment records + plan-file ledger update.

### Session 1.5 (NEW — Substages 1.5 + 2.5 bundled)

- **Substages**: 1.5 + 2.5 (soundness fix; bundled into one commit).
- **Wall time**: ~7-8 h (4h LOC + 2h tests + 2h Welch + commit).
- **Git-tip pickup**: `cd48071` (current tip).
- **Ledger update**: row "Exp 14 Substage 1.5+2.5: TomitaShell + per-arc heavy fields (soundness fix)" with Welch panel + gauntlet 4206/0.
- **pgmcp record**: 1 experiment (Substage 1.5+2.5).
- **Gate to Session 2**: ACCEPT iff Welch NEUTRAL on all 7 arms + gauntlet 4206/0 + 8 new tests pass.

### Session 2 (Substage 3 — ingest pass) (was prior Session 3)

- Substage 3.
- Wall time: ~1 day.
- pgmcp: 2 experiments (Welch + memory).
- Gate: ingest round-trip is RSS-neutral within 5%; Welch NEUTRAL.

### Sessions 3-6 (Substages 4-7) (renumbered; substages otherwise unchanged)

Sessions follow the prior plan's structure for Substages 4 (ObsInvariant fast path), 5 (Push/Pop graduation), 6 (arc ⊕-aggregation with Arc-pointer disambiguator), 7 (test un-ignores).

Across-session plan-file ledger update obligation: unchanged.

---

## 11. Verification checklist (UNCHANGED methodology)

At every session boundary, run:

```bash
# 1. Gauntlet
cargo test --release -p prattail --lib 2>&1 | tail -20

# 2. Trampoline (fast)
./target/release/deps/trampoline_tests-* \
    --skip chain_10000 --skip chain_5000 --skip chain_2000 \
    2>&1 | tail -10

# 3. chain_500 LEFT-assoc
./target/release/deps/trampoline_tests-* \
    --exact test_left_assoc_chain_500 \
    --include-ignored 2>&1 | tail -10

# 4. 7-arm Welch panel (LEFT 50/100/200 + RIGHT 50/100/200/1000)
for n in 50 100 200; do
  hyperfine -N --warmup 3 --runs 15 \
    "./target/release/deps/trampoline_tests-* --exact test_left_assoc_chain_$n" \
    --export-json /tmp/welch-exp14-treatment-left-$n.json
done
for n in 50 100 200 1000; do
  hyperfine -N --warmup 3 --runs 15 \
    "./target/release/deps/trampoline_tests-* --exact test_right_assoc_chain_$n" \
    --export-json /tmp/welch-exp14-treatment-right-$n.json
done

# 5. pgmcp Welch decide
# 6. Memory experiment
# 7. Clean build
# 8. Git state
```

ACCEPT iff:
- Step 1: 4206/0 or higher per substage's test additions.
- Step 2: 18/0/6 or higher.
- Step 3: passes within ~1 minute.
- Step 4: 7 hyperfine JSONs captured, σ/μ < 2%.
- Step 5: every arm's experiment_decide is `accepted` or `inconclusive`.
- Step 6: chain_10000 fits in 24 GB or growth rate ≤ baseline.
- Step 7: clean.
- Step 8: tree clean, tip at expected commit.

REJECT at any step → revert offending substage + update ledger.

---

### Critical Files for Implementation

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/tomita_frontier.rs` (Substage 1.5 the load-bearing extension)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/cohort_lazy.rs` (Substage 2.5 signature update; H12 path untouched)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs` (Substage 3+ step_fanout restructure)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/walker_stats.rs` (Substage 3 stats)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/dispatch_cohort.rs` (UNCHANGED reference for the H12 ~_obs construction-time guarantee)
