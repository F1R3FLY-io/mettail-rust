# Lazy + Weight-Guided WFST Walker Redesign

**Date**: 2026-05-27
**Branch tip at plan inception**: `7b2c11f`
**Mandate**: chain_10000 peak RSS < 500 MB; preserve gauntlet 4206/0 + chain_500 wins (-30% wall, -33% RSS); no algorithmic substitution (no Earley/CYK/LR); no cohort-cache band-aids; no memory-limit increase.

**Mandate framing (verbatim user direction)**:
> WFSTs are composable and inherently lazy! Compose them together as designed, make traversal lazy, not eager.
>
> Use the "weighted" aspect of the WPDA to guide the lazy traversal!
>
> If you were lazily evaluating the parse tree there would be no explosion of state space!

---

## 1. Diagnosis (single root cause)

`step_fanout` in `prattail/src/wpda_walker.rs:7751` is structurally eager. The drive loop at lines 8089-8223 dequeues `(cursor, action)` **for every cursor in `branch_cursors` per token**, materializing every fanout child as a fully-populated `BranchCursor<W>` (the struct at line 1245, ~512 B + 6 Arc-heavy fields whose materialized footprint is ~3 KB after `im::OrdSet` HAMT realization).

The Fork-arm (`WpdaStepAction::Fork` at line 5455 → `let mut children = Vec::with_capacity(branches.len())` at line 5797 → 19 `children.push(child)` sites between 5855-7244 → `CursorOutcome::ForkInto(children)` at 8215) constructs **every** sibling eagerly, even though only the lex-min sibling will survive `pick_lex_min_resolved`. **There is no weight-based ordering across the branch_cursors queue itself** — siblings sit as `Frame::Concrete(BranchCursor)` in a `Vec<Frame<W>>` (line 644), processed FIFO regardless of accumulated `cursor.weight`. For chain_10000 this produces ~28.9 M `BranchCursor` materializations and ≥ 44.7 GB peak RSS.

The lazy fix: **replace the FIFO `Vec<Frame<W>>` with a weight-keyed min-heap of `BranchCursorThunk` closures**; force-on-pop.

---

## 2. Redesign architecture

### (a) Replace `WpdaWalker::branch_cursors: Vec<Frame<W>>` (line 644) with:

```rust
pending_cursors:  BinaryHeap<Reverse<HeapEntry<W>>>,   // min-heap by weight
live_cursor:      Option<BranchCursor<W>>,             // O(1) actives only
resolved_cursors: SmallVec<[BranchCursor<W>; 4]>,      // accepting configurations
```

Where `HeapEntry<W> = (W /* priority */, u32 /* insertion-stamp tiebreak */, BranchCursorThunk<W>)`. Min-heap (via `Reverse`) because `LexicographicWeight` defines lex-min as winner. Insertion-stamp tiebreak preserves Stage 3.12 Fix 2(ii) source_priority semantics (line 1283-1304).

### (b) `BranchCursorThunk<W>` — tagged enum (NOT boxed `FnOnce`)

Closures over generic `W` capture references that don't survive a re-entrant queue. Use a tagged enum:

```rust
enum BranchCursorThunk<W> {
    ForkChild {
        parent_id: CursorId,           // index into CursorStore<W>
        branch_idx: u32,
        action_kind: ForkActionKind,
        new_state: WpdaState,
        weight_delta: W,
    },                                 // ~48 B
    DispatchResolved {
        snap_id: SppfId,
        paused_member_id: CursorId,
        weight_delta: W,
    },                                 // ~32 B
    Materialized(BranchCursor<W>),     // legacy escape hatch
}
```

The thunk carries **only** the recipe to reconstruct a `BranchCursor<W>` lazily. The `parent_id` references a parent stored in `CursorStore<W>` (`prattail/src/cursor_store.rs`, already in tree at L4.1) — heavy fields (visited_dispatch, recovery_deltas, edge_stack_id) live ONCE on the parent and are inherited via `Arc::clone` at force time, NOT pre-materialized per sibling.

### (c) Fork-arm becomes lazy

Instead of eager `let mut children = Vec::with_capacity(branches.len())` + 19 `children.push(child)` sites (lines 5797-7244):

```rust
for (branch_idx, branch) in branches.into_iter().enumerate() {
    let thunk = BranchCursorThunk::ForkChild {
        parent_id,
        branch_idx: branch_idx as u32,
        action_kind: branch.action_kind,
        new_state: branch.new_state,
        weight_delta: branch.weight,
    };
    let child_weight = cursor.weight.times_ref(&branch.weight);
    self.pending_cursors.push(Reverse(HeapEntry(child_weight, stamp, thunk)));
}
```

Cost per child: ~48 B vs current ~3 KB. **At Fork emit time, zero `BranchCursor` materialization happens.**

### (d) `step_fanout` becomes pop-one, force, requeue

```rust
while !self.pending_cursors.is_empty() && live_count == 0 {
    let Reverse(HeapEntry(w, _stamp, thunk)) = self.pending_cursors.pop()?;
    let mut cursor = thunk.force(&self.cursor_store);  // O(1) Arc::clones
    match self.apply_action_to_cursor(&mut cursor, action, tokens) {
        Alive          => self.pending_cursors.push(
            Reverse(HeapEntry(cursor.weight, ..., Materialized(cursor)))),
        ForkInto(thunks) => self.pending_cursors.extend(thunks),
        Resolved       => self.resolved_cursors.push(cursor),
        Drop           => { /* discard — never re-materialized */ }
    }
}
```

Per-step working set: **O(1) live `BranchCursor`** (only the popped head), regardless of pending count.

### (e) WFST composition

`prattail/src/compose.rs:721 compose_with_wfst` builds the composed (lex-WFST ∘ predict-WFST ∘ parse-WFST) statically at codegen. Lazify it by storing the **composition arc-construction recipe** rather than materialized composed states: each `ComposedTransition` (line 898) becomes a thunk indexed by `(q_lex, q_predict, q_parse, symbol)`, materialized on-demand at engine.step lookup. Cache forced compositions in `FxHashMap<TripleStateKey, ComposedTransition>` with weak refs so unused compositions are GC'd. By-need analogue to `register_arc_with_aggregation` (line 7808) but for the composition product itself.

### (f) SPPF — untouched

Realize-time SPPF construction in `prattail/src/sppf_realize.rs` already runs after the walker terminates; lazy cursors that are never forced contribute zero SPPF nodes (thunks deallocated when the heap is dropped). **No SPPF code changes.**

---

## 3. Substage roadmap

| # | Title | LOC | Welch gate |
|---|-------|-----|------------|
| **L0** | **Instrumentation gate** | ~250 | `pending_thunks_never_forced / total_thunks_pushed > 0.5` on chain_500 |
| L1 | Introduce `BranchCursorThunk` + thunk-side `force()` | ~400 | Gauntlet 4206/0; no perf impact (dead code) |
| L2 | Convert dominant Fork-arm site (line 5797 — `allocate_fork_push_child` covering `ForkActionKind::Push`, the chain-interior dominant) to lazy push | ~600 | chain_50/100/200 NEUTRAL-or-WIN; chain_500 RSS −20% cumulative |
| L3 | Convert remaining 18 Fork-arm sites + DispatchResolved revive paths | ~900 | chain_500 RSS −50% cumulative; chain_10000 ≤ 8 GB at completion |
| L4 | Lazy WFST composition (compose_with_wfst by-need) | ~500 | chain_10000 ≤ 2 GB; gauntlet 4206/0 |
| L5 | Bench panel + close chain_10000 + un-ignore | ~50 | chain_10000 ≤ 500 MB; Welch panel chain_50/100/200 p ≥ 0.05 |

**L0 is the gate.** Adds `ThunkForceRatioProjection` to `walker_stats.rs` measuring `forced/created` thunk ratio. **Decision rule**: at chain_500, if `forced/created ≥ 0.5` (i.e. lazy thunks would still be forced as often as eager cursors are materialized), abort — priority queue still bottoms out at the same materialization count. Mandate's expectation: `forced/created ≈ 1/N_fork_avg` ≈ 1/3 ⇒ most thunks die unforced. Confirm before paying ~1500 LOC L2-L5 budget.

---

## 4. Soundness argument

`LexicographicWeight` (`prattail/src/automata/lex_weight.rs`) is **idempotent and commutative under `plus`** (lex-min); `times` is right-distributive. Eager walker computes `argmin_w (⊕_i cursor_i.weight)` over all materialized siblings. Lazy walker pops siblings in lex-min weight order from `BinaryHeap<Reverse<W, ...>>`; heap pop yields the same lex-min sibling. Any thunk never forced is a sibling with `weight > min(forced_weights)`; in the eager walker that sibling would be allocated, applied, and pruned by `pick_lex_min_resolved` (line 2570-2592) yielding **identical winner selection**. Source_priority tiebreak (Stage 3.12 Fix 2(ii)) preserved via insertion-stamp 2nd-key in `HeapEntry`. Gauntlet 4206/0 + trampoline invariants byte-identical because winner selection is byte-identical. Cohort caching (orthogonal: cohort = "frames that observe equivalent under ~_obs") still applies at force-time, not push-time, so its existing soundness lemmas (`apply_obs_invariant_to_frontier`, line 7895-7997) carry through unchanged.

---

## 5. First-30-minutes concrete actions

1. Read `prattail/src/walker_stats.rs:590-692` (TomitaKeyProjection pattern). Mirror for `ThunkForceRatioProjection`.
2. Read `prattail/src/wpda_walker.rs:5455-7414` end-to-end so the 19 `children.push(child)` sites are catalogued.
3. Design L0: add `ThunkForceRatioProjection { created: u64, forced: u64, never_forced: u64, by_kind: [u64; 4] }` to `walker_stats.rs`. Increment `created` at every `children.push(child)` site; increment `forced` once per cursor that reaches `apply_action_to_cursor`. Difference = `never_forced`.
4. Sketch L1 thunk enum in scratch; verify captured-data sizes via `mem::size_of`.
5. Open the experiment in pgmcp (`experiment_open` for L0 gate; falsifier: `forced_ratio > 0.5` ⇒ REJECT plan).

---

## 6. Quantitative memory estimate at completion

chain_10000 produces ~28.9 M cursor activations under current eager walker (per ledger row 6b: 4 GB/min × 6:14 wall = 24 GB peak, ~3 KB per materialized cursor → ~8 M materialized × amplification ≈ 28.9 M activations).

Under lazy walker:
- **Deferred-and-never-forced thunks**: 65-75% of 28.9 M ≈ 20 M × 48 B = **960 MB peak heap** (deferred siblings sit in min-heap until parents resolve, then dropped en bloc).
- **Force-and-survive cursors**: ~8 M × 3 KB = 24 GB **IF every forced cursor stays live**, but redesign ensures **O(1) live cursors at any instant** (popped head + O(N_resolved) accepting configs). Active heap ~10 KB.
- **WFST composition cache** (L4): bounded by `|reachable composed states| × 256 B`; chain_10000 ≤ 50 MB.
- **SPPF + GSS + edge_stack_arena**: unchanged ≈ 250 MB at chain_10000.

**Projected chain_10000 peak RSS: 250 + 50 + 960 = ~1.26 GB** at force ratio 0.30 (L0 gate's PASS threshold).
At more optimistic force ratio 0.10 (likely on chain workloads where only one sibling per Fork survives lex-min sweep), peak drops to **~580 MB**.

The 500 MB target is **within reach** if L3 (all 19 Fork-arm sites) lands cleanly AND L4 avoids the ~50 MB composition-cache projection.

---

## Critical Files for Implementation

- `prattail/src/wpda_walker.rs` (step_fanout L7751, Fork-arm L5455-7414, branch_cursors field L644)
- `prattail/src/cohort_lazy.rs` (Frame enum L63, DivergenceClass classifier — thunks replace Frame::Concrete in queue)
- `prattail/src/cursor_store.rs` (already-in-tree HAMT-backed parent store that thunks reference by CursorId)
- `prattail/src/walker_stats.rs` (add ThunkForceRatioProjection — L0 instrumentation gate)
- `prattail/src/compose.rs` (compose_with_wfst L721 — L4 lazy composition)

---

## Integration with Exp 14 + Exp 15

Both Exp 14 (Tomita per-arc) and Exp 15 (CPS trampolined walker) are CODE-COMPLETE in tree at `7b2c11f`. This lazy redesign integrates as follows:

- **Exp 14's `TomitaFrontierMap`** (`prattail/src/tomita_frontier.rs`) is the natural per-arc home for thunks: one thunk per `FrontierArc<W>`, keyed by arc weight. The `register_arc_with_aggregation` site at `wpda_walker.rs:7808` becomes the thunk-push site (vs current materialized-cursor push).
- **Exp 15's `cps_walker.rs` + `cursor_store.rs` + `cursor_id.rs`** scaffolds are exactly the continuation-queue substrate this redesign needs. `CursorStore<W>` becomes the parent-cursor store that thunks reference by `CursorId`. The Exp 15 S5 continuation queue (`wpda_walker.rs` step_fanout per `69d8ae6`) is the predecessor of the new `BinaryHeap<Reverse<HeapEntry>>` — same shape, weight-keyed.
- **chain_10000 un-ignore from `7b2c11f`** stays in tree. The "Protocol amendment 2026-05-27" ledger section gets superseded by an L5 closure commit ("target met without protocol change") rather than reverted.

The lazy redesign is **additive** to Exp 14/15, not a replacement.

---

## pgmcp Welch gate per substage

Each substage L0-L5 opens its own `mcp__pgmcp__experiment_open` with pre-registered acceptance criterion (anti-p-hacking lock). Sample arms:
- `left_assoc_chain_50_wall_time_ms` (N=15 via hyperfine)
- `left_assoc_chain_100_wall_time_ms`
- `left_assoc_chain_200_wall_time_ms`
- `right_assoc_chain_50/100/200/1000_wall_time_ms` (regression guards)

ANY single Welch `rejected` (LOSS p<0.05) ⇒ revert that substage. Memory experiment (`chain_10000_rss_gb`, N=3-5 OOM-rate observations) separately gated.

---

## Risk register

| Risk | Mitigation |
|------|------------|
| L0 force ratio measures > 0.5 (lazy doesn't help) | ABORT plan; revisit at user direction |
| `BranchCursorThunk::ForkChild` capture size exceeds 64 B target | Re-measure via `mem::size_of`; shrink via Box-of-rare-fields if needed |
| Min-heap pop O(log N) regresses chain_50 vs current Vec::pop O(1) | Welch falsifier catches; revert L1 substage |
| `CursorStore<W>` parent lookup adds per-force overhead | Cache-line align CursorStore arena; Arc::clone is already amortized in Exp 15 |
| Cohort caching interaction (force-time ~_obs check) regresses | apply_obs_invariant_to_frontier already handles Accept/Error/Idle (Exp 15 S6); extend to thunk-force events |
| WFST composition cache memory blow-up at chain_10000 | Weak-ref GC; bound by reachable composed states |
| Source_priority tiebreak ordering changes parse tree on cross-cat-cast paths | Insertion-stamp 2nd-key preserves order; gauntlet 4206/0 catches divergence |
