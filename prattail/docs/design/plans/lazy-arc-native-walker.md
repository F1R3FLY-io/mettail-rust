# Lazy Tomita Frontier Walker — Arc-Native Cohort-Sharing Redesign

**Date**: 2026-05-27
**Branch tip**: `7b2c11f`
**Supersedes**: `lazy-weight-guided-walker.md` (L0 gate FAILED at chain_50 ratio 0.799; weight-priority structurally insufficient for chain workloads)
**Mandate**: chain_10000 peak RSS < 500 MB; preserve gauntlet 4206/0 + chain_500 wins.

---

## 1. Diagnosis (L0 failure mode → new direction)

The prior lazy-weight-guided plan FAILED its L0 instrumentation gate on chain_50:
```
created = 1,339,196  forced = 1,070,530  ratio = 0.799  (need < 0.5)
projected_memory_savings_multiplier = 1.24x
```

**Why**: chain workloads have weight-tied siblings (`1+1+1+...` is unambiguous; all cohort members at an InfixLoop step carry identical `LexicographicWeight`). The min-heap can't differentiate; it pops every sibling sequentially.

**The actual structural waste** is at `wpda_walker.rs:7929-8074` — the Tomita drain materializes each arc back into a full `BranchCursor<W>` (~3 KB effective with Arc-held heavy fields) and runs `apply_action_to_cursor` per arc whenever the action classifies as `ObsDivergentOverArcs`. At chain_500: ~28.9M arc-emissions collapse via merge to ~9.6M, but still ~1.02M BranchCursor materializations.

**Substage 5** (InfixContinuation Push fast-path) is the only narrowly-graduated `ObsInvariantOverArcs` exit. EVERY OTHER action class still pays per-arc materialization.

**The single lazy mechanism that delivers 100×+**: eliminate the per-arc round-trip itself. **Operate directly on `(Arc<TomitaShell>, FrontierArc)` pairs end-to-end** — never materialize `BranchCursor` between steps. Arc count at chain_500 ~1.02M cumulative × ~100 B/arc = **102 MB**, vs current ~3 KB per BranchCursor × 1.02M = ~3 GB. **~30× per-cursor reduction**, directly addressing the gap.

---

## 2. Redesign: arc-native walker, shell-broadcast for ALL action classes

**Data structure change** — replace `branch_cursors: Vec<Frame<W>>` (line 644) with `frontier: TomitaFrontierMap<W>` as the **primary** representation, not a transient ingest/drain pass. The walker becomes "arc-native": steady-state cursor work happens on `(Arc<TomitaShell>, FrontierArc)` pairs; `BranchCursor` materialization happens ONLY at:
- the seed boundary
- terminal `Accept` / `Resolved` for SPPF realize
- the rare `ObsDivergentOverArcs` fallback (must become exceptional, not common)

### `step_fanout_v2` concrete shape

1. For each frontier node: call `engine.step(&shell.inner_state, gss, ..., shell.pos, tokens)` ONCE (already done at Substage 4, keep).
2. Classify the action with `classify_for_tomita_arc(action, edge_kind)`. **Extend the classifier** so the following become `ObsInvariantOverArcs` when their effect is shell-broadcastable:
   - **`Pop` with single-predecessor convergent EdgeKind**: shell-pop, per-arc weight ×= pop_weight, per-arc cursor_resolution_check.
   - **`Consume` / `ConsumeAndPush` / `ConsumeAndReplace` / `Replace`**: shell-mutate (pos + state + GSS push/replace once), per-arc weight broadcast.
   - **`AdvanceWithEffect` with non-recovery effects**: shell-apply effect once, per-arc cursor_resolution_check. Recovery effects stay per-arc fallback.
   - **`OptGroupAbsent`**: shell-mutate GSS pop+push, per-arc append `BuilderDelta::PushOptionalAbsent` (already per-arc via `recovery_deltas`).
3. Residual genuine divergence (Fork, ParsePredicate, AdvanceWithEffect-recovery, IterativeChainAbsorb, OptGroupFinalize): per-arc materialize fallback. L0 instrumentation shows these are **≤ 5% of step volume** at chain workloads.
4. `cursor_resolution_check` continues per-arc; cheap (no allocation), routes `CursorOutcome` enum directly into next frontier.

### Fork-arm becomes arc-emit, not cursor-emit

At the 21 `children.push(child)` sites in the Fork arm (`wpda_walker.rs:5455-7390`), emit `FrontierArc<W>` directly into `next_frontier: TomitaFrontierMap<W>` keyed by the post-arm `TomitaKey`. 6 Arc::clone (~100 B) replace the ~3 KB BranchCursor allocation. Sibling arcs landing on the same `(new_state, node, pos, edge_top, depth)` **merge immediately via `register_arc_with_aggregation`** — that's the lazy WFST composition: the post-Fork frontier is the lazy composition of the WPDA's transition fan-out with the Tomita-merge equivalence relation.

### What's "lazy" here

Thunks are NOT the lazy unit; **arcs are**. A `FrontierArc` is the recipe to reconstruct a `BranchCursor` on demand. It materializes only if:
1. Action classifies as residual `ObsDivergentOverArcs`
2. SPPF-realize boundary
3. Termination as `Resolved`

The "weight-guided" mandate is honored by `⊕`-aggregation in `register_arc_with_aggregation` — weight-tied arcs collapse via `LexicographicWeight::plus` (lex-min idempotent). The heap-of-thunks is replaced by **lex-min absorption directly in the merge map**.

---

## 3. Substage roadmap

| # | Title | LOC | Empirical Gate |
|---|-------|-----|----------------|
| **L2** | Graduate `Pop` for single-predecessor convergent EdgeKinds | ~400 | chain_500 LEFT `apply_action_calls` drops ≥ 35% (1.07M → ≤ 700k) |
| **L3** | Graduate `Consume` / `ConsumeAndPush` / `ConsumeAndReplace` / `Replace` | ~500 | chain_500 LEFT peak RSS ≤ 9 GB (currently 14.2 GB; -35%) |
| **L4** | Promote `TomitaFrontierMap` to PRIMARY; delete `branch_cursors: Vec<Frame>`; convert 21 Fork-arm sites to arc-emit | ~800 | chain_500 LEFT peak RSS ≤ 5 GB; gauntlet 4206/0 |
| **L5** | Eliminate `apply_action_to_cursor` for OptGroupAbsent + non-recovery AdvanceWithEffect | ~600 | `apply_action_calls / arc_count` ≤ 0.10 (≤ 10% residual per-arc) |
| **L6** | chain_10000 close: tune frontier capacity + `evict_stale` | ~400 | **chain_10000 LEFT peak RSS < 500 MB**; chain_500 wins preserved; gauntlet 4206/0 |

Total: ~2700 LOC, ~7 days. Every substage falsifiable BEFORE shipping.

### L2 Falsifier

If `apply_action_calls` reduction < 20%, the Pop arm classification missed the chain-interior dominator. Re-measure via new `pop_kind_histogram` walker stat; re-classify.

### L3 Falsifier

If RSS reduction < 20%, the broadcast helpers leak per-arc allocations. Instrument `frontier_arc_allocations_per_step`; force gate before shipping.

### L4 Falsifier

If any scripted Fork test breaks, the arc-emit path missed a per-cursor side effect. Instrument `fork_arm_arc_emissions_by_action_kind`; patch missing side effect.

### L5 Falsifier

If ratio > 0.20, residual divergent actions taking slow path. Break the histogram by action kind; graduate next dominant kind.

### L6 Falsifier

If peak ≥ 800 MB, arc count grows superlinearly. Re-instrument `arcs_per_frontier_histogram`; confirm Tomita merge factor; tune `merge_disambiguator` predicate.

---

## 4. Soundness

**Gauntlet 4206/0 preservation**: each substage's shell-broadcast helper is a structural refactor of an existing per-arc path. The per-arc path REMAINS as the fallback when classifier rejects — tests exercising residual ObsDivergent actions traverse unchanged. Each substage commits ONLY when gauntlet stays 4206/0.

**Soundness boundary**: `TomitaShell` carries only TomitaKey-invariant axes (Substage 1.5+2.5 spec). `FrontierArc` carries the 6 heavy fields per-arc (already shipped). `register_arc_with_aggregation` requires `Arc::ptr_eq` on all heavy fields before merging — distinct heavy-field provenance keeps arcs distinct. Shell-broadcast Pop is sound because all arcs at the same TomitaKey share `incoming_edge_stack_id` (a TomitaKey axis).

**chain_500 wins preserved**: Substage 5 InfixContinuation broadcast already shipped; this redesign EXTENDS the broadcast surface, never narrows it.

---

## 5. Memory estimate at completion

- Per-arc: ~100 B (Substage 1.5+2.5 measured).
- Shell: 1 per TomitaKey, ~48 B (Arc-shared, ~8 B refcount per arc holder).
- Per-step peak working set at chain_10000: ~5000 active arcs × 100 B = **500 KB per step**.
- Cumulative arc allocations across the parse: ~20M (chain_10000 × 2k arcs/step avg); freed at end-of-step `evict_stale`.
- Live peak bounded by `frontier_arc_peak_count`.

**Projected chain_10000 peak RSS: 200-400 MB** (working set + GSS + SPPF arena, all linear in chain length under arc-native walker).

`force_ratio` becomes meaningless under the redesign — every arc IS a "thunk" that materializes lazily only at SPPF-realize boundaries.

---

## 6. First-30-minutes concrete actions

1. Read `prattail/src/cohort_lazy.rs:600-800` (`apply_obs_invariant_to_frontier` impl — L2 template).
2. Read `prattail/src/wpda_walker.rs:5228-5260` (Pop arm of `apply_action_to_cursor` — source code for L2 broadcast helper).
3. Read `prattail/src/wpda_walker.rs:7949-8052` (existing Substage 5 Push shell-broadcast — exact template for L2 Pop, L3 Consume).
4. Add `pop_kind_histogram: [u64; N]` walker stat in `walker_stats.rs` to confirm Pop EdgeKind dominator BEFORE implementing L2 — fail fast if InfixContinuation isn't the dominator.

---

## 7. Risk register

**L2 risk**: `apply_pop_body_to_cursor` (line 5243) writes per-cursor SPPF state via `cursor_resolution_check`'s downstream calls. If any side effect is per-arc-distinct (not shell-shareable), broadcast is unsound. **Falsifier**: gauntlet 4206/0 + post-L2 `arc_resolution_outcomes_per_step` confirming identical outcomes across arcs at the same shell.

**L3 risk**: `Replace` and `ConsumeAndPush` emit GSS pushes; if the symbol depends on per-arc state (e.g., `cursor.cohort_origin`), shell-broadcast collapses cohort distinctions. **Falsifier**: post-L3 scripted Fork tests at `wpda_walker.rs:13316` exercise Fork siblings explicitly.

**L4 risk**: deleting `branch_cursors` is large structural surgery; 200+ downstream sites read `self.branch_cursors`. Each needs migration. **Falsifier**: compile errors during rewrite — bounded by type system.

**L5 risk**: recovery effects need per-arc journal append. If two arcs share a `recovery_deltas` Arc, `Arc::make_mut` triggers deep-clone — restoring per-cursor cost. **Falsifier**: `recovery_arc_make_mut_count` stat — should be ≤ arc count, not ≤ arc²; ship only when bounded.

**L6 risk**: `TomitaFrontierMap` hash collisions at scale inflate FxHashMap probe length. **Falsifier**: heaptrack at chain_10000 showing FxHashMap bucket array < 5% of peak heap.

---

## 8. Integration with prior work

- **L0 instrumentation** (just shipped) is preserved as a residual-divergence diagnostic. Re-purpose to measure `apply_action_calls / arc_count` (the L5 gate).
- **L1 `BranchCursorThunk` module** stays in tree as dead code. It's the fallback substrate if the arc-native approach hits an unsolvable soundness obstruction. The Materialized variant is rare under the new design.
- **Exp 14 Tomita per-arc shipped** — the new plan EXTENDS its substrate by promoting `TomitaFrontierMap` from transient to primary.
- **Exp 15 CPS scaffold shipped** — `CursorStore<W>` becomes useful at L4/L5 if we need O(1) lookup of arc → minimal-state mapping.
- **chain_10000 un-ignore from `7b2c11f`** stays in tree; the "Protocol amendment 2026-05-27" ledger section gets superseded by L6 closure ("target met without protocol change").
