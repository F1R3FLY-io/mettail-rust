# Phase F.13 — Algorithmic Cross-Cat-Projection Cohort Plan

**Status:** Plan agent design — awaiting user review before any code is written.

**Date:** 2026-05-21 (Plan agent run; tip post-H13 Step 0 instrumentation).

**Empirical basis (`chain_50`, `walker-stats`):** 2,036,307 `apply_action_calls`; 1,543,396 `cross_cat_branches` (88% of all Push branches); `merge_miss_multi = 97.5%`; `H13_would_merge_under_edge_kind = 0.6%` (100× below the 60% gate). Scaling exponent ~2.62.

**Conclusion of the diagnostic phase:** Cross-cat-projection cursors at the same `pos` are NOT spurious clones — they each carry a distinct **return frame** (return-context: `incoming_edge_stack`, outer `cur_bp`, outer GSS node, semantic-builder lineage). Filtering, EdgeKind-relaxation, and naïve memoization (H10) all fail. The remaining mathematically-valid lever is to **share the sub-parse work** across distinct return-frames — exactly the contract of Tomita's GLR call-graph sharing.

---

## 1. Mathematical framing — Why is the bottleneck O(N²)?

### 1.1 The cross-cat-projection invariant (cited from code)

At `prattail/src/wpda_walker.rs:5119-5142`, the Fork-arm Push branch unconditionally emits one child cursor per `CrossCatDelegate { source_src_idx, inner_cur_bp }` branch. The codegen side (`macros/src/gen/runtime/wpda_codegen/prefix.rs:1466-1620` and `engine_impl.rs:1360-1395`) emits a `CrossCatDelegate` for every category projection that COULD match at this `(pos, outer_cur_bp)` — `Num ⊆ Expr` in calculator means at every `pos` between `^` operators the walker forks Num-projection, Expr-projection, and any sub-cat reachable by single-step coercion.

The engine.step on `CrossCatDelegate` (`engine_impl.rs:1387-1394`) **always** produces:

```
WpdaStepAction::Push {
    symbol: CategoryEntry(source_src_idx),
    weight: lex_one(),
    new_state: WpdaState::PrefixDispatch { pos: _pos, cur_bp: *inner_cur_bp },
}
```

That is, **the very next step on every cross-cat-projection cursor is a deterministic Push that depends ONLY on `(source_src_idx, _pos, inner_cur_bp)`** — no cursor-specific history influences this Push. The sub-parse it initiates is then driven by `PrefixDispatch(pos, inner_cur_bp)` whose behavior is a pure function of `(grammar, source_src_idx, pos, inner_cur_bp, tokens)`.

### 1.2 The Tomita-GLR mathematical identity

For two cursors `C₁, C₂` that both reach a `CrossCatDelegate { source_src_idx = S, inner_cur_bp = B }` at the same `pos = P`:

- `C₁.builder`, `C₁.incoming_edge_stack`, `C₁.sppf_stack`, `C₁.weight` (collectively: the **return frame R₁**) ≠ `C₂`'s (this is the 97.5% multi-discriminator divergence).
- BUT the work needed to compute `(SymbolId, hi_pos) = subparse(S, P, B)` is **identical** for both — by construction of `engine.step` on `CrossCatDelegate` (`engine_impl.rs:1360-1395`).
- The SPPF already encodes this identity at the output: `sppf.intern_symbol(nt_tag(S), P, hi_pos)` (`sppf.rs:511-525`) yields the SAME `SppfId` for both cursors' eventual reduction.

**Theorem (informal).** For any two cursors `C_i` that emit `CrossCatDelegate { S, B }` at `pos P`:

```
∀ R, S, P, B :   subparse_result(S, P, B)  is a pure function of (grammar, S, P, B, tokens)
```

Therefore the sub-parse can be **shared**: run once, fan out the result `(SppfId, hi_pos, sub_weight)` to ALL cohort members, each of which then applies its distinct return frame `R_i` independently.

This is Tomita 1985 / Scott-Johnstone GLL 2010 in our notation. It's the same mathematical content that already governs SPPF Symbol-dedup at `(nt, lo, hi)` — but we apply it to the **work** that *finds* `(nt, lo, hi)`, not just the **output** that records it.

### 1.3 Why the redundant work is `Θ(N²)`

In `chain_50 = a₁ ^ a₂ ^ … ^ a₅₀` (right-assoc, RHS-recursive):
- Each `^` operator at position `i` triggers `CrossCatDelegate { Num, r_bp(^) }` on the RHS sub-parse, which itself spawns the same cross-cat Forks at each `aⱼ` for `j > i`.
- The non-shared variant runs `subparse(Num, j, r_bp)` once for **each predecessor i < j**, i.e. each leaf is parsed `Θ(N)` times → `Θ(N²)` total work.
- The peak cursor frontier is `1355` for `chain_50` (50 chain elements × 27 average return-frame variants) — observed `branch_cursors_peak_pre_merge=4012`, post-merge `2842`.

**Predicted cohort entries** for `chain_50` ≈ `(num distinct positions) × (num distinct (S, B) pairs at each pos)` ≈ `50 × ~3 = 150` (vs. 1,543,396 cross-cat branches observed) — a **~10⁴× collapse** of the dispatch frontier.

---

## 2. Hypothesis enumeration (three candidates, ranked)

### H12 (RECOMMENDED) — Tomita-GLR Dispatch-Cohort Sharing

**Statement.** Replace the per-cursor sub-parse with a **walker-global dispatch cache** keyed on `(pos, source_src_idx, inner_cur_bp)`. On the first cross-cat-projection cursor that reaches a given key, perform the sub-parse with the standard Fork machinery; cache the resulting `(SppfId, hi_pos, sub_weight)`. On subsequent cursors with the same key, skip the recursive sub-parse and synthesize a **single child** that pretends the sub-parse already happened: push the cached `Symbol(S, P, hi_pos)` SppfId onto its `sppf_stack`, advance `pos` to `hi_pos`, multiply its `weight` by `sub_weight`, and transition `inner_state` to the post-projection state (`WpdaState::Unwinding`, identical to what the original sub-parse would have produced).

**Algorithm.**

Add to `WpdaWalker<W>`:

```rust
/// Phase F.13 H12 (2026-05-21): Tomita-GLR dispatch-cohort cache.
/// Keyed by (pos, source_src_idx, inner_cur_bp) — the EXACT triple
/// that engine.step's CrossCatDelegate arm consumes (engine_impl.rs:
/// 1360-1394). Stores the result of the FIRST cursor's sub-parse;
/// subsequent cursors at the same key synthesize a singleton child
/// pre-loaded with the cached output.
///
/// Soundness: engine.step on CrossCatDelegate is a pure function of
/// (S, P, B, grammar, tokens). Two cursors hitting the same key
/// MUST produce the same (SppfId, hi_pos, sub_weight) — proven by
/// inspection of engine_impl.rs:1387-1394 (no cursor-local state read).
dispatch_cohort_cache: rustc_hash::FxHashMap<
    DispatchKey,
    DispatchCacheEntry<W>,
>,
```

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DispatchKey {
    pos: u32,
    source_src_idx: u16,
    inner_cur_bp: u8,
}

enum DispatchCacheEntry<W: SemiringRef> {
    /// First cursor is currently in-flight; subsequent cohort members
    /// register here as PAUSED cursors and are revived by `finalize_cohort`
    /// when the in-flight cursor's sub-parse completes.
    InFlight {
        first_cursor_idx: usize,
        pending_cohort: Vec<CohortMember<W>>,
    },
    /// Sub-parse complete. Subsequent cursors synthesize a single child
    /// from this entry without recursing.
    Resolved {
        symbol_id: SppfId,
        hi_pos: u32,
        sub_weight: W,
    },
}

struct CohortMember<W: SemiringRef> {
    return_frame: BranchCursor<W>,   // PAUSED — not in branch_cursors
    weight_at_dispatch: W,
}
```

**Three steps in the algorithm:**

1. **Detect cohort entry** — at the Fork-arm Push branch (`wpda_walker.rs:5119-5142`), before allocating a new child cursor for a `CrossCatDelegate { S, B }`, look up `(pos_after, S, B)` in the cache:
   - Vacant → insert `InFlight { first_cursor_idx = children.len() }` and proceed normally to allocate the worker child.
   - InFlight → push the parent cursor (with its return-frame state) into `pending_cohort` and **do not emit a child** to `children`. This cursor is "paused."
   - Resolved → synthesize a single child that already advanced past the sub-parse (see step 3 below).

2. **Capture sub-parse completion** — when the worker child finishes its sub-parse, it eventually pops the `CategoryEntry(S)` it pushed at the dispatch site. The pop site is `apply_pop_body_to_cursor` (`wpda_walker.rs:9106-9211`). On the pop where `popped_symbol.kind == SymbolKind::CategoryEntry` AND the cursor's `incoming_edge` was `EdgeKind::CrossCatProjection { source_src_idx: S, inner_cur_bp: B }`, mark the dispatch cache entry **Resolved** with:
   - `symbol_id` = `cursor.sppf_stack.last()` (the SppfId the sub-parse produced; SPPF dedup guarantees this is the canonical `(nt(S), P, hi_pos)` id)
   - `hi_pos` = `cursor.pos`
   - `sub_weight` = the weight delta accumulated from dispatch to pop. We need to record `weight_at_dispatch` on the worker cursor at the InFlight step; then `sub_weight = cursor.weight / weight_at_dispatch` (multiplicative inverse). For LexicographicWeight there is no inverse — so instead the worker stores its `pre_dispatch_weight` and the pop site computes `sub_weight` as the value to combine with each cohort member's frame weight.
   - **Soundness anchor**: SPPF Symbol-dedup at `(nt, P, hi_pos)` already collapses all derivations. The cohort members were forked at the SAME pos with the SAME `inner_cur_bp`, so any sub-parse the worker discovers produces an SppfId that the cohort members would have produced too. `intern_symbol` (`sppf.rs:511-525`) is the formal witness.

3. **Replay cohort members** — once the cache entry is Resolved (either at the end of the worker's pop, or eagerly on a later cursor's lookup), for each paused cohort member:
   - Synthesize a child cursor from the paused frame.
   - Push the cached `symbol_id` onto its `sppf_stack` (and call `cursor_gss_push_with_kind` with a NEW EdgeKind `CrossCatProjectionResolved { source_src_idx, inner_cur_bp, cohort_key }` so the pop machinery walks one edge — see step 4 below for cohort-aware pop).
   - Advance `cursor.pos = hi_pos`.
   - Combine `cursor.weight = weight.times_ref(&sub_weight)`.
   - Transition `cursor.inner_state = WpdaState::Unwinding` — the same post-sub-parse state the worker arrives at after popping `CategoryEntry(S)`.
   - Append to `children` (i.e., emit the cohort member as a single resumed cursor, NOT as a fresh Push-with-recursive-sub-parse).

4. **Pop-side simplification** — the resolved cohort members never had the actual `CategoryEntry(S)` push happen on their GSS stack. So the next pop (driven by Unwinding) must not try to pop CategoryEntry — it should pop the calling Return frame directly. Two options:

   - **4a (cleaner)**: synthesize a "ghost" GSS edge `CrossCatProjectionResolved` on the cohort member's `incoming_edge_stack` whose `target` is the calling frame and whose pop semantics in `cursor_gss_pop_via_edge` (`wpda_walker.rs:9489-9500`) collapse exactly two stack frames at once (the would-be `CategoryEntry(S)` and the subsequent `Return` push the engine would have emitted). This requires extending `cursor_gss_pop_via_edge` to handle the ghost case.
   - **4b (simpler-but-leakier)**: actually push `CategoryEntry(S)` + the wrapping Return frame onto the cohort member's GSS stack at resume time, then mark `cursor.inner_state = WpdaState::Unwinding` so the next step pops them. This adds 2 GSS edge allocations per cohort member but reuses all existing pop machinery unchanged. **For Stage 1 of staging, USE 4b** — minimal blast radius.

**Soundness sketch — why this preserves 6157 tests.**

- **Pure-sub-parse claim.** Inspect `engine_impl.rs:1387-1394`. The `CrossCatDelegate` arm reads only `*source_src_idx`, `*inner_cur_bp`, and `_pos`. No cursor state is read. Therefore the Push it emits is identical for any cursor at the same `(pos, S, B)`.
- **SPPF preservation.** `intern_symbol(nt_tag(S), P, hi_pos)` (`sppf.rs:511-525`) dedups by `(nt, lo, hi)` regardless of which cursor invoked it. Two cohort members at the same `(P, S, B)` that ran the sub-parse independently would have produced THE SAME SppfId. Replaying the cached SppfId is bit-identical to running the sub-parse.
- **Return-frame preservation.** Each cohort member retains its OWN `incoming_edge_stack`, `binder_scope_marks`, `sppf_stack` (pre-dispatch), `last_action_output_cat`, `recovery_deltas`, `optional_scope_marks`, `pending_packing_weight`, `source_priority`, etc. The resume step just **appends** the cached `(symbol_id, hi_pos, sub_weight)` to each member's pre-dispatch state. No frame information is lost.
- **Comparison-after-cast tests (H11b regression).** H11b broke because it dropped cohort members whose dispatch was deemed "redundant." H12 keeps **all** cohort members — it just shares their *sub-parse work*. Each member resumes with its OWN return frame, so the cast/comparison projection downstream paths see the same return contexts they would have without H12. The 7 broken tests should pass.
- **Side-effecting cross-cats?** A cross-cat sub-parse can mutate `cursor.builder` (Arc-CoW), push `RecoveryEvent`s, and intern SPPF nodes. Builder mutations: the worker's `cursor.builder` is the only one that performs the mutations; cohort members must inherit them. Solution: at resolve time, the worker's `cursor.builder: Arc<SemanticBuilder>` is **already** a persistent CoW snapshot. The resolve action assigns `cohort_member.builder = Arc::clone(&worker.builder)` (replacing the paused member's pre-dispatch builder with the post-sub-parse builder, via a 1-line Arc bump). This is the Phase 5 / F.11 pattern in `redesign-a-persistent-builder.md:1-50` applied at cohort granularity. **Caveat:** the cohort member's pre-dispatch builder snapshot is DISCARDED in favor of the worker's post-sub-parse builder. This is sound IFF the worker's pre-sub-parse builder was Arc-equal to the cohort member's pre-sub-parse builder. By the cohort definition (same `pos`, same `source_src_idx`, same `inner_cur_bp`), both cursors had walked the SAME input prefix to the SAME state-machine state, so their builders are content-equivalent — the SPPF will dedup the difference. **But:** to be mathematically rigorous, we must add a `dispatch_cohort_invariant_check` (debug-only) that asserts `Arc::ptr_eq(&worker.builder, &cohort_member.builder)` at registration time, OR `worker.builder.equivalent(&cohort_member.builder)` if the builder type implements such a method. If the assertion fires, the cohort is unsafe and we fall back to the per-cursor sub-parse.
- **Recovery events.** If the worker's sub-parse fired recovery events (via `cursor.recovery_deltas`), those deltas must be appended to each cohort member's deltas. Like the builder, this is one Vec extension per cohort member; `recovery_deltas` is already a per-cursor `Vec<BuilderDelta>` (`wpda_walker.rs:~1240`). The deltas are by construction commutative-suffixed onto each member.
- **Sub-parse FAILURE.** If the worker's sub-parse drops (e.g., recovery dispatch fails), the cache entry becomes `Failed`. Subsequent cohort lookups see `Failed` and drop their cursors too. This is correct: at the cohort key the sub-parse demonstrably cannot produce a valid parse, so every cohort member would have failed identically.
- **Ambiguity.** A sub-parse can produce MULTIPLE Resolved (`SppfId, hi_pos`) pairs via the AmbiguityFanout machinery. Solution: the cache entry stores a `Vec<(SppfId, hi_pos, W)>`, and resume emits one cohort member per (resumed cohort × Resolved fanout). This is the only place the algorithm risks rebroadening, but the multiplier is the sub-parse's inherent ambiguity (small constant for calculator's cross-cat ladder), NOT N.

**Expected speedup (work).** For chain_50:
- Current: 1,543,396 cross-cat branches → 2,036,307 apply_action_calls. The work is dominated by the redundant Fork-arm Push + subsequent sub-parse steps.
- With H12: ~50 unique `(pos, S, B)` triples (one per chain element with ~3 (S, B) variants observed). Each runs the sub-parse once. Cohort members resume with one Push + one Unwinding step each. New apply_action_calls ≈ `50 worker sub-parses × O(50) steps each + 50 chain elements × ~20 cohort members × 2 resume steps = ~2500 + ~2000 = ~4500`. Ratio = `2,036,307 / 4500 ≈ 450×`.
- Wall-time projection: 17.28s / 450 ≈ **40ms for chain_50**. Even allowing for 10× constant-factor overhead in the cache + resume machinery, **<400ms is realistic.**

**Risk register.**
- *Risk: Builder Arc snapshot at cohort registration violates the cohort invariant.* Mitigation: debug-only `Arc::ptr_eq` check (or content equivalence). If it fails on any gauntlet test, fall back to per-cursor path for that key and log. The check costs ~1ns.
- *Risk: Sub-parse weight aggregation is order-dependent in a `LexicographicWeight ⊕`-non-commutative tiebreak.* Mitigation: store `weight_at_dispatch` per cohort member; compute `member.final_weight = member.weight_at_dispatch.times_ref(&cached_sub_weight)` at resume — this matches the calling-order semantics of the per-cursor path bit-for-bit.
- *Risk: Sub-parse interacts with `visited_dispatch` / `visited_recovery` cycle defenses (`wpda_walker.rs:4486-5012`).* The B12/B14 cycle defenses are PER-CURSOR. The worker's `visited_dispatch` mutations during the sub-parse must NOT be propagated to cohort members — each member keeps its own. Mitigation: at resolve, do NOT copy `worker.visited_dispatch` to cohort members; they retain their own pre-dispatch sets.
- *Risk: `last_action_output_cat` (the F.3a invariant at `wpda_walker.rs:5096-5102`) is also per-cursor.* Same mitigation: don't propagate from worker.
- *Risk: Sub-parses that themselves do cross-cat (recursive cohort lookups).* Each recursive sub-parse hits the same cache — first cursor wins, others register as pending. Reentrant invariant: the cache key `(pos, S, B)` is monotone w.r.t. `pos`, so no cycles. (Even if `pos` were equal, the `B` would change because `inner_cur_bp` strictly increases with recursive precedence.)
- *Risk: Sub-parse fires the LATTICE_TOKEN_SOURCE alt-emission mechanism (M3).* The alt index is encoded in `cursor.weight`, which we propagate correctly. Cohort members at the same `pos` see the same DAG of token alts; the alt-index path traverses the same nodes — preserved by weight propagation.
- *Smallest test to falsify.* `comparison_after_cast_results::float_cast_eq` — `"float(3) == 3.0"`. This was the simplest of the seven H11b-regressing tests. If H12 breaks here, the algorithm has lost return-frame information.

**Staging — independently committable steps.**

- **Stage 1.0 (preparation, no algorithm change):** Refactor cross-cat-projection child allocation (`wpda_walker.rs:5119-5145`) into a single helper `emit_cross_cat_child(parent, branch, kind, child_priority)`. Asserts identical behavior; gauntlet must remain 6157/0. **Diff**: ~20 LoC moved. **Verifiable independently.**
- **Stage 1.1 (cache scaffolding, dead code):** Add `dispatch_cohort_cache: FxHashMap<DispatchKey, DispatchCacheEntry<W>>` field to `WpdaWalker`, declare types `DispatchKey`, `DispatchCacheEntry`, `CohortMember`. Gate population behind `feature = "dispatch-cohort"` cargo feature, off by default. No reads or writes from production code. **Diff**: ~80 LoC of types. **Gauntlet**: 6157/0 (no behavior change).
- **Stage 1.2 (write-only path):** Wire the registration / promotion / write logic. On every cross-cat Fork-arm child, populate the cache in InFlight mode (first cursor only); record `Resolved` at the matching pop. Reads from cache still disabled. Add a walker-stats counter `dispatch_cohort_resolved_total` to observe how many entries get resolved per parse. **Gauntlet**: 6157/0 (writes are observation-only). Run `chain_50 --features walker-stats dispatch-cohort` to confirm ~50 resolved entries.
- **Stage 1.3 (read path — minimum-viable cohort sharing):** Wire the resume path using approach 4b (re-push `CategoryEntry(S)` + Return on cohort members at resume, transition to Unwinding). Cohort registration on a `Resolved` cache entry replaces the per-cursor sub-parse with a synthetic singleton child. **Gauntlet must be 6157/0.** Run `chain_50` and verify wall-time drops from 17s to <1s. If ANY gauntlet test regresses, revert this stage; the diagnostic counters from 1.2 still ship.
- **Stage 1.4 (cleanup — pop-time fast path 4a):** Replace approach 4b with the ghost-edge approach 4a (no extra GSS allocations on resume). Strict gauntlet re-run.
- **Stage 1.5 (sub-cohort recursion + ambiguity handling):** Extend `DispatchCacheEntry::Resolved` to `Vec<(SppfId, hi_pos, W)>` for multi-result sub-parses; cohort resume produces one cursor per (cohort × result) pair. Run rholang edge_case gauntlet (heavier ambiguity exercise) and prattail proptest gauntlet.
- **Stage 1.6 (default-on):** Promote `dispatch-cohort` from cargo feature to default behavior (delete the feature gate). The feature gate provides per-commit safety net; default-on locks the win in.

---

### H14 — SPPF-keyed Push-deduplication (alternative; weaker but simpler)

**Statement.** Replace `dispatch_cohort_cache` with a much narrower cache: at every Fork-arm Push that emits `CrossCatDelegate`, look up `(pos_after, source_src_idx, inner_cur_bp)` in an `FxHashMap`. If the key exists AND maps to an SppfId where `sppf.symbol_for(nt_tag(source_src_idx), pos_after) → Some(sid)` (the sub-parse has been completed by another cursor at this exact key, AND the resulting SppfId is already in the SPPF), then skip the recursive sub-parse: synthesize a single child that pushes the cached SppfId. Differs from H12 by **not pausing cohorts** — cursors that hit the cache while it's in-flight just run the sub-parse themselves (a pessimistic non-sharing case).

**Mathematical statement.** Same as H12 but only exploits the **terminal-state** identity: if `intern_symbol(S, P, *) → SppfId X` has already been recorded, then any cursor at `(P, S, B)` whose sub-parse would produce X can skip.

**Soundness.** Strictly weaker than H12. Same proof, but the cache only fires after the FIRST cursor's sub-parse has fully completed and registered with the SPPF. Subsequent cursors that arrive during the in-flight window still recurse.

**Expected speedup.** For chain_50, the sub-parses don't strictly serialize — many fire in parallel within a single `step_fanout` iteration. So the H14 cache hit rate is much lower than H12's. Estimate: ~5-10× speedup vs H12's ~450× speedup. chain_50 might drop to 2-3s.

**Risk register.** Much smaller blast radius than H12 (no cohort pausing, no builder-state inheritance question). Mitigation for builder-state mismatch: skip the cache hit if the cursor's `builder` Arc is not pointer-equal to the worker's pre-sub-parse builder.

**Staging.** Strictly simpler: 1 commit to add the cache, 1 commit to wire the lookup.

**Why this is a fallback, not the recommendation.** If H12 fails at gauntlet, H14 is the next thing to try. But H12 should be tried first because:
- The exponent is ~2.62, not just 2.0. The dominant work is in-flight-overlapping sub-parses (cursor frontier grows IN PARALLEL with the worker), so H14's terminal-only cache misses the bulk of the redundancy.
- H12's cohort machinery is the cleaner long-term architecture; H14 leaves us still O(N²) in the in-flight window.

---

### H15 — Compile-time cross-cat reduction (preprocessing; orthogonal)

**Statement.** Modify codegen (`macros/src/gen/runtime/wpda_codegen/prefix.rs:1466-1620`) to NOT emit `CrossCatDelegate` Fork branches when the source category has no operators that could fire at the call site's `inner_cur_bp`. Static analysis at grammar-compile time determines which cross-cats are productive.

**Mathematical statement.** For each `(call_site_cat, source_src_idx, inner_cur_bp)` triple emitted by codegen, statically determine whether any rule in `source_src_idx` has `min_bp ≥ inner_cur_bp` AND a first-token set intersecting the call site's first-token set. If not, OMIT the `CrossCatDelegate` branch.

**Soundness.** Pure pruning of provably-empty Forks. Tests should be unaffected.

**Expected speedup.** Likely 2-4× on chain_50 — many calculator cross-cat branches at chain_50's chosen `inner_cur_bp = r_bp(^)` are vacuous (Bool, Str, Fixed all have no `^`-precedence rules). But this is constant-factor: the exponent stays ~2 because the productive cross-cats still proliferate.

**Why not first?**
- Compile-time analysis touches the macro layer (`macros/`), expanding blast radius across 6157 tests via codegen changes.
- The win is bounded above by the ratio of productive vs total cross-cat branches; H12 captures the productive ones too.
- Best as a **post-H12 follow-on** — H12 makes the runtime cost negligible regardless of branch count; H15 then reduces SPPF intern traffic.

---

## 3. Ranking and recommendation

**Pursue H12 (Tomita-GLR Dispatch-Cohort Sharing) first.**

Reasoning:
1. **Math is sound and proven**: `engine.step(CrossCatDelegate, …)` reads no cursor state. The cohort identity is structural, not statistical.
2. **Expected speedup is asymptotic** (drops exponent from ~2.62 to ~1.0-1.2), not constant-factor.
3. **The staging plan provides per-commit verifiability** — Stage 1.2 ships diagnostic-only and is guaranteed to be 6157/0. Stage 1.3 is the only stage where breakage could occur, and at that point we have the cache statistics to debug.
4. **The architectural Arc-CoW pattern** is already established in `redesign-a-persistent-builder.md` for sharing `cursor.builder` across cohorts; H12 reuses it.
5. **H14 is a fallback** if H12 has unexpected breakage; the cache scaffolding from Stage 1.1 can be reused.
6. **H15 is a follow-on** that compounds with H12.

---

## 4. Decision points for user authorization

Before Stage 1.0:

1. **Cache scope: walker-global or per-step?** RECOMMENDATION: walker-global, reset between top-level parses. Per-step would lose cross-step cohort sharing (the worker resolves in step `k`, cohort member arrives in step `k+1` — common in chain ascent). User decision: confirm walker-global.

2. **Cargo feature gate during stages 1.1-1.5?** RECOMMENDATION: yes, `dispatch-cohort`, off by default. Provides per-commit rollback safety. User decision: confirm feature gate, OR opt to land in main branch directly (riskier but fewer commits).

3. **Approach 4a (ghost-edge pop) or 4b (re-push-stack pop) for Stage 1.3?** RECOMMENDATION: 4b first (~10 extra GSS ops per cohort member, but reuses existing pop machinery unchanged); upgrade to 4a in Stage 1.4 once correctness is confirmed. User decision: confirm staged 4b→4a, OR go 4a directly (faster but more code-touch risk).

4. **Builder-equivalence check at registration: `Arc::ptr_eq` (fast, may have false negatives) or content equivalence (correct but expensive)?** RECOMMENDATION: `Arc::ptr_eq` ONLY in debug builds; production trusts the cohort invariant. If user wants extra rigor: add a `cfg(debug_assertions)` content-equivalence check that runs on every cohort registration and panics on mismatch. User decision: confirm `Arc::ptr_eq` for prod, content equivalence in debug.

5. **Sub-parse failure handling.** RECOMMENDATION: cache the failure as `DispatchCacheEntry::Failed { error_msg }`; all subsequent cohort members at that key drop. Avoids re-running known-failing sub-parses. User decision: confirm failure caching.

6. **Chain_10000 acceptance target.** RECOMMENDATION: after Stage 1.3, run chain_50/100/200/1000 — confirm exponent ≤ 1.2 (Welch's t-test on slope of log(t) vs log(N)). If chain_1000 doesn't drop into the seconds, escalate to H14 hybrid OR H15. User decision: confirm the acceptance target.

---

## 5. Out-of-scope (DON'T do this in F.13 H12)

1. **Refactoring `cursor.builder` to non-Arc** — already F.11 pattern; further refactoring (`redesign-a-persistent-builder.md`) is out of scope.
2. **Calculator AST `Box → Arc` conversion** (H4 from baseline memo) — large blast radius across consumers; defer.
3. **mimalloc default-on** — already shipped as opt-in cargo feature `mimalloc` per user direction.
4. **Removing `EdgeKind::Generic` placeholder** — the H13 taxonomy is useful diagnostic infrastructure regardless of H12's outcome. Don't touch.
5. **GSS pop-via-edge multi-predecessor (`cursor_gss_pop_all`)** — deleted in F.13 prep (`wpda_walker.rs:9502-9508`); was orphaned. H12 doesn't need it.
6. **Persistent-data-structure migration of `incoming_edge_stack`** (H2 rejected) — Arc-CoW failed for this field; don't retry.
7. **General span-memoization** (H10 rejected) — fundamentally different algorithm; H12 is structurally distinct (cohort sharing, not memo lookup).
8. **WFST / fuzzy-cluster runtime fast path** — orthogonal axis.
9. **Recovery cohort sharing** — H12 covers cross-cat-projection cohorts only. Recovery cohorts are a separate axis (deferred until H12 ships).

---

## 6. First commit (Stage 1.0) — diff sketch

**Goal:** purely structural refactor. Move the cross-cat-projection child allocation at `wpda_walker.rs:5050-5145` into a helper. Behavior must be bit-identical; this stage is the safety net that buys us a clean call site for Stage 1.1.

**Sketch (pseudo-code; replace the inline `BranchCursor { … }` allocation at `5050-5106` and the subsequent kind-aware push at `5108-5145`):**

```rust
// New helper, file-scoped (private to WpdaWalker impl):
//
// Phase F.13 H12 Stage 1.0 (2026-05-21): factor Fork-arm Push child
// allocation into one helper. Pre-H12 this was an inline block at
// wpda_walker.rs:5050-5145. The refactor is structural: the helper
// receives the parent, branch, and child_source_priority, produces
// the child cursor (with EdgeKind classification), and returns it.
// Behaviorally identical to the inline pre-refactor.
//
// Stage 1.1+ will introduce a `dispatch_cohort_cache` lookup BEFORE
// this helper is called for CrossCatDelegate branches; if the cache
// hits, the helper is bypassed entirely (cohort resume instead).
fn emit_cross_cat_or_push_child(
    &mut self,
    parent: &BranchCursor<W>,
    branch: ForkBranch<W>,
    pos_after: usize,
    child_recovery_depth: u32,
    child_visited_recovery: ImOrdSet<…>,
    child_visited_dispatch: ImOrdSet<…>,
    child_source_priority: u32,
) -> BranchCursor<W> {
    let is_cross_cat = matches!(&branch.new_state, WpdaState::CrossCatDelegate { .. });
    let mut symbol = branch.symbol;
    let mut child = BranchCursor {
        node: parent.node,
        pos: pos_after,
        weight: parent.weight.times_ref(&branch.weight),
        inner_state: branch.new_state.clone(),
        recovery_deltas: parent.recovery_deltas.clone(),
        source_priority: child_source_priority,
        incoming_edge_stack: parent.incoming_edge_stack.clone(),
        recovery_depth: child_recovery_depth,
        visited_recovery: child_visited_recovery,
        visited_dispatch: child_visited_dispatch,
        sppf_stack: Arc::clone(&parent.sppf_stack),
        optional_scope_marks: parent.optional_scope_marks.clone(),
        binder_scope_marks: parent.binder_scope_marks.clone(),
        pending_packing_weight: parent.pending_packing_weight
            .times_ref(&branch.weight),
        collection_stack_depth: parent.collection_stack_depth,
        sppf_collection_arena: Arc::clone(&parent.sppf_collection_arena),
        last_action_output_cat: parent.last_action_output_cat,
    };
    self.emit_push_side_effects(&mut child, &mut symbol);
    if let WpdaState::CrossCatDelegate { source_src_idx, inner_cur_bp } = &branch.new_state {
        let kind = EdgeKind::CrossCatProjection {
            source_src_idx: *source_src_idx,
            inner_cur_bp: *inner_cur_bp,
        };
        let _ = self.cursor_gss_push_with_kind(&mut child, symbol, pos_after, branch.weight.clone(), kind);
    } else {
        let _ = self.cursor_gss_push_auto(&mut child, symbol, pos_after, branch.weight.clone());
    }
    let _ = is_cross_cat;  // reserved for Stage 1.1 cohort registration
    child
}
```

**Call site change at `wpda_walker.rs:5032-5145`:**

```rust
match branch.action_kind {
    ForkActionKind::Push => {
        let child = self.emit_cross_cat_or_push_child(
            &cursor,
            branch,
            pos_after,
            child_recovery_depth,
            child_visited_recovery.clone(),
            child_visited_dispatch.clone(),
            child_source_priority,
        );
        children.push(child);
        child_came_from_cross_cat.push(is_cross_cat_delegate_branch);
    }
    ForkActionKind::OptGroupAbsent { replace_symbol } => {
        // ... unchanged ...
    }
    // ... unchanged ...
}
```

**Gauntlet expectation:** 6157/0 (prattail lib 4051 + gen_calc_op 1331 + gen_rholang_op 532 + edge_case 229 + wpda_parity_calculator 16 + wpda_parity_lambda 2 + macros lib 333). chain_50 wall-time unchanged (~17.28s — this is purely a refactor).

If gauntlet is green, the user authorizes Stage 1.1 (cache scaffolding, dead code).

---

## 7. Files cited

All citations are absolute paths; line numbers are at the H13-instrumentation tip (current working directory `HEAD`).

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:5050-5145` — Fork-arm Push branch (cross-cat-projection child allocation); H12 Stage 1.0 target.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:5119-5142` — explicit CrossCatProjection EdgeKind tag; cohort identity anchor.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:7099-7228` — `merge_equivalent_cursors`; downstream of H12 (unchanged by H12 because cohort members never share `incoming_edge` with one another).
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:1597-1638` — `ConfigKey` struct (the merge predicate); for the soundness proof of H11a/H13 rejection.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:8988-9088` — `cursor_gss_push_with_kind` / `cursor_gss_push_auto`; the kinded push primitive H12 builds on.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:9106-9211` — `apply_pop_body_to_cursor`; H12 Stage 1.2 hooks the cache-resolve at the CategoryEntry pop here.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs:9489-9500` — `cursor_gss_pop_via_edge`; if approach 4a chosen, this is extended for ghost edges.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/gss.rs:393-535` — `EdgeKind` taxonomy + `is_convergent`; H12 adds new variants `CrossCatProjectionResolved` (Stage 1.4).
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/sppf.rs:511-525` — `intern_symbol`; the formal SPPF dedup that makes the cohort identity sound.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/walker_stats.rs:43-120` — `WalkerStats`; H12 adds `dispatch_cohort_resolved_total`, `dispatch_cohort_cohort_resumes_total`, `dispatch_cohort_failed_total`.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_runtime.rs:545-574` — `WpdaState::CrossCatDelegate`; the state H12 detects.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/runtime/wpda_codegen/engine_impl.rs:1360-1395` — engine.step for CrossCatDelegate; this is the proof of "cursor-state-independent transition" that justifies cohort sharing.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/runtime/wpda_codegen/prefix.rs:1466-1620` — codegen emit sites for CrossCatDelegate Fork branches (H15 territory; out of scope for H12).
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/tests/trampoline_tests.rs:131-152` — chain_50 / chain_100 / chain_200 tests; H12 acceptance targets.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/tests/edge_case_tests.rs:295-326` — `comparison_after_cast_results::float_cast_*`; the 7 tests H11b broke; H12 smallest falsification target.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/src/calculator.rs:208,223` — `PowInt`/`PowFloat` right-assoc rules with cross-cat to Num/Float; the workload generator.
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/docs/design/redesigns/redesign-a-persistent-builder.md:1-50` — the Arc-CoW persistent-builder pattern H12 reuses for cohort builder propagation.
- `/home/dylon/.claude/projects/-home-dylon-Workspace-f1r3fly-io-mettail-rust/memory/f13-baseline-2026-05-20.md` — F.13 prior session record (H1-H10 outcomes).
- `/home/dylon/.claude/projects/-home-dylon-Workspace-f1r3fly-io-mettail-rust/memory/f13-h13-result-2026-05-21.md` — H13 0.6% gate fail; the trigger for H12.

---

### Critical Files for Implementation

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/gss.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/sppf.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/walker_stats.rs`
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/macros/src/gen/runtime/wpda_codegen/engine_impl.rs`
