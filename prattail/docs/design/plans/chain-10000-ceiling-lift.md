# chain_10000 architectural ceiling — lift plan

**HEAD:** `64586b5` on `feature/wfst-architecture`.
**Status:** Plan agent design 2026-05-25, **pending user review**. Do not execute without approval.

## Empirical baseline (already established)

| Stage | Commit | chain_10000 result |
|-------|--------|---------------------|
| pre-Stage 3.0 (im::OrdSet) | `aa0be44` | 31 GB OOM in 64 min |
| 3.0 substrate (FxHashSet) | `1ec6921` | 16 GB OOM in 64 min |
| 3.A 11-axis diagnostic | `1205adc` | (diagnostic only) |
| 3.B PackedDispatchConfig u64 | `e3de5b0` | 24 GB OOM in similar trajectory |
| 3.C Arc-wrap CohortMember | `7ab7c77` then REVERT `64586b5` | 24 GB OOM in 1h 46min (+42min progress) — REJECTED via Welch +6.6% chain_1000 regression |
| 3.1a peek_text &str (Driver #4) | `c280238` (VERIFIED 2026-05-25) | chain_50 +2.40% NEUTRAL, chain_100 −1.68% ACCEPT, chain_200 −2.76% ACCEPT, chain_1000 +0.60% NEUTRAL (Welch's quiet bench N=15). Initial REJECT was 100% system noise from concurrent gauntlet+rustc — σ/μ at chain_1000 was 11.7% noisy vs 0.83% quiet, 14× variance inflation. Gauntlet 4058/0 prattail-lib + all 9 calculator failures pre-existing at e3de5b0. |
| 3.1b sppf_symbol_terms GC sweep | uncommitted (REJECTED 2026-05-25) | Tried 10K, 10K+doubling, 100K, 1M thresholds. All chain_1000 regressed (+14%, +10%, +2.56%, ~). **Empirical instrumentation** revealed `sppf_symbol_terms` peak scales LINEARLY at ~6N: chain_50=304, chain_100=604, chain_200=1204, chain_1000=6004. At chain_10000 peak would be ~60K entries × 80 bytes = ~5 MB, NOT the 6-10 GB Plan agent estimated. The sppf_symbol_terms map is NOT the chain_10000 consumer. Reverted. |
| 3.2 incoming_edge_stack as im::Vector | uncommitted (REJECTED 2026-05-25) | Catastrophic regression: 22 GB RSS at chain_1000 (baseline ~5 MB) within ~1 min. The persistent `im::Vector` had massive overhead vs `Vec` for this workload — likely the small `GssEdgeId` element size relative to RRB-tree node overhead. Reverted. |
| 3.3 SPPF dedup_packing rework | DEFERRED | Contingent on 3.1b+3.2 helping (both failed). High-risk SPPF arena rework for unverified benefit. |

## Empirical conclusion: chain_10000 ceiling is fundamental to current architecture

After two failed structural optimizations (3.1b sppf_symbol_terms GC, 3.2 im::Vector for incoming_edge_stack), the chain_10000 24 GB ceiling appears fundamental to the current walker architecture:

1. **sppf_symbol_terms is NOT the consumer** (empirical: linear ~6N scaling, ~5 MB at chain_10000).
2. **im::Vector is WORSE than Vec** for the cursor-fork workload (22 GB at chain_1000).
3. **Heaptrack at chain_1000 fingered BranchCursor::clone at 49% of peak heap** — per-cursor state (visited_dispatch/visited_recovery, recovery_deltas, etc.) is the dominant consumer.

The per-cursor state consists of 6 fields that are *mutated every step* (defeats Arc-CoW). The cursor count (~225 at chain_200/1000/10000) × deep per-cursor state = ~225 × O(N) state = O(N²)-ish memory.

To fundamentally fix chain_10000, options (per `2026-05-24-chain_10000-heaptrack-architectural-ceiling.md`):

1. Reduce cursor count (better merging) — VIOLATES ambiguity-preservation mandate (`feedback_never_disambiguate_early`).
2. Reduce per-cursor state — visited_dispatch/visited_recovery sets are necessary for cycle detection.
3. Lazy materialization of cohort fanout — multi-week research-level work.
4. Mark `test_left_assoc_chain_10000` as `#[ignore = "architectural ceiling"]`.

None of these are quick wins. The 24 GB chain_10000 ceiling is the architectural maximum for the current walker without a structural redesign that is out of scope for the Stage 3 merge-convergence workstream.

**Gauntlet 6169/0 preserved throughout.**

## Two parallel Explore agents identified the actual drivers

### Explore agent 1: cohort cache NOT the dominant consumer

- `DispatchCohortCache.entries`: never evicted in-parse, only at `reset()` (`wpda_walker.rs:2604`).
- `pending_cohort` capped at 4 (`dispatch_cohort.rs:424`); `worker_snapshots` capped at 4 (`:355`).
- Per-entry steady-state ≈ 1 KB; chain_10000 extrapolation ≈ 60 MB direct cache footprint.
- **NOT the 24 GB consumer**.
- Pos-based eviction UNSAFE: cross-cat-projection re-entry can hit DispatchKeys at arbitrary earlier pos.

### Explore agent 2: the four actual drivers

| Driver | Field | Location | chain_10000 estimate |
|--------|-------|----------|----------------------|
| **#1** | `sppf_symbol_terms: HashMap<SppfId, Arc<dyn Any+Send+Sync>>` | `wpda_walker.rs:599` (walker-global; F.13 H1 promotion) | **6-10 GB** (O(N²) realized Symbols × ~48 B avg) |
| **#2** | SPPF arena `dedup_packing: FxHashMap<(u32, Vec<SppfId>), SppfId>` | `sppf.rs:289-322` | **2-6 GB** at sizable collection rules (R6 collision-safety key) |
| **#3** | `incoming_edge_stack: Vec<GssEdgeId>` (NOT Arc-wrapped) | `wpda_walker.rs:1150` | ~400 MB (O(N) per cursor × ~100 cursors × ~100 Fork events) |
| **#4** | `peek_text(pos).to_string()` per Consume arm | `wpda_walker.rs:4855, 4862, 4916, 5634-5636, 6142, 6272, 6350, 6491, 6542, 6601` | 100 MB to 1 GB (15.9M Consume sites × discarded clones) |

## The Plan agent's lift plan (4 stages, ranked by impact-per-effort)

### Stage 1a — Driver #4: eliminate `peek_text().to_string()` clones

**Effort:** 3-5 h.
**Risk:** lowest — pure deletion of unconditional malloc+free.
**Expected delta @ chain_10000:** -100 MB to -1 GB.

**Root cause:** `peek_text -> Option<&str>` (`wpda_runtime.rs:903`), but every caller `.to_string()`s because three `emit_push_*` helpers take `text: String` by value. The owned `String` is then **discarded on dedup-hit** (~all hits at chain_10000, since the same token at same position dedupes).

**Change:** modify three `emit_push_*` signatures (`wpda_walker.rs:8297, 8337, 8358`) from `text: String` to `text: &str`. Replace `.to_string()` at all 10 call sites with the raw slice. `intern_terminal` (`sppf.rs:440-460`) already accepts the `&str` form internally.

**Welch's t-test prediction:** chain_50/100/200/1000 STRICT WIN (deletion of an unconditional clone). chain_10000: 100 MB to 1 GB savings.

**Falsifier (Stage A test):** if chain_1000 bench shows <1% improvement, hypothesis falsified (likely SSO already absorbed the cost).

---

### Stage 1b — Driver #1: reference-counted eviction of `sppf_symbol_terms`

**Effort:** 12-20 h.
**Risk:** medium — soundness boundary at cross-cat-projection re-realize.
**Expected delta @ chain_10000:** **-3 to -8 GB** (the biggest single win).

**Problem:** `sppf_symbol_terms` is monotone-write — `wpda_walker.rs:8998` inserts on every `emit_fire_action` success, and only `reset()` at `:2590` clears. At chain_10000 with ~60K rule firings and O(N²) interned SymbolIds, this is the dominant memory consumer.

**Why H1 promoted it from per-cursor to walker-global**: the per-cursor `Arc<Vec<(SppfId, Arc<dyn Any>)>>` was a 7.3% CPU hotspot at chain_100. The migration was a CPU win, NOT a memory win — and the new memory cost wasn't load-bearing until chain_10000.

**Are the realized terms necessary after consumption?** Two consumer paths read them:
1. `reconstruct_action_arg` (`wpda_walker.rs:8562-8576`) called by parent's `fire_action_via_transient` during the next reduce.
2. `realize_packing_call` POST-COMMIT only — does NOT use `sppf_symbol_terms`; recursively unfolds via `packings_by_symbol` directly.

**So `sppf_symbol_terms` is required ONLY for the parse-time `reconstruct_action_arg` path.** Once all parents that will fire have fired, the entry is dead.

**Fix:** add a side-table `pending_refs: FxHashMap<SppfId, u32>`. Increment on every `Arc::make_mut(&mut cursor.sppf_stack).push(symbol_id)` (line 8990). At the end of `emit_fire_action`, iterate consumed `children: Vec<SppfId>`, decrement each `pending_refs[child]`, and on zero `sppf_symbol_terms.remove(&child)`.

**Soundness gate:** cross-cat-projection that re-fires a Symbol via a different cat hits the SAME SppfId (Symbol-dedup `(nt, lo, hi)` at `sppf.rs:511`). If we evicted too early, `reconstruct_action_arg` returns `None` → cursor goes to Error.
**Mitigation:** increment `pending_refs[sid]` on EVERY push, not just first-intern. The push count tracks parent demand exactly.

**Welch's t-test prediction:** chain_50/100/200 ~flat (negligible terms in memo); chain_1000 possible 1-2% regression (hashmap remove ops); chain_10000 **GAIN of 3-8 GB**.

**Falsifier:**
- proptest gauntlet — any cursor going to Error means evicted-too-early bug.
- chain_1000 Welch's t-test — if regression > 5%, FAIL (Stage 3.C was rejected at +6.6%).

---

### Stage 2 — Driver #3: `incoming_edge_stack: Arc<im::Vector<GssEdgeId>>`

**Effort:** 6-9 h.
**Risk:** medium — `im::Vector` is O(log₃₂); per-op slightly slower for tiny N.
**Expected delta @ chain_10000:** -200 to -400 MB.

**Why H2's plain `Arc<Vec<…>>` failed:** `Arc::make_mut` on a single mutation deep-clones the entire Vec — at chain_10000 the Fork explosion triggers thousands of make_mut's per second.

**Why `im::Vector` is different:** RRB tree, branching factor 32. `push_back` is O(log₃₂ N) ≈ O(1) for N<2¹⁵. Mutation copies only the path from root to leaf (~3-5 nodes for chain_10000), orders of magnitude less than full Vec clone.

The `im` crate is already a prattail dependency.

**Change:** `incoming_edge_stack: Vec<GssEdgeId>` → `Arc<im::Vector<GssEdgeId>>` at line 1150. Update Clone (`:1472`), seed (`:1563`), fork_child (`:1632`), all push/pop/.last() callers. Mirrors the existing `sppf_stack: Arc<Vec<…>>` pattern at line 1234.

**Do NOT swap** `recovery_deltas`, `binder_scope_marks`, `optional_scope_marks` — low chain_10000 fanout per Explore agent 2's estimates; `BuilderDelta` is large enough that `im::Vector` overhead dominates.

**Welch's t-test prediction:** chain_50/100 may show 1-3% regression (RRB tree overhead > Vec for small N); chain_1000 ~flat; chain_10000 GAIN 200-400 MB and may unblock the ceiling-timeout.

**Falsifier:** identical to H2 — feature-gated branch, chain_50-1000 Welch's gauntlet. **Falsifier: > 5% chain_1000 regression.**

---

### Stage 3 — Driver #2: SPPF `dedup_packing` hash-only key + Packing GC (DEFERRED)

**Effort:** 20-30 h.
**Risk:** HIGH — collision soundness regression risk.
**Expected delta @ chain_10000:** 2-6 GB at O(N³) collection sites; ~0 for pure operator chains.

**Defer unless 1a+1b+2 don't ship chain_10000 under 24 GB.** The R6 fix that introduced full `Vec<SppfId>` keys was specifically committed as the principled collision-safe choice; reworking requires careful soundness verification.

---

## Recommended execution sequence

1. **Stage 1a** (3-5 h) — lowest risk, immediate win, validates the methodology.
2. **Stage 1b** (12-20 h) — the largest single win; ship if proptest + chain_1000 Welch pass.
3. **Stage 2** (6-9 h) — incremental win; ship if Welch passes.
4. **Stage 3** (20-30 h, OPTIONAL) — only if chain_10000 still doesn't complete after 1a+1b+2.

**Total budget (Stages 1a+1b+2):** 21-34 hours.

## Honest assessment

**Is chain_10000 fundamentally achievable?** Plan agent says: **YES, conditionally.** The walker's steady-state memory at chain_10000 is NOT inherently O(N²) for pure operator chains. `sppf_symbol_terms` retention is artificial (mostly garbage), per-cursor String clones are pure waste, and `incoming_edge_stack` deep-clones are an artifact of the Arc<Vec> shape.

**Architectural max-N for the current walker:**
- As-is: ~5000-7000 for operator chains.
- Post Stage 1a+1b+2: estimated **20,000-40,000 sustainably**.
- Beyond that: Driver #2 (Stage 3) is the next ceiling.

**The 24 GB ceiling is dominantly Driver #1 + Driver #3 — both fixable without algorithmic change.**

## Critical files

- `prattail/src/wpda_walker.rs` (BranchCursor + emit_push_* + emit_fire_action + sppf_symbol_terms manipulation)
- `prattail/src/sppf.rs` (SPPF arena + intern_terminal + dedup_packing)
- `prattail/src/wpda_runtime.rs` (peek_text signature)
- `prattail/src/dispatch_cohort.rs` (NOT touched; ruled out as dominant consumer)

## Welch's t-test gate (per `[[feedback-optimization-t-test]]`)

For each stage's behavior change:
- chain_50/100/200/1000 N=15 trials per stage.
- ACCEPT iff p<0.05 AND treatment_mean < baseline_mean OR (treatment_mean ≈ baseline_mean within 1 SE).
- chain_10000 operational gate: must reach EOI (currently OOMs at 24 GB).
- Gauntlet 6169/0 must be preserved.

## Decision point

**Pending user approval before execution.** Three questions for review:

1. Approve Stage 1a + 1b + 2 as a unit, or stage-by-stage (each gated on prior's empirical result)?
2. Defer Stage 3 (high-risk SPPF arena rework) unless explicitly needed?
3. Acceptance threshold for chain_50/100 regression: 1%? 3%? 5%? (Stage 3.C was rejected at 6.6%.)
