# chain_10000 Experiments — Scientific Ledger

**Goal**: close the `test_left_assoc_chain_10000` 24 GB OOM ceiling via the candidate architectural changes documented in:
- `prattail/docs/design/plans/operator-precedence-iterative.md` (Plan A)
- `prattail/docs/design/plans/cursor-id-keyed-walker-global.md` (Plan B)
- `prattail/docs/design/plans/allocation-pooling.md` (Plan C)
- `prattail/docs/design/plans/chain-10000-alternative-approaches.md` (Plan D / E3)

**Acceptance gate per experiment**:
1. Compilation success.
2. prattail-lib gauntlet 4066/0 preserved (no test regressions).
3. trampoline 15/0/2 ignored preserved (or chain_10000 closes — improvement).
4. **Welch's two-sample t-test (unequal variance), p < 0.05**, comparing N=15 quiet runs of treatment vs baseline.
   - **ACCEPT**: p < 0.05 AND treatment_mean ≤ baseline_mean + 1 SE (NEUTRAL or WIN).
   - **REJECT**: p < 0.05 AND treatment_mean > baseline_mean + 1 SE (LOSS) → revert experiment.
   - **INDETERMINATE**: p ≥ 0.05 → record as inconclusive; treat as NEUTRAL but flag.
5. Quiet bench conditions: no concurrent cargo/rustc, CPU at max frequency (per hardware-specifications.md), `systemd-run --user --scope -p MemoryMax=24G`.

**Recording protocol**: each experiment gets a row in the Results table below + a detailed entry under "Experiment Entries". A failing experiment's revert is also recorded.

**Generalization rule** (per user direction): every implementation must generalize over the mettail-rust feature set (binders, mixfix, cross-cat, recovery, optional groups, collections, predicates, lex-Fork, cohort sharing). No grammar-specific overfitting.

---

## Results table

| # | Date | Experiment | Tip commit | Gauntlet | chain_50 t-stat (p) | chain_100 t-stat (p) | chain_200 t-stat (p) | chain_1000 t-stat (p) | chain_10000 RSS | Verdict |
|---|------|-----------|------------|----------|---------------------|----------------------|----------------------|------------------------|------------------|---------|
| BASE | 2026-05-26 | Baseline (post L1-L6 + L4.2 + L6) | `5708950` | 4066/0 | — | — | — | — | OOM 24 GB at ~9 min | — |
| 1 | 2026-05-26 | Plan C Substage 0 — read-only length histogram for `incoming_edge_stack` + `recovery_deltas` (under `walker-stats` feature) | `7e82cb6` | 4081/0 | n/a (feature-off zero-cost) | n/a | n/a | n/a | n/a (data-collection next) | **ACCEPT** (pure instrumentation; zero behavior change when feature off) |
| 2 | 2026-05-26 | Plan D E3 Substage 1 — standalone `SppfStackArena` data structure + unit/property tests | `8056b9a` | 4081/0 | n/a (no integration) | n/a | n/a | n/a | n/a | **ACCEPT** (15/15 unit+property tests pass; no behavior change) |
| 3 | 2026-05-26 | Plan D E3 Substage 2 — wire `SppfStackArena` into `BranchCursor::sppf_stack_id` | `f18a847` | 4081/0 + tramp 15/0/2 | **WIN** −5.02 % (t=−8.20, df=26) | **WIN** −3.95 % (t=−8.64, df=27) | **WIN** −1.22 % (t=−2.33, df=27) | NEUTRAL −0.91 % (t=−1.75, df=26) | 8 GB at 21 min (~24 % growth-rate improvement vs L4.2 baseline; still won't fit 24 GB unaided) | **ACCEPT** (3 sizes WIN, 1 NEUTRAL; no regression; representation change unlocks future substages) |
| 4 | 2026-05-26 | Plan C Substage 1 — `Arc<Vec<GssEdgeId>>` → `Arc<SmallVec<[GssEdgeId; N]>>` (N from Substage 0) | n/a (REJECTED pre-attempt) | n/a | n/a | n/a | n/a | n/a | n/a | **REJECT-BEFORE-ATTEMPT** — Substage 0 histograms (chain_50/100/200/1000) show `incoming_edge_stack.max` scales linearly with chain depth: chain_50 max=56, chain_100 max=106, chain_200 max=206, chain_1000 max=1006. p99 well above 32 at every size. Per Plan C decision tree: "p99 > 32 → SmallVec is wrong tool." For chain workloads SmallVec inline would spill on ≥ 94 % of chain_1000+ samples → inline storage pure overhead. `recovery_deltas` 100 % empty for chain workloads (max=0 at every chain size). Pivot to Exp 4-alt: extend E3 path-tree arena to `incoming_edge_stack` (Plan D §E6). |
| 4-alt | 2026-05-26 | Plan D E6 applied to `incoming_edge_stack` — generic `PathTreeArena<T>` + `EdgeStackArena = PathTreeArena<GssEdgeId>` (sub1 `48ebcff` standalone; sub2 `54cfff9` wired) | `54cfff9` | 4102/0 + tramp 15/0/2 | **WIN vs base** −7.69 % (t=−4.24); vs E3 NEUTRAL | **WIN vs base** −7.42 %; vs E3 WIN −3.61 % | **WIN vs base** −10.99 %; vs E3 WIN −9.89 % | **WIN vs base** −7.79 %; vs E3 WIN −6.94 % | OOM 24 GB at 15:44 wall (vs pre-E3 ~9 min — 70 % slower) | **ACCEPT** (3 sizes WIN vs E3, 1 NEUTRAL; 4 sizes WIN vs cumulative baseline; per-cursor `incoming_edge_stack` allocation eliminated via path-tree dedup) |
| 5-S0 | 2026-05-26 | Exp 5 Substage 0 — `visited_dispatch` + `visited_recovery` length histograms | `41d0d22` | 4102/0 | n/a (feature-off zero-cost) | n/a | n/a | n/a | n/a | **ACCEPT** (instrumentation) |
| 5 | 2026-05-26 | Plan B Substage 1 — CursorId-keyed walker-global pilot on `visited_dispatch` | n/a (SKIP-AFTER-DATA) | n/a | n/a | n/a | n/a | n/a | n/a | **SKIP-AFTER-DATA** — see below |
| 6a | 2026-05-26 | Plan A First Substage 6a — types + walker scaffold (`WpdaState::InfixChainIterative`, `WpdaStepAction::IterativeChainAbsorb`, walker arm, `is_iterative_candidate` with PILOT-ONLY `label=="AddInt"` gate) | `a033a97` | 4102/0 | n/a (unreachable — no codegen emission) | n/a | n/a | n/a | n/a | **ACCEPT** (scaffold-only, behavior-equivalent) |
| 6b | 2026-05-26 | Plan A First Substage 6b — codegen activation: `emit_iter_eligible_fn`, modify InfixLoop singleton arm, engine `InfixChainIterative` dispatch arm | `969f3d5` | 4102/0 + tramp 15/0/2 + parity 16/0 | **WIN vs base** −15.32 % (t=−23.08); vs E6 WIN −8.28 % | **WIN vs base** −14.74 %; vs E6 WIN −7.91 % | **WIN vs base** −13.16 %; vs E6 WIN −2.44 % | **WIN vs base** −8.76 %; vs E6 NEUTRAL −1.05 % | OOM 24 GB at 6:14 wall (FASTER OOM than E6-only's 15:44 — ~4 GB/min vs 1.6 GB/min) | **ACCEPT-WITH-CAVEAT** (Welch ACCEPT all 4 chain sizes per user keep-criterion; chain_10000 trajectory regressed — chain-extension elision changes memory pattern, kept GSS frame alive longer accumulates more state). |

---

## Welch's two-sample t-test reference

For two independent samples with N=15 each, means μ₁ and μ₂, sample standard deviations σ₁ and σ₂:

```
t = (μ₁ - μ₂) / √(σ₁²/N + σ₂²/N)

degrees of freedom (Welch–Satterthwaite):
ν = (σ₁²/N + σ₂²/N)² / [ (σ₁²/N)²/(N-1) + (σ₂²/N)²/(N-1) ]

reject H₀ (means are equal) iff |t| > t_critical(ν, α=0.05/2)
```

For N=15+15 the critical t (two-tailed, α=0.05) is approximately 2.05.

---

## Experiment entries

### BASELINE (2026-05-26, tip `4723bee`)

State of repo at session start of experiment workstream:
- Branch: `feature/wfst-architecture`, tip `4723bee` (post-Substage-0 instrumentation, no behavior change vs `5708950`).
- L1-L6 cohort lazy materialization stack shipped.
- L4.2 Arc-wrapping of `recovery_deltas` and `incoming_edge_stack`.
- Both chain_10000 tests `#[ignore]`'d with empirical attribution to per-cursor mutate-every-step pattern defeating Arc-CoW.

**Quiet-bench measurements** (hyperfine N=15, `systemd-run --user --scope -p MemoryMax=24G`, single chain test in isolation, binary direct-invocation no cargo overhead):

| Chain | Mean | σ | σ/μ | Range (min…max) |
|-------|------|---|-----|-----------------|
| `test_right_assoc_chain_50` | 30.2 ms | 0.4 ms | 1.3 % | 29.6 ms … 31.4 ms |
| `test_right_assoc_chain_100` | 73.0 ms | 0.8 ms | 1.1 % | 71.3 ms … 74.4 ms |
| `test_right_assoc_chain_200` | 201.7 ms | 2.6 ms | 1.3 % | 198.8 ms … 209.1 ms |
| `test_right_assoc_chain_1000` | 3.316 s | 0.053 s | 1.6 % | 3.278 s … 3.497 s |

σ/μ all under 2 % — quiet conditions confirmed. JSON exports saved at `/tmp/baseline_chain_*.json` (note: tmp; will not survive reboot — for the per-experiment Welch we'll save per-experiment treatment JSON next to it).

---

(Experiment entries will be appended below as each completes.)

---

### Exp 0.5 (2026-05-26) — Plan C Substage 0 data collection

Build: `--features walker-stats` (binary `trampoline_tests-5d3902e45367797a`).

Histograms via `PRATTAIL_WALKER_STATS=1 ./trampoline_tests --exact test_right_assoc_chain_<N>`:

**`incoming_edge_stack_len_histogram` (samples per step_fanout iteration per cursor)**:

| Chain | N samples | max | 64+ % | 32-63 % | 16-31 % | ≤ 15 % |
|-------|-----------|-----|-------|---------|---------|--------|
| 50  | 7,304   | 56   | 0.0 %  | 43.2 % | 31.8 % | 25.1 % |
| 100 | 14,554  | 106  | 39.6 % | 31.9 % | 15.9 % | 12.5 % |
| 200 | 29,054  | 206  | 69.8 % | 16.0 % | 8.0 %  | 6.2 %  |
| 1000 | 145,054 | 1006 | 93.9 % | 3.2 %  | 1.6 %  | 1.3 %  |

**Conclusion**: `incoming_edge_stack.max` scales LINEARLY with chain depth N. For chain_1000 the p99 is well above 64; for chain_10000 max would be ~10,000. SmallVec inline N=8/16/32/64 all spill on the majority of samples at chain_1000+. **SmallVec is THE WRONG TOOL for this field on chain workloads.**

**`recovery_deltas_len_histogram`**:

| Chain | N samples | max | All buckets |
|-------|-----------|-----|-------------|
| 50   | 7,304    | 0 | 100 % at length 0 |
| 100  | 14,554   | 0 | 100 % at length 0 |
| 200  | 29,054   | 0 | 100 % at length 0 |
| 1000 | 145,054  | 0 | 100 % at length 0 |

**Conclusion**: `recovery_deltas` is 100 % empty on chain workloads. L4.2 Arc-wrap doesn't help chain tests (no Vec allocation ever happens). SmallVec inline N=anything is unused storage. For chain_10000 specifically, recovery_deltas optimization is irrelevant.

Raw output saved under `prattail/docs/design/plans/bench-data/exp0_5_*` if you need them; the headline numbers above are sufficient for the Substage 1 decision.

---

### Exp 4 REJECT (2026-05-26) — Plan C Substage 1 SmallVec for `incoming_edge_stack`

REJECT-BEFORE-ATTEMPT per the Exp 0.5 histograms above. Per Plan C decision tree (substage 0 §"Decision tree based on measured p99"): "p99 > 32 → SmallVec is the wrong tool; revisit with bumpalo or Vec::with_capacity preallocation." chain_1000 p99 > 1000.

**Pivot**: see Exp 4-alt below. The empirical evidence + the structural success of E3 SppfStackArena (Exp 3 ACCEPT) recommends a second path-tree arena over the bumpalo / preallocation alternatives.

---

### Exp 4-alt (planned) — Plan D E6: `IncomingEdgeStackArena`

Extend the E3 SppfStackArena pattern to `BranchCursor::incoming_edge_stack`. Substage 1 = standalone arena + unit tests (mirroring E3 Substage 1). Substage 2 = wire into BranchCursor (mirroring E3 Substage 2).

---

### Exp 5 Substage 0 (2026-05-26) — visited_dispatch + visited_recovery length data

Histograms via `PRATTAIL_WALKER_STATS=1 ./trampoline_tests --exact test_right_assoc_chain_<N>`:

**`visited_dispatch_len_histogram`**:

| Chain | N samples | max | 64+ % | ≤ 31 % |
|-------|-----------|-----|-------|--------|
| 50  | 7,304   | 53   | 0.0 %  | 49.4 % |
| 100 | 14,554  | 103  | 47.7 % | 24.7 % |
| 200 | 29,054  | 203  | 73.8 % | 12.4 % |
| 1000 | 145,054 | 1003 | 94.8 % | 2.5 % |

Same linear-scaling pattern as `incoming_edge_stack` (Exp 0.5). Gate criterion (max > 16 → proceed) triggers.

**`visited_recovery_len_histogram`**: 100 % empty (max=0) on chain workloads. Useless to optimize for chain; matters only for recovery tests / rhocalc.

### Exp 5 SKIP-AFTER-DATA (2026-05-26)

Per-Plan-B-agent gate criterion (max > 16 → proceed) is triggered by the visited_dispatch data, BUT a deeper post-data analysis recommends SKIP for Plan B's *specific design* (walker-global `FxHashMap<CursorId, Arc<FxHashSet<…>>>`):

1. **Plan B's HashMap-keyed design has the same deep-clone cost as today's Arc-CoW.** Each Fork-arm child copies the parent's FxHashSet eagerly (per Plan B: "Fork-arm clone becomes 'allocate new CursorId, copy entries'"). Today's Arc-CoW does the SAME deep clone on first per-cursor mutation post-fork. Plan B doesn't eliminate the deep clone — it just shifts the bookkeeping from `Arc::make_mut` to `walker.cursor_visited_dispatch.entry().or_default()`. Net allocation cost: identical. Plus Plan B adds a HashMap lookup per access (lines 5025, 5426).

2. **H2 precedent.** Arc-CoW on this exact field was rejected at chain_100 -6.9 % p≈0.01 (recorded in `chain-10000-ceiling-lift.md`). Plan B's design has the same per-mutation overhead PLUS the HashMap lookup penalty.

3. **`visited_recovery` is useless to optimize for chain workloads** (100 % empty). The pilot's small theoretical upside applies to chain only via `visited_dispatch`, and even there the design choice doesn't match the dedup pattern that succeeded for E3/E6.

4. **The dedup pattern that succeeded for E3/E6 (path-tree interning) cannot directly apply to a SET.** FxHashSet semantics require contains() in O(1) but path-tree's contains() is O(chain_length). A path-tree-arena-for-sets design would need an LRU cache for the materialized FxHashSet — substantial added complexity that the Plan B agent did not propose.

5. **The cumulative E3 + E6 + L4.1 + L4.2 wins already addressed the major per-cursor allocators.** Exp 4-alt ACCEPT: chain_1000 −7.79 % vs baseline. Further per-cursor field optimizations would need a fundamentally different design (path-tree-arena-for-sets with LRU, or Plan A operator-precedence iterative which reduces cursor_count rather than per-cursor cost).

**Recommendation per ledger row 5**: SKIP Plan B Substage 1; proceed to Exp 6 (Plan A operator-precedence iterative) which targets `cursor_count` (the multiplier in `cursor_count × per-cursor-state = O(N²)` memory) rather than the per-cursor factor that E3 + E6 already addressed.

A future "Exp 5-alt" (path-tree-for-sets with LRU cache for contains()) is documented for follow-up consideration but not in scope at tip `41d0d22`.
