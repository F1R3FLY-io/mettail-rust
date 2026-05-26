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

---

### Exp 6b ACCEPT-WITH-CAVEAT (2026-05-26, tip `969f3d5`) — Plan A iterative codegen activation

Already entered in row 6b above. Caveat: chain_10000 OOM trajectory regressed from E6's 15:44 wall (1.6 GB/min) to 6:14 wall (4 GB/min). Cause diagnosed by Explore Agent 1 of the post-6b investigation: the `IterativeChainAbsorb` walker arm (`wpda_walker.rs:5167-5201`) elides the chain-extension GSS push AND the per-iteration `Unwinding → Pop(Return) → emit_fire_action` cycle. Without fire-action, sppf_top diverges per iteration, blocking merge of cursors that should otherwise collapse.

Exp 7 (below) attempts to fix this.

---

### Exp 7 (2026-05-26, tip `6da30a5`) — fix per-iteration fire-action in IterativeChainAbsorb arm

**Hypothesis** (Plan agent, prespecified): restoring per-iteration `emit_fire_action` in the `IterativeChainAbsorb` arm will (a) preserve Exp 6b's chain_50/100/200/1000 wins AND (b) recover the E6 chain_10000 OOM trajectory (≤ 1.6 GB/min).

**Falsifier** (Plan agent, prespecified): if chain_10000 RSS rate > 2× E6 baseline (3.2 GB/min), REVERT both Exp 7 and Exp 6b. The interpretation would be that the chain-extension GSS push elision itself is regressive.

**Acceptance gate**: chain_50/100/200/1000 Welch NEUTRAL-or-WIN AND chain_10000 RSS growth ≤ 1.6 GB/min AND gauntlet 4102/0 preserved.

**Implementation**: in the `IterativeChainAbsorb` arm of `dispatch_step` (`wpda_walker.rs:5167-5201`), when `already_chained == true`, BEFORE the existing pos/weight/state mutations, call `emit_fire_action(cursor, symbol)`. This restores the per-iteration fire-action that the chain-extension elision had skipped. The chain-extension GSS push is still elided (Exp 6b's allocation win preserved). SPPF chain shrinks by 1 per iteration → cohort merge can rediscover equivalent cursors.

**Results (Welch t-test, exp7 vs baseline N=15 quiet, MemoryMax=24G)**:

| Chain | Baseline μ±σ | Exp 7 μ±σ | Δ | t | df | p | Verdict |
|-------|-------------|-----------|-----|---|-----|---|---------|
| 50 | 30.16 ms ± 0.43 | 25.62 ms ± 0.72 | -15.1 % | -20.90 | 22.9 | <0.0001 | **WIN** |
| 100 | 73.04 ms ± 0.83 | 62.07 ms ± 0.97 | -15.0 % | -33.26 | 27.3 | <0.0001 | **WIN** |
| 200 | 201.72 ms ± 2.56 | 176.69 ms ± 2.79 | -12.4 % | -25.59 | 27.8 | <0.0001 | **WIN** |
| 1000 | 3316.17 ms ± 52.9 | 3025.21 ms ± 14.7 | -8.8 % | -20.53 | 16.1 | <0.0001 | **WIN** |

**chain_10000**: OOM at 24 G after **6 min 26 s wall (~3.7 GB/min)**. Falsifier threshold = 3.2 GB/min (2× E6's 1.6). **Falsifier triggered** — though only marginally (3.7 vs 3.2 = 16 % over).

**Gauntlet**: 4102/0 prattail-lib preserved.

**Hypothesis fate**: PARTIALLY confirmed. Fire-action restoration preserves chain_50/100/200/1000 wins (Welch WIN ×4). Fire-action restoration does NOT recover E6 trajectory at chain_10000 (3.7 GB/min vs target ≤ 1.6 GB/min).

**Verdict**: **DEFERRED** to user (cross-criteria tradeoff). Per Plan agent's prespecified falsifier: REVERT 6b+7. Per Welch (user's explicit keep-criterion): KEEP 6b+7 — all 4 sizes WIN at p<0.0001 with magnitudes -8.8% to -15.1%. Trade-off:
- **Keep 6b+7**: chain_50/100/200/1000 ~12 % faster; chain_10000 OOMs at 6:26 vs E6's 15:44.
- **Revert 6b+7**: chain_10000 returns to E6 trajectory (still OOMs); chain_50/100/200/1000 lose the wins.

Either way chain_10000 still OOMs — so revert just sacrifices the smaller-chain wins for a slower-but-still-failed chain_10000 trajectory. Exp 10 S0 (below) reveals the real merge-blocker is structural (node + edge axes always co-diverge at 100%), beyond what fire-action alone can fix.

---

### Exp 10 Substage 0 (2026-05-26, tip `67d4a3e`) — ConfigKey pairwise correlation matrix

Read-only instrumentation (`PairCounts: PairCounts` newtype + `merge_miss_pair_participation` field + pairwise loop in `sample_merge_misses` multi-diff branch). Display impl prints lower-triangular cells. Zero behavior change when `walker-stats` feature off.

**Build**: 4102/0 prattail-lib under `--features walker-stats`.

**Run** (chain_1000, Exp 7 state in tree): see `prattail/docs/design/plans/bench-data/exp10_12_s0_chain_1000_stats.txt`.

**Pair-correlation matrix** (denom = multi_diff_total = 383,566):

| Pair (i, j) | Co-occurrence count | % of multi-diff |
|-------------|---------------------|-----------------|
| (state, node) | 68,778 | 17.9 % |
| (state, edge) | 68,732 | 17.9 % |
| (state, sppf_top) | 49,622 | 12.9 % |
| (state, lex_alt_idx/weight_src_idx/weight_rule_idx) | 10,480 | 2.7 % each |
| (state, cohort_origin) | 220 | 0.1 % |
| **(node, edge)** | **383,429** | **100.0 %** |
| (node, sppf_top) | 313,278 | 81.7 % |
| (node, lex_alt_idx/weight_src_idx/weight_rule_idx) | 18,541 | 4.8 % each |
| (node, cohort_origin) | 9,475 | 2.5 % |
| (edge, sppf_top) | 313,328 | 81.7 % |
| (edge, lex_alt_idx/weight_src_idx/weight_rule_idx) | 18,523 | 4.8 % each |
| (edge, cohort_origin) | 9,525 | 2.5 % |
| (cohort_origin, sppf_top) | 3,470 | 0.9 % |
| (sppf_top, lex_alt_idx/weight_src_idx/weight_rule_idx) | 18,523 | 4.8 % each |
| (lex_alt_idx, weight_src_idx/weight_rule_idx) | 18,582 | 4.8 % each |
| (weight_src_idx, weight_rule_idx) | 18,582 | 4.8 % |

**Sole-diff baseline** (from `merge_miss` line; %s of multi_diff_total = 383,566):
- node_only = 8 (0.002 %)
- edge_only = 6 (0.002 %)
- state_only = 6022 (1.57 %)
- All others (sppf_top, cohort_origin, lex_alt_idx, etc.) = 0 or near-0

**Gate analysis** (Plan agent's criterion: co-occurrence > 0.95 AND sole-diff < 1 % → drop candidate):

| Pair | Co-occurrence | Sole-diff (i) | Sole-diff (j) | Verdict |
|------|---------------|---------------|---------------|---------|
| **(node, edge)** | **100.0 %** | node 0.002 % | edge 0.002 % | **FIRES — drop one of {node, edge}** |
| (node, sppf_top) | 81.7 % | node 0.002 % | sppf_top 0.006 % | below 95 % gate, do not drop |
| (edge, sppf_top) | 81.7 % | edge 0.002 % | sppf_top 0.006 % | below 95 % gate, do not drop |
| (state, node) | 17.9 % | state 1.57 % | node 0.002 % | state sole-diff too high (>1 %) |

**Verdict**: **ACCEPT** (instrumentation) + **GATE FIRES** for Exp 10 Substage 1. The (node, edge) co-divergence is structural: when node differs, edge ALWAYS differs (and vice versa, modulo 8+6 outliers). Both have sole-diff rates of 0.002 % — neither carries information the other lacks. Dropping ONE of {node, edge} from ConfigKey will let 383,429 currently-blocked merges proceed (100 % of node-or-edge multi-diff cases).

**Caution**: node and edge being 100 % co-divergent on chain_1000 is **specific to chain workloads** where every cursor sits on a fresh GSS edge. On non-chain workloads (binders, cross-cat, recovery) the correlation may differ. Exp 10 Substage 1 will need a generalization-test gate (gauntlet 4102/0 plus rhocalc trampoline 15/0/2 ignored).

**Mechanical recommendation** (subject to plan-agent review of Substage 1 design): drop `edge` since `node` carries more semantic weight (the GSS node identity is the more natural per-cursor discriminator; `edge` is the incoming-edge ID, which is derivable from `node` for chain workloads).

---

### Exp 12 Substage 0 (2026-05-26, tip `67d4a3e`) — binder + optional scope-marks histograms

Read-only instrumentation (3 new `WalkerStats` fields: `binder_scope_marks_len_*`, `optional_scope_marks_len_*`, `binder_scope_names_len_*`). `stats_histogram_sample!` calls at per-cursor step_fanout sampling site.

**Build**: 4102/0 prattail-lib under `--features walker-stats`.

**Run** (chain_1000):

| Histogram | n samples | max | All buckets |
|-----------|-----------|-----|-------------|
| binder_scope_marks_len | 145,054 | 0 | 100 % at length 0 |
| optional_scope_marks_len | 145,054 | 0 | 100 % at length 0 |
| binder_scope_names_len (inner Vec<String>) | not sampled (outer is always empty) | n/a | n/a |

**Gate analysis** (Plan agent's criterion: if max ever exceeds 1 with non-trivial frequency, path-tree arena candidate):

**Gate does NOT fire** for chain workload. Like `recovery_deltas` (Exp 4 REJECT) and `visited_recovery` (Exp 5 SKIP), scope marks are always empty on chain workloads — there are no binders or optional groups to scope-mark. Exp 12 Substage 1 (path-tree arena for scope marks) would be wasted effort for chain_10000 closure.

**Verdict**: **ACCEPT** (instrumentation) + **REJECT-BEFORE-ATTEMPT** for Exp 12 Substage 1 (chain track). Scope marks may matter for binder-heavy workloads (rhocalc PInputs/PNew, Lambda) but those are not in the chain_10000 critical path.

---

## Summary — chain_10000 closure status (post-Exp 7 + Exp 10 S0 + Exp 12 S0)

**Remaining viable experiments per data**:

1. **Exp 10 Substage 1**: drop one of {node, edge} from ConfigKey. **GATE FIRES** on chain_1000 (100 % co-divergence, 0.002 % sole-diff). 383K merge opportunities currently lost — partial close of chain_10000 ceiling expected. Risk: medium (generalization across non-chain workloads needs gauntlet verification).

2. **Exp 8**: path-tree arena for `visited_dispatch` + LRU cache for contains(). Agent 2 diagnosed `visited_dispatch.max = 1003` linearly scaling → ~7 GB live peak at chain_10000. Substage 0 data already in ledger (row 5-S0).

3. **Approach P** (Plan agent Candidate 1, designed at `phase-f13-stage-1-5-4-approach-p-realize-time-fanout.md` but unshipped): realize-time cohort fanout. Highest impact for chain. Substage 0 would be `cohort_revive_count` counter; threshold ≥ 50 % of branch_cursors_sum.

4. **Earley + Leo outboard** (Plan agent Candidate 2): `prattail/src/earley.rs` has full Earley + Leo coded but unwired. Delegate chain regions to Earley; lift back as a single Packing. Substage 0 = chain-region detection counter.

**Order recommendation** (based on Exp 10 S0 evidence and prior plan-agent ranking):
- Exp 10 Substage 1 first (lowest-effort, highest direct evidence — gate already fires on actual data).
- Exp 8 second (per-cursor allocator dominant per Agent 2 diagnosis).
- Approach P or Earley outboard third (highest-impact-if-it-works, but more design risk).

**Pending user decision** (Exp 7 verdict):
- Keep 6b + 7 (chain_50-1000 WIN, chain_10000 LOSS) AND ship Exp 10 next
- Revert 6b + 7 per Plan-agent's prespecified falsifier AND ship Exp 10 on E6 baseline

---

### Exp 10 Substage 1 REJECTED (2026-05-26) — drop `incoming_edge` from ConfigKey

**Hypothesis**: drop `incoming_edge` from ConfigKey (per Exp 10 S0 gate firing: (node, edge) 100.0 % co-divergent with sole-diffs 0.002 % each) to unlock 383,429 currently-blocked merges. Expected: NEUTRAL or WIN at all 4 chain sizes; possibly help chain_10000 RSS.

**Implementation**: removed `incoming_edge: Option<GssEdgeId>` from `ConfigKey` struct (`wpda_walker.rs:1847`) and from the construction in `merge_equivalent_cursors` (`wpda_walker.rs:8288-8290`). ~25 LOC.

**Build**: 4102/0 prattail-lib + 15/0/2 tramp ignored.

**Welch results** (treatment = Exp 10 S1, baseline = Exp 7 at tip `6da30a5`):

| Chain | Exp 7 μ±σ | Exp 10 S1 μ±σ | Δ | p | Verdict |
|-------|----------|---------------|---|---|---------|
| 50 | 25.62 ms ± 0.72 | 24.69 ms ± 1.94 | -3.6 % | 0.098 | NEUTRAL |
| 100 | 62.07 ms ± 0.97 | 59.77 ms ± 0.89 | -3.7 % | <0.0001 | WIN |
| 200 | 176.69 ms ± 2.79 | 175.58 ms ± 3.24 | -0.6 % | 0.326 | NEUTRAL |
| **1000** | 3025 ms ± 14.7 | 3248 ms ± 62.6 | **+7.4 %** | **<0.0001** | **LOSS** |

**chain_10000 RSS**: test killed at 5:13 CPU time (could not complete in window). Inconclusive measurement; the chain_1000 LOSS is decisive.

**Hypothesis fate**: FALSIFIED at chain_1000. Per user mandate ("keep all that pass Welch's T-test, revert all that do not"), chain_1000 +7.4 % LOSS p<0.0001 is a clean REJECT.

**Verdict**: **REJECT** — reverted both edits.

**Diagnosis** (post-hoc reasoning): the 8 + 6 = 14 cases (out of 383,566 multi-diff) where node ≠ but edge =, or edge ≠ but node =, are load-bearing at chain_1000. The 100 % co-divergence rate is necessary but not sufficient — the small absolute sole-diff counts represent decisions where edge carries unique information that node does not. The Exp 10 S0 gate threshold ("co-occurrence > 0.95 AND sole-diff < 1 %") was met, but the actual sole-diff cases are concentrated at chain_1000 hot paths where ConfigKey collisions cascade into duplicated work. Dropping `edge` causes cursors to attempt merge → fail downstream re-discriminator (sppf_top or weight components) → carry extra work per cursor.

**Implication for Exp 10**: the (node, edge) pair-correlation alone is insufficient evidence to drop either axis. A stronger S0-bis would need to identify the *downstream effect* of the 14 outlier sole-diff cases — e.g., are they on the cohort-revive path? Are they at the InfixLoop boundary? Without that, the Plan agent's recommendation is to leave ConfigKey unchanged.

**Bench data saved**:
- `prattail/docs/design/plans/bench-data/exp10_s1_chain_{50,100,200,1000}.json`

---

### Exp 11 Substage 0 (2026-05-26) — per-class Fork breakdown gate

Read-only instrumentation. Added `fork_total_by_class: [u64; 4]` + `fork_branches_by_class: [u64; 4]` to `WalkerStats` + classification loop in `WpdaStepAction::Fork` arm (`wpda_walker.rs:5360-5410`). Three classes (walker generic over W, can't peek at LexicographicWeight.primary to distinguish pass-2c from h12): 0=lex_fork, 1=cross_cat_total (over-approximates implicit_cast + h12), 2=other. Display impl prints class breakdown + avg-fanout-by-class.

**Build**: 4102/0 prattail-lib under `--features walker-stats` (and feature-off).

**Run** (chain_1000): see `prattail/docs/design/plans/bench-data/exp11_s0_chain_1000_stats.txt`.

**Headline numbers**:

| Class | Firings | % | Avg fanout |
|-------|---------|---|------------|
| lex_fork (LexAlt* family) | 0 | 0.0 % | 0.00 |
| cross_cat_total (CrossCatDelegate) | 17,981 | 100.0 % | 1.67 |
| other | 0 | 0.0 % | n/a |

**Gate analysis** (Plan agent's criterion: PROCEED iff `(lex_fork + implicit_cast) / total > 0.30` AND `avg_fanout(lex) + avg_fanout(cast) > 2.0`):

- Percentage criterion: PASS (cross_cat_total = 100 % which is the over-approximation of `lex_fork + implicit_cast + h12`)
- avg_fanout criterion: **FAIL** (1.67 < 2.0)

Per Plan agent's prespecified decision table: "Combined % > 30 % but `avg_fanout ≤ 2.0` → **SKIP** — suspension bookkeeping cost exceeds savings (only 2 specs per frame; the L3.4 H12 path already covers ≥3-way)."

**Independent finding** (chain workload-specific): `lex_fork=0` confirms the chain test has **no lexical ambiguity** (single-character `+` tokens). The Plan agent's hypothesis that lex-Fork is the upstream source of cursor population was wrong for chain workloads (correct for rhocalc binders, edge_case grammars, calculator cast suites). For chain_10000 specifically, lex-Fork suspension would save zero work.

**Verdict**: **ACCEPT** (instrumentation) + **SKIP-AFTER-DATA** for Exp 11 Substages 1.a-1.e. The L3.4 H12 cohort path already handles ≥ 3-way cases; SuspendedFork would only save half a cursor per Fork on average — not worth the 600-800 LOC investment. Pivot to **Exp 8** (path-tree arena for `visited_dispatch` with LRU cache) next, per Plan agent's second-priority recommendation.

**Risk implication**: chain_10000 closure path now narrows to (Exp 8, Exp 10 S0-bis, Exp 9/Approach P, Exp 9-alt/FOLLOW-K, Exp 13/Earley). Exp 11 is closed without implementation.
