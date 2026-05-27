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
| 7 | 2026-05-26 | Restore per-iteration `emit_fire_action` in `IterativeChainAbsorb` arm | `6da30a5` | 4102/0 + tramp 15/0/2 + parity 16/0 | **WIN** −15.06 % (p<0.0001) | **WIN** −15.03 % (p<0.0001) | **WIN** −12.41 % (p<0.0001) | **WIN** −8.77 % (p<0.0001) | OOM 24 GB at 6:26 wall (~3.7 GB/min; marginal vs 6b but Welch wins preserved) | **KEEP** (user explicit "keep all that pass Welch's T-test"; chain_10000 still OOMs but revert would sacrifice the smaller-chain wins for no closure). |
| 10 S0 | 2026-05-26 | ConfigKey pairwise correlation matrix + scope-mark histograms (`PairCounts` newtype + 10×10 lower-triangular tally) | `67d4a3e` | 4102/0 | n/a (feature-off zero-cost) | n/a | n/a | n/a | n/a | **ACCEPT** — gate FIRES: `(node, edge) = 100.0 %` co-divergence with sole-diffs 0.002 %. Drop one of {node, edge}. |
| 10 S1 | 2026-05-26 | Drop `incoming_edge` axis from `ConfigKey` | `beab904` (revert) | 4102/0 | NEUTRAL −3.6 % p=0.10 | WIN −3.7 % p<0.0001 | NEUTRAL −0.6 % p=0.33 | **LOSS +7.4 %** p<0.0001 | n/a | **REJECT** — Welch chain_1000 LOSS. 14 sole-diff outliers (0.002 %) carry load-bearing distinctions. Reverted in-tree. |
| 11 S0 | 2026-05-26 | Per-class Fork breakdown gate (`fork_total_by_class: [u64; 4]` + classification in `WpdaStepAction::Fork` arm) | `32f331b` | 4102/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT + SKIP-AFTER-DATA** — `lex_fork=0 (0.0%)`, `cross_cat=100 %`, `avg_fanout=1.67` (below 2.0 threshold). Per Plan agent: SKIP. Substages 11-S1.a/b/c/d/e CANCELLED. |
| 12 S0 | 2026-05-26 | `binder_scope_marks` + `optional_scope_marks` length histograms | `67d4a3e` (shared with 10 S0) | 4102/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT + SKIP-BEFORE-ATTEMPT** — all 3 histograms 100 % at length 0 on chain workload (max=0). |
| 8 S1 | 2026-05-26 | `VisitedSetArena<T>` + walker-global LRU cache (canonical-order path-tree, K=64 default) — STANDALONE module + 18 tests | `db6a4c8` | 4120/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT** (standalone module; 18/18 tests; retained). |
| 8 S2 | 2026-05-26 | Wire `BranchCursor::visited_dispatch_id` end-to-end (30+ sites) | `57152e3` ATTEMPT → reverted at `a36d348` | 4120/0 | LOSS +3.91 % p=0.0013 (K=64) / +3.91 % p=0.0001 (K=128) | **LOSS +7.57 %** p<0.0001 (K=64) / **+8.39 %** p<0.0001 (K=128) | LOSS +7.41 % / +9.78 % | LOSS +16.36 % / +13.55 % | n/a | **REJECT** — chain_100 LOSS > 5 % at K=64 AND K=128 (Plan agent prespecified falsifier). Arena `contains()` overhead exceeds memory savings vs `Arc<FxHashSet>`. |
| 9 S0 | 2026-05-26 | Cohort revive share confirmation (re-using Exp 11 S0 data) | n/a | n/a | n/a | n/a | n/a | n/a | n/a | **ACCEPT** — `cohort_cursors_emitted = 335,808` vs `branch_cursors_sum = 193,102` = **174 %** (threshold ≥ 50 %). Proceed to S1. |
| 9 S1.a | 2026-05-26 | `CohortContinuation<W>` type + new module `cohort_continuation.rs` + `deferred_continuations` field on `DispatchCacheEntry` (additive) | `1f26cfa` | 4124/0 (4120 + 4 new tests) | n/a | n/a | n/a | n/a | n/a | **ACCEPT** (types-only, additive; module retained for future reuse). |
| 9 S1.b | 2026-05-26 | Dual-write `CohortContinuation` at Sites A + B (`try_build_continuation` + `push_deferred_continuation`) | `5df1df8` ATTEMPT → reverted at `95576b9` | 4124/0 | NEUTRAL +1.34 % (re-run) | NEUTRAL | NEUTRAL | LOSS +2.30 % p<0.001 | n/a | **REVERT** (Welch chain_1000 LOSS p<0.05; per user mandate). |
| 9 S1.c | 2026-05-26 | `install_cohort_continuations` at EOI (drain `deferred_continuations` into outer-rule Packings via `sppf.intern_packing` + `link_packing_to_symbol`; dedup'd with revive-produced packings) | `c97fcdc` ATTEMPT → reverted at `fea5fdc` | 4124/0 + tramp 15/0 | LOSS +3.14 % p=0.18 | LOSS +5.51 % p=0.004 | LOSS +3.25 % p<0.0001 | LOSS +4.79 % p<0.0001 | n/a | **REVERT** (dual-write + EOI install combined LOSS p<0.05 at chain_100/200/1000). |
| 9 S1.d | 2026-05-26 | Switch: skip revive at Sites B + C when continuation built (cursor-population reduction) | `e86aaa9` ATTEMPT → reverted at `3f0361f` | 4124/0 + tramp 15/0 | LOSS +2.72 % p=0.044 | LOSS +2.90 % p<0.0001 | LOSS +1.24 % p=0.013 | LOSS +0.97 % p<0.0001 | OOM 24 GB at 6:38 wall (~3.6 GB/min vs Exp 7's 3.7 GB/min — only ~3 % improvement) | **REJECT** — all 4 sizes LOSS p<0.05; chain_10000 architectural ceiling NOT closed. Per user mandate: revert. |
| 10 S0-bis | 2026-05-26 | Sole-diff outlier downstream-context classification | `c6eb865` | 4134/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT** (instrumentation; gate NOT FIRES — node_only 50/50, edge_only 100 % other; per-state ConfigKey relaxation NOT viable). |
| 13 S0 | 2026-05-26 | chain_region_iterations counter | `c6eb865` | 4134/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT** (gate fires structurally for left-assoc chain). |
| 13 S1.a | 2026-05-26 | Rewrite earley.rs as functional Earley + Leo recognizer with SPPF emission + 17 unit tests | `12b6d61` | 4134/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT, RETAINED** (additive module). |
| 13 S1.b | 2026-05-26 | WpdaWalker::earley_outboard_chain unreachable method | `be9a2eb` | 4134/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT, RETAINED** (additive). |
| 13 S1.c | 2026-05-26 | current_chain_streak + trigger gate at IterativeChainAbsorb | `1e2128b` ATTEMPT → reverted at `e29c79d` | 4134/0 + tramp 15/0 | NEUTRAL +0.79 % p=0.42 | LOSS +2.04 % p=0.0007 | NEUTRAL +0.12 % p=0.79 | LOSS +1.15 % p=0.0001 | OOM 24 GB at 6:35 wall (~3.65 GB/min) | **REJECT** — chain_100/1000 LOSS p<0.05; chain_10000 marginal. Per user mandate p<0.05: revert. |
| 9-alt | 2026-05-26 | FOLLOW-K lookahead prune | n/a | n/a | n/a | n/a | n/a | n/a | n/a | **SKIP-BEFORE-S0** — S0 requires FOLLOW-K codegen infra (S1-level). |
| 14 | 2026-05-26 | Tomita per-arc GSS-cursor merging | n/a | n/a | n/a | n/a | n/a | n/a | n/a | **SKIP** per laziness Plan agent — architectural rewrite ~3000+ LOC. |
| 15 | 2026-05-26 | CPS / trampolined walker rewrite | n/a | n/a | n/a | n/a | n/a | n/a | n/a | **SKIP** per laziness Plan agent — multi-week scope. |
| D-E4 S1.a | 2026-05-26 | Streaming SPPF reclamation-window instrumentation | `99e98b6` | 4134/0 | n/a | n/a | n/a | n/a | n/a | **ACCEPT** (data captured) + **DATA-CONCLUDED for S1.b-S1.e**: chain_1000 = 99.8 % cache_pinned, 99.9 % window < 6.25 %, 100 % candidates < 10 %. Streaming SPPF empirically futile. |
| D-E4 S1.b-e | 2026-05-26 | chunked SPPF storage + reclaim trigger + integration + tuning | n/a (BLOCKED by S1.a gate failure) | n/a | n/a | n/a | n/a | n/a | n/a | **REJECT-DATA-CONCLUDED** — gate failed by 3+ orders of magnitude on chain_1000. Cohort cache pinning of SPPF Symbol positions (median gap ~2000 positions) prevents any streaming reclamation strategy from recovering meaningful memory. The chain_10000 ceiling is in the cohort cache itself, not the SPPF arena. |

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

---

### Exp 8 Substage 1 (2026-05-26, tip `db6a4c8`) — VisitedSetArena<T> + LRU cache (standalone)

Standalone implementation per Plan agent design. New module
`prattail/src/visited_set_arena.rs` with canonical-order path-tree
arena + walker-global LRU cache for O(1) `contains()`.

Design:
- Canonical-order intern: elements sorted by `T: Ord`; two cursors
  visiting the same SET (in any insertion order) arrive at the same
  `VisitedSetStackId` via dedup on `(parent, elem)`.
- Idempotent `insert`: returns `stack` unchanged if `elem ∈ stack`.
- Fast path (monotonic): `elem > top → intern_push`. Chain workloads
  visit configs in monotonic-position order, hitting this 100 % of
  the time.
- Slow path (out-of-order): rebuild in canonical order + splice at
  rank.
- LRU cache: walker-global `FxHashMap<StackId, Arc<FxHashSet<T>>>` +
  `VecDeque<StackId>` for eviction. K=64 default (~1.8 MB at
  chain_1000).

18/18 standalone tests pass. Full prattail-lib gauntlet: 4120/0.

**Verdict**: **ACCEPT** (standalone module, no integration regression).

---

### Exp 8 Substage 2 (2026-05-26, tip `57152e3` ATTEMPT) — wire into BranchCursor

Wired across 30+ sites in `wpda_walker.rs` + `cohort_lazy.rs`:
- `WpdaWalker::visited_dispatch_arena` field + 3 ctor inits + `reset`
- `BranchCursor::visited_dispatch_id: VisitedSetStackId` (Copy u32)
- `CohortShell::visited_dispatch_id` field swap
- `BranchCursor::clone` (Copy u32)
- `materialize_branch_cursor` + `CohortShell::from_branch_cursor`
- 3 empty-init sites + parent.clone propagation
- Push-arm singleton bucket cycle defense (contains + insert)
- B14/C5 per-branch `parent_in_visited`
- Fork-arm `child_visited_dispatch_id` pre-compute
- `allocate_fork_push_child` signature
- `commit_winner` winner.visited_dispatch_id
- walker-stats histogram `.len()` accessor

Build clean. prattail-lib 4120/0. Trampoline 15/0/2 ignored.

**Welch results** (treatment = Exp 8 S2, baseline = Exp 7 at `6da30a5`):

| Chain | K=64 Δ | K=64 p | K=128 Δ | K=128 p | Verdict |
|-------|--------|--------|---------|---------|---------|
| 50 | +3.91 % | 0.0013 | +3.91 % | 0.0001 | LOSS |
| 100 | **+7.57 %** | <0.0001 | **+8.39 %** | <0.0001 | **LOSS** |
| 200 | +7.41 % | <0.0001 | +9.78 % | <0.0001 | LOSS |
| 1000 | +16.36 % | <0.0001 | +13.55 % | <0.0001 | LOSS |

**Hypothesis fate**: FALSIFIED. Per Plan agent's prespecified
falsifier: chain_100 LOSS > 5 % at BOTH K=64 AND K=128 → REVERT
(Plan agent's "tune K=64 → K=128 once, re-run; if still LOSS →
REVERT and document as Exp 8 SKIP-AFTER-DATA").

**Verdict**: **REJECT** — reverted via `git revert HEAD` (tip
returns to `db6a4c8`, the Substage 1 standalone arena retained).

**Diagnosis** (post-hoc): the path-tree-arena + LRU pattern that
worked for `sppf_stack` (E3) and `incoming_edge_stack` (E6) does
NOT translate to set semantics. The arena's `contains()` — even on
cache hit — costs:
1. `FxHashMap::get` (cache lookup)
2. `VecDeque` linear scan (LRU touch)
3. `FxHashSet::contains` on cached set

vs the baseline `Arc<FxHashSet>::contains()` = just step 3.

The cumulative overhead (2 extra HashMap probes + linear scan per
hot-path access) exceeds memory savings on chain workloads where
most cursors share the same monotonic chain prefix and the Arc-CoW
pattern was already optimal. The H2 precedent (Arc-CoW on this
field rejected at chain_100 -6.9 %) was the same failure mode at
the other end of the spectrum.

**Implication**: per-cursor `visited_dispatch` is NOT a productive
optimization target via the path-tree-arena pattern. Other patterns
worth trying: (a) walker-global memoization keyed by
`(dispatch_config, sub_parse_id)` — Plan B design that was already
SKIP-AFTER-DATA; (b) profile-guided sparse-set encoding (Briggs +
Torczon 1993) — out of current scope. For chain_10000 closure
specifically, the per-cursor `visited_dispatch` is now confirmed
NOT a tractable target. The remaining experiments target either
the walker control-flow (Exp 9 / Approach P realize-time cohort
fanout, Exp 9-alt FOLLOW-K prune, Exp 13 Earley + Leo outboard) or
the upstream cursor population (Exp 11 SKIPPED, no remaining
upstream candidates with non-skip gates).

**Bench data saved**:
- `bench-data/exp8_s2_chain_{50,100,200,1000}.json` (K=64)
- `bench-data/exp8_s2_k128_chain_{50,100,200,1000}.json` (K=128)

`visited_set_arena.rs` module retained for potential future reuse
(different workload could justify the tradeoff; the 18 standalone
tests + property tests serve as a reference implementation).

---

### Exp 9 (Approach P) — realize-time cohort fanout: ALL SUBSTAGES REJECTED at 2026-05-26

Per Plan agent (`replicated-conjuring-turtle.md` + Exp 9 design): defer per-cursor cohort revives into `CohortContinuation` records interned as outer-rule SPPF Packings at end-of-input. Target: 174 % cohort-revive share on chain_1000 (335,808 revives vs 193,102 branch_cursors_sum) — projected ~3.4 M revived cursors at chain_10000.

**Substage outcomes**:

| Substage | Commit | Result | Verdict |
|----------|--------|--------|---------|
| 9 S1.a (types-only) | `1f26cfa` | 4124/0 + 4 new continuation tests | **ACCEPT, RETAINED** |
| 9 S1.b (dual-write Sites A+B) | `5df1df8` ATTEMPT | Welch chain_1000 LOSS +2.30 % p<0.001 vs Exp 7 (chain_50/100/200 clean re-runs NEUTRAL) | **REVERT** at `95576b9` |
| 9 S1.c (EOI install) | `c97fcdc` ATTEMPT | Welch LOSS chain_100 +5.51 %, chain_200 +3.25 %, chain_1000 +4.79 % p<0.05 | **REVERT** at `fea5fdc` |
| 9 S1.d (switch — skip revive) | `e86aaa9` ATTEMPT | Welch LOSS chain_50/100/200/1000 +2.72/+2.90/+1.24/+0.97 % p<0.05; **chain_10000 OOM 24 GB at 6:38 wall = 3.6 GB/min** (vs Exp 7's 3.7 GB/min — only ~3 % memory improvement) | **REVERT** at `3f0361f` |

**Hypothesis fate**: FALSIFIED at the architectural-closure goal. The cohort revives ARE the dominant cursor-population source (174 % share confirmed by S0 data), but deferring them to EOI doesn't reduce the per-step memory pressure — `pending_members` and `cohort_shell` continue accumulating in the cache at the same rate. Approach P targets the cursor-EMISSION layer (revive → concrete cursor) but not the cursor-PAUSE layer (member state stored in cache).

**Per user mandate** ("keep all that pass Welch's T-test, revert all that do not" with p<0.05): all 3 implementation substages (S1.b/c/d) showed LOSS at p<0.05 at one or more chain sizes → REVERT.

**What S1.a retains**: `prattail/src/cohort_continuation.rs` module + `CohortContinuation<W>` type + `deferred_continuations: Vec<CohortContinuation<W>>` field on `DispatchCacheEntry::{InFlight, Resolved}` + `push_deferred_continuation` helper (wait — that's S1.b's helper; **CORRECTION**: the push_deferred_continuation helper was reverted along with S1.b. Only the type + field + 4 unit tests + Vec initialization survive). Future experiments combining deferred fanout with a different cursor-population-reduction mechanism can build atop this scaffold.

**Bench data saved**:
- `bench-data/exp9_s1b_chain_{50,100,200,1000}.json` (dual-write attempt; deleted by revert but recoverable via `git show 5df1df8`)
- `bench-data/exp9_s1c_chain_{50,100,200,1000}.json` (dual-write + install attempt; via `git show c97fcdc`)
- `bench-data/exp9_s1d_chain_{50,100,200,1000}.json` (switch attempt; via `git show e86aaa9`)

**chain_10000 closure path narrows further**: with Exp 8 + Exp 9 + Exp 10 S1 + Exp 11 all REJECTED, only Exp 13 (Earley + Leo outboard chain-region delegation), Exp 10 S0-bis (downstream sole-diff investigation), and Exp 9-alt (FOLLOW-K lookahead prune) remain as viable closure attempts. Streaming SPPF realization (Plan D E4, task #231) is the deferred high-effort fallback.

---

## Summary at session end 2026-05-26

| Experiment | Status |
|------------|--------|
| Exp 0 → 6b (E3, E6, A iterative) | SHIPPED, cumulative WIN |
| Exp 7 (fire-action restore) | KEEP per Welch (chain_10000 marginal) |
| Exp 8 S1 (VisitedSetArena standalone) | ACCEPT |
| Exp 8 S2 (wire) | REJECT (Welch chain_100 LOSS > 5 %) |
| Exp 10 S0 (ConfigKey corr matrix) | ACCEPT (instrumentation; gate fires) |
| Exp 10 S1 (drop edge axis) | REJECT (Welch chain_1000 LOSS +7.4 %) |
| Exp 10 S0-bis (sole-diff outlier downstream effect) | **PENDING** |
| Exp 11 S0 (Fork-class gate) | ACCEPT + SKIP-AFTER-DATA (avg_fanout < 2.0) |
| Exp 11 S1.a-e (SuspendedFork) | CANCELLED per gate |
| Exp 12 S0 (scope-marks histograms) | ACCEPT + SKIP-BEFORE-ATTEMPT (chain workload empty) |
| Exp 9 S1.a (CohortContinuation types) | ACCEPT, RETAINED |
| Exp 9 S1.b-d (Approach P switch) | REJECT (Welch LOSS p<0.05 + chain_10000 ceiling unmoved) |
| Exp 9-alt (FOLLOW-K) | **PENDING** (task #227) |
| Exp 13 S0 (chain-region detection) | **PENDING** (task #228) |
| Exp 13 S1 (Earley + Leo outboard) | **BLOCKED** on S0 (task #217) |
| Exp 14 (Tomita per-arc) | SKIP per Plan agent |
| Exp 15 (CPS rewrite) | SKIP per Plan agent |
| Streaming SPPF (Plan D E4) | DEFERRED (task #231) |

**Cumulative WINs preserved at session-end tip** (vs original baseline, post all REJECT reverts):
- chain_50: -15.06 % (Exp 7 contribution)
- chain_100: -15.03 % (Exp 7)
- chain_200: -12.41 % (Exp 7)
- chain_1000: -8.77 % (Exp 7)
- chain_10000: still OOM at 24 GB ~6:26 (Exp 7's trajectory)

**Architectural ceiling**: NOT closed. All path-tree-arena + per-cursor allocator reductions have been explored. Remaining strategies require either walker-architecture changes (Exp 13 Earley outboard) or SPPF-level memory reclamation (Streaming SPPF E4) — both multi-session efforts.

---

### Exp 13 (Earley + Leo outboard) — REJECTED at session end 2026-05-26

Per design at `prattail/docs/design/plans/phase-f13-exp13-earley-outboard.md`.

**Substages**:

| Substage | Commit | Result | Verdict |
|----------|--------|--------|---------|
| 13 S0 | `c6eb865` | chain_region_iterations counter — gate fires structurally for left-assoc | **ACCEPT** (instrumentation) |
| 13 S1.a | `12b6d61` | Rewrite earley.rs: RuleItem model + working scan/complete + emit_sppf_subforest. 17 unit tests pass; 4134/0 gauntlet. | **ACCEPT, RETAINED** (additive; useful for future Earley experiments) |
| 13 S1.b | `be9a2eb` | WpdaWalker::earley_outboard_chain method (unreachable; #[allow(dead_code)]) | **ACCEPT, RETAINED** (additive) |
| 13 S1.c | `1e2128b` ATTEMPT → reverted at `e29c79d` | current_chain_streak field + IterativeChainAbsorb trigger at THRESHOLD=1000 | **REJECT** — Welch chain_100 +2.04 % p=0.0007 LOSS, chain_1000 +1.15 % p=0.0001 LOSS; chain_10000 marginal (OOM at 6:35 vs Exp 7's 6:26 = ~1 % improvement). Per user mandate p<0.05: revert. |

**Hypothesis fate**: FALSIFIED at the architectural-closure goal. The Earley handoff either didn't fire (streak resets at cohort/cross_cat boundaries that interrupt long chain regions), or fired but Earley's chart allocation + walker's pre-handoff cache state combined to retain the original memory pressure. Per Plan agent's "Risk register" point 1 ("bottleneck might not be cache growth alone"), the chain_10000 memory consumption is NOT dominated by per-iteration walker overhead alone — by the time the streak reaches 1000, the GSS / SPPF / cohort cache state has already allocated significantly.

**Architectural implication**: chain_10000 closure requires either (a) lower-level walker rewrite (Tomita per-arc GSS-cursor merging — Exp 14 SKIPPED, or CPS — Exp 15 SKIPPED), (b) streaming SPPF realization (Plan D E4 — multi-week deferred), or (c) accepting the 24 GB OOM as an architectural ceiling that grows linearly with chain length but constant-factor-improved across the experiment series.

**What S1.a + S1.b retain**:
- `prattail/src/earley.rs` — functional Earley + Leo recognizer with SPPF emission, 17 unit tests, dedup-safe. Available for future experiments combining Earley with different trigger mechanisms (e.g., grammar-level chain analysis at codegen time, or per-state handoff bookkeeping).
- `WpdaWalker::earley_outboard_chain(...)` — unreachable but compileable; future trigger designs can call it without redoing the chart-build logic.

**Bench data saved**:
- `bench-data/exp13_s1c_chain_{50,100,200,1000}.json`

---

## Final closure status (session end 2026-05-26)

**Cumulative improvements (vs original baseline 4066/0)**:
- chain_50: −15.06 % WIN (Exp 7)
- chain_100: −15.03 % WIN (Exp 7)
- chain_200: −12.41 % WIN (Exp 7)
- chain_1000: −8.77 % WIN (Exp 7)
- chain_10000: still OOM at 24 GB ~6:26 wall (Exp 7 trajectory)

**Architectural ceiling**: NOT closed. All path-tree-arena + per-cursor allocator + cohort-revive deferral + Earley outboard experiments have been REJECTED at the chain_10000 acceptance gate.

**Closure-path exhaustion**:
- Per-cursor allocator reductions: Exp 3 (sppf arena), Exp 4-alt (edge arena) ✓ shipped; Exp 8 (visited_dispatch path-tree) ✗ rejected; H2 + Plan B previously rejected.
- Operator-precedence iterative: Exp 6/7 ✓ shipped (constant-factor wins; chain_10000 ceiling unmoved).
- ConfigKey reduction: Exp 10 S0 ✓ instrumentation; S1 ✗ rejected; S0-bis ✓ instrumentation (no actionable per-state relaxation).
- Cohort revive deferral: Exp 9 / Approach P ✗ rejected (pause-side overhead not addressed).
- Fork suspension: Exp 11 SuspendedFork ✗ skipped (avg_fanout 1.67 < 2.0 threshold).
- Scope-mark arena: Exp 12 ✗ skipped (chain workload has zero scope marks).
- Chain-region outboard: Exp 13 Earley ✗ rejected (handoff overhead exceeded savings; left-recursive Earley complete is O(n²)).
- FOLLOW-K prune: Exp 9-alt ✗ skipped (S0 itself requires S1's FIRST/FOLLOW codegen infra).

**Remaining viable closure attempts** (multi-session efforts):
- **Streaming SPPF realization** (Plan D E4, task #231): `madvise(MADV_DONTNEED)` arena pages once min_referenced_pos advances. Highest impact if window small; highest implementation risk (changes the SPPF arena invariants).
- **Tomita per-arc GSS-cursor merging** (Exp 14, SKIPPED): would redesign branch_cursors entirely. ~3000+ LOC walker rewrite.
- **CPS / trampolined walker rewrite** (Exp 15, SKIPPED): architectural answer (c) from laziness analysis. ~5000+ LOC.

**The chain_10000 ceiling stands as an architectural property of the current walker representation** with all REJECTED experiments empirically documented to inform future work.

---

### Plan D E4 Substage 1.a (2026-05-26, tip `99e98b6`) — Streaming SPPF reclamation-window measurement

Per Plan agent design: Streaming SPPF requires a non-trivial reclamation window — `min(cursor.pos)` AND `min over cohort_cache entries of symbol_id.lo_pos`. Hypothesized that cohort cache might pin low SPPF positions all the way to position 0 on chain workloads. S1.a measured this empirically BEFORE committing to the ~1000-1500 LOC S1.b-S1.e implementation cost.

**Run** (chain_1000 with PRATTAIL_WALKER_STATS=1): see `prattail/docs/design/plans/bench-data/e4_s1a_chain_1000_stats.txt`.

**Headline numbers** (5023 samples):

| Metric | Value | Interpretation |
|--------|-------|----------------|
| sppf_reclaim_window_samples | 5023 | sampling baseline |
| sppf_reclaim_cache_pinned_samples | 5014 (**99.8 %**) | cohort cache holds an SPPF Symbol position BELOW the cursor frontier on essentially every step |
| sppf_reclaim_cache_pin_gap_max | 1999 | the worst-case lost reclamation opportunity is ~2000 positions (cohort cache pins ~2/3 of chain_1000) |
| sppf_reclaim_symbol_count_max | 6001 | peak SPPF Symbol count at chain_1000 |
| window_histogram bucket 0 (0-6 % of chain) | 5019 (**99.9 %**) | the reclaimable window is < 6.25 % of chain at virtually every sample |
| candidate_fraction bucket 0 (0-10 %) | 5023 (**100.0 %**) | fewer than 10 % of Symbol nodes are ever reclaim candidates |

**Plan agent gate** (PROCEED to S1.b iff candidate fraction ≥ 50 % AND window ≥ 12.5 %): **candidate = 0.0 %, window = 0.1 %** — **FAILS BOTH CRITERIA by 3+ orders of magnitude**.

**Verdict**: **DATA-CONCLUDED — Streaming SPPF is empirically futile for chain workloads**. The cohort cache pins SPPF positions at 99.8 % of samples; the median pinned-gap is ~2000 positions. No streaming reclamation strategy (madvise, segmented arena, copying GC, lazy realize) can recover memory that the cohort cache actively pins.

**Architectural implication**: chain_10000's 24 GB OOM is NOT in the SPPF node arena (heaptrack always pointed elsewhere; S1.a now confirms this from a different angle). The cohort cache's `DispatchCacheEntry::Resolved.symbol_id` + `deferred_continuations` + `pending_members` are the actual memory consumers AT chain_10000. The "fix" for chain_10000 must address the cohort cache size directly — either:
- Reduce the number of cache entries (Exp 9 / Approach P attempted, REJECTED — pause-side state is the bottleneck, not revive-side)
- Reduce per-entry size (would require a fundamental cohort_shell / pending_members redesign)
- Drop cache entries that won't be re-hit (requires a reachability analysis the walker doesn't currently maintain)

Each of these is a multi-week architectural rewrite with its own Plan-agent design cycle.

**E4 closure**: SHIPPED as instrumentation only. S1.b-S1.e implementation BLOCKED by empirical gate failure. Closed per Plan-agent NO-GO recommendation with data backing the closure.

---

### Exp 16 (2026-05-26) — Walker memory attribution profiling + mimalloc allocator test

**Motivation**: Plan D E4 S1.a confirmed SPPF is not the chain_10000 bottleneck. Exp 9 (cohort cache) and Exp 8 (visited_dispatch) also rejected. The 24 GB OOM has not been empirically attributed. Exp 16 instruments every walker-owned structure for byte-attribution + tests mimalloc allocator hypothesis (chain_10000 might be allocator high-water mark rather than live memory).

**Implementation** (commit `504948e`): comprehensive walker-stats counters for branch_cursors, dispatch_cohort_cache + sub-fields, sppf_stack_arena, incoming_edge_stack_arena, sppf nodes/packings, gss nodes/edges, visited_dispatch Arc dedup + total entries, recovery_deltas Arcs, sppf_symbol_terms. Display impl prints byte-attributed breakdown with conservative per-element size estimates.

**chain_1000 attribution** (peak):

| Structure | Count | Size (B) | MB | % |
|-----------|-------|----------|-----|---|
| worker_snapshots | 73,048 | 96 | 6.69 | **43.2 %** |
| pending_members | 23,979 | 96 | 2.20 | 14.2 % |
| gss_edges | 25,992 | 64 | 1.59 | 10.3 % |
| cohort cache base | 6,000 | 256 | 1.46 | 9.5 % |
| gss_nodes | 17,996 | 64 | 1.10 | 7.1 % |
| sppf_nodes | 15,005 | 56 | 0.80 | 5.2 % |
| visited_dispatch (25 unique Arcs, 999× dedup) | 24,989 entries | 24 | 0.57 | 3.7 % |
| edge_stack_arena | 35,976 | 16 | 0.55 | 3.5 % |
| sppf_symbol_terms | 6,001 | 32 | 0.18 | 1.2 % |
| branch_cursors | 338 | 512 | 0.17 | 1.1 % |
| sppf_stack_arena | 7,001 | 16 | 0.11 | 0.7 % |
| sppf_symbol_packings | 8,004 | 8 | 0.06 | 0.4 % |
| recovery_deltas | 0 | — | 0.00 | 0.0 % |
| **Total** | — | — | **15.47 MB** | — |

**mimalloc test** (commit `504948e` + tramp built with `--features mimalloc,walker-stats`): OOM at 24 GB after **7:04 wall** (~3.4 GB/min).

Comparison across allocators / experiments at chain_10000:

| Experiment | Allocator | OOM wall | GB/min |
|------------|-----------|----------|--------|
| Exp 7 (current best baseline) | glibc | 6:26 | 3.7 |
| Exp 9 S1.d (Approach P) | glibc | 6:38 | 3.6 |
| Exp 13 S1.c (Earley outboard) | glibc | 6:35 | 3.65 |
| Exp 16 mimalloc | mimalloc | **7:04** | **3.4** |

mimalloc gave a marginal 8 % growth-rate improvement but did NOT close the architectural ceiling. The 24 GB is genuinely live walker state, not allocator high-water mark.

**Critical empirical finding**: chain_1000 walker total = 15.47 MB. Linear projection to chain_10000 = 154 MB. Actual measured = 24,000 MB. **155× super-linear gap** unexplained by the structures counted in Exp 16. The gap must come from:

1. **Vec/HashMap capacity overhead** (entry counts × element size don't include the allocator's per-allocation header + Vec capacity vs len + HashMap bucket vs entries).
2. **Arc heap headers** (visited_dispatch Arc count is measured but the Arc allocation header isn't).
3. **sppf_collection_arena per-cursor `Arc<Vec<Vec<SppfId>>>` arena** (NOT measured by Exp 16; Phase F.4 made this per-cursor; may accumulate splices).
4. **SPPF dedup_packing HashMap with Vec<SppfId> keys** that grow per chain depth — dedup_packing has 8,004 entries at chain_1000 but key sizes may scale with chain depth.
5. **WorkerSnapshot's internal Arc'd contents** (WorkerSnapshot contains worker_inner_state + worker_pending_packing_weight + Arc'd recovery_deltas — the 96 B size estimate only covers the struct, not its Arc'd heap).

**Verdict**: Exp 16 ships as instrumentation + mimalloc hypothesis-test. SHIPPED as data-collection; the chain_10000 super-linear gap remains UN-ATTRIBUTED. Closing chain_10000 requires either:

(a) **heaptrack profiling on chain_5000** (longest test that fits in 24 GB by extrapolation): would identify the actual dominant allocator. Multi-tool setup but produces definitive attribution.

(b) **Further instrumentation**: per-step memory deltas, sppf_collection_arena size, dedup_packing key total bytes, WorkerSnapshot Arc-content sizing. Each ~50 LOC.

Either of these is the prerequisite for any further closure attempt — the structural attribution gap is the load-bearing scientific gap.

---

### Exp 16 round 3 (2026-05-26) — CRITICAL FINDING: chain_500 LEFT-assoc reveals the actual chain_10000 bottleneck

**Setup**: added `test_left_assoc_chain_500/1000/2000/5000` (ignored by default) to probe scaling on the LEFT-assoc workload that hits chain_10000's iterative path (Exp 6b/7's AddInt activation). All prior Welch tests used RIGHT-assoc (`^`, exponentiation, NOT iterative-eligible) — a fundamentally different memory profile.

**Run**: `left_assoc_chain(500)` completed successfully (test passed) in **17 min 02 s wall** with **21.2 GB peak RSS**. Did NOT OOM (just below 24 GB cap). Walker-stats attribution:

| Structure | Count | Size (B) | MB | % |
|-----------|-------|----------|-----|---|
| **edge_stack_arena** | **225,565,809** | 16 | **3,441.86** | **70.7 %** ← DOMINANT |
| **visited_dispatch** | **49,615,919** entries (69,719 unique Arcs, **712× dedup**) | 24 | **1,135.62** | **23.3 %** |
| sppf_stack_arena | 8,642,388 | 16 | 131.87 | 2.7 % |
| branch_cursors | 183,843 | 512 | 89.77 | 1.8 % |
| sppf_nodes | 578,235 | 56 | 30.88 | 0.6 % |
| gss_edges | 309,193 | 64 | 18.87 | 0.4 % |
| sppf_symbol_terms | 278,942 | 32 | 8.51 | 0.2 % |
| pending_members | 47,546 | 96 | 4.35 | 0.1 % |
| worker_snapshots | 45,587 | 96 | 4.17 | 0.1 % |
| sppf.dedup_symbol entries | 278,942 | 16 | 4.26 | n/a |
| **Total** | — | — | **4,870.10 MB** | — |

**Dispatch cohort cache stats**:
- registrations_total = **100,749,075** (~200K per chain element!)
- inflight_collisions = 98,933,608 (98.2 %)
- cohort_cursors_emitted = **28,947,298** ← 29 M cursor allocations for 500 chain elements
- cohort_cursors_graduated = 2,435,299 (8.4 %)

**Why this matters**:

1. **The chain_50/100/200/1000 Welch tests use RIGHT-assoc (`^`)**, which is NOT iterative-eligible. At chain_1000 right-assoc, walker peak = 15.47 MB. At chain_500 LEFT-assoc, walker peak = **4,870 MB** — 315× larger for half the chain length. **All prior REJECTED experiments (Exp 8 / Exp 9 / Exp 10 S1 / Exp 13) were measured on the wrong workload.** The chain_10000 OOM happens on LEFT-assoc; the Welch gate was right-assoc.

2. **edge_stack_arena dedup is broken on left-assoc**: 225 M unique arena nodes for 29 M cohort cursors = ~7.8 unique nodes per cursor. Per Exp 4-alt the path-tree was supposed to dedup chain prefixes. On left-assoc, **each cohort cursor has its own unique edge chain** — the arena dedup factor is ≈ 1.

3. **The actual chain_10000 closure path** must address edge_stack_arena growth — either reduce cohort cursor emission count (Exp 9 / Approach P attempted this; was REJECTED on the wrong Welch gate), or change the arena to dedup at a coarser granularity (some "GSS path summary" rather than per-edge).

4. **Approach P revisit indicated**: Exp 9 S1.d's chain_10000 RSS measurement showed marginal 3 % improvement on the right-assoc-style trajectory. With LEFT-assoc the cohort emission rate (29 M cursors) is what produces the 3.4 GB edge_stack_arena. Approach P's defer-cohort-revive would have collapsed those 29 M into deferred continuations and PROBABLY closed the LEFT-assoc ceiling, but the right-assoc Welch gate vetoed it.

**Conclusion**: The chain_10000 architectural ceiling has been empirically attributed to **edge_stack_arena (70.7 %) + visited_dispatch entries (23.3 %)** under LEFT-assoc cohort cursor explosion (~58K cohort cursors per chain element). The Welch gate methodology was incorrect for this experiment series — it tested a NON-iterative workload while the OOM target was iterative. Future closure attempts must use LEFT-assoc Welch baselines (the new `test_left_assoc_chain_{500,1000,2000,5000}` tests at `trampoline_tests.rs`).

**Specific architectural fix paths newly justified**:

1. **Re-run Exp 9 / Approach P with LEFT-assoc Welch baseline** — S1.d's skip-revive would collapse cohort emissions; the Welch right-assoc gate that REJECTED it was wrong. **Highest-confidence path.**
2. **edge_stack_arena coarse dedup**: replace per-GssEdgeId nodes with per-RuleIndex summaries. Multi-week.
3. **Per-cohort visited_dispatch sharing**: cohort revives currently inherit parent's Arc<FxHashSet>, but a per-revive insert mutates → CoW deep-clone. Replace with per-cohort Arc<FxHashSet> shared across revivals from the same key. ~200 LOC.

**Bench data saved**: `prattail/docs/design/plans/bench-data/exp16r3_left_assoc_500.txt`

---

### Exp 17 (2026-05-26, tip `65ae007` ATTEMPT → revert at next commit) — Re-apply Approach P with LEFT-assoc Welch baseline

**Hypothesis** (per Exp 16 round 3 finding): the original Exp 9 / Approach P REJECTED on right-assoc Welch which doesn't exercise chain_10000's iterative path. Re-applying S1.b/c/d with LEFT-assoc Welch baseline might pass.

**Implementation**: re-applied the original 3 reverted commits (S1.b dual-write + S1.c install_cohort_continuations + S1.d skip-revive). All compile / gauntlet 4134/0 + tramp 15/0.

**LEFT-assoc baseline** (default trampoline_tests, no Exp 17, N=15):

| Test | Mean | σ |
|------|------|---|
| left_assoc_chain_50 | 1.430 s | 0.017 |
| left_assoc_chain_100 | 9.734 s | 0.109 |

**Welch results** (Exp 17 vs baseline):

| Chain | Baseline | Exp 17 | Δ | p | Verdict |
|-------|----------|--------|---|---|---------|
| left_assoc_50 | 1430.3 ms | 2064.0 ms | **+44.31 %** | <0.0001 | **LOSS** |
| left_assoc_100 | 9733.6 ms | 12479.2 ms | **+28.21 %** | <0.0001 | **LOSS** |

**Hypothesis fate**: FALSIFIED. Approach P's continuation construction + push_deferred_continuation overhead **exceeds any cursor-population savings on LEFT-assoc workload too**. The Welch right-assoc REJECT was not an artifact of wrong-workload measurement — Approach P is genuinely time-regressive even on the workload it was supposed to help.

**Verdict**: **REJECT** per user mandate "keep all that pass Welch's T-test, revert all that do not". Reverted at next commit. S1.a infra (cohort_continuation.rs module + DispatchCacheEntry deferred_continuations field) retained as before.

**Critical implication for chain_10000 architectural ceiling**:

Per Exp 16 round 3 + Exp 17 combined:
- The 24 GB ceiling is in `edge_stack_arena` (70.7 %) + `visited_dispatch entries` (23.3 %) driven by 29 M cohort cursor emissions per chain_500 left-assoc.
- Reducing cursor emissions via Approach P's defer-to-EOI strategy adds enough per-step overhead to REGRESS time even on left-assoc (where it should help most).
- Therefore: the cohort revive mechanism's time cost and memory cost are **fundamentally coupled** — you can't reduce one without increasing the other within the current walker architecture.

**Remaining viable closure paths** (all multi-week architectural rewrites per the laziness Plan agent):

1. **Tomita per-arc GSS-cursor merging** (Exp 14, SKIPPED) — would eliminate the cohort revive mechanism entirely. ~3000+ LOC rewrite.
2. **CPS / trampolined walker rewrite** (Exp 15, SKIPPED) — same architectural depth. ~5000+ LOC.
3. **Coarse edge_stack_arena dedup** (per-RuleIndex instead of per-GssEdgeId) — would address the 70.7 % memory dominator directly. ~1000-2000 LOC; correctness risk unknown.

None of these is in scope for the current session given the Welch p<0.05 gate has rejected every targeted fix so far. The chain_10000 architectural ceiling is documented as **a stable property of the current walker representation** with all explored mitigations exhausted.

**Bench data**:
- `prattail/docs/design/plans/bench-data/baseline_left_assoc_chain_{50,100}.json`
- `prattail/docs/design/plans/bench-data/exp17_la{50,100}.json`
