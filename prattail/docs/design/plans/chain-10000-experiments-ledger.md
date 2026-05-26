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
| 1 | TBD | Plan C Substage 0 — read-only length histogram for `incoming_edge_stack` + `recovery_deltas` (under `walker-stats` feature) | — | — | — | — | — | — | — | — |
| 2 | 2026-05-26 | Plan D E3 Substage 1 — standalone `SppfStackArena` data structure + unit/property tests | `8056b9a` | 4081/0 | n/a (no integration) | n/a | n/a | n/a | n/a | **ACCEPT** (15/15 unit+property tests pass; no behavior change) |
| 3 | TBD | Plan D E3 Substage 2 — wire `SppfStackArena` into `BranchCursor::sppf_stack_id` | — | — | — | — | — | — | — | — |
| 4 | TBD | Plan C Substage 1 — `Arc<Vec<GssEdgeId>>` → `Arc<SmallVec<[GssEdgeId; N]>>` (N from Substage 0) | — | — | — | — | — | — | — | — |
| 5 | TBD | Plan B Substage 1 — CursorId-keyed walker-global pilot on `visited_dispatch` | — | — | — | — | — | — | — | — |
| 6 | TBD | Plan A First Substage — operator-precedence iterative for Calculator-Int's `AddInt` | — | — | — | — | — | — | — | — |

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

### BASELINE (2026-05-26, tip `5708950`)

State of repo at session start of experiment workstream:
- Branch: `feature/wfst-architecture`, tip `5708950`.
- L1-L6 cohort lazy materialization stack shipped.
- L4.2 Arc-wrapping of `recovery_deltas` and `incoming_edge_stack`.
- Both chain_10000 tests `#[ignore]`'d with empirical attribution to per-cursor mutate-every-step pattern defeating Arc-CoW.

Quiet-bench baseline measurements to be recorded here once the bench harness runs.

---

(Experiment entries will be appended below as each completes.)
