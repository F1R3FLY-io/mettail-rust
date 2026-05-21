# Phase F.13 H12 Stage 1.5.3 — Multi-Packing Cohort Sharing Soundness Fix

**Status:** Plan agent design (2026-05-21). Targets the single remaining gauntlet failure: `edge_case_tests::precedence_associativity_stress::postfix_binds_tighter_than_unary` (`-3!`).

**Tip:** `8657b60`.

## 1. The single hard problem

Cohort revives at multi-packing dispatch sites compute weights via `cohort.weight_at_dispatch × sppf.symbol_weight_sum(symbol_id)`. That **Goodman-aggregate** weight is a `LexicographicWeight::plus` (lex-min) over ALL linked packings — losing per-packing distinction.

The per-cursor baseline gives each cursor `cohort.pre × packing_i.contribution`. Cohort code gives `cohort.pre × (lex_min over all packings)`. These differ exactly when packings differ in weight.

## 2. The principled fix in one sentence

Capture the worker's pre-dispatch weight per snapshot. At revive time, compute the **additive primary delta** `delta_primary = worker_post.primary - worker_pre.primary`, then assemble the cohort revive's weight as `cohort.weight_at_dispatch × LexicographicWeight::new(TropicalWeight(delta_primary), worker_post.tiebreak…)`. Under LexicographicWeight's left-projection on `times`, this collapses to the per-cursor baseline cursor's weight exactly.

## 3. Why prior attempts failed

| Attempt | Why it failed |
|---|---|
| `cursor.weight = member.weight_at_dispatch × snap.worker_pending_packing_weight` | At pop time, `worker_pending_packing_weight = W::one_ref()` after the LAST fire's `mem::replace`. Effective contribution = identity. |
| `cursor.weight = snap.worker_weight` | Replaces cohort.pre's tiebreak with worker's tiebreak. Broke `rhocalc::int_of_float_add`. |
| `cursor.weight = member.weight_at_dispatch × sppf.symbol_weight_sum(symbol_id)` | Goodman aggregate. Loses per-packing distinction. CURRENT STATE. |
| `witness_packing_id` + `sppf.packing_weight()` | Packing's stored weight = per-Fork-arm residual, not full path. |

All failed for lack of an **algebraic inverse**. The principled fix uses tropical primary subtraction on the LexicographicWeight scalar.

## 4. Approach ranking (top 5)

| # | Approach | Soundness | Disruption | Effort | Risk |
|---|---|---|---|---|---|
| **O** | **Worker_pre capture + tropical-delta semiring extension (chosen)** | **1** | **2** | **1** | **1** |
| J | Drop cohort sharing when key becomes multi-packing | 1 | 2 | 1 | 2 |
| D | Drop already-revived cursors when 2nd worker pops; fall back to per-cursor | 2 | 2 | 1 | 3 |
| I | ConfigKey extension with sppf_stack top SymbolId | 3 | 2 | 2 | 4 |
| L | Refuse merge across packing-distinct cursors | 3 | 3 | 2 | 3 |

## 5. Schema changes

```rust
pub struct WorkerSnapshot<W: SemiringRef> {
    pub worker_inner_state: WpdaState,
    pub worker_last_action_output_cat: Option<u16>,
    pub worker_pending_packing_weight: W,
    pub worker_weight: W,
    pub worker_pre_dispatch_weight: W,  // NEW
}

pub enum DispatchCacheEntry<W: SemiringRef> {
    InFlight {
        cohort_size: u32,
        pending_cohort: Vec<CohortMember<W>>,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        worker_pre_dispatch_weight: W,  // NEW
    },
    Resolved {
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        pending_cohort: Vec<CohortMember<W>>,
        snapshots_drained: usize,
        worker_pre_dispatch_weight: W,  // NEW
    },
    Failed,
}

pub fn register(&mut self, key: DispatchKey, worker_pre_weight: W) -> RegisterOutcome<W> { ... }
```

## 6. TropicalDeltaWeight trait

```rust
pub trait TropicalDeltaWeight: SemiringRef {
    fn tropical_primary_delta(pre: &Self, post: &Self) -> Self;
}

impl TropicalDeltaWeight for LexicographicWeight {
    fn tropical_primary_delta(pre: &Self, post: &Self) -> Self {
        let delta_primary = post.primary.0 - pre.primary.0;
        LexicographicWeight {
            primary: TropicalWeight(delta_primary),
            lex_alt_idx: post.lex_alt_idx,
            src_idx: post.src_idx,
            rule_idx: post.rule_idx,
        }
    }
}
```

## 7. Revive computation

```rust
let delta = W::tropical_primary_delta(
    &snap.worker_pre_dispatch_weight,
    &snap.worker_weight,
);
cursor.weight = member.weight_at_dispatch.times_ref(&delta);
```

## 8. Soundness proof sketch

Under LexicographicWeight semantics:
- `worker.post_i = worker.pre × Π_{j ∈ P_i} Fork_j`. Primary additive: `worker.post_i.primary = worker.pre.primary + Σ Fork_j.primary`.
- `delta = (Σ Fork_j.primary, post.tiebreak)`.
- `R(M, snap_i).weight = cohort.pre × delta = (cohort.pre.primary + Σ Fork_j.primary, cohort.pre.tiebreak)` [left-projection on cohort.pre].
- `PCB(M, P_i).weight = cohort.pre × Π_{j ∈ P_i} Fork_j = (cohort.pre.primary + Σ Fork_j.primary, cohort.pre.tiebreak)` [identical mechanism].
- ∴ `R(M, snap_i).weight = PCB(M, P_i).weight`  ∎

## 9. Staging (4 commits)

### Stage 1.5.3a — Schema + capture (no behavior change)
- Add `worker_pre_dispatch_weight` field to schema.
- Walker passes `parent.weight × branch.weight` at register sites.
- Walker reads field at resolve site.
- **Behavior unchanged**: revive still uses `symbol_weight_sum`. Gauntlet: 6160/1 (unchanged).

### Stage 1.5.3b — TropicalDeltaWeight trait + impl
- Define trait in `automata/semiring.rs`.
- Implement for `LexicographicWeight` in `automata/lex_weight.rs`.
- Add proptest + unit tests.

### Stage 1.5.3c — Switch revive to delta path
- Replace `symbol_weight_sum` call with `TropicalDeltaWeight::tropical_primary_delta`.
- **Expected gauntlet: 6161/0** (no regressions).
- Welch's t-test on chain_50: no walltime regression.
- 100× isolated runs of `-3!` and 6 `float_cast_*`: all pass.

### Stage 1.5.3d — Defensive hardening
- `debug_assert!(!cohort.weight_at_dispatch.is_one_ref(), ...)`.
- Stat counter: `tropical_delta_invocations_total`.

## 10. Axioms / invariants relied upon

| Axiom | Justification | Verification |
|---|---|---|
| **A1.** TropicalWeight subtraction is exact under f64 for path weights < 1000. | IEEE-754 exact arithmetic. | proptest in lex_weight.rs. |
| **A2.** LexicographicWeight's `times` does left-projection on tiebreaks. | `lex_weight.rs:409-422` (explicit). | Unit test. |
| **A3.** A cohort member's `weight_at_dispatch` is non-identity in production. | Cross-cat dispatch entry traverses at least one `BP_TIER_*`-weighted ForkBranch. | Stage 1.5.3d debug_assert. |
| **A4.** Worker_pre is shared across internal Fork sub-cursors of the same root worker. | Internal Forks happen AFTER register; only ONE register per cursor. | Code structure. |
| **A5.** `dispatch_cohort_cache` only ever runs with `W = LexicographicWeight` in shipped code. | Facade uses `LexicographicWeight` at all entry points. | grep verifies. |

## 11. Effort estimate

**1-2 days of focused work.**

- 1.5.3a: 2-4 hours.
- 1.5.3b: 1-2 hours.
- 1.5.3c: 30 min + verification (~1 hour).
- 1.5.3d: 30 min.
- Welch's t-test + 100x stability: 2-3 hours.

## 12. Test plan

### Functional gates (must pass)
- G1: `postfix_binds_tighter_than_unary` PASS.
- G2: Full gauntlet ≥ 6161/0.
- G3: `comparison_after_cast_results::float_cast_*` (6) PASS (regression check).
- G4: `rhocalc::int_of_float_add` PASS (regression check).
- G5: chain_10000 within timeout.

### Performance gates (Welch's t-test, p < 0.05)
- P1: chain_50 walltime within ±5% of baseline.
- P2: chain_200 walltime within ±5%.
- P3: chain_10000 walltime within ±5%.

### Stress
- 100× isolated `-3!` runs → all PASS.
- 100× isolated `float_cast_*` runs → all PASS.
- 100× isolated chain_50 runs → no deadlock/panic.

### Synthetic semantic verification
```rust
#[test]
fn delta_recovers_per_packing_weight() {
    let cohort_pre = LexicographicWeight::from_cost(0.5, 3, 7);
    let worker_pre = LexicographicWeight::from_cost(0.1, 9, 11);
    let worker_post_A = LexicographicWeight::from_cost(0.3, 9, 11);
    let worker_post_B = LexicographicWeight::from_cost(0.4, 9, 11);

    let delta_A = LexicographicWeight::tropical_primary_delta(&worker_pre, &worker_post_A);
    let delta_B = LexicographicWeight::tropical_primary_delta(&worker_pre, &worker_post_B);

    let revive_A = cohort_pre.times(&delta_A);
    let revive_B = cohort_pre.times(&delta_B);

    assert_eq!(revive_A.primary.0, 0.7);  // cohort_pre.primary + delta_A.primary
    assert_eq!(revive_A.src_idx, 3);      // cohort_pre's tiebreak (left-projection)
    assert_ne!(revive_A.primary.0, revive_B.primary.0);  // per-packing distinction
}
```

## 13. Critical files
- `prattail/src/dispatch_cohort.rs`
- `prattail/src/wpda_walker.rs`
- `prattail/src/automata/lex_weight.rs`
- `prattail/src/automata/semiring.rs`
- `languages/tests/edge_case_tests.rs`
