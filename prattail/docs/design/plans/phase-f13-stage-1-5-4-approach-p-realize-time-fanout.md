# Phase F.13 H12 Stage 1.5.4 — Approach P: Realize-Time Cohort Fanout

**Status:** Plan agent design (2026-05-21). Successor to falsified Stage 1.5.3 (tropical-delta) and Stage 1.5.3R (cohort_origin / ConfigKey bucketing).

**Tip:** `a6b05cf`. Gauntlet 6160/1. Sole failure: `precedence_associativity_stress::postfix_binds_tighter_than_unary` (`-3!`).

## 1. Core principle

Move the cohort cache from being a parse-time PRESSURE-RELEASE (short-circuiting cursors during step_fanout) to a parse-time RECORD KEEPER + realize-time FANOUT MULTIPLIER.

1. **At parse-time:** Cohort cache still records workers and pauses cohort members, but NO LONGER revives cohort cursors into branch_cursors. Paused cohort members stay paused for the rest of the parse.
2. **At end-of-parse:** Before realize is called, the cohort cache is QUERIED. For each paused cohort member, a `CohortContinuation` (structural Packing template) is interned into the SPPF.
3. **At realize-time:** Realization walks the SPPF as-is. The deferred Packings appear naturally in `packings_of(symbol_id)` enumeration.

## 2. Schema additions

```rust
pub struct CohortContinuation {
    pub parent_rule_idx: u32,
    pub parent_lo: u32,
    pub parent_hi: u32,
    pub parent_cat_src_idx: u16,
    pub children_template: Vec<SppfId>,
    pub worker_symbol_substitution_slot: usize,
    pub weight_contribution: W,
}

pub struct OuterRuleTemplate {
    pub outer_rule_idx: u32,
    pub outer_cat_src_idx: u16,
    pub outer_lo_pos: u32,
    pub other_children: Vec<SppfId>,
    pub substitution_slot: usize,
}

pub struct CohortMember<W> {
    pub return_frame: BranchCursor<W>,
    pub weight_at_dispatch: W,
    pub outer_rule_template: OuterRuleTemplate,  // NEW
}

pub enum DispatchCacheEntry<W> {
    InFlight { ... },
    Resolved {
        symbol_id: SppfId,
        hi_pos: u32,
        pos_at_dispatch: u32,
        worker_snapshots: Vec<WorkerSnapshot<W>>,
        pending_cohort: Vec<CohortMember<W>>,
        snapshots_drained: usize,
        worker_pre_dispatch_weight: W,
        deferred_continuations: Vec<CohortContinuation>,  // NEW
    },
    Failed,
}
```

## 3. Lifecycle

### Pause site
At `allocate_fork_push_child` InflightCollision: read parent's GSS top RuleAt frame → construct OuterRuleTemplate. Eligibility gate (§5) decides whether to pause. If false, fall through to per-cursor.

### Worker pop
After FirstResolve/SnapshotAppended in `cursor_gss_pop_via_edge`: drain `pending_cohort` into `deferred_continuations` by applying `CohortContinuation::from_member_template`.

### End-of-step drain
**REMOVED.** No more cohort cursor revival during parse.

### End-of-parse install
In `resolve_at_end_of_input`, BEFORE realize: `install_cohort_continuations()` iterates all Resolved entries, interns each deferred Packing into SPPF, links to outer Symbol. `harvest_chain` recursively wraps nested cohort dispatches.

## 4. Soundness

**Theorem:** After `install_cohort_continuations`, SPPF contains all and only the Packings that per-cursor baseline would have interned for each cohort member's outer rule against the worker's sub-parse symbol_id.

Proof: engine purity (Lemma 1) ensures worker's sub-parse output = any cohort member's independent sub-parse output. Symbol-dedup + Packing-dedup ensure SppfId identity. Template adequacy (Lemma 2) ensures outer Packing matches per-cursor baseline.

## 5. Cohort eligibility gate

Required for soundness — only paus cohort members whose outer rule is "pure-pass-through-with-last-child-dispatch":

```rust
fn is_cohort_eligible(cursor, branch) -> bool {
    let outer_frame = self.gss.node(cursor.node)?;
    if outer_frame.symbol.kind != RuleAt(_) { return false; }
    let outer_arity = engine.action_for(...).arity;
    let accumulated = inspect_cursor_state();
    accumulated == outer_arity - 1  // dispatch is the LAST child
}
```

Mixfix rules with post-dispatch children fall back to per-cursor.

## 6. Memory bounds

- `MAX_DEFERRED_PER_KEY = 8`
- `MAX_TOTAL_DEFERRED_CONTINUATIONS = 1024` walker-global
- Per-continuation ~64 bytes; max overhead 64 KB per parse.

## 7. Staging (4 commits)

| Commit | Scope | Effort | Verification |
|---|---|---|---|
| 1.5.4-a | Schema + capture | 1-2 days | gauntlet 6160/1 unchanged |
| 1.5.4-b | Disable parse-time revive | 0.5 day | INTENTIONAL regressions |
| 1.5.4-c | Realize-time install + harvest_chain | 3-4 days | gauntlet 6161/0, `-3!` PASS |
| 1.5.4-d | Hardening + observability | 1 day | Remove Stage 1.5.3R artifacts |

**Total: 10-15 working days (2-3 weeks).**

## 8. Why this fixes `-3!`

The worker's Int sub-parse fires BOTH Sub-A (P_Fact) and Sub-B (P_Neg) reduces, linking both to S(Int, 0, 3). Cohort members (Pass-2c IntToBigInt, IntToBigRat, etc.) install their outer wrapping Packings via install_cohort_continuations. realize naturally enumerates `Neg(Fact(IntLit(3)))` via P_Neg.

## 9. Risk register

| Risk | Impact | Mitigation |
|---|---|---|
| OuterRuleTemplate needs codegen extension | +3 days | Reuse existing rule-metadata tables |
| Nested cohort harvest_chain | +2 days | MAX_HARVEST_DEPTH=4; fall back |
| Mixfix rules not covered | speedup loss only | Eligibility gate; no correctness loss |
| Cache survives reset incorrectly | memory leak | Explicit clear() after realize |

## 10. Fallback: Approach R

If Approach P proves infeasible (Commit 1 or 3 blockers > 5 days), fall back to Approach R: detect snapshot divergence in resolve() → mark entry Failed → cohort members fall through. 4 hours. Lose ~5% chain_50 speedup. Trivially sound.
