# Phase F.13 Stage L3 — Implementation Plan

Branch: `feature/wfst-architecture`, tip `f30fb6a`.

## Scope summary

L3 introduces the `Frame<W>` field-type swap in `WpdaWalker` and the bulk-step cohort fast path. Memory benefit lands here: ObsInvariant actions step the shell once instead of N times. Six substages, each independently revertable.

Key file & line anchors (current `f30fb6a` state):

| File | LoC | Role |
|---|---|---|
| `prattail/src/wpda_walker.rs` | 13,703 | `WpdaWalker`, `BranchCursor`, `apply_action_*`, `step_fanout`, `merge_equivalent_cursors`, `revive_cohort_member_with_snapshot` |
| `prattail/src/cohort_lazy.rs` | 480 | `Frame`, `CohortFrame`, `CohortShell`, `CohortMemberState`, `materialize_branch_cursor`, `DivergenceClass` |
| `prattail/src/dispatch_cohort.rs` | 667 | `DispatchCacheEntry`, `take_pending_for_drain`, `pause_cohort_member` |
| `prattail/src/wpda_runtime.rs` | 3,126 | `WpdaState` (`WpdaStepAction` is in walker.rs L276) |

---

## L3.1 — Field-type swap: `Vec<BranchCursor<W>>` → `Vec<Frame<W>>`

### Goal
Purely mechanical conversion. No behavior change. `Frame::Cohort` not yet constructed; every write uses `Frame::Concrete(cursor)`; every read uses `frame.as_concrete_expect()` or similar accessor. Compiles + 4058/0 gauntlet.

### Reads/writes inventory (`wpda_walker.rs`)

Field declaration: **line 520**.

**Write sites:**
- `2398`, `2466`, `2529`: ctor `vec![initial_cursor]` → `vec![Frame::Concrete(initial_cursor)]`
- `2572`: `self.branch_cursors = vec![BranchCursor::seed_from_live(...)]` → wrap
- `2963`: `self.branch_cursors = vec![BranchCursor { ... }]` → wrap
- `4614`: `swap_remove(0)` returns `Frame`; pattern-match to extract concrete
- `4623`: `self.branch_cursors.push(BranchCursor{...})` → wrap
- `4691`: `self.branch_cursors.push(cursor)` → wrap
- `4711`: `self.branch_cursors = children` where `children: Vec<BranchCursor>` → `children.into_iter().map(Frame::from).collect()`
- `7044`, `7047`: `Vec<BranchCursor<W>>` → `Vec<Frame<W>>`
- `7077`: `self.branch_cursors = vec![cursor]` → wrap
- `7086`, `7096`, `7099`, `7133`: `new_cursors.push(...)` / `.extend(children)` → wrap each push
- `7139`: `self.branch_cursors = new_cursors`
- `7471`, `7493`, `7641`: `merge_equivalent_cursors` drain + write
- `7688`, `7689`: `commit_winner` swap_remove + clear
- `7948`: `self.branch_cursors = vec![BranchCursor{...}]`
- `8047`: `truncate(k)` — works unchanged
- `8521`: `branch_cursors.first()` — needs `.and_then(|f| f.as_concrete())`

**Read sites:**
- `2686`, `2703`: `current_snapshot` enumerates cursors — wrap with `.as_concrete().expect(...)`
- `2811`–`2812`: `branch_cursors_for_test()` — return `&[Frame<W>]`; update test sites
- `3191`, `3210`, `3223`, `3225`: `run_to_end_of_input` fingerprint read — use `.as_concrete_expect()`
- `3372`, `3470`, `3471`, `3475`: `resolve_at_end_of_input` retain — pattern `frame.as_concrete().map_or(false, |c| ...)`
- `3490`, `3492`, `3502`, `3520`, `3521`, `3569`, `3570`: `commit_winner`/`pick_lex_min_resolved` indexing
- `7290`, `7298`, `7315`–`7316`: `sample_merge_misses` (walker-stats feature)
- `7482`, `7488`, `7490`–`7493`: merge enter (L3.1 invariant: no Cohort frames yet)
- `7726`: drop loop
- `8026`, `8036`, `8047`, `8050`: `maybe_prune_frontier`
- Test sites: lines 11372, 11422, 12483, 12587, 12610, 12642, 12683, 12712, 12738, 12788, 12822, 12855, 12887, 12935, 12985, 13073, 13200, 13406

### Accessor strategy

`cohort_lazy.rs` has `as_concrete`, `as_concrete_mut`, `into_concrete`. Add:
- `pub fn as_concrete_expect(&self) -> &BranchCursor<W>` → `self.as_concrete().expect("L3.1: branch_cursors entry must be Concrete (no cohort frames before L3.4)")`
- `pub fn as_concrete_expect_mut(&mut self) -> &mut BranchCursor<W>`
- `pub fn concrete_iter(slice: &[Frame<W>]) -> impl Iterator<Item = &BranchCursor<W>>`

### Test gate
```bash
cargo +nightly build -p mettail-prattail 2>&1 | tail -20
systemd-run --user --scope -p MemoryMax=24G cargo test --release -p mettail-prattail --lib 2>&1 | tail -10
```
SHIP if 4058/0; REVERT (single commit) otherwise.

### LoC estimate
+200 lines.

### Revert
Single commit; `git revert HEAD`.

---

## L3.2 — Stub `step_cohort_frame` (always materialize)

### Goal
Add dispatch arm so `step_fanout` handles `Frame::Cohort` by materializing → per-cursor step. Behavior-equivalent to today (because no `Frame::Cohort` is ever constructed yet at end of L3.2).

### Code transformations

**Add to `cohort_lazy.rs`:**
- `pub const MAX_COHORT_FRAME_MEMBERS: usize = 256;`
- Free function:
  ```rust
  pub fn materialize_cohort_to_frames<W: SemiringRef + Clone>(
      cf: CohortFrame<W>,
  ) -> Vec<Frame<W>>
  ```

**Add to `wpda_walker.rs` impl WpdaWalker (around line 7040):**
```rust
fn step_cohort_frame(
    &mut self,
    cf: Box<CohortFrame<W>>,
    tokens: &dyn WpdaTokenSource,
) -> Vec<Frame<W>>
```

L3.2 body: always materialize_cohort_to_frames → per-cursor step.

**Refactor `step_fanout` (line 7039) drain loop:**
```rust
for frame in drained {
    match frame {
        Frame::Concrete(cursor) => { /* existing 7048-7101 logic */ }
        Frame::Cohort(cf) => {
            let produced = self.step_cohort_frame(cf, tokens);
            new_cursors.extend(produced);
        }
    }
}
```

### Test gate
Gauntlet 4058/0 (no cohort frames constructed → pure no-op behaviorally).

### LoC estimate
+80 lines.

### Revert
Single commit.

---

## L3.3 — Action divergence classifier

### Goal
`DivergenceClass::classify(&WpdaStepAction<W>) -> DivergenceClass`. Defines criterion used by L3.4 to decide bulk-apply vs materialize.

**Conservative L3.3 classify (recommended):**
- ObsInvariant: `Advance`, `Accept`, `Error`, `Idle`
- ObsDivergent: everything else (anything carrying weight: W, anything fork-arm, anything pop)

### Code transformations

**Edit `cohort_lazy.rs`:** Add `impl DivergenceClass { pub fn classify<W>(action: &WpdaStepAction<W>) -> DivergenceClass { ... } }`.

### Test gate
Compile + unit test. No gauntlet change.

### LoC estimate
+60 lines.

### Revert
Single commit.

---

## L3.4 — ObsInvariant fast path

### Goal
Real memory win lands here. `step_cohort_frame` consults `classify` and for ObsInvariant actions mutates `shell` in-place, leaving `members` untouched.

### Approach

Inside `step_cohort_frame` after dispatch-result early-return:
1. Synthesize representative inner_state.
2. Call engine.step.
3. Classify action.
4. Branch: ObsInvariant → apply_obs_invariant_to_shell; ObsDivergent → fall through to L3.2's materialize path.

### Code transformations

**`cohort_lazy.rs`:** Add `pub fn apply_obs_invariant_to_shell(...) -> Result<(), WpdaStepAction<W>>`.

**`wpda_walker.rs::step_cohort_frame`:** Replace L3.2 body with classifier dispatch.

### Test gate
Gauntlet 6169/0; Welch's-t STRICT-WIN or NEUTRAL chain_50/100/200/1000.

### LoC estimate
+150 lines.

### Revert
Single commit.

---

## L3.5 — DispatchResolved broadcast (`fan_out_cohort`)

### Goal
When cohort's queued sub-parse completes, broadcast result to all members in one shot.

### Approach

Add `WpdaWalker::fan_out_cohort(cf, tokens) -> Vec<Frame<W>>`:
1. Read `cf.dispatch_result`.
2. Cartesian product `cf.members × dispatch_result.worker_snapshots` → for each pair: materialize cursor + apply `revive_cohort_member_with_snapshot`.
3. Wrap revived cursors in `Frame::Concrete`.

Populate `cf.dispatch_result` from H12 cache lazily inside `step_cohort_frame`.

### Test gate
Gauntlet 6169/0 + Welch neutral. Chain_10000 should reach ≥ 2× baseline OOM step count.

### LoC estimate
+120 lines.

### Revert
Single commit.

---

## L3.6 — Forced materialization sites

### Goal
Per design doc §3.6, four sites must force-materialize cohort frames before per-cursor logic:
1. Fork producing children with per-member field mutations (handled L3.4 fallback)
2. Pop with weight-dependent body (handled L3.4 fallback)
3. `merge_equivalent_cursors` (line 7481): materialize Cohort frames at entry
4. EOI (`resolve_at_end_of_input` line 3372): materialize all cohorts

### Code transformations

Insert at top of `merge_equivalent_cursors`, `resolve_at_end_of_input`, `commit_winner`, `maybe_prune_frontier`:
```rust
let mut materialized: Vec<Frame<W>> = Vec::with_capacity(self.branch_cursors.len());
for frame in std::mem::take(&mut self.branch_cursors) {
    match frame {
        Frame::Concrete(c) => materialized.push(Frame::Concrete(c)),
        Frame::Cohort(cf) => {
            materialized.extend(crate::cohort_lazy::materialize_cohort_to_frames(*cf));
        }
    }
}
self.branch_cursors = materialized;
```

### Test gate
Gauntlet 6169/0. Chain_10000 reaches ≥ 2× baseline-OOM-step under 16 GB.

### LoC estimate
+50 lines.

### Revert
Single commit.

---

## Sequencing summary

```
L3.1 (mechanical Frame<W> swap)              [~200 LoC, gauntlet 4058/0]
  └─ L3.2 (step_cohort_frame stub)           [~80 LoC,  gauntlet 4058/0]
       ├─ L3.3 (classifier)                  [~60 LoC,  unit tests]
       │    └─ L3.4 (ObsInvariant fast path) [~150 LoC, gauntlet 6169/0 + welch neutral]
       │         └─ L3.5 (DispatchResolved)  [~120 LoC, gauntlet 6169/0 + welch neutral]
       └─ L3.6 (forced materialization)      [~50 LoC, gauntlet 6169/0 + chain_10000 ≥ 2× baseline]
```

## Memory expectation

chain_10000 should reach 6-12 GB peak RSS after L3.4+L3.6 (vs 24 GB today).
