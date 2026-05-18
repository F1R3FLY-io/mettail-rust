# Cursor-explosion diagnosis — rhocalc grammar (2026-05-18)

## Hypothesis selection

Plan: `~/.claude/plans/replicated-conjuring-turtle.md`. Three candidate
hypotheses:

- **H1**: lex-Fork explosion at parse time from keyword-vs-Ident ambiguity.
- **H2**: SPPF/builder desync at cast paths.
- **H3**: `ConfigKey.incoming_edge` over-strict.

**Verdict: H1′** — a refinement of H1. The cursor explosion is NOT at
parse-time lex-Fork (cursor count there is bounded at ~25, oscillating).
The explosion is in **recovery dispatch**, where a cursor with
`recovery_depth=1` cycles through every category's PrefixDispatch
exactly once, then (presumably) cycles indefinitely.

## Empirical evidence

Method: temporary `eprintln!` at `step_fanout` entry in
`prattail/src/wpda_walker.rs:6085` printing cursor count + per-cursor
ConfigKey breakdown. Run on the shortest failing test
(`mettail-languages::rhocalc_tests native_ops::boolean::and_tt`
parsing `{true and true}`, 14 bytes).

Captured to `/tmp/cursor-trace2.log` — 1662 lines covering ~140
fanout iterations in ~10 seconds (~14/s, ~70ms per iteration).

### Phase 1 — productive cat-fanout (iter 1, count=5 → 25)

Initial 30 iterations explore the legitimate cross-cat parse space at
position 1 (right after `{`):

```
step=0 count=5 state=AmbiguityFanout { branches: [2, 3, 4, 5, 6] }
  [C0] node=2 state=CrossCatDelegate { source_src_idx: 5 }
  [C1] node=3 state=CrossCatDelegate { source_src_idx: 4 }
  [C2] node=4 state=CrossCatDelegate { source_src_idx: 3 }
  [C3] node=5 state=CrossCatDelegate { source_src_idx: 2 }
  [C4] node=6 state=CrossCatDelegate { source_src_idx: 11 }
```

All 5 cursors at the same `pos=1`, differ only in `source_src_idx` (one
cat per delegate). Cursor count peaks at ~25 around iter 30, then
decreases as `merge_equivalent_cursors` collapses redundant paths and
many cats fail-out.

### Phase 2 — single Accepted cursor (iter ~120, count=1)

Around iter ~120, the parse REACHES an `Accepted` cursor with a valid
SPPF root:

```
step=0 count=1 state=AmbiguityFanout { branches: [4294967295] }
  [C0] node=4294967295 pos=5 state=Accepted
       weight=src=1 rule=0 ops_len=0 sppf_stack_top=Some(32)
       visited_dispatch_len=5 recovery_depth=0
```

But the WALKER state stays in `AmbiguityFanout`, not `Accepted` — the
walker continues iterating despite a valid parse being reached. (This
is by design for ambiguity-preserving parsing: multiple Accepted
cursors may be possible.)

### Phase 3 — recovery-dispatch cycle (iter ~125-140, count=1, BUG)

The Accepted cursor is REPLACED by a recovery cursor at the start of
the next iter:

```
step=0 count=1 state=AmbiguityFanout { branches: [0] }
  [C0] node=0 pos=1 state=PrefixDispatch { pos: 0, cur_bp: 0 }
       weight=src=2 rule=2 ops_len=1 recovery_depth=1
       sppf_stack_top=None visited_dispatch_len=0
```

The cursor's state stays at `PrefixDispatch{pos:0, cur_bp:0}` for every
subsequent iteration, but `weight.src` cycles through ALL 11 category
source indices in priority order:

```
iter N+0:  src=2
iter N+1:  src=3
iter N+2:  src=4
iter N+3:  src=5
iter N+4:  src=6
iter N+5:  src=7
iter N+6:  src=11
iter N+7:  src=12
iter N+8:  src=8
iter N+9:  src=9
iter N+10: src=10   ← test killed by timeout shortly after
```

Critical observations:
- **`visited_dispatch.len() = 0` throughout the cycle.** No
  defense-in-depth entries accumulating.
- **`cursor.inner_state` is invariant** at `PrefixDispatch{pos:0, cur_bp:0}`.
- **Only `weight.src` changes per iter** — `(primary, rule)` constant
  at `(TropicalWeight(1.4), 2)`; only the `src` cat-idx field cycles.
- **Progress detection at `wpda_walker.rs:2733-2744` is fooled**: the
  progress fingerprint includes `c.weight.clone()` and the weight DOES
  change between iters (via `src` cat-idx), so `progress_made=true`
  every iter. The loop never exits.

### Root cause

The cycling Fork emitted by the engine at this configuration has N
branches, each carrying a different cat in `weight.src`. The branches
are NOT recovery-tagged BuilderDeltas (so the recovery defense at
`wpda_walker.rs:4422-4470` doesn't fire), and the new_state of each
branch is NOT `CrossCatDelegate` (so the B14 C5 per-branch gate at
`wpda_walker.rs:4496-4504` does not insert into `visited_dispatch`
either — the gate's insertion at `wpda_walker.rs:5884-5888` is
filtered by `child_came_from_cross_cat[idx]`).

Net effect: a Fork emits N alternatives at `(pos=1, cat_src=PARENT,
cur_bp=0)` per iteration. Each iteration picks one alternative
(causing a weight.src change). The visited_dispatch set never grows
because the insertion filter excludes non-projection branches.
Result: live-lock with no upper bound.

## Why H2 and H3 are NOT the dominant cause

- **H2 (SPPF/builder desync)**: would manifest as cursors with
  legitimate parses being fragmented into distinct ConfigKey
  buckets. The trace shows the parse DOES reach Accepted (Phase 2);
  the bug is post-Accepted recovery, not parse-time merge miss.
- **H3 (`incoming_edge` over-strict)**: in Phase 1, the 5 initial
  cursors share `pos=1` but have distinct `node` (different cross-cat
  delegate paths), so they correctly don't merge. The cycle in
  Phase 3 has only 1 cursor — `incoming_edge` discrimination is not
  the bottleneck.

## Targeted fix (H1 extension per plan §"If H1 wins")

Extend `visited_dispatch` insertion at `prattail/src/wpda_walker.rs:5884-5888`
from CrossCatDelegate-branch-only to ALL non-recovery Fork-arm children.
After the first cycle iteration inserts `(pos=1, cat_src=PARENT, cur_bp=0)`
into `visited_dispatch`, the cycle defense at `wpda_walker.rs:4502-4525`
(or the per-branch gate at 4546-4558 extended similarly) catches the
next iteration's re-entry and emits `WpdaState::Error` to abort the
runaway cursor.

Mandate compatibility: per `feedback_never_disambiguate_early.md`,
ruling out by EVIDENCE is correct. Re-entering an identical dispatch
config is the GLL descriptor-uniqueness termination argument
(Scott-Johnstone 2010 §3) — not a weight-based pruning.

## Outcome (2026-05-18, post-fix)

Two principled changes applied in `prattail/src/wpda_walker.rs`:

### Fix 1: drop weight from `run_to_end_of_input` progress fingerprint

The pre-fix fingerprint at line 2718-2731 included `c.weight.clone()`.
The recovery cycle's cursor had `weight.primary` constant at
`TropicalWeight(1.4)` but `weight.src_idx` cycling through cat-ids
2,3,4,5,6,7,11,12,8,9,10. Per `PartialEq`-derived equality on
`LexicographicWeight`, the cycling fingerprint differed → progress
detector reported `progress_made = true` every iteration → loop never
exited.

The fix replaces `c.weight.clone()` in the fingerprint with
`c.sppf_stack.len()`. Rationale:

- Productive parse steps change at least one structural axis
  (node, pos, inner_state, recovery_deltas.len, sppf_stack.len). The
  pre-fix fingerprint included only the first four structural axes;
  weight was used to catch "weight-only refinement" progress (e.g.,
  cost accumulation during recovery — Stage 3.12 Fix 3a, 2026-05-02).
- The recovery cycle's weight refinement is **tiebreaker-only**
  (`src_idx`/`rule_idx` cycling), not real cost progress. The new
  fingerprint loses sensitivity to these tiebreaker mutations,
  recovering the fixed-point detection semantics.
- `sppf_stack.len()` is added to preserve SPPF-interning progress
  detection when state/node/pos stay constant but reduces fire (a
  legitimate progress mode that weight-only refinement may have
  signaled).

### Fix 2: unconditional `visited_dispatch.insert` for non-recovery Fork children

At `prattail/src/wpda_walker.rs:5877-5890`, the pre-fix code inserted
the parent's `(pos, cat_src, cur_bp)` only into children whose
originating branch was CrossCatDelegate. The H1 plan called for
extending this to all branch types, per the GLL descriptor-
uniqueness argument (Scott & Johnstone 2010 §3). The post-fix
unconditional insertion populates `visited_dispatch` for ALL
non-recovery Fork-arm children, so future re-entry to the same
dispatch config can be caught by the per-branch gate at line 4546
(CrossCatDelegate branches only — the pre-fix gate was retained
intentionally to preserve the `nested_fork_resolves_to_lex_min_grandchild`
synthetic test invariant; extending the gate too dropped legitimate
nested-Fork branches).

### Verification

- `cargo test --lib -p mettail-prattail`: **4047/4047 ✓**
- `cargo test --test gen_calculator_op -p mettail-languages`:
  **1321 passed / 10 pre-existing R1 failures** (no regression).
- `cargo test --test gen_rhocalc_op -p mettail-languages`:
  **532/532 ✓**.
- Individual rhocalc `native_ops::boolean::and_tt` test was traced
  empirically to confirm the fixed-point detector now fires twice
  during the parse (`/tmp/cursor-trace6.log:67, /tmp/cursor-trace6.log:135`).

### What this fix does NOT address

The empirical trace also revealed that `parse_term` for these inputs
invokes `run_to_end_of_input` THIRTEEN times per call (likely via
the macro-generated `parse_<Cat>_via_wpda` chain, where parsing the
top-level `Proc` recursively invokes sub-parses for each candidate
category). The first 2 sub-parses run ~67 step_fanout iterations
each and now exit via FIXPOINT (Fix 1 effective); the remaining 11
sub-parses each run only 1 step_fanout and exit via `state.is_terminal()`.

The remaining ~120s+ test wall-clock is dominated by the outer
13-sub-parse loop plus subsequent `run_ascent` evaluation —
neither of which is in the walker's `step_fanout` cursor-management
path. That hang is a separate pathology (likely in
`parse_preserving_vars` / `decompose_into_cek` / `run_ascent` flow
for cross-cat rhocalc cast paths), outside this principled walker
fix's scope.

The walker fix DOES reduce per-parse memory consumption (each
sub-parse now terminates cleanly via FIXPOINT instead of looping
through the full `MAX_STEPS = 1_000_000` budget). Under `cargo
nextest run --workspace`, this should reduce peak-RSS pressure
on the parallel test execution even where individual rhocalc tests
still exceed their previous wall-clock budget.
