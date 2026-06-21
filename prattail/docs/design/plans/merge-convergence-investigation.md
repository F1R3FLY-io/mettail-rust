# `merge_equivalent_cursors` convergence investigation — 2026-05-23

**HEAD:** `ff506dc` (post-Phase F.13 Stage 2.3.7 + #117 + #112-falsification).
**Trigger:** `test_left_assoc_chain_10000` OOMs at systemd `MemoryMax=16G`
after 64 min (was 31 GB before Stage 2.3.x). The `im::OrdSet` →
`FxHashSet` swap (uncommitted; saved in working tree) halved memory
but the asymptotic remains O(N²–N³).

This document collects four agent reports for review:

- **Explore Agent 1** — `merge_equivalent_cursors` mechanism survey
- **Explore Agent 2** — `BranchCursor` lifecycle trace
- **Explore Agent 3** — ConfigKey per-field essentiality + theory
- **Plan Agent** — implementation plan (Stages A/B/C/D)

The four reports converged on three leads. Numbered findings at end.

---

## Explore Agent 1 — `merge_equivalent_cursors` mechanism

### 1.1 Where it lives

| Item | File:line |
|------|-----------|
| Function definition | `prattail/src/wpda_walker.rs:7328` (`fn merge_equivalent_cursors(&mut self)`) |
| Single call site | `prattail/src/wpda_walker.rs:7116` (end of `step_fanout`) |
| ConfigKey struct | `prattail/src/wpda_walker.rs:1697-1800` |
| Per-axis diagnostic | `prattail/src/wpda_walker.rs:7238-7325` (`sample_merge_misses`) |
| Walker-stats counters | `prattail/src/walker_stats.rs:139-170` |

### 1.2 ConfigKey fields (11 total, history)

| # | Field | Line | Added in | Purpose |
|---|-------|------|----------|---------|
| 1 | `state` | 1701 | Stage 3.5b (`2026-05-01`) | WpdaState discrim |
| 2 | `node` | 1704 | Stage 3.5b | GSS tip |
| 3 | `pos` | 1706 | Stage 3.5b | input pos |
| 4 | `incoming_edge: Option<GssEdgeId>` | 1718 | Stage 3.12.6 (`2026-05-02`) | predecessor edge identity |
| 5 | `collection_depth` | 1737 | Phase 4 #5b (`2026-05-12`) | open collection scopes |
| 6 | `cohort_origin: Option<DispatchKey>` | 1749 | F.13 H12 Stage 1.5.3R-c (`2026-05-21`) | cohort-revive vs per-cursor |
| 7 | `sppf_top: Option<SppfId>` | 1768 | F.13 H12 Alt#1 (`2026-05-21`) | GLL descriptor `w` |
| 8 | `lex_alt_idx: u16` | 1791 | F.13 Stage 2.0 (`2026-05-22`) | lex-Fork branch |
| 9 | `weight_src_idx: u16` | 1792 | F.13 Stage 2.0 | weight provenance src |
| 10 | `weight_rule_idx: u16` | 1793 | F.13 Stage 2.0 | weight provenance rule |
| 11 | `lex_fork_stamp: Option<LexForkStamp>` | 1799 | F.13 Stage 2.1 (`2026-05-22`) | cursor-layer lex provenance |

**Trajectory:** 3 → 4 → 5 → 6 → 7 → 11. **Every recent change ADDED a
discriminator** to fix over-merging bugs. None removed.

### 1.3 Merge predicate

Strict structural ConfigKey equality via
`HashMap<ConfigKey, usize>::entry(key)`. No relaxation. On collapse,
weights are `plus_ref`'d; the cursor with strict lex-min weight (or
lower source_priority on tie) survives. **Loser's `visited_dispatch` /
`visited_recovery` sets are DROPPED**, not unioned.

### 1.4 Diagnostic counters (`walker-stats` feature)

| Counter | Line | What |
|---------|------|------|
| `merge_attempts_total` | walker.rs:7335 | input cursor count per merge |
| `merge_collapses_total` | walker.rs:7399 | Occupied hits (= cursors collapsed) |
| `cursors_dropped_via_merge` | walker.rs:7400 | sink |
| `merge_miss_pairs_considered_total` | stats.rs:140 | per-step sampled pairs (≤10) |
| `merge_miss_state_diff_total` | stats.rs:142 | sole-cause `state` |
| `merge_miss_node_diff_total` | stats.rs:144 | sole-cause `node` |
| `merge_miss_edge_diff_total` | stats.rs:146 | sole-cause `incoming_edge` |
| `merge_miss_depth_diff_total` | stats.rs:148 | sole-cause `collection_depth` |
| `merge_miss_multi_diff_total` | stats.rs:150 | ≥2 axes differ |
| `merge_miss_pairs_edge_kind_equivalent` | stats.rs:169 | H13: drop `edge` entirely |

**KEY GAP** (per Explore 1's audit): the sole-cause counters cover only
the **original 4 axes** (state, node, edge, depth) per the comment at
walker.rs:7222-7225. The **7 newer fields** (`cohort_origin`, `sppf_top`,
`lex_alt_idx`, `weight_src_idx`, `weight_rule_idx`, `lex_fork_stamp`)
land in `merge_miss_multi_diff_total` regardless of which one truly
differs. The reported "97.5% multi-diff in chain_50" is **uninterpretable**
— we don't know which discriminator dominates.

---

## Explore Agent 2 — BranchCursor lifecycle in left-assoc chain

### 2.1 Test code

- `left_assoc_chain(N)` at `languages/tests/trampoline_tests.rs:48-57`
  produces `"1 + 1 + ... + 1"` (N elements).
- `right_assoc_chain(N)` at lines 35-45 produces `"2 ^ 2 ^ ... ^ 2"`.
- `test_left_assoc_chain_10000` at lines 175-180; `test_right_assoc_chain_10000`
  at lines 161-166.
- Grammar in `languages/src/calculator.rs:203`: `AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold` (left-assoc, fold).

### 2.2 Walker entry

`Int::parse_structured` → codegen `parse_Int_via_wpda` → `WpdaWalker::run_to_end_of_input`
at `prattail/src/wpda_walker.rs:3106`. Driver loop is `step_fanout` at
`wpda_walker.rs:6988`.

**`walker-stats` is OFF by default** (`prattail/Cargo.toml:40`:
`walker-stats = []`). To enable: rebuild with
`--features prattail/walker-stats` + run with
`PRATTAIL_WALKER_STATS=1`.

### 2.3 Cursor sources

- **Seed** (1 per parse): `BranchCursor { ... }` literal at walker.rs:2911, 4571, 7795.
- **Fork constructors** in `apply_action_to_cursor`:
  - `BranchCursor::fork_child(...)` at walker.rs:1617 — called from ~11 sites (6248, 6283, 6335, 6370, 6424, 6475, 6534, 6594, 6636, 6680).
  - Inline `BranchCursor { ... }` literals at 10 Fork-arm sites (5287, 5383, 5453, 5516, 5612, 5687, 5763, 5899, 6015, 6156).
  - `allocate_fork_push_child(...)` at walker.rs:9298 (uses literal at 9418).
- `BranchCursor::clone` (walker.rs:1450) — total clone post ι Phase 1; per-field still does O(depth) for `incoming_edge_stack: Vec<GssEdgeId>` (no Arc wrap; H2 rejected at baseline).

### 2.4 Merge schedule

Once per `step_fanout` call at walker.rs:7116, AFTER cursor advance
(6996-7051), AFTER beam pruning (`maybe_prune_frontier` at 7102), AFTER
cohort drain (7058-7099). Standard WPDS semantics.

### 2.5 Ideal vs measured (chain_50 right-assoc `^`, prior memory)

| Metric | Ideal (Tomita/GLL) | Measured |
|--------|--------------------|----------|
| Cursors per step | O(1) | **1355.73** (avg) |
| Peak cursors | O(1) | **4012** (pre-merge) |
| `apply_action_to_cursor` calls | O(N) = 50 | **2,036,307** (= 40,726× ideal) |
| Cursors created via Fork | O(N) | **1,502,702** |
| Cursors dropped via merge | O(N) | **805,570** (28.3% collapse) |
| Cross-cat-projection Forks | 0 (no cross-cat in this test) | **1,543,396** |
| Wall-time | ms | **17.28 s** |

**The cross-cat-projection Fork count is the smoking gun.** Even in a
pure `^` arithmetic chain with no cross-cat operations, 1.5 M
cross-cat-projection Forks fire — these are the cohort-fanout cursors
that should have been collapsed by H12 / now Stage 2.3.x.

For chain_10000 the same scaling extrapolates to ~10¹⁰ apply_action
calls and ~10⁹ cursors at peak. Hence the 16-31 GB RSS.

---

## Explore Agent 3 — ConfigKey per-field essentiality

For **pure left-assoc chains** (`1+1+...+1`), per-field correctness audit:

### Strictly essential

| Field | Why essential |
|-------|---------------|
| `state` | WpdaState discriminates Pre/PostReduce, PrefixDispatch vs InfixLoop |
| `node` | GSS tip identity — required by WPDS configuration semantics |
| `pos` | input position — different pos = different future |

### Operationally essential, but candidates for **relaxation**

| Field | Why discriminating | Relaxation idea |
|-------|--------------------|-----------------|
| `incoming_edge: Option<GssEdgeId>` | Each Push allocates a fresh `GssEdgeId`. Chain of length N → N distinct edge IDs at same (state, node, pos). **Primary driver of 1355 cursors/step.** | Replace with `(predecessor_node, EdgeKind)` projection. Cursors that pushed *structurally identical* edges from same predecessor merge. Pop semantics preserved (cursor's `incoming_edge_stack` stays). |
| `sppf_top: Option<SppfId>` | Each cursor builds distinct Symbols (different `hi_pos` at each reduce). | Symbol-dedup at `sppf.rs:170-200` already collapses `(nt, lo, hi)` structurally. For single deterministic parse the tips would converge IF cursors merged on `incoming_edge` first. **Closing the `incoming_edge` lead should auto-close this.** |
| `cohort_origin: Option<DispatchKey>` | Cohort-revives bucket separately for `-3!` semantics. | **None in pure-arithmetic chains** (no cross-cat dispatch). Falsifiable: assert `cohort_origin.is_none()` throughout chain_10000. If true, omitting is no-op. |

### Strictly redundant or weakly motivated in pure left-assoc

| Field | Vacuous in chain_10000? | Removal verdict |
|-------|--------------------------|-----------------|
| `collection_depth` | Yes (no collections in `Int+Int`). Always 0. | Safe to omit when known zero (grammar-static elision). |
| `lex_alt_idx` | Yes (one tokenization of `1` and `+`). | Constant 0 — omitting is no-op for chain_10000. |
| `weight_src_idx` | Yes (Int_idx constant). | Same — constant. |
| `weight_rule_idx` | Differs per cursor when multiple infix rules at same precedence (mixed `+`/`-`). In `1+1+...+1` only one rule (`+`). | Constant when single-rule. |
| `lex_fork_stamp` | None (no lex-Fork ambiguity in `1+1+...`). | Constant None — omitting is no-op. |

### H13 vs Lead #1: critical distinction

**H13 was rejected at the 60% gate (chain_50 measured 0.6% would-merge).**
But H13 dropped `incoming_edge` *entirely* (kind-only matching). The
right metric is `(pred, EdgeKind)`-equivalence — strictly finer than
H13's kind-only, strictly coarser than full GssEdgeId. **The right
number has never been measured.**

---

## Three converging leads

1. **EdgeKind-class incoming_edge.** Replace `ConfigKey.incoming_edge:
   Option<GssEdgeId>` with `Option<GssEdgeIdOrClass>` where:
   - `Generic`-kinded edges fall back to GssEdgeId identity (preserves
     Stage 3.12.6's pop semantics for un-classified edges).
   - Classified edges use `(pred_node, EdgeKind)` — same semantic edge
     from same predecessor merges. The cursor's `incoming_edge_stack`
     keeps the original `GssEdgeId` for pop. Only the KEY changes.

2. **Extend `sample_merge_misses` to ALL 11 axes.** Add per-field
   sole-cause counters + the `pred_edge_class_equivalent` counter that
   measures Lead #1's expected coverage BEFORE we commit to it. Risk-
   free; produces the data needed for the Stage B decision.

3. **Grammar-static field elision (`ConfigKeyProfile`).** At
   macro-codegen time, emit `const HAS_LEX_FORK: bool`,
   `HAS_CROSS_CAT_DISPATCH: bool`, `HAS_COLLECTIONS: bool`. Merge code
   branches into narrowed ConfigKey omitting proven-vacuous fields.
   Calculator's pure-arithmetic chains hit narrow path; `-3!` and
   rhocalc hit wide path. **Complementary to Lead #1, not redundant.**

---

## Plan Agent — Implementation Plan (Stages A/B/C/D)

### Stage A (risk-free, 2-3 h): extend `sample_merge_misses`

**Edits:**

1. `prattail/src/walker_stats.rs:139-170` — add 7 new sole-cause
   counters + `merge_miss_pairs_pred_edge_class_equivalent_total` +
   `merge_miss_sole_cause_by_field: [u64; 11]`. ~75 LoC.
2. `prattail/src/wpda_walker.rs:7238-7325` — rewrite per-pair body:
   ```
   diff_count = sum of 11 bools
   if diff_count == 1: increment sole-cause[that field]
   if diff_count >= 2: increment multi + per-axis "participating" tallies
   if only incoming_edge differs: also compute (pred_a, kind_a) vs (pred_b, kind_b);
     if equal, increment pred_edge_class_equivalent counter
   ```
   ~60 LoC, all `#[cfg(feature="walker-stats")]`.
3. `walker_stats.rs:240-289` — extend Display impl. ~30 LoC.

**Capture command:**
```bash
PRATTAIL_WALKER_STATS=1 cargo test --release --features prattail/walker-stats \
  -p languages --test trampoline_tests test_left_assoc_chain_200 -- --nocapture
```
(chain_200 first as proxy; chain_10000 OOMs at baseline.)

**Decision criterion for Stage B:**
- If `merge_miss_pairs_pred_edge_class_equivalent / merge_miss_pairs_considered_total > 40%`
  AND `(sole_cause[incoming_edge] + multi_participating[incoming_edge]) > 60%`:
  ship Lead #1.
- Else, re-rank by dominant sole-cause field and pick a different surgical relaxation.

### Stage B (conditional on Stage A, 6-8 h): implement Lead #1

**Edits:**

1. `prattail/src/wpda_walker.rs:1690` — new enum
   ```rust
   pub enum GssEdgeIdOrClass {
       Identity(GssEdgeId),                  // for Generic-kinded edges
       Class(GssNodeId, EdgeKind),           // for classified edges
   }
   ```
   `#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]`. ~15 LoC.

2. `prattail/src/wpda_walker.rs:1719` — change ConfigKey field:
   ```rust
   pub incoming_edge_class: Option<GssEdgeIdOrClass>,
   ```
   Update docstring with WPDS justification.

3. `prattail/src/wpda_walker.rs:7344-7349` — key build:
   ```rust
   incoming_edge_class: cursor.incoming_edge_stack.last().copied().map(|eid| {
       let kind = self.gss.edge_kind(eid).unwrap_or(EdgeKind::Generic);
       match kind {
           EdgeKind::Generic => GssEdgeIdOrClass::Identity(eid),
           k => GssEdgeIdOrClass::Class(
               self.gss.edge_target(eid).expect("valid edge"),
               k,
           ),
       }
   }),
   ```

**Pop-semantics invariant (CRITICAL — no change to cursor state):** the
per-cursor `cursor.incoming_edge_stack: Vec<GssEdgeId>` STAYS unchanged.
When popping, `cursor_gss_pop_via_edge` (walker.rs:~4752) consults
`incoming_edge_stack.last()` and routes via the exact `GssEdgeId`. Only
the merge BUCKETING key changes. Two cursors with merge-equivalent
`(pred, kind)`: one wins (loser's stack dropped — already current
behavior at walker.rs:7330). Survivor's edge id will pop to a
predecessor whose target matches by construction, so WPDS semantics
preserved.

**Correctness preservation:**

- `-3!` test (the reason Stage 2.0/2.1 added `lex_alt_idx`/etc.):
  those 4 fields STAY in ConfigKey. Lead #1 touches `incoming_edge`
  only. The `-3!` falsification was about `lex_alt_idx=0` vs
  `lex_alt_idx=2` reaching identical `(state, node, pos, edge, depth,
  sppf_top)` — orthogonal to the edge projection.
- rhocalc / lambda binders: `EdgeKind::Generic` retains identity-
  strict comparison via `Identity(eid)`. Two `Generic`-kinded edges
  from the same predecessor were previously assumed divergent (gss.rs:393).
  Falling back to identity preserves Stage 3.12.6's divergence guard.

### Stage C (3-4 h): Welch's t-test verification

Per `[[feedback-optimization-t-test]]`:

| Test | Baseline | Treatment | Gate |
|------|----------|-----------|------|
| chain_50 | HEAD `ff506dc` N=15 | post-Stage-B N=15 | p<0.05 AND treatment < baseline |
| chain_100 | same | same | same |
| chain_200 | same | same | same |
| chain_1000 | same | same | same |
| chain_10000 | OOMs at baseline | post-Stage-B | operational: completes <60s with <500 MB peak RSS |

Plus narrow gauntlet: `prattail lib 4059 + gen_calc_op 1331 + gen_rhocalc_op 532 + edge_case 229 + wpda_parity_calc 16 + wpda_parity_lambda 2 + recovery_cohort 5 = 6174/0`.

### Stage D (contingent, 8-12 h): Lead #3 grammar-static elision

Only if Stage B alone doesn't clear the chain_10000 operational gate.

---

## Risk register

| Risk | Probability | Mitigation |
|------|-------------|------------|
| Breaks `-3!` | LOW | `lex_alt_idx`/`weight_src_idx`/`weight_rule_idx`/`lex_fork_stamp` STAY. Verify with explicit test. |
| Breaks rhocalc (binders + cross-cat heavy) | MEDIUM | `Generic`-fallback Identity preserves divergence guard. Update `from_symbol` mapping (gss.rs:494) to keep `ReturnFrame` on Identity arm. Verify with `gen_rhocalc_op 532/0`. |
| Lambda-calc binder shadowing | LOW | Lambda binder edges → `Generic` → Identity arm → no merge change. |
| Cohort revive cursors merge wrong | LOW | `cohort_origin` STAYS in ConfigKey. Lead #1 orthogonal. |
| H13's 0.6% number applies | NONE | H13 measured kind-only. Lead #1 is `(pred, kind)` — strictly finer, expected coverage TBD by Stage A's `pred_edge_class_equivalent` counter. |

---

## Effort estimate

| Stage | Hours |
|-------|------:|
| A | 2-3 |
| B | 6-8 |
| C | 3-4 |
| D (contingent) | 8-12 |
| **A+B+C** | **11-15** |
| **A+B+C+D** | **19-27** |

---

## Critical files

| File | LoC change |
|------|-----------:|
| `prattail/src/walker_stats.rs` | ~100 (new counters + Display) |
| `prattail/src/wpda_walker.rs` | ~90 (ConfigKey enum + sample_merge_misses + merge key build) |
| `prattail/src/gss.rs` | 0 (already exposes `edge_target`, `edge_kind`) |
| `languages/tests/trampoline_tests.rs` | 0 (tests already exist) |
| `prattail/src/automata/lex_weight.rs` | 0 |

---

## Open question (for user)

Is **Lead #3 (grammar-static `ConfigKeyProfile`)** worth implementing
as a Stage D, or is Lead #1 sufficient on its own?

Plan agent's prior: Lead #1 hypothesized sufficient — the 4012-cursor
peak is driven by `GssEdgeId` proliferation, not by the 7-narrow-fields
collision rate. Lead #3 saves HashMap key bytes per cursor + improves
hash distribution for Calculator's pure-arithmetic chains, but is
strictly additive after Lead #1.

**Decision needed:** approve Stages A-C as a unit? Defer D pending B's
results?
