# Cohort Lazy Materialization — Multi-Week Implementation Plan

**Status:** Plan agent design, 2026-05-25. Pending user review.

**Tip:** `c280238` (post Stage 3.1a accepted) on `feature/wfst-architecture`.

**Cross-references:**
- `prattail/src/wpda_walker.rs:1234` `BranchCursor<W>`; `:1698` `ConfigKey`; `:7039` `step_fanout`; `:7481` `merge_equivalent_cursors`; `:9460` `allocate_fork_push_child`; `:9662` `revive_cohort_member_with_snapshot`.
- `prattail/src/dispatch_cohort.rs` — H12 cohort cache (single-snapshot revive today).
- `prattail/docs/design/plans/chain-10000-ceiling-lift.md` — falsified Stages 3.1b / 3.2.
- `prattail/docs/design/plans/phase-f13-algorithmic-cross-cat-cohort.md` — H12 algorithmic motivation; the 97.5% multi-axis divergence + 88% cross-cat branches at chain_50.
- `prattail/docs/design/plans/phase-f13-stage-1-5-4-approach-p-realize-time-fanout.md` — earlier Approach P sketch (deferred-fanout via SPPF templates).
- `~/.claude/projects/.../memory/2026-05-24-chain_10000-heaptrack-architectural-ceiling.md` — heaptrack on chain_1000 (BranchCursor::clone = 49% of peak heap).
- `~/.claude/projects/.../memory/2026-05-25-stages-3.1a-3.1b-3.2-ceiling-lift-empirical.md` — empirical rejections.

---

## 1. Mathematical Foundation — Correctness Criterion

### 1.1 The current configuration descriptor

Today, two cursors are considered "equivalent" for the purpose of `merge_equivalent_cursors` (`wpda_walker.rs:7481`) iff they share a 12-tuple ConfigKey:
```
K = (state, node, pos, incoming_edge, collection_depth, cohort_origin,
     sppf_top, lex_alt_idx, weight_src_idx, weight_rule_idx, lex_fork_stamp,
     [implicit: identical engine pure step output])
```
This is the closest-known approximation to the **GLL descriptor** `(L, u, i, w)` of Scott & Johnstone (ENTCS 253(7), 2010 §3) augmented with the WPDS stack-suffix and lex/cross-cat provenance discriminators.

The 97.5% multi-axis divergence (`phase-f13-algorithmic-cross-cat-cohort.md`) tells us that at the busiest pos-buckets, no single-axis relaxation collapses the frontier. Two cursors at the same `(pos, source_src_idx, inner_cur_bp)` dispatch site differ on `state`, `node`, `edge`, AND `sppf_top` simultaneously. **Yet they perform IDENTICAL work** for the sub-parse they are about to launch. This is the asymmetry lazy materialization exploits.

### 1.2 The cohort equivalence relation

Define two relations on cursors:

**`~_dispatch` (Tomita work-sharing).** `C₁ ~_dispatch C₂` iff
- both cursors are about to emit the same `WpdaStepAction` whose immediate effect is a `Push CategoryEntry(S) → PrefixDispatch(P, B)` (the H12-eligible cross-cat-projection arm at `allocate_fork_push_child:9473`),
- with identical `(pos = P, source_src_idx = S, inner_cur_bp = B)`,
- with engine purity of `engine.step` on `CrossCatDelegate` (per `engine_impl.rs:1387-1394`) guaranteeing the sub-parse output `(SppfId_sub, hi_pos, sub_weight_sum)` is a pure function of `(grammar, S, P, B, tokens)`.

By construction this is an equivalence relation: reflexive, symmetric, transitive over `(S, P, B)` identity.

**`~_obs` (observational divergence).** `C₁ ~_obs C₂` iff `C₁` and `C₂` agree on every component of the post-dispatch ConfigKey **except** those that the dispatch produces (i.e. `sppf_top`, `pos`, `state`, `pending_packing_weight`). Concretely:
- same `node`, `incoming_edge_stack` (the **return frame**),
- same `collection_depth`, `optional_scope_marks` shape, `binder_scope_marks` shape,
- same `cohort_origin`, `lex_alt_idx`, `weight_src_idx`, `weight_rule_idx`, `lex_fork_stamp`,
- same `visited_dispatch ⊆`, `visited_recovery ⊆` cycle-defense state at the dispatch site,
- same `recovery_deltas` journal up to the dispatch point.

The 97.5% multi-axis fact is precisely: `~_dispatch` is huge (chain_50: 1.5M cross-cat branches collapse to ~150 keys), but `~_obs` is **tiny** — almost every pair that shares `~_dispatch` differs on `~_obs`.

### 1.3 The lazy materialization correctness criterion

A cohort cursor `Ĉ_K` representing all `{C_i}_{i ∈ K}` with `C_i ~_dispatch C_j` is **observationally adequate** for the parse iff:

**(L1)** For every event the cohort cursor emits, the multiset of `(BranchCursor, action)` pairs the per-cursor baseline would have emitted at the same step is recoverable by traversing the cohort cursor's lazy representation followed by a (deferred) materialization.

**(L2)** Materialization MUST happen whenever a step would produce divergent `~_obs` futures across `{C_i}`. Specifically, if any `C_i` would emit a `CursorOutcome::ForkInto` whose children differ from `C_j`'s on any `~_obs` axis, the cohort must be split before that step is executed.

**(L3)** At end-of-input, the multiset of materialized `Accepted` cursors must be a superset (with weight-preserving ⊕) of the per-cursor baseline's `Accepted` cursors. No derivation silently dropped.

**(L4)** All `visited_dispatch` / `visited_recovery` cycle-defense state of every `{C_i}` is honored.

**(L5)** Welch's-t-gate prediction: cohort cursors that NEVER diverge on `~_obs` (the H12 happy path) save memory; cohort cursors that diverge on the very next step waste memory plus runtime. The plan must demonstrate the former dominates the workloads we care about.

---

## 2. Data Structure Design

### 2.1 What replaces `branch_cursors: Vec<BranchCursor<W>>`

```rust
enum Frame<W: SemiringRef> {
    Concrete(BranchCursor<W>),
    Cohort(Box<CohortFrame<W>>),
}

pub struct WpdaWalker<W> {
    frontier: Vec<Frame<W>>,             // replaces branch_cursors
    // ... rest unchanged
}
```

### 2.2 `CohortFrame<W>` shape

```rust
pub struct CohortFrame<W: SemiringRef> {
    shell: Arc<CohortShell<W>>,
    members: Vec<CohortMemberState<W>>,
    dispatch_result: Option<CohortDispatchResult<W>>,
}

pub struct CohortShell<W: SemiringRef> {
    // All ~_obs axes (shared, immutable after formation)
    node: GssNodeId,
    incoming_edge_stack: Arc<Vec<GssEdgeId>>,
    collection_depth: u8,
    cohort_origin: Option<DispatchKey>,
    lex_alt_idx: u16,
    weight_src_idx: u16,
    weight_rule_idx: u16,
    lex_fork_stamp: Option<LexForkStamp>,
    binder_scope_marks: Arc<Vec<(u16, Vec<String>)>>,
    optional_scope_marks: Arc<Vec<usize>>,
    sppf_collection_arena: Arc<Vec<Vec<SppfId>>>,
    visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>,
    visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>,
    recovery_depth: u8,
    dispatch_key: DispatchKey,
    sppf_stack_baseline: Arc<Vec<SppfId>>,
}

pub struct CohortMemberState<W: SemiringRef> {
    weight_at_dispatch: W,
    snapshot_idx: u8,
    pending_packing_weight: W,
    last_action_output_cat: Option<u16>,
    source_priority: u32,
}

pub struct CohortDispatchResult<W: SemiringRef> {
    sub_symbol_id: SppfId,
    hi_pos: u32,
    pos_at_dispatch: u32,
    worker_snapshots: Vec<WorkerSnapshot<W>>,
}
```

### 2.3 Per-cursor mutable field mapping

| Field | Today | Cohort lazy form |
|-------|-------|------------------|
| `recovery_deltas` | Cloned per Fork | In `shell` if all share journal; recovery Forks materialize |
| `incoming_edge_stack` | Cloned per Fork | `Arc<Vec<GssEdgeId>>` in shell; ~_obs members never differ here |
| `visited_dispatch` | Cloned per Fork | `Arc<FxHashSet>` in shell; insertion triggers materialization |
| `visited_recovery` | Cloned per Fork | Same |
| `optional_scope_marks` | Cloned per Fork | `Arc<Vec>` in shell |
| `binder_scope_marks` | Cloned per Fork | `Arc<Vec>` in shell |

### 2.4 Memory at chain_10000 peak

~225 logical cursors → ~10 CohortFrames × ~22 members each. Per-CohortFrame: ~1.8 KB (shell + members) vs today's ~70 KB (22 × 3.2 KB BranchCursor::clone) = ~40× reduction at the cohort boundary.

---

## 3. Step-Fanout / Merge / Fork Algorithms

### 3.1 step_fanout

```
for frame in drained:
    match frame {
        Frame::Concrete(c) => /* identical to today */
        Frame::Cohort(cf) => step_cohort_frame(cf, tokens)
    }
```

### 3.2 step_cohort_frame

```
match action.divergence_class() {
    ObsInvariant => apply_obs_invariant(cf, action),
    ObsDivergent => {
        let materialized = materialize_cohort(cf);
        materialized.into_iter().flat_map(per_cursor_step).collect()
    }
    DispatchResolved(sub_result) => {
        cf.dispatch_result = Some(sub_result);
        fan_out_cohort(cf)
    }
}
```

### 3.3 Fork-arm triage

- **Cross-cat-projection Fork**: build/extend CohortFrame keyed on dispatch key. Caps go from 4 → effectively unbounded.
- **Lex-alt Fork**: different `lex_alt_idx`, materialize.
- **Recovery Fork**: recovery_deltas mutate per-member, materialize.
- **OptGroup Fork**: same shell, different member-state → ideal CohortFrame case without materialization.

### 3.4 merge_equivalent_cursors

1. Merge Concrete by ConfigKey (unchanged).
2. Merge Cohorts by `(dispatch_key, shell_id)`.
3. Hybrid merge: Concrete with same `~_obs` axes as Cohort's shell → ABSORB into cohort (inverse materialization).

### 3.5 Materialization

`materialize_cohort` constructs N Concrete cursors via:
1. Arc bump shell's `Arc<Vec>` fields (O(1) per field).
2. Copy small Copy fields.
3. Per-member: synthesize weight, pending_packing_weight, etc.
4. Per-member: push dispatch SppfId via `Arc::make_mut(sppf_stack)`.

### 3.6 Forced materialization sites

- Fork producing children that mutate 6 mutable fields per-member.
- Pop whose `apply_pop_body_to_cursor` fires action depending on member-specific weight.
- Merge step needing per-member field for ConfigKey distinctness.

All other steps (Advance, ObsInvariant Push, deterministic Pop) apply in bulk to shell.

---

## 4. Ambiguity-Preservation Invariant — Proof

**Theorem.** Let `Π_per(input)` be the multiset of `Accepted` cursors at EOI under per-cursor baseline, `Π_lazy(input)` under lazy materialization. Then `Π_lazy(input) ⊇ Π_per(input)` semantic superset, weight-preserving, with multiset equality up to ⊕-reduction.

**Proof by induction on step count.**

*Base case*: both walkers start with one seed; Π identical.

*Inductive case*: assume `Π_per^k ⊆ Π_lazy^k`. For each C in `Π_per^k`:
- If C is `Frame::Concrete(C')` in lazy: pure function application identical.
- If C is member m of `Frame::Cohort(cf)`:
  - **(L2) discipline**: any per-cursor action on C that would alter m's `~_obs` axes triggers materialization BEFORE the action fires.
  - **ObsInvariant path**: by Lemma 1 (engine purity at `engine_impl.rs:1387-1394`) and Lemma 2 (Symbol-dedup at `sppf.rs:511-525`), shell-level action is correctness-identical to N independent per-cursor applications.
  - **DispatchResolved path**: broadcasts cached `(SppfId_sub, hi_pos, snapshot)` to all members; identical to existing `revive_cohort_member_with_snapshot:9662` per-member.

In merge, two members with identical post-step ConfigKey collapse via ⊕ — same behavior as per-cursor merge. Loser's `~_obs` axes preserved as multiset duplication, NOT silent drop.

**(L4) cycle-defense**: shell's `visited_*` Arc-shared at cohort formation. Member's insertion attempt that would alter shared set materializes cohort; each materialized cursor's set reconstituted from shell snapshot. No member sees a `visited_*` entry not present in its per-cursor counterpart.

**(L3) EOI**: all surviving cohorts forcibly materialized; `resolve_at_end_of_input` enumerates per-cursor as today. No ambiguity dropped before EOI because (L2) ensures divergent futures materialize before divergence.

By induction, `Π_lazy^N ⊇ Π_per^N`. ∎

**Falsifier**: any proptest gauntlet failure where a baseline derivation is missing post-lazy.

---

## 5. Migration Path — 6 Stages with Empirical Gates

### Stage L1 — Schema + Frame enum (dead-code)
**Effort:** 2-3 days. **Risk:** very low.

Add `Frame<W>`, `CohortFrame<W>`, `CohortShell<W>`, `CohortMemberState<W>` in new module `prattail/src/cohort_lazy.rs`. Convert `branch_cursors` to `Vec<Frame<W>>` where conversion is `Frame::Concrete(cursor)` everywhere. ZERO algorithmic change — the `Frame::Cohort` variant is reachable from L2 onward, but defined here as dead-code scaffold.

**Acceptance:** gauntlet 6169/0 unchanged; chain_50/100/200/1000 Welch's-t NEUTRAL.

### Stage L2 — CohortFrame formation at H12 collision sites
**Effort:** 4-5 days. **Risk:** medium.

In `allocate_fork_push_child`'s `InflightCollision` arm, build `CohortFrame` containing H12 paused members. Replace `pending_cohort: Vec<CohortMember>` with `pending_cohort_frame: Option<CohortFrame<W>>`. End-of-step drain at `step_fanout:7109` becomes "drain into one CohortFrame per dispatch_key with N members + N snapshots".

Materialization is automatic at this stage (every step falls into ObsDivergent). Memory-equivalent re-architecture; no savings yet.

**Acceptance:** gauntlet 6169/0; -3! test passes; Welch's-t chain_50/100/200/1000 NEUTRAL.

### Stage L3 — ObsInvariant fast path
**Effort:** 6-8 days. **Risk:** medium-high.

Implement `step_cohort_frame` with action-divergence classifier. Cover ObsInvariant cases: `WpdaStepAction::Advance`, `Push` not mutating per-member sppf_top, `revive_cohort_member_with_snapshot` path applied to all members in one shot. Add walker-stats counters.

**Acceptance:** gauntlet 6169/0; Welch's-t STRICT WIN or NEUTRAL. chain_10000 **operational**: reaches step count ≥ 2× baseline-OOM-step. Expected: 6-12 GB peak RSS.

### Stage L4 — Cycle-defense Arc-sharing + materialize-on-mutation
**Effort:** 3-5 days. **Risk:** medium.

Arc-wrap `visited_dispatch` and `visited_recovery` in shell. Mutation calls `cow_visited_dispatch(&mut cursor)` which materializes cohort if cohort, or `Arc::make_mut` deep-clones if concrete.

**Acceptance:** gauntlet 6169/0; chain_1000 Welch NEUTRAL. chain_10000 reaches EOI under 16 GB.

### Stage L5 — Hybrid merge (re-absorb Concrete into Cohort)
**Effort:** 4-6 days. **Risk:** medium.

In `merge_equivalent_cursors`, when `Frame::Concrete(c)` and `Frame::Cohort(cf)` share `~_obs` axes AND c's next action dispatches on cf's key, ABSORB c into cf's members.

**Acceptance:** gauntlet 6169/0; Welch chain_1000 NEUTRAL or WIN. chain_10000 reaches EOI under 8 GB.

### Stage L6 — Hardening + remove H12 caps
**Effort:** 2-3 days. **Risk:** low.

Remove `MAX_PENDING_COHORT_PER_KEY=4` and `MAX_WORKER_SNAPSHOTS_PER_KEY=4`. Replace with `MAX_COHORT_FRAME_MEMBERS = 256` (defense-in-depth). Migrate `revive_cohort_member_with_snapshot:9662` to lazy frame extension. Delete dead `pending_cohort_drain_keys` machinery.

**Acceptance:** gauntlet 6169/0; chain_10000 completes under TARGET. chain_50/100/200/1000 WIN or NEUTRAL.

### Stage gate matrix

| Stage | gauntlet | chain_50 | chain_100 | chain_200 | chain_1000 | chain_10000 |
|------:|---------:|---------:|----------:|----------:|-----------:|------------:|
| L1 | 6169/0 | NEUTRAL | NEUTRAL | NEUTRAL | NEUTRAL | 24 GB OOM |
| L2 | 6169/0 | NEUTRAL | NEUTRAL | NEUTRAL | NEUTRAL | 24 GB OOM |
| L3 | 6169/0 | ≥NEUTRAL | ≥NEUTRAL | ≥NEUTRAL | ≥NEUTRAL | 6-12 GB |
| L4 | 6169/0 | WIN | WIN | WIN | WIN | <16 GB EOI |
| L5 | 6169/0 | WIN | WIN | WIN | WIN | <8 GB EOI |
| L6 | 6169/0 | WIN | WIN | WIN | WIN | <4 GB EOI |

Failed gate → REVERT and re-plan (per `feedback_optimization_t_test` and the empirical Stage 3.1b/3.2 failures).

---

## 6. Expected Memory Reduction at chain_10000

### 6.1 Plan agent's miscalibration caveat

Prior Plan agent estimates were wildly wrong:
- Stage 3.1b sppf_symbol_terms GC: 6-10 GB → empirical 5 MB (off by 3 orders of magnitude).
- Stage 3.2 im::Vector: -200-400 MB → empirical +22 GB (off by sign AND ~100× magnitude).

Estimates below are **ranges with explicit instrumentation requirements** — re-measure at every gate.

### 6.2 Cursor-state accounting

From heaptrack at chain_1000: `BranchCursor::clone` = 49% of 608 MB = ~298 MB. Per-cursor avg ~3.2 KB. ~70-100 K clone invocations.

chain_10000 extrapolation: ~10⁹ cursors at peak, ~3-6 GB just from cursor state (compounded with SPPF/FxHashMap/alloc churn = 24 GB).

Cohort lazy at peak ~225 logical cursors organized into ~10 cohort frames:
- 10 shells × ~1 KB = ~10 KB
- 225 member states × 64 B = ~14 KB
- Total: ~125 KB at frontier (vs today ~720 KB)

### 6.3 Predicted ranges

| Stage | Predicted chain_10000 peak | Confidence |
|------:|---------------------------:|------------|
| Baseline | 24 GB OOM | observed |
| L3 | 6-12 GB | LOW |
| L4 | 4-8 GB | MEDIUM |
| L5 | 2-4 GB | MEDIUM-HIGH |
| L6 | 1.5-3 GB | MEDIUM |

**Honest assessment**: eliminating most of BranchCursor::clone via lazy cohort representation should bring chain_10000 from 24 GB to roughly **4-8 GB at L4 gate**. Reaching <2 GB requires L5+L6 gains (highest uncertainty).

### 6.4 What falsifies the design

If at L3 cohort_avg_member_count < 3, abort and re-plan. If L3's chain_1000 Welch regresses > 3%, cohort overhead exceeds savings.

---

## 7. Risk Register

| # | Risk | Likelihood | Impact | Mitigation |
|---|------|-----------:|-------:|------------|
| 1 | Cohort_avg_member_count = 1-2 in practice | LOW | HIGH | Stage L3 instrumentation BEFORE L4 commits |
| 2 | (L2) discipline violation: ObsInvariant misclassification → silent ambiguity drop | MEDIUM | CATASTROPHIC | Property test enumerating all WpdaStepAction variants × 6 mutable fields |
| 3 | Cycle-defense soundness: false-positive rejection from shared visited_dispatch | LOW | HIGH | Stage L4 inverse-coverage test |
| 4 | Materialization storms in lex-Fork heavy grammars | MEDIUM | MEDIUM | rhocalc + lambda + -3! Welch gate every stage; if materialization rate > 50%, narrow to dispatch-key only |
| 5 | Multi-packing snapshot count grows unbounded at L6 | LOW | MEDIUM | MAX_COHORT_FRAME_MEMBERS = 256 hard cap |
| 6 | Engine.step purity violated by future grammar features | LOW | HIGH | Property test on all WpdaState variants under CrossCatDelegate |
| 7 | Hybrid-merge (L5) stale-pointer bug | MEDIUM | HIGH | All shared Arcs immutable after cohort formation; writes go through materialization |
| 8 | chain_50/100 perf regression > 5% | MEDIUM | MEDIUM | Welch's-t REJECT triggers revert of the offending stage; design the L3 fast path so the ObsInvariant branch is a single early-return for any cursor that is currently `Frame::Concrete` (no allocation, no comparison cost) — only paid by frames that are actually `Frame::Cohort` |
| 9 | Multi-week plan abandoned mid-way | MEDIUM | MEDIUM | Each stage committed independently and reversible; flag stays OFF if abandoned |
| 10 | Plan agent estimate off by 10×-1000× | HIGH | LOW | Empirical re-measurement at every gate is non-negotiable |

---

## Critical Files

- `prattail/src/wpda_walker.rs` (BranchCursor, ConfigKey, step_fanout, merge_equivalent_cursors, allocate_fork_push_child, revive_cohort_member_with_snapshot — most changes land here; ~13.7 KLoC file)
- `prattail/src/dispatch_cohort.rs` (current cohort machinery; lazy replaces `pending_cohort: Vec<CohortMember>` with `pending_cohort_frame: Option<CohortFrame>`)
- `prattail/src/cohort_lazy.rs` (NEW MODULE; ~400-600 LoC at completion)
- `prattail/src/walker_stats.rs` (new cohort-specific counters)
- `prattail/Cargo.toml` (no feature flag — each stage lands as a single commit with the gauntlet + Welch's-t gate; if any stage fails its gate, REVERT the commit)

Supporting references read but not primary surface:
- `prattail/src/sppf.rs` (Symbol-dedup at line 511 — load-bearing for §1.2 Lemma 2)
- `prattail/src/gss.rs` (GSS edge/node API)
- `languages/tests/trampoline_tests.rs` (test_left_assoc_chain_10000 at line 176 — operational target)

---

## References

- Tomita, M. (1985). *Efficient Parsing for Natural Language*. Kluwer.
- Scott, E. & Johnstone, A. (2010). "GLL Parsing." *ENTCS* 253(7): 177-189.
- Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS 2007*.
- Goodman, J. (1999). "Semiring Parsing." *Computational Linguistics* 25(4):573-605.

---

## Explore-agent validation of foundational assumptions (2026-05-25)

Four parallel Explore agents validated the design's correctness foundations. Findings:

### Agent 1 — Engine purity (Lemma 1) — TRUE WITH CAVEATS

- `engine.step` `CrossCatDelegate` arm at `macros/src/gen/runtime/wpda_codegen/engine_impl.rs:1390-1425` is provably pure on `(source_src_idx, pos, inner_cur_bp)`. Body reads only the destructured fields; outputs `Push { CategoryEntry(S), lex_one(), PrefixDispatch(P, B) }`.
- `engine.step` takes `&self` (Rust type system enforces no engine mutation).
- Zero textual matches for `recovery_deltas`, `incoming_edge_stack`, `sppf_top`, or `visited_*` in engine_impl.rs.
- Symbol-dedup at `sppf.rs:511-525` VERIFIED — `intern_symbol(nt, lo, hi)` is the 3-tuple dedup key.
- **CAVEAT**: `lex_fork_path` (`wpda_walker.rs:1402`) is a per-cursor identity discriminator the engine does NOT read but the walker's `ConfigKey` (`:1799`) does. Two cursors with same `(S, P, B)` but different `lex_fork_path.last()` produce identical sub-parse structural output but are treated as DISTINCT parses. **Cohort representation must carry `lex_fork_path` as a shell axis OR as per-member state**; the design's `CohortShell.lex_fork_stamp` field is the correct placement (member-uniform at formation since `lex_fork_stamp` is `~_obs`).

### Agent 2 — Mutation sites inventory + classifier (informs §3 algorithm)

- 17 distinct mutation sites across the 6 per-cursor mutable fields.
- **11 shell-invariant** (`visited_*` Stage F.11 R7 hoist 5246-5269, `optional_scope_marks` all paths, `binder_scope_marks` all paths).
- **6 per-member-divergent** — all `recovery_deltas.push` sites; they only fire on recovery Forks, which already diverge `recovery_depth` per member.
- **4 depends-on-engine-purity** — `incoming_edge_stack` push/pop sites; shell-invariant *only if* the GSS edge allocation is deterministic on `(pos, symbol)`. Current implementation satisfies this since `GSS::add_edge_kind`'s dedup key is `(pos, symbol)`.

**Concrete action-divergence classifier** delivered:
```rust
fn divergence_class(action: &WpdaStepAction<W>) -> DivergenceClass {
    match action {
        Idle | Accept | Error(_) | Advance(_) | Consume{..} | ConsumeAndReplace{..}
            | ConsumeIdentAndReplace{..} | Replace{..} | ReplaceAndPush{..}
            | ConsumeAndPush{..} | OptGroupAbsent{..} | OptGroupFinalize{..}
            | ParsePredicate{..} | Push{..}    => ObsInvariant,
        AdvanceWithEffect { effect, .. } if is_recovery_delta(effect) => ObsDivergent,
        AdvanceWithEffect{..}                                          => ObsInvariant,
        Push { new_state: WpdaState::CrossCatDelegate{..}, .. }       => DispatchResolved,
        Pop{..} | ConsumeAndPop{..}                                    => pop_will_fire_action(..) ? ObsDivergent : ObsInvariant,
        Fork { branches, ..} => {
            if any branch.is_recovery() || any branch is LexAlt*       => ObsDivergent,
            if any branch is CrossCatDelegate                           => DispatchResolved,
            else                                                        => ObsInvariant,
        }
    }
}
```

### Agent 3 — H12 cohort cache mapping (informs Stage L2 replacement)

- **Critical ambiguity-lossy bug confirmed**: `MAX_WORKER_SNAPSHOTS_PER_KEY = 4` (`dispatch_cohort.rs:365`) silently DROPS the 5th+ packing's snapshots. Per the file's own comment at 362-364, pathological grammars with >8 packings per Symbol fall through, but paused cohort members lose access to the 5th+ packing's distinct revives. **Stage L6 must close this hole** (or the whole design is moot for high-ambiguity grammars).
- Drain semantics: **members outer × snapshots inner** with `snapshots_drained` advance for cross-step delta. New `CohortFrame` must preserve member-outer enumeration.
- `revive_cohort_member_with_snapshot:9662` is a 12-step bulk-set sequence. New design's `materialize_cohort` and `fan_out_cohort` must reproduce these 12 fields per emitted cursor.
- State machine: `InFlight → Resolved` one-way; never returns. Resolved persists for entire parse. `pending_cohort_drain_keys: FxHashSet<DispatchKey>` is the scheduling channel from resolve site to drain.
- Coupling that must be preserved: `cohort_origin` ConfigKey discriminator (`:1749`), `cohort_revive_depth` G2 graduation (`:10238-10244`), `cursor_gss_push_with_kind` with `EdgeKind::CrossCatProjection`.

### Agent 4 — ConfigKey + merge correctness (informs Stage L5 hybrid merge)

- 10 of 11 ConfigKey fields are `~_obs` axes (cohort-uniform). Only `sppf_top` is per-member.
- Post-dispatch all revived members share `sppf_top == Some(symbol_id)` (the sub-parse Symbol). Divergence on `sppf_top` happens at the **first per-member action firing**, which is precisely when materialization should fire — natural alignment.
- `cohort_origin` is the load-bearing discriminator preserving the `-3!` ambiguity fix. G2 graduation rule clears it when cursor exits its dispatch's return frame (`:10238-10244`).
- `lex_fork_stamp` is `~_obs` — cohort members are forced identical at formation (else they bucket separately upstream). Belongs in `CohortShell`.
- **Hybrid merge correctness condition**: absorb `Frame::Concrete(c)` into `Frame::Cohort(cf)` iff
  - `c.cohort_origin == Some(cf.shell.dispatch_key)` (otherwise retroactively claiming cohort heritage),
  - `c`'s next `engine.step` action projects to `cf.shell.dispatch_key`,
  - all 9 other `~_obs` axes match.
- Action-peek is **FREE** — `engine.step` is `&self`, idempotent. No cursor mutation required.
- **Recommended ConfigKey changes**: add a `frame_kind: enum {Concrete, Cohort(ShellId)}` discriminator so Cohort frames bucket by shell. No other changes needed.

### Aggregate verdict

The design's correctness foundations are **sound** modulo three discovered caveats:
1. `lex_fork_path` must be carried as part of `CohortShell` (already planned).
2. Pop-with-action must classify as `ObsDivergent` (new constraint surfaced).
3. `MAX_WORKER_SNAPSHOTS_PER_KEY` cap removal is now a Stage L6 **hard requirement** (was previously a nice-to-have).

The action-divergence classifier rule is concrete and implementation-ready. The H12 cohort cache replacement path is fully mapped. The hybrid merge absorption invariant is precisely stated.

**Next implementation step**: Stage L1 (Frame enum scaffolding). Per the migration path's empirical-gate discipline — no feature flag, no env gate, no opt-in: each stage lands as a single commit gated on gauntlet 6169/0 + Welch's-t-test pass; if it fails, REVERT.

---

## Summary

24 GB chain_10000 ceiling is dominantly `BranchCursor::clone` cost (49% of peak per heaptrack). Per-cursor state (six mutable fields) defeats simple Arc-CoW. Cursor count (~225) is constant and merging cannot shrink it without violating ambiguity preservation.

Cohort lazy materialization introduces `Frame<W>` enum: `Concrete(BranchCursor)` (today) and `Cohort(CohortFrame)` (shared `~_obs`-invariant shell + Vec of per-member divergence). Cohorts form at H12 cross-cat-projection sites where same `(S, P, B)` triple is hit by 10s-100s of cursors. Shell's mutable fields Arc-shared, materialize only on per-member mutation.

6-stage plan (L1-L6), each gated on Welch's-t-test for chain_50/100/200/1000 and chain_10000 operational target. No feature flag — each stage lands as a single commit; failed gates trigger a clean revert. L1-L2 scaffolding (Frame enum + cohort frame at H12 sites, no algorithmic change yet); L3 ObsInvariant fast path; L4 Arc-shared cycle defense; L5 hybrid re-absorption; L6 removes H12 caps. Expected chain_10000 after L6: 1.5-3 GB.

Total effort: 21-32 working days (4-6 calendar weeks). Each stage independently reversible.

Principal risks: (a) cohorts not forming densely enough — measure at L3; (b) (L2) discipline correctness via property tests; (c) cycle-defense soundness via inverse-coverage test. All addressed by walker-stats instrumentation and 6169/0 gauntlet preservation at each gate.

Plan agent's prior memory estimate miscalibration (Stage 3.1b 6-10 GB → 5 MB; Stage 3.2 -200 MB → +22 GB) makes re-measurement at every gate non-negotiable.
