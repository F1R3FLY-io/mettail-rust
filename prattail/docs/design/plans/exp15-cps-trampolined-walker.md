# Exp 15 — CPS / Trampolined Walker Rewrite (multi-session plan)

**Branch / tip**: `feature/wfst-architecture` at `734ceb7`
**Status**: design only — no code shipped at this commit. All substages are PROPOSED.

## 1. Goal & non-goals

### Goal

Architecturally reduce `BranchCursor`'s per-element memory footprint from ~512 B to ≤ 64 B *continuation records* over a walker-global persistent state map, replacing the implicit-recursion `apply_action_to_cursor` driver with an explicit FIFO continuation queue (CPS / trampoline). Target: chain_500 LEFT-assoc walker peak drops from 4.87 GB to ≤ 1.0 GB; chain_10000 LEFT-assoc test passes within 24 GB.

### Non-goals

- **Does not change grammar surface.** No new EBNF, no new operators, no codegen-emitted token disposition changes.
- **Does not change SPPF layout.** `Sppf::intern_packing`, `intern_symbol`, `link_packing_to_symbol`, `dedup_packing`, `dedup_symbol`, `SppfId`, `SppfNode` all preserved verbatim.
- **Does not change semiring.** `Semiring`, `SemiringRef`, `LexicographicWeight`, `times_ref`, `plus`, the lex-min comparator all preserved.
- **Does not change CESK store / CEK eval / green threads / LogicT.** `cesk_store.rs`, `cek.rs`, `green_thread.rs`, `logict.rs` are *referenced* as precedent only.
- **Does not change `WpdaStepAction` variants.** The 17 variants (Advance / AdvanceWithEffect / Push / Pop / Replace / Fork / ConsumeAndPush / ConsumeAndPop / Consume / ConsumeIdentAndReplace / ConsumeAndReplace / ReplaceAndPush / ParsePredicate / OptGroupAbsent / OptGroupFinalize / IterativeChainAbsorb / Accept / Error / Idle) are preserved. CPS rewrites what *consumes* them, not what *produces* them.
- **Does not change the engine→walker contract.** Engine still returns `WpdaStepAction<W>` from `engine.step(state, gss, top, pos, tokens)`.
- **Does not introduce feature gates / env vars / runtime flags** per user mandate (the walker-stats feature gate is already in place and is reused for memory/perf attribution; no new gates added).
- **Does not introduce parallelism.** Continuation queue is single-threaded FIFO; per-parse-session ownership preserved.
- **Does not change ConfigKey merge semantics.** `merge_equivalent_cursors` is rewritten internally but its observable contract (cursors with equal ConfigKey collapse with lex-min weight winning) is preserved verbatim.
- **Does not remove the existing L1-L6 cohort lazy machinery.** CohortShell+CohortMemberState is *generalized*, not replaced — see §3 Interaction.
- **Does not promote `incoming_edge_stack_arena` or `sppf_stack_arena` from per-cursor `StackId` to walker-global `(cursor_id, kind)` keying** until Substage 4 (these arenas already win — Exp 0.5 ACCEPT for sppf_stack; the CPS rewrite preserves them).
- **Does not change Welch's-t-test gate methodology.** p<0.05 LEFT-assoc + RIGHT-assoc panel REMAINS the ship gate, scored per substage via `mcp__pgmcp__experiment_decide`.

## 2. Theoretical foundation

### 2.1 Continuation-passing style + trampolining

A **continuation** is a first-class representation of "the rest of the computation". In direct-style code,
`apply_action_to_cursor(cursor, action, tokens) -> CursorOutcome` recursively threads control through 17 match arms, each of which may call back into helpers (`cursor_gss_push_with_kind`, `apply_pop_body_to_cursor`, `emit_fire_action`) that themselves may call back into apply-like primitives. The implicit call-stack carries the *whole* cursor (~512 B BranchCursor) by mutable reference.

A **trampoline** explicitly hoists the recursion into a heap-allocated queue. Each iteration dequeues one continuation, runs *one step*, and may enqueue 0..N successor continuations. The call stack stays O(1) regardless of derivation depth. Functional-PL community: Felleisen et al. "The Essence of Compiling with Continuations" (1993); Steele "Lambda: The Ultimate Imperative" (1976).

### 2.2 Persistent data structures (Bagwell HAMT, Okasaki)

A **persistent data structure** preserves all prior versions when "mutated"; the new version shares the unchanged majority of the structure with the old. Phil Bagwell's Hash Array Mapped Trie (HAMT, 2001) gives O(log32 N) insert / lookup / delete with structural sharing. The `im` crate ships `im::HashMap` (HAMT-backed), `im::OrdSet` (RRB-tree-backed `BTreeMap`), and `im::Vector` (RRB-tree balanced rope). Chris Okasaki, *Purely Functional Data Structures* (1998), establishes the lower-bound algorithms.

### 2.3 Why CPS+persistent gives walker-wide sharing where Arc-CoW gives per-cursor copies

Today the walker has per-cursor `Arc<FxHashSet<PackedDispatchConfig>>` for visited_dispatch. The Arc gives O(1) clone *bump* on Fork; but the first per-cursor `insert` post-Fork triggers `Arc::make_mut` which deep-clones the entire `FxHashSet`. With 28.9 M cohort cursor emissions on chain_500 LEFT-assoc (Exp 16 r3), even 712× content-level dedup gives 49.6 M `(cursor_id, config)` *entries* across all FxHashSet snapshots (1.1 GB at 24 B/entry).

A walker-global `im::OrdSet<(CursorId, PackedDispatchConfig)>` with HAMT-style sharing collapses this differently: each `(cursor_id, config)` is interned exactly once across the entire walker. Two cursors that share a prefix of visited-configs share the underlying HAMT chain through the trie; per-cursor "cycle defense" becomes "lookup of `(my_cursor_id, candidate_config)` in the global set". The 49.6 M entries collapse to **at most the number of unique-cursor-configs ever visited** = (peak cursor count) × (peak visited set size). At chain_500 left-assoc that's 183,843 cursors × ~712 unique configs = 130 M entries — but each entry is *24 B with HAMT-shared interior nodes*, AND the cursor_id tag is just 4 bytes. Per-trie-node overhead is amortized at log32(130 M) ≈ 6 levels (256 KB for index nodes).

More importantly: when cursor `c` Forks into children `c1, c2`, today each child gets an `Arc<FxHashSet>::clone` and the first mutation costs O(|set|). Under the CPS+persistent scheme, each child's continuation just carries cursor_id `c1` / `c2`; their insert is `set.update((c1, config), ())` which costs O(log32 |set|), and shares ALL of `c`'s entries via HAMT structural sharing. **The 1.1 GB visited_dispatch dominator is the per-cursor `Arc<FxHashSet>` copies after Arc::make_mut**, exactly the layer CPS+persistent eliminates.

### 2.4 Soundness — observed-output equivalence with the recursive walker

**Theorem** (informal): for any input, the CPS walker produces the same set of `CursorOutcome::Resolved` cursors with the same `(weight, pos, sppf_id)` tuples in the same lex-min order as the recursive walker.

**Proof sketch** (full obligation deferred to Substage 5):
- Each `apply_action_to_cursor(c, a, t)` call in the recursive walker corresponds to dequeuing a `Continuation::Apply { cursor_id, action }` in the CPS walker. The `match action` body is mechanically transcribed: arms that today return `CursorOutcome::Alive` enqueue a `Continuation::Resume { cursor_id }`; arms that return `CursorOutcome::ForkInto(children)` enqueue N `Continuation::Apply { cursor_id: new_id, action: next }` records; arms that return `Drop` / `Resolved` are non-enqueuing terminal arms.
- The ORDER of dequeue matches the order of `extend` in the recursive walker iff the queue is FIFO and Fork-arms enqueue children in source order (preserves the load-bearing "tiebreak chain link 4" at `wpda_walker.rs:7813`).
- `merge_equivalent_cursors` is structurally preserved: it operates on the *set* of alive cursors at end-of-step; the CPS version drains the alive-continuation queue into a Vec, runs the existing merge, and re-queues the survivors.
- `commit_winner` runs over the lex-min `Continuation::Resolved` record's full BranchCursor materialized once at commit time (the per-cursor state lives in the walker-global persistent maps; materialize is O(log32 N) reads).
- Therefore, every Resolved cursor produced by the recursive walker is produced by the CPS walker with the same per-cursor state, and conversely (since CPS never invents continuations). Lex-min ordering is preserved because Welch-gate's existing `pick_lex_min_resolved` is the only comparator used in both architectures.

The 4134/0 lib gauntlet + 18/0/6 trampoline gauntlet at every substage is the empirical falsifier of any subtle violation.

## 3. Architecture changes

### 3.1 Continuation record format

```rust
// New module: prattail/src/cps_walker.rs (Substage 1)
#[derive(Debug)]
pub enum Continuation<W: SemiringRef> {
    /// Pick up the cursor's state from walker-global map, ask engine for next action, enqueue ApplyAction.
    Step { cursor_id: CursorId },                                // ≤ 8 B
    /// Apply a precomputed action; produced by Fork-arm broadcasts.
    ApplyAction { cursor_id: CursorId, action: WpdaStepAction<W> }, // ≤ 64 B for Advance; Fork variants are heavier — see §3.1.1
    /// Cursor is in a terminal state; rendezvous with merge.
    Resolved { cursor_id: CursorId },                            // ≤ 8 B
    /// Cohort-shell dispatch: bulk-apply ObsInvariant action over N members.
    ShellApply { cohort_id: CohortId, action: WpdaStepAction<W> }, // 16 + sizeof(W) + sizeof(action_payload)
    /// End-of-step rendezvous marker (drains queue → merge_equivalent_cursors → re-queues).
    StepBarrier,                                                 // 4 B
}
```

**Size budget**:
- `CursorId = u32` (Copy). `CohortId = u32` (Copy).
- `Continuation::Step` and `Resolved` are **8 B** (1-byte tag + 4-byte id + padding).
- `ApplyAction` for `WpdaStepAction::Advance(WpdaState)` is **24 B** (tag + cursor_id + WpdaState 12-16 B).
- `ApplyAction` for `WpdaStepAction::Push { symbol, weight, new_state }` is **48-72 B** depending on `W` size. For `LexicographicWeight` (12 B) it's ~60 B.
- `ApplyAction` for `WpdaStepAction::Fork { branches: Vec<ForkBranch<W>>, .. }` is **24 B for the enum shell + the existing Vec heap allocation** — but the Fork-arm continuation does NOT carry the full branches vec post-Substage 3; instead Fork-arm emission enqueues *one Continuation per branch* with the per-branch action precomputed, so the Vec heap allocation is *consumed at enqueue time and not carried in the queue*.

**Plan target**: P50 continuation size ≤ 32 B, P99 ≤ 64 B. Workload validates this at Substage 0 instrumentation.

### 3.2 Walker-global persistent state map (`CursorStore`)

```rust
// prattail/src/cursor_store.rs (Substage 1)
pub struct CursorStore<W: SemiringRef> {
    /// Heavy per-cursor fields, sparsely indexed. im::HashMap<CursorId, _>
    /// gives O(log32 N) read/write with HAMT structural sharing.
    visited_dispatch_membership: im::OrdSet<(CursorId, PackedDispatchConfig)>,
    visited_recovery_membership: im::OrdSet<(CursorId, PackedDispatchConfig)>,
    recovery_deltas:             im::HashMap<CursorId, im::Vector<BuilderDelta>>,
    optional_scope_marks:        im::HashMap<CursorId, im::Vector<usize>>,
    binder_scope_marks:          im::HashMap<CursorId, im::Vector<(u16, im::Vector<String>)>>,
    lex_fork_path:               im::HashMap<CursorId, im::Vector<LexForkStamp>>,
    // CursorId-keyed pure-Copy state lives in a parallel Vec indexed by cursor_id (cache-friendly hot path).
    minimal: Vec<MinimalCursorState<W>>, // see §3.3
    free_list: Vec<CursorId>,
    next_id:   u32,
}

#[derive(Clone, Debug)]
pub struct MinimalCursorState<W: SemiringRef> {
    pub node: GssNodeId,
    pub pos: usize,
    pub weight: W,
    pub inner_state: WpdaState,
    pub source_priority: u32,
    pub incoming_edge_stack_id: EdgeStackId,
    pub recovery_depth: u8,
    pub sppf_stack_id: StackId,
    pub pending_packing_weight: W,
    pub collection_stack_depth: u8,
    pub last_action_output_cat: Option<u16>,
    pub cohort_origin: Option<DispatchKey>,
    pub cohort_revive_depth: u32,
    pub sppf_collection_arena: Arc<Vec<Vec<SppfId>>>, // unchanged; F.4 stays
    // Total size target: ≤ 96 B (vs today's 512 B BranchCursor — 5.3× reduction).
}
```

**Allocation policy**: `CursorId` is a recycled u32. Fork emits N new `CursorId`s via `cursor_store.alloc_n(N, parent_id)`; the alloc returns ids and pre-installs the parent's minimal state per child (cheap `Clone` of MinimalCursorState — no Vec/HashSet inside) AND shares all heavy persistent fields via the `im::HashMap`'s existing per-key entry (no insert needed; sharing inherited by lookup keying on `parent_id`).

**The KEY insight**: per-child Fork no longer does `parent.visited_dispatch.clone()` (Arc bump + later Arc::make_mut). Instead the child's `cursor_id` simply DOES NOT have an entry in `recovery_deltas` (= empty Vector inherited via fallback-to-parent semantics in lookup — see §3.5). The first per-child insert is `cursor_store.recovery_deltas.update(child_id, parent_recovery_deltas.update_back(delta))`, which is O(log32) and *shares the unchanged prefix with parent* via HAMT.

### 3.3 What stays per-cursor (minimal); what moves walker-global

| Field (today on `BranchCursor`) | New location | Rationale |
|---|---|---|
| `node: GssNodeId` | `MinimalCursorState` | Read every step; small Copy |
| `pos: usize` | `MinimalCursorState` | Same |
| `weight: W` | `MinimalCursorState` | Same |
| `inner_state: WpdaState` | `MinimalCursorState` | Same |
| `source_priority: u32` | `MinimalCursorState` | Pure Copy |
| `incoming_edge_stack_id: EdgeStackId` | `MinimalCursorState` | Already a u32 handle; arena-shared |
| `recovery_depth: u8` | `MinimalCursorState` | Pure Copy |
| `sppf_stack_id: StackId` | `MinimalCursorState` | u32 handle; arena-shared |
| `pending_packing_weight: W` | `MinimalCursorState` | Per-cursor by Q1.A+ semantics |
| `collection_stack_depth: u8` | `MinimalCursorState` | Pure Copy |
| `last_action_output_cat: Option<u16>` | `MinimalCursorState` | Pure Copy |
| `cohort_origin: Option<DispatchKey>` | `MinimalCursorState` | Small enum |
| `cohort_revive_depth: u32` | `MinimalCursorState` | Pure Copy |
| `sppf_collection_arena: Arc<Vec<Vec<SppfId>>>` | `MinimalCursorState` | Already Arc; F.4 fix preserved |
| `recovery_deltas: Arc<Vec<BuilderDelta>>` | `CursorStore::recovery_deltas: im::HashMap<CursorId, im::Vector<BuilderDelta>>` | HAMT shares prefix-of-deltas across cursors |
| `visited_dispatch: Arc<FxHashSet<PackedDispatchConfig>>` | `CursorStore::visited_dispatch_membership: im::OrdSet<(CursorId, PackedDispatchConfig)>` | **This is the 23.3 % dominator** |
| `visited_recovery: Arc<FxHashSet<PackedDispatchConfig>>` | `CursorStore::visited_recovery_membership: im::OrdSet<(CursorId, PackedDispatchConfig)>` | Same pattern |
| `optional_scope_marks: Vec<usize>` | `CursorStore::optional_scope_marks: im::HashMap<CursorId, im::Vector<usize>>` | Sparse — most cursors empty |
| `binder_scope_marks: Vec<(u16, Vec<String>)>` | `CursorStore::binder_scope_marks: im::HashMap<CursorId, im::Vector<(u16, im::Vector<String>)>>` | Sparse |
| `lex_fork_path: Arc<Vec<LexForkStamp>>` | `CursorStore::lex_fork_path: im::HashMap<CursorId, im::Vector<LexForkStamp>>` | Sparse; HAMT-shared |

**Note**: H2 (Arc-CoW incoming_edge_stack) was REJECTED at -6.9 %. That precedent is structurally distinct from CPS because: H2 added a layer (Arc) UNDER per-cursor Vec semantics; CPS REMOVES the per-cursor Vec entirely and replaces it with persistent global state. The mutation cost in H2 was Arc::make_mut deep-clone-once-per-Fork; the mutation cost in CPS is `im::OrdSet::update` (O(log32 N) HAMT update *with* sharing). Different layer, different invariant.

### 3.4 Continuation queue

**Choice**: single-threaded `VecDeque<Continuation<W>>` owned by the walker. **Justification**:

1. Walker is single-threaded per parse session (per `prattail/Cargo.toml` lacking parallel features for the walker, and per `f13-baseline-2026-05-20.md`).
2. Crossbeam-deque is in the dep list but for the `worker_pool.rs` / green-thread system, not the parser; introducing it here adds lock-free coordination cost that's pure overhead for single-threaded use.
3. `VecDeque` is cache-friendly (ring buffer) and supports O(1) push_back / pop_front for the FIFO discipline. Memory: ~16 B header + element_size × capacity, amortized doubling.
4. Future parallelism (e.g., multi-thread cohort dispatch) can be added by replacing the queue type with a crossbeam-deque without changing the continuation-record format. Out of scope.

Queue lifecycle: `WpdaWalker::run_one_step()` drains the queue until either `Continuation::StepBarrier` is dequeued OR the queue empties; then runs `merge_equivalent_cursors` over the alive cursor_ids; then re-enqueues `Continuation::Step { cursor_id }` for each survivor plus a fresh `StepBarrier`. End-of-input is reached when, after a barrier, the survivor list is all Resolved.

### 3.5 visited_dispatch becomes walker-global persistent

```rust
// On insert:
fn cursor_visited_dispatch_insert(store: &mut CursorStore<W>, cursor_id: CursorId, key: PackedDispatchConfig) {
    store.visited_dispatch_membership.insert((cursor_id, key));
}

// On contains-check:
fn cursor_visited_dispatch_contains(store: &CursorStore<W>, cursor_id: CursorId, key: PackedDispatchConfig) -> bool {
    store.visited_dispatch_membership.contains(&(cursor_id, key))
}

// On Fork (child inherits parent's visited set):
fn fork_inherit(store: &mut CursorStore<W>, parent_id: CursorId, child_id: CursorId) {
    // Sweep parent's prefix in the OrdSet, re-insert under child_id.
    // BUT: at chain_500 the per-cursor visited set is ~700 entries; sweeping
    // 700 × 28.9 M cohort cursors is 20 B inserts. UNACCEPTABLE.
    //
    // SOLUTION (key insight): use cursor_id as a LINEAGE-prefix. Child cursor_id
    // gets a sentinel "inherits-from(parent_id)" marker in a small auxiliary
    // im::HashMap<CursorId, CursorId> "parent_of_inheritance". contains-check
    // walks the chain: contains(c, k) = membership.contains((c,k)) || parent_of_inheritance.get(c).map_or(false, |p| contains(p, k)).
    // insert(c, k) writes only the (c, k) tuple; chain walk handles the rest.
}
```

**The lineage-chain insight is load-bearing**: this is the structural mechanism by which `cursor_id`-keyed visited sets are O(1) per Fork yet preserve cycle defense soundness. The chain depth is bounded by Fork-depth (= number of nested ambiguity points along the cursor's history, typically < 64 even at chain_10000).

False positives: `contains` walks the chain; if `cursor_id` was forked deeply (e.g., 60 nested Forks), `contains` is O(60 × log32 N). Mitigation: at periodic intervals (e.g., every merge_equivalent_cursors), flatten chains shorter than 4 by re-inserting entries directly under the leaf cursor_id and deleting the lineage pointer.

The 1.1 GB visited_dispatch dominator drops to **(number of unique inserted (cursor_id, key) tuples)** × (24 B per OrdSet node) + lineage map (~8 B × cursor count). At chain_500 left-assoc: estimated 1.5-2.5 GB → ≤ 200 MB total. **Substage 3 falsifies if this prediction is off by > 3×.**

### 3.6 Fork emits N continuations instead of N BranchCursor clones

Today's Fork-arm at `wpda_walker.rs:5736-6639`: each branch builds a fresh `BranchCursor { recovery_deltas: parent.clone(), visited_dispatch: parent.clone(), ... }` (Arc bumps) and the surviving children Vec is `extend`ed into branch_cursors.

CPS rewrite of Fork-arm:
```rust
WpdaStepAction::Fork { branches, consume_trigger } => {
    if consume_trigger { state.pos += 1; }
    let parent_id = current_cursor_id;
    for (i, branch) in branches.into_iter().enumerate() {
        let child_id = self.cursor_store.alloc_child(parent_id, /* source_priority = */ i as u32);
        // child_id inherits parent's minimal state by Clone of MinimalCursorState (~96 B); no Vec/HashSet inside, pure Copy + Arc bumps for sppf_collection_arena (F.4 preserved).
        let child_minimal = &mut self.cursor_store.minimal[child_id.0 as usize];
        child_minimal.weight = child_minimal.weight.times_ref(&branch.weight);
        child_minimal.inner_state = branch.new_state;
        child_minimal.pending_packing_weight = parent_minimal.pending_packing_weight.times_ref(&branch.weight);
        // ENQUEUE the next-step continuation:
        self.cont_queue.push_back(Continuation::Step { cursor_id: child_id });
    }
    // Parent cursor_id is no longer alive; it's effectively replaced by N children.
    self.cursor_store.retire(parent_id);
    return CursorOutcome::ForkInto(/* N children but vec not materialized — queue carries them */);
}
```

Memory saved per Fork-arm at chain_500 left-assoc: 28.9 M cohort cursors × (512 B BranchCursor - 96 B MinimalCursorState - 64 B Continuation) = **28.9 M × 352 B = 9.7 GB**. Conservative: factor of 0.7 for HAMT overhead → ~6.8 GB walker peak reduction (corroborating chain_10000 fitting in 24 GB).

### 3.7 merge_equivalent_cursors becomes "merge continuations"

`merge_equivalent_cursors` at `wpda_walker.rs:8659` works on `branch_cursors: Vec<Frame<W>>`. It computes `ConfigKey` per cursor, buckets cursors by key, and within each bucket lex-min-merges via `LexicographicWeight::plus`.

Rewrite: same algorithm but over a `Vec<CursorId>` (drained from queue at the barrier). ConfigKey computation now reads from `CursorStore::minimal[cursor_id.0]` instead of `&BranchCursor`. Bucket structure unchanged. Lex-min winner's cursor_id is enqueued as the survivor; loser cursor_ids are retired (`cursor_store.retire(id)` triggers `recovery_deltas.remove(id)` etc. — entry deletion under im::HashMap is O(log32) with sharing-aware drop).

**Performance contract**: merge_equivalent_cursors is O(N × log32 cursor_count) instead of today's O(N × |visited_dispatch|) because the ConfigKey doesn't need to materialize the visited sets (it reads `cohort_origin: Option<DispatchKey>`, `lex_fork_path.last()`, etc. — all O(log32) reads from the persistent maps).

### 3.8 Interaction with cohort_lazy.rs L1-L6

The current `CohortFrame<W>` already IS a partial CPS shape: `CohortShell` is shared state, `CohortMemberState` is per-member divergence. Generalize:

- **CohortShell → first-class persistent map.** Cohorts become a `Vec<CohortFrame<W>>` PARALLEL TO `Vec<CursorId>` in the walker. A cohort's shell is `Arc<CohortShell<W>>` (unchanged); each member-state is a `(CursorId, snapshot_idx, weight_at_dispatch, pending_packing_weight, source_priority, cohort_revive_depth)` tuple. Cohort members become FIRST-CLASS continuations: `Continuation::ShellApply { cohort_id, action }` applies an ObsInvariant action to the shell once and bumps all member-cursor pending_packing_weights via a sweep.
- **L3.4 ObsInvariant fast path graduates to include Push/Pop/ConsumeAndPush** (per replicated-conjuring-turtle.md Intervention B; that intervention's design IS valid even after Intervention A failed). The CPS rewrite makes this trivially safe because per-member state lives in CursorStore.
- **L6 cap (currently 16) can be raised to MAX_COHORT_FRAME_MEMBERS = 256** because cohort member cost drops from 76 B (current) to ~16 B (CursorId tuple in persistent map).

The L1-L6 work is PRESERVED, not removed; CPS treats CohortFrame as a special kind of continuation aggregator with shell-amortized step semantics.

### 3.9 Interaction with the Exp 18 Substage 0 EdgeKindProjection instrumentation

KEEP as walker-stats diagnostic. The `WalkerStats::edge_kind_projection` field at `walker_stats.rs:406` is feature-gated and zero-cost when off; useful as a permanent diagnostic for future EdgeKind hypotheses. CPS does NOT change the EdgeStackArena dedup keying — Exp 18 Substage 0 confirmed cursor histories are genuinely distinct, so coarse keying is wrong; CPS instead reduces per-cursor cost, leaving the arena keying alone.

### 3.10 Composition with Exp 14 Tomita per-arc

See §13 for the full compare. Short answer: **the two plans COMPOSE multiplicatively**. Tomita per-arc reduces cohort cursor emissions at the Fork-arm (fewer enqueues into the CPS queue); CPS reduces per-cohort-cursor cost (cheaper records). My recommendation: ship CPS Substage 1-4 first (the LOAD-BEARING per-cursor cost reduction), then re-evaluate Exp 14 against the post-CPS walker peak. If post-CPS chain_500 walker peak < 1.0 GB, Exp 14 may be unnecessary; if 1.0 GB < peak < 3.0 GB, Exp 14 composes for further reduction.

## 4. API + data model changes (file:line + new shape sketch)

### 4.1 New files

| File | Purpose | LOC budget |
|---|---|---|
| `prattail/src/cps_walker.rs` | Continuation enum + queue + drain loop | ~450 |
| `prattail/src/cursor_store.rs` | CursorStore struct + MinimalCursorState + alloc/retire/fork helpers | ~600 |
| `prattail/src/cursor_id.rs` | CursorId newtype + recycle policy + Display/Debug | ~80 |

### 4.2 Modified files (file:line of current shape, target shape sketch)

| File:line | Current | New shape (post-CPS) |
|---|---|---|
| `prattail/src/wpda_walker.rs:1136-1507` (BranchCursor 30+ fields) | Heavy struct, deep clone per Fork | DELETED in Substage 4. Replaced by `MinimalCursorState` + lookups in `CursorStore` |
| `prattail/src/wpda_walker.rs:499-?` (WpdaWalker fields) | `branch_cursors: Vec<Frame<W>>` + 30+ other fields | Add `cont_queue: VecDeque<Continuation<W>>`, `cursor_store: CursorStore<W>`. `branch_cursors` deleted by Substage 4. |
| `prattail/src/wpda_walker.rs:5002-7459` (`apply_action_to_cursor` and helpers, ~2500 LOC) | Takes `&mut BranchCursor<W>`, returns `CursorOutcome<W>` | Rewritten as `apply_action_continuation(&mut self, cursor_id: CursorId, action: WpdaStepAction<W>, tokens) -> ContinuationOutcome<W>`. Each helper that today takes `&mut BranchCursor` takes `&mut CursorStore` + `cursor_id` instead. |
| `prattail/src/wpda_walker.rs:7618-7857` (`step_fanout`) | Outer loop over `branch_cursors: Vec<Frame<W>>` | Replaced by `drive_until_barrier(&mut self, tokens)`. |
| `prattail/src/wpda_walker.rs:7460-7510` (`step_cohort_frame`) | Returns `Vec<Frame<W>>` | Returns `Vec<Continuation<W>>` (enqueues directly). |
| `prattail/src/wpda_walker.rs:8659-?` (`merge_equivalent_cursors`) | Over `branch_cursors` | Over `Vec<CursorId>` drained from queue. |
| `prattail/src/wpda_walker.rs:5736-6639` (Fork-arm ~15 sites) | `let mut child = BranchCursor { ... }` constructors | `let child_id = self.cursor_store.alloc_child(parent_id, branch_idx)` + `self.cont_queue.push_back(Continuation::Step { cursor_id: child_id })` |
| `prattail/src/wpda_walker.rs:10776` (`cursor_gss_push_with_kind`) | `&mut BranchCursor` | `&mut CursorStore + cursor_id` |
| `prattail/src/wpda_walker.rs:11805` (`cursor_gss_pop_via_edge`) | Same | Same |
| `prattail/src/cohort_lazy.rs:108-185` (CohortShell) | Heavy shell with 20+ fields | Unchanged structurally; field reads route via `cursor_store` for shell-member fields that are now persistent. |
| `prattail/src/cohort_lazy.rs:194-236` (CohortMemberState) | Per-member state | Add `cursor_id: CursorId` field; remove `lex_fork_path` (now in CursorStore). |
| `prattail/src/cohort_lazy.rs:313` (DivergenceClass::classify) | Conservative; graduates Push/Pop in Substage 3 | Add `classify_with_edge_kind` (Intervention B) once CursorStore lands. |
| `prattail/src/walker_stats.rs:406` (edge_kind_projection) | EdgeKindProjection field | Unchanged. Diagnostic only. |
| `prattail/src/lib.rs` | Module list | Add `pub mod cps_walker; pub mod cursor_store; pub mod cursor_id;` |

## 5. Substage breakdown

The substages are designed to be **independently revertable**: each ships through a self-contained dual-write phase so that `git revert <substage-K>` restores the prior walker semantics without unwinding K-1.

### Substage 0 — Diagnostics + Continuation record size sample

**Goal** (1-2 sentences): Add walker-stats counters for the proposed CPS continuation queue size distribution + cursor-id-keyed visited_dispatch projection (counterfactual measurement). Verify P50 continuation ≤ 32 B before committing to Substage 1.

**LOC budget**: ~150 (all under `#[cfg(feature = "walker-stats")]`).

**Code paths touched**:
- `prattail/src/walker_stats.rs` (new struct `ContinuationProjection`, ~80 LOC).
- `prattail/src/wpda_walker.rs:7618` (`step_fanout` — sample per-cursor projected continuation size at each step).
- `prattail/src/wpda_walker.rs:5736-6639` (Fork-arm — sample N at each Fork).
- `languages/tests/trampoline_tests.rs` — re-use existing test_left_assoc_chain_50/100/200 + test_right_assoc_chain_50/100/200/1000.

**Welch-gate sample-arms**: NONE (instrumentation only; gauntlet 4134/0 + tramp 18/0/6 preserved).

**Welch falsifier**: N/A (no functional change).

**Gauntlet falsifier**: `cargo test --release -p mettail-prattail --lib` must stay at 4134/0; trampoline at 18/0/6.

**pgmcp lifecycle**:
- `experiment_open(title="Exp 15 S0 — CPS continuation size projection", hypothesis="P50 continuation record ≤ 32 B AND P99 ≤ 64 B on left_assoc_chain_500", primary_metric="cont_record_size_p50_bytes", lower_is_better=true, acceptance_criterion={"type":"hard","threshold":32})`
- `experiment_record_measurement(samples=[size_at_each_enqueue], unit="bytes")`
- `experiment_decide(...)`
- `experiment_log_artifact(kind="walker_stats", content=stats_text)`

**Substage falsifier**: If P50 > 64 B OR P99 > 128 B, the per-record cost will not deliver the projected 5.3× per-cursor reduction. SKIP Substage 1; reconsider format.

**Pre-gate prediction**: P50 = 8-16 B (most actions are Advance / Step / Resolved); P99 = 64 B (Fork ApplyAction with branches Vec); off-by-3× falsifier = P50 > 96 B.

**Memory experiment**: SKIP (no memory change at Substage 0).

**Revert**: `git revert <s0 commit>` removes instrumentation only.

### Substage 1 — Module scaffold + CursorStore type definitions (DEAD code)

**Goal**: Land new modules `cps_walker.rs`, `cursor_store.rs`, `cursor_id.rs` with all type definitions, constructors, alloc/retire/fork helpers, but NO wiring into `step_fanout`. Walker continues to use BranchCursor path verbatim.

**LOC budget**: ~1100 (new module code only; zero deletions in wpda_walker.rs).

**Code paths touched**:
- New: `prattail/src/cursor_id.rs` (~80 LOC).
- New: `prattail/src/cursor_store.rs` (~600 LOC including unit tests).
- New: `prattail/src/cps_walker.rs` (~450 LOC including unit tests).
- `prattail/src/lib.rs` — add module decls.

**Welch-gate sample-arms**: full 7-arm panel (LEFT 50/100/200 + RIGHT 50/100/200/1000).

**Welch falsifier**: Any LOSS at p<0.05. (Should be no measurable effect since new code is dead.)

**Gauntlet falsifier**: 4134/0 + 18/0/6.

**pgmcp lifecycle**: experiment_open → 7 record_measurement calls → 7 experiment_decide.

**Substage falsifier**: gauntlet REGRESS (compile error) or Welch panel any-arm REGRESS p<0.05.

**Pre-gate prediction**: zero effect on wall-time (new modules are dead code); chain_500 LEFT-assoc walker peak unchanged at 4.87 GB; chain_100 LEFT-assoc unchanged at 9.7 s.

**Memory experiment**: chain_10000 RSS rate unchanged (predicted 3.4-3.7 GB/min OOM trajectory, identical to baseline).

**Revert**: `git revert <s1 commit>` removes 3 module files + 3 lib.rs lines.

### Substage 2 — Dual-write CursorStore alongside BranchCursor (DEAD READ)

**Goal**: At every BranchCursor mutation site, MIRROR the mutation into CursorStore for a parallel "shadow cursor" allocated at BranchCursor's allocation. Reads still come from BranchCursor. Verify the two stay in sync via debug_asserts.

**LOC budget**: ~800 (mostly mirror-write boilerplate in wpda_walker.rs).

**Code paths touched**:
- `prattail/src/wpda_walker.rs:5002-7459` — every mutator gets a mirror write.
- `prattail/src/wpda_walker.rs:5736-6639` — Fork-arm allocates child cursor_id alongside child BranchCursor.
- `prattail/src/wpda_walker.rs:2527` — seed cursor allocates seed cursor_id.
- `prattail/src/wpda_walker.rs:8659` — merge_equivalent_cursors retires loser cursor_ids in mirror.
- `prattail/src/cohort_lazy.rs:446-523` — cohort formation mirrors into CursorStore.
- `prattail/src/cohort_lazy.rs:546-581` — materialize_branch_cursor mirrors into CursorStore.

**Welch-gate sample-arms**: full 7-arm panel.

**Welch falsifier**: Welch LOSS p<0.05 on any arm. **Risk: mirror writes are NOT zero-cost.** Predicted slowdown: 5-10 % per step due to im::HashMap update overhead. **This is expected to fail Welch UNLESS mirror writes are feature-gated.** Decision: Substage 2 SHIPS with mirror writes feature-gated under `walker-stats` (existing feature, already accepts non-zero perf cost). Production builds (no walker-stats) don't pay the cost.

Revised LOC: ~900 (every mirror write wrapped in `#[cfg(feature = "walker-stats")]` or `crate::stats_inc!`-style macro).

**Gauntlet falsifier**: 4134/0 + 18/0/6. In walker-stats build, additional debug_asserts firing → test failures.

**pgmcp lifecycle**: same 7-arm Welch panel + a NEW `experiment_open(title="Exp 15 S2 — CursorStore mirror parity")` with `primary_metric="mirror_parity_violations_count", lower_is_better=true, acceptance_criterion={"threshold":0}`.

**Substage falsifier**: ANY mirror parity violation (debug_assert fires on a test in walker-stats build) → REVERT. Welch p<0.05 LOSS on production build → REVERT.

**Pre-gate prediction**: production build unchanged (chain_100 LEFT-assoc 9.7 s, chain_500 LEFT-assoc walker peak 4.87 GB — predicting **no change** because mirror writes are feature-gated). Walker-stats build chain_100 +20-30 % wall (acceptable since walker-stats is diagnostic-only).

**Memory experiment**: chain_10000 RSS rate unchanged (predicted; mirror writes only active under walker-stats).

**Revert**: `git revert <s2 commit>` removes mirror-write feature-gated lines.

### Substage 3 — Switch reads from BranchCursor to CursorStore (ATOMIC SWITCH)

**Goal**: All READ sites pivot to `cursor_store` lookups; writes still also go to BranchCursor (for L4-style fallback safety). After this substage, BranchCursor is functionally redundant but not yet deleted.

**LOC budget**: ~1200 (every read site rewritten).

**Code paths touched**:
- `prattail/src/wpda_walker.rs:5002-7459` — every `cursor.visited_dispatch.contains(&key)` becomes `cursor_visited_dispatch_contains(&self.cursor_store, cursor_id, &key)`. Similar for all 6 heavy fields.
- `prattail/src/wpda_walker.rs:1815-?` (ConfigKey computation) — reads from cursor_store.
- `prattail/src/wpda_walker.rs:8659` (merge_equivalent_cursors) — same.
- `prattail/src/cohort_lazy.rs:546-581` (materialize_branch_cursor) — reads from cursor_store, optionally returns the same BranchCursor (still dual-write).

**Welch-gate sample-arms**: full 7-arm panel.

**Welch falsifier**: Welch LOSS p<0.05 on any arm. **Predicted impact**: O(log32 N) im::OrdSet/HashMap reads instead of O(1) FxHashSet contains. Predicted slowdown: 5-15 % at chain_100 left-assoc. **Risk of REJECT is HIGH.** Mitigation: cache hot reads in MinimalCursorState (e.g., last-inserted visited_dispatch entry as a small inline buffer).

**Gauntlet falsifier**: 4134/0 + 18/0/6.

**pgmcp lifecycle**: 7-arm Welch + a NEW `experiment_open(title="Exp 15 S3 — Reads pivot to CursorStore", primary_metric="left_assoc_chain_100_wall_time_ms", lower_is_better=true, acceptance_criterion={"type":"welch_t","alpha":0.05,"tail":"less","min_effect":{"kind":"cohens_d","threshold":0.0}})`.

**Substage falsifier**: ANY Welch LOSS at p<0.05 on any of the 7 arms → REVERT.

**Pre-gate prediction**: chain_100 LEFT-assoc 9.7 s → 10.5-11.2 s (HAMT read overhead). chain_500 LEFT-assoc walker peak 4.87 GB → 4.87 GB (no memory change yet; dual-write still active). If chain_100 wall > 14.5 s, off-by-3× falsifier triggers.

**Memory experiment**: chain_10000 RSS rate unchanged (dual-write still active — no memory release until S4).

**Revert**: `git revert <s3 commit>` restores reads from BranchCursor.

### Substage 4 — Delete BranchCursor heavy fields (THE MEMORY WIN)

**Goal**: Delete the 6 heavy fields from BranchCursor (`recovery_deltas`, `visited_dispatch`, `visited_recovery`, `optional_scope_marks`, `binder_scope_marks`, `lex_fork_path`). BranchCursor shrinks to ~MinimalCursorState size (~96 B). Stop dual-writing; CursorStore is sole source of truth.

**LOC budget**: ~800 (mostly removal — net negative).

**Code paths touched**:
- `prattail/src/wpda_walker.rs:1136-1507` — delete fields, derive Clone/Debug etc.
- `prattail/src/wpda_walker.rs:5736-6639` — Fork-arm child construction no longer copies the 6 heavy fields.
- `prattail/src/cohort_lazy.rs` — CohortShell no longer Arc-wraps the 6 heavy fields; they're CursorStore-resident.

**Welch-gate sample-arms**: full 7-arm panel.

**Welch falsifier**: Welch LOSS p<0.05 on any arm.

**Gauntlet falsifier**: 4134/0 + 18/0/6.

**pgmcp lifecycle**: 7-arm Welch + memory experiment.

**Substage falsifier**: Welch ANY-arm LOSS p<0.05 → REVERT.

**Pre-gate prediction**: chain_100 LEFT-assoc 10.5-11.2 s (S3 baseline) → 9.0-10.0 s (cheaper Fork clones offset the HAMT read overhead). chain_500 LEFT-assoc walker peak 4.87 GB → **1.0-1.5 GB** (5× reduction — the LOAD-BEARING memory drop). If chain_500 walker peak > 4.0 GB, off-by-3× falsifier triggers (S4 must be re-designed).

**Memory experiment**: chain_10000 RSS rate from 3.4 GB/min to **0.8-1.2 GB/min**, projected to complete in ~6-9 min within 24 GB. If observed rate > 3.6 GB/min, falsifier triggers.

**Revert**: `git revert <s4 commit>` restores BranchCursor heavy fields.

### Substage 5 — apply_action_to_cursor → CPS continuation queue

**Goal**: Replace the recursive `apply_action_to_cursor → ... → step_fanout` driver with the explicit Continuation queue. step_fanout becomes "drain queue until barrier; run merge; re-seed". 8.22 M apply_action calls become 8.22 M dequeues.

**LOC budget**: ~1500 (significant restructuring).

**Code paths touched**:
- `prattail/src/wpda_walker.rs:5002` (`apply_action_to_cursor`) — rewritten as `process_continuation_apply(&mut self, cursor_id, action, tokens) -> ContinuationOutcome<W>`.
- `prattail/src/wpda_walker.rs:7618` (`step_fanout`) — rewritten as `drive_until_barrier`.
- `prattail/src/wpda_walker.rs:5736-6639` (Fork-arm) — enqueues Continuation::Step per child (per §3.6).

**Welch-gate sample-arms**: full 7-arm panel.

**Welch falsifier**: Welch ANY-arm LOSS p<0.05.

**Gauntlet falsifier**: 4134/0 + 18/0/6.

**pgmcp lifecycle**: 7-arm Welch + memory experiment.

**Substage falsifier**: Welch LOSS p<0.05 → REVERT. CRITICAL: this substage is the most likely to regress, because the queue/dequeue overhead may exceed the saved per-cursor cost. Mitigation: instrument queue ops as part of S0 to pre-validate.

**Pre-gate prediction**: chain_100 LEFT-assoc 9.0-10.0 s (S4 baseline) → 8.5-10.0 s (similar; CPS overhead amortized over saved per-cursor work). chain_500 LEFT-assoc walker peak 1.0-1.5 GB (S4 baseline) → 1.0-1.5 GB (no further memory change since CursorStore is already source-of-truth). If chain_100 wall > 30 s, off-by-3× falsifier triggers.

**Memory experiment**: chain_10000 RSS rate 0.8-1.2 GB/min → 0.8-1.2 GB/min (no change). Falsifier: rate > 3.6 GB/min.

**Revert**: `git revert <s5 commit>` restores recursive driver. CursorStore and dual-read path preserved from S3.

### Substage 6 — Cohort generalization + L3.4 graduation

**Goal**: Generalize the L1-L6 cohort machinery atop CursorStore + Continuation queue. Graduate `DivergenceClass::classify` Push/Pop/ConsumeAndPush to ObsInvariant when EdgeKind is convergent (replicated-conjuring-turtle.md Intervention B, viable atop CPS).

**LOC budget**: ~600.

**Code paths touched**:
- `prattail/src/cohort_lazy.rs:313` — `classify_with_edge_kind`.
- `prattail/src/cohort_lazy.rs:608-624` — `apply_obs_invariant_to_shell` extended to Push/Pop/ConsumeAndPush.
- `prattail/src/wpda_walker.rs:7460-7510` (`step_cohort_frame`) — enqueues ShellApply continuations.
- `prattail/src/cohort_lazy.rs` `MAX_COHORT_FRAME_MEMBERS` raised 256 → 1024.

**Welch-gate sample-arms**: full 7-arm panel.

**Welch falsifier**: Welch ANY-arm LOSS p<0.05.

**Gauntlet falsifier**: 4134/0 + 18/0/6.

**pgmcp lifecycle**: 7-arm Welch + memory experiment + `cohort_cursors_emitted_reduction_rate` experiment.

**Substage falsifier**: Welch LOSS p<0.05 OR cohort_cursors_emitted reduces by < 30 % on left_assoc_500 → REVERT.

**Pre-gate prediction**: chain_500 LEFT-assoc cohort_cursors_emitted 28.9 M → 8-15 M (50-70 % reduction). chain_500 LEFT-assoc walker peak 1.0-1.5 GB → 0.4-0.8 GB. chain_10000 RSS rate 0.8-1.2 GB/min → 0.3-0.6 GB/min, projected to complete in ~3-6 min within 24 GB. If chain_500 walker peak > 4.0 GB, off-by-3× falsifier triggers.

**Memory experiment**: chain_10000 RSS rate as above.

**Revert**: `git revert <s6 commit>` restores conservative DivergenceClass.

### Substage 7 — chain_10000 #[ignore] removal (the prize)

**Goal**: Remove `#[ignore]` from `test_left_assoc_chain_10000` and `test_right_assoc_chain_10000`. Tramp gauntlet becomes 20/0/4 (or 20/0/3 if test_left_assoc_chain_5000 + 2000 also pass).

**LOC budget**: ~30 (annotation removal + docstring update).

**Code paths touched**:
- `languages/tests/trampoline_tests.rs:179-194` (left_assoc_chain_10000 ignore).
- `languages/tests/trampoline_tests.rs:162-171` (right_assoc_chain_10000 ignore).
- Optionally `test_left_assoc_chain_500/1000/2000/5000` un-ignore.

**Welch-gate sample-arms**: full 7-arm panel (regression guard).

**Welch falsifier**: any-arm REGRESS.

**Gauntlet falsifier**: 4134/0 + 20/0/4 (the new target).

**pgmcp lifecycle**: 7-arm Welch (regression guard) + memory experiment proves chain_10000 completes within 24 GB AND within reasonable wall-time (< 60 min per Welch sample).

**Substage falsifier**: chain_10000 OOM or wall > 60 min → REVERT (and revert S6/S5/S4 progressively until passing).

**Pre-gate prediction**: chain_10000 LEFT-assoc completes in 20-40 min wall with peak RSS 8-16 GB. If wall > 120 min or RSS > 24 GB, off-by-3× falsifier triggers.

**Memory experiment**: chain_10000 completion documented.

**Revert**: `git revert <s7 commit>` re-ignores. Lower-level substages remain.

## 6. Memory falsifier (per substage)

Per the user mandate: SEPARATE pgmcp experiment per substage with the chain_10000 RSS rate as primary_metric.

```python
mcp__pgmcp__experiment_open(
    title=f"Exp 15 S{n} — chain_10000 RSS gate",
    question="Does Substage K reduce chain_10000_rss_gb_per_min below the previous substage's measurement?",
    hypothesis=f"Substage {n} reduces chain_10000 LEFT-assoc RSS rate.",
    primary_metric="chain_10000_rss_gb_per_min",
    unit="GB/min",
    acceptance_criterion={
        "type": "welch_t",
        "alpha": 0.05,
        "tail": "less",
        "min_effect": {"kind": "cohens_d", "threshold": 0.0},
    },
    lower_is_better=True,
    kind="optimization",
    anchor_paths=[
        "prattail/src/cps_walker.rs",
        "prattail/src/cursor_store.rs",
        "prattail/src/wpda_walker.rs",
        "prattail/src/cohort_lazy.rs",
    ],
    git_ref="<tip>",
    hardware={"host":"arch-workstation","ram_gb":...},
)
```

Sample-collection procedure per arm (N=3-5 RSS-curve runs):

```bash
systemd-run --user --scope -p MemoryMax=24G \
  ./target/release/deps/trampoline_tests-XXXX \
  --ignored --exact test_left_assoc_chain_10000 \
  --nocapture
# Capture peak RSS via:
journalctl --user -u run-XXXX.scope --no-pager | grep "MaxRSS"
# Capture wall via /usr/bin/time -v.
# Compute GB/min: peak_RSS_gb / wall_min.
```

Submit samples per `mcp__pgmcp__experiment_record_measurement`, decide via `mcp__pgmcp__experiment_decide`.

A substage ACCEPTs iff the Welch wall-time panel AND the memory experiment both ACCEPT. Either REJECT triggers `git revert <substage>`.

## 7. Per-substage memory + time prediction (mandated by replicated-conjuring-turtle.md)

| Sub | chain_500 LEFT walker peak | chain_100 LEFT wall | chain_10000 trajectory |
|---|---|---|---|
| Baseline (734ceb7) | 4.87 GB | 9.7 s | OOM at 24 GB in ~7 min |
| S0 (diagnostics) | 4.87 GB | 9.7 s | OOM unchanged |
| S1 (dead scaffold) | 4.87 GB | 9.7 s | OOM unchanged |
| S2 (mirror-write, feature-gated) | 4.87 GB | 9.7 s (prod) | OOM unchanged |
| S3 (reads pivot) | 4.87 GB | 10.5-11.2 s | OOM unchanged (no memory release; reads only) |
| **S4 (BranchCursor delete)** | **1.0-1.5 GB** | 9.0-10.0 s | RSS 0.8-1.2 GB/min, completes in 6-9 min |
| S5 (CPS queue) | 1.0-1.5 GB | 8.5-10.0 s | unchanged |
| S6 (cohort graduation) | 0.4-0.8 GB | 8.0-9.5 s | RSS 0.3-0.6 GB/min, completes in 3-6 min |
| S7 (un-ignore chain_10000) | 0.4-0.8 GB | 8.0-9.5 s | completes in 20-40 min wall, peak 8-16 GB |

Off-by-3× falsifier triggers if any measured value exceeds the predicted by 3×. E.g., S4 with measured chain_500 walker peak > 4.0 GB → S4 design failure, revert.

## 8. Risk register

| # | Risk | Probability | Impact | Mitigation | Detection |
|---|---|---|---|---|---|
| 1 | im::OrdSet HAMT read overhead exceeds Arc::contains, causing Welch LOSS at S3 | HIGH | Substage REJECT | Pre-instrument hot reads at S0; cache last-N reads in MinimalCursorState | Welch on S3 |
| 2 | Lineage-chain `contains` walk too deep at chain_10000, becomes O(N²) | MEDIUM | Substage REJECT | Flatten chains at merge boundaries; cap chain depth at 8 | Welch + chain_10000 wall |
| 3 | Fork-arm CursorId alloc allocates faster than retire, fragmenting MinimalCursorState Vec | MEDIUM | Memory bloat | Free-list recycle; if free-list empty, allocate from end | walker-stats `cursor_id_alloc_rate` counter |
| 4 | im::HashMap insert overhead on persistent map dominates at chain_10000 | MEDIUM | Wall regression | Use im 15's "make_mut" eager-fork policy carefully; benchmark per substage | S5/S6 Welch |
| 5 | merge_equivalent_cursors over Vec<CursorId> mis-orders ties (tiebreak chain link 4) | LOW | Test regression | Preserve source_priority on MinimalCursorState; merge unit tests | Gauntlet 4134/0 |
| 6 | Cohort generalization (S6) breaks L3.6 force_materialize invariant at safety nets | MEDIUM | Gauntlet break | Force_materialize re-implemented over CursorStore; assertion-heavy debug build | Gauntlet |
| 7 | CPS queue exhausts memory at S5 due to over-eager Fork enqueue | LOW | OOM at non-chain workloads | Cap queue capacity at 1M (the walker-global cursor count is bounded) | walker-stats `queue_max_depth` |
| 8 | Continuation::ApplyAction Fork branches Vec heap-alloc dominates | LOW | Memory bloat | Per §3.6, Fork-arm doesn't carry branches in Continuation; it enqueues per-branch directly | S0 size sample |
| 9 | Soundness violation: lex_fork_path reads return wrong values post-Fork | LOW | Silent disambiguation bug | Dual-write through S3 lets debug_asserts catch parity violations | walker-stats `mirror_parity_violations` |
| 10 | im 15 not pinned to a stable version; future cargo update breaks API | LOW | Build break | Pin `im = "=15.x.y"` in Cargo.toml | CI build |
| 11 | The implementation effort exceeds estimates (15K LOC walker + 1500 new) | HIGH | Multi-week timeline | Substage independence allows partial wins; S4 alone may close chain_10000 | Sprint retrospective |
| 12 | Soundness proof obligation (§2.4) not discharged → walker accepts wrong inputs | LOW | Catastrophic | Property-test suite at each substage; gauntlet 4134/0 is the empirical falsifier | Gauntlet |

## 9. Rollback strategy

| Substage | Rollback command | Cascading effect |
|---|---|---|
| S0 | `git revert <s0_hash>` | Removes diagnostics only; S1-S7 unaffected |
| S1 | `git revert <s1_hash>` | Removes 3 new module files + lib.rs entries; S2-S7 would lose their dep |
| S2 | `git revert <s2_hash>` | Removes mirror writes; S1 still in tree (dead scaffold) |
| S3 | `git revert <s3_hash>` | Restores reads from BranchCursor; mirror writes (S2) still active; **walker behavior identical to pre-S2 in production builds** |
| S4 | `git revert <s4_hash>` | Restores 6 heavy fields on BranchCursor; mirror writes still active (S2); reads still via CursorStore (S3) — this is a viable state |
| S5 | `git revert <s5_hash>` | Restores recursive `apply_action_to_cursor`; S4 (lean BranchCursor) still in tree |
| S6 | `git revert <s6_hash>` | Restores conservative DivergenceClass; S5 (CPS queue) still in tree |
| S7 | `git revert <s7_hash>` | Re-ignores chain_10000; lower substages preserved |

For multi-substage compositions: if S6 REJECTs but S5 ACCEPTed and S4 ACCEPTed, revert ONLY S6. If S5 REJECTs in isolation but S4 ACCEPTed, revert ONLY S5 — S4's memory win is preserved.

## 10. Out-of-scope deferrals + comparison to prior REJECTs

| Prior REJECT | What it tried | Why CPS is structurally different |
|---|---|---|
| H2 (Arc-CoW incoming_edge_stack, -6.9 % chain_100) | Added Arc layer UNDER per-cursor Vec | CPS REMOVES per-cursor Vec entirely; replaces with persistent global. H2 paid Arc::make_mut cost per mutation; CPS pays HAMT O(log32) cost per mutation but shares ALL unchanged data. Different layer. |
| H10 (span-memo cache, +15.6 % chain_200) | Memoized expensive computations | CPS doesn't memoize anything; it changes per-cursor representation. Different problem. |
| Exp 8 (VisitedSetArena<T> + LRU + FxHashSet, slowdown) | 3 indirections per access | CPS has 1 indirection (HAMT lookup keyed on (cursor_id, key)). LRU is absent. Different access pattern. |
| Exp 17 (cohort revive deferral, +44 % LEFT-assoc) | Deferred cohort revives to EOI | CPS doesn't defer; it changes per-cohort-cursor cost (76 B → 16 B). Cost is paid at step time, not amortized to EOI. Different mechanism. |
| Exp 18 S0 (EdgeKind coarse dedup, ratio 1.0003×) | Coarse arena keying | CPS doesn't change arena keying. The 70.7 % edge_stack_arena dominator persists structurally; CPS attacks the 23.3 % visited_dispatch dominator and the per-cursor BranchCursor cost (1.8 %), aiming for cumulative 5.3× reduction. Different dominator. |
| LogicT / green_thread integration | (Not yet attempted) | DEFERRED. Those infras are for different layers (CEK eval, constraint propagation). The walker doesn't need fair backtracking; FIFO suffices. |
| Newton's method / StarSemiring | (Not yet attempted) | DEFERRED. Closure problem, not relevant to chain workloads. |
| im::Vector for incoming_edge_stack (Stage 3.2, +22 GB) | Persistent vec for small u32 elements | CPS uses im::OrdSet for visited (24 B keys, sharing helps) and im::Vector for recovery_deltas (sparse, HAMT helps). Stage 3.2 failed because im::Vector's 512 B per inner node overwhelms small elements; CPS uses HAMT structures for LARGE state, not for small element streams. Different data shape. |

## 11. Multi-session execution plan

Total effort estimate: ~5000-7000 LOC across 8 substages.

**Session A** (~1 day): Substage 0 (diagnostics) + measurement.
- Substage 0: ~150 LOC, walker-stats instrumentation, ContinuationProjection struct.
- pgmcp experiment_open + record + decide for the continuation-size projection gate.
- Tip pickup: `734ceb7`.
- Plan-file ledger update: ledger gets row "Exp 15 Substage 0".

**Session B** (~1 day): Substage 1 (scaffold).
- New modules: cursor_id.rs (80 LOC) + cursor_store.rs (600 LOC) + cps_walker.rs (450 LOC).
- lib.rs additions.
- All-dead-code; Welch panel should pass trivially.
- pgmcp experiment for the 7-arm panel.
- Tip pickup: end of Session A.

**Session C** (~1 day): Substage 2 (mirror write under walker-stats feature).
- Walker mutator sites mirror to CursorStore under `#[cfg(feature = "walker-stats")]`.
- Debug_asserts validate parity in walker-stats build.
- Welch in production build (mirror writes inert).
- Tip pickup: end of Session B.

**Session D** (~1 day): Substage 3 (reads pivot).
- All reads switch to CursorStore (dual-write still active).
- HIGH RISK substage — pre-validate via Substage 0 data on hot-read frequency.
- Welch may REJECT; fallback: ship S3 with read-caching layer in MinimalCursorState.
- Tip pickup: end of Session C.

**Session E** (~1-2 days): Substage 4 (BranchCursor heavy-field delete) — THE LOAD-BEARING SUBSTAGE.
- Delete 6 heavy fields from BranchCursor; update Clone/Debug.
- All Fork-arm sites updated (15+ locations).
- Cohort_lazy.rs updated (CohortShell field deletions).
- THIS IS THE MEMORY WIN. Welch must hold; memory experiment must show RSS rate < 1.5 GB/min on chain_10000 LEFT-assoc.
- pgmcp 7-arm Welch + memory experiment.
- Tip pickup: end of Session D.

**Session F** (~1-2 days): Substage 5 (CPS queue replacement).
- Replace recursive driver with explicit queue.
- 2500-LOC rewrite of apply_action_to_cursor → process_continuation_apply.
- step_fanout → drive_until_barrier.
- Welch panel + memory experiment.
- Tip pickup: end of Session E.

**Session G** (~1 day): Substage 6 (cohort graduation + L3.4 Push/Pop/ConsumeAndPush invariant).
- DivergenceClass::classify_with_edge_kind.
- apply_obs_invariant_to_shell extended.
- 7-arm Welch + memory + cohort_cursors_emitted reduction experiment.
- Tip pickup: end of Session F.

**Session H** (~0.5 day): Substage 7 (un-ignore chain_10000).
- Annotation removal + docstring update.
- Run chain_10000 LEFT-assoc + RIGHT-assoc to verify pass.
- Update tramp gauntlet target to 20/0/4 (or higher if chain_5000/2000 also pass).
- pgmcp experiment for the wall-time + RSS of chain_10000.
- Tip pickup: end of Session G.

**Total: 7-9 working days**, comparable to prior multi-session L1-L6 effort (which shipped in a single intensive day at 2026-05-25 with 23 commits).

Each session's plan-file ledger update obligation: append the substage's result row to `prattail/docs/design/plans/chain-10000-experiments-ledger.md` AND record the pgmcp experiment_id for traceability.

## 12. Verification checklist (per session boundary)

```bash
# Always run after each substage commit:
cargo build --release -p mettail-prattail
cargo build --release -p mettail-prattail --features walker-stats
cargo test --release -p mettail-prattail --lib  # must be 4134/0
cargo build --release -p mettail-languages --tests
./target/release/deps/trampoline_tests-XXXX --skip chain_10000 --skip chain_5000 --skip chain_2000  # must be 18/0/6 (or 20/0/4 post-S7)

# Welch panel (7 arms, N=15 each, 3-warmup):
for w in left_assoc_chain_50 left_assoc_chain_100 left_assoc_chain_200 \
         right_assoc_chain_50 right_assoc_chain_100 right_assoc_chain_200 right_assoc_chain_1000; do
    hyperfine -N --warmup 3 --runs 15 \
        --export-json prattail/docs/design/plans/bench-data/exp15-s${N}-${w}.json \
        "./target/release/deps/trampoline_tests-XXXX --exact test_${w}"
done

# Memory experiment (3-5 RSS runs, 24 GB ceiling):
for run in $(seq 1 3); do
    /usr/bin/time -v systemd-run --user --scope -p MemoryMax=24G \
        ./target/release/deps/trampoline_tests-XXXX \
        --ignored --exact test_left_assoc_chain_10000 --nocapture \
        2> prattail/docs/design/plans/bench-data/exp15-s${N}-chain10000-run${run}.time
done

# pgmcp lifecycle (Welch decision):
# python3 -c "..."  # NOT manual — use mcp__pgmcp__experiment_record_measurement + experiment_decide.
```

## 13. Comparison + compose-or-replace with Exp 14 Tomita per-arc

**Exp 14** (Tomita per-arc GSS-cursor merging, SKIPPED, ~3000+ LOC): eliminates the cohort revive mechanism entirely by merging cursors at GSS arc level rather than at cohort-cache level. The walker would maintain a per-GSS-arc cursor set; when N cursors arrive at the same `(node, pos, state)` via the same arc, they merge at the arc instead of being deferred to a cohort. The H12 dispatch_cohort_cache (~256 B per entry × 6000 entries) would be deleted or near-deleted.

**CPS / Exp 15**: rewrites the per-cursor representation. BranchCursor (512 B) → MinimalCursorState (96 B) + CursorStore-resident persistent state. CPS preserves the cohort_lazy machinery and extends it.

**How they relate**:
- Tomita per-arc attacks the *cursor population* dimension (reduces N).
- CPS attacks the *per-cursor cost* dimension (reduces B).
- Total memory = N × B. The two dimensions are orthogonal; reductions compose multiplicatively.

**Composition mechanics**:
- Tomita per-arc relies on GSS arc identity. CPS preserves GSS arc identity (no change to GssNodeId / GssEdgeId / EdgeStackId). They DO compose.
- Tomita per-arc would benefit from MinimalCursorState: per-arc cursor merge becomes O(arc_count × log32 N) instead of O(arc_count × N × visited_set_size).
- CPS Substage 6 (cohort generalization) leverages cohort_lazy's L1-L6 mechanics. If Exp 14 ships AFTER CPS S6, it can be redesigned to leverage the CPS continuation queue (each Tomita-merged set becomes a single Continuation::ShellApply).

**My recommendation** (defer final call to user):
- **Ship CPS first (S0-S7).** CPS is the more general win and addresses the visited_dispatch dominator (23.3 %) + per-cursor BranchCursor cost (1.8 %) + Fork-arm allocation cost (the 9.7 GB savings projection in §3.6). CPS S4 alone should close chain_10000.
- **If post-CPS chain_500 walker peak < 1.0 GB**, Exp 14 may be unnecessary. The remaining edge_stack_arena dominator (70.7 % of 4.87 GB = 3.44 GB, would proportionally drop to ~1.0-1.5 GB after CPS-driven reduction in cursor count) becomes the next attack target — and Exp 14 directly addresses it.
- **If post-CPS chain_500 walker peak > 2.0 GB but chain_10000 fits in 24 GB**, ship S7 (un-ignore) and defer Exp 14 to future work.
- **If post-CPS chain_10000 still OOMs**, ship Exp 14 next; its design should explicitly leverage CPS continuations.

**Either-or position**: NEVER. The two compose strictly.

---

## Critical Files for Implementation

- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/wpda_walker.rs` (15,378 LOC — Fork-arms 5736-6639, apply_action_to_cursor 5002, step_fanout 7618, BranchCursor 1136-1507, merge_equivalent_cursors 8659, allocate_fork_push_child 11099)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/cohort_lazy.rs` (800 LOC — CohortShell, CohortMemberState, DivergenceClass::classify 313, apply_obs_invariant_to_shell 608, materialize_branch_cursor 546)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/cesk_store.rs` (1675 LOC — the existing im::HashMap precedent at line 749, validates the persistent-data-structure pattern at scale)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/edge_stack_arena.rs` (~140 LOC) and `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/path_tree_arena.rs` (the working precedent for walker-global interning that already shipped under Plan D E3/E6)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/walker_stats.rs` (the diagnostic feature gate; EdgeKindProjection at line 406 retained per Exp 18 S0 closure)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/languages/tests/trampoline_tests.rs` (the Welch panel including left_assoc_chain_50/100/200/500/1000 and the two chain_10000 ignored tests at lines 162-200)
- `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/docs/design/plans/chain-10000-experiments-ledger.md` (849 LOC — append substage rows here; Exp 16 r3 attribution at ~700, Exp 18 S0 REJECT at ~792)
