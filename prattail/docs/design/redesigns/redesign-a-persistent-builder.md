# Redesign A — Persistent SemanticBuilder (Phase 5)

**Status:** SHIPPED in commits `1d53336` (5.1), `c40c6f1` (5.2), `4bf25af` (5.3), `870fe25`/`ee3dbc6` (5.4), `dab07d7` (5.5), `d6db5b2` (5.6), `5abce4f` (5.7), `d38cf12` (5.8 docs), `d0d637f` (5.6-tail-A), `0901d78` (5.6-tail-B), `0858489` (5.6-tail-C), `8ae3587` (5.6-tail-D), `82b8d5e` (5.6-tail-E), `084b83f` (5.6-tail-F), `35854c6` (5.6-tail-G).

**Branch:** `feature/wfst-architecture`.

**Plan ref:** `~/.claude/plans/phase-5-persistent-builder.md`.

---

## Terminology note

Pre-Phase-5 code used a `CursorMode { Lazy, Strict }` enum to gate the
walker's per-cursor mutation strategy. The names INVERTED standard CS
terminology:

- **`CursorMode::Lazy`** denoted IMMEDIATE direct mutation of `self.builder`
  (in standard CS, this would be called "eager").
- **`CursorMode::Strict`** denoted DEFERRED/JOURNALED mutation queued in
  `pending_builder_ops` and replayed later at `commit_winner` (in standard
  CS, this would be called "lazy").

The enum is DELETED post-Phase-5.6-tail-F; the replacement is a monotone
`WpdsWalker.deterministic: bool` flag (true at construction, false
after the first Fork, never reset). Throughout this document, when
describing the pre-tail design, references to `Lazy`/`Strict` are to
the deleted enum literals (with their unconventional meanings as above),
NOT to standard CS terminology. Post-tail discussion uses the standard
GLR/GLL parser-theory terms: **deterministic** (singleton cursor, no
Fork has happened, single parse path being explored) and
**nondeterministic** (multi-cursor, post-Fork, multiple parallel parse
paths exploring grammar ambiguity).

The Phase 5 changes do NOT alter the WPDS's inherently lazy step
evaluation (configurations are processed one event at a time, on
demand); they only change the per-cursor mutation-tracking mechanism
from journal-and-replay to persistent-Arc clone-on-write.

---

## Problem

Pre-Phase-5 the WPDS walker maintained TWO parallel representations of in-flight parse state:

1. **Live `self.builder: SemanticBuilder`** — mutated directly in Lazy mode (single cursor, pre-Fork).
2. **Per-cursor `BranchCursor.pending_builder_ops: Vec<BuilderDelta>`** — journaled in Strict mode (post-Fork, multi-cursor) and replayed onto `self.builder` at `commit_winner` after a winner was picked.

The dichotomy was managed by a `CursorMode { Lazy, Strict }` enum that gated every emit helper's dispatch. The architecture had three structural problems:

1. **Hack #7 prologue** at the Fork arm transferred live's open `collection_stack` slots into the parent cursor's mirror at the Lazy→Strict transition, journaling a `SeedLiveCollectionStack` delta so commit_winner could re-seed live before replay. ~50 LoC of subtle invariant management.
2. **Adoption gate** at commit_winner's start decided whether to donate the winner's `collection_stack` mirror to live (when SeedLive was absent AND no Strict-mode `StartCollection` delta covered the slots). ~30 LoC of conditional logic.
3. **21-variant `BuilderDelta` enum** with parallel emission + replay paths, plus a `consistency_memo` that tracked dry-run validity of the cursor's journal-replay. ~1500-1900 LoC of bookkeeping.

These contortions existed because clone-on-Fork was expensive (`O(N)` per cursor field). The journal-replay model was an optimization to avoid eagerly cloning the builder per Fork branch.

## Solution

Make `SemanticBuilder` **persistent** (immutable, structurally-shared) by switching its fields to `im::Vector<T>` (HAMT-backed persistent vectors). Wrap it in `Arc<SemanticBuilder>` on the cursor. Forks clone cheaply (`Arc::clone` = O(1) refcount bump); first-write triggers `Arc::make_mut` clone-on-write (`O(log N)` per modified HAMT path). The journal becomes unnecessary for non-recovery state — `commit_winner` installs the winner's Arc directly as the new live builder.

## Architecture

### Before (~Phase 4)

```
WpdsWalker {
    builder: SemanticBuilder,                  // Lazy-mode mutation target
    cursor_mode: CursorMode { Lazy, Strict },  // dispatch gate
    branch_cursors: Vec<BranchCursor>,
}

BranchCursor {
    pending_builder_ops: Vec<BuilderDelta>,    // journal (Strict)
    collection_stack: Vec<Vec<ActionArg>>,     // mirror (Strict)
    consistency_memo: Cell<Option<Option<bool>>>,
    collection_slots_allocated: u8,
    ...
}

BuilderDelta { 21 variants }
```

Emit dispatch:

```rust
fn emit_push_token(&mut self, cursor, kind, text, pos) {
    match self.cursor_mode {
        Lazy => self.builder.push_token(kind, text, pos),
        Strict => cursor.pending_builder_ops.push(
            BuilderDelta::PushToken { kind, text, pos },
        ),
    }
}
```

commit_winner replay loop:

```rust
for delta in winner.pending_builder_ops {
    match delta {
        BuilderDelta::PushToken {..} => self.builder.push_token(...),
        BuilderDelta::FireAction { symbol } => self.fire_action_for(symbol),
        BuilderDelta::FinalizeCollection {..} => self.builder.push_collection_slot(drained),
        BuilderDelta::SeedLiveCollectionStack {..} => self.builder.push_collection_slot(...),
        // ... 17 more arms
    }
}
```

### After (Phase 5 shipped)

```
WpdsWalker {
    builder: SemanticBuilder,                  // POST-commit / pre-Fork view
    cursor_mode: CursorMode { Lazy, Strict },  // kept for now (5.6-tail will delete)
    branch_cursors: Vec<BranchCursor>,
}

BranchCursor {
    builder: Arc<SemanticBuilder>,             // primary mutation target (Phase 5.2+)
    pending_builder_ops: Vec<BuilderDelta>,    // recovery-deltas-only audit log
    collection_stack: Vec<Vec<ActionArg>>,     // informational mirror
    visited_recovery: im::OrdSet<...>,         // O(log N) Arc-cloned (Phase 5.7)
    visited_dispatch: im::OrdSet<...>,
    ...
}

BuilderDelta { 19 variants — FinalizeCollection and SeedLiveCollectionStack deleted in 5.6 }

SemanticBuilder {
    stack: im::Vector<ActionArg>,              // HAMT-backed (Phase 5.1)
    binder_scopes: im::Vector<BinderHandle>,
    collection_stack: im::Vector<im::Vector<ActionArg>>,
    optional_stack: im::Vector<im::Vector<ActionArg>>,
    ...
}
```

Emit dispatch:

```rust
fn emit_push_token(&mut self, cursor, kind, text, pos) {
    // Phase 5.3: eager Arc::make_mut on cursor.builder.
    Arc::make_mut(&mut cursor.builder).push_token(kind.clone(), text.clone(), pos);
    match self.cursor_mode {
        Lazy => self.builder.push_token(kind, text, pos),
        Strict => cursor.pending_builder_ops.push(
            BuilderDelta::PushToken { kind, text, pos },  // audit log; replay is no-op
        ),
    }
}
```

emit_fire_action (Phase 5.5):

```rust
fn emit_fire_action(&mut self, cursor, symbol) {
    match self.cursor_mode {
        Lazy => self.fire_action_for(symbol),       // on self.builder (pre-5.5)
        Strict => {
            let builder_mut = Arc::make_mut(&mut cursor.builder);
            // EAGERLY fire the action_fn on cursor.builder. Required so
            // subsequent SpliceIntoCollection emits move the CONVERTED
            // term (e.g. Proc::CastInt(0)), not the raw arg (Int "0"
            // literal).
            if let Some(message) = fire_action_for_on_builder(&engine, builder_mut, symbol) {
                cursor.inner_state = Error { message };
                self.state = Error { message };
                return;
            }
            cursor.pending_builder_ops.push(FireAction { symbol });  // audit only
        }
    }
}
```

commit_winner install (Phase 5.5):

```rust
fn commit_winner(&mut self, winner_idx: usize) {
    let winner = self.branch_cursors.swap_remove(winner_idx);
    // ...
    if self.cursor_mode == CursorMode::Strict {
        // Phase 5.5: replace live with winner's Arc.
        self.builder = Arc::try_unwrap(winner.builder)
            .unwrap_or_else(|arc| (*arc).clone());
    }
    // Replay loop is now Recovery-only.
    for delta in winner.pending_builder_ops {
        match delta {
            BuilderDelta::RecoveryEvent {..} => self.recovery_events.push(...),
            BuilderDelta::SubstituteToken {..} => self.mutable_token_source.substitute_token(...),
            BuilderDelta::InsertToken {..} => self.mutable_token_source.insert_token(...),
            BuilderDelta::CommitLexAlternative {..} => self.mutable_token_source.commit_alternative(...),
            BuilderDelta::ApplyRecoverySequence {..} => /* multi-step token-source mutation */,
            // All other variants: NO-OP (eager apply already happened on cursor.builder).
            _ => {}
        }
    }
    // Post-commit singleton inherits winner.builder.
    self.branch_cursors = vec![BranchCursor { builder: winner.builder, ... }];
}
```

## Sub-phase log

### 5.1 (`1d53336`) — SemanticBuilder field migration

- `stack`, `binder_scopes`, `collection_stack`, `optional_stack` → `im::Vector`.
- Public API signatures unchanged (internal bridge `into_iter().collect()` for `Vec<T>`-returning methods).
- `#[derive(Clone)]` added to enable `Arc::make_mut` later.
- ~140 LoC in `wpds_runtime.rs`.

### 5.2 (`c40c6f1`) — `BranchCursor.builder: Arc<SemanticBuilder>` field

- Added at all 17 BranchCursor construction sites: `seed_from_live` (fresh Arc), `fork_child` (Arc::clone from parent), all 10 Fork-arm literals, write-back / Drop / commit_winner post-singleton literals.
- `BranchCursor::clone` uses `Arc::clone`.
- `ConfigKey` unchanged — builder is per-cursor working state, not a merge key.
- ~124 LoC.

### 5.3 (`4bf25af`) — emitter helpers eagerly mutate cursor.builder

- 12 of 14 emit helpers prefixed with `Arc::make_mut(&mut cursor.builder).<method>(...)` before the existing Lazy/Strict dispatch.
- `emit_fire_action` and `emit_end_binder_scope` (latter doesn't exist as a standalone helper) deferred to 5.5.
- Semantically idempotent at 5.3 — cursor.builder was write-only.
- ~54 LoC.

### 5.4 (`870fe25` / `ee3dbc6`) — Hack #7 prologue deletion (decoupled from 5.5)

- Deleted the Lazy→Strict prologue's `take_collection_stack` + `SeedLiveCollectionStack` journal emission (~50 LoC).
- cursor.builder via Arc::clone of parent already carries pre-fork state structurally — no explicit transfer needed.
- `FinalizeCollection` confirmed DEAD (defined + replayed but never emitted; emission dropped in `ba6f24f`). Without FinalizeCollection emissions, the SeedLive replay's "live empty at seed" assertion is unreachable, so 5.4 can land cleanly without 5.5's install.
- Kept `cursor_mode = Strict` transition (still gates emit-helper dispatch).
- Plan-agent–validated principled decoupling resolved the user's "coupling is a code smell" concern.

### 5.5 (`dab07d7`) — commit_winner install + eager fire_action

- `commit_winner` installs `winner.builder` over `self.builder` in Strict mode via `Arc::try_unwrap` (with deep-clone fallback).
- `emit_fire_action` Strict path eagerly fires the action_fn on `cursor.builder` via `Arc::make_mut` — required so subsequent SpliceIntoCollection emits move the action's converted term (not the raw arg).
- `emit_start_collection` returns `Arc::make_mut(&mut cursor.builder).start_collection()`'s id as authoritative (post-Phase-4-#5b the cursor.collection_stack mirror diverges from cursor.builder.collection_stack on binder-internal CollectionMarker pop). Fixed a multi-slot rule bug where slot IDs collided.
- `apply_pop_body_to_cursor`'s splice-gate `acc_id` uses `cursor.builder.collection_stack_len() - 1`.
- 5 Fork-arm sites + `WpdsStepAction::AdvanceWithEffect` eagerly apply effects via the new static helper `apply_effect_to_builder`. Required for Class-3 BinderListLoop bootstrap effects ([StartCollection, PushCollectionId, StartBinderScope, EndBinderScope]) and Class-3 inner-walk SpliceIntoCollection.
- `cursor_resolution_check` returns `Drop` for cursors in `Error` state so all-dropped propagates to walker.
- `apply_pop_body_to_cursor`'s tail `set_cursor_inner_state` guarded by `!cursor.inner_state.is_terminal()` — preserves emit_fire_action's eager-fire Error.
- `fire_action_for` rewritten as a thin wrapper around the new static `fire_action_for_on_builder(engine, &mut builder, symbol) -> Option<String>`.
- Adoption gate (Phase 4 #1 strict_alloc_count / has_seed_live) deleted (~30 LoC).
- All non-recovery `BuilderDelta` replay arms in commit_winner are no-ops.
- Unit test `commit_winner_state_overwrite_on_action_arity_underflow` updated for the new eager-fire timing.
- ~228 LoC added, ~76 LoC deleted (net +152 LoC; deletions in 5.6/5.7 outweigh this).

### 5.6 (`d6db5b2`) — delete dead BuilderDelta variants

- `BuilderDelta::FinalizeCollection` deleted (never emitted; dropped in `ba6f24f`).
- `BuilderDelta::SeedLiveCollectionStack` deleted (never emitted after 5.4).
- Net −75 LoC.

The remaining 14 non-recovery variants (PushToken, PushIdent, …) are still emitted by emit helpers + Fork-arm action_kinds as audit logs. A follow-up sub-commit can delete them along with their emission sites once the Lazy/Strict `CursorMode` is replaced by an "always cursor.builder eager" model. That's a larger refactor; kept separate.

### 5.7 (`5abce4f`) — visited sets to im::OrdSet

- `BranchCursor.visited_recovery` and `visited_dispatch` migrated from `BTreeSet<(usize, u16, u8)>` to `im::OrdSet<(usize, u16, u8)>`.
- Clone goes from `O(N)` to `O(log N)` Arc-bump — important since both sets are cloned at every Fork (~13 sites).
- API parity (insert / contains / iteration) — no call-site changes.

### 5.8 — initial doc (this file's earlier revision)

### 5.6-tail-A (`d0d637f`) — delete consistency_memo + DryRunState + cursor consistency override

- `DryRunState` + `DryRunBrokenKind` enums deleted (~30 LoC).
- `cursor_dry_run_state` (~155 LoC), `cursor_will_produce_term` (~18 LoC), `cursor_committed_ops_consistent` (~18 LoC) deleted — all derived from the B13d-R virtual-stack simulation.
- `BranchCursor.consistency_memo` field + ~30 init/clone/set sites deleted.
- B13d-R consistency-override blocks in `merge_equivalent_cursors` and `subsume_lex_dominated_cursors` deleted (broken cursors transition to `WpdsState::Error` at eager-fire time and are filtered by `cursor_resolution_check :: Drop`; the override is unreachable).
- Added `SemanticBuilder::is_accepting_terminal()` (~29 LoC) — direct shape check on cursor.builder, replaces the dry-run.
- Net −475 LoC.

### 5.6-tail-B (`0901d78`) — unify Lazy/Strict in 14 emit helpers + post-step Arc-install

- 14 emit-helper `match cursor_mode { Lazy => …, Strict => … }` blocks deleted (~150 LoC). Single eager `Arc::make_mut(&mut cursor.builder).<method>(...)` call.
- `debug_flush_lazy_invariant` debug check + call deleted (~20 LoC).
- `emit_fire_action` always eagerly fires on cursor.builder (~30 LoC of mode-split deleted).
- `emit_start_collection` Lazy/Strict paths collapsed.
- `apply_pop_body_to_cursor` CollectionMarker drain becomes unconditional.
- `commit_winner_at_eoi` always installs winner.builder (Strict-only guard deleted).
- Post-step install added in `apply_action`'s Alive/Resolved outcome (`self.builder = (*cursor.builder).clone()`, gated on `cursor_mode == Lazy`).
- Install added in `resolve_at_end_of_input` Lazy fast-path.
- `set_cursor_inner_state` kv_phase reader routed through `cursor.builder.collection_slot_len`.
- `apply_pop_body_to_cursor` acc_id derivation routed through `cursor.builder.collection_stack_len`.
- Net −113 LoC.

### 5.6-tail-C (`0858489`) — delete Fork-arm Lazy-mirror guards + Hack #7 prologue residue

- Hack #7 prologue + Phase 5.5 cursor.builder refresh deleted (~60 LoC).
- 16 Fork-arm `if cursor_mode == Lazy { self.pos = child.pos; }` mirror guards deleted (~64 LoC). Post-Fork outer handler already mirrors `self.pos = first.pos`.
- Net −86 LoC.

### 5.6-tail-D (`8ae3587`) — gate Fork-arm effect journaling on is_recovery_delta; rename pending_builder_ops → recovery_deltas

- Added `WpdsWalker::is_recovery_delta(&BuilderDelta) -> bool` (~12 LoC).
- 6 Fork-arm "effect" journal pushes wrapped in the gate. Only recovery deltas land in `cursor.recovery_deltas`.
- `BranchCursor.pending_builder_ops` → `BranchCursor.recovery_deltas` (100+ touches).
- `fork_action_consume_and_replace_with_effect_logs_delta` test reshaped to observe binder scope on cursor.builder directly.
- Net +54 LoC (mostly from rename touches; gating itself is LoC-neutral).

### 5.6-tail-E (`82b8d5e`) — delete 9 dead BuilderDelta variants + apply_effect_to_builder arms + commit_winner no-op arms

- Deleted 9 variants: PushToken, PushIdent, PushPredicate, ExtendBinderScope, FireAction, PushToCollection, StartOptionalScope, FinalizeOptionalScopePresent, PushOptionalAbsent.
- 9 corresponding `Debug` impl arms, `apply_effect_to_builder` arms, `commit_winner` replay no-op arms deleted.
- `predicate_in_fork_branch_clone_path` test deleted (variant gone).
- BuilderDelta enum: 19 variants → 10 (5 codegen-effect + 5 recovery).
- Net −146 LoC.

### 5.6-tail-F (`084b83f`) — delete CursorMode enum; replace with monotone `deterministic: bool`

- `enum CursorMode { Lazy, Strict }` + its 12-line invariant docstring deleted.
- `WpdsWalker.cursor_mode: CursorMode` field deleted.
- `WpdsWalker::cursor_mode()` accessor deleted.
- Added `WpdsWalker.deterministic: bool` field + `WpdsWalker::deterministic() -> bool` accessor.
- 4 constructor initializations + 1 Fork-arm promotion + ~14 mode-agnostic helper guards updated.
- 6 unit tests reshaped to use `deterministic()` (test FUNCTION names also renamed: `phase4_lazy_*` → `phase4_deterministic_*`, `phase4_strict_*` → `phase4_nondeterministic_*`, `push_optional_group_at_one_*_in_lazy_mode` → `_in_deterministic_mode`, etc.).
- Net −3 LoC (deletion roughly offset by rename verbosity).

### 5.6-tail-G (`35854c6`) — delete BranchCursor.collection_stack + collection_slots_allocated mirrors

- `BranchCursor.collection_stack: Vec<Vec<ActionArg>>` field deleted (was a mirror of cursor.builder.collection_stack).
- `BranchCursor.collection_slots_allocated: u8` field deleted (was write-only post-Phase-5.5).
- 20+ struct-literal initializers + `seed_from_live`'s `live_collection_stack_depth` parameter dropped.
- `ConfigKey.collection_depth` / `merge_equivalent_cursors` shape-guard / `set_cursor_inner_state` kv_phase / `apply_pop_body_to_cursor` acc_id all routed through `cursor.builder.collection_stack_len`.
- BranchCursor field count: 13 → 10.
- Net −41 LoC.

### Cumulative Phase 5.6-tail delta

| Sub-commit | LoC delta |
|---|---|
| 5.6-tail-A | −475 |
| 5.6-tail-B | −113 |
| 5.6-tail-C | −86 |
| 5.6-tail-D | +54 |
| 5.6-tail-E | −146 |
| 5.6-tail-F | −3 |
| 5.6-tail-G | −41 |
| **Total** | **−810** |

Combined with Phase 5.1–5.7 (~−200 LoC net excluding 5.6-tail-A's
consistency_memo deletion which started here), the Phase 5 cleanup
delivers roughly the design's projected ~1000 LoC removal.

## What's NOT yet in scope

A future Phase 5.7+ could:

1. Drop `self.builder` entirely and route `take_dyn_result` through the
   surviving singleton cursor's `cursor.builder`. Would touch ~10
   accessor sites and the hang-dump snapshot path. Plan §3.1 estimates
   −200 LoC.
2. Benchmark the cumulative Phase 5 + 5.6-tail throughput vs the
   pre-Phase-5 tip (`286813e`) on `bench_rholang`. No regression
   expected (in fact a speedup on nondeterministic-mode parses since journal+replay
   is gone), but should be measured.
3. T4 SIGUSR1 hang-dump (~396 LoC, pre-existing pending).

## Verification

At every sub-phase commit:

- `cargo nextest run -p languages --test gen_calculator_op --test gen_rholang_op --test class2_binder_with_collection_smoke --test wpds_via_str_smoke --test gen_calculator_unit --test gen_rholang_unit --test class2_multi_collection_smoke --test class3_multi_collection_smoke --test class2_opt_collection_smoke --test class3_opt_smoke --test class2hashmapsmoke` → 2160-2161/2160-2161 PASS (count varies with gen_*.rs non-determinism).
- `cargo test -p prattail --lib` → 3969/3969 PASS.
- `cargo nextest run -p languages --test edge_case_tests --no-fail-fast` → 228/229 PASS (1 pre-existing `postfix_binds_tighter_than_unary` failure unrelated to Phase 5).

## Performance

The `im::Vector` HAMT has `O(log N)` per-operation cost vs `Vec`'s `O(1)`. For small N (typical SemanticBuilder stack depth in arithmetic / lambda / process-calc parses), this is a constant-factor slowdown. Mitigations:

- Arc structural sharing means clone (which used to be O(N) on `Vec<ActionArg>::clone`) is now O(1) refcount.
- Nondeterministic-mode parses no longer journal+replay 14 BuilderDelta variant types — the action / splice / push runs ONCE on cursor.builder, not twice (once at log, once at replay).
- Recovery-only journal is bounded by recovery_depth (default 5).

No benchmarks landed with Phase 5. A follow-up benchmark commit should measure the steady-state parse throughput against the pre-5.0 tip (`286813e`) on the `bench_rholang` suite.

## Acknowledgments

The Plan-agent–validated decoupling (5.4 alone, 5.5 alone) saved a large coupled refactor — credit to the user's "coupling is a dirty word" pushback for surfacing FinalizeCollection's dead-code status, which was the architectural lever.
