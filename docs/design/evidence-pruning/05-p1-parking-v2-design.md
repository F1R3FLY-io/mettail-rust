# EP-P1 parking v2 — implementation design

> Status: v2 REFUTED-AS-SPECIFIED (red-team Round 6: R6-1 the 16-member parking cap vs 3,311 on one key
> is FATAL; + R6-2..R6-8 mechanism corrections — see 03-red-team-ledger.md Round 6). The SPINE survives into v3 (member-tail-as-function, side-table wrap, host wrap_cat, orphan re-drive, member shapes). DO NOT IMPLEMENT v2.
> Supersedes the REFUTED v1 (04-p1-icommit-design.md). R5 corrections are binding inputs.

# EP-P1 CrossCatLhs Parking — v2 Implementation Plan (post-R5, binding)

Branch `feature/wfst-architecture` @ `a0fa001d`. The v2 M-commit (`CrossCatLhsParking.v`, 10 theorems) has landed; this plan implements the Rust to satisfy it. All line numbers below were re-verified against the working tree (they have drifted ~+76 lines from the v1 doc anchors; I cite the *verified* a0fa001d positions and pin every change to a **function anchor**).

## 0. Ground-truth corrections to the v1 inventory (verified this session)

The v1 doc's "two routes" table and mechanism inventory remain accurate. The hook *architecture* is replaced. Verified facts that drive v2:

- **The pop path is ONE function**: `Pop` (wpda_walker.rs:7021), `ConsumeAndPop` (7495, 7517), and the three Fork pop arms (8653/8742/8828) and the Substage-5 broadcast pops (9678/9849) **all** call `cursor_gss_pop_via_edge` then `apply_pop_body_to_cursor`. The entire CrossCatLhs post-pop tail (effective_state recompute 16228-16261; guarded reentry 16262-16285; ROOT-F splice-skip 16193-16196; D-strings re-sync 16319-16351; GroupingClose resolve 16371-16386) lives **inside `apply_pop_body_to_cursor`** — NOT in `cursor_gss_pop_via_edge`. This is the single-source-of-truth seam R5-1/R5-3 demand.
- **`revive_cohort_member_with_snapshot` (15741) is CrossCatProjection-shaped**: it re-pushes `CrossCatProjection` (15792) and sets `cursor.inner_state = snap.worker_inner_state` (15812). It re-derives NOTHING from the member's predecessor. Reusing it for CrossCatLhs is the refuted v1 broadcast (T3).
- **The snapshot does NOT need `worker_inner_state` for CrossCatLhs** (R5-3 exploitation, T2): the member tail is recomputed at the member's *own next pop* from the member's *own predecessor*. Verified: after a CrossCatLhs revive, the revived cursor must re-execute a Pop of `category_entry(source)` so that `apply_pop_body_to_cursor` runs its tail against the *member's* `pred_id`. So the parked payload stores only `(symbol_id, hi_pos)` (the BODY) — exactly as the model's `Body` record (`CrossCatLhsParking.v:120-123`).
- **`EpP1Mode` (wpda_walker.rs:111) ships with only `Off | Shadow`**; `on` warns + runs shadow (from_env 124-133). v2 adds `On`.
- **`EdgeKind` derives `PartialEq/Eq/Hash` (gss.rs:392)** and `add_edge_kind` (gss.rs:640, dedup at 649 `existing.kind == kind`) coalesces by the *compared* payload. Widening the compared `CrossCatLhs` payload changes GSS coalescing with the switch OFF (R5-2). `is_convergent` (gss.rs:540) **excludes** `CrossCatLhs` — it stays identity-strict.
- **Host vs source (R5-7)**: at the `PrefixDispatch` arm the host = `state_cat_src_idx = frontier_top.symbol.category_src_idx` (engine_impl.rs:387-389), and the arm guard pins it to `#category_src_idx` (prefix.rs:1297). The pushed symbol is `category_entry(source)` (prefix.rs:1313/1366). The Fork branch reads `branch.symbol.category_src_idx` = **source** (wpda_walker.rs:8076) — the trap.
- **The shadow half is live** at the `cursor_gss_push_with_kind` chokepoint (14549-14568), keyed `(pos, source, host_cat)` with `host_cat` recovered from the **predecessor** frame (14551-14555) — this is the worker host, and it's the substrate to flip.
- **Attribution memo (R5-4)**: `cast_then_infix_steps` (6810-6830) matches `CrossCatLhs` ONLY, never `CrossCatLhsReentry`.

---

## Part A — The side-payload carrier for `(wrap_cat, wrap_rule)` (R5-2, R5-7)

**Decision: a `GssEdgeId`-keyed side table on the walker, NOT manual Eq/Hash.** Justification:
- Manual `PartialEq`/`Hash` impls on `EdgeKind` that ignore the wrap fields would make `add_edge_kind`'s dedup (gss.rs:649) coalesce two CrossCatLhs edges that carry *different* wrap — but then `edge_kind(eid)` (gss.rs:663) returns whichever was inserted first, so the resolve site would read a STALE wrap for the second host. That silently re-introduces the M4 conflation (T8 cross-host-never-shares is violated at the read).
- A side table keyed by the edge's own `GssEdgeId` is read *only* at the resolve site, indexes the exact edge the cursor traversed, and leaves `EdgeKind`'s identity (and thus `add_edge_kind` coalescing, and the proven `test_wpds_gss_edge_identity_includes_edge_kind` gss.rs:1125) **byte-identical to OFF**. `CrossCatLhs` stays `{ source_src_idx: u16 }` unchanged in gss.rs — zero match-site churn, the 3 exact-bind sites (6621, 6976, 16262) keep compiling unchanged.

**Shape** (new field on `WpdaWalker`, wpda_walker.rs struct ~890 region, all 3 constructors ~3469/3551/3632, reset in the two per-parse resets ~3733/3827):
```rust
// EP-P1 v2: wrap (host) discriminator for CrossCatLhs edges, keyed by the
// edge's own GssEdgeId. READ-NOT-COMPARED (R5-2): EdgeKind identity is
// untouched, so add_edge_kind coalescing == OFF. Written at the push that
// creates a CrossCatLhs edge; read at the resolve site to reconstruct the
// widened DispatchKey. Only populated when ep_p1_mode == On.
crosscat_lhs_wrap: rustc_hash::FxHashMap<crate::gss::GssEdgeId, (u16, u16)>,
```
- **Write site**: `cursor_gss_push_with_kind` (14575 returns `edge_id`). Immediately after the `add_edge_kind` call, when `kind` is `CrossCatLhs` and mode `On`, insert `(edge_id → (wrap_cat, wrap_rule))`. The wrap is passed *in* from the caller (see Part C — the action arm computes the host).
- **Read sites (exact enumeration, R5-2)**:
  1. The new resolve block in `apply_pop_body_to_cursor` (Part D) — looks up the popped CrossCatLhs edge's `GssEdgeId` (available from `cursor_gss_pop_via_edge`'s returned `edge_id`, threaded through — see Part D.0).
  2. The orphan re-drive's key reconstruction (Part F) — reads the stored wrap for the parked member's edge.
  - No other reader. `wrap_cat`/`wrap_rule` never enter any `ConfigKey`, `EquivKey`, or `EdgeKind` comparison.

This refines the sharing key exactly as `CrossCatLhsParking.v` T8 (`wrap_partition_refines_sharing`) requires: the cohort `DispatchKey` carries `(wrap_cat, wrap_rule)`, but the read is keyed off the concrete edge so cross-host members land in distinct `DispatchKey` buckets and never share (T8b `cross_host_never_shares`).

---

## Part B — `EpP1Mode::On` and the divergent-share shadow counter

**B.1 — Add `On` to `EpP1Mode`** (wpda_walker.rs:112). `from_env` (122): map `Some("on") => On` (delete the warn-and-downgrade block 124-133). Keep `shadow => Shadow`.

**B.2 — New shadow counter `ep_p1_shadow_share_divergent_total`** (walker_stats.rs, beside `ep_p1_shadow_would_share_total:566`, same `[u64; WPDA_STATE_CLASS_COUNT*2]` dimensioning; default 2668; Display 2199-block).

**Design of `ep_p1_shadow_share_divergent_total`** (the integrity gate; MUST stay all-0): this is the *observable* witness for T2/T3. In `Shadow` mode, at the CrossCatLhs **resolve** point (the new block in `apply_pop_body_to_cursor`, gated to also run under Shadow), when a 2nd+ member would-share a body, compute what the **broadcast** tail (worker's `effective_state`/`reentry`) WOULD be and compare it to the **member's own** tail (recompute `effective_state(member_pred)` / `reentry_fires(member_pred)` from the member's stored predecessor kind). If they differ on either axis → increment. This makes T3's `worker_snapshot_broadcast_unsound` empirically measurable: a non-zero count means v1's broadcast would have corrupted that member. Partition index = `wpda_state_class(&cursor.inner_state) * 2 + recovery_enabled` (matching the shipped pattern at 14563-14566). Because v2 uses the member-tail revive (Part E), the *enforced* path can never produce a divergence — but the shadow counter proves the *member shapes carry enough predecessor info to detect it*, which is the soundness precondition for flipping On.

---

## Part C — The two member-construction shapes (R5-5)

Both producers register/pause/resolve against the SAME cohort cache and the SAME `DispatchKey`, but build the parked member differently. **They share the cache key; they do NOT share one helper that assumes Fork metadata.**

**C.0 — The shared cohort decision (key only, not member)**. A small helper that computes the key and consults the cache, returning an enum the caller acts on:
```rust
enum CrosscatLhsCohortAction<W> {
    Proceed,                       // this cursor is the worker; push as today
    Suppress,                      // FailedHit; drop
    Park { key: DispatchKey },     // InflightCollision; caller parks ITS OWN member shape
    ResolvedNow { key: DispatchKey, bodies: Vec<ResolvedHitBody<W>>, spawn_worker: bool },
}
fn crosscat_lhs_cohort_decision(
    &mut self, source_src_idx: u16, host_cat: u16, host_rule: u16,
    dispatch_pos: usize, worker_pre: W,
) -> CrosscatLhsCohortAction<W>
```
- `key = DispatchKey::new(dispatch_pos, source_src_idx, /*inner_cur_bp*/ 0, host_cat, host_rule)` — `inner_cur_bp = 0` is hard-coded at both emit sites (prefix.rs:1317/1376). `wrap_cat = host_cat`, `wrap_rule = host_rule` per R5-7.
- Calls `dispatch_cohort_cache.register(key, worker_pre)` and maps `WorkerInserted→Proceed`, `FailedHit→Suppress`, `InflightCollision→Park`, `ResolvedHit{bodies,spawn_worker}→ResolvedNow`.
- This helper has NO `lex_fork_stamp`/`trigger_terminal` in its signature — it cannot assume fork metadata (R5-5).

**C.1 — Singleton-arm member shape** (the `PushWithEdgeKind` action arm, wpda_walker.rs:6963, inside the existing `if let EdgeKind::CrossCatLhs { source_src_idx } = &edge_kind` block 6976):
- Host: recover from the **predecessor** frame, exactly as the shadow does — `self.gss.node(cursor.node).map(|n| n.symbol.category_src_idx)`. But we also need `host_rule`. The host *rule* is not on the CategoryEntry frame. **Use a per-arm-constant sentinel** for `wrap_rule` here: the singleton path fires from exactly one `(host_cat, source)` arm by construction (the arm guard `state_cat_src_idx == #category_src_idx`), so `host_rule` can be a fixed sentinel `u16::MAX` *as long as it is the same sentinel the resolve and orphan paths reconstruct*. Over-discrimination is safe (T8a); under-discrimination is the M4 failure. Since on the shipped grammars each `(host_cat, source)` has one CrossCatLhs arm (verified in the ledger: calc host=7 constant, rhocalc host=0), `(host_cat, u16::MAX)` is at least as discriminating as the host arm — sound.
  - **Cleaner alternative (preferred if codegen reach is acceptable):** thread `host_rule` from codegen. The singleton arm at prefix.rs:1301 has `#category_src_idx` (host) in scope but NOT a single host rule (the arm is per-*category*, shared across rules whose first-set contains the trigger). So a faithful host_rule does not exist at the singleton site — the sentinel is the correct choice. (This is precisely why R5-5 says the two producers differ.)
- Member shape: the singleton has no fork metadata, so build the member with a **plain parent clone**:
```rust
let member = CohortMember {
    member_id: self.dispatch_cohort_cache.allocate_member_id(),
    return_frame: cursor.clone(),     // pre-push cursor; NO fork stamp/trigger
    weight_at_dispatch: cursor.weight.times_ref(&weight),
};
```
- On `Park`: `pause_cohort_member(key, member)`; record the parked member's predecessor kind into the side payload for divergence-shadow + orphan re-drive (Part F stores it). Return `CursorOutcome::Drop` (Suppress the push).
- On `Proceed`: write `crosscat_lhs_wrap[edge_id] = (host_cat, u16::MAX)` after the push; continue (this cursor is the worker).
- On `ResolvedNow`: revive via the **dedicated** `revive_crosscat_lhs_member` (Part E), once per body × snapshot, mirroring the structure of allocate_fork_push_child's ResolvedHit arm (15378-15475) but with the singleton plain member shape and the dedicated revive; `Drop` the original push.

**C.2 — Fork-path member shape** (the `PushCrossCatLhs` Fork arm at 8055-8117 → `allocate_fork_push_child` 15243). `allocate_fork_push_child` currently engages the cohort cache ONLY for `WpdaState::CrossCatDelegate` (15268). Add a sibling branch for the CrossCatLhs case (the branch's `new_state` is `PrefixDispatch{pos,cur_bp:0}` + `push_edge_kind == Some(CrossCatLhs)`):
- Host: `branch.symbol.category_src_idx` is the **SOURCE** (R5-7 trap) — do NOT use it for `wrap_cat`. The host must come from the **parent's GSS top**: `self.gss.node(parent.node).map(|n| n.symbol.category_src_idx)`. `host_rule = u16::MAX` sentinel (same reasoning as C.1; the Fork branch also lacks a single host rule).
- Member shape: build with `parent_frame_with_fork_metadata(parent, lex_fork_stamp, trigger_terminal.as_ref(), branch.symbol.category_src_idx, branch.symbol.rule_index_in_category)` (15583) — the Fork member CARRIES the lex-fork stamp + trigger terminal, exactly as the CrossCatDelegate members do (15322-15328). The richer ResolvedHit handling (immediate synth 15399-15430, future_member 15436-15450, spawn_worker overflow 15451-15474) is reused *with the dedicated CrossCatLhs revive substituted*.
- This branch shares the `DispatchKey` and the cache calls with C.1 but builds the member through the fork-metadata constructor — satisfying R5-5 ("share the cache key but not one helper that assumes fork metadata").

> **Why two shapes are mandatory, restated against the model:** `CrossCatLhsParking.v` treats `Member` as `{ member_id, member_pred }` (lines 113-116) — the model abstracts over *how* the member frame is built; both shapes are valid `Member`s as long as each carries its own predecessor kind. The singleton's plain clone and the Fork's metadata frame are two refinements of the same abstract `Member`; T2 (`parking_v2_eq_percursor`) holds for both because the revive (Part E) recomputes the tail from `member_pred` regardless of frame provenance.

---

## Part D — Factoring the single-source-of-truth member-tail function (R5-1, R5-3)

This is the core correction. The CrossCatLhs post-pop tail must be a **reusable function** that both the in-place pop path AND the revive call (Part E) invoke, so they cannot drift.

**D.0 — Thread the popped `GssEdgeId` into `apply_pop_body_to_cursor`.** Currently `cursor_gss_pop_via_edge` (16416) returns `(GssNodeId, Option<EdgeKind>)` and reads `edge_id` internally (16423). Change its return to `(GssNodeId, Option<EdgeKind>, Option<GssEdgeId>)` (or stash the popped `edge_id` on a scratch field) so the resolve block can key `crosscat_lhs_wrap`. Update the ~9 call sites (7037, 7495, 7517, 8200, 8653, 8742, 8828, 9678, 9849, 10078, 10110, 10113) — most ignore the 2nd return already (`let (x, _) = ...`); the Pop/ConsumeAndPop sites that forward into `apply_pop_body_to_cursor` thread the new value.

**D.1 — Extract `apply_crosscat_lhs_reentry_tail`** — factor out lines 16228-16386 of `apply_pop_body_to_cursor` (everything from `let mut effective_new_state = new_state;` through the `set_cursor_inner_state` at 16392) into:
```rust
/// The CrossCatLhs/CategoryEntry post-pop tail, derived ENTIRELY from the
/// MEMBER's own predecessor (pred_id) — NOT from any worker snapshot.
/// Single source of truth: called by the in-place Pop path AND by
/// revive_crosscat_lhs_member (R5-1). Returns the resolved next state and
/// whether the guarded reentry fired (for the divergence shadow).
fn apply_crosscat_lhs_reentry_tail(
    &mut self,
    cursor: &mut BranchCursor<W>,
    pred_id: GssNodeId,
    popped_edge_kind: Option<&EdgeKind>,
    popped_symbol: Option<StackSymbolV2>,
    new_state: WpdaState,
    tokens: &dyn WpdaTokenSource,
) -> (WpdaState /*resolved_new_state*/, bool /*reentry_fired*/)
```
The body is the **verbatim** existing logic:
- `effective_new_state` recompute from `self.gss.node(pred_id).map(|n| n.symbol.kind)` — the CategoryEntry→InfixLoop / GroupingMarker→Unwinding / None@NONE→InfixLoop / other→Unwinding branch (16228-16261). This is `effective_state(member_pred)` in the model (`CrossCatLhsParking.v:93-99`).
- The guarded reentry push (16262-16285): if popped is CrossCatLhs CategoryEntry ∧ `pred_id != NONE` ∧ effective_state ∈ {InfixLoop,Unwinding} → push `category_entry(source)` at `cursor.pos` (= `hi_pos`, the *body's* end) with `CrossCatLhsReentry`, set state InfixLoop{cur_bp:0}. This is `reentry_fires(member_pred)` (`CrossCatLhsParking.v:105-109`). Return `reentry_fired = (pred != NONE)` per the model's guard.
- The D-strings re-sync (16319-16351) and the GroupingClose resolve (16371-16386).
- The terminal `if !cursor.inner_state.is_terminal() { set_cursor_inner_state(...) }` (16391-16393) moves to the END of the factored function (or stays in `apply_pop_body_to_cursor` after the call — keep it in the caller so the function returns the *resolved* state and the caller commits it; this keeps the splice-skip ordering intact).

`apply_pop_body_to_cursor` then **calls** `apply_crosscat_lhs_reentry_tail` in place of the inlined block. The ROOT-F splice-skip at 16193-16196 stays where it is (it reads `popped_edge_kind` during the splice decision, which is *before* the tail) — but it is part of the member-specific behavior and is already keyed on `popped_edge_kind == CrossCatLhs`, so it is correct for both paths because the revive re-drives a real Pop (Part E).

**D.2 — The resolve hook lives INSIDE `apply_pop_body_to_cursor`, AFTER the reentry computation (R5-3).** This is the decisive R5-3 correction: the resolve cannot live in `cursor_gss_pop_via_edge` because the reentry state `InfixLoop{cur_bp:0}` is computed in `apply_pop_body_to_cursor`. Place the new resolve block immediately after the `apply_crosscat_lhs_reentry_tail` call, structured as the sibling of the CrossCatProjection resolve (16441-16542) but:
- Trigger: `popped_edge_kind == CrossCatLhs` ∧ mode ∈ {On, Shadow}.
- `symbol_id = sppf_stack_arena.top(cursor.sppf_stack_id)`; category guard `symbol_cat == source_src_idx` (mirror 16467).
- Reconstruct the FULL key from `dispatch_pos = node.pos` (the popped node's pos, read BEFORE mutation) + `crosscat_lhs_wrap[popped_edge_id]` for `(wrap_cat, wrap_rule)`.
- **Snapshot stores ONLY the body** (R5-3 simplification, T2): `WorkerSnapshot{ worker_inner_state: <ignored/Unwinding placeholder>, ... }` — but since the dedicated revive (Part E) does NOT read `worker_inner_state`, we exploit this by storing a benign value. To keep the existing `resolve()`/`take_pending_for_drain_all` plumbing reusable, pass a `WorkerSnapshot` whose `worker_inner_state` is set to the *recomputed reentry state* only so the existing terminal-state filter (10903, 15401) behaves — but the revive ignores it. (The clean alternative is a separate `CrossCatLhsBody{symbol_id, hi_pos}` carrier and a `pending_crosscat_lhs_drain_keys` set; see Part E.2.)
- On `FirstResolve | SnapshotAppended` → `pending_crosscat_lhs_drain_keys.insert(key)` (the NET-NEW set, Part E).
- **Shadow mode**: instead of mutating the cache, compute the divergence (Part B.2) and increment `ep_p1_shadow_share_divergent_total` if the broadcast tail ≠ member tail. Never touch the cache (shadow-inertness).

---

## Part E — The dedicated `revive_crosscat_lhs_member` (R5-1) + drain routing

**E.1 — `revive_crosscat_lhs_member`** — a NEW function, NOT a parameter tweak on `revive_cohort_member_with_snapshot`:
```rust
fn revive_crosscat_lhs_member(
    &mut self,
    member: CohortMember<W>,
    symbol_id: SppfId,
    hi_pos: usize,
    source_src_idx: u16,
    tokens: &dyn WpdaTokenSource,
) -> BranchCursor<W>
```
Body (re-derives the tail from the member's OWN predecessor — T2):
1. `let mut cursor = member.return_frame;` — the member's own pre-dispatch frame (its own `incoming_edge_stack`, `node`, builder, etc.).
2. Weight: `cursor.weight = member.weight_at_dispatch.times_ref(&self.sppf.symbol_weight_sum(symbol_id))` (mirror 15781-15782).
3. Push the body symbol onto the cursor's sppf_stack: `intern_push(cursor.sppf_stack_id, symbol_id)` (mirror 15787-15789).
4. `cursor.pos = hi_pos`.
5. **Re-push `category_entry(source)` with the `CrossCatLhs` edge** above the member's OWN predecessor (NOT CrossCatProjection):
   ```rust
   let edge_id = self.cursor_gss_push_with_kind(
       &mut cursor, StackSymbolV2::category_entry(source_src_idx),
       /*pos at the member's dispatch*/ cursor.node_pos_or_hi, W::one_ref(),
       EdgeKind::CrossCatLhs { source_src_idx });
   ```
   This recreates the exact pre-pop configuration the per-cursor flow had: a `CrossCatLhs` frame whose predecessor is the *member's* return context. The wrap side-payload for this new edge is irrelevant (it won't re-resolve into the cohort — see step 6).
6. Set `cursor.inner_state = WpdaState::Pop`-driving state so the **next walker step pops this frame**, at which point `apply_pop_body_to_cursor` → `apply_crosscat_lhs_reentry_tail` runs against the *member's own* `pred_id` and produces the member-specific tail (effective_state + guarded reentry + splice-skip + re-sync). Concretely: set the state to whatever drives an immediate Pop of the just-pushed CategoryEntry — i.e. `Unwinding` (the engine's CategoryEntry-pop arm emits `Pop` from `Unwinding`). The body is already on the sppf_stack, so the pop's splice/fire sees the resolved body.
   - **Reentry-guard satisfaction (verified, 16262-16271):** the revived pop has `popped.kind == CategoryEntry` ✓, `pred_id = member's predecessor != NONE` ✓ (parked members always have a return frame), `effective_new_state ∈ {InfixLoop, Unwinding}` ✓ (computed from the member's predecessor). So the reentry fires exactly when the member's own predecessor warrants it — and is REFUSED for a `PredNone` member (model T3 reentry axis).
7. Tag `cohort_origin`/`cohort_revive_depth` for ConfigKey bucketing (mirror 15770-15776, 15809-15811) using `equiv()`-narrow key (preserves the chain O(1) ceiling, M4).

**This is the mechanism that discharges T2.** The model's `member_tail_config m b = MkConfig (member_id m) (body_id b) (body_hi b) (effective_state (member_pred m)) (reentry_fires (member_pred m))` is realized exactly: the body `(symbol_id, hi_pos)` comes from the worker's one parse; the state/reentry come from re-driving the member's own pop.

**E.2 — Drain routing (NET-NEW, isolated from the CrossCatProjection drain).** Add a second per-step drain set `pending_crosscat_lhs_drain_keys: FxHashSet<DispatchKey>` (struct field + 3 constructors + 2 resets, mirroring `pending_cohort_drain_keys` at 1009/3486/3568/3649/3733/3827). Add a second drain loop immediately after the existing one (10876-end), running ONLY when `mode == On && !pending_crosscat_lhs_drain_keys.is_empty()`:
```rust
if self.ep_p1_mode == EpP1Mode::On && !self.pending_crosscat_lhs_drain_keys.is_empty() {
    let keys = std::mem::take(&mut self.pending_crosscat_lhs_drain_keys);
    for key in keys {
        for job in self.dispatch_cohort_cache.take_pending_for_drain_all(&key) {
            for _snap in &job.snapshots {           // body multiplicity (alternate_bodies)
                for m in &job.members {
                    let c = self.revive_crosscat_lhs_member(
                        m.clone(), job.symbol_id, job.hi_pos, key.source_src_idx, tokens);
                    self.branch_cursors.push(Frame::Concrete(c));
                }
            }
        }
    }
}
```
- Reuses `take_pending_for_drain_all` (1178) unchanged — it returns `CohortDrainJob{symbol_id, hi_pos, pos_at_dispatch, snapshots, members}`. We use `symbol_id`/`hi_pos`/`members`; `snapshots.len()` gives the body multiplicity (each alternate body resolved into its own job). The CrossCatProjection drain loop (10876) is **untouched** — empty set on cast-free inputs → byte-identical hot path.
- T5 (`parking_preserves_result_multiset`): one revived cursor per (body × member) preserves the per-cursor occurrence count exactly.

---

## Part F — The EOI orphan re-drive for CrossCatLhs cohorts (R5-6, T6/T7)

This is the hardest correction and has NO existing analog that works as-is. The shipped `drain_orphaned_inflight_members` (dispatch_cohort.rs:1801) + `revive_orphaned_cohort_members_once` (wpda_walker.rs:10234) re-inject `member.return_frame` and rely on its `inner_state` being "the dispatch state that emits the Fork" (10271-10275). For CrossCatProjection that works because the member frame IS the pre-Fork dispatch cursor. **For CrossCatLhs the same is true IF the parked member's `return_frame.inner_state` is the pre-dispatch `PrefixDispatch{pos, cur_bp}` state — which it is, because we park `cursor.clone()` (singleton) / `parent_frame_with_fork_metadata(parent,…)` (fork) BEFORE the CrossCatLhs push.** The parked frame's state is the host's `PrefixDispatch` state at the dispatch site.

**The requirement (T6/T7):** when the worker's source sub-parse runs to EOI without popping (so the cohort key stays `InFlight`), the parked members must be re-driven to **RE-LAUNCH the source sub-parse** (re-emit their own CrossCatLhs dispatch), NOT revived to a post-reentry state (there is no body to revive against). 

**What the shell must store (R5-6):** the parked CrossCatLhs member's `return_frame` must be the **pre-dispatch** cursor whose `inner_state` re-emits the CrossCatLhs dispatch action when stepped. Verified this is exactly what C.1/C.2 park (the clone is taken before the push). So the existing `drain_orphaned_inflight_members` path *already re-injects the correct frame* — the orphan, when stepped, re-hits the `PushWithEdgeKind`/`PushCrossCatLhs` arm and re-registers. **But** there is a critical interaction: after `drain_orphaned_inflight_members` REMOVES the stale InFlight entry (1834-1841), the re-injected orphan re-registers as `WorkerInserted` (1835 comment) and re-launches the source parse for real. The FIRST re-injected orphan becomes the worker; the rest collide and re-park — and now, because the worker actually pops this time (input is exhausted but the sub-parse may still complete at EOI), the normal resolve+drain (Part E) fires.

**Concrete orphan path for CrossCatLhs (additions, not a fork of the CrossCatProjection path):**
1. In `revive_orphaned_cohort_members_once` (10234), the drained orphans are already re-injected as `Frame::Concrete(member.return_frame)` (10270-10278). For CrossCatLhs members this re-drives the host dispatch. **No change needed to the re-injection** — the member shape (Part C) guarantees `return_frame` re-launches.
2. **The guarantee that must be added**: the re-injected CrossCatLhs orphan must NOT immediately re-park against a *still-present* InFlight entry from a *sibling host* at the same `(pos, source)` but different wrap. Because `drain_orphaned_inflight_members` removes ALL InFlight keys with pending members (1805-1814) in one pass, and the re-injected orphan re-registers fresh, this is satisfied: the removal is keyed on the FULL `DispatchKey` (including wrap), so each host's orphans are drained and re-launched under their own key.
3. **`resolve_prefix_with_trailing` timing (R5-6):** the orphan re-drive fires in `run_to_end_of_input`'s `!progress_made` block (4505-4528) via `OrphanRevivalOutcome::Injected(_) => continue` (4521) — i.e. BEFORE `resolve_at_end_of_input` (4682) runs `resolve_prefix_with_trailing` (4900/4939). So the re-launched source parses get their EOI step and contribute their longest-prefix candidates to `prefix_trailing_candidates` BEFORE the trailing-prefix salvage picks the furthest-reaching one. This is exactly T7 (`orphan_drain_restores_eoi_presence`): every parked member is back in the frontier at the drain point, so the EOI presence sets coincide. The `MAX_REVIVAL_ROUNDS`/`ORPHAN_REVIVAL_FRONTIER_BUDGET` bounds (10243/10255) cap re-drive cost; overflow reports unresolved evidence (sound — no member silently lost, just not re-driven, identical to OFF where they were per-cursor and also subject to the global step budget).

**The probe (mandatory before flip):** construct `{c!(p)}`-family input where the source operand consumes to EOI (e.g. a rhocalc `{ n!(` truncation in a parking-eligible position) and assert: OFF and ON produce identical `orphaned_pending_members_count` semantics (every member either resolved or re-driven), and the accepted/longest-prefix result is byte-identical. If worker-completion-before-EOI can instead be *guaranteed* (the source sub-parse always pops before the host reaches EOI on the shipped grammars), record that as evidence and the orphan path is a safety net; but the probe must DEMONSTRATE one of the two (re-drive works OR completion is guaranteed) — R5-6 forbids shipping On without it.

> **Model linkage:** T6 (`orphan_loss_without_eoi_drain`) proves that without the re-drive, any member whose id ≠ worker's is lost at EOI; T7 proves the re-drive restores parity. The implementation above makes the re-drive a REQUIREMENT gated into the On path (the second drain set + the existing orphan-revival loop), not an optimization.

---

## Part G — Worker-merge hazard (Round-5 angle C): the guarantee

**The hazard:** the CrossCatLhs worker (the `WorkerInserted` cursor) sits at `PrefixDispatch{pos:dispatch_pos, cur_bp:0}` with a freshly-pushed `category_entry(source)` GSS top. GSS nodes dedup by `(pos, symbol)` (gss.rs:591), so two workers at the same `(dispatch_pos, source)` share the SAME top node id. If `merge_equivalent_cursors` (11788) merged the worker away before it pops, its registered cohort key would never resolve → parked members silently lost under On (Invariant-1 violation).

**The guarantee (verified safe, no mitigation needed for distinct hosts; mitigation specified for the residual):**
- `ConfigKey` (11820-11881) includes `incoming_edge` (the top edge id, 11830-11832) and `incoming_edge_stack` (the interned stack id, 11833). The worker's top edge is the `CrossCatLhs` edge it just pushed, which **targets the worker's concrete predecessor** (the host return frame). Two workers from **distinct hosts** have distinct predecessors → distinct `CrossCatLhs` edge ids (add_edge_kind only coalesces same-`(target, kind)`, gss.rs:649; distinct targets ⇒ distinct edges) → distinct `incoming_edge`/`incoming_edge_stack` → **they do NOT merge.** ✓ This is the T8 cross-host separation holding at the merge layer for free.
- Two workers from the **SAME host AND same return context** would share the same predecessor, the same CrossCatLhs edge (coalesced), the same `incoming_edge_stack` — they ARE the same dispatch and SHOULD merge; but then only ONE registered (the other got `InflightCollision` and parked) — so there is exactly one worker per key. ✓
- **Residual risk (the only one):** a worker and a *non-worker* cursor (e.g. a sibling that already parked, or a cohort revive) colliding in ConfigKey while the worker is mid-sub-parse. The worker's sub-parse pushes frames ABOVE the CrossCatLhs frame, advancing `node`/`sppf_top`/`pos` — so a mid-flight worker's ConfigKey diverges from any parked member (parked members sit at the pre-push dispatch config). They cannot collide until the worker pops back to the dispatch level, at which point it has already resolved. **Mitigation if a probe ever shows a collision:** add `cohort_origin`-style worker-bucketing — but tag the *worker* with a `cohort_worker: Option<DispatchKey>` field excluded from merge (set at register, cleared at resolve), so a registered-but-unresolved worker never merges. This is the symmetric analog of the existing `cohort_origin` merge-bucketing (11842-11853) that already protects cohort *revives*. **Decision: ship without the extra field; add the `cohort_worker` merge-exclusion only if the shadow `ep_p1_shadow_share_divergent_total` or an orphan-count mismatch reveals a lost worker.** Record the analysis + the probe (a 2-host same-`(pos,source)` input, e.g. `int(3) == 3` where Bool and Int both host an Int-source CrossCatLhs at the same position) in the ledger.

---

## Part H — Attribution correction for the flip experiment (R5-4)

Three corrections, all in the measurement layer (walker_stats.rs + the memo at 6810):
1. **`cast_then_infix_steps` must ALSO match `CrossCatLhsReentry`** (the under-count bug). In the memo (6817-6821), change the predicate to:
   ```rust
   matches!(self.gss.edge_kind(*edge_id),
       Some(EdgeKind::CrossCatLhs { .. }) | Some(EdgeKind::CrossCatLhsReentry { .. }))
   ```
   Rationale: under On, the revived members carry `CrossCatLhsReentry` frames (Part E step 5/6 re-pushes CrossCatLhs which becomes Reentry after its pop), so an attribution matching only `CrossCatLhs` mechanically under-counts the ON arm and inflates the apparent drop. Matching both keeps the OFF and ON arms in the SAME attribution space. (Re-baseline the 149,645 figure under the widened predicate FIRST, OFF, so the gate compares like-with-like — the OFF number may rise slightly; the ≤59,858 target is recomputed as 40% of the re-baselined OFF figure.)
2. **Restate the spawned criterion in the counter's own key space.** The `crosscat_lhs_delegate_dup_at_pos_source` counter keys `(pos, source)` (6982), but the cache keys the FULL `DispatchKey` (incl. wrap). On the calculator, host=7 is constant so `(pos,source)` and the full key coincide (ledger shadow cross-check: `would_share_total=3500` == dup). State the flip criterion as: "spawned at key `(6,5)` drops from 3311 to ~1 **in the `(pos,source)` counter space**, AND `would_share_total` (full-key space) drops correspondingly" — never conflate the two. The "3504→~4" claim is restated as "the `(pos,source)` dup counter at (6,5): 3311→~0; the full-key shadow: 3500→~0".
3. **Shadow cross-check on the FULL key** (already shipped @ 477aef5c): the `ep_p1_shadow_seen` map keys `(pos, source, host_cat)` (14559) = the full key modulo the per-arm-constant wrap_rule. Reuse it as the ON cross-check: under On, the post-flip `would_share_total` recomputed in shadow must drop to ~0, confirming the parking actually collapsed the measured class in full-key space.

---

## Part I — Change list (file/function-anchored)

1. **gss.rs**: NO change to `EdgeKind` (R5-2 — side table instead). (Confirm `GssEdgeId` is `Copy`/`Hash` for the side-table key — it is, it's a packed u32.)
2. **wpda_walker.rs**:
   - `EpP1Mode` (111): add `On`; `from_env` (122) maps `on→On`.
   - Struct (~890): add `crosscat_lhs_wrap: FxHashMap<GssEdgeId,(u16,u16)>` + `pending_crosscat_lhs_drain_keys: FxHashSet<DispatchKey>`; init in 3 constructors (3469/3551/3632); clear in 2 resets (3733/3827).
   - `cursor_gss_pop_via_edge` (16416): return the popped `GssEdgeId` (3rd tuple element); update call sites.
   - `cursor_gss_push_with_kind` (14509): after `add_edge_kind` (14575), write `crosscat_lhs_wrap[edge_id]` for CrossCatLhs pushes under On; keep the shadow block (14549) and extend it to compute nothing new here (divergence shadow lives at resolve).
   - **`apply_crosscat_lhs_reentry_tail`** (NEW): factor 16228-16386 out of `apply_pop_body_to_cursor`; call it from the same spot.
   - **CrossCatLhs resolve block** (NEW) inside `apply_pop_body_to_cursor` after the tail call: register/resolve into the cohort cache (On) or compute `ep_p1_shadow_share_divergent_total` (Shadow); insert into `pending_crosscat_lhs_drain_keys`.
   - **`crosscat_lhs_cohort_decision`** (NEW, C.0) + singleton engagement in the `PushWithEdgeKind` arm (6976) + Fork engagement in `allocate_fork_push_child` (new branch beside 15268).
   - **`revive_crosscat_lhs_member`** (NEW, E.1).
   - **Second drain loop** (NEW) after 10876 (E.2).
   - Orphan re-drive: verify `revive_orphaned_cohort_members_once` (10234) re-injects CrossCatLhs members correctly; add the probe-gated guarantee (Part F) — likely zero code change, one assertion + the probe test.
   - Attribution memo (6817): widen to `CrossCatLhsReentry` (H.1).
3. **macros/src/gen/runtime/wpda_codegen/prefix.rs**: NO edge widening (side table). The host (`#category_src_idx`) is already the arm guard; the singleton/Fork emit sites (1301/1362) are UNCHANGED. (The wrap is recovered at runtime from the predecessor — R5-7 — not threaded through codegen, because a faithful host *rule* doesn't exist at the per-category arm, so the sentinel `u16::MAX` is correct.)
4. **walker_stats.rs**: add `ep_p1_shadow_share_divergent_total: [u64; WPDA_STATE_CLASS_COUNT*2]` (beside 566) + default (2668) + non-zero-slot Display (2199-block). Widen the `cast_then_infix_steps` memo predicate is in wpda_walker.rs (the field stays).
5. **dispatch_cohort.rs**: NO structural change (reuse `register`/`resolve`/`pause_cohort_member`/`take_pending_for_drain_all`/`drain_orphaned_inflight_members` as-is). Doc note that CrossCatLhs members are body-only (worker_inner_state ignored at revive).

---

## Part J — Verification sequence

**J.0 — Build gates**: `cargo build -p mettail-prattail` (default) + `--features walker-stats` (the load-bearing build, round-2 B-1); `cargo build -p mettail-languages --features walker-stats --examples`.

**J.1 — Shadow gates (mode=shadow, walker-stats, full battery + corpus):**
- `ep_p1_shadow_share_divergent_total` all-0 **HARD** (the integrity gate; any non-zero = the member shapes don't carry enough predecessor info, or the broadcast would corrupt — stop and fix). This is the empirical T2/T3 check.
- `ep_p1_shadow_would_share_total ~= 3500` on idx 4 (full-key cross-check, reuses 477aef5c).
- OFF vs SHADOW byte-identical battery (shadow-inertness).

**J.2 — Battery OFF + ON byte-identical** (the no-loss gate, I1): mode UNSET (Off) and `=on`:
- `gen_ledtest_op` 220/0 SENTINEL; `gen_calculator_op` 1330/0; `gen_rhocalc_op` 530/1 (pre-existing castbigrat); `edge_case_tests` 229/0 — specifically `comparison_after_cast_results` + `operator_chains_after_casts` byte-identical OFF/ON; `rhocalc_tests` 126/0 BOTH STATES (the `{c!(p)}` reentry family — the most sensitive CrossCatLhs consumer, exercising the member-tail revive + reentry-axis); ambient 52/0+13/0+17/0; `mettail-prattail --lib` 3980/0 BOTH cfgs; `-3!` canary (`postfix_binds_tighter_than_unary`); `rocq-prattail-wpda` green.
- **The orphan probe** (Part F): the constructed `{c!(`-truncation input — OFF==ON longest-prefix + orphan-count parity.
- **The worker-merge probe** (Part G): the 2-host same-`(pos,source)` input — OFF==ON, no lost worker.

**J.3 — Flip experiment (idx 4, =on, corrected attribution per Part H):**
- `(pos,source)` dup counter at (6,5): 3311 → ~0.
- full-key shadow `would_share_total`: 3500 → ~0.
- `cast_then_infix_steps` (widened predicate, re-baselined OFF): ≤ 40% of the re-baselined OFF figure (the ≥60% drop gate). If <60%, record residue + attribution → P2/P3 (plan-sanctioned).
- NEUTRAL: chain_50/100/200 byte-identical (CrossCatLhs is cast-only; both drain sets empty on chains → byte-identical hot path).
- Trigger-free inputs (idx 1/2/3/5): OFF==ON.

**J.4 — L-commit (separate, after this I-commit):** Welch N≥15 `cast_tower_bench` release, p<0.05, treatment<control, zero behavioral diffs both states; idx 6 SHOULD complete under On (depth-independence evidence); flip `from_env` default to On.

---

## Part K — Risk register with falsification tests

| # | Risk | Falsification test (must pass) |
|---|---|---|
| K1 | **Member-tail drift** — the factored `apply_crosscat_lhs_reentry_tail` diverges between in-place pop and revive. | The function is the SOLE source; both paths call it. Falsify: a unit test that revives a `PredGroupingMarker` member and asserts its next-pop state == `Unwinding` with NO reentry (model T3 state axis), and a `PredNone` member asserts reentry REFUSED (T3 reentry axis). If either fires reentry, drift exists. |
| K2 | **EdgeKind split with switch OFF** (R5-2). | `test_wpds_gss_edge_identity_includes_edge_kind` (gss.rs:1125) unchanged + GREEN; OFF battery byte-identical. Since `EdgeKind` is untouched, this is structurally guaranteed, not grammar-conditional. |
| K3 | **Stale wrap read** — side table returns wrong `(wrap_cat,wrap_rule)` for a coalesced edge. | Side table is keyed by the exact `GssEdgeId` traversed; coalesced edges share the id AND the wrap (same host+source ⇒ same wrap). Falsify: assert `crosscat_lhs_wrap[eid]` at resolve == the host recorded at push for that eid (debug_assert under walker-stats). |
| K4 | **Lost worker via merge** (Part G). | The 2-host probe (J.2); `ep_p1_shadow_share_divergent_total`==0; orphan-count parity OFF/ON. If a worker is lost, parked members orphan → the orphan re-drive catches them OR the count mismatches (probe fails). |
| K5 | **EOI orphan loss** (R5-6, T6). | The `{c!(`-truncation probe (J.2): assert every parked CrossCatLhs member is either resolved or re-driven before `resolve_prefix_with_trailing`; OFF==ON longest-prefix. T6 says loss is CERTAIN without the re-drive, so a passing probe is the T7 witness. |
| K6 | **Attribution inflation** (R5-4). | Re-baseline OFF with the widened (`+CrossCatLhsReentry`) predicate BEFORE computing the drop; the gate is 40% of the re-baselined figure. Falsify: if the ON arm's attributed steps fall outside the widened space, the drop is fictitious. |
| K7 | **Shadow perturbs the real cache.** | SHADOW touches only `ep_p1_shadow_seen` + the divergence counter; OFF==SHADOW byte-identical battery (J.1). |
| K8 | **Body-multiplicity loss under source ambiguity** (T5). | rhocalc ambiguous-source input: assert the revived-cursor count == bodies × members (count_occ parity per the model T5). |

The plan is fully anchored to the proven contract: T2 ↔ Part D+E (member-tail revive), T3 ↔ Part B.2 (divergence shadow proving the broadcast would be wrong), T6/T7 ↔ Part F (orphan re-drive REQUIRED), T8 ↔ Part A+G (wrap refines via side table; cross-host never shares at both cache and merge layers). Net-new code is confined to exactly where R5 proved the shapes differ: `apply_crosscat_lhs_reentry_tail` (factoring), `revive_crosscat_lhs_member` (dedicated revive), the two member shapes (C.1/C.2), the second drain set + loop, the `crosscat_lhs_wrap` side payload, and the orphan guarantee. Everything else reuses `DispatchCohortCache`/`DispatchKey`/`EquivKey`/`register`/`resolve`/`pause_cohort_member`/`take_pending_for_drain_all`/`drain_orphaned_inflight_members` unchanged (R5-9).
