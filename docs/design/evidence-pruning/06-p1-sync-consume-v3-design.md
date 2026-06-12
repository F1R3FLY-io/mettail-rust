# EP-P1 v3: synchronous resolved-body consumption (+ bounded in-flight parking)

> Status: v3 CONVERGED-WITH-CORRECTIONS (Round 7, 2 critics: IMPLEMENT-WITH-CORRECTIONS R7-1..R7-12
> (idx 4: 3,476/3,504 = 99.2% of arrivals are post-resolution; in-flight 24 across ~4 keys;
> tail_divergent 0). Binding inputs: Round 5 (R5-*) + Round 6 (R6-*) corrections
> (03-red-team-ledger.md), the CrossCatLhsParking.v contract @ a0fa001d, and the measured
> splits in 02-program-ledger.md. Supersedes the REFUTED v1 (04-) and v2 (05-).

## 0. The mechanism in one paragraph

The first CrossCatLhs arrival at a `DispatchKey` (route=CrossCatLhs, R6-7) is the WORKER: it
proceeds exactly as today and its pop resolves the body into the cohort cache (the Measure
resolve site @ 79753c4b, promoted to On). An arrival at a key that is RESOLVED **and
QUIESCENT** (§2) consumes synchronously IN PLACE: no `CrossCatLhs` push, no parking, no
drain — push the interned body onto its own sppf stack, jump to `hi_pos`, and apply the
member tail computed from ITS OWN pre-dispatch frame (the model's `member_tail_config` as a
plain function — T2; never any worker state — T3). Multi-body keys consume via
`CursorOutcome::ForkInto` (one continuation per body — T5). Arrivals before quiescence PARK
through the existing `pause_cohort_member` with the bool CHECKED: cap overflow (16/key) falls
back to Proceed (re-parse — sound, only less sharing; measured in-flight population: 24
total). Parked members revive at the end-of-step drain via the SAME consume function applied
to `member.return_frame` (R6-4 corrected: into `new_cursors` pre-replacement, one revive per
(job, member)). A key whose worker never resolves orphan-re-drives at EOI (the existing
origin-agnostic re-injection re-launches the pre-dispatch frame — T6/T7).

## 1. The consume function — the single shared core (discharges R5-1/R6-2)

```rust
/// Apply one resolved source body to a cursor sitting AT its CrossCatLhs
/// dispatch decision (the pre-push configuration). Realizes
/// CrossCatLhsParking.v::member_tail_config as a FUNCTION (T2): the tail
/// derives ONLY from the cursor's own pre-dispatch frame; nothing of the
/// worker is read (T3). Used by BOTH the in-place ResolvedHit consume and
/// the drain revive — single source of truth.
fn consume_crosscat_lhs_body(
    &mut self,
    cursor: &mut BranchCursor<W>,
    source_src_idx: u16,
    symbol_id: SppfId,
    hi_pos: usize,
) {
    // (1) the body: onto the cursor's OWN sppf stack; weight mirrors the
    //     proven projection revive (weight_at_dispatch ⊗ symbol_weight_sum
    //     — left-projection tiebreak preserved, Round-6 angle C SOUND).
    cursor.sppf_stack_id = self.sppf_stack_arena.intern_push(cursor.sppf_stack_id, symbol_id);
    let body_w = self.sppf.symbol_weight_sum(symbol_id);
    cursor.weight = cursor.weight.times_ref(&body_w);
    cursor.pos = hi_pos;
    // (2) the member tail from the cursor's OWN current node (== the
    //     predecessor the per-cursor pop would have seen — the cursor is
    //     pre-push, so cursor.node IS pred_id):
    //     effective_state per wpda_walker.rs:16228-16261 semantics +
    //     the reentry guard (pred != NONE; popped frame is CategoryEntry
    //     by construction — it is the frame we are NOT pushing).
    let pred = cursor.node;
    let pred_kind = self.gss.node(pred).map(|n| n.symbol.kind);
    let reentry = pred != crate::gss::GSS_NODE_NONE && self.gss.node(pred).is_some();
    if reentry {
        // The reentry: push category_entry(source) AT hi_pos with the
        // CrossCatLhsReentry edge (mirrors :16196-16207 verbatim) and
        // enter InfixLoop{cur_bp:0} — the host's one hosted infix pass.
        let _ = self.cursor_gss_push_with_kind(
            cursor,
            StackSymbolV2::category_entry(source_src_idx),
            hi_pos,
            W::one_ref(),
            crate::gss::EdgeKind::CrossCatLhsReentry { source_src_idx },
        );
        self.set_cursor_inner_state(cursor, WpdaState::InfixLoop { cur_bp: 0 });
    } else {
        // PredNone: the per-cursor flow's effective state without reentry.
        let st = match pred_kind {
            Some(SymbolKind::CategoryEntry) | None => WpdaState::InfixLoop { cur_bp: 0 },
            _ => WpdaState::Unwinding,
        };
        self.set_cursor_inner_state(cursor, st);
    }
    // (3) the D-strings result-cat re-sync (:16319-16351 semantics) —
    //     factored alongside (Round-7 verification point: enumerate what
    //     of the :16228-16386 tail applies to a non-popping consume; the
    //     splice-skip (:16193-16196) is a POP-path concern and does not
    //     apply — there is no pop and no splice here; verify).
    self.crosscat_lhs_dstrings_resync(cursor, source_src_idx);
}
```

**Fidelity argument (Round-7 target):** the per-cursor flow = push CrossCatLhs frame →
sub-parse → pop (splice-SKIPPED for CrossCatLhs pops — ROOT-F :16193-16196 — so the pop's
only effects are the body remaining on the sppf stack + the tail) → tail from pred. The
consume reproduces: body on stack (1) ✓, pos=hi ✓, tail from the same pred (2) ✓, re-sync
(3) ✓, and SKIPS exactly what the pop path skips (the splice). The exact tail-equivalence —
including `effective_state` arm-by-arm and what `:16319-16386` does for CrossCatLhs pops —
is the Round-7 critics' primary verification surface. tail_divergent=0 on the corpus is the
empirical witness that same-key tails agree; the function form covers the general case.

## 2. Quiescence — the late-body no-loss rule (NEW; closes the gap v2 never saw)

A second sub-parse lineage (e.g. a lex-fork inside the source operand) can pop the same key
LATER with a NEW body. An arrival that consumed before that pop would miss the late body —
a loss the per-cursor flow does not have (each cursor's own parse finds all bodies).

**Rule:** a key is CONSUMABLE iff `resolved ∧ open_lineages == 0`, where `open_lineages` =
(CrossCatLhs pushes at the key) − (pops of those edges, counting Error-terminated lineages
as closed). Track per key on the walker (`FxHashMap<DispatchKey, i32>`, +1 at the worker/
Proceed push, −1 at the pop-resolve site AND at lineage death with the key's edge on the
stack — Round-7 surface: enumerate the death paths; if death-tracking is not exactly
realizable, the SOUND fallback is `open_lineages` = pushes − pops with key-age timeout →
Proceed). Arrivals at a non-quiescent key PARK (cap-checked → Proceed). This subsumes
`spawn_worker` (no body can appear post-quiescence: every body comes from a lineage that
pushed the edge; quiescence waits for all of them).

**Measured basis:** the in-flight window at the FIRST-resolve boundary holds 24 arrivals; the
quiescence window is wider by the late-lineage tail. Step 0 of implementation extends the
measure mode to count `post_resolve_pre_quiescent` arrivals exactly (one more counter) — if
it stays ≪ cap, parking covers it; overflow→Proceed regardless (sound).

## 3. The On-mode decision at the push arm (non-cfg — R6-5)

At the @79753c4b Measure hook site (already non-cfg), `On` extends the match:
- `WorkerInserted` → Proceed (push; `open_lineages += 1`; wrap side table as today).
- `FailedHit` → **Proceed** (re-parse; the per-cursor failure path — error shape, recovery —
  is preserved exactly; corpus failed_hits = 0).
- `InflightCollision` (or resolved-but-not-quiescent) → `pause_cohort_member(key, member)`
  with the singleton member shape (pre-push `cursor.clone()`); **if the bool is false (cap)
  → Proceed** (counted: `ep_p1_park_overflow_fallbacks`). Parked → `CursorOutcome::Drop`.
- `ResolvedHit{bodies, ..}` ∧ quiescent → consume: body-0 in place on `cursor`; bodies 1..N
  on clones of the PRE-consume cursor; return `CursorOutcome::ForkInto(all)` (Round-7
  surface: confirm ForkInto's caller semantics = "successors replace the cursor", so body-0
  rides the vec too rather than in-place mutation + Alive).
- The Fork-path producer (`PushCrossCatLhs` → allocate_fork_push_child) gets the same
  decision with the fork-metadata member shape (R6-5/R5-5; measured fork spawns = 0 on the
  corpus, so this is completeness, not the hot path).

## 4. The drain (parked members only — small populations by construction)

R6-4 corrected: inside the existing end-of-step drain block, a second loop over
`pending_crosscat_lhs_drain_keys` (inserted by the pop-resolve under On, only when parked
members exist and the key is quiescent), revives ONE cursor per (job, member) — `let mut c =
member.return_frame; consume_crosscat_lhs_body(&mut c, ...)` per body via the jobs (jobs are
per-body) — pushed into the drain's local `new_cursors` BEFORE the `branch_cursors`
replacement (pre-11020), so prune+merge see them like every other revived cursor.
`cohort_origin` tagging: the EquivKey-narrow projection as the projection revive does
(:15851 region) with `route: CrossCatLhs` on the full key.

## 5. EOI orphan re-drive (T6/T7)

Keys with parked members whose worker never resolves: the existing
`drain_orphaned_inflight_members` + `revive_orphaned_cohort_members_once` re-inject
`member.return_frame` verbatim — the pre-dispatch `PrefixDispatch` frame re-emits the
CrossCatLhs dispatch and re-registers (Round-6 angle A verified the engine arm guards
re-hold). Mandatory probe (R5-6/R6): a truncation input whose source consumes to EOI in a
member-bearing position; assert OFF==ON longest-prefix + member parity.

## 6. Verification (gates)

- Step 0: measure-mode extension (quiescence-window counter) + re-run the split.
- Shadow/measure neutrality re-verified (battery + arm timing).
- Battery OFF + ON byte-identical: the full 9 suites (ledtest SENTINEL; rhocalc_tests 126/0
  BOTH STATES — the `{c!(p)}` reentry family is the most sensitive consumer); -3! canary;
  R6-8: a NEW cast-then-compare AmbiguityBudget test (OFF==ON or a justified, recorded
  delta); the orphan probe; chain_50/100/200 neutrality (drain set empty on chains).
- Flip experiment (corrected attribution per R6/H): widen the `cast_then_infix_steps` memo to
  `CrossCatLhsReentry` FIRST, re-baseline OFF, then ON must be ≤ 40% of the re-baselined
  figure. Spawn-space criteria stated per counter: `(pos,source)` dup at (6,5): 3311 → ~1;
  measure-mode `resolved_hits` → ~0 under On (consumed arrivals never reach the register —
  they consume at the arm; state the expected counter shape exactly before running).
- L-commit: Welch N≥15 release `cast_tower_bench`, idx 6 completing under On = the
  depth-independence evidence; flip the env default.

## 7. Risk register (Round-7 attack surfaces)

| # | Risk | Falsification |
|---|---|---|
| 1 | Consume-vs-pop tail drift (the :16228-16386 tail has parts beyond state+reentry+resync that apply) | Round-7 line-by-line enumeration of the tail; unit tests: PredGroupingMarker member → Unwinding no-reentry; PredNone → no-reentry; byte-identical OFF/ON on the edge clusters |
| 2 | ForkInto semantics mismatch (does the caller treat it as successors-replace?) | read the ForkInto handling at the apply call sites; if in-place+extras is the convention, body-0 stays in place |
| 3 | Quiescence tracking unsound (lineage death paths missed → keys never quiesce → everything parks/falls back) | the Step-0 measurement counts quiescence latency; timeout→Proceed fallback keeps it sound either way |
| 4 | Budget semantics shift (consumed arrivals never enter the frontier as delegates) | R6-8 budget test; the consume keeps the CURSOR (it was already in the frontier) so frontier counts change less than parking did — verify |
| 5 | Weight tiebreak (consume multiplies body_w into cursor.weight vs per-cursor accumulation order) | left-projection argument (Round-6 angle C); the `-3!` canary + Display-identity on the battery |
| 6 | The reentry push at hi_pos creating node collisions with the worker's reentry node (shared (pos,symbol) GSS node) | Round-6 1b: no node-keyed mutable state; verify for the reentry node specifically |
