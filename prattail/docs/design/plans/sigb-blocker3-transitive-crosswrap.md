# Sig-B Blocker 3 — TRANSITIVE cross-wrap splice (cast family's last residual, 2026-06-01)

**pgmcp experiment #9.** Builds ON Blocker-2 (`sigb-blocker2-body-splice.md`, the single-level cross-wrap splice —
DONE, closes 8/9 + nested, zero-regression, Welch-WIN; KEEP all of it). Build state: `wip/cast-family-cohort`
(`3d5d94e`) ≡ `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-COMPLETE.patch` + `cp Cargo.lock`. Design-only;
evidence/code-confirmed.

## 0. The one residual (measured)
`simulator_regression_bool_prefix_tokens` fails on EXACTLY `int(y != z > x < "qua")` (`calculator.rs:2176`).
Ladder (`/var/tmp/suite-green/b2-ladder*-results.log`): var-first `int(y != z > x < "qua")` + `int(y != true > x <
"qua")` FAIL; **boollit-first** `int(true != y > x < "qua")` OK; 3-op `int(y!=z>x)`/`int(z>x<"qua")` OK;
ends-in-var `int(y!=z>x<w)` / ends-in-int `int(y!=z>x<5)` OK. Requires ALL: (1) var-first, (2) ≥4-op chain, (3)
Int→Str cross at the TAIL. The bare-var LHS adds ONE extra coercion level → depth pushes past the relay's reach.

## 1. Root cause — the single-level relay is ONE-LEVEL-PER-STEP (code-confirmed)
Inside `step_fanout` (`wpda_walker.rs:9182`): (1) the per-cursor advance loop runs FIRST (pop sites `:6088`/`:6518`
+ `continuation_queue`), inserting resolved keys into `pending_cohort_drain_keys` at `:14455`. (2) The end-of-step
drain block (`:9752`) runs SECOND as a SINGLE `mem::take` + SINGLE `for`-pass; `take_pending_for_drain_crosswrap`
(`:9878`, Blocker-2 §3b) pushes the spliced revives into `new_cursors` (`:9892`) — they only advance NEXT step.
So a cross-wrap splice at step S produces a level-L revive that advances on S+1, resolves, re-inserts L's OUTER key,
and only at end of S+1 splices L+1 → **one level per step.** `revive_cohort_member_with_snapshot` parks the member at
`cursor.pos = hi_pos` (`:13917`) = at/near EOI for the deep var-first chain. The relay needs N steps to climb N
levels, but the revived cursors are at EOI and `step_fanout` stops once all live cursors are at EOI → the OUTERMOST
`int(` cast member's `K_pause` is never reached → stays `BinderRule` → `is_accepting_config:5620` `_=>false` →
`accepting_indices=0` → "no accepting branch … `(`". NOT a missing eligibility (557 ELIGIBLE + 112 backstop jobs
fire) — a depth-vs-steps starvation structural to the one-level-per-step relay.

## 2. Mechanism — end-of-step cross-wrap drain to FIXPOINT (drive in-block)
Keep the SAME-wrap drain single-pass (Welch-load-bearing). Make the CROSS-WRAP drain re-enter itself within the same
end-of-step block: after a cross-wrap splice revives a member, drive it to its own body-pop IN-BLOCK (it is at
`hi_pos` with the resolved-wrap `CrossCatProjection` edge on top), feeding the fresh resolution back into the drain.
Iterate to fixpoint over a worklist; `crosswrap_drained` bounds it.
**2a (`wpda_walker.rs`, the §3b block `:9844-9895`):** replace the single `take_pending_for_drain_crosswrap(&key)`
call (`:9878`) with a worklist fixpoint local to the end-of-step block: seed = keys resolved this step; for each, run
`take_pending_for_drain_crosswrap`; for each job, `revive_cohort_member_with_snapshot` (`:13865`, REUSE) then
`drive_crosswrap_revive_to_resolution(&mut revived, tokens)` (§2b) — if it returns a freshly-resolved key, enqueue it;
push the revived member to `new_cursors`. The same-wrap drain (`:9756-9843`) stays OUT of the loop (single pass).
**2b (`wpda_walker.rs`, NEW `drive_crosswrap_revive_to_resolution`, next to `apply_pop_body_to_cursor:13992` /
`cursor_gss_pop_via_edge:14375`):** one body-pop mirroring the per-cursor loop: (i) one `apply_action`/`emit_fire_action`
step so the revived `BinderRule` fires its cast action over the spliced body; (ii) `cursor_gss_pop_via_edge(&mut revived)`
— if the popped edge is the resolved-wrap `CrossCatProjection`, the existing resolve path (`:14403-14463`) inserts the
next-outer key into `pending_cohort_drain_keys`; remove + RETURN it (fixpoint owns it); (iii) if no `CrossCatProjection`
pop (resolved a non-cast level / hit EOI / errored) → return `None`, member joins `new_cursors`, relay stops on that
branch (no soundness loss). Reuses ONLY existing primitives (no novel state mutation).
**2c (§3d backstop UNCHANGED):** `crosswrap_backstop_for_pausing_member` (`:13665`) still fires at the pause site; its
revives flow into the per-cursor path → next step they pop + insert their key → next step's drain seeds the fixpoint.
No change to its predicate/site.

## 3. TERMINATION (no new cap, no heuristic — the existing take-once set IS the certificate)
`take_pending_for_drain_crosswrap` inserts `(K_sib, r_symbol_id)` into `crosswrap_drained: FxHashSet<(DispatchKey,SppfId)>`
(`dispatch_cohort.rs:458`/insert `:978`) and SKIPS any pair already present (`:846`); never cleared mid-parse (`:506`
reset only). So each `(K_sib, body-symbol)` splices AT MOST ONCE across the whole parse incl. all fixpoint iterations.
`drive_…` enqueues only when a NEW splice resolved; a key whose eligible siblings are all already drained yields zero
jobs → no re-enqueue. Iterations bounded by #distinct `(K_sib, body-symbol)` ≤ #DispatchKeys × #body-symbols, finite +
grammar/input-bounded (#levels × #wraps × #members, members ≤ `MAX_PENDING_COHORT_PER_KEY=16` `:1181`). §3b/§3d share
`crosswrap_drained` → no double-splice. Disjoint from `MAX_REVIVAL_ROUNDS`/`revive_orphaned_cohort_members_once:8937`
(EOI orphan path, different mechanism, untouched). M3.3 TERMINATION test asserts the deep + synthetic-deeper chains
return (wall-clock bound) + `crosswrap_splices_total` ≤ the static product.

## 4. Invariants preserved
Only ADDS sound cursors (`K_sib` never removed); per-level own-wrap-non-resolution gate (clause 4: `K_sib` InFlight OR
Resolved `hi_pos < R.hi_pos`) UNCHANGED at EVERY climbed level → `cross_cat_with_parens` STAYS GREEN (the parens-inner
self-Resolved-at-equal-hi steal excluded at every level); `EquivKey` (`:131`) READ-only, cache + `crosswrap_drained` +
`cohort_origin` full `DispatchKey` (R5, un-conflation 67>23); `Ambiguous` first-class; Blocker-1 descriptor + Blocker-2
single-level splice + §3d + C-bis Newton (realize walk `:4680`, disjoint) intact; Welch-neutral on chains (the whole
drain block behind `if !pending_cohort_drain_keys.is_empty()` `:9752` — empty on cast-free chains → fixpoint seed
empty → byte-identical hot path).

## 5. Milestones (ONE worktree `/var/tmp/wt-b3-impl`, serial FOREGROUND `--wait` builds; main tree NEVER modified)
Env gates: `SIGB_CROSSWRAP`/`B2_DISABLE`/`SIGB_TRACE` (reuse) + NEW `B3_DISABLE` (skips ONLY the in-block driving →
falls back to Blocker-2's one-level relay, for A/B).
- **M3.0** — diagnostic (INERT): `B3_DISABLE`-gated trace at the §3b seed; for `int(y != z > x < "qua")` confirm the
  relay climbs k levels in k steps + dies one level short of the `int(` cast (outermost member stays `BinderRule`,
  never an executed `K_sib`); contrast boollit-first reaching it. gauntlet 4220/0 (inert ≡ Blocker-2); chain Welch NEUTRAL.
- **M3.1** — `drive_crosswrap_revive_to_resolution` (§2b) + fixpoint loop (§2a), gated `!B3_DISABLE`. GATE: ALL 9
  M4-regressions GREEN (5 Sig-B incl. `bool_prefix_tokens`/`int(y!=z>x<"qua")` + 4 realize) + `cross_cat_with_parens` +
  16 M4-fixed + `_{ge,ne,lt}` + `_in_expression` + nested `test_nested_{int_int,float_float_int}`/`test_triple_nested_float`
  stay + gauntlet 4220/0. With `B3_DISABLE=1`: reproduces Blocker-2's 8/9 (residual returns) — proves transitivity is
  the sole new lever.
- **M3.2** — full sweep: gauntlet 4220/0; C-bis cycle/newton/tarjan/star/scc/self_loop 0-fail; op-suites ≥1331/532;
  soundness + `-3!` (edge_case 229/0 + probe_neg_zero 23/0) + parity 16/0 + cross_cat 2/0; rhocalc pre-existing-fail ≤8.
- **M3.3** — TERMINATION test (`int(y!=z>x<"qua")` + synthetic 5-op + deeper 6-op all parse + RETURN; `crosswrap_splices_total`
  ≤ static bound) + **interleaved Welch chain panel N≥51 + chain_1000/2000 RSS +5% max** (control `B2_DISABLE=1`; predict
  NEUTRAL/WIN) + ambiguity probe.

## 6. GATES (experiment #9 — Blocker-3 = cast family fully closed)
ALL 9 M4-regressions green (incl. `bool_prefix_tokens`) + `cross_cat_with_parens` + 16 M4-fixed + nested stay; gauntlet
4220/0; C-bis 0-fail; op-suites ≥1331/532; soundness + `-3!` + parity; Welch chain panel N≥51 no LOSS + RSS +5% max;
ambiguity; TERMINATION (deep + synthetic-deeper don't hang). Zero regression. → merge `wip/cast-family-cohort` into
`feature/wfst` + commit.

## 7. Risks
R1 non-termination → monotone `crosswrap_drained` take-once (§3); no new cap; M3.3 asserts bound + wall-clock. R2
in-block desync → reuses exact per-cursor primitives; member also pushed to `new_cursors`. R3 over-fire at a new outer
level → per-level clause-4 unchanged; `cross_cat_with_parens`/`_{ge,ne,lt}`/`_in_expression` sentinels; `B3_DISABLE=1`
must restore Blocker-2 8/9. R4 chain RSS → seed empty on chains → NEUTRAL/WIN. R5 EquivKey leak → READ-only; full
DispatchKey; 67>23 re-asserted. R6 returned key double-drained → removed when claimed (or one bounded no-op pass).

## 8. Critical files
- `prattail/src/wpda_walker.rs` (drain `step_fanout:9752`; §3b call `:9878`→fixpoint; NEW `drive_crosswrap_revive_to_resolution`
  next to `:13992`/`:14375` reusing resolve+insert `:14403-14463`; §3d `:13665` UNCHANGED; `revive_cohort_member_with_snapshot:13865`
  REUSE; per-cursor pops `:6088`/`:6518`; `is_accepting_config:5620`; gates `b2_crosswrap_disabled():85` + NEW `b3_disabled()`)
- `prattail/src/dispatch_cohort.rs` (`take_pending_for_drain_crosswrap:791` UNCHANGED body; `crosswrap_drained:458`/insert `:978`/skip `:846`;
  `crosswrap_backstop_for_pausing_member:1281`; `crosswrap_splices_total:463`; `DispatchKey:73`/`equiv:131`; `MAX_PENDING_COHORT_PER_KEY:1181`)
- `languages/tests/calculator.rs` (`simulator_regression_bool_prefix_tokens:2176`; nested `:1064`/`:1054`/`:1059`; NEW TERMINATION test)
- `prattail/src/cohort_lazy.rs` (`materialize_branch_cursor`/`CohortShell` REUSE); `prattail/src/gss.rs` (`EdgeKind::CrossCatProjection:418`)
