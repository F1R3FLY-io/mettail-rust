# Sig-B Blocker 2 — Cohort Body-Splice: live-`BinderRule` cross-wrap splice (2026-05-31)

**pgmcp experiment #9.** Supersedes the FALSIFIED `sigb-gll-descriptor-redesign.md` §2 ("end-of-step EquivKey
drain"). Keeps Blocker-1 (GLL descriptor — DONE, banked: gauntlet 4220/0, `cross_cat_with_parens` GREEN, C-bis
116/0). Build ON `wip/cast-family-cohort` (`3c8d188`) = session-fixes + M4 keying + Blocker-1 descriptor (≡ `6507b9c`
+ `/var/tmp/suite-green/sigb-gll.patch` + `cp Cargo.lock`). Design-only; evidence-grounded (minimal reproducers).

## 0. Why §2 ("end-of-step EquivKey drain") is FALSIFIED (measured, opposite-direction failures)
Two mechanisms built + measured (`sigbgll-m2-diag-with.log` = equiv-drain ON; `sigbgll-m2v2-diag.log`/`floattrace`
= EOI-orphan-equiv-splice):

| input | equiv-drain | EOI-splice | base |
|---|---|---|---|
| `int((-0.5<0.5)<=b!="hh")` parens2 | **FAIL(regress)** | OK | OK |
| `int(y<=z<b<=0.5)` floats | OK | **FAIL** | FAIL |
| `int(-220439700>1827376848==c!=-0.5)` chain3 | OK | **FAIL** | FAIL |
| `int(...<=(...))` nested / `int(y!=true>x<"qua")` boollit | FAIL | FAIL | FAIL |

- **Equiv-drain OVER-fires:** `sigbgll-m2-equivtrace.log` — at one `(source=2,bp=0)@pos=5` equiv class, 5 distinct
  resolved wraps `{(5,11),(0,0),(8,3),(7,34),(6,1)}` MUTUALLY drain each other's members (bidirectional). For parens2 the
  Float-paren-LHS `(-0.5<0.5)` forces an INNER cross-cat dispatch sharing `(source,bp)` equiv at the SAME `pos` as the
  outer cast's await → the drain STEALS the inner parse's self-resolving member. Minimizer (`sigbgll-m2-minimize2.log`):
  `int((a<b)<=c!="h")` OK vs `int((-0.5<0.5)<=c!="h")` FAIL — the paren must contain a cross-cat (Float) comparison.
- **EOI-orphan-equiv-splice UNDER-fires:** pairs a STILL-`InFlight`-at-EOI member with a `Resolved` equiv-sibling.
  parens2's cast member IS such an orphan → splices → PASS. But floats/chain's cast member is the LIVE
  `WpdaState::BinderRule` frontier cursor — never in the EOI orphan set → no splice → FAIL.

## 1. Root cause (code-confirmed, the lifecycle)
The cross-cat cast `<Y>To<X> . a:Y |- "int" "(" a ")" : X` pushes `WpdaState::BinderRule{result_src_idx,rule_idx,
body_src_idx,outer_bp}` (`wpda_runtime.rs:497`; the generic `PrefixOp` body-await, doc `:1052`) and awaits its body via
a `CrossCatDelegate`.
1. **Pause:** `allocate_fork_push_child:13494` builds `K=DispatchKey::new(pos_after,source,inner_bp,wrap_cat,wrap_rule)`
   (`:13542`); `register(K)` `:13562` → `InflightCollision:13568` → `pause_cohort_member(K, member=parent.clone())`
   `:13582` — the paused `member.return_frame` is the LIVE cast cursor awaiting the body. (`wrap_cat=branch.symbol.
   category_src_idx`, `wrap_rule=branch.symbol.rule_index_in_category`.)
2. **Resolve:** `cursor_gss_pop_via_edge:14264` reconstructs `K_resolve` from the edge wrap (`:14305`),
   `resolve(K_resolve,symbol_id,hi_pos=cursor.pos,pos_at_dispatch=node.pos,snap)` `:14337`, schedules
   `pending_cohort_drain_keys.insert(K_resolve)` `:14344`.
3. **Drain:** `step_fanout:9736` → `take_pending_for_drain(&K_resolve)` `:9740`/`dispatch_cohort.rs:584` →
   `revive_cohort_member_with_snapshot:13754` re-pushes `CategoryEntry(source)` onto the member's `return_frame` at
   `pos_at_dispatch`; next step pops it → `apply_pop_body_to_cursor:13881` fires the cast action = **the body-splice**.
**DEFECT:** drain is keyed on the FULL widened `K_resolve`. Cast member paused under `K_pause(W1=<)`; its body (the
whole chain, OUTERMOST wrap `W2=<=`) resolves under `K_resolve(W2)`. `take_pending_for_drain(K_resolve)` never reaches
the `K_pause(W1)` member → never splices → stuck `BinderRule` → `is_accepting_config:5604` `_=>false` →
`accepting_indices=0` → "no accepting branch ... '('". `K_resolve.equiv()==K_pause.equiv()` but `K_resolve!=K_pause`.

## 2. The over/under-fire boundary — THE structural discriminator (NOT a count)
**Eligibility predicate:** cross-revive paused member `M` from `Resolved` sibling `R` iff:
`R.equiv()==M.K.equiv()` (narrow READ, `dispatch_cohort.rs:121`) **AND** `R != M.K` (DISTINCT wrap — same-wrap is the
normal drain) **AND** `R.pos_at_dispatch == M.K.pos` (dispatch-site identity) **AND** (`M.K` is `InFlight` **OR**
`M.K.Resolved.hi_pos < R.hi_pos`) (own-wrap-non-resolution — THE load-bearing gate).
- **GENUINE (floats/chain):** the cast member's own-wrap entry `K_pause(W1)` is `InFlight` (or resolves a SHORTER inner
  span) while the body it needs is the OUTERMOST-wrap `R(W2)` at the same `pos_at_dispatch`, full-body `hi_pos` → ELIGIBLE
  → splice → GREEN.
- **PARENS-INNER steal (forbidden):** the inner `(-0.5<0.5)` SELF-RESOLVES — its own dispatch is `Resolved` at its OWN
  required `hi_pos` (== `R.hi_pos`) → the `hi_pos < R.hi_pos` gate FAILS → NOT eligible → no steal → STAYS GREEN.
All facts are grammar/parse-state (`equiv`, `pos_at_dispatch`, `hi_pos`), no count/weight/cap. The §2 blind drain
ignored the own-wrap gate.

## 3. Mechanism — end-of-step own-wrap-gated cross-wrap splice
**3a (`dispatch_cohort.rs`):** new `take_pending_for_drain_crosswrap(resolved_key) -> Vec<CrossWrapSpliceJob<W>>`
(next to `:584`): require `entries[resolved_key]` be `Resolved` (= `R`, read `symbol_id,hi_pos,pos_at_dispatch,
worker_snapshots`); scan for sibling `K_sib` with `K_sib.equiv()==resolved_key.equiv()`, `K_sib!=resolved_key`,
`K_sib.pos==R.pos_at_dispatch`, and state `InFlight{members≠∅}` OR `Resolved{hi_pos<R.hi_pos, members≠∅}`; materialize
its members (clone the `take_pending_for_drain:599` pattern via `cohort_lazy::materialize_branch_cursor`) → one
`CrossWrapSpliceJob{member,symbol_id:R.symbol_id,hi_pos:R.hi_pos,pos_at_dispatch:R.pos_at_dispatch,source,inner_bp,
wrap_cat:resolved_key.wrap_cat,wrap_rule:resolved_key.wrap_rule,snapshots}` per (member×snapshot). **Take-once
idempotence:** `crosswrap_drained: FxHashSet<(DispatchKey,SppfId)>` so repeated passes don't re-splice. **Do NOT remove
`K_sib`** (its own-wrap worker may still resolve its own span — only ADD the cross-wrap body). Bound:
`MAX_PENDING_COHORT_PER_KEY=16` (`:830`) × grammar-bounded siblings (no new cap).
**3b (`wpda_walker.rs`):** at the end-of-step drain (`step_fanout:9736`), AFTER `take_pending_for_drain(&key)`, also call
`take_pending_for_drain_crosswrap(&key)` and revive each job via the EXISTING `revive_cohort_member_with_snapshot:13754`
(pushing into `new_cursors` as the normal drain does); the revive re-pushes `CategoryEntry(source)` with the RESOLVED
wrap; `cohort_origin.equiv()` stays narrow (`:13780`, R5). Member's next step → `apply_pop_body_to_cursor:13881` fires
the cast → splices → `is_accepting_config` true → `accepting_indices>0`. Fires at the NORMAL drain (reaches the LIVE
frontier member); does NOT touch `revive_orphaned_cohort_members_once:8937` / `MAX_REVIVAL_ROUNDS` / the 256-gate.
**3c invariant:** only ADDS sound cursors (never drops); structural predicate (no heuristic); EquivKey READ-only (cache
stays full `DispatchKey`, R5); `Ambiguous` first-class (each resolving packing cross-revives → merge collapses only
observationally-equal); Blocker-1 descriptor + C-bis Newton untouched.
**3d backstop (only if residual):** if nested/boollit need the cast member to splice when it pauses AFTER its body
resolved, extend the `Resolved`-arm of `pause_cohort_member:865` to emit a `CrossWrapSpliceJob` under the SAME predicate
(symmetric revive-on-pause). Add only if M2.1 leaves a residual; re-gate identically.

## 4. Milestones (ONE worktree `/var/tmp/wt-b2-design`, serial FOREGROUND `--wait` builds; main tree NEVER modified)
- **M2.0** — primitive `CrossWrapSpliceJob` + `take_pending_for_drain_crosswrap` (3a), INERT (no walker trigger);
  `SIGB_CROSSWRAP` trace logs, for the 5 inputs, each eligible `(K_sib,R)` with the predicate fields. GATE: confirm
  `int(a<b<=0.5)` cast member's `K_pause` shares equiv with `K_resolve`, same `pos_at_dispatch`, `InFlight`-or-shorter
  (NOT self-`Resolved` at equal hi_pos); confirm parens2's inner member is self-`Resolved` at EQUAL `hi_pos` (the
  discriminator). gauntlet 4220/0 (inert); chain Welch NEUTRAL.
- **M2.1** — wire the end-of-step trigger (3b). GATE: ALL 5 Sig-B GREEN + `cross_cat_with_parens` STAYS GREEN + 16
  M4-fixed + 4 realize-fixed + `_ge`/`_ne`/`_in_expression` stay + gauntlet 4220/0. If nested/boollit residual → add 3d,
  re-gate.
- **M2.2** — full sweep + Welch (§5).

## 5. GATES (experiment #9 acceptance)
5 Sig-B + `cross_cat_with_parens` green; 16 M4-fixed + 4 realize-fixed + `_ge`/`_ne`/`_in_expression` stay; gauntlet
4220/0; C-bis cycle/newton/tarjan/star/scc/self_loop 0-fail; op-suites gen_calculator_op≥1331/gen_rholang_op 532;
soundness + `-3!` + `wpda_parity_calculator`; **interleaved Welch chain panel N≥51 + chain_1000/2000 RSS +5% max**
(cross-wrap drain is empty on single-wrap chain steps → byte-identical → NEUTRAL; load-bearing guard); ambiguity-preservation.

## 6. Risks
R1 over-fire (parens) → the own-wrap-non-resolution gate is load-bearing; M2.0 confirms parens2 inner is self-`Resolved`
at EQUAL hi_pos; add a synthetic regression mirroring `q_b`/`q_d`. R2 under-fire (floats/chain) → `R.pos_at_dispatch==
K_sib.pos`; live tests `cross_cat_dispatch_chaining`+`cross_cat_with_floats`. R3 re-injection loop → `crosswrap_drained`
dedup; entry NOT removed; bounded. R4 chain RSS → empty on chains → NEUTRAL (no new per-cursor field). R5 EquivKey leak →
READ-only; cache full `DispatchKey`; assert M4 un-conflation count > M1's. R6 nested/boollit → 3d symmetric pause-site
backstop, same predicate.

## 7. Critical files
- `prattail/src/dispatch_cohort.rs` (`DispatchKey:63`/`equiv:121`/`EquivKey:140`; `DispatchCacheEntry::{InFlight:201,
  Resolved:244}` incl. `pos_at_dispatch:247`/`hi_pos`; `take_pending_for_drain:584`; `pause_cohort_member:818`/`Resolved
  arm:865`; NEW `CrossWrapSpliceJob`+`take_pending_for_drain_crosswrap`+`crosswrap_drained`)
- `prattail/src/wpda_walker.rs` (end-of-step drain `step_fanout:9736`/`:9740` — wire here; `revive_cohort_member_with_
  snapshot:13754` REUSE; `allocate_fork_push_child:13494`/`InflightCollision:13568`; `cursor_gss_pop_via_edge:14264`/
  `:14344`; `is_accepting_config:5604`; `apply_pop_body_to_cursor:13881`; `revive_orphaned_cohort_members_once:8937` =
  explicitly NOT the injection point)
- `prattail/src/cohort_lazy.rs` (`CohortShell:108`/`materialize_branch_cursor`/`from_branch_cursor`);
  `prattail/src/wpda_runtime.rs` (`WpdaState::BinderRule:497`); `prattail/src/gss.rs` (`EdgeKind::CrossCatProjection` wrap carrier)
