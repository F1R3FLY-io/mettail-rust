# Sig-B Blocker-3 — FANOUT-LEVEL drain-fixpoint (cast family's last residual, 2026-06-01)

**pgmcp experiment #9.** REDESIGN of `sigb-blocker3-transitive-crosswrap.md` §2 after its in-block single-body-pop
drive (§2b) was IMPLEMENTED + FALSIFIED at M3.1 (regressed `cross_cat_dispatch_chaining`+`cross_cat_with_floats`+
`test_nested_int_int`; calc 207/10 vs baseline 210/7). Builds ON Blocker-1 descriptor + Blocker-2 single-level
cross-wrap splice + §3d backstop + C-bis Newton — KEEP ALL. Build state ≡ `6507b9c` +
`/var/tmp/suite-green/sigb-cast-family-COMPLETE.patch` + `cp Cargo.lock`. Design-only; evidence-confirmed.

## 0. Residual (measured)
`simulator_regression_bool_prefix_tokens` on EXACTLY `int(y != z > x < "qua")` (`calculator.rs:2176`; tokens
`0=int 1=( 2=y 3=!= 4=z 5=> 6=x 7=< 8="qua" 9=)`). var-first + ≥4-op chain + Int→Str tail (bare-var LHS adds one
coercion level). Same class: `test_nested_float_float_int`, `test_triple_nested_float`. Baseline 210/7 → B3 success 213/4.

## 1. Root cause — re-localized: cross-sibling cascade starved by the EOI stop (evidence)
M3.1 proved the climb is a **CROSS-SIBLING RESOLUTION CASCADE through the NORMAL per-cursor fanout** (`advance_cursor_pos`
+ `merge_equivalent_cursors` + resolution-check + per-step drain), NOT a one-level-per-step intra-member relay:
- **Real climb (`b3-m31-trace-nestedintint.log`, B3_DISABLE=Blocker-2):** the per-step cross-wrap drain fires once per
  resolved key; revives advance NEXT `step_fanout` through the normal loop → a DIFFERENT OUTER sibling resolves + is
  drained at the outer pos. `int(int(5,32),32)` DRAIN `R_key.pos` 4→6/2→**0**+9 over ~37 fanout-steps → PASSES.
- **Starvation (`b3-varfirst-b2drain.log`):** for `int(y!=z>x<"qua")` the cascade tops at pos:8; members park at EOI
  (pos:9) and `run_to_end_of_input`'s `if !progress_made` (post-patch `:4131`) declares a structural fixpoint + exits
  ~2 fanout-iterations BEFORE the outer `int(` cohort (`XCP(w=0,9)` at pos:0) resolves — EVEN THOUGH the cohort cache
  still holds an eligible, un-drained `K_sib` cross-wrap job. The loop measures cursor-STRUCTURAL progress, not
  pending-cohort-work.
- **Why §2b in-block drive FAILED:** `cursor_gss_pop_via_edge` pops the TOP edge = the just-pushed INNER wrap
  `XCP(w=0,0)`, re-inserting the SAME inner key (the outer `XCP(w=0,9)` is THREE pops deeper) → 5010 same-level
  self-enqueues, never climbs; the premature in-block drain diverged member state + broke merge/dedup → 3 sentinels
  regressed. `B3_DISABLE=1` restores EXACTLY Blocker-2's 8/9 → the §2a scaffolding is sound; only §2b is the defect.

## 2. Mechanism — (a) FANOUT-LEVEL drain-fixpoint (reject (b))
**(b) revive-pop-target restructure REJECTED:** making the outer frame the pop target needs either changing the inner-wrap
edge (breaks the splice Blocker-2 relies on → regresses 8/9) or a multi-pop in-block body walk (= the falsified §2b that
bypasses merge/dedup → regresses the 3 sentinels). No (b) variant emits a genuinely-outer key without the in-block walk.
**(a) RECOMMENDED — purely the stop condition:**
- **2.1 Revert §2a/§2b in `step_fanout`:** DELETE the falsified §2a worklist fixpoint + `drive_crosswrap_revive_to_resolution`;
  restore Blocker-2's per-step SINGLE-PASS cross-wrap drain (promote the `b3_disabled()` arm to unconditional) — byte-identical
  to Blocker-2 (the proven 8/9 shallow cascade). Keep behind `if !pending_cohort_drain_keys.is_empty()` (Welch-load-bearing)
  + `!b2_crosswrap_disabled()`. NET: `step_fanout` == Blocker-2; zero new helper.
- **2.2 Add ONE escape hatch in `run_to_end_of_input` `!progress_made` block (post-patch `:4131`)**, modeled EXACTLY on the
  existing orphan precedent:
  ```
  if !progress_made {
      if self.revive_orphaned_cohort_members_once(tokens) > 0 { continue; }   // existing, FIRST
      if !b2_crosswrap_disabled() && !b3_disabled() && self.has_pending_crosswrap_climb() { continue; }  // NEW, SECOND
      return Ok(());
  }
  ```
  `continue` re-enters the `for _ in 0..max_steps` loop → recomputes the fingerprint → `step_fanout` again → the normal loop
  advances the still-live cohort members + the restored per-step drain fires for any key resolved this iteration → the next
  iteration the OUTER `int(` sibling resolves + is drained at pos:0 → `is_accepting_config` flips the `int(` member to
  accepting → parse succeeds.
- **2.3 NEW `has_pending_crosswrap_climb(&self) -> bool`** (walker, next to `step_fanout`; delegates to
  `DispatchCohortCache::has_eligible_undrained_crosswrap(&self)`): a PURELY READ-ONLY mirror of
  `take_pending_for_drain_crosswrap`'s clauses 1-4 — scan `entries` for a pair `(Resolved R, K_sib)` with
  `K_sib.equiv()==R.equiv()` ∧ `K_sib!=R` ∧ `K_sib.pos==R.pos_at_dispatch` ∧ `(K_sib,R.symbol_id)∉crosswrap_drained` ∧
  (`K_sib` InFlight∧members≠∅ ∨ Resolved∧`sib_hi<R.hi_pos`∧members≠∅); short-circuit `true` on first hit. NO insert/
  materialize/count. Consults the SAME monotone `crosswrap_drained` the drain mutates → once every eligible pair is drained
  it returns `false`.

## 3. TERMINATION (no new cap — the existing take-once set IS the certificate)
`crosswrap_drained: FxHashSet<(DispatchKey,SppfId)>` is monotone non-shrinking (insert + skip-if-present; cleared only at
parse boundary), bounded by #distinct `(K_sib,body-symbol)` ≤ #DispatchKeys × #SPPF-symbols (grammar/input-bounded:
#levels×#wraps×#members, members ≤ `MAX_PENDING_COHORT_PER_KEY=16`). Each §2b hook-`continue` is followed by one
`step_fanout` that either (a) makes cursor-structural progress (`progress_made=true`, hook not reached next iter), or (b)
its per-step drain marks ≥1 new `(K_sib,R.symbol_id)` drained (strictly grows the set) + revives ≥1 member. A `continue`
with no resolvable key + no drainable pair is impossible (the predicate returned true ⇒ an eligible-undrained `Resolved`-R
pair exists, drained within ≤1 step). ⇒ `crosswrap_drained.len()` strictly grows between hook-fires ⇒ finitely many ⇒
loop reaches `return Ok(())`. `max_steps` (`:3974`, `Err(WpdaMaxStepsExceeded)`) is the hard backstop. Disjoint from the
orphan hook (`MAX_REVIVAL_ROUNDS=4`, runs FIRST, only removes entries). `step_counter` frozen during fanout — not relied on.

## 4. Invariants
Only ADDS sound cursors (§2a restored Blocker-2; §2b adds NO cursors, only re-runs the fanout); per-level clause-4 own-wrap
gate UNCHANGED at every level (the read-only predicate applies the identical clause 4) → `cross_cat_with_parens` STAYS
GREEN, parens-inner steal excluded at every level. `EquivKey` (`dispatch_cohort.rs`) READ-only; cache + `crosswrap_drained`
+ `cohort_origin` full `DispatchKey` (R5, 67>23). `Ambiguous` first-class (revives flow through merge + SPPF dedup).
Blocker-1 + Blocker-2 + §3d + C-bis Newton intact. **`B3_DISABLE=1` restores EXACTLY Blocker-2's 8/9** (the A/B lever +
the regression net). Welch-neutral: §2a behind non-empty-seed guard; §2b hook reached only at `!progress_made` + guarded;
`has_pending_crosswrap_climb()` is O(1) on cast-free chains (`entries` empty).

## 5. Milestones (ONE worktree `/var/tmp/wt-b3-redesign`; serial FOREGROUND `cargo` — `systemd-run --scope` runs sync, do NOT pass `--wait`; self-clean + verify `pgrep -x rustc`==0; main tree NEVER modified)
- **M4.0** — revert §2b (delete the worklist fixpoint + `drive_crosswrap_revive_to_resolution`; restore Blocker-2 per-step
  drain) + add `has_eligible_undrained_crosswrap`/`has_pending_crosswrap_climb` (NOT yet wired) + a `SIGB_CROSSWRAP` trace at
  the hook site. GATE: calc == Blocker-2 210/7; gauntlet 4220/0; chain Welch NEUTRAL. CONFIRM the trace shows
  `has_pending_crosswrap_climb()==true` with an eligible `K_sib` at the `int(` cast level at the deep-chain stop boundary
  (work IS pending) and `==false` for boollit-first / the 1-level nest at their final boundary. (If the `int(` cohort is NOT
  eligible at the boundary → DIFFERENT blocker → STOP+report, do NOT relax clause 4.)
- **M4.1** — wire the §2b hook (gated `!b3_disabled()`). GATE: ALL 9 M4-regressions GREEN (5 Sig-B incl. `bool_prefix_tokens`
  + 4 realize) + `cross_cat_with_parens` + 16 M4-fixed + `_{ge,ne,lt}` + `_in_expression` + nested `test_nested_{int_int,
  float_float_int}`/`test_triple_nested_float` GREEN + gauntlet 4220/0. **The 3 M3.1-regression sentinels
  (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`) MUST stay GREEN.** `B3_DISABLE=1` ⇒ EXACTLY
  Blocker-2's 8/9. Calc 213/4. If any sentinel regresses → STOP+report.
- **M4.2** — gauntlet 4220/0; C-bis 0-fail; op-suites ≥1331/532; soundness + `-3!` (229/0 + 23/0) + parity 16/0 + cross_cat
  2/0; rholang pre-existing ≤8.
- **M4.3** — TERMINATION test (`int(y!=z>x<"qua")` + synthetic 5-op + 6-op parse AND RETURN; `crosswrap_splices_total` ≤
  static bound; instrument + assert §2b hook-`continue`s ≤ `crosswrap_drained.len()`) + **interleaved Welch chain panel N≥51
  + chain_1000/2000 RSS +5% max** (control `B2_DISABLE=1`; predict NEUTRAL/WIN — hook never fires on cast-free chains) +
  ambiguity probe. Save `git diff > /var/tmp/suite-green/sigb-cast-family-FINAL.patch`.

## 6. GATES (= cast family fully closed) → merge `wip/cast-family-cohort` into `feature/wfst` + commit
ALL 9 M4-regressions green (incl. `bool_prefix_tokens`) + `cross_cat_with_parens` + 16 M4-fixed + nested stay; gauntlet
4220/0; C-bis 0-fail; op-suites ≥1331/532; soundness + `-3!` + parity; Welch N≥51 no LOSS + RSS +5% max; ambiguity;
TERMINATION (bounded hook-fires + splices, no hang); `B3_DISABLE=1` restores 8/9; **the 3 M3.1-sentinels MUST NOT regress.**

## 7. Risks
R1 non-termination → monotone `crosswrap_drained` certificate + `max_steps` backstop; M4.3 asserts bounded fires/splices.
R2 cascade still tops short → M4.0 trace MUST confirm `has_pending_crosswrap_climb()==true` with an eligible `K_sib` AT the
`int(` level at the stop boundary (existence proof = the B2 1-level reaching pos:0); if not eligible → DIFFERENT blocker,
STOP. R3 over-fire → clause-4 unchanged, read-only predicate identical → parens stays green. R4 chain Welch → guards +
O(1) empty-entries → NEUTRAL/WIN. R5 EquivKey leak → READ-only, full DispatchKey, 67>23. R6 orphan-hook interaction →
orphan FIRST (only removes entries), no shared counter.

## 8. Critical sites (post-patch lines = 6507b9c + COMPLETE.patch)
- `prattail/src/wpda_walker.rs`: `run_to_end_of_input !progress_made` ~`:4131` (INSERT the §2b hook after the orphan
  `continue`); `step_fanout` same-wrap `:9803` / falsified §2a `:9899-10055` (DELETE the worklist; restore Blocker-2 single
  pass); `drive_crosswrap_revive_to_resolution` `:14104` (DELETE); NEW `has_pending_crosswrap_climb` ~`:9229`;
  `revive_cohort_member_with_snapshot` `:14027` (REUSE); `cursor_gss_pop_via_edge` `:14686-14760` (UNCHANGED);
  `is_accepting_config` `:5620`; gates `b2_crosswrap_disabled`/`b3_disabled` ~`:89`.
- `prattail/src/dispatch_cohort.rs`: `take_pending_for_drain_crosswrap` UNCHANGED (clause source); NEW read-only
  `has_eligible_undrained_crosswrap`; `crosswrap_drained`/`crosswrap_splices_total`/`crosswrap_backstop_for_pausing_member`
  UNCHANGED; `DispatchKey:63`/`equiv:90`; `MAX_PENDING_COHORT_PER_KEY:797`.
- `languages/tests/calculator.rs`: `bool_prefix_tokens:2176`; nested `:1054/:1059/:1064`; NEW TERMINATION test.
- `prattail/src/cohort_lazy.rs` (`materialize_branch_cursor`/`CohortShell` REUSE); `prattail/src/gss.rs`
  (`EdgeKind::CrossCatProjection` wrap carrier).
