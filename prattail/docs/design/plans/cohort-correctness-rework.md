# Cohort-Correctness Rework — Implementation Plan (2026-05-31)

**Repo:** `/home/dylon/Workspace/f1r3fly.io/mettail-rust` (PraTTaIL). **Branch:** `feature/wfst-architecture`,
HEAD `6507b9c` + uncommitted validated session fixes (`git diff --shortstat` = 18 files / +1498 / −175;
recovery snapshot `/var/tmp/suite-green/current-tree-2026-05-31.patch`). **Closes:** Cluster Y (~36 tests,
ledger `docs/design/plans/drive-suite-green-ledger.md` "Authoritative residual 2026-05-31").

> **UPDATE 2026-05-31 (post-measurement):** M2(plain-M4)+M3 were EXECUTED + MEASURED — see the ledger
> `drive-suite-green-ledger.md` "M2+M3 MEASURED". Refinements: **plain-M4 fixes 16 but REGRESSES 9** (not
> shippable alone); **F1 contradicted** (with eval-cast present, plain-M4 DOES drop the 2 "sound" inputs);
> **R2/M3 recognition hypothesis FALSIFIED** (nested cluster shows 1053+ registrations, cohort fully engages —
> NOT `registrations_total=0`). The R1-regressions + nested cluster share ONE root = **cohort-revival
> incompleteness** (Sig-A realize-empty / Sig-B orphans-exceed-revive-bound). The actionable design is now
> `prattail/docs/design/plans/cohort-revival-completeness.md` (the completeness mechanism). M0/M3/M5 below are
> superseded by that; the §2 machinery map + §0 invariant remain authoritative.
>
> This plan was produced by a Plan agent that **empirically re-traced M4 on the current tree in an isolated
> worktree** and **partly contradicts the ledger's M4 narrative** (the "verify, don't blindly trust" discipline).
> Where the traces (F1–F5 below) conflict with the older ledger entries, **the traces supersede**. The big result:
> the doubly-nested cluster is a parse-RECOGNITION gap, NOT a cohort explosion / Exp-15 memory problem → **Exp-15
> is de-scoped from Cluster Y.**

## 0. HARD INVARIANT (governs every milestone)
NEVER prematurely drop a sound parse/derivation alternate. Drop ONLY on EVIDENCE: token-soundness (terminal yield
== spanned input; enforced by the shipped Step-A `min_terminal_span` realize filter, `wpda_walker.rs:4830-4900` +
`WpdaEngine::min_terminal_span:257`), a cursor that cannot reach an accepting branch, or EOI exclusion. A
WEIGHT/COST heuristic that makes "X win over Y" is FORBIDDEN. `Ambiguous(...)` is first-class. Dedup ONLY
observationally-equivalent terms (`semantic_hash`/SPPF dedup/ConfigKey merge, never Display).

## 1. EMPIRICAL GROUND TRUTH (this session's traces — supersede the ledger's M4 narrative where they conflict)
Isolated worktree (HEAD + session fixes + M1 + M4 via `h5-directfirst-m4.patch`, `PRATTAIL_WALKER_STATS=1`) vs
current-tree M1 reference binary. Worktree removed; main tree verified unmodified (18/+1498/−175).

- **F1.** h5-M4 does NOT drop the two ledger-named "sound" inputs — `int(y != true > x < "qua")` and
  `int(-220439700 > 1827376848 == c != -0.5)` both PASS (orphans revived by M1; `failed_orphan_members=0`).
  **The documented regression #2 is in the different `stepB-M4-with-regression.patch`, NOT in h5.** ⇒ the M4
  variant to re-land is **h5 (direct-first)**, not stepB.
- **F2.** h5-M4 DOES regress `simulator_regression_nested_casts` (M1+eval-cast: ok → h5-M4: FAILED) — a real
  un-conflation regression in the *nested* path, **possibly confounded by h5 lacking the shipped eval-cast fix**
  (must be retested with eval-cast present on the current tree).
- **F3.** The nested-2-arg-cast cluster (`test_nested_int_int`/`_int_float`/`_float_float_int`/`_float_int_arithmetic`,
  `test_triple_nested_float`, `simulator_regression_cross_cat_with_parens`/`_with_floats`/`_original_6`) fails
  **identically under M1 and M4** with `registrations_total=0` + "no accepting branch reached end of input" — the
  cross-cat cohort machinery NEVER engages. **This is a 2-arg-cast-with-non-literal-first-arg PARSE-RECOGNITION
  failure, NOT cohort explosion/hang and NOT cohort-revival drop.** (`int(5,32)`/`float(10,64)` with a *literal*
  first arg parse fine: 121–271 registrations, resolve, pass.) **Contradicts the ledger's "84% collision / 900+
  registrations / cap-256 HANG" framing** (that belongs to a different M4 integration).
- **F4.** M4's un-conflation win is real: flips `test_cast_float_overflow_to_inf`, `test_casts_from_numeric_strings`,
  `test_int_from_float_still_works`, `test_bool_from_list_elem` (M1 FAIL→ok).
- **F5.** `failed_orphan_members=0` on every input; `DispatchCohortCache::fail` (`dispatch_cohort.rs:861`) has NO
  call site (`#[allow(dead_code)]`). The Failed-discard "M2 side-queue" is LATENT, not active.

## 2. Verified machinery (line-exact, current tree)
- **Three keys:** `DispatchKey{pos,source_src_idx,inner_cur_bp}` (cohort CACHE, `dispatch_cohort.rs:63`; built
  `wpda_walker.rs:13186`, reconstructed at pop `:13915`); `EquivKey{source_src_idx,inner_cur_bp}` (merge
  discriminator in `ConfigKey.cohort_origin`, via `equiv():90`; the COQ-S1 chain O(N²)→O(N) fix — MUST stay narrow);
  `PackedDispatchConfig(u64)` (per-cursor cycle-defense `visited_dispatch`, `:2672`/`extract_dispatch_config:2710`;
  FULL u64, zero free bits; consulted `:5763`/`:6572`, drops re-dispatch as "projection cycle").
- **Lifecycle:** register `:13203` (`WorkerInserted`/`InflightCollision`→`pause_cohort_member dispatch_cohort.rs:787`,
  cap `MAX_PENDING_COHORT_PER_KEY=16`/`ResolvedHit`/`FailedHit`); pop→`resolve :13943`; end-of-step drain
  `step_fanout:9403`→`take_pending_for_drain:553`→`revive_cohort_member_with_snapshot:13384` (inherits worker's
  `symbol_id`; `intern_symbol` dedups `(nt,lo,hi)` so the worker Symbol aggregates all packings, `sppf.rs:535`).
- **M1 + spurious-gate:** `run_to_end_of_input:3932`→`revive_orphaned_cohort_members_once:8611`→
  `drain_orphaned_inflight_members:650`; gate `SPURIOUS_ORPHAN_THRESHOLD=256 ∧ parse_already_succeeds (:8689)`,
  bounded `MAX_REVIVAL_ROUNDS=4 (:955)`.
- **M4 surface (h5, read line-by-line):** widens ONLY `DispatchKey` (+`wrap_cat,wrap_rule`),
  `EdgeKind::CrossCatProjection` (`gss.rs:408`, 4→8 B/edge), and the `cohort_origin` literal `:13403` (but
  `.equiv()` strips `wrap_*` → EquivKey stays narrow). Does NOT touch `PackedDispatchConfig` (cycle-defense narrow),
  keeps `merge_equivalent_cursors` at EquivKey granularity, no `BP_TIER` value change (lex_weight hunk doc-only).
- **DEAD asset:** `cohort_continuation.rs` (`CohortContinuation`, ~32 B; general `substitution_slot`) +
  `deferred_continuations` cache field — defined, stats-read only (`:9704`), NEVER constructed/installed.
  Approach-P (parse-time-dual-write + EOI-install) was REJECTED on **chain** Welch LOSS (chain ledger 9-S1.b/c/d) —
  *chain-only* because it fired on the chain hot path.

## 3. Re-scoped diagnosis of Cluster Y (THREE roots, per F1–F5)
- **R1 — single-level cross-cat un-conflation (the cohort bug M4 addresses).** Distinct injections collide on the
  narrow `DispatchKey`; the loser is paused and (under M1) revived only if a sibling resolves or via the
  InFlight-orphan path. M4 un-conflates → flips ≥4 casts (F4). Risk: the un-conflated worker can be re-conflated/
  dropped by the narrow MERGE / cycle-defense (the F2 `nested_casts` regression is this class — retest with eval-cast).
- **R2 — nested 2-arg-cast recognition (NEW, the real doubly-nested root; F3).** `int(<cast>, w)` /
  `float(<paren-expr>, w)` fails at parse with `registrations_total=0` — the 2-arg cast rule's slot-0 dispatch does
  not admit a cast/parenthesized sub-expression in slot 0. **NOT cohort, NOT Exp-15 memory.** Codegen/dispatch
  recognition gap (likely the slot-0 FIRST-set / cross-cat-LHS bootstrap for the cast's first parameter omits
  cross-cat injections, or the InfixLoop/grouping interaction at slot 0 fails to re-enter cross-cat).
- **R3 — eval-cast surfacing (ALREADY SHIPPED).** `test_cast_int_invalid_width` PASSES on the current tree;
  `test_cast_int_nonfinite_float_is_error` is the residual eval facet. h5 lacks the fix, so shows them red — an
  artifact of h5's age, NOT a rework target.

## 4. Candidate mechanisms → RECOMMENDATION
| Mechanism | R1 | R2 | Sound (inv.) | EquivKey narrow | Subsumes gate | Evidence |
|---|---|---|---|---|---|---|
| (i) Re-land **h5** M4 (cache-key widen) alone | yes (F4) | no (regs=0) | risk (F2) | yes | no | F1/F2/F4 |
| (ii) M4 + cross-cat-gated realize-time CohortContinuation install | yes | no | **yes** | yes | **yes** | Approach-P schema; chain-only LOSS |
| (iii) Fix R2 in codegen (admit cross-cat first-arg in 2-arg cast slot 0) | n/a | **yes** | yes | n/a | n/a | F3 |
| (iv) Exp-15 GSS-batch | yes | no (R2≠memory) | yes | yes | yes | exp15 plan — NOT needed |

**RECOMMENDATION:**
- **R1 → re-land h5 M4** (`h5-directfirst-m4.patch`, NOT stepB). FIRST test plain M4-on-current-tree (mechanism i);
  escalate to the cross-cat-gated CohortContinuation install (mechanism ii — makes the un-conflated SOUND derivation
  reach the SPPF as a packing so the narrow merge/cycle-defense can't silently drop it, subsumes InFlight-orphan +
  Failed-discard + spurious-gate, chain-gated so the prior chain Welch-LOSS provably can't recur) ONLY if plain M4
  regresses on the current tree (e.g. F2 `nested_casts` persists with eval-cast present).
- **R2 → a CODEGEN/dispatch fix (mechanism iii), NOT Exp-15.** The trace (`registrations_total=0`) proves the
  doubly-nested failures are recognition gaps. **Exp-15 is NOT required for Cluster Y.**
- **R3 → already shipped; only re-confirm** (+ the nonfinite eval facet).

## 5. Milestones
**Standing GATE (every milestone):** gauntlet `cargo test --release -p prattail --lib`=**4220/0**; op-suites
`gen_calculator_op≥1331/0`,`gen_rholang_op 532/0`; disambiguation `-3!` + `wpda_parity_calculator` /0; soundness
probe `calculator.rs::pass2c_token_soundness_probe`; regression canaries `test_unambiguous_int_literal`,
`test_nfa_spillover_float_int_var`,`unit_calculator_bool_inttobool`,`simulator_regression_nested_casts` (F2 falsifier),
`test_deep_ternary_{100,500,1000}`+`test_ternary_chain_10000` (≤5% wall); for ANY cohort/keying/memory change:
interleaved Welch chain panel `{left,right}_assoc_chain_{50,100,200}`+`right_…_1000`, N≥15, ACCEPT iff no arm LOSS
p<0.05, + `chain_1000`/`chain_2000` RSS +5% max.

### M0 — Census + per-input baseline matrix (measure-only)
Confirm R1 (revivable orphan / merge-drop) vs R2 (`registrations_total=0`), `failed_orphan==0` (F5). Reuse
`orphaned_pending_members_count:734`/COQ-S0 key sets `:13190`; ADD a feature/env-gated
`merge_dropped_distinct_cohort_workers` counter in `merge_equivalent_cursors:10244` (two bucketed cursors, equal
`.equiv()`, differing full-key `wrap_*`). GATE: standing. Revert: delete counters.

### M1′ — (shipped) M1 + spurious-gate is the validated baseline anchor. Track A (M2) must subsume the gate.

### M2 — Re-land **h5** M4 (CACHE-key widen); escalate to continuation install ONLY if plain M4 regresses
Re-land from `h5-directfirst-m4.patch` (NOT stepB): `dispatch_cohort.rs:63` `DispatchKey`+`wrap_cat,wrap_rule`
(`equiv():90` UNCHANGED); `gss.rs:408` `EdgeKind::CrossCatProjection`+2; `wpda_walker.rs :13186/:13384/:13915/:9421`
thread `wrap_*`. **Measure plain M4 on the current tree first** (current tree HAS eval-cast + Step-A, unlike h5 →
resolves the F2 confound). If plain M4 is clean (F4 casts green, `nested_casts` green, no disambiguation/gauntlet/
op-suite regression): SHIP after Welch. If it regresses: wire the dead `cohort_continuation.rs` asset — generalize
eligibility to `substitution_slot`; in `pause_cohort_member:787` build a `CohortContinuation` (capturing
`other_children` from `sppf_stack`) when P-eligible AND `!pos_in_absorbed_chain_interval` (chain-perf guard);
NEW `install_cohort_continuations` at top of `resolve_at_end_of_input:4000` (drain `deferred_continuations` →
substitute worker `symbol_id` → `intern_packing`+`link_packing_to_symbol`); Step-A `min_terminal_span` filter
(`:4848`) rejects unsound results. Make `revive_orphaned_cohort_members_once:8611` defer to the continuation path
for eligible sites (gate becomes inert for cross-cat; deep-ternary chain-gated out).
GATE: standing + M0 matrix shows F4 casts green AND `nested_casts` green AND `merge_dropped_distinct_cohort_workers==0`
on reps + **re-Welch chain panel + chain_1000/2000 RSS** (predict NEUTRAL — chains gated out). Closes (~28): R1 calc
casts + rholang cross-cat/binder family (`comm::*`,`parsing::*`,`new_and_extrusion::*`,`exec`,`beta::*`,`congruence::*`,
`fraction_builds_rational`,`led_delegation::test_p1_10`). Revert: `git revert` → M1-validated.

### M3 — R2: nested 2-arg-cast recognition (CODEGEN/dispatch; the real "doubly-nested" fix)
**M3.0 (measure-first):** trace `int(int(5,32),32)` (walker-stats) to pinpoint where the slot-0 cursor dies (no
cross-cat Fork at slot 0 ⇒ the cast's first param FIRST-set omits the cross-cat sources). **Change:** extend the
2-arg cast rule's first-param dispatch to include the cross-cat-LHS bootstrap (model on `CrossCatLhs` bootstrap
`prefix.rs:1433-1453`) so a cast/cross-cat term is admissible in slot 0 — by EVIDENCE, preserving `Ambiguous`,
soundness via the Step-A filter, NO weight. Investigate: `macros/src/gen/runtime/wpda_codegen/prefix.rs` Pass-2a
`CrossCatProjection` + Pass-2c `ImplicitCast` (`:1076-1197`, `emit_unified_arm`) + the 2-arg-cast first-param dispatch.
GATE: standing + nested cluster green (`test_nested_*`,`test_triple_nested_float`,`simulator_regression_{cross_cat_with_parens,
cross_cat_with_floats,original_6,nested_casts}`). Codegen-only ⇒ run Welch panel as a guard. Risk: over-generation
of ambiguous casts → bound by span filter + the 16-regression history (`prefix.rs:1138-1143`; `simulator_regression_bool_prefix_tokens`).
Revert: `git revert` (regenerate).

### M3b — Bare-var inference reconciliation (only if residual after M2)
If `bare_variable_infers_as_proc` still `Ambiguous(Proc,Name)`: reconcile in `infer_term_type` (`language.rs:3460/3826`)
— top-level bare var reports `Proc` when `Ambiguous⊇Proc` AND Proc is the declared primary, WITHOUT dropping Name
from the term set. GATE: standing + `bare_variable_infers_as_proc`,`comm::single_channel`.

### M4 — R3 eval-cast residual (confirm-only)
`test_cast_int_invalid_width` already passes. `test_cast_int_nonfinite_float_is_error` → classify against
`macros/src/logic/mod.rs cast_error_variant_for`; if it needs an analogous None→CastErr binding for the nonfinite
path, EVAL-codegen fix. Closes `test_cast_int_nonfinite_float_is_error` + rholang analogue.

### M5 (CONTINGENT, gated) — Exp-15 GSS-batch ONLY if a measured per-cursor explosion remains
Traces show NO cohort explosion on the current tree (R2 is `registrations_total=0` recognition). **Exp-15 NOT
scheduled for Cluster Y.** Schedule ONLY if, after M2+M3, a Welch/RSS measurement shows a genuine per-cursor
materialization blowup on a surviving input. Expected UNNECESSARY; contingency with a hard empirical pre-gate.

## 6. What closes where
- M2 (R1): ~28 (calc cast family + rholang cross-cat/binder/comm/congruence/beta + led_delegation).
- M3 (R2): ~8 nested-cast (`test_nested_*`,`test_triple_nested_float`,`simulator_regression_*nested*/parens/floats/original_6`).
- M3b: `bare_variable_infers_as_proc`,`comm::single_channel` (if residual).
- M4 (R3): `test_cast_int_nonfinite_float_is_error` + rholang analogue.
- `class2_opt`/`gen_class2optsmoke`: re-measure after M2/M3 (likely cascade — else separate collection-opt fix).
- Cluster J (~26 roundtrips): re-measure after M2/M3 (J-a cascades); J-b/J-c independent (task #7).
- Exp-15 / M5: expected NONE required (R2 proven non-memory by trace).

## 7. Sequencing, risks, reverts
1. **M0** census. Zero risk.
2. **M2** re-land h5 M4 (plain first; continuation only if regresses). Hard gate: chain Welch + RSS + `nested_casts`
   (F2 falsifier). Revert → M1-validated.
3. **M3** R2 codegen recognition. Gate: nested cluster + 16-regression history. Codegen-only ⇒ minimal chain risk.
4. **M3b/M4** local fixes if residual.
5. **M5 Exp-15** ONLY on a measured blowup (expected: not needed).

**Empirical housekeeping:** all experiments in isolated worktrees (`git worktree add --detach /var/tmp/wt-X HEAD`
+ `git apply /var/tmp/suite-green/current-tree-2026-05-31.patch` + `cp Cargo.lock` — the moving pathmap tip fails
to build without it); remove when done; **main tree NEVER modified by experiments** (merge winners in controlled).
Snapshots: `/var/tmp/suite-green/{current-tree-2026-05-31.patch,checkpoint-after-M1-validated.patch,FINAL-SHIP-stepA.patch,h5-directfirst-m4.patch}`.

## 8. Why this respects the HARD INVARIANT
- **R1/M2** restores derivations M1 lost to key-collision (MORE completeness by evidence); the optional continuation
  path routes the SOUND un-conflated derivation into the SPPF as a packing so the narrow merge/cycle-defense cannot
  silently drop it. The Step-A soundness filter is the SOLE post-hoc drop. EquivKey stays narrow (re-Welch'd).
- **R2/M3** is a recognition fix (admit cross-cat in slot 0 by EVIDENCE), bounded by the span filter + the
  16-regression history — NOT a weight, NOT a cap, NOT test-hacking.
- **Exp-15** is correctly de-scoped: traces prove the doubly-nested failures are NOT memory/explosion.

## Critical files
- `prattail/src/wpda_walker.rs` (cohort lifecycle; M4 keying `:13186/:13384/:13915`; M1 revive `:8611`; spurious-gate
  `:8689`; `resolve_at_end_of_input:4000`; `merge_equivalent_cursors:10244`; cycle-defense `:5763/:6572`; Step-A `:4830`)
- `prattail/src/dispatch_cohort.rs` (DispatchKey/EquivKey `:63/:90/:109`; pause/drain/register/resolve; dead `fail():861`)
- `prattail/src/cohort_continuation.rs` (dead realize-time-continuation asset M2-ii wires) + `cohort_lazy.rs`
  (CohortShell/materialize `:593`; `MAX_COHORT_FRAME_MEMBERS:634`)
- `macros/src/gen/runtime/wpda_codegen/prefix.rs` (R2 root: Pass-2a/2c `:1076-1197`; `CrossCatLhs` bootstrap `:1433-1453`)
- `languages/tests/{calculator.rs,rholang_tests.rs}` (Cluster-Y tests; F2 falsifier `simulator_regression_nested_casts`;
  soundness probe; canaries); `gss.rs` (`EdgeKind::CrossCatProjection:408`)
