# Forward-Path Proc-Projection Fix — the Generalized Closure of the Cast Family's Last 2 Targets (pgmcp experiment #9, 2026-06-02)

**Base (implementation):** `d2d9a3b` (`sigb-b3-span-FINAL`). The prefix-trie (L1) is a banked, NOT-merged option at `f8c71ff` (`genfactor-STOP-GATE1`), baseline-equivalent only with `B6_LEFTFACTOR_DISABLE=1`. This plan designs **Layer 2 (L2) — the forward-path Proc-projection generalization** — as the SUFFICIENT root fix, shipping ALONE on `d2d9a3b` (no trie).

**Authoritative grounding (read, not re-litigated):** `float-forward-projection-root-PROVEN.md` (6-angle flip-grounded root), `/var/tmp/suite-green/realize-rootcause-VERDICT.txt` (252-line trace verdict + 23 traces), `float-root-PROVEN.md` (the genfactor FLIP_NOUNARY proof), `general-rule-set-left-factoring.md §RESULTS` (the trie's GATE-1 STOP). The root is taken as PROVEN.

**The standing mandate (verbatim):** *"No hardcoded assumptions! We must support any pattern supported by the `language!` specification grammar!"* — every predicate keys on STRUCTURAL facts (a transparent Proc projection exists for a category), never a category name / keyword / lattice-size / arity / rule-count constant.

---

## §0 — THE CENTRAL QUESTION: L2-ALONE vs L2+L1, with grounding

### §0.1 The answer (design decision)
**L2 ships ALONE on the clean `d2d9a3b` base (NO prefix-trie). L1 is NOT a prerequisite.** The fix lives entirely at the **forward CrossCatProjection emission + the GLL projection-cycle gate**, NOT at the prefix-Fork dispatch. Because L2 leaves the 5-way `float(`/`int(` prefix-group Fork **byte-identical**, it cannot reintroduce the prefix-Fork↔cross-wrap coupling that regressed `simulator_regression_nested_casts` (`int(str(…))`) under the trie. **This is a BLOCKING M0 claim** (not yet built — the design agent had read-only tooling): M0 must confirm L2-alone closes the 2 targets AND holds `int(str)`/`int(int)`/Bool, and STOP if not.

### §0.2 Why L2-alone is the right scope — the grounded argument
1. **The `int(str)` regression is causally tied to L1's PREFIX-Fork structure change, not to "more cast results projecting to Proc."** trie-ON release = `213/7` (NEW regression); trie-OFF (`B6=1`) = `214/6` = exact baseline (clean A/B). The genfactor verdict §(e) localizes the cause to the trie's co-equal-D2 cursor-population change presented to the SAME cross-wrap drain — a function of the prefix-Fork population, which L2 does not touch.
2. **L2 is a WALKER change ORTHOGONAL to the prefix-Fork.** The forward Proc-projection lives in the `EdgeKind::CrossCatProjection` resolve gate (`cursor_gss_pop_via_edge:15013`) + the GLL projection-cycle gate (`:6964`/`:7094`/`ProjDescriptorKey:2893`). NONE is `emit_binder_prefix_arms` (the 5-way Fork L1 rewrites). L2 emits the SAME prefix Fork → the `int(str)` drain sees the SAME cursor population → no perturbation.
3. **The cohort/revival layer is PROVEN insufficient (flip v1+v2), so the fix MUST be forward — which is exactly L2.** `revive_cohort_member_with_snapshot` (`:14480`) cannot rebuild the outer fold's `, w )` continuation. L2 reproduces the FLIP's forward in-line parse by EVIDENCE (forcing the inner fold to pop as a CrossCatProjection at the outer operand pos, so the popping cursor IS the in-line outer continuation) — not by post-hoc cohort delivery.

**Conclusion:** L2 is NECESSARY (closes the proven root) and SUFFICIENTLY ISOLATED (orthogonal to the `int(str)` coupling). If M0 falsifies L2-alone, the FALLBACK is to re-scope (NOT to bolt on L1 — §7 R1).

### §0.3 Grounding performed + the one gap M0 closes
- **Pos-2 projection asymmetry (re-extracted from `RC_POPTRACE`):** FLOAT FAIL = **0** pos-2 CrossCatProjection pops; INT PASS = **11** distinct pos-2 pops over `[4,8]`, dominated by NON-Proc wraps (`Int→BigInt` `wrap=(6,1)`, `BigInt→BigRat`, …; `ProcInt` `wrap=(0,0)` does NOT appear at pos 2 — INT is rescued PURELY by redundant non-Proc lossless projections).
- **Codegen symmetry:** Proc-context `int` arm (`wpda.rs:2359`) and `float` arm (`:2799`) are BOTH 5-branch `CrossCatDelegate` Forks — isomorphic; the asymmetry is NOT in the dispatch-arm shape.
- **Lattice asymmetry:** `Int32→[Int64,Int128,CanonicalBigInt,CanonicalBigRat]` (rich) vs `Float64→[CanonicalBigRat]` only (sparse); Float's other casts are trigger-prefixed, inapplicable to a bare fold operand. `language.rs:1066` vs `:1110-1111`; `calculator.rs:100-110`/`:128-129`.
- **PROXIMATE suppression mechanism (the WHY, pinned):** the GLL projection-cycle gate. A CrossCatProjection edge exists only for a `CrossCatDelegate` push (`allocate_fork_push_child:14320-14337`). Whether one is allocated at the outer operand pos is gated by the per-branch skip (`:7094`) + pure-projection Drop (`:6964`), both keyed on `ProjDescriptorKey=(gss_node, sppf_stack, cat_src, cur_bp)` (`:2893`). The outer `float(`'s Float delegate re-enters Float context (`cat_src=5`) to parse the inner `float(`; the inner ProcFloat projection (src=5→Proc) would re-enter at the SAME `(gss_node, sppf_stack, cat_src=5, cur_bp)` → descriptor reproduces → ProcFloat delegate SKIPPED → no pos-2 pop. INT's `Int→BigInt` targets a DIFFERENT category → distinct descriptor → allowed → pops → registers the Resolved body → outer slot fills.

**The single gap M0 closes empirically:** that forcing a Float forward CrossCatProjection pop at pos 2 closes the 2 targets WITHOUT the trie AND WITHOUT regressing `int(str)`/`int(int)`/Bool.

---

## §1 — Proven-root recap (confirm-spec; M0 reproduces inert)
Targets `float(float(10,64),64)` / `float(int(5,32),64)` ERR ("no accepting branch", `wpda_walker.rs` `accepting_indices.len()==0` arm). **Discriminator:** failure ⟺ the OUTER is a `float`-FOLD whose first operand `a:Proc` is itself a 2-arg cast fold.
- **PROXIMATE/NECESSARY:** `cursor_gss_pop_via_edge:15013` registers a Resolved dispatch-cohort body ONLY for an `EdgeKind::CrossCatProjection` pop; the inner FloatBin pops via `CategoryEntryRoot` (same-cat home-Fork) → no pos-2 body → outer `a:Proc` (paused `{pos:2,src:5,wrap:(0,1)}`) starved → `accepting_indices==0`.
- **DEEPER/SUFFICIENCY:** flip v1+v2 (deliver perfect-span `[2,8]` Proc body to the cohort) BOTH failed — outer continuation not reconstructible from `revive_cohort_member_with_snapshot:14480`. ⇒ the fix MUST be a FORWARD-path structural change, NOT a cohort/merge/projection/prefix patch. (Explains all 5 prior falsifications.)
- **Bool-vs-Float:** span-anchored bound Bool (`span_lo==2==dispatch pos`, trigger-free operand) but cannot bind Float (`span_lo=4≠2`, inner trigger shifts `lo_pos` by 2). ⇒ the fix is NOT a span-anchored extension.

---

## §2 — The generalized forward-projection mechanism

### §2.0 The structural principle (no hardcoding)
> **Every cast-keyword result category that has a transparent Proc projection MUST be able to emit a forward `EdgeKind::CrossCatProjection` pop at a cross-cat operand dispatch position — independent of how many redundant lossless readings its result category happens to have. Eligibility is keyed on the STRUCTURAL fact "a transparent (trigger-less, span-preserving) Proc projection rule exists for this category," never the category name, keyword, lattice size, or arity.**
INT incidentally satisfies this via its rich lattice; the fix makes Float/Bool/Str/UInt/Fixed satisfy it by the SAME structural route, WITHOUT relying on lattice multiplicity.

### §2.1 Surface choice
- **Surface (i) — enrich the transparent-projection emission/lattice.** REJECTED as primary: risks the #1 over-generation risk and distorts the lattice (smells of category-keying); does not address WHY the existing ProcFloat is suppressed.
- **Surface (ii) — refine the GLL projection-cycle gate so a same-cat home-Fork pop of a cast-FOLD result ALSO registers the forward Proc CrossCatProjection when the operand context demands it. CHOSEN.** Closes the asymmetry at its proximate source (the gate that suppresses Float's ProcFloat) with the SMALLEST behavioral delta: adds ONLY the missing forward projection; changes NOTHING about the prefix Fork, the lattice, the cohort layer, or the cross-wrap drain. Makes Float MECHANICALLY symmetric with Int.

### §2.2 The mechanism (surface (ii), precise)
**(M-A) Eligibility predicate `is_self_projecting_fold_operand(cursor, popped_symbol, dispatch_pos)` (structural, no hardcoding):**
- the popped edge is `CategoryEntryRoot` (same-cat home-Fork pop), AND
- the popped SPPF Symbol is **multi-token** (`span_hi - span_lo >= min_terminal_span(cat, rule) >= 2` — reuses the EXISTING `min_terminal_span` authority as the "is a real sub-parse" test), AND
- there exists a paused InFlight cohort member at `dispatch_pos` whose `source_src_idx == popped_symbol.category_src_idx`, AND
- a transparent Proc projection rule exists for `popped_symbol.category_src_idx` (looked up from the SAME projection-rule set codegen builds for Pass-2a / `single_hop_coercion`).

**(M-B) Forward registration:** when (M-A) holds and the pop would otherwise be a pure `CategoryEntryRoot` pop, ALSO register a Resolved cohort body for the matching member at `dispatch_pos`, keyed `DispatchKey::new(dispatch_pos, source_src_idx, inner_cur_bp, wrap_cat=Proc, wrap_rule=ProcX_rule)`. This is the FORWARD analogue of the INT rescue: the popping cursor IS the in-line outer continuation (unlike flip v1/v2, the outer `, w )` is driven forward, not reconstructed).

**(M-C) GLL-gate refinement:** make the cast-fold self-projection carry the ADVANCED `sppf_stack` in `ProjDescriptorKey` (`:2901`) so the post-fold projection re-entry is a DISTINCT descriptor → not skipped. This is the EXISTING design intent of the progress-aware key ("a productive SPPF-fold re-enters at an ADVANCED StackId → distinct descriptor → allowed", `:7060-7062`); the fix makes the cast-fold self-projection case actually advance the key (today it reproduces because the projection re-enters before the fold Symbol is folded onto `sppf_stack`). The no-progress paren re-entry (the gate's original defense) STILL reproduces its descriptor and is STILL skipped.

**Net:** the inner FloatBin, on completing/popping at the outer operand pos, registers a CrossCatProjection body with `wrap=(Proc, ProcFloat)`, mirroring INT's `wrap=(6,1)`. The outer `a:Proc` slot fills on the forward path. Both targets close. Float is symmetric with Int by STRUCTURE, not lattice accident.

### §2.3 Symmetry table
| | INT (passes at baseline) | FLOAT (fixed) |
|---|---|---|
| Inner fold result | Int(2) `[4,8]` | Float(5) `[4,8]` |
| Pos-2 CrossCatProjection pop | YES via `Int→BigInt` (`wrap=(6,1)`), redundant DISTINCT-cat lossless (escapes GLL skip) | NOW YES via `ProcFloat` (`wrap=(0,1)`), SAME-cat transparent, registered forward by (M-B) + un-suppressed by (M-C) |
| Resolved pos-2 body | registered → drain splices outer | registered → drain splices outer |
| Mechanism | incidental (lattice multiplicity) | structural (every join member self-projects) |

### §2.4 Why this is NOT cohort/revival and NOT span-anchored
- **Not cohort/revival:** (M-B) fires on the FORWARD pop (the in-line cursor), so the outer continuation is driven by the SAME live cursor — no `revive_cohort_member_with_snapshot`. flip v1/v2 (revive a PAUSED member) do not apply.
- **Not span-anchored:** (M-B) keys on `DispatchKey` (dispatch_pos+source+wrap), NOT `R.span_lo==K_sib.pos`. The inner-trigger shift (`span_lo=4≠2`) is irrelevant — the forward pop happens at `dispatch_pos=2` regardless.

---

## §3 — Termination / soundness (RIGOROUS)
- **T1 — bounded.** AT MOST ONE forward registration per `(dispatch_pos, source, ProcX-wrap)` per qualifying fold pop (the INT-path cardinality; deduped by `dispatch_cohort_cache` `ResolveOutcome::FirstResolve/SnapshotAppended/NoOp:15068`). (M-C) UN-suppresses a delegate the flat-Fork already enumerated → cursor population ≤ existing. Peak `branch_cursors` bounded by the existing INT-path peak.
- **T2 — GLL descriptor uniqueness preserved.** (M-C) makes the cast-fold self-projection carry the ADVANCED `sppf_stack` (genuine progress) → distinct descriptor; the no-progress paren re-entry still reproduces + is still skipped. Scott-Johnstone descriptor-uniqueness (`:6644`), CrossCatDelegate cycle guard (`:5859`), bounded-recovery (`:6599`/`:6869`) untouched.
- **T3 — soundness via `min_terminal_span` (UNTOUCHED + load-bearing in (M-A)).** The projection is over the inner fold's REAL multi-token span; (M-A) REQUIRES `span >= min_terminal_span >= 2`, so a token-UNSOUND span never projects; realize's slack filter still rejects unsound packings independently. `min_terminal_span` (`:315`/`:4843-4884`/generated `:21599`) READ-ONLY.
- **T4 — `Ambiguous` first-class (UNTOUCHED).** A second accepting root → the `accepting_indices>=2` arm yields multi-root `Ambiguous` under the cap. The fix never collapses ambiguity; it un-starves the empty accepting set.

---

## §4 — Invariants to preserve (verified at §6)
- `min_terminal_span` (`:315`/`:4843-4884`/generated `:21599`) UNTOUCHED + reused as the (M-A) gate.
- `Ambiguous` `>=2` arm + multi-root realize UNCHANGED.
- lex-min (`lex_weight.rs`), resolve/accepting (`:4260-4324`) UNTOUCHED — the fix removes a STARVATION, never changes cursor comparison.
- **Cohort/revival layer UNTOUCHED (proven WRONG layer):** `revive_cohort_member_with_snapshot:14480`, `revive_span_anchored_outer_cast_members:14424`, `take_span_anchored_outer_cast`, `intern_coercion_over_body:14381` — ZERO edits.
- **Prefix-Fork UNTOUCHED (the `int(str)` coupling surface):** `emit_binder_prefix_arms` (`binder.rs:1035`, generated `wpda.rs:1443`) — ZERO edits. Structural guarantee L2 doesn't reintroduce the trie's `int(str)` regression.
- **Must-not-perturb set:** 2 targets → PASS (calc **216/4**, NOT 215/1 — 4 pre-existing non-Float failures remain: `test_bool_from_list_elem` + 3 `*_wraps_in_release`); Bool win (`int(y != true > x < "qua")`); 3 M3.1 sentinels (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`); `test_nested_float_int_arithmetic`; 5 trie-regressed cross-cat tests (`parse_int_cross_cat_comparison_le`, `simulator_regression_original_6`, `sigb_b3_span_anchored_termination_bool`, `test_nested_int_int`, `test_nested_int_float`); **`simulator_regression_nested_casts`/`int(str(...))`**; standalone+nested unary casts (`float(10.5)`, `int(true)`, `str(3)`, `bool(0)`, `float(float(10.5))`, `test_all_to_int`, `test_float_float_nested`); op-suites ≥1331/532; `-3!`/parity; chain Welch; gauntlet 4220/0.
- **A/B lever `FWDPROJ_DISABLE`** (env, read at WALKER init — runtime, NOT codegen, so A/B does NOT require a rebuild; STRICT improvement over the trie's codegen lever). Mirrors `b3_disabled()`/`b3_span_disabled()` (`:14420`).

---

## §5 — Milestones (M0 = BLOCKING)
All builds `systemd-run --user --scope -p MemoryMax=32G cargo …`, ONE at a time. Worktree `/var/tmp/wt-realize @ d2d9a3b` has a warm 1.2G target cache; the fix is WALKER-only → incremental rebuilds (NO macro re-expansion of `calculator/wpda.rs`); A/B is a same-binary runtime toggle.
- **M0 — DIAGNOSTIC-CONFIRM (BLOCKING; STOP-gated; resolves §0):**
  1. Re-confirm baseline (release): calc `214/6`, gauntlet 4220/0; targets ERR, `int(str)`/`int(int)`/Bool GREEN.
  2. Reproduce the asymmetry inert (extend `RC_POPTRACE`, UNTRACKED): FLOAT 0 pos-2 pops, INT 11; inner FloatBin `[4,8]` pops at pos 2 ONLY via `CategoryEntryRoot`.
  3. Confirm the planned forward registration makes the inner FloatBin register as CrossCatProjection at pos 2 (scratch (M-A)/(M-B)/(M-C), UNTRACKED): NEW pos-2 Resolved body `{pos:2,src:5,wrap:(0,1)=ProcFloat}`; a `cat=0 Proc` Symbol over the outer operand span delivered FORWARD; the outer `[2,10]` FloatBin actually forms.
  4. **§0 RESOLUTION (decisive):** scratch ON, TRIE OFF (clean `d2d9a3b`), FULL calculator suite (release). **PASS:** 2 targets PASS (→ `216/4`) AND `int(str)` PASS AND `int(int)`/Bool/3 M3.1 PASS. **STOP:** (a) forcing the projection does NOT close the targets (necessary-not-sufficient like the cohort flips — re-open root); (b) `int(str)`/`int(int)`/Bool perturbs (over-generation, #1 risk — re-scope (M-C) narrower); (c) any new non-genuine `Ambiguous`.
  5. No-hardcoding inspection: the (M-A) predicate reads `popped_symbol.category_src_idx` opaquely, looks up ProcX from the codegen-built set, uses `min_terminal_span` as the gate — NO category-id/keyword/lattice-size/arity constant.
- **M1 — implement (M-A)+(M-B)** in `cursor_gss_pop_via_edge` (`:15012-15081`), behind `FWDPROJ_DISABLE`, reusing existing `DispatchKey`/`resolve`/`pending_cohort_drain_keys` (`:15031-15077`) — no new cache/state.
- **M2 — implement (M-C)** in `ProjDescriptorKey`/`extract_proj_descriptor` (`:2893-2945`/`:6950`); assert the no-progress paren cycle STILL fires (unit + `cross_cat_with_parens`).
- **M3 — targeted green (ONE build):** 2 targets PASS; `float(10.5)`/`int(true)`/`str(3)`/`bool(0)`/`float(float(10.5))`/`test_all_to_int`/`test_float_float_nested` PASS; `int(str)`/`int(int)`/Bool PASS.
- **M4 — generality sweep:** `int`/`uint`/`fixed` nested folds parse via the SAME forward self-projection (trace-confirm Float and Int both register a pos-2 body via their transparent projections); `str`/`bool` standalone+nested green; full A/B (`FWDPROJ_DISABLE` ON vs OFF) byte-clean.

---

## §6 — Gates (all pass before commit)
- **calc 216/4** (RELEASE): 2 targets PASS; the 4 pre-existing non-Float failures remain; ZERO other regressions. Re-assert: Bool win, 3 M3.1 sentinels, `test_nested_float_int_arithmetic`, the 5 trie-regressed cross-cat tests, **`int(str)`**, standalone+nested unary casts.
- **§0 must-not-perturb A/B (dominant tripwire):** `FWDPROJ_DISABLE=1` → exact baseline `214/6`; `=0` → `216/4`. ONLY delta = the 2 targets. ANY other test flipping ⇒ STOP.
- **Welch (chain neutrality):** `FWDPROJ_DISABLE` ON vs OFF, cast-free chain corpus, N≥51 (left_50/100/200, right_50/100/200/1000/2000), statistically indistinguishable (the predicate never fires on chains; runtime lever = same-binary toggle). Any arm loss (p<0.05) ⇒ STOP.
- **Cross-cat sweep:** `cross_cat_dispatch_chaining`/`cross_cat_with_floats`/`cross_cat_with_parens`/`cross_cat_with_strings`/`comparison_le/ge/ne/lt`/`in_expression` GREEN.
- **Sweep:** op-suites ≥1331/532, `pass2c_token_soundness_probe`, `-3!` (`edge_case_tests` 229 + `probe_neg_zero` 23), `wpda_parity_calculator` 16 + `_cross_cat` 2, C-bis 70, gauntlet **4220/0**.

---

## §7 — Risks
- **R1 (#1) — the forward projection over-generates → regresses working `int(str)`/`int(int)`/Bool.** Mitigation by construction: (M-A) fires ONLY for a same-cat `CategoryEntryRoot` pop of a multi-token cast-FOLD at a dispatch pos with a matching paused member. `int(str)` works via a DISTINCT-cat StrToInt cross-wrap (not a same-cat fold pop) → predicate does not fire. `int(int)` already passes via Int→BigInt; the same-cat ProcInt registration is deduped (`NoOp`/`SnapshotAppended`) → no new cursor. Bool is a trigger-free single-operand comparison (not a fold) → excluded by the fold-shape clause. M0 sub-check 4 + the §6 A/B is the tripwire. If R1 materializes, narrow (M-C) to fire only when the paused member's source category EQUALS the popped fold's category (the exact `float(float)` shape).
- **R2 — necessary-not-sufficient (like flip v1/v2).** Distinguished: the fix registers on the FORWARD pop of the IN-LINE cursor (no revive). M0 sub-check 3+4 confirms the outer `[2,10]` actually forms. STOP at M0 otherwise.
- **R3 — (M-C) re-opens a projection cycle.** (M-C) only advances the `sppf_stack` for genuine fold progress; the no-progress paren re-entry still reproduces + is skipped (T2). M2 unit + `cross_cat_with_parens` + gauntlet 4220/0 are tripwires.
- **R4 — soundness (token-unsound cast fabricated).** (M-A) gates on `span >= min_terminal_span >= 2`; realize's slack filter rejects independently. `-3!` + `pass2c_token_soundness_probe` gates.
- **R5 — runtime lever perturbs non-cast hot paths.** (M-A)'s first clause is FALSE on every chain/operator step (no paused cross-cat cast member) → O(1) short-circuit. Welch confirms.

---

## §8 — Critical sites (worktree `d2d9a3b`; the fix is WALKER-only)
**Primary fix sites (the ONLY files edited):**
- `prattail/src/wpda_walker.rs:15012-15081` (`cursor_gss_pop_via_edge`, the CrossCatProjection-only resolve gate `:15013`): add `is_self_projecting_fold_operand` (M-A) + forward Resolved registration (M-B), reusing `DispatchKey::new` (`:15031`)/`resolve` (`:15061`)/`pending_cohort_drain_keys` (`:15070`). Behind `FWDPROJ_DISABLE`.
- `prattail/src/wpda_walker.rs:6950-6958` + `:6964-6983` (pure-projection Drop) + `:7092-7099` (per-branch skip) + `:2893-2945` (`ProjDescriptorKey` + `extract_proj_descriptor`): the (M-C) gate refinement (advanced `sppf_stack` for cast-fold self-projection).

**Read-only authorities (NOT edited):**
- `prattail/src/wpda_walker.rs:14318-14346` (`allocate_fork_push_child` — the `CrossCatDelegate`→`CrossCatProjection` push at `:14325`): the forward projection-edge factory the fix mirrors.
- `:14480` (`revive_cohort_member_with_snapshot`) + `:14424` (`revive_span_anchored_outer_cast_members`) + `:14381` (`intern_coercion_over_body`): the cohort/revival/span-anchored layer — PROVEN insufficient; the fix MUST NOT live here.
- `:315`/`:4843-4884` + generated `wpda.rs:21599` (`min_terminal_span`; FloatBin `(5,15)=2`): the soundness authority reused as the (M-A) gate.
- `:4260-4324` (`resolve_at_end_of_input` + the `accepting_indices` match): UNTOUCHED.
- `prattail/src/gss.rs:393-541` (`EdgeKind::CategoryEntryRoot`/`CrossCatProjection` + `from_symbol`/`edge_kind`): the edge taxonomy the gate keys on.
- `macros/src/gen/runtime/wpda_codegen/prefix.rs:1425-1648` (`emit_unified_arm`) + `:203-321` (`classify_atomic`) + `:1085-1119` (Pass-2a bucket): transparent-projection emission (surface (i), NOT chosen) + the ProcX projection set the (M-A) lookup reuses.
- `ast/src/language.rs:1048`/`:1066`/`:1110-1111` (`lossless_targets`: Int rich vs Float sparse) + `calculator.rs:100-110`/`:128-129`/`:233/238/240`: the lattice-multiplicity asymmetry (the ROOT's "why INT incidentally passes"); the fix REMOVES the dependence on multiplicity — NOT a fix surface.
- `macros/src/gen/runtime/wpda_codegen/binder.rs:1035` (`emit_binder_prefix_arms`, generated `wpda.rs:1443`): the PREFIX-Fork — UNTOUCHED (the L2-isolation guarantee).
- `prattail/src/automata/lex_weight.rs`: UNTOUCHED.

---

## Provenance
Designed by Plan agent `a80373a8` (2026-06-02), grounded against `/var/tmp/wt-realize @ d2d9a3b` (read-only) + the `RC_POPTRACE` artifacts + the proven-root doc. The design agent had read-only tooling (no probe build), so the L2-alone claim (§0.1) is grounded reasoning made a BLOCKING M0 empirical gate (§5 M0 sub-check 4). The fix is WALKER-only, keyed on structural facts (no hardcoded category/keyword/lattice/arity), reuses existing `DispatchKey`/`resolve`/`min_terminal_span`/`ProjDescriptorKey` machinery, and is orthogonal to the prefix-Fork (so it cannot reintroduce the trie's `int(str)` regression). Supersedes no prior design; pairs-with-or-replaces the banked prefix-trie (L1, `genfactor-STOP-GATE1`) pending M0's L2-alone confirmation.

---

## ⚠ §9 RESULTS — STOP at M0: forward-REGISTRATION necessary-but-insufficient AND over-generating (2026-06-02; agents `a9380281` + `a99ec3ada`; tag `fwdproj-STOP-M0` = `1a6bd18`)

The (M-A)/(M-B)/(M-C) forward-registration was implemented + iterated, then STOPPED at the M0 §0 decisive check — BOTH STOP conditions fired.

**PROGRESS (real, flip-grounded):** lever-ON registers 30+ pos-2 `ProcFloat` bodies (vs 0 baseline) + advances the parse frontier from the baseline death (pos 7) to the outer fold's `)` (pos 10) — further than flip v1/v2 ever reached.

**WALL 1 — NECESSARY-BUT-INSUFFICIENT (the asymmetry is RECURSIVE; registration routed through the WRONG layer):** the WIP registers the INNER pos-2 `ProcFloat` body (`hi_pos=8`) but the TOP-LEVEL pos-0 `float→Proc` projection (`hi_pos=11`) is GLL-suppressed + never reached — `(M-A)` fires at `dispatch_pos ∈ {2,4,6,7,9,10}` but NEVER pos 0. INT passes because its rich lattice pops the whole-fold body as a DISTINCT-cat `CrossCatProjection` at the top level (`hi_pos=11` ×3761); Float's sparse lattice is suppressed at EVERY level. The revived inner cursor sits at `cursor.pos=8` with STALE `inner_state=PrefixDispatch{pos:2}`, `0 advance_cursor_pos`, never consumes the outer `,` at 8→9 → dropped ("all fork branches dropped"). CRITICALLY, `(M-B)` delivered via `pending_cohort_drain_keys → revive_cohort_member_with_snapshot` — the proven-WRONG cohort REVIVE layer — NOT the in-line forward parse §2.2 envisioned → it hit the flip-v1/v2 wall AGAIN.

**WALL 2 — OVER-GENERATING (§7 R1 MATERIALIZED):** §0 A/B (clean, same-binary runtime lever) — lever OFF `FWDPROJ_DISABLE=1` → `214/6` (EXACT baseline; the lever mechanism itself is clean), lever ON (default) → `212/8` (STRICTLY WORSE −2): the 2 targets do NOT close + 2 NEW cross-cat regressions (`parse_int_cross_cat_comparison_le`, `simulator_regression_original_6` = `int(-N <= y <= (-N <= y))`).

**TRUE SUFFICIENT MECHANISM (identified, NOT implemented):** an IN-LINE forward cursor that FIRES the cast + RECURSIVELY projects to Proc at EVERY dispatch level (incl. top-level pos-0) — the genfactor `FLIP_NOUNARY` in-line structural collapse achieved WITHOUT deleting the unaries, applied PRECISELY (no over-generation). This is a DEEP `CrossCatDelegate`-forward-dispatch change, NOT a registration/revive patch (the registration approach is now FALSIFIED as the 6th attempt: A2-merge, M8.1-`lo_pos`, M9-cohort-projection, prefix-trie, forward-registration). Likely natural territory for the planned Exp 15 CPS-trampolined-walker (the in-line forward-parse architecture). ESCALATED to user.

**Banked:** commit `1a6bd18`, tag `fwdproj-STOP-M0`, branch `fwdproj-impl` (NOT merged). CAUTION: the `FWDPROJ_DISABLE` lever DEFAULT is fix-ON, so a plain checkout = the regressed `212/8` (set `FWDPROJ_DISABLE=1` for the `214/6` baseline); the agent did NOT invert the default or revert (no-revert-without-approval); the branch is never merged → the default-on regression cannot reach `main`. Verdict: `/var/tmp/suite-green/fwdproj-FINAL-VERDICT.txt` + census traces (`fwdproj-recover-{float,int}-census.log`, `fwdproj-recover-calc-lever{OFF,ON}-full.log`).
