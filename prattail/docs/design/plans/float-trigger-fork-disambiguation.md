# Float Trigger-Fork Disambiguation — Generalized Evidence-Driven Fix (experiment #9)

**Base:** `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-FINAL.patch` (Bool-closed).
**Root status:** FLIP-PROVEN (`float-root-PROVEN.md`, agent `a304ec4e`). This plan does NOT re-investigate the root; it designs the generalized fix, grounded by a live trace of `float(float(10,64),64)` (agent `a2375cb3`, 32G-capped, no tracked source modified).

---

## §0 What is already true (do not re-litigate)
- The trigger-group Fork for `float` (Float ctx, src 5) emits **5 co-cost branches** `lex_w(0.0, 5, rule_idx)`: `IntToFloat`(11), `BoolToFloat`(12), `StrToFloat`(13), `FloatId`(14) [unary, `tc.len()==1`] + `FloatBin`(15) [2-arg fold]. Emitted by `emit_binder_prefix_arms` (`macros/src/gen/runtime/wpda_codegen/binder.rs:1138-1177`); verified in generated `wpda.rs:1443-1483`.
- `int`/`uint`/`fixed` are structurally identical (unary set + a fold). The shared structural property: "a trigger group mixing ≥1 `tc.len()==1` unary rule AND a multi-arg fold rule sharing the trigger."
- lex-min tiebreak `(primary, lex_alt_idx, src_idx, rule_idx)` (`prattail/src/automata/lex_weight.rs:349-357`) collapses to `rule_idx` ascending when the first 3 TIE — the proven premature-disambiguation lever.
- `min_terminal_span` realize filter (`wpda_walker.rs:257`, override `wpda.rs:21599`; float unary `(5,11..14)=1`, `FloatBin (5,15)=2`) is the EVIDENCE token-soundness backstop — drops fabricated casts at realize (slack < min_span) regardless of weight. **Stays the soundness authority; the fix is disambiguation only.**
- `subsume_lex_dominated_cursors()` is already DELETED (`wpda_walker.rs:9632-9645`); walker keeps ALL alive cursors; default `bounding_mode = Unbounded`.

## §1 Proven-root confirm-spec (M9.2.0 diagnostic gate — reproduce inert FIRST)
- **Confirm-1 (Fork is NOT where it dies):** under `PRATTAIL_TRACE=cursors` on `float(float(10,64),64)`, all 5 inner-float branches (11–15) coexist as live cursors (steps 3–8) and do NOT merge (`merge_equivalent_cursors` `ConfigKey` includes `weight_rule_idx` `:10431` + `sppf_top` `:10416`). So `rule_idx` does not drop a branch at Fork time.
- **Confirm-2 (where it dies):** the OUTER `FloatBin` (15, `body_src_idx 0 = a:Proc`) reaches `pos=11` (EOI) in `InfixLoop`, but `is_accepting_config`(`:5456`)→`is_cursor_accepting_terminal`(`:11445`) requires the `sppf_stack` to hold exactly ONE complete Symbol; the `a:Proc` slot (inner `float(10,64)`) never delivered a realized `Proc` Symbol → not accepting → `resolve_at_end_of_input` `accepting_indices.len()==0` arm (`:4304`) → panic "no accepting branch reached end of input."
- **Confirm-3 (the rule_idx lever, at the INNER Fork + realize):** the inner `float(10,64)` is itself a trigger-group Fork; for the outer slot to fill, the inner reading must be `FloatBin` (the only one consuming the inner `,`). At realize, the shared inner `(Float, lo, hi)` Symbol is preferred toward the lower-`rule_idx` unary packing; that unary packing is token-unsound for the 2-arg inner span and is dropped by `min_terminal_span` → NO inner `Proc`-Symbol where one is structurally required → outer never completes. FLIP (`FLIP_NOUNARY=1`) collapses the inner Fork to a single `ConsumeAndPush`→`FloatBin` → inner `Proc`-Symbol delivered → outer accepts (PROVEN-doc table; controls hold; gauntlet 4220/0).
- **Confirm-4 (why int/uint/fixed only LOOK fine):** Int has Proc-projection redundancy (`ProcInt . i:Int |- i : Proc`, `calculator.rs:100`) + cross-cat casts giving `IntBin`'s `a:Proc` slot an alternate non-Fork-starved fill path Float lacks. The same lever is present, merely masked. **M9.2.0 must reproduce Confirm-1..4 + show the chain-Welch surface is excludable by the structural predicate; STOP if not.**

## §2 Solution space + recommended fix
**HARD INVARIANT:** never drop an alternate by declaration order, only by evidence. For the trigger group, the EVIDENCE is the post-trigger token shape after arg 1: a second `,`-separated arg before `)` ⇒ fold survives; single arg + `)` ⇒ unary survives. Keep BOTH alive until that O(1)-token lookahead resolves.

**Candidate A (RECOMMENDED) — keep same-`(primary, lex_alt_idx, src_idx)` trigger-group Fork branches CO-EQUAL.**
- **A2 (PREFERRED, smallest):** leave codegen weights as-is; stamp each such Fork's branch cursors with `trigger_group_coequal` (bool / small group-id) on `BranchCursor`, set true ONLY when the Fork's branch set satisfies the mixed-structural predicate. In `merge_equivalent_cursors`, when BOTH colliding cursors carry the same coequal group, drop ONLY `weight_rule_idx` from their `ConfigKey` so they ⊕-merge by `plus` + `source_priority` (evidence-neutral, deterministic) instead of bucketing apart by `rule_idx`; `ConfigKey` is byte-identical everywhere else. The evidence prune is unchanged (a worker that can't consume its next token dies in `apply_action_to_cursor`).
- **A1 (fallback):** in codegen, emit the mixed group's branches with an identical `rule_idx` sentinel in the WEIGHT (the `symbol`/`new_state` keep true per-rule `rule_idx` so the right rule still fires). Observable in generated `wpda.rs`; wider blast radius than A2. Use only if the `BranchCursor` field proves costly to thread (it should not — `source_priority`/`lex_fork_path` are already such fields).
- **Why it restores the alternate:** co-equal means the inner `FloatBin` reading is not out-prioritized by `rule_idx`; it survives on `source_priority`, and the inner `,` evidence kills the unary workers before they can mis-fill the slot. No weight heuristic, no `,`-lookahead peek in codegen — pure evidence + Fork-source order.

**Candidate B (REJECTED) — evidence-gated strictly-winning fold weight.** Give the fold `−ε` primary only when its `,` is in lookahead. Rejected: (i) reintroduces a weight heuristic on the hot lex-min path (violates the invariant + `feedback_use_wpds_disambiguation_not_heuristics`); (ii) needs a paren-balanced `,`-before-`)` scan at dispatch = the exact pre-F7 heuristic the Fork replaced (`binder.rs:1032-1034`); (iii) perturbs the weight algebra for genuinely-ambiguous inputs.

**Chain-Welch neutrality (the dominant constraint), by construction:** the coequal stamp is set iff `classify_trigger_group_mixed` = "≥1 `classify_unary_prefix_shape`-positive `tc.len()==1` branch AND ≥1 multi-arg fold (`tc.len()≥2`, `,`-sep) sharing the trigger." NO chain/operator-tier/projection/lex-alt/opt-group Fork satisfies this. So on cast-free chains the stamp is `false`, `ConfigKey` still includes `weight_rule_idx`, and `merge_equivalent_cursors` is bit-for-bit unchanged → the landed chain Welch wins are untouched by construction. §6 still requires the Welch A/B to PASS as confirmation (tripwire for predicate leakage).

## §3 Termination / boundedness
- Co-equalizing adds NO cursors (the 5 branches already fan out today); it only MERGES two (A2, decreasing count) or leaves counts equal (A1). Peak `branch_cursors` ≤ today's at every step.
- Evidence prune is O(1) tokens: a unary worker at its arg-close hits `,` with no matching arm → no child → dies (`step_fanout` empty-children death); the fold dies symmetrically on single-arg `)`. Both within 1 token after arg 1 completes. GLL descriptor-uniqueness (`:6644`) + recovery cycle bounds (`:6599`) unchanged.
- Genuine ambiguity (none for `float(`, arity decided by `,`) → both reach EOI → `accepting_indices.len()≥2` arm (`:4376`) → `Ambiguous`, realized under the `Some(64)` cap.

## §4 Invariants to preserve
- Soundness stays on EVIDENCE: `min_terminal_span` realize filter (`:4843-4884`) untouched — sole authority dropping fabricated casts. The fix changes only WHICH same-cost cursors coexist, never which derivations are token-sound.
- `Ambiguous` first-class (`≥2` arm + multi-root realize unchanged).
- Standalone unary casts (`float(10.5)`, `int(true)`, `float(float(3))` nested-unary `:1291`): single-arg `)` kills the fold worker on evidence; unary completes.
- Must-not-perturb: Bool win (`calculator.rs:2188`), the 3 M3.1 sentinels (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`), `test_nested_float_int_arithmetic` (`:1074`), `cross_cat_with_parens`/`strings`, op-suites ≥1331/532, soundness/`-3!`/parity, gauntlet 4220/0.
- A/B lever `B5_FORK_EVIDENCE_DISABLE=1` → coequal stamp false everywhere → exact pre-fix behavior.

## §5 Milestones
- **M9.2.0 — DIAGNOSTIC-CONFIRM (BLOCKING).** Reproduce §1 Confirm-1..4 inert under trace; show the chain-Welch surface is excludable (no chain Fork matches `classify_trigger_group_mixed`); confirm R3 (the inner unary packing over a `,`-bearing span is `min_terminal_span`-rejected, so inner `FloatBin` is the unique realizable inner `Proc`-Symbol once co-equal). STOP if Confirm-4 or the exclusion can't be shown.
- **M9.2.1 — predicate.** `classify_trigger_group_mixed(entries)` in `binder.rs` (reuse `classify_unary_prefix_shape` + a multi-arg-fold shape check). Unit-assert TRUE for float/int/uint/fixed groups, FALSE for unary-only (cos/exp/ln/sin), paren groups, operator tiers.
- **M9.2.2 — A2.** Add `trigger_group_coequal` to `BranchCursor` (default false); set true on children of a mixed trigger-group Fork (Fork arm `:6427`+, gated by the predicate on `branches`); thread into the `ConfigKey` computation in `merge_equivalent_cursors` (`:10372`) to drop ONLY `weight_rule_idx` when both colliding cursors share the coequal group. Wire `B5_FORK_EVIDENCE_DISABLE`.
- **M9.2.3 — regenerate + targeted green.** One 32G build; `test_nested_float_float_int` + `test_triple_nested_float` PASS; all §4 controls hold.
- **M9.2.4 — generality.** Confirm `uint`/`fixed` nested-fold analogues parse; int-nested still passes (now via the robust path, not solely redundancy).

## §6 Gates (all pass before commit)
- **calc 215/1:** `cargo test -p languages --test calculator` → the 2 targets flip to PASS, zero regressions (215 pass + the 1 intentional-ambiguous).
- **Welch (dominant):** chain Welch A/B `B5_FORK_EVIDENCE_DISABLE` ON vs OFF over the cast-free chain corpus, N≥51 → live-cursor distributions statistically indistinguishable. Any drift ⇒ predicate leaking onto a chain Fork ⇒ STOP + re-scope.
- **Sweep:** op-suites ≥1331/532, soundness, `-3!`, parity, `prattail --lib` gauntlet 4220/0; one 32G-capped build.

## §7 Risks
- **R1 (dominant) — coequal leak onto a chain Fork** → structural predicate excludes operator/projection/lex-alt/opt-group by shape; Welch gate is the tripwire; A/B lever isolates.
- **R2 — co-equal merge discards a needed operational delta** → `merge_equivalent_cursors` keeps the `source_priority`/`plus`-winner's `recovery_deltas` (`:10455-10481`); collisions are same `(state,node,pos,edge,depth,sppf_top)` minus `rule_idx`; deltas diverge only AFTER the `,`/`)` evidence (losers already dead). Validate via the `-3!` parity gate.
- **R3 — realize Symbol-dedup still prefers a unary inner packing** → confirm in M9.2.0 the inner unary packing over a `,`-bearing inner span has slack < min_span and is dropped, so inner `FloatBin` is the unique realizable inner `Proc`-Symbol.
- **R4 — `body_src_idx 0 vs 5` confusion** → fix operates only on the coequal group flag, never special-cases `body_src_idx`; verify nested + triple-nested.

## §8 Critical sites
- `macros/src/gen/runtime/wpda_codegen/binder.rs:1138-1177` — trigger-group Fork emission; add `classify_trigger_group_mixed` (+ A1 weight sentinel, if A1).
- `prattail/src/wpda_walker.rs:6427+` — Fork arm; stamp `trigger_group_coequal` when the predicate holds on `branches`.
- `prattail/src/wpda_walker.rs:10340-10481` (`merge_equivalent_cursors`) + `ConfigKey` `:10372-10435` — drop `weight_rule_idx` only for same-coequal-group collisions.
- `prattail/src/automata/lex_weight.rs:349-357` — lex-min order (read-only reference; A2 does not modify).
- `prattail/src/wpda_walker.rs:4286-4375` + `:4843-4884` (`min_terminal_span`) + `:11445` (`is_cursor_accepting_terminal`) — resolution/soundness/accepting checks the fix must leave intact.

---

## ⚠ FALSIFICATION — Candidate A2 FALSIFIED at M9.2.3, 2026-06-02 (agent `a02cb1c1`; tag `fork-fix-A2-falsified` = `a3e69f2`)
**M9.2.0 PASSED** (Confirm-1..4 reproduced; the FLIP `FLIP_NOUNARY=1` → both targets PARSE; chain-exclusion ✓ — the coequal predicate marks only int/float trigger groups, no chain Fork). **M9.2.3 FAILED:** A2-enabled calc **209/11** (with `B5_FORK_EVIDENCE_DISABLE=1` → **214/6 = exact base**, clean A/B isolation) — the 2 Float targets STILL fail AND **5 cross-cat tests regress** (`parse_int_cross_cat_comparison_le`, `simulator_regression_original_6`, `sigb_b3_span_anchored_termination_bool`, `test_nested_int_int`, `test_nested_int_float`).

**Why A2 was the wrong layer (root-caused from the `M92_COEQ_MERGE` trace):** (1) the 5 trigger branches NEVER directly co-merge — `ConfigKey.state = WpdaState::BinderRule{rule_idx,…}` carries `rule_idx` INDEPENDENTLY of the weight, so dropping `weight_rule_idx` alone does NOT collide them (the §2 "everything else byte-identical" premise is FALSE). (2) The coequal stamp leaks via `fork_child`/`Clone` to descendant body cursors and OVER-MERGES genuinely-distinct reduces (e.g. `rule_idx 34↔5`, `15↔16`) → corrupts the parse + breaks int cross-cat cohort resolution.

**Re-confirms M8.1 + M9 from a third angle:** the operative asymmetry is the **FORWARD CROSS-CAT PROJECTION** of the inner-fold result — int's inner fold projects to Proc (ProcInt redundancy), float's inner `FloatBin` forms a `(Float,[…])` symbol but never projects to Proc over the outer operand span. The FLIP works by changing Fork **structure** (collapsing to a single `FloatBin` `ConsumeAndPush`), which NEITHER the merge layer (A2), NOR the Symbol-`lo_pos` layer (M8.1 Option D), NOR the cohort-projection drain (M9 Option E) can reproduce.

**IMPASSE:** three layer-fixes are now falsified (M8.1 Symbol-`lo_pos`; M9 cohort-projection; A2 Fork-merge). The only proven-working transform is STRUCTURAL (eliminate the competing unary branches / collapse the Fork). The principled fix is now a PLAN-LEVEL REDESIGN: (i) grammar/codegen **left-factoring** of the cast keyword (factor out the common `"kw" "("` prefix so the unary-vs-fold branch is decided AFTER the common prefix by the arg structure — the FLIP's structural effect, generalized), or (ii) a fundamental walker change to how a Fork-resident inner fold's result projects to Proc. Both are significant; ESCALATED to the user. Artifacts: `/var/tmp/suite-green/fork-fix-{M9.2.0-VERDICT,M9.2.3-STOP-VERDICT}.txt`, `fork-fix-A2-ONLY-delta.patch` (760 ins/6 files), tag `fork-fix-A2-falsified` (`a3e69f2`).
