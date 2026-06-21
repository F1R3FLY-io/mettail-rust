# Cast-Keyword Left-Factoring — the Generalized FLIP (experiment #9)

**Base:** `b8b5559` (= `6507b9c` + `/var/tmp/suite-green/sigb-cast-family-FINAL.patch`, Bool-closed; calc 214/6 with the 2 Float targets ERR; gauntlet 4220/0; 221 calc tests in tree).
**Root status:** FLIP-PROVEN (`float-root-PROVEN.md`). Three layer-fixes FALSIFIED (`float-trigger-fork-disambiguation.md` + its `⚠ FALSIFICATION`): M8.1 Symbol-`lo_pos`, M9 cohort-projection drain, A2 Fork-merge. This plan does NOT re-propose any of them. It designs the ONE transform the FLIP proves works — eliminating the competing unary Fork branches — generalized in the codegen as **left-factoring of the shared `"kw" "("` prefix**.

---

## §0 Residual / what is already true (do not re-litigate)

- **The trigger-group Fork** (`emit_binder_prefix_arms`, `macros/src/gen/runtime/wpda_codegen/binder.rs:1138-1177`) emits, for the `float` group in Float ctx (`state_cat_src_idx == 5`), 5 co-cost `ForkBranch`es — generated `wpda.rs:1443-1484`:
  - rule_idx 11 `IntToFloat`, 12 `BoolToFloat`, 13 `StrToFloat`, 14 `FloatId` (unary, `classify_unary_prefix_shape`-NEGATIVE — they're `"float" "(" a ")"`, not `"float" a`), 15 `FloatBin` (fold).
  - All five: `action_kind: Push`, `weight: lex_w(0.0, 5, rule_idx)`, `body_src_idx: 5`, `symbol = rule_at(5, rule_idx, 1, Some(_outer_bp))`.
- **lex-min** `(primary, lex_alt_idx, src_idx, rule_idx)` (`lex_weight.rs:167-193`) collapses to `rule_idx` ascending when the first 3 TIE — the proven premature-disambiguation lever: unary 11-14 out-rank fold 15 BEFORE the `,`/`)` evidence.
- **`classify_binder`** (`binder.rs:278`) builds `BinderShape.positions` by stripping `sp[0]` (the trigger) and lowering the rest. CONFIRMED shapes (positions, post-trigger):
  - `FloatBin`: `[Literal("("), ParamParse{Proc}, Literal(","), ParamParse{Int}, Literal(")")]`.
  - `IntToFloat`: `[Literal("("), ParamParse{Int}, Literal(")")]`; `BoolToFloat`→Bool, `StrToFloat`→Str, `FloatId`→Float.
  - **All 5 share `positions[0] == Literal("(")`, and `positions[1]` is a `ParamParse`** — left-factoring is structurally valid.
- **`ParamParse{cat}` dispatch** (`binder.rs:1538-1565`): `ReplaceAndPush { replace_symbol = rule_at(.., next_pos), push_symbol = category_entry(cat_src_idx), new_state = PrefixDispatch{ pos, cur_bp } }`. The operand parses in its OWN category; on return (Unwinding pops the `category_entry`), the marker sits at `next_pos` (the `,` or `)`).
- **The cross-cat delegate path** (`prefix.rs::emit_cross_cat_prefix_unary_arm`, generated e.g. `wpda.rs:3667`): in a Proc slot (`state_cat_src_idx == 0`) the `float`/`int`/… keyword forks to `CrossCatDelegate{ source_src_idx = 5 }` at `BP_TIER_CROSSCAT_PROJECTION`, which parses the inner cast in its source cat then projects to Proc (`ProcFloat`, `calculator.rs:101`). This is how a nested `float(…)` dispatches inside the outer `a:Proc` slot.
- **`min_terminal_span`** (`wpda_walker.rs:257`; override table generated `wpda.rs:21599`): Float unary `(5,11..14)=1`, fold `(5,15)=2`. Sole authority dropping token-unsound cast fabrications at realize (`resolve` filter, `wpda_walker.rs:4843-4884`). **Untouched by this plan.**
- **`calc_try_bigint_unary`** (`languages/numeric_dispatch.rs:216`) PROVES a unary cast can take `a:&CalcProc` and recover the underlying category at ACTION time (`calc_peel_list_elem` + match on `ProcStr`/`ProcFixed`/…). The single-rule Proc-operand casts `BigintCast`/`BigratCast` (`calculator.rs:389-394`) are the live, working model for a Proc-operand unary close.
- **`subsume_lex_dominated_cursors()` deleted; `bounding_mode = Unbounded`** (`wpda_walker.rs`). Walker keeps all alive cursors.

## §1 Proven-root + falsification recap (confirm-spec; M0 reproduces inert)

The root (FLIP-PROVEN, re-stated for the M0 gate, NOT re-investigated):

- **C1 (Fork is where competition starts):** under `PRATTAIL_TRACE=cursors` on `float(float(10,64),64)`, all 5 inner-`float` branches (11–15) fan out as live cursors. They do NOT co-merge (`ConfigKey.state = BinderRule{rule_idx}` carries `rule_idx`); the A2 premise that dropping `weight_rule_idx` collides them is FALSE.
- **C2 (where it dies, today):** the inner `float(10,64)` is read by the lower-`rule_idx` unary branches (11–14) FIRST; the fold (15) is out-ranked by `rule_idx` before the inner `,` is seen. The unary packing over the 2-arg inner span is token-unsound (span 2 vs `min_terminal_span(5,11..14)=1`) → dropped at realize. So NO inner `Proc`-projecting Symbol is delivered for the OUTER `FloatBin`'s `a:Proc` slot → outer never completes → `resolve_at_end_of_input` `accepting_indices.len()==0` arm (`wpda_walker.rs:4303-4324`) → "no accepting branch reached end of input."
- **C3 (the FLIP, proven):** `FLIP_NOUNARY=1` drops branches 11–14 → inner Fork collapses to a single `ConsumeAndPush`→`FloatBin` → inner `FloatBin` parses, projects to Proc, fills the outer slot → both targets PARSE; controls hold; gauntlet 4220/0.
- **C4 (why int/uint/fixed only LOOK fine):** the operative asymmetry is FORWARD CROSS-CAT PROJECTION of the inner-fold result. Int's inner fold reaches Proc via `ProcInt` redundancy on an alternate non-Fork-starved path; Float's inner `FloatBin` forms a `(Float,…)` Symbol but, under the rule_idx pre-commit, never wins to project over the outer `a:Proc` span. **The lever is symmetric; int merely masks it.**

**Why the three layer-fixes failed and left-factoring is categorically different:** M8.1 (Symbol-`lo_pos`), M9 (cohort-projection drain), and A2 (Fork-merge) ALL tried to make the fold WIN a 5-way disambiguation that is mis-decided by `rule_idx` at Fork time and re-confirmed by realize. None changed Fork STRUCTURE; A2 additionally over-merged distinct reduces and regressed 5 cross-cat tests. The FLIP works ONLY by removing the competing unary branches. Left-factoring is the codegen-level, generalized realization of exactly that structural collapse — it never touches `merge_equivalent_cursors`, `ConfigKey`, the cohort cache, or the weight algebra (the A2 blast surface). **M0 must reproduce C1–C4 inert and STOP if it cannot.**

## §2 The left-factoring transform (the design)

### §2.1 Structural predicate (codegen, keyed on STRUCTURE never a category id)

In `binder.rs`, after the `groups: BTreeMap<(trigger, result_src_idx), Vec<RuleEntry>>` is built (`:1059-1091`), classify each group:

```
classify_trigger_group(entries) -> TriggerGroupKind:
  let folds  = entries where shape.positions == [Literal("("), ParamParse, Literal(","), ParamParse, Literal(")")]   // 2-arg, comma-sep, paren-wrapped
  let unaries = entries where shape.positions == [Literal("("), ParamParse, Literal(")")]                            // 1-arg, paren-wrapped
  if folds.len() >= 1 && unaries.len() >= 1 && folds.len() + unaries.len() == entries.len():
      MixedCastGroup { unaries, fold }     // (assert exactly one fold; see §7 R4 for >1)
  else:
      Plain                                 // emit exactly as today (Fork or single ConsumeAndPush)
```

The predicate is **purely structural** — paren-wrapped `"kw" "("` prefix, mixing ≥1 single-`ParamParse`+`)` unary with ≥1 `ParamParse "," ParamParse )` fold. It is NOT `classify_unary_prefix_shape` (those are bare-operand `"-" a`, which never have the `(` prefix). It matches `float`/`int`/`uint`/`fixed` (each: 3-4 unaries + 1 fold) and NOTHING else: cos/sin/ln/exp are unary-only single-rule (already `ConsumeAndPush`, never a group ≥2); `bigint`/`bigrat` are unary-only single-rule; operator tiers, projections, lex-alt, opt-group, paren-grouping (`(`-trigger, skipped at `:1079`) are all emitted by other code paths and never enter `emit_binder_prefix_arms`'s group map with this shape. **M1 unit-asserts the predicate (TRUE for the 4 mixed groups, FALSE for every other group across all test languages).**

### §2.2 Emitted structure — common prefix + evidence dispatch (the generalized FLIP)

For a `MixedCastGroup`, replace the 5-way `Fork` (`:1169-1177`) with a single arm that:

**(a) Common prefix `"kw" "("`** — one open arm. Emit a NON-Fork `ConsumeAndPush` that consumes the trigger (`consume_trigger` semantics preserved) and transitions to a **single dispatch state** carrying the fold's identity as the canonical marker, because the fold's first arg (`a:Proc`) is the WIDEST first-arg parse:

```
Fixed(__trigger) if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
    ConsumeAndPush {
        symbol:    rule_at(#result_src_idx, #fold_rule_idx, 1u8, Some(_outer_bp)),
        weight:    lex_w(0.0, #result_src_idx, #fold_rule_idx),
        new_state: BinderRule { result_src_idx, rule_idx: #fold_rule_idx, body_src_idx, outer_bp },
        trigger_mode: Discard,
    }
}
```

This is byte-identical to what `FLIP_NOUNARY=1` produces (single `ConsumeAndPush`→fold). Position 1 = `Literal("(")` is consumed by the fold's existing pos-1 `GuardedConsumeAndReplace` arm (`emit_binder_rule_body`, `:1225-1253`). **No unary branch is emitted at the prefix** — that is the structural collapse, generalized.

**(b) First-arg sub-parse — single, in the fold's `Proc` category.** The fold's pos-2 `ParamParse{Proc}` (`:1548-1565`) fires UNCHANGED: pushes `category_entry(Proc_src_idx)`, `PrefixDispatch{cur_bp}`. ONE sub-parse serves both readings because `Proc` is the join of all unary source cats (Int/Bool/Str/Float all project into Proc via `ProcInt`/`ProcFloat`/`ProcBool`/`ProcStr`, `calculator.rs:100-103`). A nested inner `float(…)` reaches Proc via the existing `CrossCatDelegate` arm (unchanged).

**(c) Post-prefix evidence dispatch — the `,`-vs-`)` decision at fold position 3.** After arg 1 returns, the fold marker is at pos 3 = `Literal(",")`. TODAY that is a 1-branch `GuardedConsumeAndReplace{expected_text: ","}` (`:1225-1253`) — it consumes `,` on match and DIES on `)` (empty-children death, `step_fanout`). For a `MixedCastGroup` fold, **`emit_binder_rule_body` emits a 2-branch guarded Fork at this position** (the machinery already exists — see the `peek_text`-guarded 2-branch forks at `:1442-1535`):

```
(#result_src_idx, #fold_rule_idx, #comma_pos) => {
    let _ = tokens.peek_text(_pos);
    Fork { branches: vec![
        // BRANCH 0 — FOLD continuation (evidence: peek == ","):
        ForkBranch {
            symbol:    rule_at(#result_src_idx, #fold_rule_idx, #next_pos, Some(*outer_bp)),
            weight:    lex_w(0.0, #result_src_idx, #fold_rule_idx),
            new_state: BinderRule { rule_idx: #fold_rule_idx, .. },
            action_kind: GuardedConsumeAndReplace { expected_text: "," },   // fires iff peek==","
        },
        // BRANCH 1 — UNARY close (evidence: peek == ")"):
        ForkBranch {
            symbol:    rule_at(#result_src_idx, #unary_close_rule_idx, #unary_close_pos, Some(*outer_bp)),
            weight:    lex_w(0.0, #result_src_idx, #unary_close_rule_idx),
            new_state: BinderRule { rule_idx: #unary_close_rule_idx, .. },
            action_kind: GuardedConsumeAndReplace { expected_text: ")" },   // fires iff peek==")"
        },
    ], consume_trigger: false }
}
```

The two branches are **mutually exclusive by the guard token** (`,` vs `)`) — pure EVIDENCE, never declaration order or weight. Exactly one survives `step_fanout`'s guard check; the other allocates no child. (Weights/`rule_idx` here are irrelevant to the choice — the guard, not lex-min, decides. They remain well-formed for the surviving cursor's downstream packing.)

### §2.3 The unary-close rule selection (which `XToY` cast fires on `)`)

This is the hard part the prompt flags: a SINGLE Proc first-arg parse must, on `)`, fire the CORRECT unary cast. Two design options; **Option U-PROC is RECOMMENDED.**

**Option U-PROC (RECOMMENDED) — collapse the unaries to ONE Proc-operand unary cast (the `BigintCast` model).** The four unary casts `IntToFloat`/`BoolToFloat`/`StrToFloat`/`FloatId` differ ONLY in their source-cat extraction; their result is identically `Float` and their semantics are "interpret the operand as a float." This is EXACTLY what a Proc-operand unary already does: `BigintCast . a:Proc |- "bigint" "(" a ")"` dispatches at action time via `calc_try_bigint_unary` peeling the Proc variant. The design therefore treats the unary-close BRANCH 1 as a **synthesized Proc-operand unary close over the SAME first-arg Proc**: `unary_close_rule_idx` = a single canonical unary cast whose action recovers the source from the Proc operand (mirroring `calc_try_*_unary`). For the calculator this is a grammar-level consolidation handled by the macro: when a `MixedCastGroup` is detected, the unary casts collapse into one `XProcUnary` whose action is the existing per-source match (the macro already generates such helpers — `numeric_dispatch.rs`). The post-prefix dispatch then has exactly TWO outcomes (fold vs the one Proc-unary), both consuming the SAME arg-1 Proc Symbol. This reproduces the FLIP's structure precisely (one fold + one unary, no rule_idx competition) and the `)`-vs-`,` guard is the sole discriminator.
  - *Why this is sound:* the unary-close action is `calc_try_<kw>_unary(&a_proc)` — the same total, fallible, source-peeling dispatch as `BigintCast`. `float(10.5)` → arg-1 Proc = `ProcFloat(10.5)` → `)` → Proc-unary → `CanonicalFloat64::from(10.5)`. `float(true)` → `ProcBool(true)` → `1.0`. Identical results to today's per-source unary actions; the source-cat branch lives in the action, not the parse.
  - *Standalone unary casts keep working* because the `)` guard fires BRANCH 1 and the Proc-unary action handles every source variant.

**Option U-DISPATCH (FALLBACK, if U-PROC's action-consolidation proves invasive) — keep the typed unary rules, dispatch BRANCH 1 by the realized arg-1 category.** Parse arg 1 as Proc as in (b); on `)`, instead of one Proc-unary, emit BRANCH 1 as an INNER guarded sub-Fork over the typed unary rules, each gated by the realized first-arg's underlying category (read from the arg-1 Symbol's `src_idx`, available on the SPPF Symbol the sub-parse delivered). The inner arg already carries its category (the Proc projection wraps a typed inner Symbol); a small per-branch guard `inner_symbol_src_idx == {Int|Bool|Str|Float}` selects `IntToFloat|BoolToFloat|StrToFloat|FloatId`. This keeps the existing 4 typed actions but adds a category-keyed guard. It is strictly more code than U-PROC and reintroduces a 4-way (guarded, evidence-driven, NOT rule_idx) sub-choice; use ONLY if M0/M1 show U-PROC's action consolidation perturbs a non-cast rule. **Decision recorded at M0** based on the trace.

In BOTH options the choice is by EVIDENCE (the `)` token + the realized arg category), never declaration order/weight; `min_terminal_span` remains the realize backstop.

### §2.4 Unary-only groups left UNCHANGED (cos/sin/ln/exp/bigint/bigrat)

`classify_trigger_group` returns `Plain` for every non-mixed group, so the existing `:1095-1135` single-rule `ConsumeAndPush` path (cos/sin/ln/exp, bigint/bigrat — each a lone rule in its `(trigger, result)` group) and the existing multi-rule `Fork` path (any genuine same-result multi-rule group that is NOT a cast-mixed shape) are emitted **byte-for-byte as today**. No unary-only group has a fold, so none matches `MixedCastGroup`. **This is the explicit non-regression guarantee for the #1-risk "unary-only trigger groups."**

### §2.5 Cross-cat / chain preservation argument (why this does NOT regress where A2 did)

- **A2 regressed cross-cat** because it mutated `merge_equivalent_cursors`/`ConfigKey` GLOBALLY (the coequal stamp leaked via `fork_child`/`Clone` and over-merged distinct reduces `34↔5`, `15↔16`, corrupting the int cross-cat cohort resolution). **Left-factoring touches NEITHER `merge_equivalent_cursors`, `ConfigKey`, the dispatch cohort cache (`wpda_walker.rs:13262+`), nor the weight algebra.** It is a pure CODEGEN emission change: fewer Fork branches at one prefix arm + one extra guarded branch at the fold's comma position. The walker runs unchanged.
- **The cross-cat delegate path is untouched.** When `float(…)` appears in a Proc slot, the `CrossCatDelegate{source 5}` arm (`prefix.rs::emit_cross_cat_prefix_unary_arm`) fires; it re-enters the SAME Float-ctx prefix dispatch — which, post-fix, is the collapsed common-prefix arm. So nested casts inside cross-cat operands route through the new (simpler) structure with no special-casing. The 5 A2-regressed tests (`parse_int_cross_cat_comparison_le`, `simulator_regression_original_6`, `sigb_b3_span_anchored_termination_bool`, `test_nested_int_int`, `test_nested_int_float`) exercise `int(PREDICATE)` / nested int casts: their parse paths (IntBin fold + predicate sub-parse + ProcInt projection) are structurally preserved because the `int` group's collapse is the SAME shape transform as `float`'s, applied symmetrically — the int fold is no longer out-ranked by typed-int unary branches, but the int fold ALREADY won at baseline (redundancy), so its successful path is preserved and merely de-competed. M0 confirms inert; the gates (§6) are the tripwire.
- **Chains (Welch) are cast-free.** No chain Fork has the `"kw" "(" ParamParse ("," ParamParse)? ")"` shape; `classify_trigger_group` returns `Plain` for every chain/operator construct → the chain emission is byte-identical → the landed chain Welch wins are untouched **by construction** (no walker change at all, unlike A2 which changed `merge_equivalent_cursors` that chains DO traverse). §6 still runs the Welch A/B as the leakage tripwire.

## §3 Termination / boundedness (RIGOROUS, bounded)

- **Cursor count strictly DECREASES at the prefix.** Today the prefix fans out 5 cursors; post-fix it pushes 1 (the common-prefix `ConsumeAndPush`, zero fan-out). At the fold's comma position it forks 2 (fold-cont vs unary-close), of which exactly 1 survives the `peek_text` guard within the SAME step (the other allocates no child — `step_fanout` empty-children). Net peak `branch_cursors` at every step ≤ today's (5→1, then 2→1). No new unbounded fan-out.
- **Evidence prune is O(1) tokens.** The `,`/`)` decision is a single `peek_text(_pos)` at the comma position; the losing branch dies immediately (1 token). No paren-balanced scan, no lookahead loop.
- **GLL descriptor-uniqueness** (`wpda_walker.rs:6644`) and **bounded-recovery cycle defense** (`:6599`, `:5859` CrossCatDelegate cycle guard) are unchanged — the new arms reuse existing `ConsumeAndPush`/`Fork`/`GuardedConsumeAndReplace` actions which already participate in those bounds.
- **Genuine ambiguity** (none for casts — arity is decided by the `,`/`)` evidence) → both reach EOI → `accepting_indices.len() >= 2` arm (`:4376`) → `Ambiguous`, realized under the existing `Some(64)` cap. Preserved.
- **No recursion added.** Left-factoring reduces branching; it cannot introduce a non-terminating cycle the 5-way Fork didn't already have.

## §4 Invariants to preserve

- **Soundness stays on EVIDENCE:** `min_terminal_span` realize filter (`wpda_walker.rs:4843-4884`; table `wpda.rs:21599`, Float `(5,11..14)=1`/`(5,15)=2`) UNTOUCHED — sole authority dropping fabricated casts. The fix changes WHICH cursors are emitted, never which derivations are token-sound.
- **`Ambiguous` first-class** (`:4376` arm + multi-root realize) unchanged.
- **Standalone unary casts** (`float(10.5)`, `int(true)`, `float(float(3))`): the `)` guard fires the unary-close branch; the Proc-unary action (U-PROC) or category-dispatched typed unary (U-DISPATCH) completes. Nested-unary `float(float(3))`: inner `float(3)` parses via the same collapsed prefix (arg `3`→Proc, `)`→Proc-unary→Float), projects to Proc for the outer arg, outer `)`→Proc-unary→Float.
- **Must-not-perturb (verified at §6):** Bool win (`calculator.rs:2188` test = `int(y != true > x < "qua")`), the 3 M3.1 sentinels (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `test_nested_int_int`), `test_nested_float_int_arithmetic` (`calculator.rs:1074`), the 5 A2-regressed cross-cat tests, `cross_cat_with_parens`/`strings`, op-suites ≥1331/532, soundness/`-3!`/parity, the chain Welch wins, gauntlet 4220/0.
- **A/B disable lever** `B6_LEFTFACTOR_DISABLE=1` (env, read at codegen): when set, `classify_trigger_group` returns `Plain` for ALL groups → the 5-way Fork is emitted exactly as today → byte-identical pre-fix behavior. Clean isolation (mirrors the A2 `B5` lever discipline). Because the lever lives in CODEGEN, A/B requires a rebuild per arm (acceptable — one 32G build each).

## §5 Milestones

- **M0 — DIAGNOSTIC-CONFIRM gate (BLOCKING; the M*.0 gate the prompt requires FIRST).** Under `systemd-run --user --scope -p MemoryMax=32G`, ONE build at a time:
  1. Reproduce C1–C4 inert (`PRATTAIL_TRACE=cursors` on `float(float(10,64),64)`): 5 inner branches fan out, fold out-ranked by rule_idx, unary packing min_span-dropped, outer slot unfilled.
  2. Re-confirm the FLIP (the target structure): manually gate the prefix to a single fold `ConsumeAndPush` (the `FLIP_NOUNARY` transform, applied as a SCRATCH/untracked codegen toggle — NOT committed) and verify both targets PARSE + controls hold. This is the structure §2.2 reproduces.
  3. **Decide U-PROC vs U-DISPATCH** from the trace: confirm `float(10.5)`/`float(true)`/`float("3")` arg-1 parses to a `ProcFloat`/`ProcBool`/`ProcStr` Symbol whose variant the Proc-unary action can recover (U-PROC viable) OR whose `src_idx` the category guard can read (U-DISPATCH). Confirm the comma-position 2-branch guarded Fork (`,` vs `)`) is expressible with the existing `GuardedConsumeAndReplace` action (it is — `:1225-1253` + `:1442-1535`).
  4. Confirm chain/cross-cat neutrality of the predicate: `classify_trigger_group` marks ONLY the 4 mixed cast groups; dump the group classification for calculator + rhocalc + every test language and assert no chain/operator/projection group is `MixedCastGroup`.
  **STOP if** the FLIP structure can't be reproduced by the planned emission, OR the predicate marks any non-cast group, OR U-PROC/U-DISPATCH both perturb a non-cast rule.
- **M1 — predicate.** `classify_trigger_group(entries) -> TriggerGroupKind` in `binder.rs` (structural: paren-prefix mixed unary+fold). Unit-assert TRUE for float/int/uint/fixed, FALSE for cos/sin/ln/exp/bigint/bigrat/paren-groups/operator-tiers across all languages. Wire `B6_LEFTFACTOR_DISABLE`.
- **M2 — common-prefix emission.** In `emit_binder_prefix_arms` (`:1094` group loop), branch on `classify_trigger_group`: `MixedCastGroup` → emit the single fold `ConsumeAndPush` (§2.2a); `Plain` → existing code unchanged.
- **M3 — comma-position evidence dispatch.** In `emit_binder_rule_body`, for the fold rule of a `MixedCastGroup`, emit the 2-branch guarded Fork at the comma position (§2.2c). Implement the chosen unary-close (U-PROC: synthesize/route the Proc-unary action; U-DISPATCH: category-keyed sub-Fork).
- **M4 — regenerate + targeted green.** ONE 32G build. `test_nested_float_float_int` + `test_triple_nested_float` PARSE; `float(10.5)`/`int(true)`/`float(float(3))` PARSE; spot-check the generated `wpda.rs` float arm = single `ConsumeAndPush`→15 + 2-branch comma Fork.
- **M5 — generality + symmetry.** Confirm `int`/`uint`/`fixed` groups collapse identically (generated arms); `int(int(5,32),32)`, `int(float(42,64),32)`, `uint`/`fixed` nested-fold analogues PARSE; int-nested now via the robust collapsed path (not solely redundancy).

## §6 Gates (all pass before commit)

- **calc 215/1:** `cargo test -p languages --test calculator` → the 2 Float targets flip to PASS; zero regressions (215 pass + the 1 intentional-ambiguous). Explicitly re-assert: Bool win (`:2188`), the 3 M3.1 sentinels, `test_nested_float_int_arithmetic`, and **all 5 A2-regressed cross-cat tests** (`parse_int_cross_cat_comparison_le`, `simulator_regression_original_6`, `sigb_b3_span_anchored_termination_bool`, `test_nested_int_int`, `test_nested_int_float`) GREEN.
- **Welch (dominant tripwire):** chain Welch A/B `B6_LEFTFACTOR_DISABLE` ON vs OFF over the cast-free chain corpus, N≥51 → live-cursor distributions statistically indistinguishable. (Expected trivially PASS — no walker change — but it is the leakage tripwire for the predicate.) Any drift ⇒ predicate marked a chain group ⇒ STOP + re-scope.
- **Cross-cat sweep:** the full cross-cat suite (`cross_cat_dispatch_chaining`, `cross_cat_with_floats`, `cross_cat_with_parens`, `cross_cat_with_strings`, the comparison_le/ge families) GREEN.
- **Sweep:** op-suites ≥1331/532, soundness, `-3!`, parity, `prattail --lib` gauntlet 4220/0. One 32G-capped build per arm.

## §7 Risks

- **R1 (dominant) — predicate leaks onto a non-cast group** → fully structural (paren-prefix + mixed unary+fold arity); M0/M1 dump-and-assert across all languages; Welch + cross-cat gates are tripwires; `B6` lever isolates. Lower blast radius than A2 (codegen, not walker).
- **R2 — U-PROC action consolidation perturbs a non-cast rule** → confine the unary-action consolidation to rules in a `MixedCastGroup`; if M0 shows perturbation, fall back to U-DISPATCH (typed unaries + category guard). Decision gated at M0.
- **R3 — the comma-position guard mis-fires on whitespace/EOI** → reuse the existing `peek_text(_pos)` + `GuardedConsumeAndReplace` semantics verbatim (already correct for the 1-branch comma case today); the 2nd branch only ADDS a `)` guard. `min_terminal_span` is the realize backstop if both somehow survive.
- **R4 — `>1 fold per group`** (no current language has it; calculator has exactly one fold per cast trigger) → `classify_trigger_group` asserts `folds.len() == 1` for `MixedCastGroup`; if a future grammar has multiple folds sharing `"kw" "("` with differing arg shapes, fall back to `Plain` (today's Fork) for that group and widen the design in a follow-up. Documented, not silently mis-handled.
- **R5 — the collapsed single-fold prefix changes `body_src_idx` semantics** → `body_src_idx` for the fold is already `result_src_idx` (5, since `FloatBin.body_cat` is None — confirmed generated `wpda.rs:1477`); the common-prefix arm uses the fold's existing `body_src_idx`, no new value. Verified at M4 by diffing the generated arm.
- **R6 — A/B requires rebuild** (lever in codegen not walker) → accepted; one 32G build per arm, matching the project's established build discipline.

## §8 Critical sites

- `macros/src/gen/runtime/wpda_codegen/binder.rs:1094-1177` — group loop + the trigger-group Fork emission; add `classify_trigger_group` + the `MixedCastGroup` common-prefix `ConsumeAndPush` (§2.1, §2.2a).
- `macros/src/gen/runtime/wpda_codegen/binder.rs:1190-1253` (`emit_binder_rule_body`, the `Literal` comma-position arm) + `:1442-1535` (the existing 2-branch `peek_text`-guarded Fork model to mirror) — the post-prefix `,`-vs-`)` evidence dispatch (§2.2c, §2.3).
- `macros/src/gen/runtime/wpda_codegen/binder.rs:1538-1565` (`ParamParse{cat}` dispatch) — the single first-arg `Proc` sub-parse (read-only reference; unchanged) (§2.2b).
- `languages/numeric_dispatch.rs:175-232` (`calc_try_float_bin`, `calc_try_bigint_unary`) — the proven Proc-operand action-time source-recovery model for U-PROC (§2.3).
- `prattail/src/wpda_walker.rs:6427` (Fork arm), `:7849` (`GuardedConsumeAndReplace` apply), `:13262`/`:5859` (CrossCatDelegate + cycle guard) — UNCHANGED; the read-only confirmation that the walker needs no edit (the §2.5 cross-cat/chain-preservation argument).
- `prattail/src/wpda_walker.rs:4286-4324` (resolve/accepting), `:4843-4884` + `:257` (`min_terminal_span`), `prattail/src/automata/lex_weight.rs:167-193` (lex-min order) — the soundness/resolution authorities the fix must leave intact.

---

## Provenance

Designed by Plan agent `acb0fc85` (2026-06-02), grounded entirely by reading the proven docs + codegen + generated `wpda.rs` + walker + grammar + runtime dispatch (the FLIP — the target structure — is already PROVEN in `float-root-PROVEN.md`, so no build was needed for the design; the single 32G build belongs in M0 of implementation). The A2-regression blast surface (`merge_equivalent_cursors`/`ConfigKey`/cohort cache) is entirely untouched by a codegen emission change — that is precisely why left-factoring is categorically safer than A2. Supersedes Candidate A2 (FALSIFIED, tag `fork-fix-A2-falsified`) and the M8.1/M9 layer-fixes (FALSIFIED).