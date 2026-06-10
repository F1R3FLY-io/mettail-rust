# Phase 5A — cast-then-compare parse failure: root-cause ledger

> Scientific ledger for the cast-comparison family (~78 of the 217 baseline
> failures). Records the CONFIRMED failure, the hypotheses FALSIFIED by experiment
> (so they are not re-attempted), and the localized bedrock + the next drill. Per
> the standing mandate: prove the root by a flip BEFORE naming a fix; document what
> does not work. pgmcp #265; local task #5.

## ★★ TRUE ROOT — PROVEN (2026-06-10, fresh-context re-investigation) — lex-fork drops keyword dispatch

**The pre-compaction "cast/EqInt evidence" framing (H1–H4 below) chased the wrong layer.**
Fresh reproduction at HEAD `65b40581`: `gen_rhocalc_op` = **33 fails** (30 ×
`eval_rhocalc_*_err_err_smoke` → *"frontier of 17 cursors exceeds budget of 16"* + 3 ×
map); `gen_calculator_op` = **156 fails**, dominated by collection ops (`at`/`delete`/
`concat`/`length`/`get`/`keys`/`put`/`merge`/`union`/`remove`/`diff`/`count`) all
`"unexpected Fixed(\"(\") after parsing"`. Same `"unexpected Fixed(\"==\")"` shape as the
cast family (line below) — ALL are the SAME root.

**Single common root (PROVEN — lattice probe + 6.5M-line walker trace + code read):**
keywords that ALSO match the ident regex (`list`/`bag`/`map`/`at`/`error`/`int`/…) make
`lex_dag` emit a SAME-LENGTH lattice ambiguity `{Fixed("kw"), Ident}` (probe: `list(5)`
pos 0 primary=`Fixed("list")`, alt=`Ident` end_byte=4). `is_ambiguous_at` ⇒ the lex-fork
(`emit_lex_fork_at_prefix_dispatch`, `forks.rs:150`) fires and rebuilds dispatch via
`lex_alt_rules_for_prefix`, whose `LexAltRuleKind` only covers `Atomic|PrefixOp|
CrossCatProjection` (`_ => {}` drops collection-literal ListLit/BagLit/MapLit and
multi-token keyword-prefix rules like ElemList `at(...)`). The keyword branch is
dropped/over-forked, so the lex-fork `return`s a Fork of only the secondary `Var`
branch(es) ⇒ the keyword parses as a bare variable, `(...)` trails (collections /
ops), or the 11-way cross-cat `Ident→Var` fan-out blows the 16-cursor budget
(`error op error`). Trace (`list(5)`): max pos = 1 (never consumes `(`), `coll_depth`
never > 0, `CollectionOpenParen` never entered, 333,567-step livelock.

**FIX (designed-but-unwired mechanism, now wired):** `kind_dispatch.rs` already generates
`prefix_primary_has_dispatch_rule(cat, kind)` — docstring: *"The lex fork uses this to
avoid replacing a valid primary keyword/binder arm with a lone secondary Ident -> Var
branch"* — true for `NonAtomic` rules whose first syntax literal matches (ListLit
`"list"`, ElemList `"at"`) and for `TerminalKeyword`/`PrefixOperator`/`CrossCatPrefixUnary`
triggers (Err `"error"`). It was **NEVER CALLED** (only `mod.rs:624` asserts it is
generated). Wire it into the lex-fork fall-through, guarded SAME-LENGTH so genuine
multi-length `{Minus@1, Integer@2}` (`-3`) keeps forking: fall through to the normal
`match peek` dispatch (which has the collection + keyword-prefix arms) when
`prefix_primary_has_dispatch_rule(primary_src, primary_kind) && all alts same-length`.
Keyword-reservation at a same-length lexical tie: the explicitly-declared keyword beats
the auto-injected `Var` fallback. Probe: `languages/examples/lex_probe.rs` (DELETE after).
Baselines: `/tmp/5a-rhocalc-op-baseline.txt`, `/tmp/5a-calc-op-baseline.txt`.

**RESULT (VERIFIED, 2026-06-10):** one-line wiring in `forks.rs`
(`emit_lex_fork_at_prefix_dispatch` fall-through) fixed **189 of the 217** baseline
op-suite failures with **ZERO regressions** (exact failing-set diff, not just counts):
`gen_calculator_op` 156→6, `gen_rhocalc_op` 33→1, `edge_case_tests` 28→21; prattail lib
stays 3979/0. FV: `LexForkKeywordReservation.v` (5 theorems, registered in `_CoqProject`,
`make check-capped FORMAL_CAPPED_TARGET=rocq-prattail-wpda` green; `Print Assumptions` =
"Closed under the global context" — zero-admission/zero-axiom). The remaining **28** are
the genuinely-separate **cast-then-compare** family (`comparison_after_cast_results::*`,
`{eq,ne,lt,gt,le,ge}fixed_casterrfixed`, `castop_putmap_castbigrat`, `operator_chains_
after_casts`, `postfix_cross_category`) + 2 ambient (`nested_new`, `parallel_ambients`) —
the `==`/infix CANNOT attach AFTER a cast result (`int(3.14) == 3` → `1:11: unexpected
Fixed("==")`). That is the ORIGINAL Phase 5A target (a normal-InfixLoop attachment root,
NOT the lex-fork) — next sub-task. DRILL instrumentation removed; probe deleted.

### Cast-compare BEDROCK — EVID-confirmed (2026-06-10)
Probe discriminator (calculator): literals `3 == 3`/`3.0 == 3.0`/`true == true` OK; cast +
CATEGORY-CHANGING infix `int(3) == 3`/`float(3) == 3.0` (EqInt/EqFloat →Bool) FAIL; cast +
SAME-cat infix `int(3) + 3` OK; cast to Bool `bool(1) == true` (EqBool Bool→Bool, not
category-changing) OK; cast alone `int(3.14)` OK. ⇒ failure = *a cast result as LHS of a
CATEGORY-CHANGING infix*. Trace (`PRATTAIL_TRACE=actions`): `int(3) == 3` → 7×
`suppress category-changing infix source=2 result=7 evidence=None`; `3 == 3` ALSO emits 7
suppresses BUT parses OK (a literal's cross-cat-LHS delegate keeps a `CrossCatLhs{Int}`
edge → pop→reentry → `evidence=Some(2)` → guard admits EqInt). Temp trace in
`cross_cat_lhs_infix_evidence_source` (`wpda_walker.rs:6405`, since removed) showed the
cast result's InfixLoop top = `CategoryEntry{cat=2 Int}` with **`edge=Some(Generic)`** (NOT
CrossCatLhs/Reentry/Projection) ⇒ `_ => None` ⇒ suppressed. ROOT: the cast's
`CrossCatLhs{Int}` delegate edge is BURIED during the cast's own nested cross-cat
projection, leaving a plain `Generic` top. FIX LOCUS: mirror the reentry at
`apply_pop_body_to_cursor:15508-15527` but for the CAST RESOLUTION — lay down
`CrossCatLhsReentry{result-cat C}` when a cast resolves to a cross-cat-infix-SOURCE C and
heads to InfixLoop. NARROW (cast-result only, keyed by RESULT cat) — a blanket relax = the
H2 bypass that regressed 27 `-3!`. Needs a trace of the cast's exact pop/edge sequence
(the `==` top is `Generic`, so the laydown is at the cast's POP, not the infix step)
BEFORE editing → a dedicated focused effort (this is the multi-layer cross-cat area the
prior session churned; drill-to-bedrock-first per the anti-churn discipline).

### Cast-compare — FALSIFIED approach #1 (2026-06-10, reverted) + deepened bedrock
POP-sequence trace (temp `[wpds-POP]` in `apply_pop_body_to_cursor`, since removed) for
`int(3) == 3` shows the cast DOES set up a `CrossCatLhs{2}`/`CrossCatLhsReentry{2}` edge
but it is POPPED at **pos=3** (the cast's `)`, pred=`CategoryEntry{7=Bool}`) — ONE token
BEFORE `==` at pos=4 — leaving a `Generic`-edge top. Why: the cast's Int ARGUMENT (`3`)
is itself an Int (a cross-cat source) so it spawns a NESTED CrossCatLhs reentry that the
cast's `)` close pops; the OUTER cast-result evidence is never established.

**FALSIFIED FIX #1 (do NOT retry):** adding a parallel re-establishment block in
`apply_pop_body_to_cursor` after the CrossCatLhs reentry — "when `popped_edge ==
CrossCatProjection` && popped is `CategoryEntry` && eff=InfixLoop, re-push
`CategoryEntry{last_action_output_cat}` + `CrossCatLhsReentry`" — FAILED: `int(3) == 3`
still failed AND it REGRESSED `int(3) != 3` (col 8 → col 4, the cast's own `(` now
trailed). Reason: a cast emits MANY `CrossCatProjection` CategoryEntry pops DURING its
internal/arg parse, so the block fires mid-cast and corrupts the cast's `(arg)` frames.
The re-establishment must fire ONLY at the OUTERMOST cast-result resolution, which cannot
be distinguished from internal cast frames by `(edge, popped.kind, eff)` alone.

**NEXT (dedicated, cursor-identity trace required):** instrument a SINGLE cursor's frame
stack across the whole `int(3) == 3` parse (cursor id + GSS stack snapshot per step) to
identify the exact step where the EqInt-bearing cursor loses its reentry, and re-establish
evidence ONLY there (gated by cast-result-outermost, e.g. the cast's Return resolving into
the enclosing CategoryEntry, not an internal arg CategoryEntry). This is the careful
frame-level effort the anti-churn discipline reserves for this exact (furious-history)
cast-family bug — NOT another `(edge,kind,eff)` guess.

---

## Confirmed failure (reproduced, `feature/wfst-architecture`)

```
cargo test -p mettail-languages --test edge_case_tests comparison_after_cast_results::int_cast_eq
  → parse("int(3.14) == 3") failed: 1:11: unexpected Fixed("==") after parsing
     (the WPDS parser finished but input remains)
```
The cast term `int(3.14)` parses as a COMPLETE term (interned as category `Int`,
the cast TARGET — verified by trace, NOT mis-classified), but the following infix
comparison (`==`, `>=`, …) cannot attach. `int(3.14) == 3` is a VALID calculator
expression (cast → `3`, then `3 == 3` → true), so this is a REAL parse bug, not a
correct WFST-dead-rule rejection. ~78 cast-family failures share this shape
(`edge_case_tests::{comparison_after_cast_results, operator_chains_after_casts,
postfix_cross_category}` + `gen_calculator_op::cross_cat_calculator_cast*`).

Cast rule: `FloatToInt . a:Float |- "int" "(" a ")" : Int ![a.get() as i32] step;`
(`languages/src/calculator.rs:233`). Source = Float(6), target = Int(2).

## Hypotheses FALSIFIED by experiment (do NOT re-attempt)

### H1 — EOI source-ordering / `CrossCatDelegate.source_src_idx` (the plan's hypothesis): **REFUTED**
History bisection (dedicated investigation): the failure is character-identical at
`1c08c3b2` (the PARENT of `97f06c46` "Fix lattice WPDA EOI source ordering") and at
`7f0b654e` (parent of `141d56ae`, which introduced `guard_category_changing_infix`).
The bug PREDATES both. `97f06c46` only changed the trailing-token error *position*
(`pos < eof_node` → `pos != eof_node`), not whether the parse fails. Trace shows the
cast result interns as `nt=2` (Int = target), so the category index is NOT mis-set.

### H2 — `guard_category_changing_infix` evidence suppression (the proximate gate): **REFUTED**
Flip experiment (DIAGNOSTIC, reverted): bypassing `guard_category_changing_infix`
(`prattail/src/wpda_walker.rs:6425`, `return action` at entry) so it never suppresses
the category-changing infix.
- Predicted (by the proximate hypothesis): cast cases flip fail→pass.
- OBSERVED: cast cases STILL FAIL (12 failed / 2 passed, UNCHANGED), AND the
  `-3!`/ambiguity controls in `languages/tests/calculator.rs` REGRESSED (199→ with 27
  failures). ⟹ the guard is NOT the gate blocking the cast-compare parse; it IS
  load-bearing (its removal over-generates ambiguous derivations). Suppressing the
  guarded consume path is downstream of the real cause.

## Localized bedrock (the surviving explanation)

A cast-result operand never gets the **bp:5 cohort cross-category infix projection**
that a plain literal operand gets. Trace discriminator (`1 == 1` PASS vs
`int(3.14) == 3` FAIL, same `EqInt` rule):
- `1 == 1`: a cohort dispatch `key=pos:1 src:2 bp:5 wrap=(7,0)` (EqInt Int→Bool
  projection) fires (22×), launching `transient start cat=7 rule=0 arity=2` →
  interns Bool over the full input.
- `int(3.14) == 3`: NO `wrap=(7,0)` dispatch, NO `cat=7 rule=0 arity=2`, max binding
  power reached is **bp:0** (never the operator's bp:5), max span `[0,5]` (the `==`
  is never consumed). The cast result reaches an accepting `Int` configuration at
  bp:0 and unwinds WITHOUT re-entering the bp:5 infix dispatch.

Control confirming the mechanism: `bool(1) == true` PASSES because `IntToBool` →
Bool and `EqBool` is Bool→Bool (NOT category-changing), so it takes a different
(working) path. The bug is specific to casts whose TARGET category differs from the
comparison's RESULT category (Int/Float casts feeding Int→Bool / Float→Bool
comparisons) — matching the 12-fail / 2-pass split exactly.

## Next drill target (to nail bedrock) + candidate fix directions

**Drill:** the operand-resolution → infix-dispatch transition. After a literal
operand resolves, `WpdaEvent::BranchResolved` (`prattail/src/wpda_walker.rs:3991`)
sets `InfixLoop { cur_bp: 0 }` and the codegen-emitted InfixLoop step peeks the
operator, computes its binding power, and schedules `wrap=(result_cat, rule)` at that
bp. Compare the cursor / GSS state at the moment `==` is peeked for a `span=[0,1]`
literal operand vs the `span=[0,5]` cast result — find why the cast cursor does not
schedule the bp:5 cohort projection (e.g. the cast result is delivered on a
GSS/cursor path that does not feed the cohort infix-dispatch scheduler, or its
`wrap`/cohort key is keyed by the cast rule rather than `(Int, ·)`).

**Candidate fix directions (to be flip-proven before adopting):**
1. Schedule the bp:5 cohort cross-cat infix projection for cast-result operands the
   same way literal operands get it (the missing dispatch) — preferred, addresses
   the cause directly.
2. Have a cast result lay down the `CrossCatLhs` evidence edge
   (`prattail/src/wpda_walker.rs:7642`) so the guarded consume path is permitted —
   but H2 showed the consume path alone does not fire `EqInt` for a cast LHS, so this
   is likely insufficient on its own.
Do NOT delete `guard_category_changing_infix` (H2 proved it load-bearing).

**FV obligation (when fixed):** extend `RuntimeModel.v` with
`cast_result_infix_dispatch_complete` (a cast result of category C admits the same
infix continuations as a literal of category C) — the genuine model, not a static
count-lemma.

## Deeper trace evidence (PRATTAIL_TRACE=actions, with `[wpds-DRILL]` instrumentation)

Tracing `int(3.14) == 3` confirms:
- `[wpds-DRILL] PushWithEdgeKind sym_cat=5 pos=2 edge=CrossCatLhs { source_src_idx: 5 }
  new_state=PrefixDispatch { pos: 2, cur_bp: 0 }` — the cast pushes a `CrossCatLhs`
  edge whose `source_src_idx = 5` (**Fixed**, the cast's SOURCE; `3.14` lexes as
  Fixed), and enters `PrefixDispatch{cur_bp:0}`.
- The cast result interns as Int (nt=2) — correct target.
- NO `cohort resolve … bp:5 wrap=(7,0)` (the EqInt Int→Bool projection a literal Int
  operand gets) ever appears; all cohort resolves are `bp:0 wrap=(0,X)` (Proc
  injections). The cast operand never re-enters the binding-power-5 infix dispatch.

**CORRECTION (re-trace with enriched instrumentation):** the `apply_pop_body_to_cursor`
`CrossCatLhs{source_src_idx}` re-entry at `:15530-15558` is a RED HERRING for the
post-cast infix — it fires at **pos=3** (the cast's INNER Fixed argument `3.14`) with
`last_out=Some(5)` (Fixed), `pred_cat=Some(7)` (Bool). It is the cast's argument
handling, NOT the `==` continuation. So `cursor.last_action_output_cat` is NOT a
reliable cast-RESULT signal here (it's Fixed=5, not Int=2). Do NOT key the fix on it.

**Actual blocker (pos≈5, after the cast completes):** the earlier trace shows
`suppress category-changing infix source=2 result=7 pos=5` (×7) — i.e. the cast
RESULT is correctly Int (source=2) at the `==`, and an `EqInt` (Int→Bool, result=7)
is attempted via the GUARDED-CONSUME path, which `guard_category_changing_infix`
suppresses (evidence mismatch). But H2 proved the consume path is a DEAD END (even
un-suppressed it does not fire EqInt). The WORKING mechanism a literal Int operand
uses is the **`bp:5` cohort cross-category infix projection** (`cohort resolve
key=pos:.. src:2 bp:5 wrap=(7,0)` → `transient start cat=7 rule=0 arity=2`), which is
NEVER scheduled for the cast-result operand.

**Real fix site (to find next):** the COHORT-PROJECTION SCHEDULER (the producer of
the `bp:5 wrap=(result_cat, rule)` cohort entries; consumers are the "cohort
resolve"/"cohort revive" emits at `wpda_walker.rs:~15780`/`~15104`). Determine where a
literal operand's resolution schedules the `bp:5` Int→Bool projection and why a
cast-result operand's resolution (post-cast, at pos≈4) does not reach that scheduler
(it lands on the guarded-consume path instead). Fix = route the cast-result operand
into the same cohort-projection scheduling for its RESULT category at the operator's
binding power. Keep `guard_category_changing_infix`. Canary: `-3!` tests.

**Candidate fix (to verify, foreground, regression-checked against `-3!`):** the
post-cast infix re-entry must dispatch on the cast RESULT category, not the source —
either by carrying the result category on the edge (a `CrossCatLhs` keyed by/also
carrying the result cat), or by re-entering `category_entry(result_cat)` for the
cast-continuation case while leaving the genuine cross-cat-LHS infix case (which the
`-3!` tests exercise) on the source. Must NOT weaken `guard_category_changing_infix`
(load-bearing, H2). Confirm `cur_bp:0` → the operator's bp (5) projection is then
scheduled.

**Working-tree note:** `prattail/src/wpda_walker.rs` has 29 lines of uncommitted
`[wpds-DRILL]` eprintln trace instrumentation (gated by `trace_actions_enabled()`,
i.e. `PRATTAIL_TRACE=actions`) at `apply_action_to_cursor` (~:6635) and
`apply_pop_body_to_cursor` (~:15511/:15537). It is throwaway diagnostics — REMOVE all
`[wpds-DRILL]` lines before committing the fix. Do NOT `git checkout`/revert it
(survives on disk; remove by hand).

## ⚠ CORRECTION (DRILL2, NOT yet converged — do not treat the chain below as final)

A second instrumentation (`[wpds-DRILL2]` at the `effective_new_state` decision,
`apply_pop_body_to_cursor:~15514`) CONTRADICTS step 2 of the chain below: the
cast-result Int (cat=2) **DOES** reach `InfixLoop { cur_bp: 0 }` at pos=5
(`CE-pop cat=2 edge=None pred_id=GSS_NODE_NONE pred_kind=None eff=InfixLoop pos=5`) —
the SAME state a literal Int reaches. So "the cast result never enters the InfixLoop
dispatch / unwinds at bp:0" is WRONG. The true blocker is INSIDE the InfixLoop
dispatch / `engine.step` at the operator position: with the cast-result cursor in
`InfixLoop{cur_bp:0}` at the `==`, `engine.step` does NOT emit the `EqInt`
`CrossCatDelegate{Int,bp:5}` Fork it emits for a literal Int cursor in the same state.
NOT YET ISOLATED why (candidate axes: the cursor's GSS top / SPPF top differs; the
operator token position vs the cast span; a visited_dispatch/proj-descriptor dedup
that already fired for the cast path; the `1:11 unexpected ==` means the dispatch
returns no action / Unwinding for the cast cursor). NEXT: compare `engine.step`'s
inputs+output for a literal-Int InfixLoop cursor vs the cast-result InfixLoop cursor
at the `==` (same `cur_bp:0`) — what cursor/GSS/SPPF field differs that makes the
generated InfixLoop step emit the EqInt fork for one and not the other. The
`engine.step` InfixLoop logic is codegen (`macros/src/gen/runtime/wpda_codegen/`).
Two `[wpds-DRILL]`/`[wpds-DRILL2]` instrumentation blocks are in the working tree
(~:6635, ~:15514, ~:15511/:15537) — remove before any fix commit.

**FALSIFIED H3 (singleton-ConsumeAndPush, 2026-06-10):** hypothesis was that the
InfixLoop singleton fast-path (`engine_impl.rs:1248`) emits a bare
`ConsumeAndPush{new_state: CrossCatDelegate}` for a category-changing infix that never
registers the `CrossCatProjection` (only the Fork/push-child path does). Implemented
the fix (route singleton `CrossCatDelegate` → `Fork`-of-one) and VERIFIED: the 12 cast
cases STILL FAIL (2 pass / 12 fail, unchanged). So the cast's category-changing-infix
ConsumeAndPush either does NOT come from the `:1248` singleton, or a Fork-of-one still
doesn't register/fire the projection. REVERTED (engine_impl.rs clean). Do not
re-attempt the `:1248` singleton fix without first proving the cast's EqInt emission
site (the `suppress category-changing infix source=2 result=7 pos=5` ConsumeAndPush —
find WHICH emission produces it; candidate sites: the IterativeChainAbsorb fallthrough,
the lex-fork infix dispatch `#lex_fork_infix_dispatch` at engine_impl.rs:956, or a
walker-side ConsumeAndPush, NOT necessarily the :1248 singleton).

## ★ CONVERGENT ROOT (H4, reconciles ALL prior falsifications) — 2026-06-10

The guard `guard_category_changing_infix` (`wpda_walker.rs:6435-6462`) suppresses a
category-changing infix in TWO ways when `lhs_evidence != Some(infix_source)`:
- `ConsumeAndPush` arm (`:6449`): returns `Advance(Unwinding)` (drops it).
- `Fork` arm (`:6456-6462`): `branches.retain(|b| lhs_evidence == Some(source))` —
  REMOVES the category-changing branch (→ empty Fork).
The cast's `EqInt` is suppressed with **`evidence=None`** (needed source = Int(2)):
`suppress category-changing infix source=2 result=7 pos=5 evidence=None`.
`lhs_evidence = cross_cat_lhs_infix_evidence_source(cursor)` is `Some(src)` ONLY when
the cursor's incoming GSS edge is `CrossCatLhs{src}` / `CrossCatLhsReentry{src}`
(`:6405-6423`, edge made at `:7642`). The cast result carries NO such edge for its
RESULT category (the cast pushed `CrossCatLhs{source=5=Fixed}` for its ARGUMENT, and at
the EqInt step the evidence is `None`).

**This RECONCILES the falsifications:** H2 (bypass guard) failed because a bare
`ConsumeAndPush{CrossCatDelegate}` does not register the `CrossCatProjection` (only the
Fork/push-child path `allocate_uncached_push_child:14854` does); H3 (singleton→Fork)
failed because the guard's Fork-filter (`:6456`) removed the EqInt branch for
`evidence=None`. So NEITHER alone suffices.

**FIX (H4, to verify in fresh context):** make a cast result lay down a `CrossCatLhs`
(or `CrossCatLhsReentry`) evidence edge keyed by its **RESULT** category (Int=2) when it
resolves, so (1) `lhs_evidence = Some(Int)` ⇒ the guard ADMITS the `EqInt` infix, and
(2) the cast result then dispatches the infix the same way a genuine cross-cat-LHS
operand does (the working path that DOES register the projection + fires EqInt). This
is precisely the "cast SOURCE classification" the phase name refers to: the evidence is
absent/keyed-by-source, but the post-cast infix needs it keyed by the RESULT category.
VERIFY FIRST: instrument the guard to print `lhs_evidence` for the LITERAL `1 == 1`
EqInt step — confirm it is `Some(2)` (vs the cast's `None`); that is the smoking gun.
Then add the result-category evidence at the cast-resolve site and verify the 12 cast
cases pass with zero `-3!`/op-suite regressions. Do NOT weaken the guard (load-bearing).

**VERIFIED FACT (DRILL3 at allocate_uncached_push_child:14854, 2026-06-10):** for the
cast `int(3.14) == 3`, EVERY registered `CrossCatProjection` is at `bp=0` (the prefix
injections — `source=2 bp=0 wrap=(0,0)` ProcInt, `wrap=(6,1)` IntToFloat, `wrap=(3,..)`
IntToBigInt, etc.; also source=3/5/6/7 injections). **NO `bp>0` projection is EVER
registered** — in particular the `EqInt` projection (`source=2 bp=5 wrap=(7, EqInt
rule)`) is NEVER registered, whereas a literal Int's `1==1` trace DOES register+resolve
`bp:5 wrap=(7,0)`. So the cast's InfixLoop dispatch at `==` emits a (guard-suppressed)
`ConsumeAndPush` for EqInt, NOT the `Fork{CrossCatDelegate}` that would register the
projection. This is the single most reliable finding; the WHY (why the cast's EqInt is
a singleton ConsumeAndPush while the literal's is a Fork — candidate-count / state diff
at the InfixLoop) is the remaining un-isolated question.

**DECISIVE NEXT EXPERIMENT (fresh context):** (a) re-confirm whether H3 actually
rebuilt (touch macros, verify cargo recompiles `mettail-macros` + regenerates) — the
H3 falsification may have been a stale-build artifact; with DRILL3 in place, re-apply
H3 and check if `DRILL3 source=2 bp=5` then appears. (b) site-tag EVERY `ConsumeAndPush`
emission in engine_impl.rs (singleton :1248, IterativeChainAbsorb fallthrough,
`#lex_fork_infix_dispatch` :956, InfixChainIterative arm) to find WHICH emits the cast's
EqInt ConsumeAndPush. (c) instrument the InfixLoop `__cands.len()` to print the
candidate count + each candidate's new_state for the cast's `==` step vs a literal
`1==1` `==` step — the candidate-count difference (singleton vs Fork) is the crux.

**STATUS: root NOT converged after 3 falsified hypotheses (H1 EOI, H2 guard, H3
singleton-ConsumeAndPush) — this is the multi-round false-root CHURN pattern the user
forbids; context saturation is the driver. Per the anti-false-root rule + the
persist-clear authorization, the next attempt MUST start from FRESH context: first
isolate the EXACT emission site of the cast's `suppress category-changing infix
source=2 result=7 pos=5` ConsumeAndPush (instrument every ConsumeAndPush emission with
a site tag), confirm by experiment which site it is, THEN design the fix. No more code
changes on un-isolated roots.**

## (SUPERSEDED — see correction above) earlier chain hypothesis

1. Cast `int(3.14)` reduces to Int (trace `transient start cat=2 rule=15 pos=5`,
   children = [Trigger(int), Symbol(nt=5 Fixed)]). Result category Int(2) is correct.
2. The Int result resolves ONLY into the `bp:0` Proc-injection cohort
   (`cohort resolve key=pos:2 src:2 bp:0 wrap=(0,0)`) and then UNWINDS. It is never
   offered to the Int-category infix dispatch at the operator binding power (bp:5).
3. **Producer of the cross-cat infix projection** = `allocate_uncached_push_child`
   (`prattail/src/wpda_walker.rs:14854`): it pushes
   `EdgeKind::CrossCatProjection{source_src_idx, inner_cur_bp, wrap_cat, wrap_rule}`
   **IFF** `branch.new_state == WpdaState::CrossCatDelegate{source_src_idx, inner_cur_bp}`.
   That registers the cohort the consumer at `:15716`/`:15775` later resolves.
4. A literal Int operand, in its InfixLoop dispatch on `==`, GENERATES a Fork branch
   with `new_state = CrossCatDelegate{source=Int(2), inner_cur_bp=5}` for EqInt
   (wrap=(Bool=7, EqInt rule 0)) → CrossCatProjection registered → `cohort resolve …
   bp:5 wrap=(7,0)` → `transient start cat=7 rule=0 arity=2` (EqInt) → Bool over full
   input. The cast result NEVER generates that CrossCatDelegate fork (it unwound at
   step 2), so the projection is never registered; the only EqInt attempt is the
   guarded-CONSUME path (`suppress category-changing infix source=2 result=7 pos=5`),
   which H2 proved is a dead end.
5. **FIX:** after the cast result reduces to its TARGET category, route the cursor
   into the InfixLoop dispatch for that target category at the operator bp, so it
   emits the same cross-cat infix `CrossCatDelegate{target_cat, op_bp}` Fork the
   literal emits → CrossCatProjection registered → comparison projects. The
   InfixLoop dispatch that emits these cross-cat infix forks is CODEGEN-generated
   (`macros/src/gen/runtime/wpda_codegen/` — the InfixLoop step emitter); the
   post-cast-reduction state transition is `apply_pop_body_to_cursor`
   `effective_new_state` (`:15490-15511`: CategoryEntry pred → InfixLoop; else →
   Unwinding). NEXT READ: (a) the codegen InfixLoop emitter to see how it decides to
   emit cross-cat infix `CrossCatDelegate` forks for an operand's category, and
   (b) why the cast-result cursor lands at `bp:0`-unwind instead of InfixLoop at the
   operator. Keep `guard_category_changing_infix`. Canary: `-3!` tests; also re-run
   gen_calculator_op/gen_rhocalc_op/edge_case baseline-relative (0 new failures).

## Process directives (this session)
- **Boyscout rule** ([[feedback_boyscout_rule]]): fix discovered+localized issues NOW,
  in the same effort; do not defer. "Multi-session OK" is for separate un-started scope.
- **No sub-agents** — complete this fix in the FOREGROUND (user does not trust
  sub-agents' "pragmatic"/debt-hiding shortcuts).
- **Git** — NEVER `git stash` / `git checkout` / `git branch` / `git worktree` /
  `git reset` / `git restore` etc. unless explicitly requested; stay on
  `feature/wfst-architecture`.
- Don't spend time on pre-existence/blame (no history bisection).

## Status
STEP 0 + root-cause COMPLETE (flip-falsified H1/H2; bedrock localized to the
`CrossCatLhs` source-vs-result re-entry at `wpda_walker.rs:~15537` + the missing bp:5
Int projection). Fix is the next foreground step (regression-sensitive; `-3!` canary).
This ledger + the pgmcp task/memory are the complete resumable record — context may be
cleared without loss; resume from here.
