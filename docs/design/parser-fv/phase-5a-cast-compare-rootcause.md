# Phase 5A — cast-then-compare parse failure: root-cause ledger

> Scientific ledger for the cast-comparison family (~78 of the 217 baseline
> failures). Records the CONFIRMED failure, the hypotheses FALSIFIED by experiment
> (so they are not re-attempted), and the localized bedrock + the next drill. Per
> the standing mandate: prove the root by a flip BEFORE naming a fix; document what
> does not work. pgmcp #265; local task #5.

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

**Localized fix site:** `apply_pop_body_to_cursor` (`prattail/src/wpda_walker.rs:~15537`).
When the `CrossCatLhs { source_src_idx }` edge is popped, the re-entry pushes
`StackSymbolV2::category_entry(*source_src_idx)` — i.e. it re-enters the **SOURCE**
category's dispatch (Fixed=5). For the post-cast infix continuation the cursor needs
the cast's **RESULT/TARGET** category (Int=2) so the Int infix projection (`EqInt`,
`GtEqInt`, …) is scheduled. The re-entry keying on the source category (not the
result) is why `==` finds no Int comparison rule.

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
