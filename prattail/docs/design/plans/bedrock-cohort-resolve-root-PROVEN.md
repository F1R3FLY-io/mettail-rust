# Float Cast-Family — BEDROCK Root: dispatch-cohort resolve detachment (flip-proven, 2026-06-03)

Authoritative trace: `/var/tmp/suite-green/bedrock-VERDICT.txt` (312 lines, agent `a1c9f5c4`, worktree `/var/tmp/wt-realize` @ `d2d9a3b`, reverted clean). **This doc SUPERSEDES the prior root docs** — `float-root-PROVEN.md` (rule_idx tiebreak — FALSIFIED), `float-forward-projection-root-PROVEN.md` (realize/CrossCatProjection-gate — mechanism mislocated), and corrects the `inline-forward-projection-fix.md §9` IFP M0 numbering error. Seven approaches were falsified; this is the first root proven by a flip at the ACTUAL mechanism layer.

## The 2 targets
`float(float(10,64),64)` (`test_nested_float_float_int`) and `float(float(float(10,64),64),64)` (`test_triple_nested_float`) ERR "no accepting branch reached end of input" — the Float parse dies at **pos 8** (0 cursors at pos 9/10/11). Controls PASS: `int(int(5,32),32)`, `float(10,64)`, `float(float(10.5))`, Bool win, `int(str(...))`.

## §0 Numbering (DEFINITIVE — corrects the IFP M0 error)
From the GENERATED `target/generated/calculator/wpda.rs` `WPDA_CATEGORIES` (cross-confirmed: `CosFloat = rule_at(5,8)`; `"bigint"` trigger = `state_cat_src_idx==6`):
```
0=Proc 1=BigRat 2=Int 3=UInt32 4=Fixed 5=FLOAT 6=BigInt 7=Bool 8=Str 9=List 10=Bag 11=Map
```
**Float = src_idx 5.** The codegen REORDERS categories (`collect_category_names_with_literals` orders by first rule-LHS appearance, NOT source `types{}` order). The realize root-cause's `cat_src=5 = Float` was CORRECT. The IFP M0 verdict's "Float=6 / Fixed=5" was WRONG (it read the source `types{}` block) — so IFP M0's "no Float suppression anywhere" census actually inspected source=6=BigInt; under correct numbering source=5 (Float) carries `parent_in_visited=true` 13×. (The numbering fix alone does NOT explain the bug — the realize doc had the right category but still mislocated the MECHANISM to the GLL gate / projection-starvation; the real mechanism is the cohort resolve.)

## §1 Trace-diff (Float-FAIL vs INT-PASS) — refutes the "starved a:Proc" framing
Token stream `float(float(10,64),64)` = pos 0..11. Cursor census (max-pos):
- FLOAT dies at **pos 8**; INT reaches **pos 11 (Accepted)**.
- **At pos 8 both are STRUCTURALLY IDENTICAL:** the outer Bin sits with `body_src_idx=0` (the Proc operand slot FILLED) at the outer `,`. **⇒ the realize doc's "outer a:Proc starved" framing is REFUTED — the slot is filled in BOTH.**
- **The exact divergence:** the inner fold's result returns to the outer `a:Proc` slot via a `CrossCatProjection` pop at the operand dispatch position (node_pos=2) for INT (10,490 pops @cur.pos=8) but **NEVER for FLOAT (0 source=5 pops)**. The outer FloatBin therefore never reaches `RuleAt(3)@pos8`; the outer IntBin does (×42).

## §2 The BEDROCK root (code site + condition)
**Site:** the H12 dispatch-cohort register/resolve — `prattail/src/wpda_walker.rs:14165` (`allocate_fork_push_child`) + `:15012` (`cursor_gss_pop_via_edge`), backed by `prattail/src/dispatch_cohort.rs:526` (`register`).

**Root (BEDROCK_REG census):** the `ProcFloat` projection (source=5, wrap_cat=0, wrap_rule=1) is dispatched ONLY at pos 0 and pos 2 — never deeper. Its lone pos=2 cohort worker must resolve by parsing the entire inner `float(10,64)` fold and popping its projection edge. **Under the cohort it NEVER resolves (0 ResolvedHit, 0 pops):** the inner FloatBin completes but pops via its OWN `PrefixRuleEntry` (RuleAt 6 → InfixLoop → Unwinding) at low GSS-depth, **DETACHED** from the pos=2 source=5 worker entry → the entry stays `InFlight` forever → the 289 members paused on it via `InflightCollision` are LOST → no inner result delivered to the outer `a:Proc` slot's *projection* → the outer FloatBin never advances past pos 8 → 0 cursors at EOI.

**Why INT passes (the precise asymmetry):** INT's `Int→Proc` projection (source=2) is dispatched at pos=2 AND AGAIN at pos=4 (the inner IntBin's operand `5`, a bare Int literal), where it RESOLVES instantly (402 ResolvedHit @pos4), bootstrapping the cohort chain. FLOAT has no deeper same-category re-dispatch — the inner `float(10,64)`'s operand `10` is an **Int**, so pos=4 is source=2, not source=5. The `Float→Proc` projection has no trivially-resolving deeper instance. **The "rich vs sparse lattice" (`ast/src/language.rs:1066` Int32→{Int64,Int128,BigInt,BigRat} vs `:1111` Float64→{BigRat}) is the SYMPTOM; the cohort RESOLVE is the MECHANISM.**

## §3 FLIP experiments (triangulated — the proof)
1. **`FLIP_NOUNARY`** (drop the 4 unary branches → Fork collapses to FloatBin): BOTH targets PASS; source=5 pops 1078× (was 0). Breaks standalone unaries (expected). [confirms the genfactor FLIP, re-anchored]
2. **`FLIP_FOLDWINS`** (keep all 5, give FloatBin the winning lex weight): BOTH targets STILL FAIL, byte-identical to baseline. **⇒ FALSIFIES `float-root-PROVEN.md`'s "premature rule_idx tiebreak" root** — making FloatBin win the tiebreak does nothing; the bedrock is the Fork's multi-cursor COHORT interaction, not lex ranking. Also falsifies "FloatBin never parses" — FloatBin DOES complete; DELIVERY fails.
3. **`FLIP_NOCOHORT`** (force every CrossCatDelegate to run as its own worker, bypassing cohort sharing): `=0` FAIL → `=1` **`test_nested_float_float_int` PASS** (correct AST 10.0; source=5 pops 104×); **all 7 controls GREEN**. **⇒ THE BEDROCK FLIP-PROOF** (the cohort detachment is the cause; bypassing the cohort lets the worker resolve standalone). Caveats: triple-nested EXPLODES (14.1M cursors — the cohort is LOAD-BEARING for sharing) and 6 cohort-dependent cross-cat tests regress (expected for a PROOF flip, not a fix).

## §4 Scope note (honest)
Flip-proof COMPLETE for the double-nested (`test_nested_float_float_int`). For the triple-nested, `FLIP_NOCOHORT` confirms cohort-dependence but causes EXPLOSION rather than a clean PASS — so the triple's closure is the same root BY MECHANISM but not by a clean FAIL→PASS flip. The fix must close BOTH without exploding (the cohort must STAY for sharing — bypassing it explodes + regresses 6 tests).

## §5 Why the genfactor trie (Layer 1) advanced but didn't close
The prefix-trie left-factors the inner `float(` group (evidence-driven unary/fold disambiguation + standalone-unary recovery), fixing the SURFACE Layer-1 symptom. But it operates purely on the inner trigger-group dispatch — it does NOT change the dispatch-COHORT pause/resolve for the OUTER `a:Proc` Float→Proc projection. The lone source=5 worker still fails to resolve regardless of inner factoring. **Layer 1 is necessary but not sufficient; the sufficient layer is the cohort resolve.**

## §6 Fix direction (NOT designed — to be Plan-confirmed + RED-TEAMED to convergence)
Make the inner FloatBin's completion RE-ATTACH to / RESOLVE the pos=2 source=5 cohort worker entry (so its 289 paused members deliver the inner result to the outer `a:Proc` projection), WITHOUT bypassing cohort sharing (which explodes the triple + regresses 6 tests). I.e. reconnect the "detached pop" (the inner fold popping via its own `PrefixRuleEntry`/Unwinding path at low GSS-depth) to the cohort entry that is paused waiting for it. Candidate surfaces (to be Plan-confirmed, NONE chosen): the `register`/`resolve` keying (`dispatch_cohort.rs:526`/`:581`) so the inner fold's pop matches the pos=2 worker's DispatchKey; the `cursor_gss_pop_via_edge` resolve trigger (`:15012`) so a `PrefixRuleEntry`/Unwinding pop of a projecting fold ALSO resolves the cohort entry; the worker/GSS-depth attachment so the inner pop isn't detached. **HARD constraints:** preserve the 6 tests `FLIP_NOCOHORT` regressed; do NOT explode the triple (keep cohort sharing); preserve the Bool win + the 5 trie-regressed + 2 registration-regressed cross-cat tests; gauntlet 4220/0. Per the user mandate, the resolution design will be RED-TEAMED by adversarial critics iterating until they CONVERGE before implementation.

**Critical sites:** `prattail/src/dispatch_cohort.rs:526` (`register`) / `:581` (`resolve`); `prattail/src/wpda_walker.rs:14165` (`allocate_fork_push_child` — the cohort dispatch), `:15012` (`cursor_gss_pop_via_edge` — the resolve trigger), the `PrefixRuleEntry`/`InfixLoop`/`Unwinding` inner-fold pop path. UNTOUCHED authorities: `min_terminal_span`, `Ambiguous`, lex-min (`FLIP_FOLDWINS` proved lex ranking is NOT the lever), the prefix-Fork (`binder.rs:1035`).
