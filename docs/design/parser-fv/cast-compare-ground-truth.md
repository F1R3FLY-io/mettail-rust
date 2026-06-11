# Cast-then-compare — GROUND TRUTH (trace-proven fact chain) + the re-grounded fix

> Status: **GROUND TRUTH, 2026-06-10c.** `feature/wfst-architecture @ 94240b31` (Rust = efec0eb7).
> This is the step-1 re-investigation the red-team refutation demanded
> (`evidence-gated-cross-cat-dispatch.md` banner). Trace artifact: `/tmp/trace_gt.txt`
> (`PRATTAIL_TRACE=actions`, probe `languages/examples/trace_host.rs`, inputs `3 == 3` vs
> `int(3) == 3`). Every fact below is a quoted trace line or a grammar/codegen line.

## 1. The fact chain for `int(3) == 3` (calculator; Proc=0, Int=2, Bool=7)

| # | Fact | Evidence |
|---|------|----------|
| F1 | In the **Bool-seeking context** (entered via the root's `ProcBool` **CrossCatProjection lex-alt** — which exists and works), `int` parses as **`VarBool`** (Bool rule 41, child `Terminal(Ident)`): the **keyword interpretation is dropped**. | trace `intern cat=7 rule=41 packing(rule=0x70029, children=[Terminal(Ident)])`; grammar: Bool owns no `int`-leading rule |
| F2 | In the **Int-seeking context** (root's `ProcInt` projection), `int(3)` parses fine as the cast: `Int[0,4]` (rule 18 = `IntId`; all five `int(...)` casts are **cat-Int rules** — FloatToInt/BoolToInt/StrToInt/IntId/IntBin, `calculator.rs:233-242,377`). | trace `intern cat=2 rule=18 ... span=[0,4]` |
| F3 | The efec0eb7 post-resolution synthesis fires on the Int-context cursor (`cast-host synth reentry source=2 pos=4`), EqInt (Bool rule 0) fires with `[Int[0,4], Int[5,6]]`, and **`Bool[0,6]` IS interned** (×4). | trace `transient start cat=7 rule=0 ... children=[Int[0,4], Int[5,6]]` → `intern cat=7 rule=0 ... span=[0,6]` |
| F4 | **No `Proc[0,6]` root is ever interned** (0 occurrences). | `grep -c "intern success cat=0 .*span=\[0,6\]"` = 0 |
| F5 | `Bool[0,6]` is offered ONLY to **Int-consuming frames** and rejected by each: `cat=0 rule=0` (Proc←Int), `cat=1 rule=1` (UInt32←Int), `cat=6 rule=1` (Float←Int) — all `reason=expected-cat ... expected=2`. The cast cursor's continuation injects **c=Int, never d=Bool** — the worker-identity theorem (`CastRehostOutputProjection`) observed live. | trace `transient reject ... expected=2 node=Symbol(nt=7, span=[0,6])` |
| F6 | The reported errors (`1:1 found Fixed("int")` / `1:4 unexpected Fixed("(")`) are **salvage-position reports** from the premature-filter/longest-prefix path (the surviving short parse is `Proc[0,1]` from F1's VarBool). **The red-team agent-2 reading "fails before the operand parses" is REFUTED** — F2/F3 prove the operand parses and EqInt fires. | trace END line + `cohort resolve key=pos:0 src:7 wrap=(0,2)` on `Bool[0,1]` → `Proc[0,1]` |

## 2. The mechanism (codegen lines)

The root context **already** fans `int` to the ProcBool projection: `lex_alt_rules_for_prefix`
supports `LexAltRuleKind::CrossCatProjection{source}` (`kind_dispatch.rs:471-501` emits one entry
per FIRST-token of each projection's source; `Fixed("int") ∈ FIRST(Bool)` via the Phase-F.6
Param-first recursion through EqInt's Int LHS — the same mechanism that lets literal `3` open a
Bool). The failure is exactly **one level down**, in the Bool-seeking context:

1. `int` is keyword/ident lex-ambiguous → the lex-fork takes over (`forks.rs:174`).
2. The lex-alt table has **no `LexAltRuleKind::CrossCatLhs` variant** (`wpda_runtime.rs`: Atomic,
   PrefixOp, CrossCatProjection, PostfixOp, InfixOp, MixfixFirstTrigger) — the Pass-0
   cross-cat-LHS arm (`prefix.rs::emit_unified_arm:1301-1323`, which DOES exist for
   `(Bool, Fixed("int")) → CrossCatLhs{Int}`) is **unrepresentable** in the fork.
3. The 51d57c91 fall-through rescue does not fire: `prefix_primary_has_dispatch_rule(Bool, "int")`
   is **false** — it covers only the state cat's OWN leading-literal rules
   (`kind_dispatch.rs:172-199`), and Bool owns none for `int`.
4. ⇒ the fork emits only the `Ident→VarBool` branch (F1). The keyword interpretation — the one
   that would make this cursor a genuine **Bool-context (d-)worker** parsing `int(3)` as the
   EqInt Int-LHS via the CrossCatLhs delegate — is dropped.

**This is the same gap class 51d57c91 fixed** (the lex-fork dropping an interpretation its table
cannot represent: then collection/multi-token-prefix rules, now the cross-cat-LHS delegate), one
context over. The literal `3 == 3` works because `Integer` is NOT lex-ambiguous — the normal
dispatch (which owns the Pass-0 CrossCatLhs arm) handles it directly.

## 3. Why this kills the whole cluster (incl. the cases the post-resolution +2 couldn't reach)

A Bool-context worker parsing the cast LHS via `CrossCatLhs{Int}` is a **dispatch-time d-worker**:
EqInt fires with evidence (the delegate edge), `Bool[0,6]` returns to the Bool context, the
ProcBool projection wraps it → `Proc[0,6]` root → accept. The output injection is **native** —
no synthesis, no salvage. And because the fix is dispatch-time (not post-resolution-shape-gated):
- the **no-arg** casts (`cast_error_fixed != 0.0`, the 6 `gen_calculator_op` `*casterrfixed*`
  failures that `min_terminal_span>0` could not touch) are covered the same way —
  `prefix_primary_has_dispatch_rule(Fixed, "cast_error_fixed")` is true (TerminalKeyword), and
  Bool's Pass-0 has `CrossCatLhs{Fixed}` (NeFixed/EqFixed sources);
- `comparison_after_cast_results::*` (12), `operator_chains_after_casts` (2),
  `string_edge_cases` (2, via `CrossCatLhs{Str}`/EqStr) all take the same path.

## 4. The two fix shapes (the algorithm fork; both proven in `CastLexForkCrossCatLhsGap.v`)

Both are localized to the lex-fork at PrefixDispatch and ride EXISTING machinery (the Pass-0
unified arm / `ForkActionKind::PushCrossCatLhs`); neither touches `DispatchKey`/`EquivKey`/cohort
keys (the red-team's M4 objection is moot for both).

- **(d1) Fall-through extension (the 51d57c91 pattern, minimal):** extend the fall-through
  predicate to `(prefix_primary_has_dispatch_rule(s, pk) ∨ crosscat_lhs_has_dispatch_rule(s, pk))
  ∧ all_alts_same_length`, where the new predicate is true iff the state cat has a Pass-0
  CrossCatLhs bucket containing the token (∃ source I ∈ cross_cat_infix_sources(s) with
  pk ∈ FIRST(I)). The fork is skipped; the normal dispatch's unified arm (singleton
  `CrossCatLhs{Int}` for `(Bool, "int")`) fires. The `Ident→Var` interpretation is dropped at the
  same-length tie — **keyword reservation**, the exact documented 51d57c91 policy ("a
  grammar-declared keyword beats the auto-injected `Var` fallback — evidence-based").
- **(d2) New lex-alt variant (maximally ambiguity-preserving):** add
  `LexAltRuleKind::CrossCatLhs{source_src_idx}` + table pushes (mirroring
  `emit_cross_cat_projection_prefix_pushes`, one per source-FIRST token) + a fork-branch arm
  constructing the same push as the unified Fork's `PushCrossCatLhs` branch
  (`prefix.rs:1362-1380`). The fork then carries BOTH `Ident→VarBool` AND the delegate; the Var
  branch dies by evidence (premature filter at EOI), per `feedback_preserve_disambiguation`.

**Boundedness (derived, both shapes):** new delegate dispatches occur ONLY in
cross-cat-source contexts (Bool/…); a nested cast's inner levels are the casts' **param-cat
contexts**, where the keyword has a same-cat primary (the EXISTING 51d57c91 disjunct → cast arm,
no new branch). So the added fan-out is a constant per comparison-LHS position — **depth-
independent** — in contrast to the falsified earlier experiment, which routed keywords into
delegates at EVERY level (per-level fan-out compounds: 2^depth, the 327-cursor blowup). The model
derives both growth shapes from one counting function over the context classification.

**Non-interference with the 189 fixes (both shapes):** the extension only ADDS behavior where
`prefix_primary_has_dispatch_rule` is false; every 189-fix token fires in its owner context
(predicate true), taking the unchanged first disjunct. The `-3!` multi-length guard
(`all_alts_same_length`) is untouched — multi-length ambiguities keep forking.

## 5. Verification gates for the implementation
`cast_probe` (direct/nested casts + controls) · op-suites diffed vs
`baseline-cf03e571-failures.txt` (217) · `-3!` canary · prattail-lib gauntlet ·
`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-prattail-wpda` (zero-admission).
