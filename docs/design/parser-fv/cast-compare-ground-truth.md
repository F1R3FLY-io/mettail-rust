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

## 6. IMPLEMENTED (2026-06-10d): d1 + the snapshot-dedup completion

**d1 shipped** (the fall-through extension; chosen as the recommended shape — it generalizes the
proven 51d57c91 mechanism, zero extra fork branches, and applies the same documented same-length
keyword-reservation policy):
- `kind_dispatch.rs`: new generated predicate `prefix_crosscat_lhs_has_dispatch_rule(cat, kind)`
  emitted by `emit_prefix_crosscat_lhs_dispatch_arms` — true iff ∃ source `I` ∈
  cross_cat_infix_sources(cat) with `kind` ∈ FIRST(I); the source-set computation mirrors
  `prefix.rs:892-903` verbatim (no drift) and token coverage reuses `first_set_of_category`.
- `forks.rs`: the fall-through disjunct becomes
  `(__primary_has_dispatch || __primary_has_crosscat_lhs) && __all_alts_same_length`.

**The one consequence + its principled completion:** the d1 delegate cursors re-resolve the SAME
cohort keys as the owner-category parse, and the shipped snapshot-dedup compared the two
consumer-DEAD weight fields (`worker_weight`, `worker_pre_dispatch_weight` — revive reads only
`{inner_state, last_action_output_cat, pending_packing_weight}`; the pre-dispatch weight is
`let _`-discarded per the falsified Stage-1.5.3 delta scheme). Weight-only-distinct snapshots
occupied cap slots while reviving BYTE-IDENTICALLY — the d1 delegates tipped saturated keys to
17 > `MAX_WORKER_SNAPSHOTS_PER_KEY = 16` (spurious AmbiguityBudget failures on nested/chained
casts). Fix: narrow `worker_snapshot_observationally_eq` to the consumed fields — exact
observational-equivalence dedup (never weight-pruning), `-3!`'s per-packing distinction stays in
the key via `pending_packing_weight`. FV: `CohortSnapshotObservationalDedup.v` (zero-admission)
— `dedup_revival_no_loss`, `dedup_preserves_revived_set`,
`narrow_key_fits_where_full_key_overflows`, `dedup_never_longer`.

Note vs the red-team banner in `evidence-gated-cross-cat-dispatch.md`: d1 needed **no lookahead
gate** (the gate WAS circular — refutation upheld; completeness instead comes from the additive
viability of the delegate + evidence rejection at EOI) and **no cohort-key change** (the M4
`DispatchKey` and the `EquivKey` merge are untouched; the dedup narrowing is at the SNAPSHOT
level, orthogonal to both).

### Verification results (2026-06-10d, d1 + snapshot-dedup)

| Gate | Before (efec0eb7) | After | Verdict |
|---|---|---|---|
| `cast_probe` (13 cases incl. nested + `-3!` + controls) | 4 direct-cast FAIL | **13/13 OK** | ✓ flip |
| `gen_calculator_op` | 1324/6 (`*casterrfixed*` ×6) | **1330/0** | ✓ 6 fixed |
| `edge_case_tests` | 210/19 | **227/2** (`ambient` ×2 pre-existing) | ✓ 17 fixed |
| `gen_rholang_op` | 530/1 (`castbigrat`) | **530/1** (same case) | ✓ neutral |
| prattail lib | 3979/0 | **3979/0** (2 overflow tests updated to consumed-distinct constructors) | ✓ |
| `cargo test --lib egraph::` | 51/0 | **51/0** | ✓ mandate |
| `rocq-prattail-wpda` | green | **green** (9 cast models, all zero-admission) | ✓ |

**Net: 23 failures fixed, 0 new failures** (remaining 3 — `ambient_edge_cases::{nested_new,
parallel_ambients}` + `cross_cat_rholang_castop_putmap_castbigrat_smoke` — are all in the original
cf03e571 baseline and are different families). The fixed set includes every
`comparison_after_cast_results` case (12), `operator_chains_after_casts` (2),
`chained_casts_with_operators` regressors (4 — transient, introduced+fixed within this change),
`nested_keyword_prefix_functions` (5 — transient), `string_edge_cases` (3), the no-arg
`casterrfixed` family (6), and `rholang_edge_cases::int_of_float_add`.

**Perf — the falsified premise + the trigger-presence gate (the third component):** the model's
original `fix_levels` premise ("inner cast levels are owner-context") was FALSIFIED empirically:
the cast arm forks over its BODY categories, and the Bool-body branch is a SourceCtx at EVERY
nesting level; each delegate RE-PARSES its suffix, so an n-deep trigger-free cast tower cost
2^n WORK at constant cursor count (nextest: `float_int_float_roundtrip` 18.4 s,
`int_float_int_roundtrip` 30.2 s, `deep_chain_str_float_int_bool` TIMED OUT >120 s; sequential
suite wall 978 s). Fix: gate the fall-through on **trigger-presence in the remaining input** —
an infix can fire only by CONSUMING its trigger from the remaining input, so absence is definite,
monotone refutation of every future firing (the non-circular realization of the lookahead-gate
idea — whole-suffix token presence, not next-token prediction, decidable at dispatch). FV:
`CastLexForkCrossCatLhsGap.TriggerPresenceGate` (`gate_no_loss`,
`gate_zero_overhead_when_absent`, `gate_kills_tower_blowup` — 2^n vs owner-only work, derived;
plus the scientific-ledger record of the falsified premise). Generated:
`prefix_crosscat_lhs_trigger_ahead(cat, tokens, pos)` (per-result-cat trigger sets from the same
rule walk as the source sets), ANDed into the fall-through disjunct. Result: edge_case
**227 passed in 7.25 s** (was 978 s — ~135×), `nested_keyword_prefix_functions` 23/23 in 6.37 s,
zero correctness change (cast_probe 13/13; every previously-fixed case stays fixed — trigger
present ⇒ delegate kept). Cast-free workloads (chains `1+2+…`) never enter any of the new paths
(Integer tokens are not lex-ambiguous; the snapshot-dedup narrowing only shrinks per-key slots,
`dedup_never_longer`).
