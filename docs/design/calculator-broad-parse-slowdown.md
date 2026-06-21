# Calculator Broad Complex-Term Parse Slowdown — Infix Cross-Category Lex-Fork Fan-Out

**Target:** branch `feature/wfst-architecture`, HEAD `b78e5e1e`.
**Status:** IMPLEMENTED + verified (2026-06-21; uncommitted on `feature/wfst-architecture`). Root cause
confirmed by throwaway probe (this document, §3); the divergence-axis pinpoint is established for the broad
bigint / bigrat / sim surfaces (§3.3–§3.5); the implemented direction is **seal-local `lex_fork_path`
truncation at the infix-loop operand boundary** (the infix twin of the committed rhocalc collection-splice
fix `cc91d291`), with a rigorous soundness argument (§4); the rejected alternatives are recorded (§5); a
verification plan with timing targets is given (§6); and the implemented form, the **clear-all-vs-watermark
decision** (clear-all chosen — empirically term-identical, §9), the ON/OFF differential, and the
**simulation-bound `sim` residual** are recorded in §9. All probes are reverted (§7); the working tree shows
only `prattail/src/wpda_walker.rs` + this document.

**Scope (implemented fix):** WPDA walker, the cross-category infix dispatch path
(`prattail/src/wpda_walker.rs`). **Stack-free clear-all** of the cursor's `lex_fork_path` at the canonical
infix-operand seal (the final `InfixLoop` state write in `apply_pop_body_to_cursor`), behind the
`PRATTAIL_INFIX_LEXCLEAR` kill switch (default `Clear`; `0`/`off` reverts; `watermark` selects the per-operand
watermark A/B variant). **No grammar / regex / spec change. No change to `merge_disambiguator` /
`register_arc_with_aggregation`. No revert of any committed fix. The multi-result (`_all` / `_prefix`) path
and the live-fork invariants are preserved** (verified byte-identical ON vs OFF across 2332 languages tests +
3795 prattail tests, §9). The `macros/.../forks.rs` emitter is **unchanged** — the fix lives entirely at the
walker seal site, plus a comparison-only watermark capture for the `watermark` A/B variant.

**Companion documents.** This is the **third** in a family of cursor-frontier fan-out investigations against
the `30acf6de` "preserve ambiguity and runtime evidence" series, each reaching its conclusion by the same
method (probe → axis pinpoint → soundness):

| Document | Surface | Dominant redundant axis | Verdict |
|---|---|---|---|
| `docs/design/rhocalc-collection-fork-explosion.md` | rhocalc `{0\|1\|…\|N}` collection literals | `lex_fork_path` + `sppf_collection_arena` `Arc` | **false divergence** — collection-local `lex_fork_path` clear at splice (Change B) + global arena content-eq (Change A). **Committed** `cc91d291`. |
| `docs/design/calculator-map-crosscat-fanout.md` | calculator `put/get/merge` nested function calls | `LexicographicWeight` provenance triple | **genuine multi-result evidence** — single-result demand-mode weight-dominance subsumption. **Committed** `c45bdea2`. |
| **this document** | calculator **infix** arithmetic `a + b - c bitand …` (bigint / bigrat / bare-int / `sim`) | **`lex_fork_path` (the `LexForkStamp` sidecar)** | **false divergence**, but the merge gate may NOT be globally relaxed (live-fork invariant) ⇒ **seal-local truncation at the infix operand boundary** (the infix twin of rhocalc Change B). |

> **Why a third document.** The committed map fix (`c45bdea2`) collapses cursors that differ **only in the
> weight triple**. The probe (§3.3) shows the broad infix surface is kept apart by a **different** axis —
> `lex_fork_path.last()`, the `LexForkStamp` — in **80–84 %** of no-merges. That axis is a **kept** component of
> *both* the strict merge key *and* the `SubsumeConfigKey`, so neither the strict Tomita merge nor the committed
> subsumption collapses these cursors. This is precisely the residual the map document explicitly left out of
> scope, and the reason map is still `4.4×` over baseline while bigrat is *neutral* to the subsumption
> (`ON ≈ OFF`).

---

## 1. Problem

The calculator heavy display-roundtrip property tests are **4–180× slower at HEAD than baseline `b781d754`**,
and under full-workspace 16-core concurrency whichever heavy proptest is scheduled last exceeds the 180 s
per-test cap (the single remaining workspace *timeout*; **0 tests FAIL**). The affected tests:

| test | entry | baseline `b781d754` | HEAD |
|---|---|---|---|
| `map_display_parse_roundtrip` | `Map::parse` | 25.5 s | 111 s (after the committed map fix; was > 180 s) |
| `sim_calculator_proptest_campaign` | `arb_bool(3)` → `Bool::parse` | 8.4 s | > 120 s |
| `bigint_display_parse_roundtrip` | `BigInt::parse` | < 1 s (old lenient) | > 180 s |
| `bigrat_display_parse_roundtrip` | `BigRat::parse` | < 1 s (old lenient) | 40 s |

They pass in isolation; only the concurrent tail-scheduled one times out. The committed map fix
(`c45bdea2`) collapses one fan-out axis (the weight triple), but `map` remains `4.4×` over baseline and `bigrat`
is **neutral** to the subsumption — so **bigint / bigrat / sim (and map's residual) have a DIFFERENT redundant
fan-out axis** the committed fixes do not collapse. This document root-causes and designs the fix for that axis.

### 1.1 Symbol glossary (defined before use)

| Symbol / term | Meaning |
|---|---|
| WPDA | Weighted Push-Down Automaton — the parser runtime (`prattail/src/wpda_walker.rs`) |
| GLR / GLL | Generalised LR / LL parsing (Tomita 1985; Scott & Johnstone 2010) — the multi-cursor model |
| SPPF | Shared Packed Parse Forest — the parse-forest DAG (`prattail/src/sppf.rs`) |
| Symbol node | an SPPF identity node keyed by `(non-terminal, lo_pos, hi_pos)` |
| Packing node | one *derivation* of a Symbol, keyed by `(rule_idx, children)`; weights `⊕`-aggregated |
| cursor / arc | one live parse configuration in the frontier (`BranchCursor`; `FrontierArc` when ingested) |
| frontier | the live set of cursors at one walker step (`self.branch_cursors`) |
| TomitaKey | the coarse frontier bucket `(state, node, pos, edge_top, edge_stack, collection_depth)` — `tomita_frontier.rs:70` |
| `merge_disambiguator` | the arc-level *anti-merge* tuple inside a TomitaKey bucket — `tomita_frontier.rs:326` |
| `ConfigKey` | the strict per-step cursor-merge key in `merge_equivalent_cursors` — `wpda_walker.rs:3420` |
| `SubsumeConfigKey` | the committed single-result subsumption key = strict `ConfigKey` − weight-triple — `wpda_walker.rs:3289` |
| **`LexForkStamp`** | **`(pos, alt_idx, src_idx, rule_idx)`** — one lexical-disambiguation traversal stamp — `wpda_walker.rs:2924` |
| **`lex_fork_path`** | **per-cursor `Arc<Vec<LexForkStamp>>` sidecar; one stamp appended per lex-fork arm taken; never popped** — `wpda_walker.rs:2861` |
| `LexicographicWeight` | the path weight `(primary: TropicalWeight, lex_alt_idx, src_idx, rule_idx)` — `rigail/src/lex_weight.rs` |
| weight triple | the three integer tiebreaks `(lex_alt_idx, src_idx, rule_idx)` of a `LexicographicWeight` |
| `visited_proj_descriptors` | per-cursor `im::OrdSet<ProjDescriptorKey>` cross-cat projection cycle-defense set — `wpda_walker.rs:2624` |
| `ProjDescriptorKey` | `(gss_node, sppf_stack, pos, cat_src, cur_bp)` GLL cross-cat dispatch descriptor — `wpda_walker.rs:4382` |
| cross-cat | a rule whose argument/result category differs from the category being parsed (a cast or a foreign-arg op) |
| single-result demand | the `Cat::parse` facade path: stop at the first accepting root, realize `min_by(weight)` |
| `d` | the cross-cat **infix arm degree** — the number of categories that share an operator token (per grammar) |

### 1.2 What the generators actually emit (the hot surface)

The bigint / bigrat / sim generators (`languages/tests/gen_calculator_prop.rs`) build deeply-nested
**infix arithmetic** terms, not nested function calls:

- `build_bigint_from_tape` (`:548`) emits `AddBigInt(a "+" b)`, `SubBigInt(a "-" b)`, `BitAndBigInt(a "bitand" b)`,
  `BitOrBigInt(a "bitor" b)`, unary `NegBigInt`/`BitNotBigInt`, plus the cross-cat cast cascade
  `IntToBigInt`, `UInt32ToBigInt`, `BoolToBigInt`, `BigintCast` (Proc → BigInt).
- `build_bigrat_from_tape` (`:621`) emits `AddBigRat`/`MulBigRat`/`DivBigRat`/`BitAndBigRat`/`BitOrBigRat`/`Fraction`
  plus an even larger cast lattice: `IntToBigRat`, `BigIntToBigRat`, `UInt32ToBigRat`, `FloatToBigRat`,
  `FixedToBigRat`, `BoolToBigRat`, `BigratCast`.
- `sim_calculator_proptest_campaign` (`:2892`) uses `arb_bool(3)` — the most general entry, whose terms reduce
  through the whole `Proc` cohort and the infix comparison operators.

The displayed surface is therefore an **infix operator spine** with a shared operator alphabet. The crux is
that the operator tokens are **shared across categories** (`languages/src/calculator.rs`):

```
"+"      AddInt | AddUInt32 | AddBigInt | AddBigRat | AddFloat | AddFixed | AddStr   (7 rules)
"-"      SubInt | SubBigInt | SubFloat | SubFixed   + unary Neg|NegBigInt|NegBigRat|NegFloat|NegFixed
"*"      MulInt | MulBigRat | MulFloat | MulFixed
"/"      DivInt | DivBigRat | DivFloat | DivFixed
"bitand" BitAndInt | BitAndUInt32 | BitAndBigInt | BitAndBigRat | BitAndFixed
"bitor"  BitOrInt | BitOrUInt32 | BitOrBigInt | BitOrBigRat | BitOrFixed
```

### 1.3 The cross-category infix ambiguity (the multiplier)

When the walker is in `InfixLoop` after an operand and sees a shared operator token, it must consider **every
category's rule** for that operator. The compile-time grammar lint dumps the competition, e.g. for `BigInt`:

```
BigInt: KwBitnot→BitNotBigInt (vs IntToBigInt wt 0.67, UInt32ToBigInt wt 0.67, VarBigInt wt 11.00);
        KwInt→IntToBigInt (vs VarBigInt wt 11.00); KwBigint→BigintCast (vs VarBigInt wt 11.00); …
```

and for `BigRat` the lattice is larger still (`IntToBigRat` vs `BigIntToBigRat` vs `UInt32ToBigRat` vs
`FixedToBigRat` vs `VarBigRat`). At each operator in the chain the infix loop **forks a cohort of cross-cat
delegate arms**, one per category that owns the operator (`InfixOp { result_src_idx } != primary_src ⇒
CrossCatDelegate`). Each nesting level multiplies that cohort against the enclosing one. This is a *non-lexical*
cross-product — it reproduces even when every leaf is a single-token literal (the bare-int control, §3).

---

## 2. Confirmed root cause (one sentence)

> The infix-loop lex-fork emitter (`emit_lex_fork_at_infix_loop`, `forks.rs:563`) forks one
> `ForkBranch` **per category that shares the operator token**, and each arm appends a **distinct
> `LexForkStamp`** `(pos, alt_idx, src_idx, rule_idx)` to the cursor's `lex_fork_path` sidecar
> (`wpda_walker.rs:22192`); because `lex_fork_path.last()` is a **kept** axis of *both* the strict merge
> `ConfigKey` *and* the committed `SubsumeConfigKey`, the per-operator cross-cat cohort **never re-converges**,
> and the per-level fan multiplies across the infix spine into an `O(dᴺ)` cursor frontier.

The frontier blow-up is the cause of the wall-time regression: per-step cost is `O(frontier)` (merge + hash),
so the `~65×` larger concurrent frontier (probe §3.2) inflates wall time super-linearly in nesting depth.

The `30acf6de` provenance is the same as the two companion cases: the series switched the cross-cat-delegate
cohort fan-out to `parent_frame_with_pushed_fork_branch` (GSS push per fork arm → distinct return lineages
that carry the lex-fork stamp forward), and the lex-fork stamp keeps each arm separated. The baseline
`b781d754` carries the **same** `LexForkStamp` machinery (verified — its `merge_disambiguator` includes
`lex_fork_path.last()`); the difference is the fan-out re-convergence, which the baseline got *for free* from
the metadata-frame and HEAD lost.

---

## 3. Probe evidence

A throwaway probe (since reverted; §7) parsed left-nested infix chains over a fixed operator alphabet at
nesting `n ∈ {1..8}` via the single-result demand facade (`BigInt::parse` / `BigRat::parse` — the failing
tests' entry points), with three controls:

- **bigint** `1n + 2n - 3n bitand 4n …` (suffixed BigInt literals),
- **bigrat** `1r + 2r * 3r / 4r …` (suffixed BigRat literals),
- **bare** `1 + 2 - 3 bitand 4 …` (no suffix — maximises the `IntToBigInt`/`IntToBigRat` injection lattice).

Frontier counters came from the built-in `walker-stats` (`PRATTAIL_WALKER_STATS=1`, feature `walker-stats`).
The per-axis no-merge breakdown came from a temporary classifier in `register_arc_with_aggregation`. Baseline
numbers are from the read-only worktree `mettail-rust-lexdeleg @ b781d754` (the same probe copied in, then
removed). All runs: debug build, `taskset -c 0`.

### 3.1 The super-linear curve (timing) — vs the LINEAR baseline

| n | input len | **baseline** bigint | **HEAD** bigint | HEAD/base | **baseline** bigrat | **HEAD** bigrat |
|--:|--:|--:|--:|--:|--:|--:|
| 1 | 7 | 2.8 ms | 5.2 ms | 1.9× | 4.5 ms | 7.9 ms |
| 2 | 12 | 3.0 ms | 17.8 ms | 5.9× | 5.6 ms | 19.4 ms |
| 3 | 22 | 4.3 ms | 29.4 ms | 6.8× | 7.9 ms | 64.3 ms |
| 4 | 31 | 5.6 ms | 105.9 ms | 18.9× | 10.3 ms | 198.3 ms |
| 5 | 36 | 6.8 ms | 180.6 ms | 26.6× | 12.6 ms | 470.2 ms |
| 6 | 41 | 8.1 ms | 553.5 ms | 68.3× | 15.0 ms | 612.7 ms |
| 7 | 51 | 9.5 ms | 513.7 ms | 54.1× | 17.8 ms | 1 323.9 ms |
| 8 | 60 | 11.0 ms | 2 548.3 ms | **231.7×** | 20.6 ms | 2 468.1 ms (**120×**) |

> **The baseline is essentially LINEAR in input length** (bigint 2.8 → 11.0 ms ≈ 4×; bigrat 4.5 → 20.6 ms),
> while HEAD is **super-linear** (bigint 231×, bigrat 120× at n=8). This is the broad slowdown: the same
> single-result parse the baseline produces in `O(N)` takes `O(dᴺ)` at HEAD. The regression is therefore
> **redundant fan-out**, not real ambiguity (the grammar is unchanged; the baseline parsed the identical
> strings linearly).

A **nested-cast** control `bigint(bigint(…(1+2)…))` was ALSO measured and is **roughly linear** at HEAD
(3.9 → 155 ms over 5 levels) — i.e. the cast *nesting* is not the problem; the **infix spine** is. This rules
out the cast cohort (the map-document axis) as the broad driver.

### 3.2 Frontier size (walker-stats, bigint n=5, the heavy phase)

| Metric | **baseline** `b781d754` | **HEAD** `b78e5e1e` | ratio |
|---|---:|---:|---:|
| `branch_cursors_peak_pre_merge` | **20** | **1 296** | **64.8×** |
| `branch_cursors_peak_post_merge` | 20 | 1 160 | 58.0× |
| `apply_action_calls` | (linear) | 12 892 | — |
| `avg_merge_factor` | (≈1) | 7.27× | — |
| `cursors_dropped: merge` | (few) | 1 343 | — |
| `cursors_dropped: sr_subsume` (the committed map fix) | 0 (field absent) | **198** | — |

> **Smoking gun #1.** The committed single-result subsumption (`sr_subsume`) **does fire** (198 drops) — it is
> *not* inert here — yet the peak frontier is still `1 296` (`65×` baseline's `20`). The subsumption collapses
> only the weight-triple-separated minority; the dominant redundancy survives it. This is why `bigrat` is
> **neutral** to the subsumption (`ON ≈ OFF`): its redundant cursors differ in an axis the subsumption *keeps*.

### 3.3 Per-axis no-merge breakdown (the pinpoint) — `lex_fork`, NOT the weight triple

The classifier recorded, on every arc that landed on an existing TomitaKey bucket but **failed to merge with
any existing arc**, which axis differed from the closest existing arc. Consistent across all three controls
(percentages are of all no-merges; an arc can differ on several axes, so columns sum > 100 %):

| Axis (kept by merge gate?) | bigint n=5 | bigrat n=5 | bare n=5 | interpretation |
|---|---:|---:|---:|---|
| **`lex_fork` (`lex_fork_path.last()`)** | **83.0 %** | **80.8 %** | **83.7 %** | **dominant blocker — the `LexForkStamp` sidecar** |
| `weight_triple` | 26.3 % | 25.4 % | 22.2 % | the map-document axis — secondary here |
| `visited_proj_descriptors` | 24.6 % | 32.4 % | 19.5 % | cross-cat projection cycle-defense (genuine; §3.5) |
| `sppf_stack` | 7.7 % | 12.1 % | 8.4 % | GLL `w` progress (genuine) |
| `cohort_origin` | 0.8 % | 1.3 % | 1.5 % | dispatch-key provenance (genuine) |
| `incoming_edge_stack` | **0.0 %** | **0.0 %** | **0.0 %** | **never the divergence** — arena hash-conses it |
| `visited_dispatch` / `visited_recovery` / arena / scope-marks | 0.0 % | 0.0 % | 0.0 % | not the driver |
| `last_action_output_cat` | 0.8 % | 0.6 % | 0.5 % | not the driver |

> **Smoking gun #2 (the axis pinpoint).** The broad infix surface is kept apart by **`lex_fork` in 80–84 %** of
> no-merges — the **opposite** of the map case, where the **weight triple** was the 95.6 % blocker and `lex_fork`
> was **0 %** (the map terms are single-token, so no lexical fork ever fired). The map fix's `SubsumeConfigKey`
> *keeps* `lex_fork_stamp` (`wpda_walker.rs:3353`), so it cannot collapse these cursors — exactly the residual
> the map document deferred.

### 3.4 The decisive decomposition (why the committed subsumption can't help, and what CAN)

The classifier further decomposed each no-merge by *what blocks it*:

| Decomposition (of all no-merges) | bigint n=5 | bigrat n=5 | bare n=5 |
|---|---:|---:|---:|
| `same_subsume_key` (collapsible by the committed map fix) | 1.6 % | 2.8 % | 1.9 % |
| `diff_subsume_key` (blocked by a **kept** axis) | **98.4 %** | **97.2 %** | **98.1 %** |
| ├ **`lexfork_SOLE_blocker`** (some sibling differs **only** in `lex_fork`; every other kept axis *and* the weight triple equal) | **55.2 %** | **46.6 %** | **60.1 %** |
| ├ `lexfork_AND_weight_only` (differs in `lex_fork` + weight triple, nothing else genuine) | 14.8 % | 12.8 % | 14.6 % |
| └ `genuine_config_distinct` (differs in `sppf_stack` / `visited_proj` / `cohort` — a real GLR/GLL axis) | 30.0 % | 40.7 % | 25.3 % |

> **Conclusion of the pinpoint.** **~60–75 %** of all redundant arcs are blocked **by `lex_fork`** (sole +
> with-weight), and **>98 %** are blocked by *some* kept axis (so the committed subsumption, gated on the
> weight triple only, captures `< 3 %`). Of the `lex_fork`-blocked arcs, **47–60 % are *sole* `lex_fork`
> blocks**: a sibling arc exists that is **identical on every other observable axis including the weight
> triple**, differing *only* in the `LexForkStamp`. These are the false-divergence candidates. The residual
> `25–41 %` `genuine_config_distinct` is a **secondary** axis (`visited_proj_descriptors`), addressed in §3.5
> and §4.6.

### 3.5 The lever, confirmed by a controlled drop — and the soundness boundary it reveals

A second throwaway probe gated `lex_fork_path.last()` out of `merge_disambiguator`, the strict `ConfigKey`,
**and** `SubsumeConfigKey` behind an env flag (`PROBE_DROP_LEXFORK`). This is a *coarse over-approximation*
(a **global** clear, not the seal-local fix) used only to confirm the lever and map the blast radius:

| Measurement (bigint) | HEAD (lex_fork kept) | HEAD + `PROBE_DROP_LEXFORK` | baseline |
|---|---:|---:|---:|
| wall n=8 | 4 840 ms | **640 ms** (7.6× faster) | 11 ms |
| wall n=5 | 318 ms | 86 ms (3.7×) | 6.8 ms |
| `branch_cursors_peak` n=5 | 1 296 | **304** (4.3× smaller) | 20 |
| no-merges n=5 | 10 331 | **1 293** (8× fewer) | — |

After the drop, the **single-result parse result is BYTE-IDENTICAL** (a battery of heavy bigint/bigrat terms
+ `-3!` produced the *same* `Debug` term with and without the drop), and the **multi-result `_all` count is
unchanged** (`Int::parse_via_wpda_all("-3!")` returned the **same 3 alternatives**:
`Fact(NumLit(-3))`, `Fact(Neg(NumLit(3)))`, `Neg(Fact(NumLit(3)))`). This empirically confirms `lex_fork` is
**non-semantic** — it changes *which cursors merge*, not *which parse is produced*.

> **But the global clear is NOT a sound fix.** With `PROBE_DROP_LEXFORK` set, the two **invariant unit tests**
> `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` and
> `arc_merge_disambiguator_distinguishes_lex_fork_stamp` (`tomita_frontier.rs:1231`/`:1250`) **FAIL** — they
> assert that two arcs with `lex_fork_path=[stamp(alt:0)]` vs `[stamp(alt:1)]` (same `pos,src,rule`) stay as
> **two** arcs. A global relaxation of the merge gate violates this. The strict `ConfigKey` docstring
> (`wpda_walker.rs:3528`) names the `-3!` falsification: Branch A (`NumLit "-3" → Fact`) and Branch B
> (`Minus "-" → Neg`) reach the same configuration and **must** bucket separately so both reach their outer
> reduce. **Therefore the fix must NOT weaken the merge gate; it must remove the *sealed-operand* stamps
> UPSTREAM, exactly as the committed rhocalc collection fix does — leaving genuinely-live forks distinct.**

The residual `304` (vs baseline `20`) after the `lex_fork` drop is the `genuine_config_distinct` axis: the
re-run breakdown shows `diff_visited_proj = 70.7 %` of the *residual* no-merges. This `visited_proj_descriptors`
axis is a **secondary** fan-out (the cross-cat projection cycle-defense set, §4.6); the **primary** lever is
`lex_fork` (`1 296 → 304`), and it has a directly-applicable committed precedent.

### 3.6 Cross-product vs additive sharing (diagram)

```
LEX-FORK CROSS-PRODUCT (cursor frontier, HEAD)              ADDITIVE PACKED SHARING (SPPF, already correct)
──────────────────────────────────────────────             ──────────────────────────────────────────────

  operator k  ("+")        operator k+1  ("bitand")               BigInt Symbol [lo..hi]  ← ONE Symbol id / span
  ┌───────────────────┐    ┌───────────────────┐                         │
  │AddBigInt stamp s₀ │─┐ ┌│BitAndBigInt s₀'  │  each shared-operator  ┌──┼──┐
  │AddInt    stamp s₁ │─┼─┼│BitAndInt    s₁'  │  arm appends a UNIQUE  pk pk pk    ← AddBigInt/AddInt/… packings,
  │AddBigRat stamp s₂ │─┼─┼│BitAndBigRat s₂'  │  LexForkStamp; the     │  │  │       weights ⊕-aggregated
  │AddFixed  stamp s₃ │─┘ └│BitAndFixed  s₃'  │  stamp STICKS to       arg arg arg ← child Symbols (shared)
  │ …  (≈d arms)      │    │ …                │  lex_fork_path forever  = O(rules · positions) forest nodes
  └───────────────────┘    └───────────────────┘
         d           ×             d          …… ×d per further operator
               = dᴺ arcs at the SAME TomitaKey          The SPPF already collapses the d arms to ⊕-summed
                 (probe: peak 1296 vs baseline 20)      packings under one Symbol. The leak is purely in
                                                        the cursor frontier's lex_fork-separated bookkeeping.
```

The fix (§4) makes the frontier mirror the right-hand side: once an operand is sealed into its Symbol, its
lex-fork stamps are dropped, so the next operator's arms re-converge to a single frontier arc — additive
`d·N`, not multiplicative `dᴺ`.

---

## 4. Recommended design — seal-local `lex_fork_path` truncation at the infix operand boundary

**Idea.** `lex_fork_path` is a **sidecar that no semantic action, no `engine.step` dispatch, and no SPPF
realizer ever reads** — *every* read of `lex_fork_path.last()` feeds a merge / equivalence-bucketing consumer
(enumerated in §4.2). A lexical-disambiguation choice made *while parsing an operand* is, once that operand is
**reduced onto the SPPF working stack**, already recorded as an **SPPF packing** under the operand's Symbol.
The stamp is then a **redundant** parallel record. Dropping the operand's stamps **at the moment the operand is
sealed** lets the sibling lexical readings of the *next* operator re-converge in the frontier merge —
**without ever weakening the merge gate** (so genuinely-live forks, e.g. `-3!`, stay distinct).

This is the **direct infix twin of the committed rhocalc Change B** (`emit_splice_into_collection`,
`wpda_walker.rs:20050`), which clears `lex_fork_path` when a *collection element* is spliced (sealed). The
collection seal point is the splice; the infix seal point is the **operand reduce that returns the cursor to
`InfixLoop`**.

### 4.1 The seal point (where the operand's stamps become redundant)

In the infix-loop state machine, an operand is *sealed* when its parse reduces and the cursor re-enters
`WpdaState::InfixLoop { cur_bp }` with the operand's Symbol on top of the SPPF working stack. The candidate
seal sites (all already exist; the fix adds a truncation at each):

| Seal site | File:line | Role |
|---|---|---|
| operand reduce → InfixLoop (post-fanout) | `wpda_walker.rs:5590` (`BranchResolved` arm) | a resolved operand returns to the infix loop |
| transparent cross-cat reentry → InfixLoop | `wpda_walker.rs:9811` (`reenter_transparent_projection_source`) | a cast-result operand re-hosts at the infix |
| general operand pop → InfixLoop | the `apply_pop_body_to_cursor` return path (`wpda_walker.rs:23900`) that sets `InfixLoop` | a reduced operand Symbol returns to the infix loop |

Each operand has a **watermark** — the `lex_fork_path.len()` captured when the operand sub-parse *opened* (at
the infix loop's right-operand dispatch / the prefix dispatch that begins the operand). On seal, truncate
`lex_fork_path` back to the watermark. The stamps appended *within* the operand are removed (now redundant SPPF
packings); any stamp appended *at the infix-loop level itself* (above the watermark of the operand) is kept.

> **Why a watermark stack, not a blanket clear.** The committed rhocalc fix could use a blanket
> `clear()` at the splice because a collection element sub-parse fully *destroys and rebuilds* `CollectionLoop`
> from the persistent marker, so no enclosing live stamp survives the element (`rhocalc-collection-fork-
> explosion.md` §3.1 implementation note). The infix spine is **left-associative and continuous**: after sealing
> operand `k`, the cursor is still mid-parse of the *outer* expression, and the **operator-level** lex-fork
> stamps (e.g. the `-3!`-style top-level `Minus` vs `NumLit "-3"` choice) must survive. A blanket clear at the
> infix seal would delete those and re-introduce the very `-3!` merge collapse the strict `ConfigKey` defends
> against. The **per-operand watermark** removes *only* the stamps appended *inside the just-sealed operand*,
> which is exactly the redundant set. This is why §3.5's *global* clear, though result-preserving on the tested
> battery, fails the live-fork invariant — and why the seal-local watermark is the sound refinement.

### 4.2 Why the realized result is unchanged (the core soundness lemma)

**(L1) `lex_fork_path` is non-semantic.** Enumerating every read site of `lex_fork_path` in `prattail/src`:

| Read site | File:line | Consumer class |
|---|---|---|
| `merge_disambiguator` (the `.last()` component) | `tomita_frontier.rs:336` | frontier arc-merge |
| `ConfigKey::from_cursor` (`lex_fork_stamp`) | `wpda_walker.rs:9718`, `:17079` | per-step cursor merge |
| `SubsumeConfigKey::from_cursor` (`lex_fork_stamp`) | `wpda_walker.rs:3353` | single-result subsumption |
| `CohortShell` capture at cohort-pause | `cohort_lazy.rs:557` | H12 cohort `~_obs` bucketing |
| merge-miss diagnostic | `wpda_walker.rs:16759–16761` | `walker-stats` diagnostic |
| memory-attribution diagnostic | `wpda_walker.rs:16603`, `:16617` | `walker-stats` diagnostic |

**Every** consumer is a merge / equivalence / diagnostic feeder. **None** is `engine.step`, a `WpdaStepAction`,
an SPPF intern (`intern_symbol`/`intern_packing`/`link_packing_to_symbol`), or a semantic builder mutation.
Therefore `lex_fork_path` cannot change *which* SPPF nodes exist, *which* tokens are accepted, or *which* term
is realized — it can change only *how many redundant cursor arcs the walker carries*. (Empirically corroborated
in §3.5: the single-result term and the `_all` alternative set are byte-identical under a global drop.) ∎

**(L2) The truncated stamps are provably redundant at the seal point.** When operand `k` reduces, its
lexical-disambiguation choice has been interned as an SPPF **packing** under operand `k`'s Symbol
(`sppf.rs` `intern_packing` / `link_packing_to_symbol`, which `⊕`-aggregate weights, Goodman 1999). The
`lex_fork_path` stamps appended *within* operand `k` are a **parallel** record of that same choice. After the
seal, the only consumers (L1) that read those stamps are merge/bucketing gates; the SPPF already carries the
choice as a packing. So removing the within-operand stamps:

1. cannot remove an SPPF packing (the packing was interned *during* the operand parse, *before* the seal —
   the truncation runs at seal, strictly after intern);
2. lets the `d` sibling lexical readings of operand `k` present **identical** `lex_fork_path` to the *next*
   operator's merge gate, so they `⊕`-collapse to one arc whose weight is the `⊕` (= lex-min) of the siblings —
   the **same** lattice element the SPPF packing-weight `⊕` already computes.

Hence the realized `min_by(weight)` term (single-result) and the full packing set (multi-result) are invariant
under the truncation. ∎

> **Net.** L1: the stamps never affect the parse. L2: the truncated stamps are already SPPF packings at the
> seal, so removing them only re-converges redundant cursors. The parse — single- and multi-result — is
> **invariant**.

### 4.3 Why the live-fork invariants are preserved (the seal-local distinction)

The fix **does not touch** `merge_disambiguator` or `register_arc_with_aggregation` — the merge gate's
comparison is byte-identical, so the unit tests `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs`
and `arc_merge_disambiguator_distinguishes_lex_fork_stamp` (which construct arcs with explicit live stamps and
assert they stay distinct) **pass unchanged**. What changes is *upstream*: by the time two sibling arcs reach
the merge gate, the **within-operand** stamps have been truncated from the cursor, so their `lex_fork_path`s are
equal *for the sealed operand* — but any **still-live** stamp (above the operand watermark) remains and still
keeps genuinely-distinct forks apart. This is the exact rhocalc S4 argument (`rhocalc-collection-fork-
explosion.md` §3.3 S4): the invariant is about forks *still live on the cursor*; the fix removes only stamps
that have *already been sealed into SPPF packings*.

The cohort `~_obs` capture (`cohort_lazy.rs:557`) happens at **pause time** — *during* the operand sub-parse,
*before* the seal — so live operand forks are still bucketed distinctly while in flight; the truncation removes
the stamp only *after* the operand is sealed, exactly when sibling readings re-enter the frontier merge.

### 4.4 Soundness of the specific hazards (S-clauses)

**(S1) `-3!` and the lex-fork falsification are preserved.** The `-3!` distinction (`NumLit "-3" → Fact` vs
`Minus "-" → Neg`) is a **top-level infix-loop** lex fork, not a within-operand one: the `-`/`-3` choice is the
*operator/operand-boundary* decision at the OUTER expression, whose stamp is appended at the infix-loop level,
**above** any operand watermark. The watermark truncation removes only stamps appended *inside* a sealed
operand, so the `-3!` stamps survive and the two readings still bucket separately (the strict `ConfigKey` and
`merge_disambiguator` are untouched). Empirically (§3.5) `_all("-3!")` returns all 3 readings, and the
single-result term is unchanged. Gate: `dangling_else` / ternary / `-3!`-family tests in `languages/tests/calculator.rs`.

**(S2) `@a!(Nil)!(Nil)` chained output is preserved.** Chained send produces two genuinely-distinct parses the
SPPF distinguishes by **span/structure** and the frontier keeps apart by **`sppf_stack_id`** (the GLL `w`
discriminant). The fix touches **only** `lex_fork_path`; `sppf_stack_id` is untouched and remains a full
`merge_disambiguator` / `ConfigKey` / `SubsumeConfigKey` axis. The two readings differ on `sppf_stack`, not on
`lex_fork`, so they never collapse. (This is the same orthogonality the rhocalc fix relied on, S3 there.)
Gate: `gen_guardedrho_*`.

**(S3) The committed rhocalc Cluster-D collection fix stays intact and consistent.** That fix clears
`lex_fork_path` at the *collection splice*; this fix truncates `lex_fork_path` at the *infix operand seal*. They
operate at **disjoint** seal points and use the **same** principle (drop a stamp once its choice is an SPPF
packing). They compose: a collection element that *contains* an infix expression gets its inner-operand stamps
truncated at each infix seal, then the whole element's residual stamps cleared at the splice. The
`lazy_lex_equivalence` rho-collection gate must stay `< 10 s`.

**(S4) The committed single-result subsumption (`c45bdea2`) stays intact and composes.** The subsumption
collapses weight-triple-separated cursors at an identical `SubsumeConfigKey` (which *keeps* `lex_fork_stamp`).
After this fix, the within-operand stamps are gone *before* the subsumption runs, so more cursors share a
`SubsumeConfigKey` and the subsumption fires on the residual weight-triple separation — the two fixes are
**additive** (this fix collapses the `lex_fork` axis; the subsumption collapses the residual weight axis). No
change to `SubsumeConfigKey` or `subsume_weight_dominated_when_single_result` is required.

**(S5) The deep-nesting linear-time fix (`d84b4df4`) stays intact.** That fix operates on
`incoming_edge_stack_id` interning, which the probe shows is **0 %** of the divergence (§3.3) and which this
fix does not touch. No interaction.

**(S6) No new mis-parse / sub-multiset ghost.** The fix never creates a cursor, never alters an SPPF packing,
and never merges *different* configurations — it only removes a redundant *sidecar* record from a single cursor
at a seal boundary, after which the normal merge gate (unchanged) collapses now-identical siblings. It cannot
change which inputs are accepted (L1) or which packings exist (L2).

**(S7) Multi-result paths are preserved.** Unlike the committed subsumption (which is demand-gated), this fix
is **not** demand-gated — but it is sound for *all* callers because (L1) `lex_fork` is non-semantic and (L2)
the truncated stamps are already SPPF packings, so the multi-result `_all` packing set is invariant (§3.5
confirms `_all("-3!")` unchanged). The fix is the upstream analog of rhocalc Change B, which is likewise global
(not demand-gated) for the same reason.

### 4.5 Mechanism + exact code locations

**(M1) A per-operand watermark stack on the cursor.** Add `lex_fork_marks: Arc<Vec<usize>>` to `BranchCursor`
(mirroring `optional_scope_marks`, `wpda_walker.rs:2698`-region) and to `FrontierArc` /
`materialize_branch_cursor_from_arc` / `CohortShell` (the three round-trip carriers, exactly like
`optional_scope_marks`). It must ride on the cursor (not transient state) because the operand sub-parse rebuilds
the infix loop from persistent stack state — the same carrier argument the rhocalc implementation note makes.

| Edit | File | Change |
|---|---|---|
| field | `prattail/src/wpda_walker.rs` `BranchCursor` | `lex_fork_marks: Arc<Vec<usize>>` (default `Arc::new(Vec::new())` in all constructors) |
| carrier | `prattail/src/tomita_frontier.rs` `FrontierArc` + `from_cursor` + `materialize_branch_cursor_from_arc` | clone the `Arc` through the round-trip |
| carrier | `prattail/src/cohort_lazy.rs` `CohortShell` + materialize | clone the `Arc` (shared by members) |

**(M2) Push the watermark at operand open.** At the infix loop's **right-operand dispatch** (where
`emit_lex_fork_at_infix_loop` hands off to the operand's `PrefixDispatch`/`CrossCatDelegate`, `forks.rs:615`-region
and the `parent_frame_with_pushed_fork_branch` operand child allocation), push
`cursor.lex_fork_marks.push(cursor.lex_fork_path.len())`. (Symmetric for the *left* operand at the prefix
dispatch that opens the expression.)

**(M3) Truncate at operand seal.** At each seal site (§4.1: `BranchResolved` `:5590`,
`reenter_transparent_projection_source` `:9811`, and the `apply_pop_body_to_cursor` InfixLoop-return path),
pop the watermark and truncate:

```rust
if let Some(wm) = Arc::make_mut(&mut cursor.lex_fork_marks).pop() {
    if cursor.lex_fork_path.len() > wm {
        Arc::make_mut(&mut cursor.lex_fork_path).truncate(wm);
    }
}
```

This is the structural mirror of `emit_splice_into_collection`'s `Arc::make_mut(&mut cursor.lex_fork_path).clear()`
(`wpda_walker.rs:20050`), but truncating to a per-operand watermark instead of clearing all.

**(M4) Kill switch (P-series convention).** Gate the truncation behind a per-walker env flag read once at
construction (cf. `PRATTAIL_EP_P1`) — e.g. `PRATTAIL_INFIX_LEXFORK_SEAL` (default On) — so a soundness
regression can disable it without reverting the plumbing.

### 4.6 The secondary axis (`visited_proj_descriptors`) — documented, deferred

After the `lex_fork` fix, the residual frontier (`304` vs baseline `20`, §3.5) is dominated by
`visited_proj_descriptors` (`70.7 %` of the *residual* no-merges). `ProjDescriptorKey =
(gss_node, sppf_stack, pos, cat_src, cur_bp)` is the cross-cat projection **cycle-defense** set: it accumulates
one descriptor per cross-cat `PrefixDispatch` and prevents infinite projection cycles. Each infix cross-cat arm
descends through a different projection lineage and accumulates a different descriptor *set*, keeping the arms
apart even after `lex_fork` is removed.

Whether this axis is a **false divergence** (the descriptor set is redundant once the operand is sealed — a
watermark/truncation analog) or **genuine cycle-defense** (the set must persist to prevent a re-entry loop)
requires its own probe-and-soundness pass and is **out of scope** for this document. It is a **secondary**
effect: the `lex_fork` fix alone recovers `~4.3×` of the frontier (`1 296 → 304`) and `~7.6×` of the wall time
(bigint n=8 `4 840 → 640 ms`), which is the dominant share of the regression. The `visited_proj` axis is
recorded as the next investigation if the heavy proptests do not reach the §6.1 targets with the `lex_fork` fix
alone. (Hypothesis to test there: truncate `visited_proj_descriptors` to a per-operand watermark at the same
seal points, gated on the descriptor being *strictly inside* the sealed operand's span — sound only if no
enclosing cross-cat re-entry can re-reach the same `(node, sppf_stack, pos, cat, bp)`; this needs the cycle-
defense soundness argument the lex-fork case does not.)

---

## 5. Rejected alternatives

### 5.1 Reject — global `lex_fork` merge-gate relaxation (probe-refuted)

**Proposal.** Drop `lex_fork_path.last()` from `merge_disambiguator` (and the strict `ConfigKey` /
`SubsumeConfigKey`) globally — the analog of the rhocalc *Change A* arena content-equality (a global merge-gate
relaxation).

**Why rejected.** §3.5 implemented exactly this behind `PROBE_DROP_LEXFORK` and showed it **breaks the
live-fork invariant unit tests** `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` and
`arc_merge_disambiguator_distinguishes_lex_fork_stamp`. A global relaxation merges two arcs with *genuinely
distinct live* stamps (the `-3!` Branch-A/Branch-B case the strict `ConfigKey` docstring names at
`wpda_walker.rs:3528`), which is unsound for the multi-result mandate even though it happened to preserve the
*specific* `-3!` `_all` count in the tested battery (because the weight triple coincidentally also separated
them there — not a guarantee). The rhocalc document made the same distinction: arena content-equality is a
sound *global* relaxation (the content is the only observable), but `lex_fork` is **not** globally relaxable —
the rhocalc fix put `lex_fork` behind the *collection-local* seal (Change B), never a global merge relaxation.
**The seal-local truncation (§4) is the sound form; the global relaxation is not.**

### 5.2 Reject — extend the committed single-result subsumption to drop `lex_fork` from `SubsumeConfigKey`

**Proposal.** Loosen `SubsumeConfigKey` to also drop `lex_fork_stamp`, so the demand-gated subsumption
collapses the `lex_fork`-separated cursors.

**Why rejected.** (a) It would make the subsumption collapse cursors that differ in a genuinely-live lex fork
**at the single-result level**, which is the *same* unsoundness as §5.1 restricted to demand mode — and the
demand path also feeds the `AcceptedWithTrailing` exhaustive retry (`facade.rs:178`), so the live-fork
distinction can still matter. (b) It is **strictly weaker** than the seal-local fix: the subsumption fires only
*after* each step's merge, so it would still let the per-operator fan transiently reach `d` arcs and only prune
*post hoc*, whereas the seal-local truncation makes the arcs **re-converge in the merge gate itself** (so the
fan never materialises across operators). (c) It does nothing for the multi-result path (the subsumption is
demand-gated), whereas the seal-local fix is sound for *all* callers (S7). The seal-local truncation is the
upstream, mandate-clean, all-caller fix; loosening the subsumption is downstream, narrower, and re-opens the
live-fork hazard.

### 5.3 Reject — revert the `30acf6de` fan-out wholesale

The rhocalc §4 verdict applies verbatim: reverting the GSS-pushing cross-cat fork frames would undo the
`30acf6de` soundness commits (`db53e83a`, `ea1dcb6b`, `ddfafc9f` — projection evidence, prefix ambiguity,
demand-sensitivity), which the design constraint forbids. The redundancy is real but is fixable *without*
touching the fan-out, by removing the redundant *sidecar* record at the seal point.

### 5.4 Reject — grammar disambiguation (merge per-category operator rules)

Collapsing the seven `+` rules (and the rest) into one polymorphic rule would remove the cross-cat cohort
entirely, but it is a **grammar/semantics change** (it changes the admitted derivations and the cast lattice),
explicitly out of scope, and it would alter the `_all` ambiguity surface (a behavioural change). Rejected.

---

## 6. Verification / test plan

### 6.1 Performance targets (acceptance criteria)

| Metric | Target | How |
|---|---|---|
| `gen_calculator_prop::bigint_display_parse_roundtrip` | **passes, < 60 s** (so it never tail-times-out) | `cargo test -p mettail-languages --test gen_calculator_prop bigint_display_parse_roundtrip` |
| `gen_calculator_prop::bigrat_display_parse_roundtrip` | **passes, < 60 s** | likewise |
| `gen_calculator_prop::map_display_parse_roundtrip` | **passes, well under baseline (~25 s)** | likewise (the `lex_fork` fix also helps map's residual where map values are infix) |
| `gen_calculator_prop::sim_calculator_proptest_campaign` | **passes, < 60 s** | likewise |
| bigint infix n=8 peak frontier | `≈ baseline` (≤ ~40; was 1 296) | `walker-stats` probe (re-add §3 probe before/after) |
| bigint infix n=8 wall (debug) | `≤ baseline` after the secondary axis, or `≤ ~640 ms` with `lex_fork` alone (was ~2 548 ms) | the §3.1 timing probe |
| curve | sub-`dᴺ` (near-linear with both axes; sub-quadratic with `lex_fork` alone) | depths 1..8, before/after |

Iterate with the **small-depth probe** (n=4..8 single-term parses), **never** the 40 s+ proptest, per the
brief. The `lex_fork` fix alone is expected to clear all four proptests under the 60 s tail-safety bar (it
removes the dominant `60–75 %` of the redundancy and `7.6×` of the wall time); if any proptest still exceeds
60 s, implement the §4.6 `visited_proj` secondary axis.

### 6.2 Soundness gates that must stay green (byte-identical ON vs OFF)

Run each suite with the fix default-ON and with `PRATTAIL_INFIX_LEXFORK_SEAL=0` (OFF); the pass-sets must be
**byte-identical** (any divergence on a non-timing test is a soundness bug — the mandate):

| Suite | What it guards | Command |
|---|---|---|
| `mettail-prattail` lib (incl. `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` `:1250`, `arc_merge_disambiguator_distinguishes_lex_fork_stamp` `:1231`, and the other `arc_merge_disambiguator_distinguishes_*`) | the merge gate is **untouched** (S1/§4.3) | `cargo nextest run -p mettail-prattail` |
| `gen_calculator_*` (unit / analytical / rewrite / prop) + `calculator` + `calculator_display_projection_tests` + `display_roundtrip_regression_tests` + dangling-else / ternary / `-3!`-family | calculator parse/eval/roundtrip + the `-3!` lex-fork falsification (S1) | `cargo test -p mettail-languages --test gen_calculator_unit` (+ the rest) |
| `rhocalc_tests` + `gen_rhocalc_{unit,analytical,rewrite,prop}` + `wpda_parity_rhocalc_collections` | rhocalc comm / cross-cat + the committed Change-B composition (S3) | `cargo test -p mettail-languages --test rhocalc_tests` (+ the rest) |
| `gen_guardedrho_*` (incl. chained output `@a!(Nil)!(Nil)`, S2) | the `sppf_stack_id` chained-output distinction | `cargo test -p mettail-languages --test gen_guardedrho_unit` |
| `lazy_lex_equivalence` (full corpus) — **must stay < 10 s** | the committed rhocalc Cluster-D fix (S3); lazy ≡ eager | `cargo test -p mettail-languages --test lazy_lex_equivalence` |
| full gauntlet (calc-op, edge_case_tests, ledtest, ambient, recovery_accumulation, led_delegation_tests, `test_deep_parens_100000`, `test_deep_unary_neg_10000`) | no cross-language / committed-fix / deep-nesting regression (S4/S5) | the standard battery |

### 6.3 New tests to add

- `wpda_walker.rs` unit `infix_seal_truncates_within_operand_lex_fork_only` — a cursor with operand-internal
  stamps + an operator-level stamp; after the seal-truncation, the operand stamps are gone and the
  operator-level stamp remains (the watermark boundary).
- `wpda_walker.rs` unit `infix_seal_preserves_live_top_level_fork` — two cursors that differ in a *top-level*
  (above-watermark) lex fork are **not** merged after the seal (the `-3!` guard, S1).
- `languages/tests` `bigint_infix_is_subquadratic` — parse `1n + 2n - 3n bitand …` for n ∈ {2,4,6,8} under
  `walker-stats`; assert peak frontier `≤ C · baseline` for small `C`. Numeric (bigint/bigrat) and bare-int
  variants.
- `languages/tests` parse-result equality — a battery of infix bigint/bigrat surfaces: `Cat::parse(s)`
  (single-result) returns the **identical** `Debug` term before/after the fix, **and**
  `Cat::parse_via_wpda_all(s)` returns the **identical** alternative *set* before/after (L1/L2 + S7 empirical).
- Add an `-3!`-family `_all`-multiplicity assertion mirroring `calculator.rs:262` to confirm the 3-reading set
  survives the fix.

### 6.4 Differential check (single-result == previous, multi-result unchanged)

For the infix battery, assert `Cat::parse(s)` returns the identical `Debug` term and `pos` before/after, and
`parse_<Cat>_via_wpda_all(s)` returns the identical alternative set before/after (the §3.5 byte-identical
result, now as a regression test). This is the empirical form of L1 + L2 + S7.

### 6.5 Formal note (optional, recommended)

Extend the evidence-pruning proof family (`CollectionForkEvidence.v` / the rhocalc Change-B lemma) with an
**`infix_operand_seal_preserves_parse`** lemma: under the `LexicographicWeight` semiring, truncating
`lex_fork_path` to the operand-open watermark at the operand seal (a) preserves the SPPF (the operand's lexical
choice is interned as a packing strictly before the seal — L2), and (b) preserves the merge gate's behaviour on
live (above-watermark) stamps (S1/§4.3). Zero-admission. This is the machine-checked counterpart of the
committed rhocalc collection-seal lemma, lifted from the collection splice to the infix operand boundary.

---

## 7. Probe hygiene

All probe instrumentation used to produce §3 was **throwaway** and has been **reverted**:

- `prattail/src/tomita_frontier.rs` — `ProbeNoMerge` thread-local + per-axis classifier in
  `register_arc_with_aggregation` + the `PROBE_DROP_LEXFORK` gate in `merge_disambiguator`. **Reverted**
  (`git checkout`).
- `prattail/src/wpda_walker.rs` — the `PROBE_DROP_LEXFORK` gates in `ConfigKey::from_cursor` and
  `SubsumeConfigKey::from_cursor`. **Reverted** (`git checkout`).
- `languages/tests/zz_probe_broad.rs` — the timing + walker-stats + no-merge-breakdown + result-equality probe.
  **Deleted.**
- The same probe test temporarily copied into the read-only baseline worktree `mettail-rust-lexdeleg`.
  **Deleted** (no other change made to that worktree; pre-existing unrelated artifacts there — a dormant
  `PRATTAIL_PROBE_RESOLVE` mod and `zzz_probe_recovery.rs` from a prior session — were left untouched).

The only artifact of this work is this design document. The repo working tree shows only this file.

---

## 8. Summary

- **Confirmed root cause:** a GLR cursor-frontier sharing leak on the **infix** surface — distinct from both
  companion cases. The infix-loop lex-fork emitter forks one arm **per category that shares an operator token**
  (`+`, `-`, `*`, `/`, `bitand`, `bitor`), each appending a distinct **`LexForkStamp`** to the `lex_fork_path`
  sidecar; because `lex_fork_path.last()` is a **kept** axis of *both* the strict merge key *and* the committed
  `SubsumeConfigKey`, the per-operator cross-cat cohort never re-converges and the fan multiplies across the
  infix spine into an `O(dᴺ)` frontier (peak `1 296` vs baseline `20` — `65×`; bigint n=8 `231×` wall, bigrat
  `120×`).
- **Divergence-axis pinpoint (probe):** `lex_fork` is the **dominant blocker** (`80–84 %` of no-merges;
  `~60–75 %` combined with the weight triple; **`47–60 %` *sole* `lex_fork` blocks**), NOT the weight triple
  (the map case's `95.6 %` axis, here only `~25 %`). `incoming_edge_stack` is **0 %** (hash-consed). The
  committed subsumption captures `< 3 %` because it keeps `lex_fork`. A controlled drop confirms `lex_fork` is
  the lever (frontier `1 296 → 304`, wall `4 840 → 640 ms`) and **non-semantic** (single-result term and
  `_all` set byte-identical) — but the *global* drop breaks the live-fork invariant tests, so the fix must be
  **seal-local**.
- **Classification:** **false divergence**, but the merge gate may **not** be globally relaxed (the live-fork
  `-3!` invariant) ⇒ the fix removes the redundant stamps **upstream**, at the seal point — the infix twin of
  the committed rhocalc Change B.
- **Recommended fix:** **seal-local `lex_fork_path` truncation at the infix operand boundary** — a per-operand
  watermark (`lex_fork_marks`, mirroring `optional_scope_marks`) pushed at operand-open and truncated at the
  operand seal (`BranchResolved` / transparent-reentry / `apply_pop_body_to_cursor` InfixLoop-return). Result-
  preserving by L1 (`lex_fork` non-semantic — all read sites are merge/diagnostic) + L2 (the truncated stamps
  are already SPPF packings at the seal). Behind the `PRATTAIL_INFIX_LEXFORK_SEAL` kill switch.
- **Soundness / compatibility:** the merge gate (`merge_disambiguator` / `register_arc_with_aggregation`) is
  **untouched** (the invariant tests pass), `-3!` and `@a!(Nil)!(Nil)` are preserved (S1/S2 — their forks are
  top-level / `sppf_stack`-borne, not within-operand), the committed rhocalc collection fix (S3) and single-
  result subsumption (S4) compose additively, and the deep-nesting fix (S5) is orthogonal. Sound for **all**
  callers (S7), unlike the demand-gated subsumption.
- **Rejected:** global `lex_fork` merge relaxation (breaks the live-fork invariant — probe-refuted §5.1);
  loosening `SubsumeConfigKey` to drop `lex_fork` (re-opens the live-fork hazard, strictly weaker, demand-only
  §5.2); fan-out revert (undoes `30acf6de` §5.3); grammar disambiguation (semantics change §5.4).
- **Secondary axis (documented, deferred):** after the `lex_fork` fix, the residual frontier (`304` vs `20`) is
  dominated by `visited_proj_descriptors` (the cross-cat projection cycle-defense set) — a separate, smaller
  axis requiring its own cycle-defense soundness argument (§4.6); pursued only if the `lex_fork` fix alone does
  not reach the §6.1 targets.

---

## 9. Implemented (2026-06-21)

The fix was implemented as a **stack-free clear-all** of `lex_fork_path` at the canonical infix-operand seal,
behind the `PRATTAIL_INFIX_LEXCLEAR` kill switch, after the clear-all-vs-watermark question (§4.1) was decided
**empirically** in favour of clear-all. The change is confined to `prattail/src/wpda_walker.rs`; the
`macros/.../forks.rs` emitter is **unchanged**.

### 9.1 Final form (what landed)

| Edit | File | Change |
|---|---|---|
| kill-switch enum | `prattail/src/wpda_walker.rs` (after `SrSubsumeMode`) | `enum InfixLexclearMode { Off, Clear, Watermark }` + `from_env()` reading `PRATTAIL_INFIX_LEXCLEAR` once per construction (default `Clear`; `0`/`off` → `Off`; `watermark` → `Watermark`) — the P-series convention, mirroring `SrSubsumeMode` |
| walker fields | `WpdaWalker` struct | `infix_lexclear_mode: InfixLexclearMode` (init `from_env()` in all 3 constructors) + `infix_lexclear_watermark: usize` (comparison-only scratch for the `Watermark` variant) |
| **the seal clear** | `apply_pop_body_to_cursor`, immediately before the final `set_cursor_inner_state(cursor, resolved_new_state)` | when `resolved_new_state` is `InfixLoop { .. }` and `!cursor.lex_fork_path.is_empty()`: `Clear` ⇒ `Arc::make_mut(&mut cursor.lex_fork_path).clear()`; `Watermark` ⇒ `truncate(infix_lexclear_watermark)` (benign no-op when the watermark exceeds the length); `Off` ⇒ leave intact |
| watermark capture | `allocate_uncached_push_child`, at the lex-fork stamp push | when `infix_lexclear_mode == Watermark`, record `infix_lexclear_watermark = child.lex_fork_path.len()` *before* pushing the operand's stamp (the operand-open watermark) — comparison-only; the production `Clear` default never reads it |

**The canonical seal site.** The design (§4.1) named three candidate seal sites at the prior HEAD. Reading
the current tree corrected this:

- `BranchResolved` (the post-AmbiguityFanout resolution write-back) **already constructs a fresh cursor with
  `lex_fork_path: Arc::new(Vec::new())`** — it is the *top-level* resolution, not a per-operand infix seal, and
  needs no clear.
- `reenter_transparent_projection_source` is one specific cast-result reentry into `InfixLoop`; it mutates the
  cursor in place but is **subsumed** by the general path below.
- `apply_pop_body_to_cursor`'s **final `set_cursor_inner_state`** (the single, post-everything state write —
  after all splices, `emit_fire_action`s, cross-cat reentries, and weight multiplications) is the **one
  canonical operand-seal-into-the-infix-loop** point. Clearing there (gated on `resolved_new_state ==
  InfixLoop`) covers every operand reduce that returns the cursor to the infix loop, including the
  transparent-reentry and cross-cat-LHS-reentry cases (they all funnel through this write). This is the exact
  structural mirror of the rhocalc `emit_splice_into_collection` clear, lifted from the collection splice to
  the infix operand boundary.

### 9.2 Clear-all vs watermark — decided empirically (clear-all)

The §4.1 design recommended a per-operand **watermark** (to keep enclosing-operator stamps live, since the
infix spine is left-associative/continuous, unlike the rhocalc collection that rebuilds `CollectionLoop` from
a marker). A throwaway probe implemented **both** `Clear` and `Watermark` behind `PRATTAIL_INFIX_LEXCLEAR` and
compared realized terms across a battery of left-nested infix chains (bigint / bigrat / bare-int, `n ∈ 1..8`),
**precedence-climbing** surfaces (`a + b*c …` — the exact hazard where an outer operator's stamp is live while
an inner higher-precedence operand seals), and the `-3!` family, in BOTH single-result (`Cat::parse`) and
multi-result (`parse_via_wpda_all`) modes:

> **`Clear` ≡ `Watermark` ≡ `Off`** on every surface — single-result terms AND `_all` alternative sets were
> **byte-identical**, and `Clear`/`Watermark` timings were within noise of each other.

This **empirically refutes the precedence-climbing over-clear hazard**: dropping the live outer-operator stamp
under `Clear` changes no realized term, because the genuine cross-cat-arm distinction also rides the
`LexicographicWeight` provenance triple (`lex_alt_idx, weight_src_idx, weight_rule_idx`) **and** `sppf_stack_id`
— both UNTOUCHED by this fix and both KEPT in `ConfigKey` / `merge_disambiguator`. The `lex_fork` axis the
clear removes is, at the seal, redundant with those surviving axes. This is the same outcome the committed
rhocalc red-team reached for the collection splice (`rhocalc-collection-fork-explosion.md` §8.1: watermark and
clear-all bit-identical; clear-all chosen because it is stack-free, cannot underflow, and needs no cohort-shell
carrier). **`Clear` is therefore the production default**; `Watermark` is retained only as an A/B lever.
Choosing `Clear` also avoided the §4.5-M1 ~40-site `lex_fork_marks` carrier plumbing across every
`BranchCursor` constructor + `FrontierArc` + `CohortShell` round-trip.

### 9.3 ON/OFF differential (soundness mandate — byte-identical)

Run with the fix default-ON (`Clear`) and with `PRATTAIL_INFIX_LEXCLEAR=0` (OFF); the pass-sets are
**byte-identical** (sequence-number-stripped, sorted):

| Suite | tests | ON vs OFF |
|---|---:|---|
| `mettail-prattail` lib (incl. both live-fork invariants `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs`, `arc_merge_disambiguator_distinguishes_lex_fork_stamp`) | 3795 | **BYTE-IDENTICAL**, all PASS |
| `gen_calculator_{unit,analytical,rewrite}` + `calculator` + `calculator_display_projection_tests` + `display_roundtrip_regression_tests` + `rhocalc_tests` + `gen_rhocalc_unit` + `wpda_parity_rhocalc_collections` + `lazy_lex_equivalence` + `led_delegation_tests` + `edge_case_tests` + `recovery_accumulation` + `roundtrip_tests` + `gen_guardedrho_unit` + `test_deep_parens_100000` | 831 | **BYTE-IDENTICAL**, all PASS |
| full languages non-`*_prop` gauntlet (ALL languages: ambient, basemath, extmath, guardedrho, importedmath, rhocalc, mixedmath, all class2/class3 collection variants, calculator, led_test, composition, consolidation, `collection_ghost_regression`, …) | 2332 | **BYTE-IDENTICAL**, all PASS |

The merge gate (`merge_disambiguator` / `register_arc_with_aggregation`) is untouched, so the two live-fork
invariant unit tests — which construct `FrontierArc`s by hand and assert the gate keeps distinct-stamp arcs
separate — pass unchanged (the fix changes the gate's *input* upstream at the seal, not its comparison).
`parse_via_wpda_all("-3!")` returns the same **3** alternatives in all three modes (multi-result preserved).

### 9.4 Performance (controlled, `taskset` clean core)

The heavy display-roundtrip proptests, ON (`Clear`) vs OFF, single test, pinned to an isolated core:

| `gen_calculator_prop` test | ON (`Clear`) | OFF | speedup | note |
|---|---:|---:|---:|---|
| `bigint_display_parse_roundtrip` | **9.7 s** | 11.4 s | 1.2× | parse-bound; well under 60 s |
| `bigrat_display_parse_roundtrip` | **24.1 s** | 301.7 s | **12.5×** | parse-bound; the dominant O(dᴺ) win |
| `map_display_parse_roundtrip` | **34.8 s** | 154.9 s | **4.4×** | parse-bound (map values are infix) |
| `sim_calculator_proptest_campaign` | **91.4 s** | ~192–201 s | ~2.1× | **simulation-bound — see §9.5** |

The small-depth infix probe (debug, `taskset -c 0`) confirmed the curve flattens from super-linear toward
additive: bigint `n=8` `2743 ms` (OFF) → `533 ms` (`Clear`) ≈ **5.1×**, with the speedup *growing* in depth.
Under the full-binary 16-core run, ON eliminated **3 of the 4** OFF timeouts (`bigint`/`bigrat`/`map`), leaving
only `sim`.

### 9.5 The `sim` residual is SIMULATION-bound, NOT the §4.6 secondary parse axis

The design §4.6 framed any residual `sim` slowness as the `visited_proj_descriptors` secondary *parse* axis,
pursued "if `sim` still exceeds 60 s." A throwaway probe **refuted that premise**: `sim_calculator_proptest_
campaign` does not parse-roundtrip — it calls `runner.run_to_normal_form(&displayed)`, a full **simulation**
(parse + up to 50 rewrite steps + invariant checks per term). Timing parse vs `run_to_normal_form` on
`arb_bool(3)`-shaped terms:

> **parse is only `9.2 %` of `run_to_normal_form`** (per-term `parse ≈ 386 ms` vs `sim ≈ 4193 ms` over the
> battery); the other `~91 %` is the rewrite/simulation engine.

Two corroborating probes: (a) synthetic deeply-nested cross-cat `Bool` comparison chains parse **linearly** and
**identically ON vs OFF** (the `lex_fork` axis is not the `sim` driver, and there is no parse blow-up to
collapse there); (b) `sim` times out OFF as well (it is in the OFF 4-timeout set), so the fix does not regress
it — it *improves* it (`~192 s → ~104 s` on a contended core; `~201 s → 91 s` clean) via its `9 %` parse share.

**Conclusion:** the `sim` timeout under maximal (32-logical-core) concurrency is a **pre-existing
simulation-engine cost**, out of scope for an infix-*parser* fix; the `visited_proj_descriptors` secondary
*parse* axis (§4.6) is **irrelevant to it** and is NOT implemented (it would be the right lever only for a
genuinely parse-bound residual, which `sim` is not). The genuinely parse-bound regressions (`bigint`, `bigrat`,
`map`) are fully resolved by the `lex_fork` clear. `sim` remains borderline against the 180 s leak-detection
cap on a heavily-loaded machine purely because of the rewrite engine; resolving it requires a
simulation-engine optimization tracked separately.

### 9.6 Residual `visited_proj_descriptors` note (unchanged from §4.6, re-scoped)

For the genuinely parse-bound surfaces the `lex_fork` clear already lands them comfortably under target
(`bigint`/`bigrat`/`map` all < 60 s), so the §4.6 `visited_proj_descriptors` secondary parse axis was **not
needed** and is **not implemented**. It remains documented as the next lever **iff** a future genuinely
parse-bound surface exceeds target — but note its higher risk: `visited_proj_descriptors` is a *semantic*
cross-cat-projection cycle-defense set read by the dispatch logic (`engine.step`-adjacent
`contains(&desc) ⇒ DROP`), not a non-semantic merge sidecar like `lex_fork_path`, so truncating it requires the
cycle-defense soundness argument (§4.6) the `lex_fork` case did not — a Plan-level design, not a drop-in twin of
this fix.
