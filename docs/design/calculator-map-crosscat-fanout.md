# Calculator Map Cross-Category Fan-Out Explosion — Weight-Provenance Cursor Cross-Product

**Target:** branch `feature/wfst-architecture`, HEAD `9c8da1eb`.
**Status:** IMPLEMENTED + verified (commit pending; uncommitted on `feature/wfst-architecture`). Root cause
re-confirmed by throwaway probe (this document, §3); the WHY-no-reconvergence question is answered precisely
(§3.4); the implemented direction is **Direction 2 (single-result demand-mode weight-dominance subsumption)**
with a rigorous soundness argument (§4), the rejected direction recorded (§5), and the implementation +
ON/OFF differential + timing results recorded in §8.6.
**Scope (recommended fix):** WPDA walker frontier-pruning, single-result demand path only
(`prattail/src/wpda_walker.rs`). One small flag on `WpdaWalker`, one demand-gated subsumption pass. **No
grammar / regex / spec change. No change to the multi-result (`_all`/`_prefix`) path. No revert of any
committed fix.**

**Companion document.** `docs/design/rhocalc-collection-fork-explosion.md` covers the *lexical* sibling case
(rhocalc `{0|1|…|19}`), where the redundant axis was a **false divergence** (the `sppf_collection_arena`
`Arc` pointer + the `lex_fork_path` sidecar) curable by a global content-equality relaxation. **This case is
different**: the probe proves there is **no false-divergence axis** to relax here — the dominant blocker is the
**`LexicographicWeight` provenance triple**, which is *genuine* multi-result evidence. The two documents
therefore reach *different* conclusions by the *same* method (probe → pinpoint → soundness). §8.2 of the
rhocalc document explicitly named the weight triple as the residual `O(N²)` it left out of scope "because it
touches the weight provenance the `30acf6de` series relies on" — that residual is precisely the *primary*
driver here, and this document shows how to neutralise it **soundly for the single-result path** without
touching the multi-result evidence.

---

## 1. Problem

The calculator property test
`languages/tests/gen_calculator_prop.rs::map_display_parse_roundtrip` (`arb_map(3)`, 100 proptest cases)
**times out (> 180 s)** on HEAD. The baseline `b781d754` ran the same test in ~127 s (it PASSED). The
regression is a **super-linear blow-up of the WPDA cursor frontier** when parsing the *nested function-call*
map terms that `arb_map` generates (`put(m,k,v)`, `get(m,k)`, `merge(a,b)`, `delete(m,k)`, `map()`), **not**
the `{k:v}` collection-literal surface that the rhocalc case exercises.

### 1.1 Symbol glossary (defined before use)

| Symbol / term | Meaning |
|---|---|
| WPDA | Weighted Push-Down Automaton — the parser runtime (`prattail/src/wpda_walker.rs`) |
| GLR / GLL | Generalised LR / LL parsing (Tomita 1985; Scott & Johnstone 2010) — the multi-cursor model |
| SPPF | Shared Packed Parse Forest — the parse-forest DAG (`prattail/src/sppf.rs`) |
| Symbol node | an SPPF identity node keyed by `(non-terminal, lo_pos, hi_pos)` — `sppf.rs:543` |
| Packing node | one *derivation* of a Symbol, keyed by `(rule_idx, children)` — `sppf.rs:573` |
| `weight_sum` | per-Symbol `⊕`-aggregate of its packings' weights (Goodman 1999) — `sppf.rs:190`, `:733` |
| cursor / arc | one live parse configuration in the frontier (`BranchCursor`; `FrontierArc` when ingested) |
| frontier | the live set of cursors at one walker step (`self.branch_cursors`) |
| TomitaKey | the frontier *merge key* `(state, node, pos, edge_top, edge_stack, collection_depth)` — `tomita_frontier.rs:70` |
| `merge_disambiguator` | the arc-level *anti-merge* tuple inside a TomitaKey bucket — `tomita_frontier.rs:326` |
| `sppf_stack_id` | per-cursor interned handle to the GLL working stack `w` (Copy `u32`) — `wpda_walker.rs:2618` |
| `incoming_edge_stack_id` | per-cursor interned handle to the GSS return-edge stack (Copy `u32`) — `wpda_walker.rs:2480` |
| `LexicographicWeight` | the path weight: `(primary: TropicalWeight, lex_alt_idx, src_idx, rule_idx)` — `rigail/src/lex_weight.rs:184` |
| weight provenance triple | the three integer tiebreaks `(lex_alt_idx, src_idx, rule_idx)` of a `LexicographicWeight` |
| `⊕` (`plus`) | semiring add = **lex-min** (idempotent) — `rigail/src/lex_weight.rs:405` |
| `⊗` (`times`) | semiring multiply = tropical-sum primary + **left-projection** of the triple — `rigail/src/lex_weight.rs:418` |
| cross-cat | a rule whose argument/result category differs from the category being parsed (a cast or a foreign-arg op) |
| single-result demand | the `Cat::parse` facade path: stop at the first accepting root, realize `min_by(weight)` |
| cross-product | a multiplicative blow-up: per-element/per-nesting choices multiply instead of adding |

### 1.2 What `arb_map` actually generates (the hot surface)

`build_map_from_tape` (`gen_calculator_prop.rs:1223`) emits **only** nested function-call ops:

```
map()                          base case (empty map literal — zero-ary)
put(<map>, <proc>, <proc>)     PutMap   : m:Map, k:Proc, v:Proc |- "put" "(" m "," k "," v ")" : Map
get(<map>, <proc>)             GetMap   : m:Map, k:Proc         |- "get" "(" m "," k ")"        : Proc
merge(<map>, <map>)            MergeMap : a:Map, b:Map          |- "merge" "(" a "," b ")"       : Map
delete(<map>, <proc>)          DeleteMap: m:Map, k:Proc         |- "delete" "(" m "," k ")"      : Map
```

It does **not** emit `{k:v}` map literals. Therefore `emit_splice_into_collection` (the rhocalc hot path) is
**never on the hot path here.** The slowness is *not* the lexical collection cross-product fixed in
`docs/design/rhocalc-collection-fork-explosion.md`.

### 1.3 The cross-category ambiguity (the multiplier)

The map ops take `Proc`-typed arguments (`k:Proc`, `v:Proc`) and `GetMap` *returns* `Proc`. The calculator's
`Proc` category is enormous and cross-cat-dense (`languages/src/calculator.rs`):

- `ProcMap . m:Map |- m : Proc` (`:106`) casts a `Map` up to `Proc` — so a `put(...)`/`merge(...)`/`delete(...)`
  (all `: Map`) is usable in any `Proc` argument slot.
- `GetMap . … : Proc` (`:417`) returns `Proc`, also usable in `Map`-typed slots through the reverse cast lattice.
- ~40 keyword-headed `Proc` rules + `VarProc` all compete at every `Proc` argument position, plus the numeric
  cast cascade `ProcInt`/`ProcBigInt`/`ProcBigRat` (`:100`,`:108`,`:109`) and `IntToBigInt`/`IntToBigRat`
  (`:128`,`:129`). The compile-time grammar lint dumps the competition explicitly, e.g.

  ```
  Proc: KwPut→ProcMap (vs VarProc wt 11.00); KwGet→GetMap (vs VarProc wt 11.00);
        KwMerge→ProcMap (vs VarProc wt 11.00); KwDelete→ProcList (vs ProcMap wt 0.67, VarProc wt 11.00); …
  ```

Every `Proc` argument position thus forks a **cohort of cross-cat delegate arms**, one per candidate source
category `×` wrapping rule. Each nesting level of `put(...)` multiplies that cohort against the enclosing one.
This is a *non-lexical* cross-product — it reproduces even when every key/value is a single-lex `Var`.

---

## 2. Confirmed root cause (one sentence)

> The `30acf6de` "preserve ambiguity and runtime evidence" series switched the cross-cat-delegate cohort
> fan-out from **metadata-only return frames** (`parent_frame_with_fork_metadata`, baseline — frontier
> re-converged) to **GSS-pushing fork frames** (`parent_frame_with_pushed_fork_branch`, HEAD — distinct return
> lineages), and each fork arm carries a distinct **`LexicographicWeight` provenance triple**
> `(lex_alt_idx, src_idx, rule_idx)` that the `merge_disambiguator` keeps apart; because the triple is *genuine
> multi-result tiebreak evidence* (not a false-divergence `Arc`), the per-argument cross-cat cohort *never
> re-converges*, and the per-level fan multiplies across the nesting depth into a super-linear frontier.

The frontier blow-up is the cause of the wall-time regression: per-step cost is `O(frontier)` (merge + hash),
so a `~3.7–4.7×` larger concurrent frontier costs `~2.3–3.3×` wall-time even at the *same* total work.

---

## 3. Probe evidence

A throwaway probe (since reverted; see §7) parsed left-nested `put(put(…put(map(),X,X)…,X,X),X,X)` for
nesting `depth ∈ {1..6}` via `Map::parse` (the single-result demand facade — the failing test's entry point),
with two controls: **VAR** (`X = a`, single-lex — isolates the *non-lexical* cross-cat mechanism) and **NUM**
(`X = 0`, tri-lex — adds the lexical multiplier on top). Frontier counters came from the built-in
`walker-stats` (`PRATTAIL_WALKER_STATS=1`, feature `walker-stats`); the per-axis no-merge breakdown came from
a temporary classifier in `register_arc_with_aggregation`. Baseline numbers are from the read-only worktree
`mettail-rust-lexdeleg @ b781d754`. All runs: debug build, `taskset -c 0`.

### 3.1 The super-linear curve (timing, VAR control)

| depth | input len | **baseline** `b781d754` time | **HEAD** `9c8da1eb` time | ratio |
|------:|----------:|-----------------------------:|-------------------------:|------:|
| 1 | 14 | 27.2 ms | 25.8 ms | 0.95× |
| 2 | 23 | 142.3 ms | 208.3 ms | 1.46× |
| 3 | 32 | 708.7 ms | 1 588.2 ms | 2.24× |
| 4 | 41 | 1 917.5 ms | 5 318.5 ms | **2.77×** |
| 5 | 50 | 3 783.8 ms | 11 578.7 ms | **3.06×** |
| 6 | 59 | 6 293.9 ms | 20 239.8 ms | **3.22×** |

The VAR control is single-lex, so the curve is driven entirely by the **cross-cat** fan-out, not lexical
ambiguity. The HEAD/baseline ratio *grows* with depth (2.24× → 3.22×), i.e. the regression is super-linear in
the regression itself — consistent with the brief's "2.29× typical, 3.33× worst case."

### 3.2 Frontier size (walker-stats, VAR depth 4)

| Metric | baseline `b781d754` | HEAD `9c8da1eb` | ratio |
|---|---:|---:|---:|
| `branch_cursors_peak_pre_merge` | 3 046 | **14 215** | **4.67×** |
| `branch_cursors_peak_post_merge` | 2 833 | 11 941 | 4.21× |
| `max_cursors_per_step` | 2 833 | 11 453 | 4.04× |
| `max_distinct_per_step` (distinct TomitaKeys) | 297 | 449 | 1.51× |
| `avg_cursors_per_step` | 962 | 3 157 | 3.28× |
| `apply_action_calls` | 211 143 | 241 874 | 1.15× |
| `step_fanout_calls` | 218 | **76** | 0.35× |

> **The smoking gun.** HEAD does roughly the same *total* work (`apply_action_calls` ~1.15×) in **fewer,
> fatter steps** (76 vs 218) with a `~4.2–4.7×` larger *concurrent* frontier. Crucially, the number of
> *distinct* TomitaKeys at peak rose only `297 → 449` (1.51×), while the *arc count* at peak rose
> `2833 → 11453` (4.04×). So HEAD carries **~25.5 arcs per distinct TomitaKey** (11453/449) versus baseline's
> **~9.5** (2833/297). The redundancy roughly *tripled*. The extra arcs are the same configurations re-derived
> along distinct fork lineages.

### 3.3 Per-axis no-merge breakdown (the pinpoint)

The classifier recorded, on every arc that landed on an existing TomitaKey bucket but **failed to merge with
any existing arc**, which axis differed. For the **VAR depth 3** control (`put(put(put(map(),a,a),a,a),a,a)`):
**120 118 no-merges, 0 merges**.

| Axis | differs in | % of no-merges | interpretation |
|---|---:|---:|---|
| `weight_rule_idx` (triple) | 114 876 | **95.6 %** | **dominant blocker — genuine weight provenance** |
| `visited_proj_descriptors` | 63 838 | 53.1 % | cross-cat projection cycle-defense `w` (genuine) |
| `sppf_stack_id` | 27 638 | 23.0 % | GLL `w` progress (genuine; *not* restored on fn-call path) |
| `cohort_origin` | 12 380 | 10.3 % | dispatch-key provenance (genuine) |
| `incoming_edge_stack_id` | **0** | **0.0 %** | **never the divergence** — PathTreeArena hash-conses it |
| `lex_fork_path.last()` | 0 | 0.0 % | (VAR is single-lex; nonzero only in NUM — §3.5) |
| `binder_scope_marks` `ptr_eq` | 120 118 | 100 % | **but 100 % content-identical (`ptr_diff_content_eq` = 120 118)** |
| `optional_scope_marks` `ptr_eq` | 120 118 | 100 % | **but 100 % content-identical (`ptr_diff_content_eq` = 120 118)** |
| `recovery_deltas` / `visited_dispatch` / `visited_recovery` / arena content | 0 | 0.0 % | not the driver |

> **WHY-no-reconvergence pinpoint (Direction 1 framing refuted, the genuine driver isolated).**
>
> 1. **The brief's hypothesised redundant axis — `incoming_edge_stack` — is NOT the divergence (0 / 120 118).**
>    The GSS-pushed fork frames *do* push a `CrossCatProjection` edge per arm, but `EdgeStackId` is
>    arena-interned (hash-consed by `PathTreeArena`), so sibling arms that push the *same* edge sequence get
>    the *same* `incoming_edge_stack_id`. There is **no false `Arc` divergence on the return-lineage edge
>    stack** to relax. (This is the opposite of the rhocalc case, where the `sppf_collection_arena` `Arc`
>    *was* a 100 % false divergence.)
> 2. **The only false-divergence axes are the scope-mark `Arc` pointers** (`binder_scope_marks`,
>    `optional_scope_marks`): they differ by pointer in 100 % of no-merges but are *content-identical* in 100 %
>    of cases. Relaxing them to content-equality is independently sound (cf. rhocalc Change A) **but is inert
>    here**: even with content-equality, only **1.1 %** of no-merges would merge (`content_merge_available =
>    1338 / 120 118`), because the **weight triple still differs**.
> 3. **The dominant *genuine* blocker is the `LexicographicWeight` provenance triple** (`weight_rule_idx`
>    differs in 95.6 %). This is exactly the residual that `rhocalc-collection-fork-explosion.md` §8.2 left
>    out of scope. It is **not** a false divergence: the triple is the lex-min tiebreak evidence that selects
>    the winning derivation, left-projected (sticky) along each fork lineage by `⊗` (`lex_weight.rs:418`).

### 3.4 The decisive decomposition (why Direction 1 is unavailable and Direction 2 is the fix)

The classifier further decomposed the **same-config** redundancy — no-merges where *every* observable axis
matches an existing arc *except* `(sppf_stack_id, weight-triple)`. "Same config" =
`(incoming_edge_stack, cohort_origin, lex_fork_last)` equal **and** all heavy fields content-equal:

| Decomposition (VAR depth 3) | count | % of no-merges |
|---|---:|---:|
| `same_config_diff_weight_or_stack` (collapsible in single-result) | 88 004 | **73.3 %** |
| └ same config, **sppf_stack_id equal**, weight triple differs (pure weight) | 65 504 | 54.5 % |
| └ same config, sppf_stack_id differs, weight triple equal (pure stack) | 10 580 | 8.8 % |
| └ same config, sppf_stack_id differs, weight triple differs (both) | 11 740 | 9.8 % |

For **NUM depth 3** the concentration is even sharper: `same_config_diff_weight_or_stack = 111 138` of
300 800 no-merges, of which **111 062 (99.9 %)** are *same config, identical `sppf_stack_id`, weight-triple-only*.

> **Conclusion of the pinpoint.** A large majority of the redundant arcs (73 % VAR, ~37 % of *all* NUM
> no-merges) are at the **identical observable WPDA configuration** — same TomitaKey, same `sppf_stack_id`,
> same `incoming_edge_stack`, same `cohort_origin`, content-equal heavy fields — and differ **only** in the
> weight provenance triple (and, for a minority, in a `sppf_stack_id` that itself reflects a different but
> *non-winning* lineage). These arcs are kept apart *solely by weight evidence that only matters when there
> is more than one result to choose between*. **In single-result demand mode there is exactly one result**:
> the min-weight winner. Every arc at the same config whose weight is provably dominated **cannot become the
> winner**, so subsuming it is result-preserving.
>
> Direction 1 ("merge a redundant return-lineage axis for *all* callers") is therefore **not available** here
> — the only relaxable false-divergence axis (scope-mark `Arc`s) is inert, and the load-bearing axis (weight
> triple) is *genuine* multi-result evidence that the ambiguity-preservation mandate forbids collapsing for
> multi-result callers.

### 3.5 Effectiveness ceiling for Direction 2 (peak post-merge config-classes)

The probe also measured, at the **peak post-merge** live frontier, the number of distinct **config-classes** —
`(node, pos, inner_state, sppf_stack_id, incoming_edge_stack, collection_depth)`, i.e. *keeping* every genuine
GLR/GLL configuration axis (including `sppf_stack_id` and the edge stack) and dropping **only** the weight
triple. This is the floor a sound single-result subsumption can reach:

| VAR depth 3 | NUM depth 3 |
|---|---|
| peak_total_cursors = **5 409** | peak_total_cursors = **12 370** |
| config_classes_at_peak = **746** | config_classes_at_peak = **306** |
| subsume_ratio = **0.138 (7.25× reduction)** | subsume_ratio = **0.025 (40× reduction)** |

> **A single-result subsumption to the lex-min representative per config-class would cut the peak frontier
> ~7× (VAR) to ~40× (NUM)**, recovering and *exceeding* the baseline's frontier — while preserving every
> genuine configuration distinction (`sppf_stack_id`, edge stack, etc. are *kept* in the class key, so the
> chained-output `@a!(Nil)!(Nil)` distinction is untouched — §4.4).

### 3.6 The fan-out switch (regression provenance)

The `30acf6de` series ("preserve ambiguity and runtime evidence") changed the cross-cat fan-out. The two
helpers coexist in HEAD:

| HEAD `parent_frame_with_pushed_fork_branch` (`wpda_walker.rs:21777`) | baseline `parent_frame_with_fork_metadata` (`wpda_walker.rs:21807`) |
|---|---|
| calls `allocate_uncached_push_child` (`:21682`) | `let mut frame = parent.clone();` |
| builds a **fresh** `BranchCursor`, runs `emit_push_side_effects` + `cursor_gss_push_with_kind` with a `CrossCatProjection` edge | appends the stamp; **no** GSS push, **no** fresh cursor |
| used at the `CrossCatDelegate` cohort sites: `InflightCollision` return_frame (`:21484`), `ResolvedHit` synthetic_member (`:21576`), `ResolvedHit` future_member (`:21613`) | used at the `CrossCatLhs` EP-P1 synchronous-consume / park sites (`:21350`, `:21401`) |

The `30acf6de` diff (`macros/src/gen/runtime/wpda_codegen/forks.rs`) added the `CrossCatLhs` lex-alt fork arm
and changed `inner_cur_bp: 0` → `inner_cur_bp: *cur_bp`, and routed the `CrossCatDelegate` cohort members
through the GSS-pushing frame. The baseline carries the *same* `merge_disambiguator` tuple and the *same*
weight machinery — the only structural difference is that the metadata frame **shares the parent's `Arc`s and
pushes no per-arm GSS return lineage**, so the per-argument cohort re-converged after each level; the
GSS-pushed frame forces a distinct fresh cursor whose **weight triple stays separated** through the cohort
revive, so it never re-converges.

### 3.7 Cross-product vs additive sharing (diagram)

```
WEIGHT-TRIPLE CROSS-PRODUCT (cursor frontier, HEAD)       ADDITIVE PACKED SHARING (SPPF, already correct)
─────────────────────────────────────────────────        ──────────────────────────────────────────────

  put-arg level k        put-arg level k+1                      Map Symbol [lo..hi]   ← ONE Symbol id per span
  ┌──────────────┐       ┌──────────────┐                            │
  │ ProcMap   t₀ │──┐ ┌──│ ProcMap   t₀ │   each (t_i)          ┌────┼────┐
  │ GetMap    t₁ │──┼─┼──│ GetMap    t₁ │   cross-cat arm is    pk  pk   pk      ← PutMap/GetMap/… packings,
  │ ProcInt   t₂ │──┼─┼──│ ProcInt   t₂ │   a SEPARATE cursor   │   │    │           weights ⊕-aggregated
  │ VarProc   t₃ │──┘ └──│ VarProc   t₃ │   arc (distinct       arg arg  arg     ← child Symbols (shared)
  │   …  (≈d arms)│       │   …          │   weight triple tᵢ)    = O(rules · positions) forest nodes
  └──────────────┘       └──────────────┘
        d           ×          d         …… ×d per further level
                = dᴺ arcs at the SAME TomitaKey         The SPPF already collapses the d arms to ⊕-summed
                  (probe: 25.5 arcs / TomitaKey)        packings under one Symbol. The leak is purely in
                                                        the cursor frontier's weight-separated bookkeeping.
```

The fix (§4) makes the *single-result* frontier mirror the right-hand side: per-config weight-separated arcs
collapse to the lex-min representative, so the frontier re-converges to the config-class count (746 for VAR
depth 3, not 5409).

---

## 4. Recommended design — Direction 2: single-result demand-mode weight-dominance subsumption

**Idea.** `Cat::parse` (the failing test's entry) is *single-result*: the facade realizes
`min_by(|(_, a), (_, b)| a.cmp(b))` over a finite raw-probe of the accepted root
(`facade.rs:142–149`). A cursor at the **same observable configuration** as another, whose accumulated weight
is **provably dominated** under the idempotent `LexicographicWeight` order, can **never** become the
min-weight winner — so for the single-result path it is **dead weight** and may be subsumed **without changing
the result**. The deleted M7c `subsume_lex_dominated_cursors` (`wpda_walker.rs:16993` comment) was forbidden
because it pruned *mid-pipeline for all callers*; the ambiguity-preservation mandate
(`feedback_never_disambiguate_early.md`) protects the cursors a *multi-result* caller wants. **Gating the
subsumption strictly to single-result demand mode removes exactly that objection** — in demand mode the caller
has asked for one min-weight result, so the pruned cursors are *ruled out by weight evidence*, which the
mandate explicitly permits ("Evidence-based rule-out IS fine").

This is **frontier pruning gated by demand**, not a fan-out rewrite and not a merge-axis relaxation. It leaves
the SPPF, the GSS, the fan-out, and the `merge_disambiguator` **untouched**, and it leaves the multi-result
(`_all`/`_prefix`/bounding-mode) path **byte-identical**.

### 4.1 The dominance predicate

Define the **config key** of a cursor (the genuine GLR/GLL configuration, *excluding* the weight triple):

```
ConfigKey(c) = ( c.node,                    // GSS tip (Symbol identity)
                 c.pos,                      // input position
                 c.inner_state,             // WPDA control state
                 c.sppf_stack_id,           // GLL working-stack progress  w   ── KEPT (genuine)
                 c.incoming_edge_stack_id,   // GSS return-edge stack            ── KEPT (genuine)
                 c.collection_stack_depth,   // collection nesting
                 c.cohort_origin,            // dispatch-key provenance          ── KEPT (genuine)
                 c.visited_proj_descriptors, // cross-cat cycle-defense w        ── KEPT (genuine)
                 c.visited_dispatch, c.visited_recovery,
                 c.recovery_deltas (Arc-id), c.lex_fork_path.last() )
```

`ConfigKey` keeps **every** axis the `merge_disambiguator` keeps **except** the three weight-triple
components `(lex_alt_idx, src_idx, rule_idx)`. The heavy `Arc` fields (`binder_scope_marks`,
`optional_scope_marks`, `sppf_collection_arena`) participate **by content** (they are content-equal across the
redundant arcs — §3.3 — so this is exact, not a relaxation).

**Subsumption (single-result demand mode only):** within a group of cursors sharing a `ConfigKey`, keep only
the cursor with the **minimum** `weight` under `LexicographicWeight::lex_cmp`; drop the rest. Formally, drop
cursor `c` if there exists a sibling `s` with `ConfigKey(s) == ConfigKey(c)` and
`s.weight.lex_cmp(c.weight) ∈ {Less, Equal}` (and `s` is not itself dropped — keep the first/min).

Ties (`Equal`): keeping either is result-stable (the realized term is selected by the SPPF `weight_sum`, which
already `⊕`-dedups identical packings — §4.2). Keep the lex-first deterministically.

### 4.2 Why the realized result is unchanged (the core soundness lemma)

The single-result facade returns `min_by(weight)` over `realize_root_to_terms_with_weights(root, cap)`
(`facade.rs:142`). The realized weight of a term is the SPPF Symbol's `weight_sum`, **`⊕`-aggregated over its
packings** (`sppf.rs:733`, `:712`: `weight_sum := weight_sum ⊕ packing.weight`), and `intern_packing`
**`⊕`-dedups identical `(rule_idx, children)` packings** (`sppf.rs:573–581`). Two facts make subsumption
result-preserving:

**(L1) Dominance is invariant under common continuation.** Let `c` and `s` share a `ConfigKey` with
`s.weight ≤ c.weight` (lex). Because the two cursors are at the *same configuration*, the engine's step
function — pure of cursor state at every dispatch site (the `TomitaShell` soundness note,
`tomita_frontier.rs:63`) — produces the **same sequence of step actions and the same per-step weight
increments** for both. Extending each weight along any common continuation path `p` is `w ⊗ w_p`, where
`⊗` does **tropical-sum on the primary and left-projection on the triple** (`lex_weight.rs:418`). Hence:

```
(s.weight ⊗ w_p).primary = s.primary + p.primary  ≤  c.primary + p.primary = (c.weight ⊗ w_p).primary
(s.weight ⊗ w_p).triple  = s.triple   (left-projected — unchanged) ,  (c.weight ⊗ w_p).triple = c.triple
```

so `lex_cmp(s ⊗ w_p, c ⊗ w_p) = lex_cmp(s, c) ∈ {Less, Equal}` — **the order is preserved exactly** (primary
gets the *same* increment; triples are each left-projected and unchanged). Therefore `c` (and every descendant
of `c`) can **never** out-rank `s` (or the corresponding descendant of `s`) at any later configuration,
including any accepting root. Dropping `c` cannot remove the eventual winner.

> Proof of the increment-equality step: `c` and `s` have identical `ConfigKey`, so identical `inner_state`,
> `node`, `pos`, `sppf_stack_id`, edge stack, etc. The next `WpdaStepAction` is a function of the
> configuration only (engine purity); the `ForkBranch.weight` / rule cost applied by `⊗` depends only on the
> rule fired, which is the same. By induction over `p`, the accumulated `p.primary` is identical for both. ∎

**(L2) No SPPF packing is lost.** For the *surviving* min-weight cursor `s` at a config, every packing that
`c` would have interned (a function of the config, by purity) is interned by `s` instead, and `intern_packing`
`⊕`-aggregates its weight into the Symbol's `weight_sum`. The Goodman-style `weight_sum` is therefore the
**same lattice element** whether or not `c` was dropped: it is the `⊕` over the *set* of distinct packings,
and `c` contributes no packing that `s` does not. (Where `c`'s lineage had a strictly-larger weight, its
contribution to `weight_sum` via `⊕` = lex-min is *absorbed* anyway — `a ⊕ b = b` when `b < a`.) Hence
`realize_root_to_terms_with_weights` returns the identical min-weight term. ∎

> **Net:** L1 says the dropped cursors can never win; L2 says dropping them cannot change the SPPF the winner
> is realized from. Single-result `min_by(weight)` is therefore **invariant** under the subsumption.

### 4.3 Why it is mandate-compliant (`feedback_never_disambiguate_early`)

The mandate forbids "weight-based 'pick one' combinators … mid-pipeline" because they "commit to one
interpretation prematurely; when that interpretation hits a downstream issue … the parse fails even though
another interpretation would have succeeded." The decisive distinction:

- The forbidden M7c pruning dropped weight-dominated cursors **unconditionally, for all callers**, including
  the `_all`/`_prefix` ambiguity-returning APIs — so it could drop a cursor a *multi-result* caller wanted.
- This design drops a cursor **only** (a) in single-result demand mode, where the caller has asked for the
  one min-weight result, **and** (b) when a *same-configuration* sibling provably dominates it. Condition (b)
  is **evidence**: by L1 the dominated cursor *cannot* reach an accepting root that out-ranks the survivor,
  for *any* continuation — it is ruled out by the weight semiring's order, not by a heuristic guess. The
  mandate explicitly permits "a precondition encoded in a rule rejects … dies legitimately"; weight-dominance
  at an identical configuration is precisely such a provable rule-out for the demand the caller stated.
- It does **not** drop genuinely-different configurations. Cursors that differ in `sppf_stack_id`, edge stack,
  `cohort_origin`, `visited_proj_descriptors`, or `lex_fork_last` are **different configs** and are **kept**
  (they are in `ConfigKey`). Only weight-separated cursors at the *same* config are collapsed.

The `_all`/`_prefix`/`_with_source_and_bounding_mode` facades route through `run_to_end_of_input_env_aware`
(`facade.rs:697`, `:178`) — the **full, non-demand** driver — and so never set the demand flag (§4.5). Their
behaviour is unchanged, preserving the mandate for every caller that wants ambiguity. The "anti-pattern"
the mandate calls out ("Use lex-min weights to break ties between WPDS-Fork branches — collapses too early")
applies to *forcing* a single result on a *multi-result* caller; here the caller *is* single-result by
construction, and lex-min is being used for exactly its sanctioned role ("Lex-min weights are FOR TIEBREAK
ORDERING WHEN DISAMBIGUATION IS FORCED").

### 4.4 Soundness of the specific hazards (S-clauses)

**(S1) `@a!(Nil)!(Nil)` chained output is preserved.** A chained send produces two genuinely distinct parses
that the SPPF distinguishes by **span/structure** and the cursor frontier keeps apart by **`sppf_stack_id`**
(the GLL `w` discriminant — `wpda_walker.rs:4122-4145`). `ConfigKey` **includes `sppf_stack_id`**, so the two
readings are in **different config-classes** and are **never** subsumed against each other. (The probe
corroborates the orthogonality from the other side: on the calculator fn-call path, `sppf_stack_id` is *not*
restored by a splice — it differs in 23 % of no-merges and is a *kept* axis here; the only arcs collapsed are
those that share it.) Single-result `Cat::parse` still selects the min-weight chained reading exactly as today.

**(S2) rhocalc comm / cross-cat correctness is preserved.** rhocalc `parse` for process/binder/guarded
categories is single-result, so it would *use* the subsumption — but every distinction those parses rely on
(`sppf_stack_id`, `incoming_edge_stack`, `cohort_origin`, `visited_proj_descriptors`, `lex_fork_last`,
content of `binder_scope_marks`) is **in `ConfigKey`** and therefore preserved. The subsumption only collapses
weight-separated cursors at the *identical* config; by L1/L2 the realized term (e.g. the lex-min comm/extrusion
derivation) is unchanged. Gate: `rhocalc_tests` + `gen_rhocalc_*` + `wpda_parity_rhocalc_collections` (§6.2).

**(S3) The committed rhocalc Cluster-D collection fix stays intact.** That fix (arena content-equality at
`tomita_frontier.rs:739` + `lex_fork_path` clear in `emit_splice_into_collection`) operates on the
**merge gate** for collection-element lexical siblings and is **orthogonal** to this design, which adds a
**separate demand-gated pruning pass** and touches neither `register_arc_with_aggregation` nor
`emit_splice_into_collection`. Both compose: Cluster-D collapses lexical siblings into one merged arc *before*
the pruning pass even runs; the pruning pass then collapses any weight-separated same-config residue in the
single-result path. The `lazy_lex_equivalence` rho-collection gate (the Cluster-D acceptance target) must stay
< 10 s (§6.1).

**(S4) The deep-nesting linear-time fix stays intact.** `d84b4df4` (edge-stack memoisation for linear-time
deep nesting) operates on `incoming_edge_stack_id` interning, which `ConfigKey` *keeps*; the subsumption never
merges across distinct edge stacks. No interaction.

**(S5) The `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` invariant
(`tomita_frontier.rs:1150`) is untouched.** This design does **not** modify `merge_disambiguator` or
`register_arc_with_aggregation` — the merge gate's comparison is byte-identical. The pruning is a *separate*
pass over the live frontier, gated by demand. The unit test continues to pass unchanged. (Likewise
`arc_merge_disambiguator_distinguishes_lex_provenance` / `_sppf_stack` / `_incoming_edge_stack` /
`_lex_fork_stamp` at `:1087`,`:1095`,`:1103`,`:1131`.)

**(S6) No new mis-parse / sub-multiset ghost.** The subsumption never *creates* a cursor, never alters an SPPF
packing, and never merges different configurations. It only deletes a live cursor that is provably non-winning
for the stated single-result demand (L1). It cannot change *which* inputs are accepted (an accepted root for
`c` implies — by L1, with the accepting continuation as `p` — an at-least-as-good accepting root for `s`).

**(S7) Multi-result paths are byte-identical.** Gated strictly on the demand flag (§4.5); `_all`/`_prefix`/
bounding-mode never set it. The exhaustive `run_to_end_of_input_env_aware` retry inside `Cat::parse`'s
`AcceptedWithTrailing` arm (`facade.rs:178`) is single-result too (it ends in `min_by`), so the flag may
remain set across it — sound by the same L1/L2 argument; alternatively scope the flag to the demand driver
only (§4.5, conservative variant).

### 4.5 Mechanism + exact code locations

**(M1) A demand flag on the walker.** Add `single_result_demand: bool` to `WpdaWalker`
(`wpda_walker.rs`, near the existing `bounding_mode` config field). Default `false`. Set it `true` for the
duration of the demand driver:

| Edit | File:line | Change |
|---|---|---|
| field | `prattail/src/wpda_walker.rs` (`WpdaWalker` struct, near `bounding_mode`) | `single_result_demand: bool` (default `false` in all 3 constructors `:4554`,`:4663`,`:4771`) |
| set on demand | `run_to_end_of_input_with_accept_demand` (`:5639`) | set `self.single_result_demand = stop_when_accepting;` at entry (RAII-restore on exit, or leave set — only the demand driver path reads it) |

`run_to_end_of_input` passes `stop_when_accepting = false` (`:5619`) so the multi-result driver clears it;
`run_to_end_of_input_until_accepting` passes `true` (`:5636`) so the single-result facade sets it. The
`_all`/`_prefix` facades call `run_to_end_of_input_env_aware` → `run_to_end_of_input` (the `false` path), so
the flag is `false` there.

**(M2) The subsumption pass.** Add a `fn subsume_weight_dominated_when_single_result(&mut self)` that, when
`self.single_result_demand`, groups the live concrete `branch_cursors` by `ConfigKey` (an `FxHashMap` keyed by
the tuple in §4.1, hashing the `Arc`-content for the heavy fields) and retains per group only the lex-min
cursor (folding dropped weights into the survivor via `⊕` for ESS-fidelity, mirroring the
`register_arc_with_aggregation` weight fold at `tomita_frontier.rs:701`). Cohort frames (`Frame::Cohort`) are
left untouched (they are lazy unresolved evidence, not concrete configs). Call it from `merge_equivalent_cursors`
**after** the existing strict-ConfigKey merge writes back `self.branch_cursors`
(`wpda_walker.rs:16986–16990`) — exactly where the deleted M7c pass used to sit (`:16993`), but now
demand-gated.

| Edit | File:line | Change |
|---|---|---|
| pass | `prattail/src/wpda_walker.rs:16990` (end of `merge_equivalent_cursors`) | call `self.subsume_weight_dominated_when_single_result();` |
| method | `prattail/src/wpda_walker.rs` (new, where M7c was at `:16993`) | the grouped lex-min retain described above |

**(M3) Kill switch (P-series convention).** Gate the pass behind a per-walker env flag read once at
construction (cf. `PRATTAIL_EP_P1`, `wpda_walker.rs:131-149`) — e.g. `PRATTAIL_SR_SUBSUME` (default On) —
so a soundness regression can disable it without reverting the plumbing.

### 4.6 Complexity argument (frontier re-converges to the config-class count)

Let `Fₖ` be the live frontier after the subsumption pass at nesting level `k`, and let `d` be the cross-cat
arm degree (the number of competing `Proc` interpretations, ~constant per grammar).

- **Without the fix:** each `put`-argument level multiplies the live arc count by `d` (the weight triple keeps
  each `(reading₀,…,readingₖ)` prefix distinct). `Fₖ = Θ(dᵏ)` ⇒ super-linear in nesting depth
  (the measured `4.04×` arc-per-step blow-up at depth 4, curve §3.1).
- **With the fix:** after the pass at level `k`, all `d` weight-separated arcs at each config collapse to one
  ⇒ `Fₖ = (#distinct config-classes at level k)`, the **746** floor measured at VAR depth 3 (§3.5), versus
  5 409 without. The transient fan *within* a step is still `≤ d` per config (bounded), so total cursor work
  is `Σₖ O(d · |configs_k|)`. The peak frontier is the config-class count, **not** `dᵏ` — exactly the
  baseline's linear-in-input behaviour, and in fact below it (the baseline metadata-frame re-convergence was
  partial; this is the SPPF-faithful floor).

`O(frontier)` per-step merge/hash cost therefore drops by the `subsume_ratio` (7.25× VAR, 40× NUM), which —
applied to the measured `2.77–3.22×` wall regression — restores the test well under 180 s with a curve no
worse than baseline's. (See §6.1 for the empirical acceptance gate.)

---

## 5. Rejected alternative — Direction 1: general fan-out re-convergence

**Proposal.** Find a redundant *return-lineage* axis on the GSS-pushed fork frame
(`parent_frame_with_pushed_fork_branch`) that the baseline's metadata frame did not carry, and design a sound
global merge/dedup of it — the analog of the rhocalc Change-A/B — without reverting the `30acf6de` fan-out.

**Why it was investigated.** The rhocalc case was fixed *exactly* this way: a 100 %-false-divergence
`sppf_collection_arena` `Arc` pointer was relaxed to content-equality (Change A), and a redundant
`lex_fork_path` sidecar was cleared at splice (Change B). The brief hypothesised the analog here would be the
`incoming_edge_stack` (the GSS push per arm).

**Why it is rejected (probe-refuted).**

1. **The hypothesised axis carries no divergence.** `incoming_edge_stack_id` differs in **0 / 120 118**
   no-merges (§3.3) — `PathTreeArena` already hash-conses the edge stack, so sibling fork arms that push the
   same edge sequence share the same `EdgeStackId`. There is **nothing to relax** on the return-lineage edge
   stack; it is already convergent.
2. **The only false-divergence axes are inert.** The scope-mark `Arc` pointers (`binder_scope_marks`,
   `optional_scope_marks`) *are* 100 % false divergences (content-identical), and relaxing them to
   content-equality is independently sound — **but it merges only 1.1 %** of no-merges
   (`content_merge_available = 1338 / 120 118`), because the weight triple still blocks. Change A alone would
   be *inert* here, exactly as it was reported inert-alone in the rhocalc case (§8.3 of that doc).
3. **The load-bearing axis is genuine, not relaxable for all callers.** The dominant blocker is the
   `LexicographicWeight` provenance triple (95.6 %). Merging on it for *all* callers is precisely the
   ambiguity collapse the mandate forbids — it would discard, from the `_all`/`_prefix` results, derivations
   that differ only by their lex-min tiebreak provenance, which is genuine multi-result evidence. The rhocalc
   document itself drew this exact line (§8.2: the weight triple is "out of scope … it touches the weight
   provenance the `30acf6de` series relies on").
4. **Reverting the fan-out wholesale is also rejected** (the rhocalc §4 verdict applies verbatim): it would
   undo the `30acf6de` soundness commits (`db53e83a`, `ea1dcb6b`, `ddfafc9f` — projection evidence, prefix
   ambiguity, demand-sensitivity) and the design constraint forbids touching them.

**Verdict: reject Direction 1.** There is no sound *global* (all-caller) merge of the load-bearing axis here,
because that axis is genuine multi-result evidence — unlike the rhocalc false-divergence. The redundancy is
real but is only *prune-able under the single-result demand*, which is Direction 2.

> **A note on combination.** The scope-mark content-equality (a real, if inert-alone, false divergence) could
> be added as a *global* `register_arc_with_aggregation` relaxation (mirroring the committed arena
> content-equality at `:739`) — it is independently sound and would shrink the multi-result frontier slightly.
> It is **not** part of the recommended fix because (a) it does not move the single-result curve (the weight
> triple dominates) and (b) it is orthogonal cleanup, not the root-cause fix for the failing test. If desired
> it can land as a separate, independently-verified change. The recommended fix (Direction 2) stands alone.

---

## 6. Verification / test plan

### 6.1 Performance targets (acceptance criteria)

| Metric | Target | How |
|---|---|---|
| `gen_calculator_prop::map_display_parse_roundtrip` | **passes < 180 s** (ideally well under) | `cargo test -p mettail-languages --test gen_calculator_prop map_display_parse_roundtrip` |
| VAR `put`-nest depth 4 peak frontier | `≈ config-class count` (≈746 at depth 3; was 14 215 at depth 4) | `walker-stats` probe (re-add §3 probe before/after) |
| VAR depth-6 wall-time | `≤ baseline` (≤ ~6.3 s debug; was ~20.2 s) | the §3.1 timing probe |
| curve | no worse than baseline's (sub-`dᵏ`) | depths 1..6, before/after |

Iterate with the *small-depth probe* (depths 3–5), **never** the 180 s proptest, per the brief.

### 6.2 Soundness gates that must stay green

| Suite | What it guards | Command |
|---|---|---|
| `prattail` lib (**3 789** tests, incl. the merge invariants `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` `:1150`, `arc_merge_disambiguator_distinguishes_*` `:1087`–`:1131`) | the merge gate is **untouched** (S5) | `cargo nextest run -p mettail-prattail` |
| `gen_calculator_*` (unit / analytical / rewrite / prop) + `calculator_display_projection_tests` + `display_roundtrip_regression_tests` + dangling-else / ternary | calculator parse/eval/roundtrip correctness | `cargo test -p mettail-languages --test gen_calculator_unit` (+ the rest) |
| `rhocalc_tests` + `gen_rhocalc_{unit,analytical,rewrite,prop}` | rhocalc comm / cross-cat (S2) | `cargo test -p mettail-languages --test rhocalc_tests` (+ the `gen_rhocalc_*`) |
| `wpda_parity_rhocalc_collections` | `{}`, `{error}`, `{error\|error}`, `{error\|error\|error}` collection shapes | `cargo test -p mettail-languages --test wpda_parity_rhocalc_collections` |
| `gen_guardedrho_*` (unit / analytical / prop), incl. chained output `@a!(Nil)!(Nil)` (S1) | the `sppf_stack_id` chained-output distinction | `cargo test -p mettail-languages --test gen_guardedrho_unit` |
| `lazy_lex_equivalence` (full corpus, incl. `rho_full_parse_lazy_eq_eager`, `report_nodes_materialized`) | the committed rhocalc Cluster-D fix (S3); lazy ≡ eager | `cargo test -p mettail-languages --test lazy_lex_equivalence` — **must stay < 10 s** |
| full gauntlet (calc-op, edge_case_tests, ledtest, ambient, recovery_accumulation, led_delegation_tests) | no cross-language / committed-fix regression | the standard battery |

### 6.3 New tests to add

- `wpda_walker.rs` unit: `subsume_weight_dominated_keeps_distinct_sppf_stack_arcs` — two cursors with the same
  TomitaKey but different `sppf_stack_id` must **not** be subsumed (S1 guard for `@a!(Nil)!(Nil)`).
- `wpda_walker.rs` unit: `subsume_weight_dominated_collapses_same_config_weight_separated` — two cursors with
  identical `ConfigKey` and `weight.lex_cmp == Less/Greater` collapse to the lex-min in single-result mode.
- `wpda_walker.rs` unit: `subsume_is_noop_when_not_single_result` — with the demand flag `false`, the frontier
  is byte-identical (the `_all` path guard, S7).
- `languages/tests`: `map_nested_putget_is_subquadratic` — parse `put`-nests for depth ∈ {2,4,6,8} under
  `walker-stats` and assert peak frontier `≤ C · (config-class count)` for a small `C` (the re-convergence
  proof). Numeric *and* VAR variants.
- `languages/tests`: parse-result equality — `Map::parse("put(put(map(),a,a),b,b)")` etc. must equal its
  pre-fix term (single-result determinism preserved); add to the existing `map_parse_determinism` family.

### 6.4 Differential check (single-result == previous, multi-result unchanged)

For a battery of nested-fn-call map/proc surfaces, assert `Cat::parse(s)` (single-result) returns the
**identical** `Debug` term and `pos` before/after the fix (L1/L2 empirical confirmation), and assert
`parse_<Cat>_via_wpda_all(s)` returns the **identical** alternative *set* before/after (S7 — the multi-result
path is untouched).

### 6.5 Formal note (optional, recommended)

Extend the evidence-pruning proof family (`CollectionForkEvidence.v` / the evidence-pruning ledger) with a
lemma **`single_result_dominance_preserves_min`**: under `LexicographicWeight` (idempotent `⊕` = lex-min,
`⊗` = tropical-primary + left-projection), if `ConfigKey(s) = ConfigKey(c)` and `s.weight ≤ c.weight`, then for
every common continuation `p`, `s ⊗ p ≤ c ⊗ p`, and the SPPF `weight_sum` is invariant under dropping `c`
(L1 + L2 of §4.2). Zero-admission. This is the machine-checked form of the core soundness lemma and the exact
counterpart the rhocalc fix deferred in its §8.2.

---

## 7. Probe hygiene

All probe instrumentation used to produce §3 was **throwaway** and has been **reverted**:

- `prattail/src/tomita_frontier.rs` — `NoMergeBreakdown` thread-local + per-axis classifier in
  `register_arc_with_aggregation` + peak config-class counters. **Reverted** (`git checkout`).
- `prattail/src/wpda_walker.rs` — peak config-class recorder at the end of `merge_equivalent_cursors`.
  **Reverted** (`git checkout`).
- `languages/tests/zz_probe_map_crosscat.rs` — the timing + stats + breakdown probe test. **Deleted.**
- The same probe test temporarily copied into the read-only baseline worktree `mettail-rust-lexdeleg`.
  **Deleted** (no other change made to that worktree).

The only artifact of this work is this design document. (The repo working tree shows only this file.)

---

## 8. Summary

- **Confirmed root cause:** a GLR cursor-frontier sharing leak — but, unlike the rhocalc lexical case, the
  redundant axis is the **genuine `LexicographicWeight` provenance triple**, not a false-divergence `Arc`.
  The `30acf6de` switch to GSS-pushed cross-cat fork frames keeps each cross-cat arm's weight triple separated
  through the cohort revive, so the per-`Proc`-argument cohort never re-converges and the per-level fan
  multiplies across `put`/`get`/`merge`/`delete` nesting into a super-linear frontier (`4.04×` arc-per-step,
  `2.77–3.22×` wall, depth-dependent).
- **WHY-no-reconvergence pinpoint (probe):** `incoming_edge_stack` is **never** the divergence (0/120 118 —
  hash-consed); the scope-mark `Arc`s are 100 % false divergences but **inert alone** (would merge only 1.1 %);
  the **weight triple** is the dominant blocker (95.6 %), and **73.3 %** of redundant arcs are at the
  **identical observable config** (same `sppf_stack_id` + edge stack + everything else), separated **only** by
  weight. Collapsing same-config weight-separated arcs to the lex-min representative would cut the peak
  frontier **7.25× (VAR) to 40× (NUM)**.
- **Recommended fix (Direction 2):** a **single-result demand-mode** weight-dominance subsumption — a
  demand-gated pruning pass that, only when `Cat::parse`'s accept-stop driver is active, keeps the lex-min
  cursor per `ConfigKey` (which **retains every genuine GLR/GLL axis**, including `sppf_stack_id` and the edge
  stack, and drops **only** the weight triple). Result-preserving by L1 (dominance invariant under common
  continuation, via `⊗` left-projection) + L2 (SPPF `weight_sum` invariant under dropping a dominated cursor).
- **Mandate-compliant:** the pruned cursors are *ruled out by weight evidence for the stated single-result
  demand* (which `feedback_never_disambiguate_early` permits), the multi-result `_all`/`_prefix` path is
  **byte-identical** (it uses the non-demand driver, so the flag is never set), and the `merge_disambiguator`
  / `register_arc_with_aggregation` gate is **untouched** (the §6.2 invariant tests pass unchanged).
- **Preserves the committed fixes:** `@a!(Nil)!(Nil)` (S1, `sppf_stack_id` is a kept axis), rhocalc comm /
  cross-cat (S2), the rhocalc Cluster-D collection fix (S3, orthogonal merge-gate change), the deep-nesting
  linear-time fix (S4, edge stack is a kept axis), and the ambiguity-preservation invariants (S5/S7).
- **Rejected (Direction 1):** general fan-out re-convergence — probe-refuted: the hypothesised redundant axis
  (`incoming_edge_stack`) carries no divergence, the only false-divergence axes are inert, and the
  load-bearing axis (weight triple) is genuine multi-result evidence that cannot be merged for all callers.

### 8.1 Refinement — L1 order is preserved as `≤`, not strict `<`

The §4.2 (L1) statement "the order is preserved exactly" is sharpened to: along any common continuation `p`,
`lex_cmp(s ⊗ w_p, c ⊗ w_p) = lex_cmp(s, c) ∈ {Less, Equal}` — the order is preserved as **`≤`** (a `Less` may
*degrade* to `Equal`, never *invert* to `Greater`). The degradation channel is `LexicographicWeight::times`'s
`is_one` short-circuit (`lex_weight.rs:418`): while a cursor's weight is still the multiplicative identity
(`primary == 0`, the freshly-seeded prefix), `1.times(other) = other`, so the *left-projection* of the triple
has not yet taken effect and the triple is whatever the *right* operand carries. Two consequences, both
sound for subsumption:

1. **Left-projection holds for NON-identity cursors.** Once a cursor has fired at least one real production
   (`primary > 0`), `times` takes the `else` arm and *freezes* the triple at the receiver's value — it is
   **monotone-sticky** thereafter (every later `⊗` left-projects the already-frozen triple). So for the cursors
   the subsumption actually compares — live frontier cursors that have made progress — the triple is constant
   along `p` and L1's triple-equality step is exact.
2. **The identity edge case cannot invert the order.** If `s` is still at identity, `s ⊗ w_p = w_p` for both
   the survivor and the dropped cursor's continuation, so they share the continuation's triple and differ only
   in `primary` (which gets the *same* increment) — the relation can only stay `Less` or collapse to `Equal`,
   never invert. Since single-result `min_by` keeps *any* lex-min representative and ties are result-stable
   (the SPPF `weight_sum` `⊕`-dedups identical packings — L2), a `Less → Equal` degradation is harmless: the
   survivor is still a (or *the*) min-weight winner.

Net: the precise invariant is **`s.weight ≤ c.weight` ⇒ `(s ⊗ p) ≤ (c ⊗ p)` for all common `p`**, with
equality reachable but inversion impossible — exactly what `min_by`-preservation requires.

### 8.2 Refinement — the subsumption is INVISIBLE under `PRATTAIL_TRACE`

`PRATTAIL_TRACE` (the `EnvTracingConsumer`, active when the env var is set) reroutes even the *single-result*
`Cat::parse` facade through the **exhaustive** driver so diagnostic output stays complete:
`run_to_end_of_input_until_accepting_env_aware` checks `EnvTracingConsumer::from_env().is_active()` and, when
tracing, delegates to `run_to_end_of_input_env_aware` → `run_to_end_of_input` (the `stop_when_accepting =
false` path) instead of `run_to_end_of_input_until_accepting` (`wpda_walker.rs`, the two `_env_aware`
drivers). That `false` path leaves `single_result_demand == false`, so
`subsume_weight_dominated_when_single_result` is a **no-op while tracing**. The subsumption therefore **cannot
be observed in a `PRATTAIL_TRACE` dump** — and, separately, the per-trace parse can diverge from the
non-traced parse (the longstanding `prattail-trace-perturbs-parse` Heisenbug). **Debug the subsumption with
`walker-stats`** (`PRATTAIL_WALKER_STATS=1`, feature `walker-stats`): the `cursors_dropped_via_sr_subsume`
counter is non-zero exactly when the pass fires; the trace is not a valid window onto it.

### 8.3 Refinement — the `ConfigKey` reconciled to the ACTUAL existing key + by-content heavy fields

§4.1 framed the subsumption key against an idealised `ConfigKey`. The implementation reconciles it to the
**actual** existing strict `ConfigKey` (`wpda_walker.rs`, the `struct ConfigKey` used by
`merge_equivalent_cursors`). The implemented `SubsumeConfigKey` is the strict key with the **three
weight-triple components removed** and three by-content additions:

| Axis | In strict `ConfigKey`? | In `SubsumeConfigKey`? | Treatment |
|---|---|---|---|
| `state` (`inner_state`), `node`, `pos` | ✓ | ✓ | scalar (Hash) |
| `incoming_edge` (`arena.top`), `incoming_edge_stack` (id) | ✓ | ✓ | scalar (Hash) |
| `collection_depth`, `cohort_origin` (`equiv()`) | ✓ | ✓ | scalar (Hash) |
| `sppf_top` (`arena.top`), `sppf_stack` (id) | ✓ | ✓ | scalar (Hash) |
| `lex_fork_stamp` (`lex_fork_path.last()`) | ✓ | ✓ | scalar (Hash) |
| `lex_alt_idx`, `weight_src_idx`, `weight_rule_idx` | ✓ | ✗ **(dropped)** | the weight triple — the *only* drop |
| `last_action_output_cat`, `recovery_depth` | ✗ | ✓ | scalar (Hash), required equal (conservative) |
| `recovery_deltas` | ✗ | ✓ | **Arc-id** (pointer identity) |
| `binder_scope_marks`, `optional_scope_marks` | ✗ | ✓ | **by content** (Phase-2 `==`) |
| `sppf_collection_arena`, `collection_sep_counts` | ✗ | ✓ | **by content** (`ptr_eq` fast path → `==`) |
| `visited_proj_descriptors`, `visited_dispatch`, `visited_recovery` | ✗ | ✓ | **by content** (Phase-2 `==`) |
| `pending_packing_weight` | ✗ | ✓ | **by content** (Phase-2 `==`) |

Because `im::OrdSet` and the generic weight `W` are not necessarily `Hash`, the key is realised as a
**two-phase grouping**: Phase 1 buckets by the Hash-able scalar axes (`SubsumeConfigKey`); Phase 2 partitions
each bucket by exact equality of the heavy fields (`heavy_fields_equal`). The composition reproduces the §4.1
key **exactly** (it never merges across any heavy-field difference) without requiring `Hash` on
`im::OrdSet`/`W`. Note the `SubsumeConfigKey` is a *refinement-or-equal* of the strict key on every retained
axis, and the pass runs **after** the strict merge — so the only cursors that can still share a
`SubsumeConfigKey` are ones that differed solely in the weight triple (or in a heavy field this key
additionally requires equal), which is precisely the §3.3 redundancy.

### 8.4 Refinement — why this differs from the deleted M7c on BOTH counts

The deleted M7c `subsume_lex_dominated_cursors` was unsound on **two independent** counts; Direction 2 differs
on **both**:

1. **All-modes vs demand-gated.** M7c pruned weight-dominated cursors **unconditionally, for every caller**,
   including the `_all`/`_prefix` ambiguity-returning APIs — so it could drop a derivation a *multi-result*
   caller wanted (the mandate violation). Direction 2 fires **only** when `single_result_demand == true` (the
   `Cat::parse` accept-stop driver), which the multi-result facades never set; their frontier is
   byte-identical.
2. **A lossy relaxed key vs the full edge stack.** M7c additionally used a **relaxed** dominance key that
   dropped `incoming_edge_stack` — so it could collapse two cursors with *distinct return lineages* (different
   next-pop targets), a structural mis-merge independent of the mode issue. `SubsumeConfigKey` **keeps the full
   `incoming_edge_stack`** (and `sppf_stack`, `sppf_top`, `visited_proj_descriptors`, `cohort_origin`,
   `lex_fork_stamp`); it drops **only** the three weight-triple axes. It therefore cannot make the structural
   mis-merge M7c's relaxed key allowed.

Direction 2 is sound precisely because it repairs *both* defects: it is evidence-gated to the single-result
demand (count 1) and it preserves every genuine GLR/GLL configuration axis (count 2).

### 8.5 Implemented mechanism (code map)

| Component | Location | Summary |
|---|---|---|
| **M1** demand flag | `prattail/src/wpda_walker.rs`: `WpdaWalker.single_result_demand` (near `bounding_mode`); set at the entry of `run_to_end_of_input_with_accept_demand` to `stop_when_accepting`; default `false` in all 3 constructors | `true` only while the single-result accept-stop driver runs |
| **M2** the pass | `prattail/src/wpda_walker.rs`: `fn subsume_weight_dominated_when_single_result`, called at the end of `merge_equivalent_cursors` (where M7c sat) after the strict merge writes back `self.branch_cursors` | two-phase group by `SubsumeConfigKey` + `heavy_fields_equal`; retain lex-min via the semiring `⊕` (= lex-min), `⊕`-fold dropped weights + `pending_packing_weight` + p5 step counts; `Frame::Cohort` untouched; `FxHashMap` preallocated to frontier size |
| **M3** kill switch | `prattail/src/wpda_walker.rs`: `enum SrSubsumeMode` + `WpdaWalker.sr_subsume_mode`, read once from `PRATTAIL_SR_SUBSUME` at construction (default `On`; `0`/`off` ⇒ `Off`) | gates the pass; `PRATTAIL_SR_SUBSUME=0` reverts it without touching the plumbing |
| key + heavy-eq | `prattail/src/wpda_walker.rs`: `struct SubsumeConfigKey` + `SubsumeConfigKey::from_cursor` + `fn heavy_fields_equal` (next to `struct ConfigKey`) | the §8.3 two-phase config key |
| stats counter | `prattail/src/walker_stats.rs`: `WalkerStats.cursors_dropped_via_sr_subsume` (+ Display line) | observability (the §8.2 debug channel) |
| unit tests | `prattail/src/wpda_walker.rs` `mod tests`: `subsume_weight_dominated_keeps_distinct_sppf_stack_arcs`, `subsume_weight_dominated_collapses_same_config_weight_separated`, `subsume_is_noop_when_not_single_result`, `subsume_is_noop_when_kill_switch_off`, `subsume_keeps_distinct_visited_proj_descriptors`, `subsume_leaves_cohort_frames_untouched` | S1/core/S7/M3/heavy-field/cohort guards |
| `_all` gate guard | `languages/tests/calculator.rs`: `all_facade_preserves_ambiguity_with_sr_subsume_default_on` | the multi-result `_all` facade still surfaces both `-3!` readings with subsumption default-ON |

### 8.6 Implementation status: IMPLEMENTED + verified (commit pending)

Implemented exactly as designed (Direction 2, §4). BACKEND-only: no grammar / regex / spec change; no change
to `register_arc_with_aggregation` / `merge_disambiguator` / `emit_splice_into_collection`; no revert of any
committed fix. Self-contained behind the `PRATTAIL_SR_SUBSUME` kill switch (default `On`).

**Performance (acceptance criterion §6.1) — direct ON/OFF attribution.** `map_display_parse_roundtrip` (100
cases, `arb_map(3)`) was run back-to-back under the SAME harness (`cargo nextest`, debug build) with
subsumption ON (default) then OFF (`PRATTAIL_SR_SUBSUME=0`), with the kill switch as the ONLY variable:

| Run | `PRATTAIL_SR_SUBSUME` | Result | Test wall |
|---|---|---|---|
| ON (default) — lightly loaded | unset ⇒ `On` | **passed** (nextest "1 slow") | **~93 s** |
| ON (default) — back-to-back attribution run | unset ⇒ `On` | **passed** (nextest "1 slow") | **168.6 s** |
| OFF — back-to-back attribution run | `0` ⇒ `Off` | **timed out** (nextest terminate-after, 180 s) | **> 180 s** (≡ pre-fix behavior) |

The OFF arm **reproduces the original timeout** (the bug); the ON arm **passes** — so the speedup is
unambiguously attributable to `subsume_weight_dominated_when_single_result`, not to environment. (Both
attribution runs were on a contended machine — load avg ~6–12 — which inflates absolute wall time toward the
180 s cap; the OFF run was, if anything, slightly *less* loaded than the ON run yet still timed out. On a
lightly-loaded machine the ON arm completes in ~93 s; the §3 "~40 s" figure was the focused depth-3..5
throwaway probe. The acceptance bar — the proptest passing under 180 s with the fix — is met, and the bug
recurs the instant the fix is switched off.)

| S3 gate | After (default ON) | Verdict |
|---|---|---|
| `lazy_lex_equivalence` slowest test | **1.75 s** (≪ 10 s) | ✓ |

**ON/OFF differential (soundness gate §6.2 / §6.4).** Default (`PRATTAIL_SR_SUBSUME` unset ⇒ `On`) vs
`PRATTAIL_SR_SUBSUME=0` (`Off`) produced **byte-identical pass-sets** (identical test-name sets, identical
pass/fail counts, zero failures) on every required suite:

| Suite | ON | OFF | Result |
|---|---|---|---|
| `mettail-prattail` (lib, incl. the §6.2 merge-invariant tests + the 6 new subsumption tests) | 3795 passed / 0 failed | 3795 passed / 0 failed | **identical** |
| `mettail-languages` differential set (`gen_calculator_{unit,analytical,rewrite}`, `rhocalc_tests`, `gen_rhocalc_{unit,analytical,rewrite}`, `wpda_parity_rhocalc_collections`, `lazy_lex_equivalence`, `calculator`, `calculator_display_projection_tests`, `display_roundtrip_regression_tests`, `led_delegation_tests`, `edge_case_tests`, `recovery_accumulation`, `roundtrip_tests`, `gen_guardedrho_unit`, `test_deep_parens_100000`, `test_deep_unary_neg_10000`) | 1010 passed / 0 failed | 1010 passed / 0 failed | **identical** |

No ON/OFF divergence on any non-map test ⇒ no soundness regression (the mandate: any such divergence would be
a soundness bug). The multi-result `_all` path is byte-identical ON vs OFF (gate disjointness, S7 — confirmed
by `all_facade_preserves_ambiguity_with_sr_subsume_default_on` passing in both arms, and by the differential
above).

**Other gates.** `proc_display_parse_roundtrip` / `name_display_parse_roundtrip` (+ the strong-roundtrip
variants) green on two independent random runs (§6 step 4). The 6 new prattail unit tests + the new `_all`
multiplicity guard all pass with subsumption default-ON. `cargo build -p mettail-languages` is clean (the only
warnings are pre-existing grammar lints + machine-generated `dovetail_report.rs` parenthesis warnings,
unrelated to this change).
