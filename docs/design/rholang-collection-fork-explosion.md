# Rholang Collection Fork Explosion — Lexical-Ambiguity Cursor Cross-Product

**Target:** branch `feature/wfst-architecture`, baseline HEAD `d84b4df4`.
**Status:** IMPLEMENTED + verified (2026-06-20). Root-cause confirmed by probe; design red-teamed to convergence; the clear-all variant of Change B was implemented (not the watermark stack — see §8). See §8 for the convergence outcome, the corrected `O(N²)` complexity, and verification results.
**Scope:** WPDA walker frontier representation (`prattail/src/wpda_walker.rs`, `prattail/src/tomita_frontier.rs`). No grammar/regex/spec change.

---

## 1. Problem

Parsing the rholang parallel-composition collection `{0 | 1 | … | 19}` (20 numeric elements) is
catastrophically slow on HEAD `d84b4df4`. The lazy/eager equivalence gate
(`languages/tests/lazy_lex_equivalence.rs::rho_full_parse_lazy_eq_eager` and `report_nodes_materialized`,
whose `RHO_FULL` corpus contains exactly this input) does not complete inside its 180 s test budget
(it finishes near 250 s). The baseline `b781d754` parsed the same input in roughly linear time
(~2.6 ms per parse, debug, measured below).

The cost is super-linear in the element count `N`. Measured peak cursor frontier scales as `~O(N⁴)`
and the per-cursor work (`apply_action` calls) scales as `~O(N⁶)`.

### 1.1 Symbol glossary (defined before use)

| Symbol / term | Meaning |
|---|---|
| `N` | number of `\|`-separated elements in the collection |
| SPPF | Shared Packed Parse Forest (Tomita 1985; Scott & Johnstone 2010) — the parse-forest DAG |
| Symbol node | an SPPF identity node keyed by `(non-terminal, lo_pos, hi_pos)` — `prattail/src/sppf.rs:543` |
| Packing node | one *derivation* of a Symbol, keyed by `(rule_idx, children)` — `prattail/src/sppf.rs:573` |
| `sppf_stack_id` | per-cursor *interned handle* to the cursor's SPPF working stack (the GLL `w`) — `wpda_walker.rs:2618` |
| `lex_fork_path` | per-cursor *sidecar* `Arc<Vec<LexForkStamp>>` recording each lexical-disambiguation choice — `wpda_walker.rs:2794` |
| `LexForkStamp` | `(pos, alt_idx, src_idx, rule_idx)` — one lexical fork-arm traversal — `wpda_walker.rs:2857` |
| `sppf_collection_arena` | per-cursor `Arc<Vec<Vec<SppfId>>>` — the spliced element Symbol ids per collection slot — `wpda_walker.rs` (`FrontierArc` field, `tomita_frontier.rs:230`) |
| TomitaKey | the frontier *merge key*: `(state, node, pos, edge_top, edge_stack, collection_depth)` — `tomita_frontier.rs:70` |
| `merge_disambiguator` | the arc-level *anti-merge* tuple inside a TomitaKey bucket — `tomita_frontier.rs:326` |
| frontier | the live set of `BranchCursor`s at one walker step (`self.branch_cursors`) |
| cross-product | a multiplicative blow-up: per-element choices multiply instead of adding |

### 1.2 The lexical ambiguity (the multiplier)

The rholang grammar (`languages/src/rholang.rs:30-64`) lexes a bare numeral such as `0` **three ways**,
because three literal patterns all match the digit `0` with no required suffix:

```
Int     : r"-?(… | [0-9](_?[0-9])*)(i64)?"      → CastInt   (k:Int   |- k : Proc)   rholang.rs:37, 98
BigInt  : r"-?(… | [0-9](_?[0-9])*)n?"          → CastBigInt(n:BigInt|- n : Proc)   rholang.rs:44, 96
BigRat  : r"-?(… | [0-9](_?[0-9])*)r?"          → CastBigRat(r:BigRat|- r : Proc)   rholang.rs:50, 93
```

The eager lex DAG dump for `0` is `node: kind=Integer alt_kinds=["BigRat","BigInt"]` — one primary
lex + two secondary alternatives. Each alternative drives a distinct cast rule
(`CastInt`/`CastBigInt`/`CastBigRat`), all of which reduce to category `Proc`.

For a collection of `N` numeric elements, there are nominally `3ᴺ` ways to *label* the elements with
lexical readings. A correct GLR parser represents this with **additive** sharing in the SPPF
(3 packings per element, referenced by one bag node) — total work `O(3·N)`. The bug is that the
**cursor frontier** instead carries the **multiplicative** `3ᴺ` combination because cursors are kept
apart by per-cursor lexical provenance that the SPPF has already collapsed.

---

## 2. Confirmed root cause

> **One sentence:** the SPPF already shares the per-element lexical alternatives additively (three
> packings under one shared `Proc` Symbol), but the cursor frontier carries a *redundant parallel
> record* of the lexical choice — the `lex_fork_path` sidecar (primary blocker) and a distinct
> `sppf_collection_arena` `Arc` allocation whose **contents are identical** (secondary blocker) — and
> the Tomita frontier-merge gate (`merge_disambiguator` + `Arc::ptr_eq`) refuses to collapse cursors
> that differ on those redundant axes, so the per-element ×3 fan multiplies across elements into `3ᴺ`.

### 2.1 The merge gate (where collapse is refused)

Every cursor is ingested into the Tomita frontier map once per step
(`wpda_walker.rs:15057-15106` → `register_arc_with_aggregation`). Two cursors collapse **iff**:

1. they share a TomitaKey (`tomita_frontier.rs:70`) — `(state, node, pos, edge_top, edge_stack, collection_depth)`; **and**
2. they share a `merge_disambiguator` (`tomita_frontier.rs:326`):

   ```
   (sppf_stack_id, incoming_edge_stack_id, cohort_origin,
    lex_alt_idx, weight_src_idx, weight_rule_idx, lex_fork_path.last())
   ```
3. **and** their six heavy `Arc` fields are pointer-equal (`register_arc_with_aggregation`,
   `tomita_frontier.rs:641-679`), including `Arc::ptr_eq(sppf_collection_arena)`.

Condition (2) embeds `lex_fork_path.last()` (the `LexForkStamp`); condition (3) embeds the
`sppf_collection_arena` `Arc` *pointer identity*. Both diverge across the three lexical readings of
the same element, so the gate keeps three arcs where one would do.

### 2.2 Probe evidence (instrumentation since reverted)

A throwaway probe parsed `{0\|1\|…}` for `N ∈ {2,3,4,5}` against two controls: `{error\|…}`
(lex-unambiguous — `error` has exactly one lex) and `{(0)\|…}` (parenthesized). Frontier size was
read from the built-in `walker-stats` counters (`PRATTAIL_WALKER_STATS=1`, feature `walker-stats`):

| `N` | `{0\|…}` peak pre-merge | `{0\|…}` apply_calls | `{error\|…}` peak | `{error\|…}` apply_calls |
|----:|------------------------:|---------------------:|------------------:|-------------------------:|
| 2 | 59 | 370 | **1** | 11 |
| 3 | 299 | 1 184 | **1** | 16 |
| 4 | 1 331 | 5 111 | **1** | 21 |
| 5 | 4 052 | 23 100 | **1** | 26 |

- **`{error\|…}` frontier is a flat constant 1** for every `N` ⇒ with zero lexical ambiguity the
  collection parse is linear. This isolates the multiplier to *lexical ambiguity*, not collection
  structure, not the separator, not the cohort machinery.
- **`{0\|…}` frontier grows `59 → 299 → 1331 → 4052`** — ratios `5.1×, 4.5×, 3.0×`, fitting `~O(Nⁿ)`
  with `n≈4`; `apply_calls` grows `~3×–4.5×` per step, consistent with the reported `O(N⁶)`.
- Per-parse wall-time (debug): `{0\|…}` `N=5` ≈ **284 ms**; `{error\|…}` `N=5` ≈ **0.86 ms**.
- `{(0)\|…}` is **not** a clean control: the inner numeral `0` inside the parens is still tri-lex, so
  PAREND *also* explodes (`90 → 225 → 729`). Parens add structure but do **not** remove the lexical
  ambiguity, so they do **not** fix the bug.

A second probe instrumented `register_arc_with_aggregation` to record, on every *failed* collapse
(an arc landing on an existing TomitaKey but not merging), exactly which discriminant differed. For
`{0|1}` it observed **0 merges and 79 no-merges**, broken down (against the bucket's first arc):

| Discriminant | differs in | notes |
|---|---:|---|
| `lex_fork_path.last()` (source **i**) | **70 / 79** | the stamps are `alt_idx:0` vs `alt_idx:2` at the *same* `pos,src,rule` — the per-element lexical reading |
| `sppf_collection_arena` `Arc::ptr_eq` (source **ii**) | 43 / 79 | but see content row below |
| `sppf_collection_arena` **content** equality | **0 / 79** | the arenas are bit-identical: `[[12]]` vs `[[12]]` — SppfId 12 is the **shared** `Proc` symbol |
| `sppf_stack_id` (source **iii**) | **4 / 79** | essentially never — the splice restores it (§2.4) |
| weight `lex_rule_idx` | minority | the `LexicographicWeight` provenance triple (distinct from the stamp) |
| `visited_proj_descriptors` | minority | empty here; not the driver |

> **Pinpoint result.** The divergence source is **(i) the `lex_fork_path` sidecar** as the dominant
> blocker (70/79, and the *sole semantically-meaningful* blocker in the 31/79 cases where every other
> axis matches), with **(ii) the `sppf_collection_arena` `Arc` pointer** as a co-blocker that is a
> **false divergence** — its *contents are identical in 100 % of cases* (`[[12]]`), only the `Arc`
> allocation differs. Source **(iii) `sppf_stack_id` is not the driver** (4/79).

### 2.3 Why `sppf_stack_id` is *not* the divergence (the SPPF already shares)

The SPPF interns a Symbol on `(non-terminal, lo, hi)` (`sppf.rs:543`). Its own docstring states the
invariant: *"two cursors that reduce DIFFERENT productions to the same `(nt, lo, hi)` get the SAME
SppfId."* So `CastInt(0)`, `CastBigInt(0)`, `CastBigRat(0)` — three different productions over the
same span `[lo,hi]` — all reduce to **one** `Proc` Symbol id, with three Packings linked under it via
`link_packing_to_symbol` (`sppf.rs:687`) and weights `⊕`-aggregated (`sppf.rs:573-581`, Goodman-style).
This is *exactly* the additive packed sharing the literature prescribes. The probe confirms it: the
spliced element id is the *same* SppfId (12) for all three readings, and `sppf_stack_id` (which tracks
the interned working-stack handle) diverges in only 4/79 cases.

**The SPPF is already correct.** The blow-up lives entirely in the cursor frontier's *parallel*
bookkeeping.

### 2.4 Why the per-element fan multiplies instead of re-converging

The collection element is spliced by `emit_splice_into_collection` (`wpda_walker.rs:19568-19601`):

```rust
if let Some(top) = self.sppf_stack_arena.top(cursor.sppf_stack_id) {
    cursor.sppf_stack_id = self.sppf_stack_arena.intern_pop(cursor.sppf_stack_id); // pops element
    Arc::make_mut(&mut cursor.sppf_collection_arena)[id as usize].push(top);       // appends element id
}
```

After splicing element `k`, `intern_pop` **restores** the pre-element `sppf_stack_id` (the
FALSIFIED-PREMISE note at `wpda_walker.rs:4149-4169` documents the same fact for the cross-cat cycle
key), and every element dispatches at the *same* `CollectionMarker` GSS node with `cur_bp:0`. So the
TomitaKey and `sppf_stack_id` **re-converge** after each element — the SPPF-side state is shared.

But two per-cursor axes do **not** re-converge:

1. **`lex_fork_path`** accumulates one `LexForkStamp` per lexical fork-arm taken, and is never popped.
   It is appended at lex-fork apply (`wpda_walker.rs:13292-13370`) and carried verbatim through the
   Tomita round-trip (`FrontierArc::from_cursor`, `tomita_frontier.rs:356`). After element 0 the path
   is `[stamp(pos=1, alt=a₀)]`; after element 1 it is `[stamp(pos=1, alt=a₀), stamp(pos=3, alt=a₁)]`.
   For the `3ᴺ` distinct `(a₀,…,a_{N-1})` labelings these are `3ᴺ` distinct paths ⇒ the
   `merge_disambiguator`'s `lex_fork_path.last()` component keeps them all apart.

2. **`sppf_collection_arena`** is `Arc::make_mut`'d independently inside each fork-arm's allocation
   path. Two arcs whose arenas hold *identical* `SppfId`s but were CoW-forked separately fail
   `Arc::ptr_eq`. The merge gate compares by pointer (`tomita_frontier.rs:667-670`), not content, so
   it treats identical content as divergent.

### 2.5 The regression: metadata-frame → GSS-pushed-frame fan-out

The blow-up was introduced by the `30acf6de` "preserve ambiguity and runtime evidence" series, which
switched the cross-cat-delegate cohort fan-out from a **metadata-only** frame to a **GSS-pushed-fork**
frame. The two helpers still coexist in HEAD:

| HEAD `parent_frame_with_pushed_fork_branch` (`wpda_walker.rs:21752`) | baseline `parent_frame_with_fork_metadata` (`wpda_walker.rs:21782`) |
|---|---|
| calls `allocate_uncached_push_child` (`:21657`) | `let mut frame = parent.clone();` |
| constructs a **fresh** `BranchCursor`, runs `emit_push_side_effects`, `cursor_gss_push_with_kind` | appends the stamp; **no** GSS push, **no** side effects |
| each branch `Arc::make_mut`s `sppf_collection_arena` independently ⇒ **distinct `Arc`** | shares `Arc::clone(&parent.sppf_collection_arena)` ⇒ **`Arc::ptr_eq` succeeds** |
| used at the `CrossCatDelegate` `ResolvedHit`/`InflightCollision` sites (`:21459`, `:21551`, `:21588`) | used at the `CrossCatLhs` `ResolvedHit` synchronous-consume site (`:21325`, `:21376`) |

The baseline `b781d754` carries the *same* `merge_disambiguator` (verified — its `lex_fork_path.last()`
component is byte-identical, `mettail-rust-lexdeleg/prattail/src/tomita_frontier.rs:326`) and the *same*
`lex_fork_path` machinery. The only structural difference is the fan-out: the baseline's metadata
frames share the arena `Arc` and never push a per-arm GSS return lineage, so the frontier re-converged
after each element. HEAD's GSS-pushed frames force distinct arena `Arc`s **and** distinct return
lineages, so they never re-converge.

> **Conclusion.** The bug is a GLR SPPF-sharing leak at the cursor layer: the cursor frontier
> re-introduces a `3ᴺ` lexical cross-product that the SPPF has already collapsed to `3·N` additive
> packings. The leak is two redundant per-cursor anti-merge axes — `lex_fork_path` (primary) and the
> `sppf_collection_arena` `Arc` identity whose content is invariant (secondary).

### 2.6 Cross-product vs packed-sharing (diagram)

```
LEXICAL CROSS-PRODUCT (cursor frontier, HEAD)        ADDITIVE PACKED SHARING (SPPF, already correct)
──────────────────────────────────────────          ──────────────────────────────────────────────

  element 0       element 1                              PPar bag Symbol [0..hi]
  ┌───────┐       ┌───────┐                                   │
  │Int  0 │──┐ ┌──│Int  1 │     each (a₀,a₁) pair is          ├── packing PPar(elem₀, elem₁, …)
  │BigI 0 │──┼─┼──│BigI 1 │     a SEPARATE cursor arc              │        │
  │BigR 0 │──┘ └──│BigR 1 │     ⇒ 3×3 = 9 arcs at one          elem₀ Sym   elem₁ Sym   ← ONE Symbol id
  └───────┘       └───────┘       TomitaKey (probe: 10)       [0..1]      [4..5]         per span (id 12)
       3       ×       3        ……… ×3 per further element    ╱  │  ╲      ╱  │  ╲
            = 3ᴺ arcs               = O(3ᴺ) cursor work     Int BigI BigR …               ← 3 PACKINGS,
                                                            pk  pk   pk                      weights ⊕-summed
                                                              = O(3·N) forest nodes
```

The fix makes the frontier mirror the right-hand side: per-element lexical alternatives converge to a
shared bag-arc, so the frontier re-converges to `O(N)`.

---

## 3. Recommended design — drop the redundant lexical anti-merge axes

The fix removes the two *redundant* anti-merge axes from the **collection-element context only**,
where they provably encode no distinction the SPPF does not already carry. It is a **frontier-merge
relaxation**, not a fan-out rewrite, and it deliberately leaves the SPPF, the GSS, and the
chained-output / cross-cat discriminants untouched.

### 3.1 Mechanism

Two coordinated changes, both inside the Tomita merge path:

**Change A — content-equality for `sppf_collection_arena` (kills source ii).**
In `register_arc_with_aggregation` (`tomita_frontier.rs:667-670`), replace the
`Arc::ptr_eq(&existing.sppf_collection_arena, &arc.sppf_collection_arena)` predicate with a
*content-or-pointer* predicate:

```rust
(Arc::ptr_eq(&existing.sppf_collection_arena, &arc.sppf_collection_arena)
 || *existing.sppf_collection_arena == *arc.sppf_collection_arena)
```

`Vec<Vec<SppfId>>` is `Eq`; the fast `ptr_eq` short-circuits the common shared case, so the structural
compare runs only when pointers differ (the false-divergence case the probe found: identical `[[12]]`).
This is sound because the arena's *content* (the spliced element Symbol ids) is the only observable;
two cursors with equal content are observationally identical on this axis. This change is global (not
collection-gated) because arena content-equality is always a sound merge condition.

**Change B — collection-local `lex_fork_path` collapse (kills source i).**
The `lex_fork_path` is a sidecar that is **never** read by `engine.step`, the SPPF realizer, or any
semantic action — it produces no AST and no parse decision. Every read of `lex_fork_path.last()` feeds
a **merge / equivalence-bucketing** path (verified by enumerating all read sites):

- `merge_disambiguator` (`tomita_frontier.rs:336`) — the frontier-merge anti-merge tuple;
- `CohortShell::lex_fork_stamp` capture at cohort-pause (`cohort_lazy.rs:557`) — the H12 cohort `~_obs`
  bucketing axis (`cohort_lazy.rs:129-132`: "the walker treats different stamps as distinct parses at
  ConfigKey merge time, so cohort members must share this");
- the cursor-snapshot mirrors (`wpda_walker.rs:9483`, `:16844`) — themselves merge/diagnostic feeders;
- the `walker-stats` diagnostic counters.

All four are *equivalence/merge* consumers, none is *semantic*. When a cursor is *inside a collection
element context* (it has pushed past a `CollectionMarker`; `collection_stack_depth > 0`), the
lexical-disambiguation choice for that element has **already been recorded as an SPPF packing** under
the shared element Symbol. The stamp is therefore redundant *there*. Crucially, the cohort `~_obs`
capture (`cohort_lazy.rs:557`) happens at *pause time* — **during** the element sub-parse, **before**
the splice — so live element forks are still bucketed distinctly while in flight; the truncation only
removes the stamp *after* the element is sealed, exactly when sibling readings re-enter the frontier
merge (see S4).

The collapse: stop letting an element's lexical stamp survive past the splice that finalizes the
element. The natural splice point is `emit_splice_into_collection` (`wpda_walker.rs:19568`), which
already pops the element's `sppf_stack_id`. Add the symmetric pop of the element's lexical stamps:

```rust
// after the existing intern_pop + arena push, inside emit_splice_into_collection:
// The element's lexical reading is now an SPPF packing under the shared element
// Symbol `top`. Its lex_fork_path stamps are redundant beyond this point — drop
// the stamps appended since this element opened so sibling lexical readings of the
// SAME element converge to one bag-arc (additive sharing, not 3^N cross-product).
truncate_lex_fork_path_to_element_open(cursor);
```

where the element-open watermark is captured the same way optional-scope marks are
(`emit_start_optional_scope`, `wpda_walker.rs:19604-19612`): record `lex_fork_path.len()` when the
element sub-parse opens (at the post-`CollectionMarker` dispatch, or at the separator consume), and on
splice `Arc::make_mut(&mut cursor.lex_fork_path).truncate(watermark)`. The watermark rides on the same
per-cursor stack discipline as `optional_scope_marks` / `collection_sep_counts`.

After Change B, the three lexical readings of element `k` carry **identical** `lex_fork_path` after the
splice (the element's stamps are gone), so `merge_disambiguator` matches; after Change A their
`sppf_collection_arena` content matches; `sppf_stack_id` already matches (§2.4). All three arcs collapse
to one. The next element therefore starts from a *single* arc, not three ⇒ the fan is `3 + 3 + … = 3·N`
additive, not `3ᴺ` multiplicative.

> **Implementation note (carrier).** Like the collection-primary-infix fix's `coll_dispatch_bp`
> carrier, the per-element stamp watermark cannot live only in transient state (the element sub-parse
> destroys and rebuilds `CollectionLoop` from the persistent marker, `engine_impl.rs:584-665`). It must
> ride on the cursor as a parallel stack to `optional_scope_marks` — call it `lex_fork_marks:
> Arc<Vec<usize>>` — pushed at element open, popped at splice. This mirrors the existing
> `optional_scope_marks` (`wpda_walker.rs:2698`-region) discipline exactly and is `O(1)` per element.

### 3.2 Why the frontier re-converges to `O(N)` (complexity argument)

Let `Fₖ` be the frontier-arc count at the TomitaKey reached *after* splicing element `k`.

- Without the fix: each element multiplies the live arc count by the element's lexical degree `d=3`,
  because the gate keeps each `(reading₀,…,readingₖ)` prefix distinct. `Fₖ = d^{k+1}` ⇒ `F_{N-1} = 3ᴺ`.
- With the fix: after splicing element `k`, all `d` lexical readings of element `k` carry identical
  `(lex_fork_path, sppf_collection_arena-content, sppf_stack_id, TomitaKey)` ⇒ they `⊕`-collapse to a
  single arc (weights aggregated, preserving the min-weight tiebreak). So `Fₖ = 1` after every splice,
  and the *transient* fan during element `k` is `≤ d` (bounded, constant). Total cursor work is
  `Σₖ O(d) = O(d·N) = O(N)`. The peak frontier is `O(d) = O(1)` in the element index, recovering the
  baseline's linear curve.

The `⊕`-aggregation already exists in `register_arc_with_aggregation` (`tomita_frontier.rs:681-695`):
the merged arc keeps `existing.weight ⊕ arc.weight` and folds the step counters. The fix simply lets it
*fire* on the lexical-sibling arcs it currently rejects.

### 3.3 Soundness argument

The design preserves every distinction the soundness suite needs. We argue each invariant explicitly.

**(S1) The realized parse(s) are unchanged.** The SPPF is the source of truth for realization
(`sppf_realize.rs:114-201`): a Symbol realizes as the concat over *all* its packings; single-result
mode takes the min-weight packing. Neither Change A nor B touches `intern_symbol`, `intern_packing`,
`link_packing_to_symbol`, or the weights. The three lexical readings of each element remain three
packings under the shared element Symbol with their `⊕`-aggregated weights, exactly as today. Collapsing
*cursor arcs* changes only *how many times the walker re-derives the same SPPF nodes*, not which nodes
exist. The min-weight winner (`{0}` → `CastBigInt(NumLit(0))`, observed) is selected by the SPPF/weight
machinery, which is untouched. Therefore `parse_Proc_via_wpda` returns the identical term.

**(S2) Weight aggregation stays monotone / idempotent.** Merged arcs combine via
`LexicographicWeight::plus` (lex-min under the idempotent semiring), which is associative, commutative,
and idempotent. Collapsing three lexical-sibling arcs into one and `⊕`-summing their weights yields the
same lattice element as the SPPF's own packing-weight `⊕` (Goodman). No weight is lost or double-counted
(the step-counter fold at `tomita_frontier.rs:694-695` is preserved).

**(S3) `@a!(Nil)!(Nil)` (chained output) is preserved.** A chained send `n!(p)!(q)` produces *two
genuinely distinct parses* that the SPPF distinguishes by **span/structure**, and the cursor frontier
keeps apart by **`sppf_stack_id`** (the GLL `w` progress discriminant — `wpda_walker.rs:4122-4145`):
the two readings push *different* reduced Symbols onto the working stack, so their `sppf_stack_id`s
diverge. Neither Change A nor Change B touches `sppf_stack_id`:

- Change A relaxes only `sppf_collection_arena` (a *collection-slot* structure; chained output is not a
  collection).
- Change B truncates only `lex_fork_path`, and only *inside a collection element* (`collection_stack_depth
  > 0`). `@a!(Nil)!(Nil)` is not inside a collection element, so its `lex_fork_path` is untouched; and even
  if it were, its readings differ by `sppf_stack_id`, which remains a full `merge_disambiguator` axis.

The probe corroborates the orthogonality: in the collection cross-product, `sppf_stack_id` is the
divergence in only 4/79 cases — it carries almost no collection-element signal, precisely because the
splice restores it. Conversely it is *the* signal for chained output. The two distinctions live on
different axes; the fix touches only the collection-element axes.

**(S4) The `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` invariant
(`tomita_frontier.rs:1132`).** This unit test asserts that two arcs with `lex_fork_path = [stamp(alt:0)]`
vs `[stamp(alt:1)]` (same `pos,src,rule`) stay as **two** arcs. This invariant is about preserving
distinct lexical forks **that are still live on the cursor** — i.e. forks that have *not yet* been
sealed into an SPPF packing. The fix does **not** weaken `merge_disambiguator`: it still includes
`lex_fork_path.last()`, so two arcs with genuinely different live stamps still do not merge, and **the
unit test continues to pass unchanged**. What the fix changes is *upstream*: inside a collection
element, the element's stamps are *removed from the cursor* at splice (because they are now redundant
SPPF packings), so by the time two sibling arcs reach the merge gate their `lex_fork_path`s are equal —
they were made equal by the splice, not by relaxing the comparison. The invariant guards the *gate*;
the fix changes the *input to the gate*. They do not conflict.

> This is the crux of the soundness separation: the test protects "do not merge arcs that still
> disagree on a live lexical fork." The fix says "once an element's lexical fork is sealed into the
> SPPF as a packing, it is no longer a *live* fork — drop it from the cursor." Both are simultaneously
> true.

The same ordering protects the **H12 cohort `~_obs` bucketing** (`cohort_lazy.rs:557`,`:129-132`),
which also reads `lex_fork_path.last()`. That capture happens at cohort *pause* time — **during** the
element sub-parse, strictly **before** `emit_splice_into_collection` truncates — so two cursors that
pause mid-element with different live lexical readings still bucket into distinct cohort members. The
truncation removes a stamp only once its element is sealed into the SPPF, i.e. after any pause/resume
for that element has completed. Live forks are distinguished; sealed forks are not. This is the same
"input to the gate, not the gate" separation, applied to the cohort path. Gate: `gen_rholang_prop` +
`rholang_tests` exercise paused-cohort collection parses and must stay green (§6.2).

**(S5) Tomita ambiguity (`realize_tomita_ambiguous_expression_yields_two`, `sppf_realize.rs:428`).**
Genuine top-level ambiguity (two full parses of the whole input) is represented by two packings under
the *root* Symbol and is unaffected — the fix operates on collection-element sub-spans, not the root,
and never deletes a packing.

**(S6) No new mis-parse / sub-multiset ghost.** The arena content-equality (Change A) merges only arcs
whose spliced element-id vectors are *bit-identical* — it cannot merge `{0}` with `{0,1}` (different
content) nor splice a cross-category element (that machinery, `collection_element_src_idx`
`wpda_walker.rs:504`, is untouched). Change B removes stamps only *after* a successful splice of *this*
element, so it cannot affect which elements are accepted.

### 3.4 Exact code locations

| Change | File:line | Edit |
|---|---|---|
| A (arena content-eq) | `prattail/src/tomita_frontier.rs:667-670` | add `\|\| *existing.sppf_collection_arena == *arc.sppf_collection_arena` to the `Arc::ptr_eq` clause |
| B carrier field | `prattail/src/wpda_walker.rs` (`BranchCursor`, near `optional_scope_marks` `:2698`) | add `lex_fork_marks: Arc<Vec<usize>>` + clone/`from_arc`/`from_cursor` plumbing |
| B carrier on `FrontierArc` | `prattail/src/tomita_frontier.rs` (`FrontierArc` near `optional_scope_marks` `:228`) | add the field + `from_cursor`/`materialize` plumbing |
| B push watermark | `prattail/src/wpda_walker.rs` element-open (post-`CollectionMarker` dispatch / separator consume) | `cursor.lex_fork_marks.push(lex_fork_path.len())` |
| B pop+truncate | `prattail/src/wpda_walker.rs:19580` (inside `emit_splice_into_collection`) | pop watermark; `Arc::make_mut(&mut cursor.lex_fork_path).truncate(w)` |

---

## 4. Rejected alternative — restore the baseline metadata-only fan-out

**Proposal.** Revert the cross-cat-delegate cohort fan-out from `parent_frame_with_pushed_fork_branch`
(`wpda_walker.rs:21459`, `:21551`, `:21588`) back to the baseline `parent_frame_with_fork_metadata`
(metadata-only, no GSS push), reconciled with the current lazy-cohort machinery (the `30acf6de`
"preserve ambiguity and runtime evidence" series that introduced the push).

**Pros.**
- It is the *exact* code that was `O(N)` at `b781d754`; the curve is known-good.
- It is structurally local to three call sites.

**Cons / risk.**
- It directly **reverts** the `30acf6de` ambiguity/runtime-evidence series, whose stated purpose was to
  *preserve* per-lexical-alternative lineages and runtime evidence that the metadata-only frame dropped.
  The memory ledger records that this series fixed real soundness gaps (preserving projection evidence,
  prefix ambiguity, demand-sensitivity — commits `db53e83a`, `ea1dcb6b`, `ddfafc9f`). Reverting risks
  re-opening those, and the design constraint explicitly lists the committed fixes
  (`normalize_crosscat_lhs_push_state`, `priority_ordered_packings`, …) as not-to-be-touched.
- The metadata-only frame "re-converges" partly by *not recording* distinctions, which is the opposite
  of the SPPF-faithful direction. It would re-converge the lexical fan but might also silently re-merge
  lineages the series intentionally separated — a correctness regression that the `{error|…}` and
  parity tests would not catch (they are lex-unambiguous).
- It does not address the *root* representational issue (a redundant cursor-side lexical record); it
  only removes one of the two fan-out paths that *expose* it. The `sppf_collection_arena` false-divergence
  (source ii) would remain on any other path that `Arc::make_mut`s the arena.

**Verdict: reject.** The metadata-only revert trades a *known soundness improvement* for a performance
win, and fixes the symptom (one fan-out path) rather than the cause (redundant anti-merge axes). The
recommended design (§3) keeps the `30acf6de` GSS-pushed fan-out intact and instead removes the redundant
distinctions at the merge layer, which is both narrower (no fan-out semantics change) and root-causal.

---

## 5. Implementation plan (incremental)

Each step is independently testable; land in order.

1. **I0 — instrumentation baseline (throwaway).** Re-add the `walker-stats` frontier probe + the
   `register_arc_with_aggregation` no-merge breakdown (the reverted probe), capture
   `{0|1|…}` `N∈{2..6}` frontier curves as the *before* baseline. Revert before I1.
2. **I1 — Change A (arena content-equality).** Single-predicate edit at `tomita_frontier.rs:667`.
   Add a unit test `aggregation_merges_arcs_with_equal_arena_content_distinct_arc`. Re-measure: this
   alone should cut the constant factor (kills source ii) but **not** the `3ᴺ` growth (source i still
   blocks). Confirm no regression on the full gauntlet.
3. **I2 — Change B carrier plumbing.** Add `lex_fork_marks` to `BranchCursor` + `FrontierArc` +
   `from_cursor`/`materialize_branch_cursor_from_arc`/`Clone`. No behavior change yet (field unused).
   Confirm zero regression (pure plumbing).
4. **I3 — Change B push/truncate.** Push the watermark at element open; truncate in
   `emit_splice_into_collection`. Gate on `collection_stack_depth > 0` so non-collection parses are
   byte-identical. Re-measure: `{0|1|…}` frontier should drop to `O(N)` (peak ≈ constant).
5. **I4 — verification sweep** (§6). All gates green + timing targets met.
6. **I5 — formal note.** Extend the collection-fork evidence proof family
   (`CollectionForkEvidence.v`, referenced in the evidence-pruning ledger) with a lemma:
   *element-sealed lexical stamps are observationally redundant* (after splice, the cursor's
   `lex_fork_path` element-suffix is recoverable from the element Symbol's packings) — so truncation is
   observation-preserving. Zero-admission.
7. **I6 — cleanup.** Remove all probes; confirm `git status` shows only intended changes.

**Kill switch.** Gate Change B behind a per-walker env flag (P-series convention, read once at
construction — cf. `PRATTAIL_EP_P1`, `wpda_walker.rs:131-149`) so it can be disabled if a soundness
gate regresses, without reverting the carrier plumbing.

---

## 6. Verification / test plan

### 6.1 Performance targets (the acceptance criteria)

| Metric | Target | How |
|---|---|---|
| `lazy_lex_equivalence::rho_full_parse_lazy_eq_eager` | **< 10 s** (from ~250 s) | `cargo test -p languages --test lazy_lex_equivalence rho_full_parse_lazy_eq_eager` |
| `lazy_lex_equivalence::report_nodes_materialized` | **< 10 s** | same test binary |
| `{0\|1\|…\|19}` peak frontier | `O(N)` (≈ constant in element index; was `O(N⁴)`) | `walker-stats` probe (I0/I3 before/after) |
| `{0\|…}` apply_action calls | `O(N)` (was `O(N⁶)`) | `walker-stats` |

### 6.2 Soundness gates that must stay green

| Suite | What it guards | Command |
|---|---|---|
| `prattail` lib (≈ 3789 tests, incl. `tomita_frontier` unit tests) | the merge invariants, incl. `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` (`tomita_frontier.rs:1132`) and `arc_merge_disambiguator_distinguishes_lex_fork_stamp` (`:1113`) | `cargo test -p prattail` |
| `rholang_tests` + `gen_rholang_{unit,analytical,rewrite,prop}` | rholang parse/eval correctness | `cargo test -p languages --test rholang_tests` (+ the `gen_rholang_*`) |
| `wpda_parity_rholang_collections` | `{error}`, `{error\|error}`, `{error\|error\|error}`, `{}` collection shapes (`tests/wpda_parity_rholang_collections.rs`) | `cargo test -p languages --test wpda_parity_rholang_collections` |
| `gen_guardedrho_*` proc display, incl. chained output `@a!(Nil)!(Nil)` (S3) | the `sppf_stack_id` chained-output distinction | `cargo test -p languages --test gen_guardedrho_unit` (+ analytical/prop) |
| `lazy_lex_equivalence` full corpus | lazy ≡ eager *and* parse-result equality on `{0\|1\|2}`, `{0..19}`, `new x, y in {…}` | `cargo test -p languages --test lazy_lex_equivalence` |
| full gauntlet (calc-op, edge, ledtest, ambient) | no cross-language regression | the standard battery |

### 6.3 New tests to add

- `tomita_frontier.rs`: `aggregation_merges_arcs_with_equal_arena_content_distinct_arc` (Change A).
- `tomita_frontier.rs`: `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` must **still pass
  unchanged** (regression guard for S4).
- `languages/tests`: a `rho_collection_fork_is_linear` test that parses `{0|1|…|N}` for `N∈{2,5,10,20}`
  under `walker-stats` and asserts peak frontier `≤ C` for a small constant `C` (the `O(N)` proof).
- `languages/tests`: parse-result equality `{0|1|2}` and `{0..19}` must equal their pre-fix terms
  (the multiset of `CastBigInt(NumLit(k))`).

### 6.4 Differential check (lazy ≡ eager preserved)

The existing `rho_parse_eq` (`lazy_lex_equivalence.rs:123`) asserts eager and lazy produce identical
`Debug` term + identical final pos. Because the fix touches neither lexer nor SPPF, lazy ≡ eager is
preserved by construction; the gate confirms it empirically.

---

## 7. Summary

- **Confirmed root cause:** a GLR SPPF-sharing leak at the cursor layer. The SPPF already shares the
  per-element tri-lex ambiguity additively (3 packings under one shared `Proc` Symbol, `sppf.rs:543`),
  but the cursor frontier carries a *redundant parallel record* of the lexical choice that the Tomita
  merge gate (`tomita_frontier.rs:326`,`:667`) refuses to collapse — multiplying the per-element ×3 fan
  into `3ᴺ`.
- **Divergence source pinpoint (probe):** **(i) the `lex_fork_path` sidecar stamp** is the dominant
  blocker (70/79 no-merges; sole semantic blocker in 31/79); **(ii) the `sppf_collection_arena` `Arc`
  pointer** is a co-blocker that is a *false divergence* (content bit-identical in 100 % of cases);
  **(iii) `sppf_stack_id`** is *not* the driver (4/79 — the splice restores it).
- **Recommended fix:** relax the merge gate's two redundant collection-element axes — arena
  *content-equality* (global, sound) + collection-local `lex_fork_path` truncation at splice — letting
  the existing `⊕`-aggregation collapse lexical-sibling arcs. Frontier re-converges to `O(N)`.
- **Soundness:** preserves the SPPF/weights/realization unchanged (S1,S2,S5,S6); preserves the
  `sppf_stack_id` chained-output distinction `@a!(Nil)!(Nil)` because the fix touches neither
  `sppf_stack_id` nor non-collection cursors (S3); the
  `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` invariant *still passes unchanged*
  because the fix changes the gate's *input* (sealing element stamps into SPPF packings at splice), not
  the gate's *comparison* (S4).
- **Rejected alternative:** reverting to the baseline metadata-only fan-out — rejected because it
  reverts a known soundness-improving series (`30acf6de`) and fixes a symptom path rather than the
  root representational redundancy.

---

## 8. Convergence (red-team outcome + implemented form)

The design was adversarially red-teamed across six attack surfaces (nested-collection watermark
scoping, interesting element sub-parses, cohort-pause timing, Change-A wrong-merge, interaction with
the committed fixes, and ambiguity preservation). The red-teamer empirically implemented both Change B
variants on the live tree and measured them. **Verdict: CONVERGED** — no soundness hole — with three
refinements that are now folded into the implemented form:

### 8.1 Change B uses **clear-all-at-splice**, NOT the watermark stack
The §3.1 watermark-stack premise ("`lex_fork_marks` mirrors `optional_scope_marks` discipline
exactly") is **false**: (a) the element-open push site is `emit_start_collection`
(`wpda_walker.rs:19541`), not the `BuilderDelta::StartCollection` arm (which never fires on the live
parse); (b) the cohort shell (`CohortShell`/`CohortMemberState`/`materialize_branch_cursor`) does not
carry the mark, so cohort-revived cursors splice with an empty stack; (c) the watermark *value*
(`lex_fork_path.len()` at open) is not `~_obs`-invariant across cohort members. The stack therefore
underflows pervasively (`{0|1}`: 15 underflows; `{0|{1|{2|3}}}`: 74). The underflow is **benign**
(truncate-to-watermark degrades to a no-op), and the red-team measured the watermark and clear-all
variants to be **bit-identical** in frontier reduction and **term-identical** across a 33-case
nested/sub-parse battery.

**Implemented form:** at `emit_splice_into_collection` (`wpda_walker.rs`, right after the arena push),
clear the cursor's `lex_fork_path` entirely (`Arc::make_mut(&mut cursor.lex_fork_path).clear()`).
`emit_splice_into_collection` is only reached when splicing a collection element, so the
`collection_stack_depth > 0` gate is implicit (the function *is* the gate). This is stack-free, cannot
underflow, needs no cohort-shell carrier, and is the red-team's recommended variant. Change A is
unchanged from §3.1 (`tomita_frontier.rs`: arena content-or-pointer equality).

### 8.2 Complexity is `O(N²)`, not `O(N)` (§3.2 corrected)
`merge_disambiguator` embeds a **second** sticky copy of the lexical-disambiguation identity — the
`LexicographicWeight` provenance triple `(lex_alt_idx, weight_src_idx, weight_rule_idx)` (left-projected
constant along the cursor, per the `LexProvenance` trait in `rigail`). After splicing element `k`, the
sealed-element cursors fall into `d=3` distinct weight-triple classes (probe: `(0,0,7)/(0,0,10)/
(0,0,11)/(0,0,12)` at the same restored `sppf_stack_id` and sealed arena `[[12]]`), so the per-splice
survivor count is `Fₖ = d` (a constant), not `1`. The total is therefore `O(d·N) = O(N²)` peak frontier
in the element index, not `O(N)`. This is still a decisive win and is NOT a multiplier (the SPPF shares
the Symbol), so it does not re-explode. Driving it to true `O(N)` would additionally require merging on
the weight triple inside a collection element — a possible future refinement, explicitly out of scope
here (it touches the weight provenance the `30acf6de` series relies on).

### 8.3 Change A alone is inert
Change A by itself does not move the frontier (the probe confirmed `lex_fork_path` still blocks every
merge); the performance win requires **A and B together**. A is retained because arena
content-equality is an independently-sound merge condition and removes a real false-divergence axis.

### 8.4 Verification results (implemented, HEAD after this commit)
- `lazy_lex_equivalence::rho_full_parse_lazy_eq_eager`: **4.2 s** (was ~250 s timeout); `report_nodes_materialized`: **4.4 s**. Both well under the 10 s target (~60× speedup). All 7 lazy≡eager equivalence checks pass.
- `cargo nextest run -p prattail`: **3789/3789**, including the S4 guards `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs` and `arc_merge_disambiguator_distinguishes_lex_fork_stamp` (both pass unchanged — the fix changes the gate's *input*, not its comparison).
- 292-test soundness sweep (gen_guardedrho_unit incl. `@a!(Nil)!(Nil)` chained output, calculator incl. dangling-else/ternary, rholang_tests, wpda_parity_rholang_collections, edge_case_tests, recovery_accumulation, calculator_display_projection_tests, display_roundtrip_regression_tests, led_delegation_tests, and the prior cluster fixes): **292/292**, zero regressions.
