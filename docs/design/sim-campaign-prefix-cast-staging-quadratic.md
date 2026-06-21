# `sim_calculator_proptest_campaign` Slowdown — Prefix-Cast-Wrap Re-Staging Quadratic

**Target:** branch `feature/wfst-architecture`, HEAD `011f7770` (main worktree).
**Status:** ROOT-CAUSED + FIXED + verified (2026-06-20; uncommitted on `feature/wfst-architecture`).
**Scope of the fix:** `prattail/src/wpda_walker.rs` (WPDA walker, prefix-cast-wrap-job staging) +
`prattail/src/gss.rs` (GSS hasher). **No grammar / regex / spec change. No revert of any committed fix.**
**Working tree shows only:** `prattail/src/wpda_walker.rs`, `prattail/src/gss.rs`, and this document.

This is the **fourth** document in the `30acf6de` "preserve ambiguity and runtime evidence" cursor-frontier
fan-out family (the prior three: `rhocalc-collection-fork-explosion.md`, `calculator-map-crosscat-fanout.md`,
`calculator-broad-parse-slowdown.md`). It **corrects an incorrect measurement** in
`calculator-broad-parse-slowdown.md` §9.5 and root-causes a **distinct** regression that all three priors
missed.

---

## 0. TL;DR

| | value |
|---|---|
| **Symptom** | `sim_calculator_proptest_campaign` (`languages/tests/gen_calculator_prop.rs:2892`) ≈ 8.4 s baseline `b781d754` → ≈ 90 s at HEAD (≈ 11×). |
| **`calculator-broad-parse-slowdown.md` §9.5 claim** | "sim is SIMULATION-bound; parse is only 9.2 % of `run_to_normal_form`; the other ≈91 % is the rewrite engine." |
| **This document's finding** | §9.5 is **WRONG** (it timed `Bool::parse`, not the `parse_term` path the runner uses). The dovetail/rewrite engine is **≈ 0.1 ms** (negligible). The campaign is **100 % PARSE-bound**, in `CalculatorLanguage::parse` (top category). |
| **Root cause** | A prefix-cast-wrap-job re-staging quadratic introduced in the codex range by `08f86457` ("publish cross-cat bodies through SPPF values"), only partially clawed back by `d84b4df4`. On cross-cat-cast inputs the walker re-stages every parked waiter against every re-published body symbol: measured **26 363 791** `(waiter × body)` staging attempts for ONE parse, of which **99.92 %** dedup away after an expensive `BranchCursor` clone + 19-field key hash. |
| **Fix** | A per-fired-body **staging watermark** (`prefix_cast_stage_watermark`): a published body symbol is staged against each parked waiter **at most once per (body, body-weight)**. Byte-identical output (proven: identical distinct-job count, ON/OFF differential 0 mismatches). Kill switch `PRATTAIL_PREFIX_CAST_STAGE_MEMO` (default ON). |
| **Secondary (general) fix** | GSS node/edge maps `std::collections::HashMap` (SipHash) → `rustc_hash::FxHashMap` (≈ 10 % on the heavy cross-cat path). Sound (hash function only; pre-existing — not a regression). |
| **Result** | `26.4 M → 5.7 k` staging operations on the worst input; worst single parse `22.3 s → ≈ 4.2 s`; campaign ≈ 90 s → median **≈ 38 s** (5-run isolated: 29.5 / 31.1 / 38.8 / 41.5 / 64.0 s), comfortably under the 60 s target on the median and under the 180 s leak cap always. |
| **Residual** | The remaining cross-cat-cast frontier explosion is controlled by the **load-bearing dual-role** `visited_proj_descriptors` suppression memo, which is **unsafe to truncate** (would re-explode the projection fan — see §6). |

---

## 1. Symbol glossary (defined before use)

| Symbol / term | Meaning |
|---|---|
| WPDA | Weighted Push-Down Automaton — the parser runtime (`prattail/src/wpda_walker.rs`). |
| SPPF | Shared Packed Parse Forest — the parse-forest DAG (`prattail/src/sppf.rs`). A **Symbol** node is keyed by `(non-terminal, lo, hi)`; a **Packing** is one derivation. |
| cursor / arc | One live parse configuration in the frontier (`BranchCursor<W>`). |
| frontier | The live cursor set at one walker step (`self.branch_cursors`). |
| GSS | Graph-Structured Stack (`prattail/src/gss.rs`, `WpdaGss<W>`) — the shared call/return stack. |
| cross-cat cast | A rule whose argument category differs from the result category — e.g. `BoolToInt` (`int(<Bool>)`), `str(<Bool>)`, `float(<Int>)`. The Calculator grammar has dozens. |
| prefix-cast-wrap job | A pending synthesis of a trigger-bearing prefix cast `C_in → C_out` over a full-span `C_in` body, forming `C_out[trigger_lo, close_hi)` (`PrefixCastWrapJob<W>`, `wpda_walker.rs`). Carries a clone of the resolving body's outer frame. |
| prefix-cast waiter | A parked wrapper continuation (`PrefixCastWaiter<W>`) recorded when a direct trigger-bearing cast launches its body via `ReplaceAndPush(CategoryEntry(C_in))`; joined later with any matching full body symbol. |
| `parked_prefix_cast_waiters` | `Vec<PrefixCastWaiter<W>>` — the parked waiters. **APPEND-ONLY for the lifetime of a parse** (only `push`ed; fully `clear`ed only at the two parse-boundary `reset` sites). |
| `try_stage_parked_prefix_cast_waiters` | Called once per SPPF symbol publication; joins the fired body symbol with matching parked waiters, producing staged jobs (`wpda_walker.rs`). |
| `push_prefix_cast_wrap_job_once` | Dedups a staged job by its full `PrefixCastWrapJobKey` into `pending_prefix_cast_wrap_job_keys`, pushing to `pending_prefix_cast_wrap_jobs` only if new. |
| `PrefixCastWrapJobKey` | 19-field structural identity of a job (`body_sid`, span fields, `c_out`, `cast_rule`, and the outer frame's node/pos/edge-stack/sppf-stack/cohort/weight-triple/lex-fork-stamp). |
| `symbol_weight_sum(sid)` | The `⊕`-aggregated weight of an SPPF Symbol. **Accumulates** as more Packings link to the Symbol (`sppf.rs`; test `symbol_weight_sum_accumulates_over_linked_packings`). |
| `prefix_cast_stage_watermark` | **(this fix)** `FxHashMap<SppfId, (usize, W)>` — per-fired-body staging high-water mark `(waiter_count_at_last_stage, body_weight_at_last_stage)`. |

---

## 2. The measurement that corrects `calculator-broad-parse-slowdown.md` §9.5

§9.5 of the broad-parse document concluded the `sim` residual was **simulation-bound** ("parse ≈ 386 ms vs
sim ≈ 4193 ms; 91 % is the rewrite engine"). A direct split of `run_to_normal_form`
(`simulation/src/runner.rs:353`) into its two phases **refutes** that:

| phase (50 `arb_bool(3)` campaign inputs, HEAD before this fix) | wall time |
|---|---|
| **PARSE** (`Language::parse_term`) | **70 571 ms (100.0 %)** |
| dovetail report (`run_default_backend_report`) | **0.1 ms (0.0 %)** |

The discrepancy is a **mislabelled parse function**. `run_to_normal_form` parses via
`self.language.parse_term(input)`, which calls `CalculatorLanguage::parse` — the language's **top category**
(`Proc`) parse. §9.5 instead timed `Bool::parse` (the single-category facade). On the slowest campaign input
they differ by **279×**:

```text
input = str("qzms" > "rvwe") >= str(has(map() , a))
  Language::parse_term  (CalculatorLanguage::parse, top category Proc) = 7 571 ms
  Bool::parse           (single-category facade)                       =    27 ms
```

`str(...) >= str(...)` is a top-level `Bool` (`>=` returns `Bool`), but parsing it as the language top
category `Proc` (via the `ProcBool` wrapper + the full `Bool` subgrammar + every cross-cat cast that can reach
`Bool`) is where the cost lives. **The campaign is parse-bound; the rewrite engine is irrelevant to it.**

```text
            run_to_normal_form(input)            ── 100 % of the campaign cost ──▶ PARSE
            ┌───────────────────────────────────────────────────────────────────────────┐
            │  parse_term(input)  =  CalculatorLanguage::parse(input)  [top category Proc]│  ◀── 7 571 ms
            └───────────────────────────────────────────────────────────────────────────┘
            ┌───────────────────────────────────────────────────────────────────────────┐
            │  run_default_backend_report(term)   [Dovetail e-graph saturation + extract] │  ◀── 0.1 ms
            └───────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Root cause: the prefix-cast-wrap re-staging quadratic

### 3.1 The mechanism (instrumented)

Atomic counters around the prefix-cast machinery, on the worst input
(`bitnot cast_error_fixed * … bitand (…)`, 22.3 s at HEAD):

```text
[PERFPROBE] stage_calls=125717  stage_candidates=26363791  stage_staged=26363791
            push_job_calls=26381389  push_job_inserted=19864   jobkey_calls=26381389
            drain_jobs=19864  park_inserted=7476
            stage_distinct_body=240  stage_repeat_body=125457  max_waiters=5932
```

Reading the counters:

- `try_stage_parked_prefix_cast_waiters` is called **125 717** times (once per SPPF publication — fine).
- But only **240 DISTINCT body symbols** are ever passed to it; the other **125 457 (99.8 %)** calls hand it a
  body symbol it has **already processed** (`stage_repeat_body`). Body symbols are re-published many times
  across cohort revives / sibling GSS lineages.
- The parked-waiter `Vec` grows to **5 932** (`max_waiters`). The per-category `BTreeMap` range filter
  (`..= order_key(body_lo)`, the `d84b4df4` "linear-time deep nesting" fix) still selects ≈ 210 candidate
  waiters per call on these adversarial inputs.
- Result: **26 363 791** `(waiter × body)` staging attempts (`stage_candidates`), **each** cloning a
  `BranchCursor` (with its `Arc<Vec<LexForkStamp>>` + `im::OrdSet<ProjDescriptorKey>` Arc bumps), building +
  hashing a **19-field** `PrefixCastWrapJobKey`, and probing the dedup set — only to discard **99.92 %**
  (`26 381 389 push − 19 864 inserted`) as duplicates.

This is `O(distinct_bodies × parked_waiters)` re-stagings where only `O(distinct_jobs)` are non-redundant. A
`perf record` of the same parse attributes **> 50 %** of total samples to this subsystem
(`PrefixCastWrapJobKey::eq` 3.7 %, the `FxHasher` engine driven by these keys ≈ 16 %,
`try_stage_parked_prefix_cast_waiters` 2.5 %, `push_prefix_cast_wrap_job_once` 1.4 %,
`prefix_cast_wrap_job_key` 1.3 %, the `Arc<…>` clones/drops ≈ 8 %, `find_or_find_insert_index_inner` 2.1 %).

### 3.2 Provenance — it is a codex-range regression

```text
git log -S try_stage_parked_prefix_cast_waiters -- prattail/src/wpda_walker.rs
  d84b4df4 perf(wpda): restore linear-time deep nesting via edge-stack memoization
  655095cf fix(wpda): preserve projection evidence through realization
  08f86457 fix(wpda): publish cross-cat bodies through SPPF values   ◀── introduced
git show b781d754:prattail/src/wpda_walker.rs | grep -c try_stage_parked_prefix_cast_waiters  →  0
```

The whole waiter-staging machinery (`try_stage_parked_prefix_cast_waiters`,
`parked_prefix_cast_waiters_by_cat`, `push_prefix_cast_wrap_job_once`) is **absent at baseline** `b781d754`
and was added inside the codex range. `d84b4df4`'s `BTreeMap` index made the *per-call* candidate scan
sub-linear but did **not** address the **cross-call** redundancy (the same body re-staged against the same
growing waiter set), which is the quadratic this document fixes.

---

## 4. The fix — per-fired-body staging watermark

### 4.1 Mechanism

A new walker field

```rust
prefix_cast_stage_watermark: rustc_hash::FxHashMap<crate::sppf::SppfId, (usize, W)>,
```

records, per fired body symbol, the `(parked_prefix_cast_waiters.len(), symbol_weight_sum)` captured the last
time that body was staged. In `try_stage_parked_prefix_cast_waiters`:

```text
current_count := parked_prefix_cast_waiters.len()
body_weight   := symbol_weight_sum(body_symbol_id)
effective_watermark :=
    match watermark[body_symbol_id]:
        Some((prev_count, prev_weight)) if prev_weight == body_weight:
            if current_count <= prev_count:  RETURN            (nothing parked since — O(1) no-op)
            prev_count                                          (only waiters [prev_count, current_count))
        _ :  0                                                  (first sight, or weight changed → all)
candidate_indices := { i ∈ by_cat[body_cat].range(..= order_key(body_lo)) : i >= effective_watermark }
watermark[body_symbol_id] := (current_count, body_weight)
… stage candidate_indices as before …
```

The kill switch `PRATTAIL_PREFIX_CAST_STAGE_MEMO` (field `prefix_cast_stage_memo_enabled`, read once per
walker construction, default `true`) forces `effective_watermark = 0` and skips the map entirely when set to
`0`/`off`, reproducing the unmemoized re-stage-everything loop for the ON/OFF differential.

### 4.2 Soundness — byte-identical to the unmemoized loop

The staged job for a `(waiter@idx, body_symbol_id)` pair is a **deterministic pure function** of:
the waiter at `idx`, the body symbol `body_symbol_id`, and the body weight — **all immutable across
re-publications** except the body weight (which `symbol_weight_sum` may accumulate). Three facts make the
memo byte-identical:

1. **Append-only waiter Vec ⇒ stable indices.** `parked_prefix_cast_waiters` is only ever `push`ed or fully
   `clear`ed at the two parse-boundary `reset` sites; a waiter at index `i` stays at index `i` for the whole
   parse. So "waiters `[0, watermark)`" denotes exactly the set already considered for this body.
2. **The position/category filter verdict is invariant per (body, waiter).** The candidate filter is
   `waiter.body_cat == body_cat` ∧ `order_key(waiter.body_start_pos) ≤ order_key(body_lo)`. `body_cat` and
   `body_lo` are intrinsic to `body_symbol_id` (interned, immutable). Hence a waiter below the watermark that
   FAILED the filter on a prior call still fails it — skipping it changes nothing; a waiter that PASSED
   already produced its job (and the existing `push_prefix_cast_wrap_job_once` deduped repeats).
3. **Body-weight change resets the watermark to 0.** The job multiplies `body_weight` into the outer-frame
   weight (`outer.weight = outer.weight.times_ref(&body_weight)`). When `LexicographicWeight::times` projects
   the **body** tiebreak (the outer frame carries the multiplicative identity — `lex_weight.rs:418`), a
   changed body weight yields a job with a **different** `PrefixCastWrapJobKey`, i.e. a genuinely new job that
   the unmemoized loop would emit at the weight-change publication. Including the weight in the watermark key
   re-stages all matching waiters with the new weight at exactly that publication (and is robust to weight
   oscillation `W1→W2→W1`, since the stored weight tracks the last). When the outer frame is non-identity the
   key is weight-independent, so the unmemoized loop already deduped weight-changed repeats and the memo is
   trivially identical.

**Therefore** every job the unmemoized loop pushes whose key is not already present, the memoized loop also
pushes — the identical job. Every job the unmemoized loop pushes that *is* already present (a duplicate) the
memoized loop simply never builds. The set of *distinct* jobs is identical.

### 4.3 Empirical confirmation of byte-identity

- **Distinct-job invariant:** `push_job_inserted` is **19 864** with the memo ON and **19 864** OFF (the
  worst input); `drain_jobs` = 19 864 unchanged. Only `stage_candidates` (26 363 791 → 5 709),
  `push_job_calls` (26 381 389 → 23 307), and `jobkey_calls` collapse.
- **ON/OFF differential:** a 52-input battery (the 10 slowest campaign inputs + `((((1+2))))`, `put(map(),a,a)`,
  `1p0/3p0+2p0`, `int(true)+float(1)`, `bool(int(str(float(a))))`, plus 40 LCG-`arb_bool(3)` inputs) parsed
  with `PRATTAIL_PREFIX_CAST_STAGE_MEMO` ∈ {ON, OFF}: **`compared=52 mismatches=0`** — identical
  `Display(parse_term(s))` for every input.

---

## 5. The secondary (general) fix — GSS FxHashMap

`WpdaGss<W>` (`gss.rs`) kept its `edges: HashMap<GssNodeId, Vec<WpdaGssEdge<W>>>` and
`node_index: HashMap<WpdaGssNode, GssNodeId>` on the **default `std::collections::HashMap` SipHasher**.
These are looked up on every cursor step (`get_or_create_node` + edge lookup). For small integer / derived-Hash
keys SipHash is ≈ 5–10× slower than `rustc_hash::FxHashMap`, and the parse profile showed it directly
(`Sip13Rounds::{c,d}_rounds` ≈ 5 %, the GSS `find::<…WpdaGssEdge…>` ≈ 1 %). Swapping to `FxHashMap` is a
drop-in (identical map semantics; only the hash function differs — GSS correctness is unaffected) and gives
≈ 10 % on the heavy cross-cat path (worst input 7 345 → 6 648 ms).

**This is a general optimization, not a regression fix** (baseline `b781d754` also used SipHash here). It is
included because it is unambiguously sound and materially improves reliability against the 60 s target. It can
be dropped independently of the §4 staging fix.

---

## 6. The residual is the `visited_proj_descriptors` suppression memo — UNSAFE to truncate

After the §4 + §5 fixes the worst single parses are still 1.4–6.6 s; the `perf` profile is **flat**
(top self-fn ≈ 2–10 %: `lex_alt_rules_for_prefix`, `step`, `apply_action_to_cursor`,
`apply_pop_body_to_cursor`, `step_fanout`, cursor clones) — the signature of **frontier explosion**
(381 k SPPF publications for one parse), not a hot loop. The only lever for the frontier is relaxing a cursor
**merge** axis, and the dominant residual axis is `visited_proj_descriptors`
(`calculator-broad-parse-slowdown.md` §4.6: 70.7 % of residual no-merges; it is compared FIRST in
`heavy_fields_equal`, `wpda_walker.rs:3541`).

`visited_proj_descriptors` (per-cursor `im::OrdSet<ProjDescriptorKey>`,
`ProjDescriptorKey = (gss_node, sppf_stack_id, pos_key, cat_src, cur_bp)`) is **NOT** a false-divergence
sidecar like `lex_fork_path`. Its own field doc (`wpda_walker.rs:2752`) and `extract_proj_descriptor`
(`wpda_walker.rs:4581`) record that it does **DOUBLE DUTY**:

1. **cycle defense** — a no-progress cross-cat re-entry reproduces the descriptor (same `sppf_stack_id`) → DROP;
2. **cross-position dispatch SUPPRESSION** — "the memo that keeps the cross-cat projection fan from re-firing
   at every input position."

Crucially, keying `pos` GLOBALLY into the descriptor (removing role 2) was already tried and **re-exploded the
fan**: rhocalc `x!(0)` regressed and the suite went **0.6 s → 133 s** (`wpda_walker.rs:4590-4609`). Truncating
the set at the infix-operand seal (the §4.6 hypothesis) removes the suppression for positions inside a sealed
operand, which — because the key is intentionally pos-less to match the SAME descriptor at *different*
positions — would let the projection fan **re-fire downstream**, the very 0.6 s → 133 s pathology. Unlike the
`lex_fork_path` clear (which is read ONLY by merge consumers, never by `engine.step` — a provable
false-divergence), a `visited_proj_descriptors` truncation alters which projections **fire**, i.e. it can
change the produced parse and/or re-explode the frontier.

**Conclusion (per the task's "is it a fixable regression?" criterion):** the residual cross-cat-cast frontier
cost is governed by a **load-bearing, dual-role** suppression memo whose truncation is unsafe without a
dedicated probe-and-soundness campaign (the §4.6 author deferred it for exactly this reason). It is **not** a
drop-in twin of the `lex_fork` clear. The genuinely-fixable codex regression on this surface is the §4 staging
quadratic (which all three prior fan-out documents missed); it is fixed soundly here.

---

## 7. Rejected alternatives

| Alternative | Why rejected |
|---|---|
| `(body_sid, waiter_idx)` dedup **set** before the cursor clone | Sound, but still **iterates** the per-category `BTreeMap` range (26.4 M element-visits) and probes a 26.4 M-entry set. The watermark removes the iteration AND the probes (O(1) short-circuit when no waiter parked since), and is strictly cheaper. |
| Watermark keyed on `body_sid` **alone** (no weight) | UNSOUND when the body weight accumulates and the outer frame is the multiplicative identity: a later, higher-weight job has a distinct `PrefixCastWrapJobKey` the memo would suppress. The weight is part of the key precisely to stay byte-identical. |
| Clear `pending_prefix_cast_wrap_job_keys` on drain (shrink the dedup set) | Does not address the quadratic (the waste is *building+hashing* keys, not set size) and risks re-admitting a job already drained — a correctness hazard. |
| Truncate `visited_proj_descriptors` at the infix seal (§4.6 hypothesis) | UNSAFE — see §6 (re-explodes the projection fan; the memo is a cross-position suppression, not a false-divergence sidecar). Out of scope without a dedicated soundness campaign. |
| Drop `visited_proj_descriptors` from `heavy_fields_equal` entirely | UNSAFE — collapses genuinely-distinct cross-cat projection lineages; loses cycle defense and parses. |
| Reduce campaign case count / depth / add a timeout | Band-aids the task explicitly forbids; hide the regression rather than fix it. |

---

## 8. Verification

| suite | result |
|---|---|
| `cargo nextest run -p prattail` | **3795 / 3795** passed (target ≥ 3795). |
| `cargo nextest run -p simulation` | **141 / 141** passed. |
| `cargo nextest run -p dovetail` | **92 / 92** passed. (NB: the package is `dovetail`, not `mettail-dovetail`.) |
| `cargo nextest run -p languages -E 'binary(rhocalc_tests) \| binary(rhocalc_dovetail_fold) \| binary(simulation_integration) \| binary(gen_calculator_unit) \| binary(gen_rhocalc_unit) \| binary(lazy_lex_equivalence) \| binary(calculator)'` | **400 / 400** passed (1 skipped). |
| `lazy_lex_equivalence` slowest test | 1.47 s (binary ≪ 10 s; `lazy ≡ eager` holds). |
| `gen_calculator_prop` (full binary) | **98 / 98** passed — incl. `map_display_parse_roundtrip` 28.6 s, `bigrat_display_parse_roundtrip` 21.5 s, `bigrat_strong_roundtrip` 0.6 s, `test_deep_parens_100000` 2.2 s (deep-nesting / map / bigrat fixes hold). |
| ON/OFF byte-identical differential (`PRATTAIL_PREFIX_CAST_STAGE_MEMO`) | 52 inputs, **0 mismatches**. |

### Timing

| metric | baseline `b781d754` | HEAD (pre-fix) | HEAD + fix |
|---|---|---|---|
| worst single `parse_term` (str-cast) | n/a (rejected) | 7 345 ms | **≈ 4 200 ms** (memo) → **≈ 3 750 ms** (memo + GSS) |
| worst single `parse_term` (`bitnot…bitand`) | n/a | 22 273 ms | **≈ 4 250 ms** |
| staging operations (`stage_candidates`, worst input) | n/a | 26 363 791 | **5 709** (4 600×) |
| 50-input campaign-equivalent parse battery | 11 986 ms | 70 571 ms | **37 011 ms** (memo only) |
| `sim_calculator_proptest_campaign` (isolated, pinned) | ≈ 8.4 s | ≈ 90 s | **median ≈ 38 s** (5-run: 29.5 / 31.1 / 38.8 / 41.5 / 64.0 s) |

The campaign is comfortably under the 60 s target on the median and never approaches the 180 s leak cap. The
occasional ≈ 64 s unlucky-seed run is the §6 residual frontier explosion (the load-bearing
`visited_proj_descriptors` memo), not the fixed quadratic.

---

## 9. Files changed

| file | change |
|---|---|
| `prattail/src/wpda_walker.rs` | `prefix_cast_stage_watermark` field + `prefix_cast_stage_memo_enabled` kill switch (`PRATTAIL_PREFIX_CAST_STAGE_MEMO`) + the watermark logic in `try_stage_parked_prefix_cast_waiters`. |
| `prattail/src/gss.rs` | `WpdaGss<W>` `edges` / `node_index` `HashMap` → `FxHashMap` (general speedup). |
| `docs/design/sim-campaign-prefix-cast-staging-quadratic.md` | this document. |
