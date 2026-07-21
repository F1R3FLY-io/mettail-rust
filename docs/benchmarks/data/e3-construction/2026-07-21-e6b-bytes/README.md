# E-3 T-E6B / H4v2 — metric (i) retained-BYTES rendering (byte-emit re-run)

Window `2026-07-21T11:53:56Z..11:56:23Z` UTC, bin `bench_e3_construction`
(sha256 `6e80d242…` — the SAME binary as the sibling `2026-07-21-e6b/`
record) @ mettail `f65daef1`; store impl `5f442ff7`, harness `c4d3be6c`.
Deterministic re-run: `--warmup 0 --reps 1` (metric (i) is pure byte
arithmetic — never RSS, never wall — so one rep pins it; no `taskset`, no
settle needed). K=50 extension-ladder appends; r ∈ {100,250,500,1000}; both
store arms (pathmap / hashmap twin). The `--mode wb-gate` equivalence gate ran
green (4/4 cases) at every r before its e6b cells.

This record **closes sub-metric (i)** for the `f65daef1` measurement — the one
sub-metric the sibling `2026-07-21-e6b/` record left "NOT RENDERED". It does
NOT overwrite that record (which remains authoritative for (ii) and (iii)); it
appends the (i) rendering the sibling deferred.

## Provenance finding — the bytes were ALWAYS emitted (no harness gap)

The sibling record's README/`e6b_summary.json` reported (i) as a "harness gap"
— "the bench emitted `store_entries` (a COUNT) but not the retained-*bytes*
field". **That characterization was an analysis-rendering miss, not a harness
emission gap.** The harness has emitted the byte quantity all along:

- The store (`rholang-codegen/src/rho_net_fragment_store.rs`, `5f442ff7`)
  computes it in `ladder_accounting` → `LadderAccounting { retained_fragment_bytes,
  whole_artifact_bytes, .. }` — Σ of `bytes().len()` deduped by `Arc::as_ptr`
  identity (treatment) vs. Σ over every snapshot of every entry's length
  (per-variant whole-artifact baseline). Never RSS.
- The bin (`rholang-runtime/src/bin/bench_e3_construction.rs`, `c4d3be6c`)
  serialises them on the terminal **`e6b_rep` summary line** of every cell:
  `retained_fragment_bytes`, `whole_artifact_bytes`, `retained_lt_whole`.
- The sibling `2026-07-21-e6b/e6b_r*_*.jsonl` files **already contain** those
  fields on their `e6b_rep` lines (the prior analysis read only the per-append
  `e6b` cell lines, which carry `store_entries`, and never parsed the summary
  line). This byte-emit re-run confirms the values are **byte-identical** to
  the committed 30-rep data (determinism cross-check below).

Consequently **no harness edit was required** to render (i); emitting a second
`retained_bytes` alias would only duplicate `retained_fragment_bytes`. The
`5f442ff7`/`c4d3be6c` code is unchanged.

## Metric (i) verdict — HOLDS at every r (strict `<`, both arms)

`retained_fragment_bytes < whole_artifact_bytes` across the K=50 ladder:

| r    | retained_bytes | whole_artifact_bytes | Δ (whole−retained) | ratio  | savings | (i) `<` |
|-----:|---------------:|---------------------:|-------------------:|-------:|--------:|:-------:|
| 100  | 25,692         | 682,812              | 657,120            | 26.58× | 96.24%  | HOLDS   |
| 250  | 41,742         | 1,501,362            | 1,459,620          | 35.97× | 97.22%  | HOLDS   |
| 500  | 68,492         | 2,865,612            | 2,797,120          | 41.84× | 97.61%  | HOLDS   |
| 1000 | 123,143        | 5,646,438            | 5,523,295          | 45.85× | 97.82%  | HOLDS   |

Both store arms are byte-identical on `retained_fragment_bytes` and
`whole_artifact_bytes` at every r (the (iii) arms differ only in container
operations; the retained-byte accounting is arm-invariant — the harness test
`e6b_arms_agree_on_every_deterministic_component` pins this). The margin is
strict and **grows with r** (26.58× → 45.85×).

## Mechanism — honest attribution (across-snapshot Arc-sharing, not key sharing)

Metric (i) deduplicates by `Arc` identity across the **51-snapshot ladder**
(base + one CoW snapshot per append). The observed counters:

| r    | snapshots | fragment_refs | distinct_frags | dedup_hits | content_dedup_hits |
|-----:|----------:|--------------:|---------------:|-----------:|-------------------:|
| 100  | 51        | 6,426         | 251            | 6,175      | 0                  |
| 250  | 51        | 14,076        | 401            | 13,675     | 0                  |
| 500  | 51        | 26,826        | 651            | 26,175     | 0                  |
| 1000 | 51        | 52,326        | 1,151          | 51,175     | 0                  |

Exact arithmetic (both arms): `distinct_fragments = r + 151` = the base's
`r + 1` fragments **plus exactly 3 new `Arc` allocations per append × 50** (the
appended rule's own fragment + the one recomputed dirty-group sibling + the new
manifest); `fragment_refs = 51·(r+1) + 1275`; `dedup_hits = refs − distinct`.

The dichotomy the sibling note anticipated ("distinct rule-ids → distinct keys
→ Arc-identity dedup cannot fire → any byte difference is fragment-vs-whole
GRANULARITY, not dedup") needs one honest correction. Two independent axes exist,
and they land on opposite sides:

- **Cross-key content sharing** — DOES NOT fire. `content_dedup_hits = 0` at
  every r (no two distinct-key fragments are byte-equal), and `store_entries`
  is 1.00× between arms (no key collisions). The sibling note is correct here.
- **Across-snapshot `Arc`-identity sharing** — FIRES MASSIVELY. `dedup_hits`
  is 6,175 → 51,175: each append re-taints only 3 `Arc`s, so every unchanged
  fragment's `Arc` persists (CoW) across all subsequent snapshots and is
  counted **once** in `retained_fragment_bytes`, whereas `whole_artifact_bytes`
  re-counts it in every snapshot. This is the axis metric (i) actually measures,
  and it is the source of the strict `<`.

So (i)'s strict `<` holds by **across-snapshot CoW `Arc`-identity dedup**, which
the per-rule fragment granularity (quarantining the fingerprint-dependent
manifest from the per-rule fragments) is precisely what *enables*: fine-grained
fragments ⇒ only 3 `Arc`s change per append ⇒ the rest share by identity across
snapshots. Granularity and dedup are not alternatives here; the granularity is
the mechanism by which the dedup fires. It is **not** a mere fragment-vs-whole
size artifact with dedup absent — dedup is present and dominant.

## Determinism cross-check (reps=1 vs. the committed reps=30 record)

Every cell's `(retained_fragment_bytes, whole_artifact_bytes)` in this reps=1
re-run is byte-identical to the corresponding `e6b_rep` summary in the sibling
`2026-07-21-e6b/` reps=30 record (all 8 cells, both arms). (i) is deterministic;
one rep suffices.

## Files

- `e6b_r{r}_{pathmap,hashmap}.jsonl` — 1 header + 50 per-append `e6b` cells + 1
  `e6b_rep` summary line (carrying the (i) bytes) per file.
- `e6b_wb_gate_r{r}.jsonl` — the equivalence gate (4 cases, all `pass:true`) run
  before each r's e6b cells.
- `e6b_summary.json` — the machine-readable (i) rendering.
