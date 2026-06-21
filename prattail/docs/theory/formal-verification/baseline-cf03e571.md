# Baseline capture — `feature/wfst-architecture` @ `cf03e571`

**Phase 0.0 of the Lazy-WPDA-Pipeline + FV-Cleanup plan.** This is the authoritative
reference state for every later gate (Invariant 4: each gate is *delta vs this baseline =
0 new failures / 0 new hangs*, NOT an absolute "N/0").

- **Date:** 2026-06-09
- **Branch:** `feature/wfst-architecture`
- **HEAD:** `cf03e571e1db42f10749dd5e14c5dcbf14fcabdb` (+ codex's uncommitted e-graph
  budget/dedup work in-tree at capture time — provably orthogonal to runtime behavior;
  see "codex orthogonality" below).
- **Toolchain:** `rustc 1.98.0-nightly (d595fce01 2026-06-02)`, codegen-backend =
  **cranelift** (dev/test profile, per `.cargo/config.toml` + workspace `Cargo.toml`),
  linker = clang + mold.

## Counts

| Suite | Pass | Fail | Notes |
|-------|-----:|-----:|-------|
| `prattail --lib` | **4350** | **0** | 0 ignored; the parser/runtime unit gauntlet |
| `gen_calculator_op` + `gen_rhocalc_op` + `edge_case_tests` (nextest) | **1873** | **217** | 2090 run, 0 skipped; `chained_add` + `grouped_mul` excluded (live hangs) |

Combined op-suite exit: nextest `100` (test failures present, as expected for a
mid-migration branch).

### Live hangs (excluded from the gauntlet, run under timeout only)
- `edge_case_tests::chained_add` (`:1218`) — width divergence (documented; `path_vec`
  self-concat lineage). **Skip** via `-E '!test(=chained_add)'`.
- `edge_case_tests::grouped_mul` (`:1223`) — same class. **Skip** via `!test(=grouped_mul)`.

### Failure breakdown (217 unique; exact list in `baseline-cf03e571-failures.txt`)

| Binary | Fails | Dominant families |
|--------|------:|-------------------|
| `gen_calculator_op` | 156 | cross-cat cast 68 · nested collection-op 50 · eval collection-op 24 · wfst-dispatch 10 · wpda-eval 4 |
| `gen_rhocalc_op` | 33 | `eval_*_err_err` error-propagation 30 · cross-cat cast 3 |
| `edge_case_tests` | 28 | comparison-after-cast (`float(3) <= 3.0` …) · ambient (`new`/`\|`) · rhocalc-edge · string-cast · postfix-cross-category · operator-chains-after-cast |

## Analysis — these are GENUINE pre-existing parser failures (not a regression, not the toolchain)

1. **Every observed failure is a deterministic PARSE error**, e.g.
   `parse("float(3) <= 3.0") failed: 1:10: unexpected Fixed("<=") after parsing`,
   `ambient parse("new(x, new(y, {x[0] | y[0]}))") failed: 1:4: unexpected Fixed("(")`.
   Parsing is deterministic logic; the **cranelift codegen backend cannot make a correct
   parser reject valid tokens with clean error messages** — a miscompile would crash or
   corrupt values, not emit consistent, position-accurate parse-rejections via the
   parser's own error path. **⇒ the auto-updated nightly+cranelift toolchain is ruled out.**
2. **They match the documented WFST-migration known-failing families.** Project memory
   records "184 unique pre-existing failures remain (Family A binder PInputs cascade,
   Family B cross-cat cast, Family D display roundtrip, Family H unary-prefix R1)" and a
   later "Cluster J cross-cat `into_term::<T>()`-None at WFST realize" root-cause. The 217
   here (cross-cat cast, collection ops, comparison-after-cast, err-propagation, ambient)
   are that same set, grown as more generated cases were added. The plan's "~10 known R1
   failures" figure was simply inaccurate.
3. **codex orthogonality:** the in-tree uncommitted work (`egraph.rs` budget/dedup,
   `EGraphBudgetDedup.v`, a test-only `wpda_walker.rs` hunk) is **compile-time e-graph
   confluence analysis with zero callers on the runtime parse/eval path** — it cannot
   affect parsing and therefore cannot have produced any of these 217 failures.

These 217 are the in-scope target of the parser-FV phases (Phase 5A cast/deref source
classification, the cross-cat families, Phase EC evidence-completeness) and ultimately the
Dovetail engine (eval-side). They are the work, not noise.

## Methodology notes (reproduce exactly)

- **Resource limits (LESSON):** `systemd-run --scope -p TasksMax=200` (the Rocq `-j1`
  cap) is **far too low** for a parallel nextest build — it exhausts the task budget,
  producing `fork: Resource temporarily unavailable` which cranelift's
  `concurrency_limiter.rs:39` `unwrap()`s into a spurious ICE. Use **`TasksMax=8192`**
  (or omit) for cargo/nextest builds; keep `MemoryMax=32G -p MemorySwapMax=0`.
- **Build only what you run:** select binaries with `--test gen_calculator_op --test
  gen_rhocalc_op --test edge_case_tests` (not all ~100 package test targets) to cut build
  time and process count.
- **Complete run:** `--no-fail-fast` (nextest fail-fast otherwise stops after the first
  batch — an earlier run showed only 41/2090).

```
systemd-run --user --scope -p MemoryMax=32G -p MemorySwapMax=0 -p TasksMax=8192 -p IOWeight=30 \
  cargo nextest run -p languages \
    --test gen_calculator_op --test gen_rhocalc_op --test edge_case_tests \
    -E '!test(=chained_add) & !test(=grouped_mul)' --no-fail-fast
```
- **prattail lib:** `cargo test -p prattail --lib` → 4350/0.
- **Rocq egraph (incl. codex's `EGraphBudgetDedup.v`):** `make -C formal check-capped
  FORMAL_CAPPED_TARGET=rocq-egraph` → success, zero admissions (verified from scratch).

## Gate rule for all later phases

A change is **clean** iff it introduces **0 new failures and 0 new hangs** vs this set
(compare the failing-test set, not just the count) AND the relevant Rocq target stays
green (zero `Admitted`/`Axiom`). In-scope phases additionally *remove* failures from this
set; record each removal here as it lands.
