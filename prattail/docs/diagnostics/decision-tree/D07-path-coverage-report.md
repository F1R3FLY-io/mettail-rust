# D07: path-coverage-report

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

Reports the coverage ratio of trie paths after a test suite run. D07 identifies
which dispatch paths in the PathMap decision trie were exercised by tests and
which remain untested. Untested paths represent grammar dispatch routes that have
no corresponding test input, meaning regressions along those paths would go
undetected.

This diagnostic is **informational** (Note severity) and **opt-in**: it is
activated by setting the `PRATTAIL_COVERAGE=1` environment variable. When
disabled, no coverage tracking overhead is incurred and no D07 diagnostics are
emitted.

## 2 Trigger Conditions

A D07 diagnostic is emitted when **all** of the following hold:

1. The `PRATTAIL_COVERAGE=1` environment variable is set.
2. `coverage_report()` is called with a `CategoryDecisionTree` and a
   `HashSet<Vec<u8>>` of covered path bytes.
3. At least one trie path in the category is **not** present in the covered set.

If all paths are covered, no D07 diagnostic is emitted for that category (the
test suite fully exercises the dispatch trie).

## 3 Coverage Tracking Mechanism

### 3.1 Enabling Coverage

Coverage tracking requires two conditions:

1. **Code generation time:** The `PRATTAIL_COVERAGE=1` environment variable must
   be set when the parser is generated (i.e., during `cargo build` or
   `cargo test`). This causes the pipeline (`pipeline.rs:1146`) to set
   `emit_coverage = true` and emit the `__coverage` module and per-arm
   instrumentation calls into the generated parser source.

2. **Compile time:** The `parser-coverage` feature must be enabled in
   `languages/Cargo.toml` (line 19: `parser-coverage = []`). All instrumentation
   calls are gated by `#[cfg(feature = "parser-coverage")]`, so without this
   feature the instrumentation compiles to nothing and incurs zero overhead.

### 3.2 Generated `__coverage` Module

When `PRATTAIL_COVERAGE=1` is set, the pipeline emits the following module into
the generated parser (`pipeline.rs:1876-1895`):

```rust
#[cfg(feature = "parser-coverage")]
mod __coverage {
    use std::sync::Mutex;
    use std::collections::HashSet;
    static COVERED: Mutex<HashSet<(&'static str, u32)>> = Mutex::new(HashSet::new());
    pub fn record(cat: &'static str, path_id: u32) {
        if let Ok(mut set) = COVERED.lock() { set.insert((cat, path_id)); }
    }
    pub fn dump() -> HashSet<(String, u32)> {
        COVERED.lock().map(|set|
            set.iter().map(|(c, id)| (c.to_string(), *id)).collect()
        ).unwrap_or_default()
    }
    pub fn reset() {
        if let Ok(mut set) = COVERED.lock() { set.clear(); }
    }
}
```

The module provides three functions:

| Function | Signature                                    | Purpose                                                                                  |
|----------|----------------------------------------------|------------------------------------------------------------------------------------------|
| `record` | `fn record(cat: &'static str, path_id: u32)` | Called at each dispatch arm; inserts `(category, path_id)` into the global `COVERED` set |
| `dump`   | `fn dump() -> HashSet<(String, u32)>`        | Returns the set of all `(category_name, path_id)` pairs exercised so far                 |
| `reset`  | `fn reset()`                                 | Clears the coverage set (useful between test runs)                                       |

### 3.3 Coverage Path Counter

Each category maintains a monotonic `u32` counter during codegen
(`trampoline.rs:2952-2953`):

```rust
let mut coverage_path_counter: u32 = 0;
```

Every dispatch arm that is emitted consumes and increments this counter. The
resulting `path_id` is unique within the category and is baked into the generated
`__coverage::record()` call as a literal. The counter is passed as
`&mut coverage_path_counter` through the dispatch-arm emission functions
(`trampoline.rs:500`).

### 3.4 Instrumentation Points

Coverage calls are emitted at four dispatch-arm sites in `trampoline.rs`:

| Site               | Line(s) | Dispatch Strategy                                                        | Description                                                            |
|--------------------|---------|--------------------------------------------------------------------------|------------------------------------------------------------------------|
| DisjointSuffix     | 580-587 | `DispatchStrategy::DisjointSuffix`                                       | Deterministic trie dispatch; shared prefix consumed, then suffix match |
| NfaTryAll + G1     | 686-693 | `DispatchStrategy::NfaTryAll` with `suffix_disjointness_check()` success | NFA overlap resolved by FIRST set suffix analysis                      |
| NfaTryAll + B1     | 779-786 | `DispatchStrategy::NfaTryAll` with `second_token_lookahead()` success    | NFA overlap resolved by two-token lookahead                            |
| NfaTryAll fallback | 864-871 | `DispatchStrategy::NfaTryAll` (G1/B1 both failed)                        | Full NFA try-all with save/restore                                     |

Each site follows the same pattern:

```rust
let path_id = *coverage_path_counter;
*coverage_path_counter += 1;
// ... emit Token::Variant => { ...
if config.emit_coverage {
    write!(buf,
        "#[cfg(feature = \"parser-coverage\")] __coverage::record(\"{cat}\", {path_id});",
    ).unwrap();
}
```

### 3.5 Pipeline Diagnostic

When coverage is enabled and at least one category has trie states, the pipeline
emits a D07 note listing the instrumented categories (`pipeline.rs:1898-1917`):

```
note[D07] (MyLang): 3 categories instrumented for coverage tracking: [Expr, Stmt, Pat]
  = hint: run tests with `parser-coverage` feature enabled, then call __coverage::dump()
```

## 4 Output Format

### 4.1 Message Structure

```
note[D07] (GrammarName): coverage: <covered>/<total> trie paths tested (<pct>%), <uncovered> untested
  = hint: set PRATTAIL_COVERAGE=1 and run tests to collect path coverage
```

### 4.2 Example: Partial Coverage

A grammar with 12 trie paths, 9 tested:

```
note[D07] (MyLang): coverage: 9/12 trie paths tested (75%), 3 untested
  = hint: set PRATTAIL_COVERAGE=1 and run tests to collect path coverage
```

### 4.3 Example: Minimal Coverage

A grammar where only basic rules are tested:

```
note[D07] (Rho): coverage: 3/20 trie paths tested (15%), 17 untested
  = hint: set PRATTAIL_COVERAGE=1 and run tests to collect path coverage
```

### 4.4 Full Coverage (No Diagnostic)

When all paths are covered, D07 does not fire:

```
(no output — all 12/12 paths tested)
```

## 5 Coverage Visualization

The following diagram shows the relationship between trie paths and coverage:

```
    root
     │
     ├── 0x00 (KwFloat) ──── 0x01 (LParen)
     │                         │
     │                         ├── 0x80 (Ident) ──▶ Commit: FloatId    [COVERED]
     │                         │
     │                         └── 0x82 (NT:Float) ──▶ Commit: IntToFloat [UNTESTED]
     │
     ├── 0x0C (KwIf) ──▶ Commit: IfThenElse                            [COVERED]
     │
     ├── 0x0F (KwLet) ──▶ Commit: LetIn                                [COVERED]
     │
     └── 0x10 (KwMatch) ──▶ Commit: MatchExpr                          [UNTESTED]

     coverage_paths():
       [0x00, 0x01, 0x80] → FloatId        ✓ covered
       [0x00, 0x01, 0x82] → IntToFloat     ✗ untested
       [0x0C]             → IfThenElse     ✓ covered
       [0x0F]             → LetIn          ✓ covered
       [0x10]             → MatchExpr      ✗ untested

     D07: coverage: 3/5 trie paths tested (60%), 2 untested
```

## 6 Source

### 6.1 Code Generation (Compile Time)

**Coverage check:** `pipeline.rs:1146`

```rust
let emit_coverage = std::env::var("PRATTAIL_COVERAGE").is_ok();
```

**`__coverage` module emission:** `pipeline.rs:1876-1895` — emits the
`record`/`dump`/`reset` module into the generated parser source, gated by
`#[cfg(feature = "parser-coverage")]`.

**D07 pipeline diagnostic:** `pipeline.rs:1898-1917` — emits a note listing
which categories were instrumented.

### 6.2 Instrumentation Emission (Codegen)

**Counter declaration:** `trampoline.rs:2952-2953`

```rust
let mut coverage_path_counter: u32 = 0;
```

**Instrumentation sites:** `trampoline.rs:580-587` (DisjointSuffix),
`trampoline.rs:686-693` (NfaTryAll+G1), `trampoline.rs:779-786` (NfaTryAll+B1),
`trampoline.rs:864-871` (NfaTryAll fallback).

**TrampolineConfig field:** `trampoline.rs:2193-2199`

```rust
pub emit_coverage: bool,
```

### 6.3 Static Analysis (Decision Tree)

**Function:** `coverage_paths()` in `prattail/src/decision_tree.rs`

```rust
pub fn coverage_paths(tree: &CategoryDecisionTree) -> Vec<CoveragePath>
```

Enumerates all `(path_bytes, action)` pairs across all trie segments, returning
a `CoveragePath` for each. This is the static-analysis complement to the runtime
instrumentation: it tells you how many paths *exist*, while `__coverage::dump()`
tells you which paths were *exercised*.

**Function:** `coverage_report()` in `prattail/src/decision_tree.rs`

```rust
pub fn coverage_report(
    tree: &CategoryDecisionTree,
    covered_paths: &HashSet<Vec<u8>>,
) -> Vec<TreeDiagnostic>
```

Compares enumerated trie paths against a covered set. If any paths are
uncovered, constructs a `TreeDiagnostic` with lint ID `"D07"` and severity
`Note`, including the `covered/total` ratio, percentage, and uncovered count.

### 6.4 Feature Gate

**`languages/Cargo.toml` line 19:**

```toml
parser-coverage = []
```

All runtime instrumentation is gated by `#[cfg(feature = "parser-coverage")]`.
Without this feature enabled at compile time, no coverage overhead is incurred
regardless of whether `PRATTAIL_COVERAGE=1` was set during code generation.

## 7 Usage

### 7.1 Enabling Coverage

Coverage requires two steps:

**Step 1: Generate instrumented parser code.** Set `PRATTAIL_COVERAGE=1` during
code generation (this triggers the pipeline to emit `__coverage::record()` calls
at each dispatch arm):

```bash
PRATTAIL_COVERAGE=1 cargo build --workspace
```

**Step 2: Compile and run tests with the `parser-coverage` feature.** This
activates the `#[cfg(feature = "parser-coverage")]` gates so the instrumentation
is compiled in:

```bash
cargo test --workspace --features parser-coverage
```

Both steps can be combined:

```bash
PRATTAIL_COVERAGE=1 cargo test --workspace --features parser-coverage
```

**Step 3: Retrieve coverage data.** After parsing some input, call
`__coverage::dump()` to get the set of exercised `(category, path_id)` pairs:

```rust
let covered: HashSet<(String, u32)> = __coverage::dump();
// e.g., {("Expr", 0), ("Expr", 3), ("Stmt", 1)}
```

Call `__coverage::reset()` between test runs to clear the accumulated set.

### 7.2 Interpreting Results

| Coverage | Assessment | Action                                        |
|----------|------------|-----------------------------------------------|
| 100%     | Excellent  | All dispatch paths exercised                  |
| 80-99%   | Good       | Review untested paths for edge cases          |
| 50-79%   | Fair       | Add tests for major untested rule families    |
| < 50%    | Poor       | Significant dispatch paths lack test coverage |

### 7.3 Identifying Untested Paths

To determine which specific paths are untested, use `coverage_paths()` directly
and filter for paths not in the covered set:

```rust
let all = decision_tree::coverage_paths(tree);
let untested: Vec<_> = all.iter()
    .filter(|p| !covered_paths.contains(&p.path_bytes))
    .collect();
for p in &untested {
    eprintln!("untested: segment={}, path={:?}, rule={:?}",
        p.segment_index, p.path_bytes, p.rule_label);
}
```

## 8 Related Lints

- [D01](D01-precision-ambiguity.md) -- Ambiguous paths are included in the
  coverage set; testing an ambiguous path exercises the NFA try-all dispatcher.
- [D03](D03-trie-unreachable-rule.md) -- Unreachable rules have no trie path
  and therefore cannot appear in coverage tracking. A rule flagged by both D03
  (unreachable) and missing from D07 coverage is expected.
- [D05](D05-decision-tree-summary.md) -- The `total_states` field in the summary
  correlates with the total number of coverage paths: each state is one
  coverable path.
