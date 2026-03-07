# PraTTaIL Decision Tree — Code Emission Architecture

| Metadata | Value                                                         |
|----------|---------------------------------------------------------------|
| Date     | 2026-03-06                                                    |
| Updated  | 2026-03-06                                                    |
| Source   | `prattail/src/decision_tree.rs`, `prattail/src/trampoline.rs` |

---

## Table of Contents

- [1 Overview](#1-overview)
- [2 API Boundary: dispatch_strategy()](#2-api-boundary-dispatch_strategy)
- [3 Trampoline Dispatch Paths](#3-trampoline-dispatch-paths)
- [4 Legacy A1+G1+B1 Fallback Path](#4-legacy-a1g1b1-fallback-path)
- [5 Diagnostic Dump Utilities](#5-diagnostic-dump-utilities)
- [6 Sprint 4 Additions](#6-sprint-4-additions)

---

## 1 Overview

The decision tree and the trampoline have a strict separation of concerns:

| Layer             | Responsibility                                                                                                                                     | File               |
|-------------------|----------------------------------------------------------------------------------------------------------------------------------------------------|--------------------|
| **Decision tree** | Compile-time trie analysis — determines *what* strategy to use                                                                                     | `decision_tree.rs` |
| **Trampoline**    | Codegen — determines *how* to emit Rust code (frame enums, continuation stacks, segment splitting, constructor calls, hot/cold function splitting) | `trampoline.rs`    |

The decision tree **cannot** produce parser code because it has no knowledge
of the trampoline's continuation-passing architecture (frame variants,
`'drive`/`'unwind` loops, `Cell<Vec<Frame_Cat>>` pooling, etc.). Conversely,
the trampoline does not re-derive prefix structure -- it queries the tree
for a pre-computed answer.

The API boundary between the two layers is a single method:
`CategoryDecisionTree::dispatch_strategy()`.

---

## 2 API Boundary: dispatch_strategy()

```rust
pub fn dispatch_strategy(
    &self,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> DispatchStrategy
```

`DispatchStrategy` has four variants:

| Variant                                                              | Meaning                                                                                            | Trampoline Action                                          |
|----------------------------------------------------------------------|----------------------------------------------------------------------------------------------------|------------------------------------------------------------|
| `NotPresent`                                                         | Token not in trie -- no RD rule dispatches on it                                                   | Skip; fall through to single-rule handler                  |
| `Singleton { rule_label }`                                           | Exactly one rule dispatches on this token                                                          | Fall through to single-rule handler (same as `NotPresent`) |
| `DisjointSuffix { shared_prefix_len, shared_terminals, suffix_map }` | Multiple rules share this token but have pairwise-disjoint suffixes after a shared terminal prefix | Deterministic multi-arm match (no backtracking)            |
| `NfaTryAll { rule_labels, shared_prefix_len, shared_terminals }`     | Multiple rules share this token and suffixes overlap                                               | NFA try-all with save/restore                              |

This method subsumes the following ad-hoc analyses that preceded the
decision tree:

| Ad-hoc Function                            | What It Did                      | Subsumed By                                     |
|--------------------------------------------|----------------------------------|-------------------------------------------------|
| `compute_shared_terminal_prefix()` (A1)    | Shared terminal prefix detection | `shared_prefix_len` + `shared_terminals` fields |
| `second_token_lookahead()` (B1)            | Depth-2 disjoint-child check     | `DisjointSuffix` with `shared_prefix_len == 0`  |
| `suffix_disjointness_check()` (G1 Phase 2) | Disjoint FIRST sets after prefix | `DisjointSuffix`                                |
| `group_rd_by_dispatch_token()`             | Grouping rules by first token    | Implicit in trie structure                      |
| `is_deterministic_fallback_dead()`         | Dead-rule detection              | `NotPresent`                                    |

---

## 3 Trampoline Dispatch Paths

The trampoline queries `dispatch_strategy()` inside `write_rd_handlers_trampoline`
when a dispatch token group has 2+ inlineable rules and no frame-pushing
rules. Four paths result:

### 3.1 DisjointSuffix (when `!needs_nfa_spillover`)

Deterministic dispatch. The trampoline:

1. Emits `expect_token` calls for each shared terminal in `shared_terminals`.
2. Emits a `match &tokens[*pos].0` on the suffix token.
3. Each match arm calls the corresponding rule handler directly (no
   save/restore). Coverage instrumentation is emitted per arm when
   `emit_coverage` is set.

This path **returns immediately** -- no fallback to NFA try-all.

### 3.2 NfaTryAll (shared_prefix_len > 0)

The decision tree reports overlapping suffixes but a non-trivial shared prefix.
The trampoline:

1. Uses the DT-provided `shared_prefix_len` (instead of calling
   `compute_shared_terminal_prefix()`).
2. Tries **G1 suffix disjointness** (`suffix_disjointness_check()` with FIRST
   set expansion) as a refinement -- the trie operates on terminal bytes only,
   so FIRST set expansion at nonterminal boundaries may resolve overlaps the
   trie cannot prove disjoint. If G1 succeeds, emits deterministic match arms
   and returns.
3. Falls through to NFA try-all with hot/cold function splitting
   (`format_nfa_result_selection_arm()`).

### 3.3 NfaTryAll (shared_prefix_len == 0)

No shared prefix. The trampoline:

1. Tries **G1** (suffix disjointness at skip=1). Returns on success.
2. Tries **B1** (`second_token_lookahead()`) for depth-2 disjoint-child
   disambiguation. Returns on success.
3. Falls through to NFA try-all with hot/cold splitting.

### 3.4 Singleton / NotPresent

These fall through to the trampoline's single-rule handler path (same
path used when `decision_tree: None`). No special DT-driven codegen
is needed since there is at most one rule to dispatch.

### 3.5 DisjointSuffix with needs_nfa_spillover

When `needs_nfa_spillover` is true, the `DisjointSuffix` match arm
falls through to NFA try-all. Spillover requires all alternatives to
be tried for semantic disambiguation (e.g., cast rules), making
deterministic single-arm dispatch incorrect.

---

## 4 Legacy A1+G1+B1 Fallback Path

The legacy dispatch path is retained for two cases:

1. **Recovery parsers** (`decision_tree: None`). Recovery codegen does not
   build decision trees; it uses the ad-hoc functions directly.
2. **NfaTryAll refinement**. G1 (FIRST set expansion at nonterminal
   boundaries) and B1 (second-token lookahead) may further disambiguate
   cases the trie conservatively reports as `NfaTryAll`. These functions
   use `FirstItem`-based FIRST sets rather than terminal-byte paths,
   giving them resolution power the trie lacks.

The legacy path is gated by `config.optimization_gates.left_factoring`
and only fires when `frame_pushing.is_empty() && inlineable.len() >= 2`.
Functions used: `compute_shared_terminal_prefix()`,
`suffix_disjointness_check()`, `second_token_lookahead()`,
`compute_group_complexity()`.

---

## 5 Diagnostic Dump Utilities

Two functions in `decision_tree.rs` produce **human-readable summaries**
for `PRATTAIL_DUMP_PARSER` debugging. They are NOT codegen outputs and are
NOT consumed by the trampoline.

### 5.1 emit_match_arms()

```rust
pub fn emit_match_arms(
    tree: &CategoryDecisionTree,
    _token_ids: &TokenIdMap,
    buf: &mut String,
)
```

Writes a textual summary of the trie's (path, action) pairs grouped by
dispatch token, with nested depth levels for shared prefixes. Actions
are rendered as comment-style labels (`/* COMMIT: RuleLabel */`,
`/* AMBIGUOUS: N candidates */`, etc.).

### 5.2 emit_flat_table()

```rust
pub fn emit_flat_table(
    tree: &CategoryDecisionTree,
    _token_ids: &TokenIdMap,
    buf: &mut String,
)
```

Writes a textual summary of the trie's flat-state representation:
transition pairs (`DISPATCH_TABLE_CAT`), state metadata
(`STATE_META_CAT`), and action tags.

### 5.3 Supporting types (test-only)

The following are `#[cfg(test)]` only and exist to validate the dump
utilities, not for production dispatch:

| Item                         | Purpose                                     |
|------------------------------|---------------------------------------------|
| `FLAT_TABLE_THRESHOLD` (256) | Threshold for choosing between dump formats |
| `EmissionStrategy` enum      | `MatchArms` vs `FlatTable`                  |
| `emission_strategy()`        | Selects dump format based on `total_states` |

---

## 6 Sprint 4 Additions

### 6.1 D07 Coverage Instrumentation

`TrampolineConfig.emit_coverage: bool` (activated by `PRATTAIL_COVERAGE=1`
env var during code generation). When set, the trampoline emits at each
dispatch arm:

```rust
#[cfg(feature = "parser-coverage")] __coverage::record("Cat", path_id);
```

The `__coverage` module is emitted by `pipeline.rs` (gated by the
`parser-coverage` feature) and provides `record()` / `dump()` functions
backed by a `Mutex<HashSet<(&'static str, u32)>>`. Test suites call
`__coverage::dump()` to report which dispatch paths were exercised.

### 6.2 Layer 10 Incremental Codegen

`.prattail-cache` file with version-tagged `IncrementalState`:

```rust
pub const CACHE_VERSION: u32 = 1;

pub struct IncrementalState {
    pub version: u32,
    pub category_hashes: HashMap<String, u64>,
    pub category_code: HashMap<String, String>,
}
```

- **Save**: `pipeline.rs` writes `IncrementalState` after codegen
  completes (best-effort; cache write failures are non-fatal).
- **Load**: `pipeline.rs` loads from `PRATTAIL_CACHE_DIR` env var at
  pipeline start. `is_valid()` checks `version == CACHE_VERSION`.
  `is_unchanged(cat, hash)` checks per-category content hashes for
  cache hits.
- **Invalidation**: Bump `CACHE_VERSION` when codegen logic changes in
  `trampoline.rs`, `recursive.rs`, `dispatch.rs`, or `pratt.rs`.

### 6.3 X06/X07 Composition Analysis

`build_decision_trees_from_spec()` runs a lightweight pipeline
(rule classification, TokenIdMap, FIRST sets, decision tree construction)
without full codegen, FOLLOW sets, or WFST construction. Used by
`compose_with_wfst()` to build decision trees for both source specs and
the merged spec, detecting:

- Common sublanguage (shared dispatch paths across source grammars)
- New ambiguities introduced by composition (paths that become
  `NfaTryAll` in the merged tree but were `Singleton`/`DisjointSuffix`
  in the source trees)
