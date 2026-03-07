# PraTTaIL Decision Tree Module Map

| Field   | Value      |
|---------|------------|
| Date    | 2026-03-06 |
| Updated | 2026-03-06 |

---

## §1 Module Overview

`prattail/src/decision_tree.rs` (~3,100 lines) is the core module implementing
the PathMap decision tree for unified parse dispatch. It is declared in
`prattail/src/lib.rs` as `pub mod decision_tree`.

The decision tree encodes every syntactic rule as a byte-key path in a PathMap
trie, one trie per grammar category. At compile time the trampoline codegen
queries the tree to determine the optimal dispatch strategy for each category:
a single committed rule, a disjoint-suffix match table, or a full NFA try-all
fallback. This replaces ad-hoc FIRST-set switch generation (A1, B1, G1) with a
single, algebraically grounded structure that can be queried, diffed, composed,
and incrementally updated.

The module provides 10 analysis layers (D01-D09 diagnostics, X06/X07
composition, D07 coverage, and Layer 10 incremental hashing), an incremental
codegen cache (`IncrementalState` with `CACHE_VERSION` + binary load/save), and
a lightweight `build_decision_trees_from_spec()` entry point for contexts that
need decision trees without running the full codegen pipeline.

---

## §2 Data Flow Diagram

```
                          ┌──────────────────────────────────────────────────────────────────────────────┐
                          │                            pipeline.rs                                       │
                          │                                                                              │
                          │  ┌─────────────────────────────────────────────────────────────────────┐     │
                          │  │  Layer 10: IncrementalState load (.prattail-cache)                  │     │
                          │  └────────────────────────────────┬────────────────────────────────────┘     │
                          │                                   │                                          │
                          │                                   ▼                                          │
 ┌──────────────┐         │  ┌──────────────────────┐    ┌────────────────────────┐                      │
 │ ParserBundle │─────────┄─→│ DecisionTreeBuilder  │───→│ CategoryDecisionTree   │                      │
 │              │         │  │                      │    │                        │                      │
 │ rd_rules     │         │  │  build_all()         │    │  ┌──────────────────┐  │                      │
 │ cross_rules  │         │  │    ├ insert_rd       │    │  │ PathMap<Decision │  │                      │
 │ cast_rules   │         │  │    ├ insert_cross    │    │  │   Action> trie   │  │                      │
 │ first_sets   │         │  │    ├ insert_cast     │    │  │ per category     │  │                      │
 │ dead_rules   │         │  │    ├ psubtract dead  │    │  └──────────────────┘  │                      │
 │ token_ids    │         │  │    └ compute_stats   │    │                        │                      │
 └──────────────┘         │  └──────────────────────┘    └────────┬───────────────┘                      │
                          │                                       │                                      │
                          │                    ┌──────────────────┼──────────────────────┐               │
                          │                    │                  │                      │               │
                          │                    ▼                  ▼                      ▼               │
                          │  ┌─────────────────────┐  ┌──────────────────┐  ┌─────────────────────────┐  │
                          │  │ D01-D06, D08-D09    │  │ TrampolineConfig │  │ PipelineAnalysis        │  │
                          │  │ diagnostics         │  │   .decision_tree │  │   .decision_trees       │  │
                          │  │ (emitted to stderr) │  │                  │  │ (returned to caller)    │  │
                          │  └─────────────────────┘  └────────┬─────────┘  └─────────────────────────┘  │
                          │                                    │                                         │
                          │                                    ▼                                         │
                          │                           ┌────────────────┐                                 │
                          │                           │ D07 __coverage │                                 │
                          │                           │ module emission│                                 │
                          │                           └────────────────┘                                 │
                          │                                                                              │
                          │  ┌─────────────────────────────────────────────────────────────────────┐     │
                          │  │  Layer 10: IncrementalState save (.prattail-cache)                  │     │
                          │  └─────────────────────────────────────────────────────────────────────┘     │
                          └──────────────────────────────────────────────────────────────────────────────┘
                                                               │
                          ┌────────────────────────────────────┼────────────────────────────────────┐
                          │                                    │                                    │
                          ▼                                    ▼                                    ▼
             ┌──────────────────────────┐     ┌──────────────────────────────┐     ┌──────────────────────────┐
             │   trampoline.rs codegen  │     │      compose.rs              │     │    cost_benefit.rs       │
             │                          │     │                              │     │                          │
             │ dispatch_strategy()      │     │ build_decision_trees_from_   │     │ OptimizationGates:       │
             │   ├ DisjointSuffix path  │     │   spec() for X06/X07         │     │   .left_factoring        │
             │   │  → deterministic     │     │   pre/post-composition       │     │   .multi_token_lookahead │
             │   │    match arms        │     │   tree comparison            │     │   .backtracking_         │
             │   ├ NfaTryAll path       │     │                              │     │     elimination          │
             │   │  → save/restore      │     │ compose_with_wfst()          │     │                          │
             │   │    per alternative   │     │   → WfstCompositionResult:   │     │ Gates control legacy     │
             │   └ Singleton path       │     │     .source_a_trees          │     │ fallback when decision   │
             │     → unconditional      │     │     .source_b_trees          │     │ tree is absent           │
             │                          │     │     .merged_trees            │     │                          │
             │ D07 __coverage::record() │     │                              │     │                          │
             │ instrumentation at each  │     │                              │     │                          │
             │ dispatch resolution      │     │                              │     │                          │
             └──────────────────────────┘     └──────────────────────────────┘     └──────────────────────────┘
```

Data flows through five interconnected modules:

1. **`pipeline.rs`** orchestrates the build. After FIRST set augmentation, WFST
   construction, lint analysis, and dead rule collection, it creates a
   `DecisionTreeBuilder` and calls `build_all()` to produce per-category
   `CategoryDecisionTree` instances. It loads the previous `IncrementalState`
   from `.prattail-cache`, computes per-category content hashes via
   `category_content_hash()`, and skips codegen for categories whose hash is
   unchanged. The trees are threaded into `TrampolineConfig.decision_tree`
   (per category) and collected into `PipelineAnalysis.decision_trees`
   (returned to the macros crate). Pipeline also runs D01-D06, D08-D09
   diagnostics and emits the D07 `__coverage` module when
   `PRATTAIL_COVERAGE=1`.

2. **`decision_tree.rs`** is the core module (~3,100 lines). It provides:
   - `DecisionTreeBuilder` + `build_all()` for trie construction
   - `CategoryDecisionTree.dispatch_strategy()` as the primary query
   - `build_decision_trees_from_spec()` lightweight pipeline (no full codegen)
   - `IncrementalState` with `CACHE_VERSION`, binary `load()`/`save()`
   - 10 analysis layers: D01 precision ambiguity, D02 unresolvable ambiguity,
     D03 unreachable rules, D04 min lookahead, D05 depth/size, D06 WFST
     consistency, D07 coverage, D08 optimization suggestions, D09 conflict
     resolution, Layer 10 incremental hashing

3. **`trampoline.rs`** consumes `dispatch_strategy()` per token variant per
   category. For `DisjointSuffix`, it emits deterministic `match` arms with
   shared prefix extraction. For `NfaTryAll`, it emits save/restore with
   per-alternative try logic. For `Singleton`, it emits unconditional dispatch.
   D07 coverage instrumentation (`__coverage::record()`) is emitted at each
   dispatch resolution point when `TrampolineConfig.emit_coverage` is true.

4. **`compose.rs`** calls `build_decision_trees_from_spec()` three times in
   `compose_with_wfst()` to build decision trees for source grammar A, source
   grammar B, and the merged grammar. These populate the X06/X07 fields in
   `WfstCompositionResult` (`source_a_trees`, `source_b_trees`,
   `merged_trees`) for pre/post-composition tree comparison and structural
   diff analysis.

5. **`cost_benefit.rs`** provides `OptimizationGates` with three gates that
   control the legacy fallback path when a decision tree is absent:
   `left_factoring` (A1), `multi_token_lookahead` (B1), and
   `backtracking_elimination` (G1). When a `CategoryDecisionTree` is present,
   the DisjointSuffix path subsumes all three; when absent, these gates
   determine which ad-hoc analyses are applied.

---

## §3 Type Hierarchy

### PatternElement

Typed pre-encoding element representing one item in a syntactic rule's pattern:

| Variant       | Description                                            |
|---------------|--------------------------------------------------------|
| Terminal      | A concrete token (keyword, operator, delimiter)        |
| IdentCapture  | An identifier capture position                         |
| BinderCapture | A binder capture position                              |
| NonTerminal   | A reference to another category (recursive parse call) |
| OptionalStart | Beginning of an optional group `[` in the grammar      |
| OptionalEnd   | End of an optional group `]` in the grammar            |

### DecisionAction

Trie node value representing the outcome at a given path. Implements both
`Lattice` and `DistributiveLattice` for algebraic merging.

| Variant             | Description                                            |
|---------------------|--------------------------------------------------------|
| Commit              | Deterministic: exactly one rule matches at this prefix |
| Ambiguous           | Multiple rules share this prefix                       |
| NonterminalBoundary | Path reaches a nonterminal; dispatch must recurse      |

### AmbiguousCandidate

A candidate rule within an `Ambiguous` dispatch point:

| Field           | Type     | Description                                        |
|-----------------|----------|----------------------------------------------------|
| rule_label      | `String` | Label of the candidate rule                        |
| category        | `String` | Grammar category the rule belongs to               |
| weight          | `f64`    | WFST tropical weight for ordering                  |
| remaining_items | `usize`  | Items remaining after the shared prefix (NFA cost) |

### NTOption / NTKind

Options at a nonterminal boundary (segment split point):

| NTKind Variant | Description                  |
|----------------|------------------------------|
| NonTerminal    | Parse a nonterminal category |
| IdentCapture   | Capture an identifier        |
| BinderCapture  | Capture a binder identifier  |

`NTOption` carries `first_tokens` (FIRST set byte codes), `resume_segment`
(index into the segments vector for the continuation trie), and `weight`
(WFST tropical weight).

### CategoryDecisionTree

Per-category trie container:

| Field    | Type                           | Description                      |
|----------|--------------------------------|----------------------------------|
| segments | `Vec<PathMap<DecisionAction>>` | One PathMap trie per segment     |
| stats    | `TreeStats`                    | Computed statistics for the tree |

### DecisionTreeBuilder

Builds trees from pipeline data:

| Field           | Description                                    |
|-----------------|------------------------------------------------|
| token_ids       | Token-to-byte-ID mapping for trie key encoding |
| first_sets      | Precomputed FIRST sets per category            |
| category_id_map | Category name to numeric ID mapping            |
| dead_rules      | Set of rules determined dead by WFST analysis  |

### DispatchStrategy

Query result consumed by trampoline codegen:

| Variant        | Description                                             |
|----------------|---------------------------------------------------------|
| NotPresent     | No rules exist for this category (empty trie)           |
| Singleton      | Exactly one rule; emit unconditional dispatch           |
| DisjointSuffix | Multiple rules with disjoint token prefixes; emit match |
| NfaTryAll      | Ambiguous prefixes; fall back to NFA try-all dispatch   |

`DisjointSuffix` carries `shared_prefix_len`, `shared_terminals` (bytes),
`suffix_map` (token variant to rule label), and `rule_labels`.
`NfaTryAll` carries `rule_labels`, `shared_prefix_len`, and
`shared_terminals`.

### TreeStats

Statistics computed over the trie:

| Field               | Type    | Description                           |
|---------------------|---------|---------------------------------------|
| total_states        | `usize` | Total number of trie states           |
| deterministic_nodes | `usize` | States with a single Commit action    |
| ambiguous_nodes     | `usize` | States with an Ambiguous action       |
| max_depth           | `usize` | Maximum path length in the trie       |
| min_lookahead       | `usize` | Minimum tokens needed to disambiguate |

### TreeDiagnostic

Diagnostic output for lint and reporting:

| Field    | Type       | Description                                |
|----------|------------|--------------------------------------------|
| lint_id  | `String`   | Lint identifier (e.g., D01, D06)           |
| severity | `Severity` | Warning, error, or info                    |
| category | `String`   | Grammar category the diagnostic applies to |
| message  | `String`   | Human-readable diagnostic message          |
| hint     | `String`   | Suggested fix or additional context        |

### NTBoundaryInfo

Nonterminal boundary data used during pattern encoding:

Tracks the position and category of a nonterminal reference encountered
while encoding a rule's pattern into byte keys, enabling the builder to
insert `NonterminalBoundary` actions at the correct trie nodes.

### IncrementalState

Content-addressable caching for incremental codegen (Layer 10):

| Field           | Type                      | Description                            |
|-----------------|---------------------------|----------------------------------------|
| version         | `u32`                     | Cache format version (`CACHE_VERSION`) |
| category_hashes | `HashMap<String, u128>`   | Per-category content hashes            |
| category_code   | `HashMap<String, String>` | Cached generated code per category     |

Binary serialization format: `[version: u32][num_categories: u32]` followed by
per-category entries `[name_len: u32][name][hash: u128][code_len: u32][code]`.
A version mismatch causes the entire cache to be discarded.

Key methods:
- `is_valid()` -- checks `version == CACHE_VERSION`
- `is_unchanged(category, current_hash)` -- checks if the hash matches
- `record(category, hash)` -- stores the hash for a category
- `load(path)` / `save(path)` -- binary file I/O

---

## §4 Key Functions

### Pattern Construction

- **`pattern_from_rd_rule()`** -- Convert an `RDSyntaxItem` sequence to a
  `Vec<PatternElement>`. Maps each syntax item (terminal, capture, optional
  group boundary, nonterminal reference) to its typed `PatternElement` variant.

- **`encode_terminal_prefix()`** -- Encode `PatternElement` items as bytes
  until the first nonterminal is encountered. Returns the byte key prefix and
  the index at which encoding stopped (the nonterminal boundary).

### Trie Insertion

- **`insert_rd_rules()`** -- Insert all recursive-descent rules for a category
  into its PathMap trie. Each rule's pattern is encoded via
  `encode_terminal_prefix()` and the resulting byte key is inserted with a
  `Commit` action (or merged via lattice join if the key already exists).

- **`insert_cross_category_rules()`** -- Insert cross-category dispatch rules.
  These encode the dispatch token (the token that triggers a cross-category
  call) followed by the target category's FIRST set tokens.

- **`insert_cast_rules()`** -- Insert cast rules. Encodes the unique tokens
  that appear in the source category but not the target category, enabling
  the decision tree to distinguish cast dispatch from same-category dispatch.

### Master Entry Points

- **`build_all()`** -- Master entry point for pipeline-driven builds.
  Orchestrates the full trie build:
  1. Insert RD rules via `insert_rd_rules()`
  2. Insert cross-category rules via `insert_cross_category_rules()`
  3. Insert cast rules via `insert_cast_rules()`
  4. Remove dead rules via lattice `psubtract`
  5. Compute statistics via `compute_statistics()`

- **`build_decision_trees_from_spec()`** -- Lightweight entry point that builds
  decision trees from a `LanguageSpec` without running full codegen. Executes
  only: rule classification, `TokenIdMap` construction, FIRST set computation,
  and `DecisionTreeBuilder.build_all()`. Used by `compose_with_wfst()` for
  X06/X07 pre/post-composition tree comparison, and by any context requiring
  decision trees without a full pipeline run.

### Query

- **`dispatch_strategy()`** -- Primary query for the trampoline codegen.
  Examines the trie structure to determine the optimal dispatch. Subsumes:
  - `group_rd_by_dispatch_token()` (grouping by first byte)
  - `compute_shared_terminal_prefix()` (A1: single-child chains)
  - `second_token_lookahead()` (B1: depth-2 unique children)
  - `suffix_disjointness_check()` (G1 Phase 2: disjoint children after prefix)

  Returns `Singleton` if one rule, `DisjointSuffix` if all top-level branches
  are deterministic, `NfaTryAll` otherwise.

- **`dispatch_tokens()`** -- Returns all dispatch tokens present in the trie
  (the set of tokens that can initiate a parse in this category).

### Code Emission

- **`emit_match_arms()`** -- Generate `match` arms for `DisjointSuffix`
  dispatch. Each arm maps a token to the committed rule's handler call.
  (Stub for future codegen replacement.)

- **`emit_flat_table()`** -- Generate a flat lookup table for dispatch.
  (Stub for future codegen replacement.)

### Diagnostics (10 Analysis Layers)

- **`precision_ambiguity_reports()`** -- D01: reports categories with ambiguous
  nodes, indicating the grammar could benefit from refactoring for
  deterministic dispatch.

- **`unresolvable_ambiguity_reports()`** -- D02: reports ambiguous nodes at trie
  leaves (NT boundary truncated both paths), stronger than D01.

- **`unreachable_rule_detection()`** -- D03: detects rules inserted into the
  trie but unreachable via any live dispatch token.

- **`min_lookahead_report()`** -- D04: reports the minimum lookahead depth
  required to disambiguate all rules in a category.

- (D05 is implicit in `compute_statistics()` -- trie depth/size reporting.)

- **`wfst_consistency_check()`** -- D06: cross-checks the decision tree against
  the WFST to detect inconsistencies between compile-time predictions and the
  WFST's weight-based analysis.

- **`coverage_instrumentation()`** / **D07 diagnostics** -- D07: coverage path
  tracking. At codegen time, `trampoline.rs` emits `__coverage::record()`
  calls at each dispatch point. At test time, untested paths are reported as
  D07 diagnostics.

- **`optimization_suggestions()`** -- D08: suggests grammar transformations
  (left-factoring, token renaming) that would improve dispatch determinism.

- **`conflict_resolution_guidance()`** -- D09: provides actionable guidance for
  resolving trie conflicts (shared-prefix ambiguities).

- **Layer 10** (`IncrementalState`) -- Content-addressable per-category hashing
  for incremental codegen. Managed by `pipeline.rs` via `load()`/`save()`.

### Statistics and Hashing

- **`compute_statistics()`** -- Compute `TreeStats` by traversing the trie:
  counting states, classifying nodes as deterministic or ambiguous, measuring
  depth, and determining minimum lookahead.

- **`category_content_hash()`** -- Compute a content-addressable hash of a
  category's trie for incremental codegen. Two tries with identical structure
  and actions produce identical hashes regardless of insertion order.

---

## §5 Pipeline Integration

### Build Phase

The decision tree is built in `pipeline.rs` after:

1. FIRST set augmentation (with native literal tokens)
2. WFST construction
3. Lint analysis
4. Dead rule collection

This occurs at approximately line 1670 in the pipeline. The constructed trees
flow to three destinations:

```
                    CategoryDecisionTree (per category)
                                │
               ┌────────────────┼─────────────────┐
               │                │                 │
               ▼                ▼                 ▼
     TrampolineConfig   PipelineAnalysis   D01-D09 diagnostics
      .decision_tree     .decision_trees   (emitted to stderr)
```

### Trampoline Threading

Each category's tree is threaded into `TrampolineConfig` as:

```rust
pub decision_tree: Option<CategoryDecisionTree>,
```

The `Option` wrapper permits the trampoline codegen to degrade gracefully when
the tree is absent. When present, the trampoline queries
`dispatch_strategy()` per token variant to select the emission path. When
absent, the legacy path controlled by `OptimizationGates` fields
(`left_factoring`, `multi_token_lookahead`, `backtracking_elimination`) is
used instead.

### Incremental Cache

`pipeline.rs` manages the Layer 10 incremental cache:

1. **Load**: reads `.prattail-cache` from `$PRATTAIL_CACHE_DIR` via
   `IncrementalState::load()` at the start of codegen
2. **Hash**: computes `category_content_hash()` for each category's tree
3. **Compare**: `is_unchanged(category, hash)` checks if cached code is reusable
4. **Save**: writes the updated `IncrementalState` via `save()` at the end

### Coverage Module

When `PRATTAIL_COVERAGE=1`, `pipeline.rs` emits a `mod __coverage` module with
`record()` and `dump()` functions, gated by the `parser-coverage` feature.
`trampoline.rs` inserts `__coverage::record("Cat", path_id)` at each dispatch
resolution point. Untested paths are surfaced as D07 diagnostics at test time.

---

## §6 Composition Integration (X06/X07)

`compose.rs` uses the lightweight `build_decision_trees_from_spec()` entry
point to construct decision trees for grammar composition analysis:

```rust
pub fn compose_with_wfst(...) -> Result<WfstCompositionResult, ...> {
    let trees_a = build_decision_trees_from_spec(spec_a);      // source A
    let trees_b = build_decision_trees_from_spec(spec_b);      // source B
    let trees_merged = build_decision_trees_from_spec(&merged); // merged
    ...
    Ok(WfstCompositionResult {
        source_a_trees: trees_a,
        source_b_trees: trees_b,
        merged_trees:   trees_merged,
        ...
    })
}
```

The three sets of trees enable X06/X07 pre/post-composition structural diff:
comparing dispatch strategies, ambiguity counts, and lookahead depths before
and after composition to detect regressions or improvements.

---

## §7 Cost-Benefit Gate Interaction

`cost_benefit.rs` defines `OptimizationGates` with 11 boolean fields. Three
gates interact directly with the decision tree's dispatch path:

| Gate                       | ID | Legacy Analysis Replaced              |
|----------------------------|----|---------------------------------------|
| `left_factoring`           | A1 | `compute_shared_terminal_prefix()`    |
| `multi_token_lookahead`    | B1 | `second_token_lookahead()`            |
| `backtracking_elimination` | G1 | `suffix_disjointness_check()` + FIRST |

When a `CategoryDecisionTree` is present, `dispatch_strategy()` subsumes all
three analyses. The gates only control the fallback code paths in
`trampoline.rs` for categories where the decision tree is `None`. This ensures
backward compatibility with grammars that disable tree construction or run
under `OptimizationGates::none_enabled()`.

---

## §8 Dependency on PathMap

The decision tree depends on the `pathmap` crate (included as a git dependency).
PathMap provides a generic trie keyed on byte sequences with algebraic value
operations. The following PathMap features are used:

| Operation                | PathMap Method | Usage in Decision Tree                               |
|--------------------------|----------------|------------------------------------------------------|
| Trie insertion           | `insert()`     | Insert encoded rule patterns                         |
| Trie lookup              | `get()`        | Query a specific byte-key path                       |
| Path enumeration         | `iter()`       | Enumerate all `(Vec<u8>, &V)` pairs                  |
| Lattice join (merge)     | `pjoin()`      | Merge overlapping rules (Commit+Commit -> Ambiguous) |
| Lattice meet (intersect) | `pmeet()`      | Intersect tries for shared-prefix analysis           |
| Lattice subtract         | `psubtract()`  | Remove dead rules from the trie                      |
| Entry counting           | `val_count()`  | Count live entries for statistics                    |
| Emptiness check          | `is_empty()`   | Guard against emitting code for empty categories     |

The `DecisionAction` type implements `Lattice` and `DistributiveLattice` so that
PathMap's algebraic operations correctly propagate ambiguity: joining two
`Commit` actions at the same path yields `Ambiguous`, while subtracting a dead
rule's path restores determinism if only one live rule remains.

---

## §9 File Reference

| File                            | Role                                                     |
|---------------------------------|----------------------------------------------------------|
| `prattail/src/decision_tree.rs` | Core module: trie, builder, queries, diagnostics, cache  |
| `prattail/src/trampoline.rs`    | Consumes `dispatch_strategy()` for codegen emission      |
| `prattail/src/pipeline.rs`      | Builds trees, threads into config, manages cache         |
| `prattail/src/compose.rs`       | X06/X07 composition via `build_decision_trees_from_spec` |
| `prattail/src/lib.rs`           | `PipelineAnalysis.decision_trees` field, module decl     |
| `prattail/src/cost_benefit.rs`  | `OptimizationGates` controlling legacy fallback          |
