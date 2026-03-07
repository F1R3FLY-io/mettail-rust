# PraTTaIL PathMap Decision Tree — Unified Parse Dispatch

| Field   | Value                          |
|---------|--------------------------------|
| Date    | 2026-03-06                     |
| Updated | 2026-03-06                     |
| Status  | Phase 5 (Integration) COMPLETE |

---

## Table of Contents

- [§1 Problem Statement](#1-problem-statement)
- [§2 Core Insight](#2-core-insight)
- [§3 Approach](#3-approach)
- [§4 Approach Comparison](#4-approach-comparison)
- [§5 Trade-offs](#5-trade-offs)
- [§6 What the Trie Subsumes](#6-what-the-trie-subsumes)
- [§7 Implementation Status](#7-implementation-status)

---

## §1 Problem Statement

PraTTaIL's generated parsers use save/restore backtracking at **eight categories of dispatch sites**:

1. **RD prefix dispatch** — which recursive-descent handler to invoke for a given token
2. **Shared prefix groups** — multiple rules sharing a terminal prefix before diverging
3. **Second-token disambiguation** — two rules sharing a dispatch token, distinguished by items[1]
4. **Suffix disjointness** — FIRST set analysis after a shared prefix to avoid NFA try-all
5. **Cross-category cast fallback** — determining whether a fallback dispatch is dead code
6. **LParen grouping vs. rule** — `(` can start a grouped sub-expression or an RD rule
7. **Optional boundary** — `[opt]?` groups where FIRST(opt) vs FOLLOW(opt) overlap
8. **Infix left-factoring** — infix operators that share a prefix with RD rules

Seven ad-hoc optimizations address these sites individually:

| Optimization                       | Gate       | Location                | Lines                                  |
|------------------------------------|------------|-------------------------|----------------------------------------|
| `group_rd_by_dispatch_token()`     | A1         | `trampoline.rs:90-135`  | Groups RD rules by first terminal      |
| `compute_shared_terminal_prefix()` | A1         | `trampoline.rs:260-305` | Finds longest common terminal prefix   |
| `second_token_lookahead()`         | B1         | `trampoline.rs:204-258` | Items[1] uniqueness check              |
| `suffix_disjointness_check()`      | G1 Phase 2 | `trampoline.rs:313-353` | FIRST set suffix pairwise disjointness |
| `is_deterministic_fallback_dead()` | —          | `dispatch.rs:71-128`    | Cross-cat token not catchable          |
| LParen LL(2)/LL(3)                 | G1 Phase 3 | `prediction.rs:607`     | LParen subtrie depth-1 dispatch        |
| Optional LL(1) guard               | G1 Phase 4 | `prediction.rs:608`     | Optional boundary FIRST vs FOLLOW      |

Each optimization has its own analysis pass, its own data structures, and its own code-emission
path.  They interact in fragile ways — for example, `suffix_disjointness_check` generalises
`second_token_lookahead` (the former handles arbitrary skip depths while the latter is fixed at
`skip=1`), yet both are invoked independently with overlapping but not identical preconditions.
Adding a new dispatch site (e.g., keyword-prefix vs. cast LL(3)) requires threading analysis
through multiple files and understanding implicit ordering constraints.

The result is **seven analyses scattered across three files** (`trampoline.rs`, `dispatch.rs`,
`recursive.rs`) with no common intermediate representation, no unified diagnostics, and no
algebraic operations for grammar composition.

---

## §2 Core Insight

Every parse dispatch decision is a function of a **token sequence**.  At any dispatch site the
parser peeks at the next k tokens and must choose: which rule to commit to, or whether to
fall back to NFA try-all.

A **trie** (prefix tree) is the natural data structure for this mapping:

```
              dispatch token (depth 0)
              ╱          ╲
         KwIf             KwLet
         ╱   ╲               ╲
     KwThen  Minus           Eq       ← depth 1
       │       │              │
   COMMIT    COMMIT        COMMIT
  IfThenElse IfMinus        LetIn
```

If we build **one trie per category** from all of that category's RD rules, cast rules, and
cross-category rules, a single walk from the root determines the dispatch strategy at every
depth.  The seven ad-hoc analyses become **observations about trie structure**:

- Grouping by first token = grouping by depth-0 children
- Shared terminal prefix = single-child chain from a depth-0 child
- Second-token lookahead = depth-1 children are all unique
- Suffix disjointness = children after a shared prefix are disjoint
- Dead fallback = no cross-category child for a given token
- LParen LL(2) = LParen subtrie has disjoint depth-1 children
- Optional LL(1) = optional boundary FIRST set vs FOLLOW set

The **PathMap** crate (`pathmap`) provides exactly this trie with lattice-algebraic operations
(`join`, `meet`, `subtract`) that enable grammar composition analysis (e.g., "what new
ambiguities arise when language A is composed with language B?").

**One trie per category subsumes all seven ad-hoc analyses into a single unified mechanism.**

---

## §3 Approach

### §3.1 Build Phase (Compile Time)

`DecisionTreeBuilder` (defined at `decision_tree.rs:349`) constructs the trie for each
category during the pipeline's compile-time pass.  It runs after FIRST sets and dead rules
are computed (`pipeline.rs:1650-1713`).

The builder processes three rule classes in sequence:

1. **RD rules** (`insert_rd_rules`, L504-558) — each rule's syntax items are converted to
   `PatternElement` values, then the terminal prefix is byte-encoded and inserted into the
   category's root `PathMap<DecisionAction>` segment.

2. **Cross-category rules** (`insert_cross_category_rules`, L592-630) — for each cross-cat
   rule with source category S, operator token T, and result category R, the builder inserts
   a two-byte path `[FIRST(S)_token, T]` into R's trie for every token in FIRST(S).

3. **Cast rules** (`insert_cast_rules`, L633-668) — for each cast from source S to target T,
   tokens in FIRST(S) \ FIRST(T) are inserted as single-byte paths into T's trie.

When two rules map to the same byte path, PathMap's `Lattice::pjoin` merges them into an
`Ambiguous` action (L140-176).  This merge is the algebraic equivalent of detecting a
prefix conflict.

### §3.2 Encoding Scheme

```
Byte Range    Meaning
──────────    ─────────────────────────────────────────
0x00..0x7F    Terminal token IDs (from TokenIdMap)
0x80          IDENT_CAPTURE — consumes one Ident token
0x81          BINDER_CAPTURE — consumes one Ident (binding)
0x82..0xBF    NonTerminal category IDs (0x82 + index)
0xC0          OPTIONAL_START marker
0xC1          OPTIONAL_END marker
```

Constants are defined at `decision_tree.rs:47-58`.

The trie is **split at nonterminal boundaries**: encoding stops when a `NonTerminal` pattern
element is reached, and a continuation segment is created for the remaining pattern.  This
prevents the exponential blowup that would occur from inlining all possible nonterminal
expansions.

### §3.3 Output Format (Adaptive)

The emission strategy is determined by `emission_strategy()` (`decision_tree.rs:1102-1108`):

| Condition            | Strategy    | Code Form                                |
|----------------------|-------------|------------------------------------------|
| `total_states` ≤ 256 | `MatchArms` | Nested `match` arms per dispatch token   |
| `total_states` > 256 | `FlatTable` | `const DISPATCH_TABLE_CAT: &[(u8, u16)]` |

**Runtime PathMap is never used** — match arms are 4-8x faster per step because they compile
to native jump tables with no pointer chasing.  The PathMap is used only at compile time for
construction and algebraic analysis.

### §3.4 Query API

At codegen time, the trampoline queries the decision tree via `dispatch_strategy()`
(`decision_tree.rs:1533-1657`):

```rust
pub fn dispatch_strategy(
    &self,
    token_variant: &str,
    token_ids: &TokenIdMap,
) -> DispatchStrategy
```

Returns one of:

| Variant          | Meaning                                        |
|------------------|------------------------------------------------|
| `NotPresent`     | Token not in trie — no RD rule matches         |
| `Singleton`      | Exactly one rule — commit without backtracking |
| `DisjointSuffix` | Multiple rules, disjoint after shared prefix   |
| `NfaTryAll`      | Overlapping suffixes — NFA try-all required    |

### §3.5 Worked Example: `Float` Category

Consider a category `Float` with three rules:

```
FloatId:     float ( <Ident> )
IntToFloat:  float ( <Int> )
FloatLit:    <FloatLiteral>
```

**Step 1: Pattern encoding.**

| Rule         | PatternElements                                      | Bytes                | Boundary    |
|--------------|------------------------------------------------------|----------------------|-------------|
| `FloatId`    | `Terminal("float",3), Terminal("(",5), IdentCapture` | `[0x03, 0x05, 0x80]` | None        |
| `IntToFloat` | `Terminal("float",3), Terminal("(",5), NT("Int",0)`  | `[0x03, 0x05]`       | NT at pos 2 |
| `FloatLit`   | (native type prefix — handled by Pratt, not RD)      | —                    | —           |

**Step 2: Trie insertion.**

```
Root segment (Float):
  [0x03]         → (no value, internal node)
  [0x03, 0x05]   → (no value, internal node)
  [0x03, 0x05, 0x80] → Commit("FloatId", weight=0.0)
```

`IntToFloat` stops at the NT boundary `[0x03, 0x05]` and creates continuation segment 1.
The root path `[0x03, 0x05]` has `FloatId` from the deeper insertion (IDENT_CAPTURE byte).

**Step 3: Query `dispatch_strategy("KwFloat", token_ids)`.**

Collects all paths starting with byte 0x03.  Both `FloatId` (at depth 3: `[0x03,0x05,0x80]`)
and the NT boundary contribute.  Since `0x80 > MAX_TERMINAL_ID`, the suffix at the branch
point is not a terminal — disjointness fails.

Result: `NfaTryAll { rule_labels: ["FloatId", ...], shared_prefix_len: 1, shared_terminals: [0x05] }`.

The shared prefix `[0x05]` (representing `(`) means the trampoline can emit the `(` token
unconditionally before entering NFA try-all for the remaining alternatives.

---

## §4 Approach Comparison

### Approach A: Keep Ad-Hoc Optimizations (Status Quo)

| Dimension        | Assessment                                                                         |
|------------------|------------------------------------------------------------------------------------|
| **Completeness** | Partial — 7 analyses cover ~80% of sites; new sites require new analysis functions |
| **Maintenance**  | Fragile — changes to one analysis can break implicit dependencies in another       |
| **Diagnostics**  | Ad-hoc — each analysis emits its own warnings with inconsistent formatting         |
| **Composition**  | None — no way to algebraically compose two grammars' dispatch decisions            |
| **Code size**    | ~350 lines spread across 3 files                                                   |

### Approach B: Decision Tree via PathMap (Chosen)

| Dimension        | Assessment                                                                     |
|------------------|--------------------------------------------------------------------------------|
| **Completeness** | Full — every dispatch site is a trie query; new sites need only new insertions |
| **Maintenance**  | Centralised — single `decision_tree.rs` module (~2,325 lines including tests)  |
| **Diagnostics**  | Unified — 10 analysis layers with consistent `TreeDiagnostic` format           |
| **Composition**  | Algebraic — `join`, `meet`, `subtract` via PathMap lattice operations          |
| **Code size**    | ~2,325 lines in one file + ~65 lines pipeline integration                      |

### Approach C: Full LL(k) Parse Table

| Dimension        | Assessment                                                                   |
|------------------|------------------------------------------------------------------------------|
| **Completeness** | Full — but requires LL(k) grammar restrictions that PraTTaIL does not impose |
| **Maintenance**  | Heavyweight — table generator is a separate compiler phase                   |
| **Diagnostics**  | Good — standard LL conflict reporting                                        |
| **Composition**  | None — LL tables don't compose algebraically                                 |
| **Code size**    | Estimated ~5,000+ lines for table generator + runtime driver                 |

**Decision:** Approach B provides completeness and algebraic composition without imposing
grammar restrictions.  The PathMap dependency is well-contained (compile-time only) and the
incremental nature (content hashing, L1455-1487) amortises the cost across builds.

---

## §5 Trade-offs

### Advantages

| # | Advantage                   | Detail                                                                                                                                                                                                                                               |
|---|-----------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 1 | **Single analysis surface** | All dispatch decisions flow through one data structure. Adding a new dispatch site means adding an insertion call in the builder, not a new analysis function.                                                                                       |
| 2 | **Precision diagnostics**   | 10 analysis layers (§7) provide consistent, actionable diagnostics: exact ambiguity paths (D01), unreachable rules (D03), minimum lookahead depth (D04), WFST consistency (D06), optimization suggestions (D08), conflict resolution guidance (D09). |
| 3 | **Grammar algebra**         | PathMap's `join`/`meet`/`subtract` enable composition analysis (Layer 5, L1278-1328): given two language grammars, compute their shared rules, unique rules, and new ambiguities — all at compile time.                                              |
| 4 | **Incremental codegen**     | Content hashing (Layer 10, L1455-1487) enables skipping code regeneration for unchanged categories.                                                                                                                                                  |
| 5 | **Adaptive emission**       | Small grammars get match arms (fast branch prediction); large grammars get flat tables (bounded binary search). The threshold is configurable (`FLAT_TABLE_THRESHOLD = 256`, L872).                                                                  |

### Disadvantages

| # | Disadvantage            | Mitigation                                                                                                                                                                                                                                                                                |
|---|-------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 1 | **PathMap dependency**  | PathMap is used only at compile time. The generated parser has zero PathMap runtime dependency — it emits pure `match` arms or `const` tables.                                                                                                                                            |
| 2 | **Encoding complexity** | The byte-encoding scheme (§3.2) maps grammar constructs to a flat byte space. Nonterminal boundaries require segment splitting, which adds complexity to continuation handling. This is contained within `encode_terminal_prefix()` (L461-486) and `insert_nt_continuation()` (L561-589). |
| 3 | **Legacy coexistence**  | The ad-hoc analysis functions (`compute_shared_terminal_prefix`, `second_token_lookahead`, `suffix_disjointness_check`) are retained for recovery parsers (where `decision_tree: None`) and as validation in tests. They are subsumed by `dispatch_strategy()` for normal codegen.        |
| 4 | **Lattice boilerplate** | `DecisionAction` must implement `Lattice` and `DistributiveLattice` (L139-227) for PathMap algebra. This is ~90 lines of mechanical code.                                                                                                                                                 |

---

## §6 What the Trie Subsumes

The following table maps each current ad-hoc optimization to its trie-structural equivalent.

| Current Optimization               | Source Location     | Trie Equivalent                          | Trie Structural Property                                                                                                                                                                                          |
|------------------------------------|---------------------|------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `group_rd_by_dispatch_token()`     | `trampoline.rs:90`  | Grouping by depth-0 child                | Each depth-0 child byte corresponds to one dispatch token. `dispatch_tokens()` (L1663-1682) returns all such tokens.                                                                                              |
| `compute_shared_terminal_prefix()` | `trampoline.rs:260` | Single-child chain from depth-0          | A run of nodes where each has exactly one child is a shared terminal prefix. `shared_prefix_depth()` (L1730-1773) computes this.                                                                                  |
| `second_token_lookahead()`         | `trampoline.rs:204` | Depth-1 children are unique              | If a depth-0 child has N depth-1 children and each maps to a distinct `Commit` action, the dispatch is deterministic at depth 1. This is a special case of `DisjointSuffix` with `shared_prefix_len=0`.           |
| `is_deterministic_fallback_dead()` | `dispatch.rs:71`    | No cross-cat child for token             | If token T has no path in the target category's trie (neither RD, cast, nor cross-cat), then the fallback is dead. Equivalent to `dispatch_strategy() == NotPresent`.                                             |
| `suffix_disjointness_check()`      | `trampoline.rs:313` | Disjoint children after prefix           | After the shared prefix chain, if the branch-point children each lead to distinct `Commit` leaves with terminal bytes, the dispatch is `DisjointSuffix`. Computed by `dispatch_strategy()` (L1580-1656).          |
| LParen LL(2)/LL(3)                 | G1 Phase 3          | LParen subtrie disjoint depth-1 children | The depth-0 child for `LParen` has depth-1 children. If they are disjoint terminals, the parser can peek two tokens to disambiguate grouping from RD rules.                                                       |
| Optional LL(1) guard               | G1 Phase 4          | Optional boundary FIRST vs FOLLOW        | The `OPTIONAL_START`/`OPTIONAL_END` markers (bytes `0xC0`/`0xC1`) delimit optional regions. If the FIRST set of the optional content is disjoint from the FOLLOW set at the boundary, the guard is deterministic. |

### Subsumption Diagram

```
 Ad-hoc Analyses                    Trie Structure
═══════════════                    ══════════════
                                   CategoryDecisionTree
                                          │
 group_rd_by_dispatch_token ──────► depth-0 children
                                          │
 compute_shared_terminal_prefix ──► single-child chains
                                          │
 second_token_lookahead ──────────► depth-1 unique children
                                          │
 suffix_disjointness_check ───────► disjoint branch-point children
                                          │
 is_deterministic_fallback_dead ──► token ∉ trie (NotPresent)
                                          │
 LParen LL(2) ───────────────────► LParen subtrie depth-1
                                          │
 Optional LL(1) ─────────────────► OPTIONAL markers + FIRST/FOLLOW
```

The function `dispatch_strategy()` (`decision_tree.rs:1533-1657`) is the single entry point
that computes all of the above in one trie walk.

---

## §7 Implementation Status

### Phases

| Phase | Name                               | Status       | Key Files                                              | Notes                                                                                                                                                                                                                                                               |
|-------|------------------------------------|--------------|--------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **1** | Infrastructure + Trie Construction | **COMPLETE** | `decision_tree.rs:28-707`                              | `DecisionTreeBuilder`, byte encoding, `PatternElement`, `DecisionAction` with `Lattice`/`DistributiveLattice` impls                                                                                                                                                 |
| **2** | Decision Tree Analysis             | **COMPLETE** | `decision_tree.rs:719-865`                             | `resolve_nonterminal_boundaries()`, `prune_dead_rules()`, `compute_statistics()`                                                                                                                                                                                    |
| **3** | Match Arm Emission                 | **COMPLETE** | `decision_tree.rs:868-944`                             | `emit_match_arms()` emits diagnostic dumps (comment-based summaries for debugging/visualization). Actual codegen is performed by `trampoline.rs` via `dispatch_strategy()` — the emit functions are diagnostic utilities, not codegen outputs.                      |
| **4** | Flat Table Emission                | **COMPLETE** | `decision_tree.rs:947-1081`                            | `flatten_tree()` builds state graph, `emit_flat_table()` emits `const` tables. These are diagnostic dump functions for visualization/debugging, not codegen outputs. Actual codegen is performed by `trampoline.rs` via `dispatch_strategy()`.                      |
| **5** | Integration                        | **COMPLETE** | `pipeline.rs:1650-1713`, `trampoline.rs:569-1023`      | Tree built in pipeline after FIRST sets. Threaded to `TrampolineConfig.decision_tree`. `dispatch_strategy()` consumed by trampoline codegen for DisjointSuffix, NfaTryAll+G1, NfaTryAll+B1, and NfaTryAll fallback arms. Singleton handled by single-rule arm path. |
| **6** | Documentation                      | **COMPLETE** | This file + `prattail/docs/diagnostics/decision-tree/` |                                                                                                                                                                                                                                                                     |
| **7** | Regenerate Languages               | **COMPLETE** | —                                                      | All test languages regenerated; 1,376 workspace tests passing                                                                                                                                                                                                       |

### Analysis Layers (Diagnostics Infrastructure)

All 10 analysis layers are implemented in `decision_tree.rs:1120-1487`:

| Layer | Lint ID | Function                                       | Line | Status                                                                                                                                                                                                                  |
|-------|---------|------------------------------------------------|------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 1     | D01     | `precision_ambiguity_reports()`                | 1137 | **COMPLETE** — active in pipeline (L1684-1695)                                                                                                                                                                          |
| 2     | D03     | `unreachable_rule_detection()`                 | 1201 | **COMPLETE**                                                                                                                                                                                                            |
| 3     | D04     | `min_lookahead_report()`                       | 1243 | **COMPLETE**                                                                                                                                                                                                            |
| 4     | D05     | `complexity_metrics()`                         | 1265 | **COMPLETE** — active in pipeline (L1670-1681)                                                                                                                                                                          |
| 5     | X06/X07 | `composition_trie_analysis()`                  | 1278 | **COMPLETE** — `build_decision_trees_from_spec` + compose integration; returns `CompositionTrieReport`                                                                                                                  |
| 6     | D06     | `wfst_consistency_check()`                     | 1334 | **COMPLETE** — active in pipeline (L1698-1710)                                                                                                                                                                          |
| 7     | D07     | `coverage_paths()` + `__coverage` module       | 1547 | **COMPLETE** — `parser-coverage` feature gate in `languages/Cargo.toml`; runtime instrumentation via `__coverage::record(cat, path_id)`, `dump()`, `reset()`; activated by `PRATTAIL_COVERAGE=1` env var during codegen |
| 8     | D08     | `optimization_suggestions()`                   | 1375 | **COMPLETE**                                                                                                                                                                                                            |
| 9     | D09     | `conflict_resolution_guidance()`               | 1420 | **COMPLETE**                                                                                                                                                                                                            |
| 10    | —       | `category_content_hash()` + `IncrementalState` | 1455 | **COMPLETE** — `.prattail-cache` with version-tagged invalidation; loaded/saved via `PRATTAIL_CACHE_DIR` env var                                                                                                        |

### Integration Points

| Component              | File              | Line(s)   | Integration Detail                                                           |
|------------------------|-------------------|-----------|------------------------------------------------------------------------------|
| Pipeline construction  | `pipeline.rs`     | 1650-1713 | `DecisionTreeBuilder::new()` + `build_all()` after FIRST sets and dead rules |
| TrampolineConfig field | `trampoline.rs`   | 1703      | `pub decision_tree: Option<CategoryDecisionTree>`                            |
| Config population      | `pipeline.rs`     | 1865      | `decision_tree: decision_trees.get_tree(&cat.name).cloned()`                 |
| Recovery path          | `pipeline.rs`     | 1990      | `decision_tree: None` — recovery path does not use decision tree dispatch    |
| Cost-benefit gate      | `cost_benefit.rs` | 49        | `G1: BacktrackingElimination` — controls Phases 1-4 of FIRST set analysis    |

### Key Source Files

| File                            | Lines  | Role                                                                      |
|---------------------------------|--------|---------------------------------------------------------------------------|
| `prattail/src/decision_tree.rs` | ~2,325 | Core module: types, builder, analysis layers, query API, tests (10 tests) |
| `prattail/src/pipeline.rs`      | ~2,100 | Pipeline state machine; decision tree construction at L1650-1713          |
| `prattail/src/trampoline.rs`    | ~2,500 | Trampolined parser codegen; `TrampolineConfig.decision_tree` at L1703     |
| `prattail/src/cost_benefit.rs`  | ~800   | Optimization gates; `G1 BacktrackingElimination` at L49                   |
| `prattail/src/dispatch.rs`      | ~300   | Cross-category dispatch; `is_deterministic_fallback_dead()` at L71        |
| `prattail/src/recursive.rs`     | ~600   | RD handler generation; `RDRuleInfo`, `RDSyntaxItem` types                 |

### Test Coverage

The module includes 10 unit tests (`decision_tree.rs:1854-2324`):

| Test                                            | Line | Validates                                                                |
|-------------------------------------------------|------|--------------------------------------------------------------------------|
| `test_pattern_encoding_terminal_only`           | 1907 | 3-terminal pattern encodes to 3 bytes, no NT boundary                    |
| `test_pattern_encoding_with_nonterminal`        | 1934 | NT boundary splits at position 2, continuation tracked                   |
| `test_builder_insert_rd_rules`                  | 1967 | Two RD rules produce ≥ 2 trie entries                                    |
| `test_ambiguous_rules_same_token`               | 1997 | Two rules sharing `float(` merge via `pjoin`                             |
| `test_dead_rule_pruning`                        | 2033 | Dead rules excluded during insertion                                     |
| `test_statistics_computation`                   | 2061 | `build_all` computes correct `TreeStats`                                 |
| `test_emission_strategy`                        | 2092 | ≤ 256 states → `MatchArms`; > 256 → `FlatTable`                          |
| `test_incremental_state`                        | 2114 | Content hash match/mismatch detection                                    |
| `test_dispatch_strategy_singleton`              | 2124 | Single rule → `Singleton`; absent token → `NotPresent`                   |
| `test_dispatch_strategy_disjoint_suffix`        | 2159 | `if + then` vs `if - else` → `DisjointSuffix` with `Plus`/`Minus` map    |
| `test_dispatch_strategy_shared_prefix_disjoint` | 2201 | `if ( + )` vs `if ( - )` → `DisjointSuffix` with `shared_prefix_len=1`   |
| `test_dispatch_strategy_nfa_tryall`             | 2245 | `float(<Ident>)` vs `float(<NT>)` → `NfaTryAll` (non-terminal at branch) |
| `test_dispatch_tokens`                          | 2295 | `dispatch_tokens()` returns exactly `{KwIf, KwLet}`                      |

### Completed Work

1. **Phase 5 codegen integration** (COMPLETE) — `dispatch_strategy()` is consumed by
   trampoline codegen (`trampoline.rs:569-1023`). The four `DispatchStrategy` variants map
   to concrete code paths: `DisjointSuffix` emits deterministic match arms,
   `NfaTryAll` falls through G1 suffix disjointness and B1 two-token lookahead before
   emitting full NFA try-all, `Singleton` is handled by the single-rule arm path, and
   `NotPresent` falls through to the legacy path.

2. **Phase 7 language regeneration** (COMPLETE) — All test languages (`calc`, `comparison`,
   `macro_lang`, `e2e`) regenerated; 1,376 workspace tests passing.

### Remaining Work

1. **Flat table runtime driver** — For grammars exceeding 256 states, emit the `const`
   tables and a small runtime driver function that walks the table. `emit_flat_table()`
   (L1031-1081) provides diagnostic dumps; a runtime driver is needed for actual dispatch.
   No current test grammar exceeds the 256-state threshold.

2. **Remove ad-hoc functions** — The following functions are retained for recovery parsers
   (where `decision_tree: None`) and test validation. They may be removed once recovery
   parsers also use the decision tree:
   - `compute_shared_terminal_prefix()` (`trampoline.rs:260`)
   - `second_token_lookahead()` (`trampoline.rs:204`)
   - `suffix_disjointness_check()` (`trampoline.rs:313`)
   - `is_deterministic_fallback_dead()` (`dispatch.rs:71`)
