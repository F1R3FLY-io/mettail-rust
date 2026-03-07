---
Date: 2026-03-06
Updated: 2026-03-06
---

# Decision Tree Pipeline Integration

## §1 Insertion Point

The decision tree is built in `pipeline.rs:generate_parser_code()` after:

1. FIRST set computation and augmentation (native types, Ident, LParen, binder tokens)
2. FOLLOW set computation
3. WFST construction and transducer cascade
4. Unified lint layer execution
5. Cost-benefit optimization analysis
6. Dead rule collection

And before:

7. Ambiguity targeting analysis (A5)
8. Grammar complexity report (D2)
9. RD handler generation
10. Trampoline parser generation

```
pipeline.rs (~line 1650):

    ┌─────────────────────────────────────────┐
    │ FIRST sets augmented                    │
    │ FOLLOW sets computed                    │
    │ WFST constructed + cascade              │
    │ Lint layer executed                     │
    │ Cost-benefit gates computed             │
    │ Dead rules collected                    │
    ├─────────────────────────────────────────┤
    │ ★ Decision tree construction ★          │ ← HERE
    │   DecisionTreeBuilder::new(             │
    │     token_id_map, first_sets,           │
    │     category_names, dead_rules          │
    │   )                                     │
    │   .build_all(rd_rules, cross, cast)     │
    │   → D05 summary diagnostics             │
    │   → D01 ambiguity diagnostics           │
    │   → D06 WFST consistency diagnostics    │
    ├─────────────────────────────────────────┤
    │ A5 ambiguity targeting                  │
    │ D2 complexity report                    │
    │ RD handler generation                   │
    │ Trampoline parser generation            │
    │   TrampolineConfig.decision_tree = ...  │
    └─────────────────────────────────────────┘
```

## §2 Data Consumed

The `DecisionTreeBuilder::new()` constructor takes:

| Parameter                               | Source                         | Purpose                      |
|-----------------------------------------|--------------------------------|------------------------------|
| `token_id_map: TokenIdMap`              | Built from FIRST/FOLLOW tokens | Terminal variant → u16 ID    |
| `first_sets: HashMap<String, FirstSet>` | Augmented FIRST sets           | NT category → FIRST tokens   |
| `category_names: Vec<String>`           | Bundle categories              | Category ordering for NT IDs |
| `dead_rules: HashSet<String>`           | collect_dead_rule_labels()     | Rules to exclude from trie   |

The `build_all()` method takes:

| Parameter                           | Source | Purpose                    |
|-------------------------------------|--------|----------------------------|
| `rd_rules: &[RDRuleInfo]`           | Bundle | Terminal-first RD rules    |
| `cross_rules: &[CrossCategoryRule]` | Bundle | Cross-category infix rules |
| `cast_rules: &[CastRule]`           | Bundle | Cast dispatch rules        |

## §3 Threading to Codegen

The built `CategoryDecisionTree` is cloned into each `TrampolineConfig`:

```rust
TrampolineConfig {
    ...
    decision_tree: decision_trees.get_tree(&cat.name).cloned(),
    ...
}
```

Recovery parsers get `decision_tree: None` since they don't use trie-based dispatch.

## §4 Codegen Integration

In `write_nfa_merged_prefix_arm()`, the decision tree is consulted first and all four `DispatchStrategy` variants are handled:

```rust
if let Some(ref dt) = config.decision_tree {
    match dt.dispatch_strategy(variant, &token_id_map) {
        DisjointSuffix { shared_prefix_len, suffix_map, .. }
            if !config.needs_nfa_spillover =>
        {
            /* Deterministic dispatch: shared prefix + match on suffix token */
            return; // Decision tree handled this arm
        }
        NfaTryAll { rule_labels, shared_prefix_len, .. } => {
            /* DT-driven NFA try-all with G1 suffix refinement and B1
               multi-token lookahead. Emits shared prefix, then tries
               each candidate rule with save/restore. */
            return; // DT NfaTryAll handled this arm
        }
        Singleton { .. } | NotPresent => {
            /* Singleton: single-rule arm handled elsewhere.
               NotPresent: no trie data for this token — skip. */
        }
        DisjointSuffix { .. } => {
            /* needs_nfa_spillover — fall through to legacy try-all */
        }
    }
}
```

The legacy A1+G1+B1 path remains as fallback for:
- Recovery parsers (`decision_tree: None`)
- `DisjointSuffix` arms requiring NFA spillover
- `Singleton`/`NotPresent` tokens (handled by the single-rule arm loop in the outer `for (variant, rules)` iteration)

## §5 Diagnostic Emission

Four diagnostic categories are emitted during tree construction and codegen:

| ID  | When                                              | Content                                |
|-----|---------------------------------------------------|----------------------------------------|
| D05 | Per category with states > 0                      | TreeStats summary                      |
| D01 | Per Ambiguous trie node                           | Token path, conflicting rules, weights |
| D06 | WFST token not in trie                            | WFST-trie reachability mismatch        |
| D07 | `PRATTAIL_COVERAGE=1` env var set at codegen time | Path coverage instrumentation report   |

**D07 Coverage Instrumentation.** When `PRATTAIL_COVERAGE=1` is set during code generation, PraTTaIL emits a `__coverage` module gated by `#[cfg(feature = "parser-coverage")]`:

- `__coverage::record(cat, path_id)` -- called at each dispatch arm to record visited paths
- `__coverage::dump()` -- returns `HashSet<(String, u32)>` of `(category, path_id)` pairs
- `__coverage::reset()` -- clears the coverage set

Each `DispatchStrategy` arm in the trampoline gets a unique `path_id`, incremented per category. The pipeline emits a D07 note listing instrumented categories.

Source: `pipeline.rs` (~line 1876-1918), `trampoline.rs` (coverage record calls), `decision_tree.rs` (`coverage_paths()`, `coverage_report()`).

## §6 Compose Pipeline Integration

The `build_decision_trees_from_spec()` function in `decision_tree.rs` provides a lightweight decision tree construction pipeline that bypasses full parser generation. It:

1. Extracts `category_names` from `LanguageSpec.types`
2. Builds `RuleInfo` structs and computes FIRST sets
3. Builds `TokenIdMap` from all FIRST set terminals plus structural delimiters
4. Constructs `RDRuleInfo`, `CrossCategoryRule`, and `CastRule` vectors
5. Runs `DecisionTreeBuilder::build_all()` with an empty dead-rules set (no cost-benefit analysis)

This pipeline is consumed by `compose_with_wfst()` in `compose.rs`, which builds trees for both source specs and the merged spec:

```
trees_a  = build_decision_trees_from_spec(spec_a)
trees_b  = build_decision_trees_from_spec(spec_b)
trees_merged = build_decision_trees_from_spec(&merged_spec)
```

Two diagnostics are emitted by comparing the source trees:

| ID  | Severity | Content                                                                             |
|-----|----------|-------------------------------------------------------------------------------------|
| X06 | Note     | Common sublanguage analysis: shared dispatch paths, unique-to-A, unique-to-B counts |
| X07 | Warning  | Composition-introduced ambiguities not present in either source grammar             |

X06 uses `composition_trie_analysis(tree_a, tree_b)` to count common/unique dispatch paths across shared categories. X07 fires when `report.new_ambiguities > 0`, hinting the user to review overlapping rules from different sources.

The resulting trees are stored in `WfstCompositionResult`:

| Field            | Content                                                    |
|------------------|------------------------------------------------------------|
| `source_a_trees` | `Option<HashMap<String, CategoryDecisionTree>>` for spec A |
| `source_b_trees` | Same for spec B                                            |
| `merged_trees`   | Trees for the merged spec                                  |

This allows downstream consumers to inspect dispatch structure differences across composed grammars without re-running the full pipeline.

## §7 Incremental Codegen

Layer 10 provides content-addressable caching via `.prattail-cache`, enabling the pipeline to skip codegen for unchanged categories across builds.

**Cache Location.** Controlled by `PRATTAIL_CACHE_DIR` env var:

```
PRATTAIL_CACHE_DIR=/path/to/dir  →  /path/to/dir/.prattail-cache
(unset)                          →  no caching
```

**IncrementalState.** Binary format stored in `.prattail-cache`:

```
[version: u32][num_categories: u32]
per category:
  [name_len: u32][name: bytes][hash: u128][code_len: u32][code: bytes]
```

| Field             | Purpose                                                                  |
|-------------------|--------------------------------------------------------------------------|
| `version`         | Must equal `CACHE_VERSION` (currently 1); mismatch discards entire cache |
| `category_hashes` | `HashMap<String, u128>` from `category_content_hash()`                   |
| `category_code`   | `HashMap<String, String>` of cached generated code per category          |

**Content Hashing.** `category_content_hash()` hashes the category name, `total_states`, `total_rules`, and all `(path, action)` pairs in the trie segments. When the hash matches the cached value, the category's codegen is skipped.

**Pipeline Integration.** In `generate_parser_code()`:

1. **Load:** `IncrementalState::load(cache_path)` at pipeline start
2. **Check:** `is_valid()` verifies `CACHE_VERSION` match; `is_unchanged(cat, hash)` per category
3. **Record:** `new_cache.record(cat, hash)` stores current hashes during codegen
4. **Save:** `new_cache.save(cache_path)` at pipeline end (best-effort, non-fatal on failure)

**Cache Invalidation.** Bump `CACHE_VERSION` in `decision_tree.rs` whenever codegen logic changes in `trampoline.rs`, `recursive.rs`, `dispatch.rs`, or `pratt.rs`. The opt-in nature (env var required) ensures no stale code in CI or default builds.

Source: `decision_tree.rs` (`CACHE_VERSION`, `IncrementalState`, `category_content_hash()`), `pipeline.rs` (~line 1148-1155, ~line 2287-2290).
