# Decision Tree Diagnostics (D-Category)

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Source:** `prattail/src/decision_tree.rs` (analysis layers), `prattail/src/pipeline.rs` (emission)

## 1 Overview

The D-category lints report on the structure, ambiguity, and consistency of the
per-category PathMap decision trees built during the PraTTaIL pipeline's Generate
phase. Each category in the grammar receives a trie whose byte-encoded token
prefixes map to parse rules. The analysis layers walk these tries and emit
diagnostics ranging from informational summaries to actionable warnings about
grammar conflicts and WFST/trie mismatches.

```
             Pipeline Stage
  ┌──────────────────────────────────────┐
  │  Extract  Ready  Generate  Finalize  │
  │                    ▲                 │
  │                    │                 │
  │       ┌────────────┴────────────┐    │
  │       │  DecisionTreeBuilder    │    │
  │       │  ┌───────────────────┐  │    │
  │       │  │ build_all()       │  │    │
  │       │  │   insert_rd       │  │    │
  │       │  │   insert_cross    │  │    │
  │       │  │   insert_cast     │  │    │
  │       │  │   compute_stats   │──┼──▶ D05
  │       │  └───────────────────┘  │    │
  │       │  ┌───────────────────┐  │    │
  │       │  │ Analysis Layers   │  │    │
  │       │  │   precision_amb   │──┼──▶ D01
  │       │  │   wfst_consist    │──┼──▶ D06
  │       │  │   unreachable     │──┼──▶ D03
  │       │  │   opt_suggest     │──┼──▶ D08
  │       │  │   conflict_guide  │──┼──▶ D09
  │       │  │   compose_trie    │──┼──▶ X06, X07
  │       │  └───────────────────┘  │    │
  │       └─────────────────────────┘    │
  └──────────────────────────────────────┘
```

## 2 Lint Index

| ID | Severity | Name | Description | Source |
|----|----------|------|-------------|--------|
| [D01](D01-precision-ambiguity.md) | Note | precision-ambiguity | Token path, conflicting rules, overlap tokens, resolution hint | `precision_ambiguity_reports()` |
| [D02](D02-unresolvable-ambiguity.md) | Warning | unresolvable-ambiguity | No finite lookahead resolves -- inherent grammar conflict | `unresolvable_ambiguity_detection()` |
| [D03](D03-trie-unreachable-rule.md) | Warning | trie-unreachable-rule | Rule shadowed by higher-priority path in trie | `unreachable_rule_detection()` |
| [D04](D04-min-lookahead-depth.md) | Note | min-lookahead-depth | Per-category minimum lookahead tokens | `min_lookahead_report()` |
| [D05](D05-decision-tree-summary.md) | Note | decision-tree-summary | States, deterministic/ambiguous ratio, depth, savings | `complexity_metrics()` |
| [D06](D06-wfst-trie-inconsistency.md) | Warning | wfst-trie-inconsistency | WFST prediction vs trie reachability mismatch | `wfst_consistency_check()` |
| [D07](D07-path-coverage-report.md) | Note | path-coverage-report | Untested trie paths (opt-in `PRATTAIL_COVERAGE=1`) | `path_coverage_report()` |
| [D08](D08-optimization-suggestion.md) | Note | optimization-suggestion | Grammar modifications to resolve ambiguity | `optimization_suggestions()` |
| [D09](D09-conflict-resolution-guide.md) | Note | conflict-resolution-guide | Strategies for genuine conflicts | `conflict_resolution_guidance()` |
| X06 | Note | composition-common-sublanguage | Common sublanguage size | `composition_trie_analysis()` |
| X07 | Warning | composition-new-ambiguity | Composition introduces new ambiguity | `composition_trie_analysis()` |

## 3 Activation Status

The following lints are **currently active** in the pipeline and emit diagnostics
during every grammar compilation:

- **D01** -- Emitted per ambiguous node in each category's trie. See
  `pipeline.rs` lines that iterate `precision_ambiguity_reports()`.
- **D05** -- Emitted per category with a non-empty decision tree. Uses
  `TreeStats::Display` for the message body.
- **D06** -- Emitted when a WFST predicts dispatch for a token that has no
  corresponding path in the category's trie. Requires a `PredictionWfst` to be
  available for the category.

The remaining lints have their analysis functions implemented in
`decision_tree.rs` and are **infrastructure-ready** -- the analysis logic exists
and can be invoked via the PathMap decision tree infrastructure. Their pipeline
emission wiring is pending integration as the diagnostic surface expands:

- **D02** -- `unresolvable_ambiguity_detection()` is implemented; detects
  grammars where no finite lookahead depth can resolve a conflict.
- **D03** -- `unreachable_rule_detection()` is implemented; detects rules
  shadowed by higher-priority paths in the PathMap trie.
- **D04** -- `min_lookahead_report()` is implemented; reports per-category
  minimum lookahead token depth from the PathMap trie structure.
- **D07** -- `path_coverage_report()` is implemented; opt-in coverage tool
  gated by the `PRATTAIL_COVERAGE=1` environment variable.
- **D08** -- `optimization_suggestions()` is implemented; suggests grammar
  modifications to resolve PathMap ambiguity.
- **D09** -- `conflict_resolution_guidance()` is implemented; provides
  strategies for resolving genuine conflicts detected in the PathMap trie.
- **X06, X07** -- `composition_trie_analysis()` is implemented; emitted during
  language composition when two grammars' decision trees are compared via PathMap
  algebraic operations (join, meet, subtract).

## 4 Diagnostic Output Format

All D-category diagnostics follow PraTTaIL's Rust-compiler-style output format
(see [`prattail/docs/diagnostics/README.md`](../../../prattail/docs/diagnostics/README.md)):

```
severity[ID] (GrammarName): message
  = context
  = hint: resolution guidance
```

For example:

```
note[D01] (Float): ambiguity at [KwFloat, LParen] between FloatId and IntToFloat
  = 2 candidates at path [0x00, 0x01]: FloatId, IntToFloat
  = hint: adding a distinguishing terminal before the divergence point
          would resolve the ambiguity between FloatId and IntToFloat
```

## 5 Architecture

Decision tree diagnostics are produced by a two-layer architecture:

1. **Analysis functions** in `prattail/src/decision_tree.rs` -- each function
   accepts a `CategoryDecisionTree` (and optionally a `TokenIdMap` or
   `PredictionWfst`) and returns `Vec<TreeDiagnostic>` or a single
   `TreeDiagnostic`.

2. **Pipeline emission** in `prattail/src/pipeline.rs` -- after
   `DecisionTreeBuilder::build_all()` completes, the pipeline iterates over
   category names, invokes analysis functions, and routes each `TreeDiagnostic`
   through `pipeline_diagnostic()` which delegates to the lint system's
   `emit_diagnostic()`.

The `TreeDiagnostic` struct carries:

```
┌────────────────────────────────────┐
│ TreeDiagnostic                     │
│ ────────────────────────────────── │
│ lint_id:  &'static str  ("D01")    │
│ severity: LintSeverity             │
│ category: String                   │
│ message:  String                   │
│ hint:     Option<String>           │
└────────────────────────────────────┘
```

## 6 Related Diagnostic Categories

- **G (Grammar Structure):** G01--G10, G24--G31 -- structural grammar lints
- **W (WFST-Specific):** W01--W09 -- WFST prediction and weight lints
- **R (Recovery):** R01--R07 -- error recovery configuration lints
- **C (Cross-Category):** C01--C04 -- cast and cross-category dispatch lints
- **P (Performance):** P02--P04 -- runtime performance lints
- **I (Infrastructure):** I01--I12 -- pipeline progress messages
