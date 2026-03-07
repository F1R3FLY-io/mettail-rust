# WPDS Layer Expansion

**Date:** 2026-03-07
**Status:** Complete (all 8 sprints)

## Overview

The WPDS Layer Expansion extends PraTTaIL's Weighted Pushdown System analysis from
core construction and saturation (Phases 1--4) to a comprehensive suite of call graph
analyses, context-sensitive tables, and pipeline integrations. The expansion adds
~1,750 lines to `wpds.rs`, ~450 lines to `lint.rs`, and ~200 lines to `pipeline.rs`.

### Motivation

The core WPDS layer (Phases 1--4) provides three fundamental algorithms:

- **poststar** — Forward saturation of a P-automaton, computing all configurations
  reachable from an initial set via Push/Replace/Pop rules
- **prestar** — Backward saturation, computing all configurations that can reach a
  target set
- **stringsum** — Per-input ambiguity counting via weighted path enumeration

These algorithms answer reachability and ambiguity questions, but they operate at the
level of individual stack symbols. The expansion builds *higher-level analyses* on top
of these primitives:

1. **Structural analysis** (G33--G36): Extract the grammar's call graph, compute
   depth bounds, classify cycles, and identify calling contexts. These analyses
   provide the foundation for context-sensitive dispatch and dead-rule detection.

2. **Context-sensitive tables** (CS-01/04/05): Use calling context information to
   build per-category per-caller rule tables, cross-category binding power hints,
   and context-based ambiguity flags. These are structural frameworks for future
   context-sensitive parsing optimizations.

3. **Pipeline integrations** (INT-01/02/03, COMP-07, RT-01): Wire WPDS results
   into the existing prediction, dead-rule, NFA spillover, and frame pool subsystems.

4. **Lint diagnostics** (W13, D14, D15, P05, W14, W16, COMP-08): Surface WPDS
   analysis results to grammar authors via the unified lint layer.

### Key Design Decisions

- **BooleanWeight for reachability, TropicalWeight for dispatch**: The WPDS is
  built and saturated twice — once with `BooleanWeight` for binary reachability
  (Tier 5 dead-rule detection), once with `TropicalWeight` for weighted dispatch
  refinement (INT-01).

- **Tarjan SCC before depth bounds**: SCC decomposition identifies mutual recursion
  *before* depth bound computation, so categories in nontrivial SCCs are correctly
  classified as unbounded (recursive).

- **G25 gate**: All WPDS analysis is gated behind the G25 cost-benefit optimization
  gate (`wpds_reachability`) and requires ≥2 categories. Single-category grammars
  skip WPDS analysis entirely.

- **Structural frameworks**: CS-01/04/05 build context rule tables and BP hints but
  do not yet drive code generation. They are structural frameworks designed for future
  context-sensitive dispatch optimization.

### Sprint-to-Deliverable Mapping

| Sprint | Deliverables | Lines | Tests |
|--------|-------------|-------|-------|
| 1 | G33 Call Graph, Tarjan SCC, `shortest_path_witness()` | ~400 | 8 |
| 2 | G34 Depth Bounds, `compute_depth_bounds()` | ~150 | 4 |
| 3 | G35 Cycle Classification, left-recursion detection | ~200 | 4 |
| 4 | G36 Calling Contexts, `compute_calling_contexts()` | ~100 | 4 |
| 5 | CS-01 Context Rule Tables, `build_context_rule_tables()` | ~200 | 4 |
| 6 | CS-04 Cross-Category BP, CS-05 Context Ambiguity | ~150 | 8 |
| 7 | INT-01, COMP-07, INT-02, INT-03, RT-01 pipeline integrations | ~200 | -- |
| 8 | W13, D14, D15, P05, W14, W16, COMP-08 lint diagnostics | ~450 | 11 |

### Architecture

```
build_wpds() ──> Wpds<W>
     |
     +-- poststar(BooleanWeight) ──> reachable_categories
     |                               unreachable_rules + D15 witness
     |
     +-- poststar(TropicalWeight) ──> category_weights
     |
     +-- extract_call_graph()   [G33] ──> WpdsCallGraph
     |    |                                +-- edges, fan_in, fan_out
     |    |                                +-- sccs (Tarjan)
     |    |
     |    +-- compute_depth_bounds()   [G34] ──> DepthBounds per category
     |    +-- classify_cycles()        [G35] ──> CycleInfo (Direct/Mutual/LR)
     |    +-- shortest_path_witness()  [D15] ──> witness traces
     |
     +-- compute_calling_contexts()   [G36] ──> CallingContext per category
     |    |
     |    +-- build_context_rule_tables()   [CS-01] ──> ContextRuleTable
     |    +-- analyze_cross_category_bp()   [CS-04] ──> BP hints per edge
     |    +-- analyze_context_ambiguity()   [CS-05] ──> unambiguous flags
     |
     +-- WpdsAnalysis (12-field struct)
          |
          +-- pipeline.rs:
          |    +-- INT-01: wpds_refine_prediction_weights()
          |    +-- COMP-07: wpds_confirm_trie_dead_rules()
          |    +-- INT-02: dead-rule recording
          |    +-- INT-03: NFA spillover reduction
          |
          +-- trampoline.rs:
          |    +-- RT-01: frame_pool_capacity from G34
          |
          +-- lint.rs:
               +-- W13: wpds-unreachable
               +-- D14: wpds-complexity-report
               +-- P05: wpds-pipeline-cost
               +-- W14: wpds-confirmed-ambiguity
               +-- W16: wpds-weight-inversion
               +-- COMP-08: wpds-refactoring-suggestion
```

### WpdsAnalysis Struct

```rust
pub struct WpdsAnalysis {
    pub grammar_name: String,
    pub num_symbols: usize,                                    // |G|
    pub num_rules: usize,                                      // |D|
    pub reachable_categories: HashSet<String>,                 // poststar result
    pub unreachable_rules: Vec<WpdsUnreachableRule>,            // W13 data
    pub category_weights: HashMap<String, f64>,                // TropicalWeight
    pub call_graph: WpdsCallGraph,                             // G33
    pub depth_bounds: HashMap<String, DepthBounds>,            // G34
    pub cycles: Vec<CycleInfo>,                                // G35
    pub calling_contexts: HashMap<String, Vec<CallingContext>>, // G36
    pub context_rule_tables: HashMap<String, ContextRuleTable>, // CS-01
    pub cross_category_bp: HashMap<(String, String), Vec<u8>>, // CS-04
    pub context_unambiguous: HashMap<String, bool>,            // CS-05
}
```

## Sub-Documents

| Document | Content |
|----------|---------|
| [Call Graph Analysis](call-graph-analysis.md) | G33, Tarjan SCC, witness traces |
| [Depth Bounds and Cycles](depth-bounds-and-cycles.md) | G34, G35, RT-01 |
| [Context-Sensitive Tables](context-sensitive-tables.md) | G36, CS-01, CS-04, CS-05 |
| [Pipeline Integrations](pipeline-integrations.md) | INT-01/02/03, COMP-07, RT-01 |

## Cross-References

- [WPDS Analysis Layer](../wpds-analysis.md) -- Parent design document
- [Five-Tier Dead-Rule Detection](../dead-rule-detection.md) -- Tier 5 details
- [Diagnostic Reference](../../../diagnostics/README.md) -- All lint diagnostics
