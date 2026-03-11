# Automata Codegen Promotions

**Date**: 2026-03-10
**Status**: Complete
**Plan**: `/home/dylon/.claude/plans/lexical-stargazing-whisper.md`

## Summary

Promoted 4 advanced automata modules from `OptimizationStatus::Diagnostic` to
`OptimizationStatus::Auto` so their analysis results feed into codegen decisions
via `PipelineAnalysis`. Two additional modules contribute informational fields
for future optimization.

## Promoted Modules

| Module | Optimization | Extends | Effect |
|--------|-------------|---------|--------|
| M1 Symbolic | SYM01-DCE | A4 DCE | Unsatisfiable guards -> dead rules |
| M7 Probabilistic | PR01-DCE | A4 DCE | Low-selectivity rules -> dead rules |
| M7 Probabilistic | PR01-WEIGHT | Sprint 3 | Corpus-trained weight blending |
| M3 Alternating | N06-ISO | Sprint 8 | Bisimulation -> shared templates |
| M6 Register | RA01-SKIP | NEW | Dead registers -> skip alpha-equiv |

## Informational Fields (Deferred Codegen)

| Module | Field | Status |
|--------|-------|--------|
| M4 VPA | `bracket_deterministic: bool` | Diagnostic |
| M8 Multi-Tape | `independent_categories: HashSet<String>` | Diagnostic |

## Architecture

Analysis results flow through `AdvancedAnalysisBundle<'a>` into
`build_pipeline_analysis()`, which populates `PipelineAnalysis` fields consumed
by the macros crate during Ascent code generation.

```
Phase 7B Analysis --> AdvancedAnalysisBundle --> build_pipeline_analysis() --> PipelineAnalysis
                                                          |
                                              +-----------+---------------+
                                              v           v               v
                                      dead_rule_labels  constructor_wts  isomorphic_groups
                                              |           |               |
                                              v           v               v
                                         Ascent DCE   Rule ordering   Shared templates
```

## Key Changes

| File | Change |
|------|--------|
| `prattail/src/pipeline.rs` | `AdvancedAnalysisBundle`, `build_pipeline_analysis()` body + call site |
| `prattail/src/lib.rs` | 3 new `PipelineAnalysis` fields |
| `prattail/src/cost_benefit.rs` | Status promotions, `GrammarProfile`/`OptimizationGates` extensions |
| `prattail/src/symbolic.rs` | `unsatisfiable_rule_labels` field |
| `prattail/src/probabilistic.rs` | `rule_selectivities` field |

## Test Coverage

- 15 pipeline tests (per-optimization unit tests)
- 13 cost-benefit tests (status, gates, profile defaults)
- All pass under default features and `--all-features`

## Safety Invariants

1. No optimization changes the recognized language
2. Feature-gating prevents compilation breakage with default features
3. `is_normalized` guard prevents probabilistic DCE without training data
4. Out-of-bounds register indices are gracefully skipped
5. Lint layer is unchanged -- all 27 lints continue to emit independently

## Cross-References

- [Codegen Optimizations Design](../../../prattail/docs/design/automata-codegen-optimizations.md)
- [Codegen Soundness Proofs](../../../prattail/docs/theory/optimization/codegen-soundness.md)
- [Per-Optimization Docs](../../../prattail/docs/optimization/)
- [Advanced Automata Overview](../../../prattail/docs/design/advanced-automata-overview.md)
