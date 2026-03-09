# Codegen Optimization Modules

The `macros/src/logic/` module system implements the Ascent Datalog code generation
pipeline for MeTTaIL grammars. This document provides an index of all module
documentation, an architecture overview, and a recommended reading order.

## Architecture

The code generation pipeline transforms a `LanguageDef` (parsed grammar specification)
into Ascent Datalog source code. The modules collaborate in a layered pipeline
orchestrated by `mod.rs`.

### Module Dependency Diagram

```
                          mod.rs (orchestration)
                         /    |    \         \
                        v     v     v         v
                 relations  categories  equations  ── rules
                    .rs        .rs        .rs        .rs
                                           |          |
                                           v          v
                                      congruence   (shared)
                                         .rs
                                           |
                            ┌──────────────┼──────────────┐
                            v              v              v
                        common.rs    bloom_filter.rs   fusion.rs
                       (utilities)     (ART04)         (BCG02)
                                           |
                                           v
                                     antipattern.rs
                                      (detection)
```

### Data Flow

```
 LanguageDef
     |
     v
 ┌─────────────────────────────────────────────────────────┐
 │  mod.rs  (generate_ascent_source)                       │
 │                                                         │
 │  1. Compute subsumed equations (pattern_trie)           │
 │  2. Detect cancellation pairs                           │
 │  3. Emit depth delta lints (ART05)                      │
 │  4. Emit delta guard lints (ART02)                      │
 │  5. Emit antipattern lints (C-AP01..C-AP05)             │
 │  6. BCG05: normalize-on-insert dedup diagnostic         │
 │  7. BCG02: rule fusion analysis + codegen               │
 │  8. ART06: compute demanded categories                  │
 │  9. BCG06: compute stratification                       │
 │ 10. Generate: relations, categories, equations, rewrites│
 │ 11. Generate: fused rules, pre-stratum, ground seeds    │
 │ 12. Pattern trie analysis (dependency groups, alpha-eq) │
 │ 13. WFST isomorphic group logging                       │
 └───────────────┬─────────────────────────────────────────┘
                 v
          AscentSourceOutput
          {full_output, raw_content, core_raw_content,
           pre_stratum_content, ground_rewrite_seeds}
```

### Module Responsibilities

| Module             | Responsibility                                              |
|--------------------|-------------------------------------------------------------|
| `mod.rs`           | Top-level orchestration, diagnostic emission, pipeline flow |
| `relations.rs`     | Ascent relation declarations (`cat`, `eq_cat`, `rw_cat`, `fold_cat`, projections) |
| `categories.rs`    | Category exploration, term deconstruction, collection projections |
| `equations.rs`     | Reflexivity, equality congruence, user-defined equations, BCG06 stratification |
| `rules.rs`         | Unified rule clause generation, condition ordering, rewrite generation |
| `congruence.rs`    | Explicit rewrite congruence rules (Simple, Collection, Binding) |
| `common.rs`        | Shared utilities: relation names, TLS pool, demand analysis, reachability |
| `antipattern.rs`   | C-AP01..C-AP05 antipattern detection                       |
| `fusion.rs`        | BCG02 rule fusion analysis and fused rule codegen           |
| `bloom_filter.rs`  | ART04 bloom filter for congruence pre-checks                |

## Recommended Reading Order

1. **[README.md](README.md)** (this file) -- architecture overview
2. **[equation-system.md](equation-system.md)** -- equation extraction, reflexivity, congruence, stratification
3. **[rule-generation.md](rule-generation.md)** -- unified rule clause generation, BCG01/BCG04/BCG05
4. **[congruence-closure.md](congruence-closure.md)** -- explicit rewrite congruence (Simple/Collection/Binding)
5. **[bloom-filter.md](bloom-filter.md)** -- ART04 bloom filter pre-check
6. **[rule-fusion.md](rule-fusion.md)** -- BCG02 deconstruction-rewrite chain fusion
7. **[antipattern-detection.md](antipattern-detection.md)** -- C-AP01 through C-AP05 detection

This order follows the logical dependency chain: equations and rules form the
foundation, congruence and bloom filter are consumed by both, fusion and
antipattern detection are standalone analysis passes.

## Feature Gate Dependencies

| Feature             | Modules Affected      | Effect                                   |
|---------------------|-----------------------|------------------------------------------|
| (default)           | All                   | Full codegen pipeline always active       |
| `wfst-log`          | `mod.rs`, `equations.rs`, `rules.rs` | Enables WFST-based dead constructor elimination (Sprint 1), weight-guided rule ordering (Sprint 3/4) |

Note: The codegen optimizations (ART04, ART06, BCG01--BCG06) are always-on
compile-time transformations. They do not require feature gates -- they activate
automatically when applicable conditions are met at macro expansion time.

## Optimization Catalog

Each optimization is documented in detail in its respective module file:

| ID    | Name                           | Module             | Lint Code |
|-------|--------------------------------|--------------------|-----------|
| ART04 | Bloom filter pre-check         | `bloom_filter.rs`  | G37, G38  |
| ART06 | Extended demand filtering      | `common.rs`        | G34       |
| BCG01 | Condition cost ordering        | `rules.rs`         | (silent)  |
| BCG02 | Rule fusion                    | `fusion.rs`        | G42       |
| BCG03 | Equation-active congruence prune | `equations.rs`   | G36       |
| BCG04 | Ground-LHS rewrite seeds       | `rules.rs`         | G35       |
| BCG05 | Normalize-on-insert dedup      | `rules.rs`         | G41       |
| BCG06 | Equation stratification        | `equations.rs`     | G42       |
| C-AP01..05 | Antipattern detection     | `antipattern.rs`   | C-AP01..05|

## Rocq Formal Proofs

Several codegen optimizations have accompanying Rocq proofs establishing
correctness properties. See [`formal/rocq/codegen_optimizations/`](../../../formal/rocq/codegen_optimizations/)
for the full proof suite:

| Proof File                   | Optimization(s) Covered                         |
|------------------------------|--------------------------------------------------|
| `ART01_HashConsing.v`        | ART01 hash consing / epoch interning             |
| `ART05_DepthBound.v`        | ART05 compile-time depth analysis                |
| `ART06_DemandAnalysis.v`    | ART06 demand-driven category filtering           |
| `BCG02_RuleFusion.v`        | BCG02 deconstruction-rewrite fusion              |
| `BCG03_EqCongruencePrune.v` | BCG03 equation-active constructor pruning        |
| `BCG06_EqStrata.v`          | BCG06 SCC-based equation stratification          |
| `AL04_MphPostLex.v`         | AL04 minimal perfect hash for post-lexer dispatch|
| `AL05_ChainCollapse.v`      | AL05 chain collapse in WFST composition          |
| `CD02_DisjointFirst.v`      | CD02 disjoint FIRST set optimization             |
| `CD05_PrefixParse.v`        | CD05 prefix parse optimization                   |

## Cross-References

- **Term operations**: [Term Operations Index](../term-ops/README.md) -- `subst()`, `normalize()`, `depth()`, `is_ground()`, hash-consing analysis
- **Runtime support**: [Runtime Module Index](../../../runtime/docs/README.md) -- `OrdVar`, `Scope`, `InternTable`, `HashBag`, epoch mechanism
- **Pipeline analysis**: [`prattail/src/pipeline.rs`](../../../prattail/src/pipeline.rs) -- WFST-based analysis feeding into codegen
- **Lint system**: [`prattail/src/lint.rs`](../../../prattail/src/lint.rs) -- diagnostic infrastructure
- **Cost-benefit framework**: [`prattail/src/cost_benefit.rs`](../../../prattail/src/cost_benefit.rs) -- optimization gate control
- **Codegen optimization catalog**: [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md)
- **Diagnostics catalog**: [Diagnostics README](../../../prattail/docs/diagnostics/README.md) -- all lint codes
