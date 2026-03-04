# Deferred and Rejected Optimizations

This document catalogs all optimization items from the WFST-Informed Ascent Optimization taxonomy that were not implemented (deferred) or were investigated and rejected. Each entry includes the core intuition, what it would do, why it would matter, where it would sit in the pipeline, its current status, reasoning, and activation conditions.

## Deferred Items

### 6g/6h — Multi-Stratum Ascent Generation

- **Intuition**: Like splitting a jigsaw puzzle into independently solvable sections — if groups of equations/rewrites share no constructors, they form independent connected components in the dependency graph. Each component can be evaluated in its own Ascent struct, reducing the SCC (Strongly Connected Component) working set of the main fixpoint.
- **What it would do**: For each independent dependency group with ≥5 rules, generate a separate `ascent!` struct with only that group's relations, category rules, and equation/rewrite rules. Chain evaluation: pre-stratum → per-group strata → main fixpoint. Use `group_categories()` to compute per-group category sets.
- **Why it would matter**: Smaller SCCs converge faster in semi-naive evaluation. A grammar with 60 rules split into 3 groups of 20 would see each group's fixpoint operate on ~⅓ the relation size, potentially reducing O(N²) join costs by ~9×.
- **Pipeline position**: After dependency group analysis (Sprint 6d), during Ascent struct generation (language.rs). Between pre-stratum (Sprint 5) and main fixpoint.
- **Status**: Deferred
- **Tier**: D
- **Reasoning**: Each additional `ascent!` struct adds ~5-10s compilation time (from Ascent's macro expansion + monomorphization). Current grammars have mostly single-rule independent groups (RhoCalc: 25/66 groups are singletons). The compilation overhead exceeds runtime savings at current grammar scale.
- **Infrastructure readiness**: 95% — `compute_fine_dependency_groups()`, `group_categories()`, and `CategoryFilter` all exist. Missing: per-group Ascent struct generation and chaining in language.rs (~200 LOC).
- **Activation condition**: When a grammar has ≥2 independent groups with ≥5 rules each, the compilation cost is amortized by the reduced SCC iteration count. Profile with `perf` to verify runtime savings exceed +10s compile cost.

### 8c-8g — Isomorphic Category Template Instantiation

- **Intuition**: Like using a form letter where you fill in different names — when two categories have identical WFST structures (same dispatch topology, same number of rules per state), the generated parser code differs only in type names and constructor labels. A `macro_rules!` template could generate the code once and stamp it out per category.
- **What it would do**: For each isomorphic group, generate a `macro_rules!` template parameterized by category name, type name, and action map. Instantiate per category with concrete values from `build_isomorphic_action_maps()`.
- **Why it would matter**: 27% generated code reduction for languages with isomorphic categories. Smaller generated code = faster compilation and potentially better instruction cache utilization.
- **Pipeline position**: During parser code generation (codegen.rs), after isomorphic group detection (Sprint 8b).
- **Status**: Deferred
- **Tier**: D
- **Reasoning**: Analysis showed 1,764 of 2,250 codegen LOC per category is data-driven (DFA tables, dispatch arms, weight literals) — not amenable to `macro_rules!` templating. Only ~210 LOC per category (frame enum + wrappers) can be templated. The 27% reduction doesn't justify the +15% maintenance burden per future codegen change (every change to the template requires understanding the `macro_rules!` expansion).
- **Infrastructure readiness**: 80% — `CanonicalWfstStructure`, `canonical_hash()`, `group_isomorphic_wfsts()`, `build_isomorphic_action_maps()` all exist. Missing: template generation and instantiation in codegen.rs (~400 LOC).
- **Activation condition**: When real grammars have 5+ isomorphic category sets, the template maintenance burden is amortized. Current languages have at most 2-3 isomorphic pairs.

### 9h/9i — Benchmark CI and Automated Profiling

- **Intuition**: Like a financial audit that runs every quarter — continuous benchmarking detects performance regressions before they reach users. Automated profiling with `perf record` and `perf stat` catches hotspot shifts early.
- **What it would do**: Add `criterion` benchmarks for Ascent fixpoint evaluation (per-grammar) to CI. Generate `perf report` flame graphs on each PR. Track metrics: fixpoint iterations, wall-clock time, L1-dcache-load-misses, branch-misses.
- **Why it would matter**: Without benchmarks, performance regressions are invisible until users report slowdowns. With benchmarks, every PR that touches codegen or runtime gets automatic regression detection.
- **Pipeline position**: CI/CD infrastructure (GitHub Actions workflow).
- **Status**: Deferred
- **Tier**: D
- **Reasoning**: Profiling infrastructure (Sprint perf-opt) already exists locally. CI integration requires: (a) stable benchmark suite with low noise, (b) baseline storage across commits, (c) `perf` availability in CI runners. Current priority is feature development over CI hardening.
- **Infrastructure readiness**: 95% — `criterion` benchmarks exist for parser pipelines. Missing: Ascent-specific benchmarks (~100 LOC), CI workflow definition (~50 LOC YAML), baseline storage mechanism.
- **Activation condition**: When runtime performance is a user-facing concern. Currently all grammars evaluate in <100ms.

## Rejected Items

### R2 — Lazy Binder Construction via `OnceLock`

- **Intuition**: Like computing a value only when first needed (lazy evaluation) — if `close_term()` is expensive (O(depth) per binder), deferring it until the binder is actually accessed could save work for binders that are created but never inspected.
- **What it would do**: Wrap `Scope::new()` to skip `close_term()`, storing the unclosed pattern+body. First call to `unbind()` or `term_eq()` would trigger lazy `close_term()` via `OnceLock`.
- **Why it would matter (hypothetical)**: For synthetic terms with 100+ nesting depth, `close_term()` dominates construction cost. Lazy construction would defer this cost to the consumer.
- **Pipeline position**: Runtime, in `Scope::new()` (binding.rs).
- **Status**: **Rejected** — proven unsound
- **Tier**: —
- **Reasoning**: `close_term()` must happen inside-out (innermost binder first) to produce correct De Bruijn indices. Deferred `close_term` reorders the traversal to outside-in, producing wrong indices for shadowed variables. A batch-close alternative (collecting all binders in a stack, then closing all at once) is theoretically sound but high-complexity (~500 LOC) with low ROI for real-world programs (3-10 nesting depth, not 100).
- **Proof**: See Sprint 5 analysis in `ascent-optimization.md`, Phase 6. Key example:
  ```
  λx. λx. x     (inner x shadows outer x)

  Inside-out close_term:
    1. Close inner scope: x → BoundVar(0, 0) ✓
    2. Close outer scope: outer x already closed → no change ✓

  Outside-in close_term (deferred):
    1. Close outer scope: ALL x → BoundVar(0, 0) ✗ (captures inner x too)
    2. Close inner scope: x already bound → no change ✗
  ```
  Result: both `x` references point to the outer binder, breaking shadowing semantics.
- **Conclusion**: Fundamentally incompatible with correct De Bruijn indexing under shadowing. No activation condition — permanently rejected.

## Summary Statistics

| Status | Count | Description |
|--------|-------|-------------|
| Implemented | 13 | Sprints 0-9, A, B, C |
| Deferred | 3 | 6g/6h, 8c-8g, 9h/9i |
| Rejected | 1 | R2 (lazy binder) |
| **Total** | **17** | All cataloged items |

## Taxonomy Tiers

The deferred items were classified into tiers during the deep-dive audit:

| Tier | Description | Items |
|------|-------------|-------|
| A | High-value, low-risk, ready to implement | N10, R1, C1 (all implemented) |
| B | Medium-value, moderate complexity | (none remaining) |
| C | Lower-value or high-complexity | (none remaining) |
| D | Infrastructure or scale-dependent | 6g/6h, 8c-8g, 9h/9i |

All Tier A items have been implemented (Sprints A, B, C). The remaining Tier D items require either scale triggers (larger grammars) or infrastructure investment (CI) to justify implementation.
