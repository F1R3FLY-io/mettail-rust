# Advanced Automata → Disambiguation, Recovery, and Dispatch Integration

## Overview

This document records the integration of advanced automata analysis (modules M1--M11) into PraTTaIL's disambiguation, error recovery, and dispatch subsystems. The work spans 12 implementation sprints across 4 phases.

## Phase A: Leverage Existing REAL Analysis (Sprints A1--A3)

### A1: VPA Nesting Depth → Recovery Cost Modulation

**Files**: `vpa.rs`, `lib.rs`, `recovery.rs`, `pipeline.rs`

Added `max_nesting_bound` field to `VpaAnalysis` (set to VPA state count). When current parse depth exceeds this bound during error recovery, skip actions are strongly favored (0.3x multiplier) since input is structurally beyond the grammar's capacity. The VPA state count bounds well-formed nesting: each nesting level requires a distinct stack state.

**New fields**: `VpaAnalysis.max_nesting_bound`, `PipelineAnalysis.vpa_max_nesting_bound`, `RecoveryConfig.vpa_nesting_ceiling`

### A2: VPA Bracket Mismatches → Recovery Insert Penalty

**Files**: `vpa.rs`, `lib.rs`, `recovery.rs`, `pipeline.rs`

When VPA analysis finds tokens used as both call and return symbols (e.g., `|` in Rust closures), InsertToken for those tokens gets a 2.0x penalty. Added `bracket_mismatch_ids: BTreeSet<TokenId>` to `RecoveryWfst` with setter and penalty helper. The penalty is applied in both `find_best_recovery()` and `find_best_recovery_contextual()`.

**New fields**: `PipelineAnalysis.bracket_mismatch_tokens`, `RecoveryWfst.bracket_mismatch_ids`

### A3: Alternating Bisimilar Categories → Constructor Weight Discount

**Files**: `pipeline.rs`, `cost_benefit.rs`

Bisimilar category pairs (not in `non_bisimilar_pairs`) indicate redundant NFA try-all. The lexicographically second category in each pair gets +0.5 tropical weight penalty on all its `constructor_weights`, deprioritizing it during dispatch ordering.

## Phase B: Enhance Key Stubs to Real Analysis (Sprints B1--B5)

### B1: Symbolic Guard Analysis -- Real SFA from Grammar FIRST Sets

**File**: `symbolic.rs`

Rewrote `analyze_from_bundle()` from trivial stub to real analysis:
- Extracts leading terminals from each rule's syntax items
- Detects overlapping guards (same-category rules sharing leading terminals)
- Detects subsumed guards (one rule's terminal set is a subset of another's)
- Marks rules with no leading terminals AND no NonTerminal start as unsatisfiable

**Impact**: SYM01-DCE now eliminates genuinely dead rules. SYM01--04 lints report real guard issues.

### B2: Buchi SCC Analysis -- Real Liveness from Grammar Graph

**File**: `buchi.rs`

Rewrote `analyze_from_bundle()` from trivial stub to real SCC-based analysis:
- Builds category dependency graph (edges from NonTerminal references)
- Runs Tarjan's algorithm for SCC detection
- Identifies accepting SCCs (self-recursive or mutually recursive categories)
- Added `accepting_sccs: Vec<Vec<String>>` to `BuchiAnalysis`

**Impact**: O01/O02 lints report real liveness data. Enables Sprint C2.

### B3: Probabilistic -- Structure-Weighted Entropy (Not Uniform)

**File**: `probabilistic.rs`

Rewrote `analyze_from_bundle()` from uniform weights to structure-based:
- Rule weight = `1.0 / (1.0 + syntax_items.len())` (simpler rules → higher weight)
- Per-category normalization (weights sum to 1.0 per category)
- Real Shannon entropy computation: `-Sigma p_i * ln(p_i)`
- Low selectivity detection (threshold 0.01)

**Impact**: PR01-WEIGHT now blends meaningful non-uniform weights. Enables Sprint C3.

### B4: Register -- Real Dead-Register Detection from Grammar Binders

**File**: `register_automata.rs`

Rewrote `analyze_from_bundle()` from empty detection to real analysis:
- `IdentCapture`/`Binder`/`BinderCollection` → Store operations
- `NonTerminal`/`Collection` → TestEq operations
- Dead register = Store but no TestEq (stored but never tested)

**Impact**: RA01-SKIP now populates `dead_binder_categories` with real data.

### B5: Multi-Tape -- Real Tape Independence Detection

**File**: `multi_tape.rs`

Rewrote `analyze_from_bundle()` from empty detection to real analysis:
- Builds category dependency graph with Union-Find connected components
- Singleton components → disconnected tapes
- Identical rule structure detection → overlapping tapes

**Impact**: MT01-INFO now populates `independent_categories` with real data.

## Phase C: Cross-Module Integrations (Sprints C1--C4)

### C1: Symbolic Guard Overlap → Cross-Category Disambiguation

**Files**: `lib.rs`, `pipeline.rs`

Added `guard_disambiguated_tokens: HashSet<String>` to `PipelineAnalysis`. Populated from `SymbolicAnalysis.subsumed_guards` -- tokens where guard subsumption proves one category's guard contains another's.

### C2: Buchi Accepting SCCs → Liveness-Aware Recovery

**Files**: `lib.rs`, `pipeline.rs`, `recovery.rs`, `buchi.rs`

Added `recursive_scc_categories: HashSet<String>` to `PipelineAnalysis`, populated from `BuchiAnalysis.accepting_sccs`. Recovery in recursive categories discounts InsertToken (0.7x) to maintain the recursive loop and penalizes SkipToSync (1.3x) to avoid breaking it.

**New fields**: `RecoveryWfst.recursive_category`, `PipelineAnalysis.recursive_scc_categories`

### C3: Entropy-Driven Per-Category Beam Width

**Files**: `lib.rs`, `pipeline.rs`

Added `per_category_entropy: HashMap<String, f64>` to `PipelineAnalysis`. Computed from probabilistic analysis -- groups rule selectivities by category and computes per-category Shannon entropy. High-entropy categories need wider beams; low-entropy need none.

### C4: Symbolic Subsumption → Predicate Dispatch Ordering

**File**: `predicate_dispatch.rs`

Added `order_by_specificity()` function that reorders predicates by guard specificity using subsumption data. More specific guards (subsumed by more general ones) are tried first, implementing most-specific-first dispatch semantics (Ernst et al. 1998).

## Test Summary

| Sprint | New Tests | Module |
|--------|-----------|--------|
| A1 | 2 | recovery.rs |
| A2 | 3 | recovery.rs |
| A3 | 3 | pipeline.rs |
| B1 | 5 | symbolic.rs |
| B2 | 4+ | buchi.rs |
| B3 | 5 | probabilistic.rs |
| B4 | 4 | register_automata.rs |
| B5 | 3 | multi_tape.rs |
| C1 | 3 | pipeline.rs |
| C2 | 2 | recovery.rs |
| C3 | 3 | pipeline.rs |
| C4 | 3 | predicate_dispatch.rs |

**Total**: 2,626 tests pass (all-features), zero failures.

## Verification

```bash
cargo check --workspace                    # default features
cargo check --workspace --all-features      # all features
cargo test --workspace --all-features       # full test suite
```

## Theory Documentation

Five formal theory documents support the disambiguation integration, located in
`prattail/docs/theory/disambiguation/`:

| Document | Topic | Key Results |
|----------|-------|-------------|
| [symbolic-guard-algebra.md](../../prattail/docs/theory/disambiguation/symbolic-guard-algebra.md) | Guard extraction, overlap, subsumption via SFA | Overlap implies ambiguity; subsumption-ordered dispatch is sound |
| [buchi-scc-liveness.md](../../prattail/docs/theory/disambiguation/buchi-scc-liveness.md) | Tarjan SCC on category dependency graph | Accepting SCCs = recursive categories; recovery cost modulation preserves correctness |
| [information-theoretic-dispatch.md](../../prattail/docs/theory/disambiguation/information-theoretic-dispatch.md) | Shannon entropy for per-category beam width | High-entropy categories need wider beams; structure-weighted entropy outperforms uniform |
| [predicate-dispatch-ordering.md](../../prattail/docs/theory/disambiguation/predicate-dispatch-ordering.md) | Most-specific-first dispatch via subsumption | Specificity-ordered dispatch is a permutation; Ernst et al. 1998 |
| [vpa-nesting-recovery.md](../../prattail/docs/theory/disambiguation/vpa-nesting-recovery.md) | VPA state count bounds well-formed nesting | Depth exceeding bound implies structural violation; skip-favoring is sound |

## Testing Strategy

Property-based testing with 60 proptest invariants validates mathematical
correctness across arbitrary grammars. The testing methodology is documented in:

- **Architecture document**: [prattail/docs/design/disambiguation/09-automata-disambiguation-integration.md](../../prattail/docs/design/disambiguation/09-automata-disambiguation-integration.md)
  -- the 3-phase integration design (A: leverage existing, B: stub-to-real, C: cross-module)
- **Testing strategy**: [prattail/docs/design/disambiguation/10-disambiguation-testing-strategy.md](../../prattail/docs/design/disambiguation/10-disambiguation-testing-strategy.md)
  -- 60 proptest properties, grammar generators, feature gate matrix, edge case catalog

### Property Distribution

| Phase | Properties | Modules |
|-------|------------|---------|
| A (Leverage Existing) | 15 | recovery.rs, pipeline.rs |
| B (Stub-to-Real) | 29 | symbolic.rs, buchi.rs, probabilistic.rs, register_automata.rs, multi_tape.rs |
| C (Cross-Module) | 9 | pipeline.rs, predicate_dispatch.rs |
| Predicate Dispatch | 7 | predicate_dispatch.rs |

### Key Test Generators

| Generator | Location | Purpose |
|-----------|----------|---------|
| `arb_grammar(num_cats, rules_per_cat)` | `test_generators.rs` | General grammar generation with controlled complexity |
| `arb_small_grammar()` | `test_generators.rs` | 2--4 categories, 1--3 rules each |
| `arb_signature()` | `predicate_dispatch.rs` | Random `PredicateSignature` bitfield |
| `arb_category()` | `predicate_dispatch.rs` | Single category name for dispatch tests |
