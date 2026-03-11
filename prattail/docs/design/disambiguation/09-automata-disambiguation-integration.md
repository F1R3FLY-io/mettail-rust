# Advanced Automata Disambiguation Integration

## 1. Overview

This document describes the integration of eleven analysis modules (M1--M11) into
PraTTaIL's disambiguation, error recovery, and dispatch subsystems. The work is
organized in three phases that form a cascade:

- **Phase A** (Leverage Existing Analysis): Three sprints wire existing VPA and
  alternating automata analysis into recovery cost modulation and dispatch weight
  adjustment. No new algorithms are introduced; the sprints simply propagate
  analysis results that were previously computed but not consumed.

- **Phase B** (Stub-to-Real Analysis): Five sprints replace trivial stub
  implementations with grammar-driven analysis. After Phase B, the analysis
  modules produce meaningful results that can feed downstream consumers.

- **Phase C** (Cross-Module Integrations): Four sprints compose Phase B results
  into cross-cutting transformations: guard disambiguation in prediction, SCC-aware
  recovery cost, entropy-driven beam width, and specificity-ordered predicate
  dispatch.

## 2. Architecture Diagram

The data-flow from analysis modules through the pipeline to consumer subsystems:

```
 Analysis Modules
 ════════════════════════════════════════════════════════════════════════
 ┌────────────────┐  ┌────────────────┐  ┌─────────────────────┐
 │ M1 Symbolic    │  │ M2 Buchi       │  │ M3 Alternating      │
 │ guard_sat()    │  │ accepting      │  │ non_bisimilar       │
 │ subsumed()     │  │   _sccs        │  │   _pairs            │
 │ overlapping()  │  │ has_accepting  │  │ bisimilar_discount  │
 └───────┬────────┘  │   _cycle       │  └──────────┬──────────┘
         │           └───────┬────────┘             │
         │                   │                      │
 ┌───────┴────────┐  ┌──────┴─────────┐  ┌─────────┴──────────┐
 │ M4 VPA         │  │ M6 Register    │  │ M7 Probabilistic   │
 │ max_nesting    │  │ dead_registers │  │ rule_selectivities │
 │   _bound       │  │ dead_binder    │  │ entropy()          │
 │ bracket        │  │   _categories  │  │ is_normalized      │
 │   _mismatches  │  │                │  │                    │
 └───────┬────────┘  └───────┬────────┘  └─────────┬──────────┘
         │                   │                      │
 ┌───────┴────────┐  ┌──────┴─────────┐             │
 │ M8 Multi-Tape  │  │ M5 Parity Tree │             │
 │ independent    │  │ (diagnostic    │             │
 │   _categories  │  │  only)         │             │
 │ overlapping    │  └────────────────┘             │
 │   _tapes       │                                 │
 └───────┬────────┘                                 │
         │                                          │
 ════════╪══════════════════════════════════════════╪════════════════
         ▼                                          ▼
 ┌────────────────────────────────────────────────────────────────┐
 │              build_pipeline_analysis()  (pipeline.rs)          │
 │                                                                │
 │  vpa_max_nesting_bound ────────────┐                          │
 │  bracket_mismatch_tokens ──────────┤                          │
 │  guard_disambiguated_tokens ───────┤  PipelineAnalysis        │
 │  recursive_scc_categories ─────────┤  (pub struct)            │
 │  per_category_entropy ─────────────┤                          │
 │  constructor_weights (adjusted) ───┘                          │
 └──────┬──────────────────┬──────────────────┬──────────────────┘
        │                  │                  │
        ▼                  ▼                  ▼
 ┌──────────────┐  ┌──────────────┐  ┌────────────────────────┐
 │prediction.rs │  │ recovery.rs  │  │ predicate_dispatch.rs  │
 │              │  │              │  │                        │
 │guard_disamb  │  │nesting ceil  │  │order_by_specificity()  │
 │  _tokens     │  │bracket pen   │  │most-specific-first    │
 │→ skip known  │  │SCC discount  │  │dispatch ordering      │
 │  subsumed    │  │→ cost mods   │  │                        │
 └──────────────┘  └──────────────┘  └────────────────────────┘
```

### Data-Flow Summary

| Source Module | PipelineAnalysis Field | Consumer | Effect |
|---------------|----------------------|----------|--------|
| M4 VPA | `vpa_max_nesting_bound` | recovery.rs | 0.3x skip multiplier beyond ceiling |
| M4 VPA | `bracket_mismatch_tokens` | recovery.rs | 2.0x insert penalty for dual-role brackets |
| M3 Alternating | constructor_weights (adjusted) | pipeline.rs | +0.5 penalty on bisimilar-redundant categories |
| M1 Symbolic | `guard_disambiguated_tokens` | prediction.rs | Skip subsumed-guard alternatives |
| M2 Buchi | `recursive_scc_categories` | recovery.rs | 0.7x insert / 1.3x skip in recursive contexts |
| M7 Probabilistic | `per_category_entropy` | pipeline.rs | Beam width scaling (high entropy = wider beam) |
| M1 Symbolic | subsumed_guards | predicate_dispatch.rs | Most-specific-first reordering |

## 3. Phase A: Leveraging Existing Analysis

Phase A wires already-computed analysis results into downstream consumers. No new
analysis algorithms are introduced; the work is purely plumbing.

### A1: VPA Nesting Depth to Recovery Cost Modulation

**Rationale.** VPA analysis computes `max_nesting_bound` (bounded by VPA state
count). When the parser's current nesting depth exceeds this bound during error
recovery, the input is structurally beyond what the grammar can describe. Skip
actions should be strongly favored to exit the over-deep context quickly.

**Formal Transformation.** Let `d` be the current nesting depth and `c` be the
VPA nesting ceiling:

```
RecoveryCost_modified = if d > c then
    RecoveryCost_skip  * 0.3    (strongly favor skip)
    RecoveryCost_insert * 1.0   (neutral insert)
  else
    RecoveryCost_skip  * 1.0    (neutral)
    RecoveryCost_insert * 1.0   (neutral)
```

**Algorithm.** In `RecoveryConfig`, the `vpa_nesting_ceiling` field (Option<usize>)
is set from `PipelineAnalysis.vpa_max_nesting_bound`. During `find_best_recovery()`,
if `current_depth > vpa_nesting_ceiling`, the skip action multiplier is set to 0.3.

**Code References.**
- `vpa.rs`: `VpaAnalysis.max_nesting_bound` field
- `recovery.rs`: `RecoveryConfig.vpa_nesting_ceiling`, depth check in `find_best_recovery()`
- `pipeline.rs`: `PipelineAnalysis.vpa_max_nesting_bound`, wiring in `build_pipeline_analysis()`

### A2: Bracket Mismatch Penalty in Recovery

**Rationale.** VPA analysis identifies tokens used as both call and return symbols
(e.g., `|` in Rust closures, `` ` `` in some languages). Inserting such tokens
during error recovery is dangerous because it may flip the nesting structure.

**Formal Transformation.** Let `B` be the set of bracket-mismatch token IDs:

```
InsertCost(t) = if t ∈ B then
    BaseCost(t) * 2.0
  else
    BaseCost(t) * 1.0
```

**Algorithm.** `RecoveryWfst` stores `bracket_mismatch_ids: BTreeSet<TokenId>`.
The setter `set_bracket_mismatch_ids()` populates this from `PipelineAnalysis
.bracket_mismatch_tokens`. In both `find_best_recovery()` and
`find_best_recovery_contextual()`, InsertToken actions for tokens in this set
receive a 2.0x penalty.

**Code References.**
- `vpa.rs`: `VpaAnalysis.bracket_mismatches` field
- `recovery.rs`: `RecoveryWfst.bracket_mismatch_ids`, `penalty_for_bracket_mismatch()`
- `pipeline.rs`: `PipelineAnalysis.bracket_mismatch_tokens`

### A3: Bisimilar Weight Discount for Dispatch Ordering

**Rationale.** When the alternating automata module identifies that two grammar
categories are bisimilar (not in `non_bisimilar_pairs`), they share structural
parse behavior. NFA try-all on both categories is redundant. The lexicographically
second category in each pair receives a weight penalty to deprioritize it.

**Formal Transformation.** For bisimilar pair (C_a, C_b) where C_a < C_b lexicographically:

```
constructor_weight(r) = if r ∈ rules(C_b) then
    original_weight(r) + TropicalWeight(0.5)
  else
    original_weight(r)
```

The +0.5 tropical penalty shifts bisimilar-redundant categories lower in dispatch
ordering without fully eliminating them.

**Algorithm.** In `build_pipeline_analysis()`, iterate over the alternating analysis
`non_bisimilar_pairs`. For each pair of categories NOT in `non_bisimilar_pairs`,
the lexicographically second category's constructor weights are penalized by +0.5.

**Code References.**
- `alternating.rs`: `AlternatingAnalysis.non_bisimilar_pairs`
- `pipeline.rs`: bisimilar discount loop in `build_pipeline_analysis()`
- `cost_benefit.rs`: `WeightedAlternatingAnalysis` optimization variant

## 4. Phase B: Stub-to-Real Analysis

Phase B replaces trivial stub `analyze_from_bundle()` implementations with real
grammar-driven algorithms. Each sprint below documents the before/after state,
the algorithm, and the key data structures.

### B1: Symbolic Guard Analysis (symbolic.rs)

**Before:** `analyze_from_bundle()` returned an empty `SymbolicAnalysis` with no
overlapping or subsumed guards.

**After:** Real guard extraction from grammar FIRST sets:

1. For each rule in each category, extract the leading terminals from
   the first syntax item (Terminal, IdentCapture, Binder, NonTerminal).
2. Within each category, compute pairwise guard overlap:
   `overlapping(r_i, r_j) iff G(r_i) ∩ G(r_j) != emptyset`
3. Detect subsumption: `subsumed(r_i, r_j) iff G(r_i) subset G(r_j)`
4. Mark rules with empty guards and no NonTerminal start as unsatisfiable.

**Key Data Structures.**
- `SymbolicAnalysis.overlapping_guards: Vec<(String, String)>` -- pairs of rule
  labels whose guard sets intersect
- `SymbolicAnalysis.subsumed_guards: Vec<(String, String)>` -- pairs (r_sub, r_super)
  where r_sub's guard set is a proper subset of r_super's
- `SymbolicAnalysis.unsatisfiable_guards: Vec<String>` -- rules with empty guard sets

**Impact.** SYM01--SYM04 lints now report real guard issues instead of vacuous
success. SYM01-DCE codegen eliminates genuinely dead rules.

### B2: Buchi SCC Analysis (buchi.rs)

**Before:** `analyze_from_bundle()` returned an empty `BuchiAnalysis` with no SCCs.

**After:** Real SCC-based liveness analysis on the category dependency graph:

1. Build a directed graph where vertices are categories and edges connect
   categories that reference each other via NonTerminal items.
2. Run Tarjan's algorithm to identify all strongly connected components.
3. Mark SCCs as "accepting" if they contain a self-loop (self-recursive category)
   or have more than one member (mutually recursive).

**Key Data Structures.**
- `BuchiAnalysis.accepting_sccs: Vec<Vec<String>>` -- each inner Vec is a set of
  mutually recursive category names
- `BuchiAnalysis.has_accepting_cycle: bool` -- true iff any accepting SCC exists
- `BuchiAnalysis.num_states: usize` -- number of categories in the dependency graph

**Impact.** O01/O02 lints report real liveness data. Enables Sprint C2.

### B3: Probabilistic Structure-Weighted Entropy (probabilistic.rs)

**Before:** `analyze_from_bundle()` assigned uniform weights (1/|rules|) to all rules.

**After:** Structure-based weight assignment and real entropy computation:

1. Each rule's weight is `1.0 / (1.0 + syntax_items.len())`. Simpler rules
   (fewer syntax items) receive higher weights, reflecting the observation that
   simpler productions are more common in typical parse inputs.
2. Per-category normalization ensures weights sum to 1.0 within each category.
3. Shannon entropy: `H(C) = -sum(p_i * ln(p_i))` for each category C, where
   p_i is the normalized weight of rule i.
4. Low selectivity detection: rules with weight below 0.01 threshold are flagged.

**Key Data Structures.**
- `ProbabilisticAnalysis.rule_selectivities: Vec<f64>` -- per-rule normalized weights
- `ProbabilisticAnalysis.entropy: f64` -- total grammar entropy
- `ProbabilisticAnalysis.low_selectivity_rules: Vec<String>` -- rules below threshold
- `ProbabilisticAnalysis.is_normalized: bool` -- always true after analysis

**Impact.** PR01-WEIGHT blends meaningful non-uniform weights. Enables Sprint C3.

### B4: Register Dead-Register Detection (register_automata.rs)

**Before:** `analyze_from_bundle()` returned empty `dead_registers` and
`dead_binder_categories`.

**After:** Real binder/use analysis from grammar syntax items:

1. Scan each rule's syntax items for Store operations (IdentCapture, Binder,
   BinderCollection) and TestEq operations (NonTerminal, Collection references).
2. A "register" (category) is dead if it has Store operations but no TestEq
   operations -- values are captured but never matched against.

**Key Data Structures.**
- `RegisterAnalysis.dead_registers: HashSet<String>` -- categories with stores but no tests
- `RegisterAnalysis.dead_binder_categories: HashSet<String>` -- same set, used for
  RA01-SKIP codegen optimization

**Impact.** RA01-SKIP populates real dead binder data, enabling alpha-equivalence
skip in codegen.

### B5: Multi-Tape Independence Detection (multi_tape.rs)

**Before:** `analyze_from_bundle()` returned empty independence/overlap sets.

**After:** Real category connectivity analysis via Union-Find:

1. Build a category dependency graph (same structure as B2).
2. Use Union-Find to compute connected components.
3. Singleton components (categories with no cross-references) are disconnected tapes.
4. Categories with identical rule structure patterns are flagged as overlapping tapes.

**Key Data Structures.**
- `MultiTapeAnalysis.independent_categories: Vec<String>` -- singleton-component
  categories
- `MultiTapeAnalysis.overlapping_tapes: Vec<(String, String)>` -- structurally
  identical category pairs

**Impact.** MT01-INFO populates real tape independence data for diagnostics.

## 5. Phase C: Cross-Module Integrations

Phase C composes Phase B results into cross-cutting transformations that modify
disambiguation, recovery, and dispatch behavior.

### C1: Guard Disambiguation (pipeline.rs)

**Data Flow.**

```
symbolic.rs                pipeline.rs              prediction.rs
 SymbolicAnalysis    ──►  guard_disambiguated   ──►  dispatch table
   .subsumed_guards         _tokens                   generation
                          : HashSet<String>
```

**Transformation Rule.** For each (r_sub, r_super) in `subsumed_guards`,
generate a `guard_disambiguated_token` label `"<Category>::<RuleName>"`.
These tokens are known to be safely subsumed -- the subsuming rule's guard
is a strict superset. Prediction can skip the subsumed rule when the
subsumer succeeds.

**Safety Argument.** Guard subsumption is a monotone set inclusion:
`G(r_sub) subset G(r_super)` means every token that matches r_sub also
matches r_super. Skipping r_sub when r_super parses is sound because
any input matching r_sub would also match r_super, which covers the same
parse paths.

### C2: Liveness-Aware Recovery (recovery.rs)

**Data Flow.**

```
buchi.rs                  pipeline.rs              recovery.rs
 BuchiAnalysis      ──►  recursive_scc       ──►   RecoveryWfst
   .accepting_sccs        _categories                .recursive_category
                        : HashSet<String>
```

**Transformation Rule.** When the current parse category is in
`recursive_scc_categories`:

```
InsertToken cost *= 0.7    (discount: preserve recursive loop)
SkipToSync  cost *= 1.3    (penalty: avoid breaking recursion)
```

When the current parse category is NOT in `recursive_scc_categories`:

```
InsertToken cost *= 1.0    (neutral)
SkipToSync  cost *= 1.0    (neutral)
```

**Safety Argument.** The modifiers only change the *ranking* of recovery
candidates, not the set of candidates. The parser still considers all
recovery options; it simply prefers insertion over skip in recursive
contexts. Since any recovery action produces a valid (possibly error-node-
annotated) AST, the modifiers cannot introduce unsound parse results.

### C3: Per-Category Entropy for Beam Width (pipeline.rs)

**Data Flow.**

```
probabilistic.rs          pipeline.rs              dispatch ordering
 ProbabilisticAnalysis ►  per_category_entropy ──►  beam width scaling
   .rule_selectivities    : HashMap<String, f64>
```

**Transformation Rule.** Group rule selectivities by category. For each
category C with rules r_1, ..., r_k having selectivities s_1, ..., s_k:

```
H(C) = -sum_{i=1}^{k} (s_i * ln(s_i))
```

Categories with high entropy (many equally-weighted rules) need wider beams
for NFA try-all. Categories with low entropy (one dominant rule) need
minimal or no beam.

**Safety Argument.** Entropy is purely informational -- it guides beam width
heuristics but does not exclude any parse path. A wider beam considers more
alternatives; a narrower beam is a performance optimization that may prune
low-probability paths but does not affect correctness of the highest-ranked
parse.

### C4: Predicate Dispatch Ordering (predicate_dispatch.rs)

**Data Flow.**

```
symbolic.rs                predicate_dispatch.rs
 SymbolicAnalysis    ──►   order_by_specificity()
   .subsumed_guards          most-specific-first
                             reordering
```

**Transformation Rule.** `order_by_specificity()` reorders a list of
predicate labels so that more specific guards (those subsumed by more
general ones) appear first. The algorithm:

1. Build a specificity score for each label: count how many other labels
   subsume it (higher count = more specific).
2. Sort by (specificity descending, original grammar order ascending).
3. Return the reordered label list.

This implements **most-specific-first** dispatch semantics (Ernst, Kaplan,
Chambers 1998): try the narrowest matching guard first, falling through to
broader guards only on failure.

**Safety Argument.** Reordering is a permutation of the original labels.
Every label is still tried; only the order changes. Since predicate
dispatch tries guards in order and takes the first match, placing more
specific guards first ensures that a specific match is preferred over a
general one. This cannot introduce false matches (every match was already
possible) and cannot suppress valid matches (every guard is still present).

## 6. Phase Composition: A then B then C

The three phases form a pipeline cascade:

```
Phase A: Leverage Existing Analysis
  ├─ A1: VPA nesting → recovery.rs         ─┐
  ├─ A2: VPA brackets → recovery.rs         ├─ (independent, parallel)
  └─ A3: Bisimilar → pipeline.rs            ─┘

Phase B: Stub-to-Real Analysis
  ├─ B1: Symbolic guards (symbolic.rs)       ─┐
  ├─ B2: Buchi SCCs (buchi.rs)               │
  ├─ B3: Probabilistic entropy (prob.rs)      ├─ (independent, parallel)
  ├─ B4: Register dead-detect (register.rs)  │
  └─ B5: Multi-tape independence (multi.rs)  ─┘

Phase C: Cross-Module Integrations
  ├─ C1: B1 → guard_disambiguated_tokens (pipeline.rs)  ─┐
  ├─ C2: B2 → recursive_scc_categories (recovery.rs)     │ (B depends on
  ├─ C3: B3 → per_category_entropy (pipeline.rs)          ├─  completion of
  └─ C4: B1 → order_by_specificity (pred_dispatch.rs)    ─┘  Phase B)
```

Phase A can be implemented independently of Phases B and C, because it
consumes already-computed analysis results. Phase C depends on Phase B,
because it consumes the enhanced analysis results.

## 7. Safety Invariants

Each transformation preserves parsing correctness through a specific
mechanism:

| Sprint | Invariant | Mechanism |
|--------|-----------|-----------|
| A1 | Recovery still considers all candidates | Multiplier changes ranking, not candidate set |
| A2 | Insert penalty does not eliminate candidates | Cost increase, not removal |
| A3 | Bisimilar discount does not eliminate categories | Weight adjustment, not removal |
| C1 | Subsumed guards remain in the grammar | Skip is advisory, not mandatory |
| C2 | Recursive recovery modifiers preserve candidate set | Same as A1 |
| C3 | Entropy is informational only | No candidate elimination |
| C4 | Reordering is a permutation | All guards still tried |

**Global Invariant.** No transformation removes a parse path. Transformations
only change the *ranking* of parse paths (via cost modifiers, weight adjustments,
or reordering). Since the parser always selects the highest-ranked valid path, and
all valid paths remain in the candidate set, correctness is preserved.

## 8. Cross-References

### Theory Documents

| Topic | Document |
|-------|----------|
| Guard extraction & subsumption | [symbolic-guard-algebra.md](../../theory/disambiguation/symbolic-guard-algebra.md) |
| SCC liveness & recovery | [buchi-scc-liveness.md](../../theory/disambiguation/buchi-scc-liveness.md) |
| Information-theoretic dispatch | [information-theoretic-dispatch.md](../../theory/disambiguation/information-theoretic-dispatch.md) |
| Predicate dispatch ordering | [predicate-dispatch-ordering.md](../../theory/disambiguation/predicate-dispatch-ordering.md) |
| VPA nesting & recovery | [vpa-nesting-recovery.md](../../theory/disambiguation/vpa-nesting-recovery.md) |

### Design Documents

| Topic | Document |
|-------|----------|
| Advanced automata overview | [advanced-automata-overview.md](../advanced-automata-overview.md) |
| Codegen optimizations | [automata-codegen-optimizations.md](../automata-codegen-optimizations.md) |
| Testing strategy | [10-disambiguation-testing-strategy.md](10-disambiguation-testing-strategy.md) |
| Integration record | [automata-disambiguation-integration.md](../../../docs/design/made/automata-disambiguation-integration.md) |
| Disambiguation README | [README.md](README.md) |

### Source Files

| File | Sprints | Role |
|------|---------|------|
| `prattail/src/symbolic.rs` | B1, C1, C4 | Guard extraction, overlap, subsumption |
| `prattail/src/buchi.rs` | B2, C2 | Category dependency graph, Tarjan SCC |
| `prattail/src/probabilistic.rs` | B3, C3 | Structure weights, Shannon entropy |
| `prattail/src/register_automata.rs` | B4 | Dead-register detection from binders |
| `prattail/src/multi_tape.rs` | B5 | Union-Find connected components |
| `prattail/src/predicate_dispatch.rs` | C4 | `order_by_specificity()` |
| `prattail/src/pipeline.rs` | A3, C1, C3 | `build_pipeline_analysis()`, field population |
| `prattail/src/recovery.rs` | A1, A2, C2 | `RecoveryWfst`, cost modulation |
| `prattail/src/vpa.rs` | A1, A2 | `VpaAnalysis.max_nesting_bound`, bracket mismatches |
| `prattail/src/alternating.rs` | A3 | `AlternatingAnalysis.non_bisimilar_pairs` |
| `prattail/src/lib.rs` | all | `PipelineAnalysis` struct fields |

### References

- D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and transducers." CAV 2017.
- Ernst, M., Kaplan, C. & Chambers, C. (1998). "Predicate dispatch: A unified theory of dispatch." ECOOP 1998.
- Tarjan, R. E. (1972). "Depth-first search and linear graph algorithms." SIAM J. Computing, 1(2), 146--160.
- Shannon, C. E. (1948). "A Mathematical Theory of Communication." Bell System Technical Journal, 27(3), 379--423.
