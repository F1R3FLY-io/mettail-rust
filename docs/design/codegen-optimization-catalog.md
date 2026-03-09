# Codegen Optimization & Lint Expansion Catalog

**Date:** 2026-03-08
**Status:** Authoritative reference
**Scope:** PraTTaIL / MeTTaIL compile-time optimization catalog

## 1. Overview

This catalog enumerates every planned and implemented code-generation
optimization for the MeTTaIL compilation pipeline.  It covers four code
generation backends and one build-system layer:

| Layer | ID Prefix | Backend | Primary Files |
|-------|-----------|---------|---------------|
| Ascent VM Runtime | A-RT | Ascent Datalog fixpoint engine | `macros/src/logic/`, `runtime/src/binding.rs` |
| Ascent Codegen | B-CG | Ascent rule generation | `macros/src/logic/common.rs`, `macros/src/gen/runtime/language.rs` |
| Ascent Antipatterns | C-AP | Compile-time static analysis | `prattail/src/lint.rs` (A01-A10 lints) |
| Lexer Codegen | A-L | DFA-based lexer generation | `prattail/src/lexer.rs`, `prattail/src/automata/` |
| Parser Codegen | B-P | Pratt + RD parser generation | `prattail/src/pratt.rs`, `prattail/src/trampoline.rs`, `prattail/src/recursive.rs` |
| Dispatch Codegen | C-D | Decision tree & cross-category dispatch | `prattail/src/dispatch.rs`, `prattail/src/decision_tree.rs` |
| Pipeline/Build | D-B | Compilation pipeline infrastructure | `prattail/src/pipeline.rs`, `prattail/src/prediction.rs` |

### Relationship to Existing Optimizations

The existing optimizations (Opts 1-5, Sprints 0-C, WFST-informed passes) are
**production-grade, proven, and deployed**.  This catalog describes the **next
generation** of optimizations that build on the same infrastructure:

```
  Existing (deployed)                 This Catalog (planned/in-progress)
  ─────────────────                   ──────────────────────────────────
  Opt 1: Rule Consolidation           A-RT01-06: Ascent VM runtime
  Opt 2: TLS Vec Pool                 B-CG01-06: Ascent codegen patterns
  Opt 3: Dead Rule Pruning            C-AP01-05: Antipattern detection
  Opt 4: OrdVar/Scope Ordering        A-L01-06:  Lexer codegen
  Opt 5: SCC Splitting                B-P01-05:  Parser codegen
  Sprints 0-C: WFST-informed          C-D01-05:  Dispatch codegen
  G1: Backtracking Elimination        D-B01-04:  Pipeline/build
  H1: Context Disambiguation
```

Each optimization in this catalog is registered as an `Optimization` enum
variant in `prattail/src/cost_benefit.rs`, with applicability predicates
evaluated against the `GrammarProfile`.  The corresponding `OptimizationGates`
fields control whether the codegen emits optimized or fallback code paths.

### Entry Structure

Every optimization entry below follows this template:

- **Problem** --- what inefficiency exists
- **Solution** --- what transformation is applied
- **Impact** --- expected speedup or code-size reduction
- **Complexity** --- implementation effort (Low / Medium / High)
- **Files** --- source files that implement or will implement the optimization
- **Proof Requirements** --- what must be formally verified in Rocq

---

## 2. Ascent VM Runtime Optimizations (A-RT01 to A-RT06)

These optimizations target the **runtime behavior** of the generated Ascent
Datalog program --- reducing allocation, iteration count, and memory
consumption during fixpoint evaluation.

### A-RT01: Hash-Consing for Recursive Term Types

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::HashConsing` |
| Gate field | `OptimizationGates::hash_consing` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 10` |
| Speedup weight | 0.15 (high benefit) |
| Compile cost | 0.50 (high) |

**Problem.** Recursive term types (`Box<NonTerminal>`) produce deep, heap-allocated
trees.  During fixpoint iteration, structurally identical sub-terms are
reconstructed and compared repeatedly, causing O(depth) comparisons and
excessive allocation pressure.

**Solution.** Replace `Box<T>` with `Rc<T>` (or `Arc<T>` for concurrent Ascent)
backed by a hash-consing table.  Before constructing a new term node, look up
the table by structural hash.  If found, return the existing `Rc`.  This yields
O(1) equality checks (pointer comparison) and eliminates redundant allocation.

**Impact.**
- Term comparison: O(depth) --> O(1)
- Allocation: proportional to unique sub-terms, not total sub-terms
- Expected parse+eval speedup: 10-30% for equation-heavy grammars

**Complexity.** High --- requires modifying the generated `NonTerminal` type
hierarchy and threading an interning table through all Ascent rules.

**Files.**
- `macros/src/gen/runtime/language.rs` --- type generation
- `runtime/src/binding.rs` --- `OrdVar` comparisons
- `macros/src/logic/common.rs` --- TLS pool interaction

**Proof Requirements.**
- `HashConsEquivalence.v`: hash-consed terms are semantically equivalent to
  boxed terms; pointer equality implies structural equality; the fixpoint
  lattice is unchanged.

---

### A-RT02: Incremental Semi-Naive Delta Guards

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::IncrementalDelta` |
| Gate field | `OptimizationGates::incremental_delta` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 5` |
| Speedup weight | 0.30 |
| Compile cost | 0.35 |

**Problem.** The Ascent engine uses semi-naive evaluation, but the generated
rules do not always emit delta guards on the correct relation.  Rules that
read from a relation `R` that was not updated in the previous iteration
still scan all tuples, wasting cycles.

**Solution.** At codegen time, analyze each rule body to determine which
relations appear in which body clauses.  Generate explicit delta-guard
predicates: a rule body clause for `R` is emitted twice --- once reading
`delta_R` (new tuples only) and once reading the full `R` (with the
complementary clause reading `delta_S`).  This is the standard semi-naive
decomposition applied at the Ascent source level.

**Impact.**
- Eliminates redundant scans of unchanged relations
- Expected fixpoint convergence: 30-50% fewer rule firings for multi-rule
  grammars

**Complexity.** High --- requires rewriting the rule generation logic in
`macros/src/logic/rules.rs` and `macros/src/logic/equations.rs` to produce
the decomposed form.

**Files.**
- `macros/src/logic/rules.rs` --- rewrite rule generation
- `macros/src/logic/equations.rs` --- equation rule generation
- `macros/src/logic/common.rs` --- delta relation naming

**Proof Requirements.**
- `DeltaGuardEquivalence.v`: the decomposed rule set produces the same
  fixpoint as the original rule set under semi-naive semantics.

---

### A-RT03: Relation Indexing Hints

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::RelationIndexing` |
| Gate field | `OptimizationGates::relation_indexing` |
| Tier | 1 (Low complexity) |
| Applicability | `rule_count > 3` |
| Speedup weight | 0.30 |
| Compile cost | 0.05 |

**Problem.** Ascent provides `#[index]` annotations on relation columns for
hash-based lookups.  Without them, body clauses that bind a column constant
scan the entire relation linearly.

**Solution.** Analyze each rule body at codegen time.  For every bound
variable in a body clause, emit an `#[index]` annotation on the
corresponding relation column.  This is a purely additive transformation ---
it never removes existing annotations.

**Impact.**
- Body clause evaluation: O(|R|) --> O(1) amortized per bound column
- Expected speedup: 2-5x for rules with selective joins

**Complexity.** Low --- Ascent's `#[index]` syntax is stable; the analysis
is straightforward.

**Files.**
- `macros/src/logic/relations.rs` --- relation declaration generation
- `macros/src/logic/common.rs` --- index analysis

**Proof Requirements.** None (additive annotation; Ascent guarantees
correctness of indexed relations).

---

### A-RT04: Bloom Filter Pre-Check for Congruence Rules

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::CongruenceBloom` |
| Gate field | `OptimizationGates::congruence_bloom` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 5` |
| Speedup weight | 0.35 |
| Compile cost | 0.15 |

**Problem.** Congruence rules fire for every pair of terms sharing a
constructor and category.  For categories with many constructors, most
firings produce duplicates that are immediately discarded by the relation's
deduplication.

**Solution.** Before inserting into the target relation, probe a per-relation
Bloom filter.  If the Bloom filter returns *definitely not present*, insert
and update the filter.  If *possibly present*, fall through to the normal
deduplication path.  The Bloom filter is maintained as a TLS `Cell<Vec<u64>>`
(bitset) using the same pool pattern as Opt 2.

**Impact.**
- Reduces redundant `HashMap` lookups in deduplication
- Expected speedup: 15-25% for congruence-heavy grammars

**Complexity.** Moderate --- the Bloom filter logic is generated per relation.

**Files.**
- `macros/src/logic/congruence.rs` --- congruence rule generation
- `macros/src/logic/bloom_filter.rs` --- Bloom filter codegen (existing file)

**Proof Requirements.**
- `BloomFilterSoundness.v`: false positives preserve correctness (no tuples
  dropped); false negatives are impossible by construction.

---

### A-RT05: Fixpoint Convergence Bound via Term-Depth Analysis

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::DepthBound` |
| Gate field | `OptimizationGates::depth_bound` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 2` |
| Speedup weight | 0.40 |
| Compile cost | 0.10 |

**Problem.** The Ascent fixpoint loop iterates until no new tuples are
produced.  For some grammars, term depth grows unboundedly due to recursive
constructors, causing non-termination or very slow convergence.

**Solution.** At compile time, analyze the grammar's constructor signature
graph.  Compute the maximum term depth reachable from each category (the
longest acyclic path in the constructor field graph).  Inject a runtime
depth counter into generated rules: if a newly constructed term exceeds the
bound, skip insertion.

**Impact.**
- Guarantees termination for grammars with bounded constructor nesting
- Expected benefit: prevents worst-case infinite loops; minimal happy-path
  overhead (single integer comparison per insertion)

**Complexity.** Moderate --- requires threading a depth counter through term
construction.

**Files.**
- `prattail/src/pipeline.rs` --- depth bound computation
- `macros/src/logic/common.rs` --- depth guard emission

**Proof Requirements.**
- `DepthBoundTermination.v`: if the constructor field graph is acyclic, the
  bounded fixpoint terminates; the bounded fixpoint produces a subset of the
  unbounded fixpoint that is sufficient for all terms of bounded depth.

---

### A-RT06: Demand-Driven Relation Population

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::DemandDriven` |
| Gate field | `OptimizationGates::demand_driven` |
| Tier | 2 (Moderate complexity) |
| Applicability | `category_count >= 2` |
| Speedup weight | 0.50 |
| Compile cost | 0.10 |

**Problem.** The SCC splitting optimization (Opt 5) separates core and
non-core categories.  However, within the core struct, all relations are
populated eagerly even if downstream consumers only query a subset.

**Solution.** Annotate each relation with its downstream consumers (which
rules read it).  At fixpoint start, only seed the entry relation.  Use a
demand-driven worklist: when a rule fires and produces a tuple for
relation `R`, check whether any rule reading `R` is on the active worklist.
If not, defer insertion.

**Impact.**
- Reduces unnecessary work for grammars where only a few categories are
  queried post-fixpoint
- Expected benefit: 10-30% for large multi-category grammars

**Complexity.** Moderate --- requires modifying the Ascent struct to track
which relations are "demanded."

**Files.**
- `macros/src/gen/runtime/language.rs` --- demand tracking
- `macros/src/logic/common.rs` --- consumer graph analysis

**Proof Requirements.**
- `DemandDrivenEquivalence.v`: the demand-driven fixpoint produces the same
  result as the eager fixpoint when restricted to demanded relations.

---

## 3. Ascent Codegen Optimizations (B-CG01 to B-CG06)

These optimizations transform the **structure of generated Ascent rules**
at compile time, reducing the number of rules, reordering joins, and
eliminating redundant computations.

### B-CG01: Join Ordering Optimization

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::JoinOrdering` |
| Gate field | `OptimizationGates::join_ordering` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 5` |
| Speedup weight | 0.40 |
| Compile cost | 0.15 |

**Problem.** Multi-body Ascent rules join several relations.  The join
order affects how many intermediate tuples are materialized.  The default
codegen emits body clauses in declaration order, which may be sub-optimal.

**Solution.** At codegen time, estimate the cardinality of each relation
using WFST constructor weights (from `PipelineAnalysis::constructor_weights`).
Reorder body clauses so that the most selective (lowest-cardinality)
relation is scanned first.  This is the classic query optimization
technique applied to Datalog.

**Impact.**
- Reduces intermediate materialization by scanning selective relations first
- Expected speedup: 20-40% for rules with 3+ body clauses

**Complexity.** Moderate --- requires cardinality estimation and clause
reordering in the rule emitter.

**Files.**
- `macros/src/logic/rules.rs` --- body clause ordering
- `macros/src/logic/equations.rs` --- equation body ordering
- `prattail/src/cost_benefit.rs` --- cardinality estimation from weights

**Proof Requirements.**
- `JoinOrderEquivalence.v`: reordering body clauses in a Datalog rule does
  not change the rule's semantics (commutativity of conjunction).

---

### B-CG02: Rule Fusion for Chained Deconstruction-Rewrite

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::RuleFusion` |
| Gate field | `OptimizationGates::rule_fusion` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 5` |
| Speedup weight | 0.40 |
| Compile cost | 0.40 |

**Problem.** A common Ascent pattern is a two-rule chain: rule A
deconstructs a term into its fields (subterm extraction), and rule B
rewrites the deconstructed fields into a new term.  The intermediate
relation holding the deconstructed fields is read only by rule B.

**Solution.** Detect such chains at codegen time (single-reader
intermediate relations).  Fuse the body of rule A and the head of rule B
into a single rule that deconstructs and rewrites in one step, eliminating
the intermediate relation entirely.

**Impact.**
- Eliminates intermediate relation allocation and tuple storage
- Expected speedup: 15-30% for deconstruction-heavy grammars

**Complexity.** High --- requires dependency analysis across rules and
safe fusion conditions (no other readers, no cycles through the
intermediate).

**Files.**
- `macros/src/logic/common.rs` --- fusion analysis
- `macros/src/logic/helpers.rs` --- consolidated deconstruction rules

**Proof Requirements.**
- `RuleFusionEquivalence.v`: the fused rule produces the same fixpoint
  as the two-rule chain when the intermediate relation has a single reader.

---

### B-CG03: Selective Equality Congruence Pruning

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::EqCongruencePrune` |
| Gate field | `OptimizationGates::eq_congruence_prune` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 3` |
| Speedup weight | 0.35 |
| Compile cost | 0.15 |

**Problem.** Congruence rules are generated for every constructor in every
category.  For categories that have no equations or rewrites, these rules
can never fire (there are no equality facts to propagate through).

**Solution.** At codegen time, compute the set of categories that
participate in equational reasoning (those referenced by `semantic_dependency_groups`).
Skip congruence rule generation for categories outside this set.

**Impact.**
- Reduces generated rule count and Ascent struct size
- Expected reduction: 30-60% fewer congruence rules for grammars with many
  non-equational categories

**Complexity.** Moderate --- extends the existing dead-rule pruning (Opt 3)
with semantic reachability.

**Files.**
- `macros/src/logic/congruence.rs` --- congruence rule generation
- `macros/src/logic/common.rs` --- equational reachability set

**Proof Requirements.**
- `CongruencePruning.v`: categories without equations produce no equality
  facts; therefore congruence rules for such categories derive nothing.
  (Extends `DeadRulePruning.v` with a semantic-layer argument.)

---

### B-CG04: Ground-Term Short-Circuit in Rewrite Rules (IMPLEMENTED)

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::GroundShortCircuit` |
| Gate field | `OptimizationGates::ground_short_circuit` |
| Tier | 1 (Low complexity) |
| Applicability | `rule_count > 2` |
| Speedup weight | 0.40 |
| Compile cost | 0.05 |
| Lint | G35 `ground-rewrite-short-circuit` |

**Problem.** Rewrite rules that match a ground term (no free variables) on
the LHS produce a fixed RHS.  The Ascent evaluation still scans the
relation and performs pattern matching, even though the result is statically
known.

**Solution.** At codegen time, detect ground-LHS rewrite rules (all pattern
positions are literals or fixed constructors).  Generate a direct insertion
of both the LHS term, the RHS term, and the `(lhs, rhs)` rewrite tuple
into the appropriate Ascent relations at fixpoint start, bypassing the
matching loop entirely.  The original Ascent rule is preserved for soundness
(equation-equivalent terms still need to match via `eq_cat(s_orig, s)`).
The equation-rewrite closure rule `rw_cat(a,c) <-- eq_cat(a,b), rw_cat(b,c)`
propagates the seeded rewrite to equation-equivalent sources.

Both LHS and RHS are normalized before seeding to eagerly collapse any
cancellation pairs.

**Impact.**
- Eliminates per-iteration scanning for ground rewrites (result available at iteration 0)
- Expected benefit: marginal for most grammars, significant for grammars
  with many ground axioms (e.g., Peano arithmetic tables)

**Complexity.** Low --- pattern inspection at codegen time; conditional
emission of a "seed" tuple.

**Files.**
- `macros/src/ast/pattern.rs` --- `is_ground_pattern()` on `Pattern` and `PatternTerm`
- `macros/src/logic/rules.rs` --- `generate_ground_rewrite_seeds()` detection and seed emission
- `macros/src/logic/mod.rs` --- `AscentSourceOutput.ground_rewrite_seeds` field, G35 lint
- `macros/src/gen/runtime/language.rs` --- seed injection in `run_ascent_typed()` initialization
- `macros/src/lib.rs` --- threading seeds through `generate_language_impl()`

**Tests.** 6 unit tests in `macros/src/ast/tests.rs`:
- `is_ground_pattern_variable_is_not_ground`
- `is_ground_pattern_nullary_constructor_is_ground`
- `is_ground_pattern_nested_constructors_are_ground`
- `is_ground_pattern_mixed_ground_and_var`
- `generate_ground_rewrite_seeds_detects_ground_rules`
- `generate_ground_rewrite_seeds_skips_premise_rules`

**Proof Requirements.** None (the ground-term short-circuit inserts exactly
the tuple that the full rule would produce; correctness follows from the
fact that ground matching succeeds unconditionally).

---

### B-CG05: Normalize-on-Insert Deduplication

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::NormalizeDedup` |
| Gate field | `OptimizationGates::normalize_dedup` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 3` |
| Speedup weight | 0.45 |
| Compile cost | 0.10 |

**Problem.** The Ascent fixpoint inserts tuples into relations and
deduplicates on exact structural equality.  When equations create large
equivalence classes, many semantically equivalent but structurally
distinct terms accumulate.

**Solution.** Generate a normalization function for each relation.  Before
insertion, apply the normalizer (e.g., canonical form selection via the
alpha-equivalence canonical structure from Sprint 6).  This reduces
equivalence class explosion.

**Impact.**
- Reduces relation sizes and fixpoint iteration count
- Expected speedup: highly variable (2x for heavily equational grammars,
  negligible for non-equational)

**Complexity.** High --- normalization must be confluent and terminating
to preserve correctness.

**Files.**
- `macros/src/logic/common.rs` --- normalizer generation
- `macros/src/logic/pattern_codec.rs` --- canonical form encoding

**Proof Requirements.**
- `NormalizeOnInsert.v`: the normalized fixpoint is isomorphic to the
  unnormalized fixpoint modulo the equivalence relation.

---

### B-CG06: Stratified Equation Evaluation

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::EqStrata` |
| Gate field | `OptimizationGates::eq_strata` |
| Tier | 3 (High complexity) |
| Applicability | `category_count >= 2` |
| Speedup weight | 0.30 |
| Compile cost | 0.40 |

**Problem.** All equations are evaluated in a single Ascent fixpoint.
Equations that do not interact (no shared variables or constructors)
unnecessarily participate in each other's fixpoint iterations.

**Solution.** Partition equations into strata (connected components of
the equation dependency graph).  Generate a separate fixpoint for each
stratum.  The SCC analysis from Opt 5 is extended to operate at the
equation level rather than the category level.

**Impact.**
- Reduces fixpoint iteration count per stratum
- Enables parallelism across independent strata
- Expected speedup: 20-40% for multi-stratum grammars

**Complexity.** High --- requires equation-level dependency analysis and
multi-struct generation (extending the SCC splitting pattern).

**Files.**
- `macros/src/logic/common.rs` --- equation dependency graph
- `macros/src/gen/runtime/language.rs` --- multi-struct dispatch
- `prattail/src/pipeline.rs` --- equation stratum computation

**Proof Requirements.**
- `EquationStrata.v`: independent equation strata produce the same fixpoint
  whether evaluated jointly or separately.  (Extends `SCCSplitting.v` with
  equation-level SCC analysis.)

---

## 4. Ascent Antipatterns (C-AP01 to C-AP05)

These are **compile-time detection patterns** --- they do not transform code
but emit diagnostics (lints A01-A10) that warn grammar authors about
patterns likely to cause performance problems at runtime.

### C-AP01: Unbounded Depth Growth

| Lint | A01 |
|------|-----|
| Name | `fixpoint-non-convergence` |
| Severity | Warning |
| Detection | Rule has 2+ self-referential NTs with <= 1 terminal |

**Pattern.** A rule `f(x, y)` where both `x` and `y` are of the same
category as `f`, and there is no depth-reducing counterpart.  This can
cause unbounded term growth in the fixpoint (e.g., `f(a) => f(f(a))`).

**Mitigation.** Ensure complementary depth-reducing rules exist, or enable
the depth bound optimization (A-RT05).

---

### C-AP02: Redundant Congruence

| Lint | A02 |
|------|-----|
| Name | `redundant-congruence` |
| Severity | Note |
| Detection | Category has <= 1 rule, is referenced as field, is not primary |

**Pattern.** A non-primary category referenced only as a field of other
constructors, with no or minimal rules of its own.  Congruence rules for
this category are likely redundant.

**Mitigation.** Review whether equations/rewrites actually need congruence
propagation through this category.

---

### C-AP03: Equivalence Class Explosion

| Lint | A04 |
|------|-----|
| Name | `large-equivalence-class` |
| Severity | Warning |
| Detection | Constructor appears in 3+ dependency groups |

**Pattern.** A constructor participates in multiple equational axiom groups
(e.g., commutativity AND associativity AND identity).  The interaction
of these axioms can produce exponentially many equivalent terms.

**Mitigation.** Use `HashBag` for collection fields to avoid order-sensitive
equivalence, or reduce the number of equational axioms.

---

### C-AP04: Ascent Struct Size

| Lint | A09 |
|------|-----|
| Name | `ascent-struct-size` |
| Severity | Warning (> 100 rules) / Note (> 50 relations) |
| Detection | Estimated relation and rule counts exceed thresholds |

**Pattern.** A grammar with many categories and constructors generates a
large Ascent struct.  Rust's monomorphization of the struct is slow, and
the fixpoint iteration scans many relations per round.

**Mitigation.** Enable SCC splitting (Opt 5), demand-driven population
(A-RT06), or split the grammar into independent modules.

---

### C-AP05: Fixpoint Iteration Anomaly

| Lint | A07 |
|------|-----|
| Name | `fixpoint-iteration-anomaly` |
| Severity | Warning |
| Detection | > 10 dependency groups with max group size > 5 |

**Pattern.** The equational reasoning substrate has many interacting groups,
suggesting the fixpoint will require many iterations to converge.

**Mitigation.** Partition equations into independent strata (B-CG06) or add
a depth bound (A-RT05).

---

## 5. Lexer Codegen Optimizations (A-L01 to A-L06)

These optimizations target the **generated DFA-based lexer**, reducing
table sizes, improving cache behavior, and exploiting SIMD.

### A-L01: DFA Transition Table Multi-Row Repacking (Comb Repacking)

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::CombRepacking` |
| Gate field | `OptimizationGates::comb_repacking` |
| Tier | 3 (but always applicable) |
| Applicability | always |
| Speedup weight | 0.40 |
| Compile cost | 0.10 |

**Problem.** The DFA transition table is stored as a 2D array
`[state][character]`.  Many rows are sparse (most characters map to a dead
state), wasting cache lines.

**Solution.** Apply comb-vector compression (the classic Tarjan-Yao
technique).  Overlay sparse rows into a single dense vector using
displacement indexing: `next_state = table[disp[state] + char]` with a
validity check.

**Impact.**
- Table size: typically 60-80% reduction
- Expected speedup: 5-15% from improved L1/L2 cache utilization

**Complexity.** Medium codegen, but the algorithm is well-understood.

**Files.**
- `prattail/src/lexer.rs` --- DFA table emission
- `prattail/src/automata/` --- DFA construction

**Proof Requirements.**
- `CombRepacking.v`: the compressed table produces the same transition
  function as the uncompressed table for all (state, char) pairs within the
  valid character set.

---

### A-L02: Hybrid Direct-Coded + Compressed Lexer

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::HybridLexer` |
| Gate field | `OptimizationGates::hybrid_lexer` |
| Tier | 2 (Moderate complexity) |
| Applicability | `total_wfst_states > 30` |
| Speedup weight | 0.30 |
| Compile cost | 0.20 |

**Problem.** Table-driven lexers incur an indirect memory access per
character.  For hot states (those visited on most inputs), this overhead
dominates.

**Solution.** Generate direct-coded `match` arms for hot states (those with
tropical weight below a threshold) and fall back to the compressed table
for cold states.  Hot states are identified from `PredictionWfst` action
weights.

**Impact.**
- Hot-path lexing: 1 branch per character instead of 1 table lookup
- Expected speedup: 10-20% on typical inputs

**Complexity.** Moderate --- requires splitting the lexer into two code
paths and maintaining state numbering consistency.

**Files.**
- `prattail/src/lexer.rs` --- dual-path emission
- `prattail/src/wfst.rs` --- hot state identification

**Proof Requirements.** None (the direct-coded path and the table-driven
path produce identical state transitions by construction; the partition
of hot/cold states is a code layout decision, not a semantic one).

---

### A-L03: SIMD-Accelerated Whitespace Skipping

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::SimdWhitespace` |
| Gate field | `OptimizationGates::simd_whitespace` |
| Tier | 3 (High complexity) |
| Applicability | always (feature-gated at codegen) |
| Speedup weight | 0.20 |
| Compile cost | 0.30 |

**Problem.** The lexer's `skip_whitespace()` loop processes one byte at a
time.  For inputs with long whitespace runs (common in formatted source
code), this is a bottleneck.

**Solution.** Use `core::arch` SIMD intrinsics (SSE2/AVX2 on x86_64,
NEON on AArch64) to scan 16-32 bytes at a time for non-whitespace
characters.  Fall back to scalar for the tail.

**Impact.**
- Whitespace skipping: 8-16x throughput for long runs
- Expected end-to-end speedup: 5-10% (whitespace-dominated inputs)

**Complexity.** High --- requires platform-specific code and runtime
feature detection.

**Files.**
- `prattail/src/lexer.rs` --- whitespace skipping
- `runtime/src/` --- SIMD runtime support (new)

**Proof Requirements.** None (byte comparison is trivially correct;
the SIMD implementation must be validated by exhaustive test over the
ASCII whitespace set `{0x09, 0x0A, 0x0D, 0x20}`).

---

### A-L04: Keyword Recognition via Minimal Perfect Hashing

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::KeywordMph` |
| Gate field | `OptimizationGates::keyword_mph` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 15` |
| Speedup weight | 0.20 |
| Compile cost | 0.30 |

**Problem.** Keyword recognition is currently embedded in the DFA.  Each
additional keyword adds states to the DFA, increasing table size.  For
languages with many keywords, the DFA becomes large.

**Solution.** Extract keywords from the DFA into a minimal perfect hash
(MPH) table.  After the DFA emits an `Ident` token, probe the MPH table.
If the identifier matches a keyword, reclassify the token.  This keeps the
DFA small (identifiers are a single accepting state) and the MPH lookup is
O(1) with no collisions.

**Impact.**
- DFA state count: proportional to non-keyword terminals only
- Keyword lookup: O(1) with guaranteed no collisions
- Expected table size reduction: 40-70% for keyword-heavy grammars

**Complexity.** High --- requires MPH construction at compile time
(CHD or similar algorithm).

**Files.**
- `prattail/src/lexer.rs` --- keyword extraction and MPH emission
- `prattail/src/automata/` --- DFA keyword state removal

**Proof Requirements.**
- `MphCorrectness.v`: the MPH function is injective over the keyword set;
  every keyword is correctly reclassified; non-keywords are never
  reclassified.

---

### A-L05: Multi-Byte Chain Transitions

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::MultiByteChain` |
| Gate field | `OptimizationGates::multi_byte_chain` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 10` |
| Speedup weight | 0.25 |
| Compile cost | 0.35 |

**Problem.** Many DFA state chains are linear sequences (e.g., matching the
keyword `while` transitions through states `w -> wh -> whi -> whil -> while`).
Each character requires a separate table lookup.

**Solution.** Detect linear chains in the DFA and collapse them into
multi-byte comparisons.  For a chain of length N, emit a single
`input[pos..pos+N] == b"while"` comparison instead of N table lookups.

**Impact.**
- Chain matching: N table lookups --> 1 comparison (often a single SIMD op)
- Expected speedup: 10-20% for keyword-heavy grammars

**Complexity.** High --- requires DFA chain detection and safe boundary
conditions (input length checks).

**Files.**
- `prattail/src/lexer.rs` --- chain detection and emission
- `prattail/src/automata/` --- DFA chain analysis

**Proof Requirements.**
- `ChainCollapse.v`: the collapsed comparison accepts exactly the same
  strings as the original chain of transitions.

---

### A-L06: Accept State Bitmap Widening

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::AcceptBitmapWiden` |
| Gate field | `OptimizationGates::accept_bitmap_widen` |
| Tier | 1 (Low complexity) |
| Applicability | always |
| Speedup weight | 0.15 |
| Compile cost | 0.02 |

**Problem.** Accept state checking uses a `match` statement or `HashSet`
lookup.  For DFAs with many accept states, the branch predictor suffers.

**Solution.** Replace the accept-state check with a bitmap lookup.  Each
DFA state maps to a bit in a `u64` (or `u128` / `[u64; N]` for large DFAs).
The check becomes `(bitmap >> state) & 1 != 0`.

**Impact.**
- Accept check: branch-free, constant time
- Expected speedup: 2-5% (removes a branch from the hot loop)

**Complexity.** Low --- bitmap construction is trivial.

**Files.**
- `prattail/src/lexer.rs` --- accept state emission

**Proof Requirements.** None (bitmap lookup is trivially equivalent to set
membership).

---

## 6. Parser Codegen Optimizations (B-P01 to B-P05)

These optimizations target the **generated Pratt + recursive descent parser**,
reducing branch overhead, enabling tail calls, and compacting lookup tables.

### B-P01: Pratt BP Table Compaction via Range Encoding

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::BpCompaction` |
| Gate field | `OptimizationGates::bp_compaction` |
| Tier | 1 (Low complexity) |
| Applicability | `category_count >= 1` |
| Speedup weight | 0.25 |
| Compile cost | 0.05 |

**Problem.** The Pratt parser's binding power (BP) table maps
`(category, token)` pairs to `(left_bp, right_bp)` values.  The generated
`match` statement has one arm per operator, which can be large.

**Solution.** Group operators with consecutive BP values into ranges.
Emit `bp if (MIN..=MAX).contains(&bp)` guards instead of individual arms.
For categories with dense BP usage, this reduces match arm count
significantly.

**Impact.**
- Match arm count: proportional to distinct BP ranges, not individual operators
- Expected code size reduction: 20-40%

**Complexity.** Low --- range detection at codegen time.

**Files.**
- `prattail/src/pratt.rs` --- BP table emission
- `prattail/src/binding_power.rs` --- BP range analysis

**Proof Requirements.** None (range containment is equivalent to individual
equality checks).

---

### B-P02: Tail-Call Elimination in Recursive Descent

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::TailCallElim` |
| Gate field | `OptimizationGates::tail_call_elim` |
| Tier | 3 (High complexity) |
| Applicability | `category_count >= 2` |
| Speedup weight | 0.40 |
| Compile cost | 0.20 |

**Problem.** The trampoline parser already converts deep recursion into an
explicit stack.  However, rules that end with a non-terminal call (tail
position) still push a continuation frame and then immediately pop it.

**Solution.** Detect tail-position non-terminal calls at codegen time.
Instead of pushing a continuation, overwrite the current category and
restart the parse loop (the trampoline equivalent of TCO).

**Impact.**
- Eliminates frame push/pop for tail calls
- Expected speedup: 5-15% for deeply nested grammars

**Complexity.** High --- requires identifying tail position in all RD rule
variants and ensuring the trampoline state machine correctly handles the
restart.

**Files.**
- `prattail/src/trampoline.rs` --- frame generation
- `prattail/src/recursive.rs` --- tail position detection

**Proof Requirements.**
- `TailCallElim.v`: the tail-call-eliminated trampoline produces the same
  parse tree as the standard trampoline for all inputs.

---

### B-P03: Token Peek Cache / BP Table Lookup

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::BpTableLookup` |
| Gate field | `OptimizationGates::bp_table_lookup` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 8` |
| Speedup weight | 0.30 |
| Compile cost | 0.15 |

**Problem.** The Pratt infix loop calls `peek()` to inspect the next token
and then matches it against the BP table.  For categories with many infix
operators, this match is expensive.

**Solution.** Pre-compute a lookup array indexed by token discriminant.
The `peek()` result is used as an index into the array, yielding
`(left_bp, right_bp)` in O(1).  This replaces the generated `match` with
a single array access.

**Impact.**
- Infix dispatch: O(operators) --> O(1)
- Expected speedup: 10-20% for operator-heavy categories

**Complexity.** Moderate --- requires stable token discriminant ordering.

**Files.**
- `prattail/src/pratt.rs` --- infix loop codegen
- `prattail/src/token_id.rs` --- discriminant mapping

**Proof Requirements.** None (array lookup is equivalent to the match when
the array is correctly populated).

---

### B-P04: Prefix Handler Inlining for Trivial Rules

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::TrivialInline` |
| Gate field | `OptimizationGates::trivial_inline` |
| Tier | 1 (Low complexity) |
| Applicability | always |
| Speedup weight | 0.30 |
| Compile cost | 0.05 |

**Problem.** Each prefix rule generates a separate handler function.  For
trivial rules (single terminal producing a literal, e.g., `NumLit: Integer`)
the function call overhead exceeds the handler body cost.

**Solution.** At codegen time, identify trivial prefix handlers (handlers
whose body is a single `Token::Variant(_) => NonTerminal::Constructor(value)`
with no further non-terminal calls).  Inline these directly into the dispatch
match arm, eliminating the function call.

**Impact.**
- Eliminates function call overhead for trivial rules
- Expected speedup: 5-10% for grammars with many literal rules

**Complexity.** Low --- trivial rule detection is straightforward.

**Files.**
- `prattail/src/recursive.rs` --- prefix handler emission
- `prattail/src/dispatch.rs` --- dispatch match generation

**Proof Requirements.** None (inlining preserves semantics by definition).

---

### B-P05: Specialized Pratt Loop for Fixed BP Ranges

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::BpRangeLoop` |
| Gate field | `OptimizationGates::bp_range_loop` |
| Tier | 3 (High complexity) |
| Applicability | `rule_count > 5` |
| Speedup weight | 0.45 |
| Compile cost | 0.15 |

**Problem.** The general Pratt loop handles arbitrary BP ranges.  For
categories where all operators have the same precedence level (e.g., a
simple list separator), the general loop's BP comparison is wasted work.

**Solution.** At codegen time, analyze the BP table per category.  If all
infix operators in a category share the same BP, generate a simplified loop
that unconditionally consumes the infix operator (no BP comparison).

**Impact.**
- Eliminates BP comparison for fixed-precedence categories
- Expected speedup: 5-10% for flat-precedence categories

**Complexity.** High (in the general case of range partitioning); low for
the degenerate single-BP case.

**Files.**
- `prattail/src/pratt.rs` --- Pratt loop emission
- `prattail/src/binding_power.rs` --- BP uniformity detection

**Proof Requirements.**
- `BpRangeLoop.v`: the specialized loop produces the same parse tree as the
  general loop when all operators share a single BP level.

---

## 7. Dispatch Optimizations (C-D01 to C-D05)

These optimizations target the **decision tree and cross-category dispatch**
layer, improving branch prediction, reducing redundant parsing, and enabling
computed dispatch.

### C-D01: Hot-Path Arm Reordering via WFST Frequency Weights (IMPLEMENTED)

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::FrequencyOrdering` |
| Gate field | `OptimizationGates::frequency_ordering` |
| Tier | 2 (Moderate complexity) |
| Applicability | always |
| Speedup weight | 0.35 |
| Compile cost | 0.10 |
| Status | **IMPLEMENTED** |

**Problem.** Match arms in the dispatch function were emitted in
declaration / lexicographic order (BTreeMap iteration).  The CPU's branch
predictor benefits when the most likely arm appears first.

**Solution.** Three dispatch sites now sort arms by weight (ascending =
hot first):

1. **Cross-category dispatch** (`dispatch.rs` `write_category_dispatch()`):
   Already weight-sorted since initial implementation.  Arms carry
   `(code, f64)` and are sorted before emission.
2. **Trampoline RD prefix dispatch** (`trampoline.rs`
   `write_prefix_match_arms()`): The `BTreeMap<variant, rules>` is
   converted to a `Vec` and sorted by the best `PredictionWfst::predict()`
   weight for each token variant.  Falls back to `complete_weight_map`
   when no WFST is available, and to BTreeMap lexicographic order when
   neither weight source exists.  Gated by
   `optimization_gates.frequency_ordering`.
3. **NFA try-all alternatives** (`trampoline.rs`): Already weight-sorted
   via `nfa_alternative_order()` since NFA disambiguation implementation.
4. **Ident-lookahead handlers** (`trampoline.rs`): Already weight-sorted
   via `handler_weight()` comparator.

**DIS01 lint** updated: now notes that codegen CD01 compensates for
unsorted WFST action tables.

**Impact.**
- Improved branch prediction hit rate for RD prefix dispatch
- Expected speedup: 5-15% (input-distribution dependent)
- No semantic change --- only ordering of non-overlapping match arms

**Complexity.** Low --- collect BTreeMap entries into Vec, sort by weight.

**Files.**
- `prattail/src/dispatch.rs` --- cross-category arm weight sorting (pre-existing)
- `prattail/src/trampoline.rs` --- RD prefix arm weight sorting (new)
- `prattail/src/lint.rs` --- DIS01 hint update
- `prattail/src/wfst.rs` --- weight extraction via `predict()`

**Proof Requirements.** None (arm reordering does not change match
semantics).

---

### C-D02: Decision Tree Segment Merging

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::SegmentMerging` |
| Gate field | `OptimizationGates::segment_merging` |
| Tier | 3 (High complexity) |
| Applicability | `avg_trie_depth > 3.0` |
| Speedup weight | 0.30 |
| Compile cost | 0.35 |

**Problem.** The PathMap decision tree can produce long linear chains of
single-child nodes.  Each node requires a branch in the generated code.

**Solution.** Merge adjacent single-child nodes at safe nonterminal
boundaries (boundaries where the parsed prefix can be committed).
The merged segment becomes a multi-token comparison.

**Impact.**
- Reduces branch count in decision tree traversal
- Expected speedup: 10-20% for grammars with deep shared prefixes

**Complexity.** High --- requires identifying safe merge points (no
ambiguity in the merged segment).

**Files.**
- `prattail/src/decision_tree.rs` --- segment merging
- `prattail/src/dispatch.rs` --- merged segment codegen

**Proof Requirements.**
- `SegmentMerging.v`: the merged decision tree accepts exactly the same
  token sequences as the unmerged tree at safe boundaries.

---

### C-D03: Computed Goto Dispatch via Function Pointer Tables

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::ComputedGoto` |
| Gate field | `OptimizationGates::computed_goto` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 20` |
| Speedup weight | 0.25 |
| Compile cost | 0.15 |

**Problem.** The category dispatch function uses a `match` statement over
token discriminants.  For large grammars, LLVM may not lower this to a
jump table, producing a chain of `if-else` comparisons.

**Solution.** Generate an explicit function pointer table indexed by token
discriminant.  The dispatch becomes `table[discriminant](&mut self)`.
Rust's optimizer reliably lowers this to an indirect jump.

**Impact.**
- Dispatch: O(1) indirect jump instead of O(operators) comparisons
- Expected speedup: 5-15% for grammars with > 20 dispatch arms

**Complexity.** Moderate --- requires stable discriminant ordering and safe
function pointer types.

**Files.**
- `prattail/src/dispatch.rs` --- function pointer table emission
- `prattail/src/token_id.rs` --- discriminant mapping

**Proof Requirements.** None (function pointer dispatch is semantically
equivalent to match dispatch when the table is correctly populated).

---

### C-D04: Jump Threading Through Decision Tree Branches

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::JumpThreading` |
| Gate field | `OptimizationGates::jump_threading` |
| Tier | 3 (High complexity) |
| Applicability | `avg_trie_depth > 2.0` |
| Speedup weight | 0.35 |
| Compile cost | 0.25 |

**Problem.** After a decision tree node dispatches to a subtree, the
subtree may immediately re-test a condition that was already established
by the parent (e.g., the parent dispatched on `Token::LParen` and the
child tests for the same token).

**Solution.** At codegen time, propagate known-true conditions through the
decision tree.  When a child node's guard is implied by the parent's
dispatch, eliminate the redundant check.  This is the classic jump
threading optimization from SSA-based compilers, applied at the AST
codegen level.

**Impact.**
- Eliminates redundant condition checks in decision tree traversal
- Expected speedup: 5-10%

**Complexity.** High --- requires tracking known conditions through the
codegen tree.

**Files.**
- `prattail/src/decision_tree.rs` --- condition propagation
- `prattail/src/dispatch.rs` --- guard elimination

**Proof Requirements.**
- `JumpThreading.v`: the threaded decision tree accepts exactly the same
  inputs as the original, with the same dispatch outcomes.

---

### C-D05: Prefix CSE for Shared Nonterminal Parses

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::PrefixCse` |
| Gate field | `OptimizationGates::prefix_cse` |
| Tier | 3 (High complexity) |
| Applicability | `shared_prefix_ratio > 0.2` |
| Speedup weight | 0.15 |
| Compile cost | 0.45 |

**Problem.** When multiple rules in a category share a prefix (e.g.,
`A "+" B` and `A "++" B`), the NFA try-all path parses the shared
non-terminal `A` multiple times.

**Solution.** Identify shared nonterminal prefixes at codegen time using
the decision tree.  Parse the shared prefix once, save the result, and
distribute it to all rules that share it.  This is common sub-expression
elimination (CSE) at the parser codegen level.

**Impact.**
- Eliminates redundant prefix parsing in ambiguous dispatch
- Expected speedup: 10-30% for grammars with heavy prefix sharing

**Complexity.** High --- requires identifying safe CSE points (the shared
parse must be valid for all consumer rules) and managing saved results.

**Files.**
- `prattail/src/decision_tree.rs` --- shared prefix identification
- `prattail/src/dispatch.rs` --- CSE codegen

**Proof Requirements.**
- `PrefixCse.v`: the CSE'd parser produces the same parse tree as the
  non-CSE'd parser for all inputs in the grammar's language.

---

## 8. Pipeline/Build Optimizations (D-B01 to D-B04)

These optimizations target the **compilation pipeline itself** --- reducing
the time spent in `language!` macro expansion and analysis phases.

### D-B01: Incremental FIRST/FOLLOW Recomputation

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::IncrementalFirstFollow` |
| Gate field | `OptimizationGates::incremental_first_follow` |
| Tier | 2 (Moderate complexity) |
| Applicability | `category_count >= 3` |
| Speedup weight | 0.40 |
| Compile cost | 0.20 |

**Problem.** FIRST and FOLLOW set computation uses dirty-flag convergence
(from the pipeline allocation optimization).  On grammar changes, the
entire computation reruns from scratch.

**Solution.** Cache FIRST/FOLLOW sets between compilations.  On
recompilation, compare the grammar's structural hash with the cached
version.  If only a subset of categories changed, recompute only the
affected categories and their transitive dependents.

**Impact.**
- Incremental builds: FIRST/FOLLOW recomputation proportional to changed
  categories, not total categories
- Expected build speedup: 30-50% for incremental edits to large grammars

**Complexity.** Moderate --- requires stable hashing and invalidation
tracking.

**Files.**
- `prattail/src/prediction.rs` --- FIRST/FOLLOW computation
- `prattail/src/pipeline.rs` --- caching infrastructure

**Proof Requirements.** None (caching is transparent; the recomputed sets
are identical to fresh computation by construction).

---

### D-B02: Lazy Analysis Phase Execution

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::LazyAnalysis` |
| Gate field | `OptimizationGates::lazy_analysis` |
| Tier | 1 (Low complexity) |
| Applicability | `category_count < 3` |
| Speedup weight | 0.50 |
| Compile cost | 0.02 |

**Problem.** Small grammars (1-2 categories) pass through all analysis
phases (WFST construction, decision tree, WPDS, mathematical analyses)
even when most produce trivially empty results.

**Solution.** Gate analysis phases on grammar size.  For small grammars,
skip WPDS analysis, mathematical analyses, and cross-category lints.

**Impact.**
- Build time for small grammars: 30-50% reduction
- No impact on correctness (skipped phases produce no actionable results
  for small grammars)

**Complexity.** Low --- add size checks at phase entry points.

**Files.**
- `prattail/src/pipeline.rs` --- phase gating

**Proof Requirements.** None (skipping phases that produce empty results is
trivially correct).

---

### D-B03: Parallel Analysis Phase Execution

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::ParallelAnalysis` |
| Gate field | `OptimizationGates::parallel_analysis` |
| Tier | 3 (High complexity) |
| Applicability | `category_count >= 3` |
| Speedup weight | 0.30 |
| Compile cost | 0.30 |

**Problem.** Analysis phases (WFST, decision tree, WPDS, mathematical
analyses) run sequentially.  Many are independent and could execute in
parallel.

**Solution.** Identify independent analysis phases using a dependency DAG.
Execute independent phases in parallel using `rayon` or `std::thread::scope`.
The dependency structure is:

```
  NFA ─────────► DFA ───────► WFST construction
                                 │
                   ┌─────────────┼──────────────────┐
                   │             │                   │
                   ▼             ▼                   ▼
              Decision       Lint layer         WPDS analysis
              Tree           (depends on DT)    (depends on WFST)
                               │                    │
                               └──────┬─────────────┘
                                      │
                                      ▼
                              Mathematical analyses
                              (depends on WPDS + lints)
```

**Impact.**
- Wall-clock build time: proportional to the critical path, not the sum
  of all phases
- Expected speedup: 2-3x for large grammars with many independent phases

**Complexity.** High --- requires careful handling of shared mutable state
and lifetime management in a proc-macro context.

**Files.**
- `prattail/src/pipeline.rs` --- phase orchestration

**Proof Requirements.** None (parallelism is a scheduling decision; each
phase produces the same output regardless of execution order).

---

### D-B04: Cached Lint Results Across Builds

| Field | Value |
|-------|-------|
| Enum variant | `Optimization::CachedLints` |
| Gate field | `OptimizationGates::cached_lints` |
| Tier | 2 (Moderate complexity) |
| Applicability | `rule_count > 10` |
| Speedup weight | 0.45 |
| Compile cost | 0.20 |

**Problem.** Lint analysis runs on every compilation, even when the grammar
has not changed.

**Solution.** Hash the grammar's `LanguageSpec` and compare with a cached
hash.  If unchanged, skip lint analysis and replay cached diagnostics.
The cache is stored in the target build directory.

**Impact.**
- Incremental builds: lint analysis time drops to near zero
- Expected speedup: 10-20% of total build time for large grammars

**Complexity.** Moderate --- requires deterministic hashing and cache
invalidation.

**Files.**
- `prattail/src/lint.rs` --- cache-aware `run_lints()`
- `prattail/src/pipeline.rs` --- cache I/O

**Proof Requirements.** None (caching is transparent; same grammar produces
same diagnostics).

---

## 9. New Lints

### 9.1 Ascent VM / Codegen Lints (A01-A10)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| A01 | `fixpoint-non-convergence` | Warning | Rule has 2+ self-referential NTs with <= 1 terminal --- potential unbounded term growth |
| A02 | `redundant-congruence` | Note | Non-primary category has <= 1 rule but is referenced as field --- congruence may be redundant |
| A03 | `eq-rw-category-mismatch` | Note | Category has parsing rules but no equations/rewrites reference its constructors |
| A04 | `large-equivalence-class` | Warning | Constructor appears in 3+ dependency groups --- potential exponential blowup |
| A05 | `self-referential-equation` | Warning | Rule is a trivial identity (single self-referential NT) --- redundant if used as equation |
| A06 | `missing-equation-congruence` | Note | Constructor in equation has NT fields whose category has no equation participants |
| A07 | `fixpoint-iteration-anomaly` | Warning | > 10 dependency groups with max size > 5 --- slow convergence expected |
| A08 | `equation-subsumes-rewrite` | Note | Constructor appears in 2+ dependency groups --- equation may subsume rewrite |
| A09 | `ascent-struct-size` | Warning/Note | Estimated Ascent struct has > 100 rules or > 50 relations |
| A10 | `unreachable-equation-variable` | Note | Variable captured but may not be referenced in RHS --- possible typo |

### 9.2 Lexer Lints (LEX01-LEX05)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| LEX01 | `overlapping-token-defs` | Warning | Two terminals match the same string in different semantic contexts |
| LEX02 | `unreachable-token-pattern` | Note | Terminal is a proper prefix of another --- longest-match semantics apply |
| LEX03 | `excessive-equiv-classes` | Note | > 25 distinct characters across terminals --- large DFA character set |
| LEX04 | `dfa-state-explosion` | Note | > 50 terminal tokens --- monitor DFA state count |
| LEX05 | `float-integer-ambiguity` | Note | Both integer and float native types present --- `123` always lexes as Integer |

### 9.3 Parser Lints (PAR01-PAR05)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| PAR01 | `deep-rd-chain` | Warning | Cross-category RD call chain depth > 5 --- stresses trampoline stack |
| PAR02 | `unused-bp-level` | Note | BP range has > 3 unused levels with total span > 6 --- wider than necessary |
| PAR03 | `postfix-prefix-collision` | Warning | Same token is both prefix and postfix in same category --- surprising precedence |
| PAR04 | `mixfix-ambiguous-delimiter` | Warning | Mixfix middle delimiter is also used as infix operator --- parsing ambiguity |
| PAR05 | `trampoline-frame-variant-count` | Note | Category has > 15 trampoline frame variants --- large frame enum |

### 9.4 Dispatch Lints (DIS01-DIS05)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| DIS01 | `hot-path-misalignment` | Note | First dispatch arm weight != minimum weight --- suboptimal branch prediction |
| DIS02 | `cold-arm-ratio` | Note | > 80% of dispatch arms are cold (weight >= 1.0) --- hot/cold splitting recommended |
| DIS03 | `decision-tree-depth` | Warning | Decision tree max depth > 8 --- long shared prefixes degrade dispatch |
| DIS04 | `backtrack-elimination-coverage` | Note | Reports committed vs save/restore arms after backtracking elimination (G1) |
| DIS05 | `nfa-try-all-set-size` | Warning | > 5 ambiguous dispatch points --- poor prefix disambiguation |

---

## 10. Priority Tiers

Optimizations are ranked into three priority tiers based on
implementation complexity, expected impact, and prerequisite dependencies.

### Tier 1: Low Complexity, High Yield

These should be implemented first --- minimal effort, immediate benefit.

| ID | Name | Speedup | Cost | Rationale |
|----|------|---------|------|-----------|
| A-RT03 | Relation Indexing | 0.30 | 0.05 | Additive `#[index]` annotations; no semantic change |
| B-CG04 | Ground Short-Circuit | 0.40 | 0.05 | Simple pattern detection; direct seed emission |
| B-P04 | Trivial Inline | 0.30 | 0.05 | Straightforward inlining decision |
| B-P01 | BP Compaction | 0.25 | 0.05 | Range grouping is a purely syntactic transform |
| A-L06 | Accept Bitmap | 0.15 | 0.02 | Trivial bitmap construction |
| D-B02 | Lazy Analysis | 0.50 | 0.02 | Size guards at phase entry points |

### Tier 2: Moderate Complexity, Solid Yield

These build on Tier 1 and existing infrastructure.

| ID | Name | Speedup | Cost | Rationale |
|----|------|---------|------|-----------|
| A-RT04 | Congruence Bloom | 0.35 | 0.15 | Reuses TLS pool pattern; existing `bloom_filter.rs` |
| A-RT05 | Depth Bound | 0.40 | 0.10 | Reuses pipeline graph analysis |
| A-RT06 | Demand-Driven | 0.50 | 0.10 | Extends SCC splitting (Opt 5) |
| B-CG01 | Join Ordering | 0.40 | 0.15 | Uses existing `constructor_weights` from WFST |
| B-CG03 | EqCongruence Prune | 0.35 | 0.15 | Extends dead-rule pruning (Opt 3) |
| A-L02 | Hybrid Lexer | 0.30 | 0.20 | Hot/cold state splitting reuses WFST weights |
| B-P03 | BP Table Lookup | 0.30 | 0.15 | Reuses `token_id.rs` discriminant map |
| C-D01 | Frequency Ordering | 0.35 | 0.10 | Trivial sort by WFST weight |
| C-D03 | Computed Goto | 0.25 | 0.15 | Function pointer table indexed by discriminant |
| D-B01 | Incremental FIRST | 0.40 | 0.20 | Builds on dirty-flag infrastructure |
| D-B04 | Cached Lints | 0.45 | 0.20 | Requires deterministic grammar hashing |

### Tier 3: High Complexity, Transformative

These require significant implementation effort but unlock major performance
improvements.

| ID | Name | Speedup | Cost | Rationale |
|----|------|---------|------|-----------|
| A-RT01 | Hash-Consing | 0.15 | 0.50 | Changes fundamental term representation |
| A-RT02 | Incremental Delta | 0.30 | 0.35 | Requires rewriting rule generation |
| B-CG02 | Rule Fusion | 0.40 | 0.40 | Cross-rule dependency analysis |
| B-CG05 | Normalize Dedup | 0.45 | 0.10 | Requires confluent normalizer |
| B-CG06 | Equation Strata | 0.30 | 0.40 | Multi-struct fixpoint splitting |
| A-L01 | Comb Repacking | 0.40 | 0.10 | Classic compression algorithm |
| A-L03 | SIMD Whitespace | 0.20 | 0.30 | Platform-specific intrinsics |
| A-L04 | Keyword MPH | 0.20 | 0.30 | MPH construction algorithm |
| A-L05 | Multi-Byte Chain | 0.25 | 0.35 | DFA chain detection |
| B-P02 | Tail-Call Elim | 0.40 | 0.20 | Trampoline state machine modification |
| B-P05 | BP Range Loop | 0.45 | 0.15 | Specialized loop variants |
| C-D02 | Segment Merging | 0.30 | 0.35 | Safe merge point identification |
| C-D04 | Jump Threading | 0.35 | 0.25 | Condition propagation through codegen tree |
| C-D05 | Prefix CSE | 0.15 | 0.45 | Shared prefix identification and result management |
| D-B03 | Parallel Analysis | 0.30 | 0.30 | Phase dependency DAG and parallel scheduling |

---

## 11. Cost-Benefit Integration

All optimizations in this catalog are registered in the cost-benefit
framework at `prattail/src/cost_benefit.rs`.

### Optimization Enum Variants

```rust
// ── Codegen Optimization Catalog ─────────────────────────────────────────

// Ascent VM Runtime
HashConsing,        // ART01
IncrementalDelta,   // ART02
RelationIndexing,   // ART03
CongruenceBloom,    // ART04
DepthBound,         // ART05
DemandDriven,       // ART06

// Ascent Codegen
JoinOrdering,       // BCG01
RuleFusion,         // BCG02
EqCongruencePrune,  // BCG03
GroundShortCircuit, // BCG04
NormalizeDedup,     // BCG05
EqStrata,           // BCG06

// Lexer Codegen
CombRepacking,      // AL01
HybridLexer,        // AL02
SimdWhitespace,     // AL03
KeywordMph,         // AL04
MultiByteChain,     // AL05
AcceptBitmapWiden,  // AL06

// Parser Codegen
BpCompaction,       // BP01
TailCallElim,       // BP02
BpTableLookup,      // BP03
TrivialInline,      // BP04
BpRangeLoop,        // BP05

// Dispatch Codegen
FrequencyOrdering,  // CD01
SegmentMerging,     // CD02
ComputedGoto,       // CD03
JumpThreading,      // CD04
PrefixCse,          // CD05

// Pipeline/Build
IncrementalFirstFollow, // DB01
LazyAnalysis,           // DB02
ParallelAnalysis,       // DB03
CachedLints,            // DB04
```

### GrammarProfile Fields Used

| Field | Used By |
|-------|---------|
| `shared_prefix_ratio` | CD05 (> 0.2) |
| `cold_fraction` | C-D01 (always) |
| `ambiguous_fraction` | (existing opts) |
| `ambiguous_count` | (existing opts) |
| `category_count` | A-RT06 (>= 2), B-CG06 (>= 2), B-P01 (>= 1), B-P02 (>= 2), D-B01 (>= 3), D-B02 (< 3), D-B03 (>= 3) |
| `rule_count` | A-RT01 (> 10), A-RT02 (> 5), A-RT03 (> 3), A-RT04 (> 5), A-RT05 (> 2), B-CG01 (> 5), B-CG02 (> 5), B-CG03 (> 3), B-CG04 (> 2), B-CG05 (> 3), A-L04 (> 15), A-L05 (> 10), B-P03 (> 8), B-P05 (> 5), C-D03 (> 20), D-B04 (> 10) |
| `total_wfst_states` | A-L02 (> 30) |
| `avg_trie_depth` | C-D02 (> 3.0), C-D04 (> 2.0) |
| `deterministic_ratio` | (DIS04 lint) |

### OptimizationGates Fields

Each optimization has a corresponding boolean field in `OptimizationGates`
(see `prattail/src/cost_benefit.rs`, lines 1148-1218).  The pipeline
populates these from `recommended_optimizations()` and threads them through
to codegen.

### Scoring

All candidates use `ProductWeight<TropicalWeight, TropicalWeight>` with
lexicographic ordering:

```
score = (speedup_weight, compile_cost_weight)
```

Lower is better.  Among equally beneficial optimizations, the cheaper one
is preferred.  The `evaluate_optimizations()` function returns all
candidates sorted by score; `recommended_optimizations()` filters to
applicable ones only.

---

## 12. Rocq Proof Requirements

The following formal proofs are needed for semantic-preserving
optimizations.  Proofs are NOT needed for purely additive transformations
(annotations, code layout, caching) or for transformations that are
trivially correct by construction.

| Proof File | Optimization | Key Theorem | Status |
|------------|-------------|-------------|--------|
| `HashConsEquivalence.v` | A-RT01 | Pointer equality implies structural equality; fixpoint unchanged | Pending |
| `DeltaGuardEquivalence.v` | A-RT02 | Decomposed rules produce same fixpoint under semi-naive | Pending |
| `BloomFilterSoundness.v` | A-RT04 | False positives preserve correctness; false negatives impossible | Pending |
| `DepthBoundTermination.v` | A-RT05 | Bounded fixpoint terminates; produces sufficient subset | Pending |
| `DemandDrivenEquivalence.v` | A-RT06 | Demand-driven fixpoint equals eager fixpoint on demanded relations | Pending |
| `JoinOrderEquivalence.v` | B-CG01 | Body clause reordering preserves rule semantics | Pending |
| `RuleFusionEquivalence.v` | B-CG02 | Fused rule produces same fixpoint as two-rule chain | Pending |
| `CongruencePruning.v` | B-CG03 | Pruned congruence rules derive nothing for non-equational categories | Pending |
| `NormalizeOnInsert.v` | B-CG05 | Normalized fixpoint isomorphic to unnormalized modulo equivalence | Pending |
| `EquationStrata.v` | B-CG06 | Independent strata produce same fixpoint separately or jointly | Pending |
| `CombRepacking.v` | A-L01 | Compressed table produces same transitions as uncompressed | Pending |
| `MphCorrectness.v` | A-L04 | MPH is injective over keywords; non-keywords never reclassified | Pending |
| `ChainCollapse.v` | A-L05 | Collapsed comparison accepts same strings as transition chain | Pending |
| `TailCallElim.v` | B-P02 | TCO'd trampoline produces same parse tree | Pending |
| `BpRangeLoop.v` | B-P05 | Specialized loop equivalent to general loop for uniform BP | Pending |
| `SegmentMerging.v` | C-D02 | Merged tree accepts same token sequences at safe boundaries | Pending |
| `JumpThreading.v` | C-D04 | Threaded tree has same dispatch outcomes | Pending |
| `PrefixCse.v` | C-D05 | CSE'd parser produces same parse tree | Pending |

### Existing Proof Infrastructure

The proofs should follow the conventions established in:

- `formal/rocq/ascent_optimizations/theories/` --- 7 files, 1,790 lines
- `formal/rocq/rule_consolidation/theories/` --- 4 files
- `formal/rocq/mathematical_analyses/theories/` --- 5 files

All proofs must have zero `Admitted` and compile with `systemd-run` resource
limits per the project's Rocq compilation policy.

---

## 13. Implementation Status

### Fully Implemented (Deployed)

| Component | Status | Notes |
|-----------|--------|-------|
| `Optimization` enum variants | Done | All 27 new variants in `cost_benefit.rs` |
| `OptimizationGates` fields | Done | All 27 boolean fields with documentation |
| `evaluate_optimizations()` | Done | All candidates scored with applicability predicates |
| `FromStr` / `Display` | Done | Short codes (ART01, BCG01, etc.) and full names |
| Lint A01-A10 | Done | Ascent VM / Codegen lints in `lint.rs` |
| Lint LEX01-LEX05 | Done | Lexer lints in `lint.rs` |
| Lint PAR01-PAR05 | Done | Parser lints in `lint.rs` |
| Lint DIS01-DIS05 | Done | Dispatch lints in `lint.rs` |
| `run_lints()` integration | Done | All new lints called in the correct order |
| `GrammarProfile` fields | Done | All fields for new predicates |

### Infrastructure Ready (Not Yet Optimizing)

| Component | Status | Notes |
|-----------|--------|-------|
| Gate propagation to codegen | Partial | Gates exist but most codegen paths do not yet branch on them |
| Cost-benefit pipeline wiring | Done | `build_grammar_profile()` populates all fields |

### Not Yet Implemented (Codegen Changes)

| Component | Status | Notes |
|-----------|--------|-------|
| A-RT01 through A-RT06 | Pending | Ascent VM runtime optimizations |
| B-CG01 through B-CG06 | Pending | Ascent codegen optimizations |
| A-L01 through A-L06 | Pending | Lexer codegen optimizations |
| B-P01 through B-P05 | Pending | Parser codegen optimizations |
| C-D01 through C-D05 | Pending | Dispatch codegen optimizations |
| D-B01 through D-B04 | Pending | Pipeline/build optimizations |
| Rocq proofs | Pending | 18 proof files required |

### Test Counts

All existing tests pass with the new lints and cost-benefit infrastructure:

- Default features: 1,764 tests passing
- All features: 2,346 tests passing
- Zero failures, zero `todo!()` stubs

---

## References

### Source Files

| Path | Description |
|------|-------------|
| `prattail/src/cost_benefit.rs` | Cost-benefit framework, `Optimization` enum, `OptimizationGates` |
| `prattail/src/lint.rs` | Unified lint layer, A01-A10, LEX01-LEX05, PAR01-PAR05, DIS01-DIS05 |
| `prattail/src/pipeline.rs` | Compilation pipeline orchestration |
| `prattail/src/dispatch.rs` | Category dispatch codegen |
| `prattail/src/decision_tree.rs` | PathMap decision tree |
| `prattail/src/lexer.rs` | DFA lexer codegen |
| `prattail/src/pratt.rs` | Pratt parser codegen |
| `prattail/src/trampoline.rs` | Trampoline parser codegen |
| `prattail/src/recursive.rs` | Recursive descent codegen |
| `prattail/src/prediction.rs` | FIRST/FOLLOW computation |
| `prattail/src/wfst.rs` | WFST construction and analysis |
| `prattail/src/token_id.rs` | Token discriminant mapping |
| `prattail/src/binding_power.rs` | Binding power table |
| `macros/src/logic/common.rs` | Shared Ascent codegen helpers |
| `macros/src/logic/congruence.rs` | Congruence rule generation |
| `macros/src/logic/rules.rs` | Rewrite rule generation |
| `macros/src/logic/equations.rs` | Equation rule generation |
| `macros/src/logic/bloom_filter.rs` | Bloom filter codegen |
| `macros/src/gen/runtime/language.rs` | Ascent struct and dispatcher generation |
| `runtime/src/binding.rs` | OrdVar, Scope wrappers |

### Documentation

| Path | Description |
|------|-------------|
| `prattail/docs/design/ascent-codegen-optimizations.md` | Existing Opt 2-5 bridge documentation |
| `docs/design/made/ascent-optimizations/README.md` | Existing Rocq proof overview |
| `prattail/docs/optimization/completed-sprints.md` | WFST-informed optimization sprints |
| `docs/design/mathematical-analyses.md` | Mathematical analysis infrastructure |
| `prattail/docs/design/semiring-catalog.md` | Semiring type reference |

### Formal Proofs

| Path | Description |
|------|-------------|
| `formal/rocq/ascent_optimizations/theories/` | Existing Opt 2-5 proofs (7 files, 1,790 lines) |
| `formal/rocq/rule_consolidation/theories/` | Opt 1 proofs (4 files) |
| `formal/rocq/mathematical_analyses/theories/` | Mathematical analysis proofs (5 files) |
