# WFST-Informed Ascent Optimization: Completed Sprints

This document records all 13 completed optimization sprints (0--9, A, B, C) that
use WFST pipeline analysis to improve Ascent codegen quality and runtime
performance.  Each sprint builds on the `PipelineAnalysis` data produced by
Sprint 0 and is consumed by the macros crate during `generate_ascent_source()`.

## Architecture Overview

```
  LanguageSpec
       │
       ▼
  ┌─────────────────────────────────────────────────────────────┐
  │ PraTTaIL Pipeline  (prattail/src/pipeline.rs)               │
  │                                                             │
  │  NFA ──► DFA ──► WFST construction ──► PredictionWfst       │
  │                        │                     │              │
  │                  dead-rule detection    canonical_structure │
  │                  (4-tier analysis)      (De Bruijn canon.)  │
  │                        │                     │              │
  │                        ▼                     ▼              │
  │              ┌──────────────────────────────────┐           │
  │              │   PipelineAnalysis               │           │
  │              │   ├─ dead_rule_labels            │           │
  │              │   ├─ unreachable_categories      │           │
  │              │   ├─ constructor_weights         │           │
  │              │   ├─ category_weights            │           │
  │              │   ├─ isomorphic_groups           │           │
  │              │   └─ isomorphic_action_maps      │           │
  │              └──────────────────────────────────┘           │
  └─────────────────────────────────────────────────────────────┘
       │ (TokenStream, PipelineAnalysis)
       ▼
  ┌─────────────────────────────────────────────────────────────┐
  │ Macros Crate  (macros/src/logic/, macros/src/gen/)          │
  │                                                             │
  │  Sprint 1: Dead-rule DCE ─────────────────────────────┐     │
  │  Sprint 2: Premise cost ordering ─────────────────────┤     │
  │  Sprint 3: Rule ordering (cache locality) ────────────┤     │
  │  Sprint 4: Body clause ordering (fail-fast) ──────────┤     │
  │  Sprint 5: Ground rewrite pre-stratum ────────────────┤     │
  │  Sprint 6: De Bruijn pattern trie ────────────────────┤     │
  │  Sprint 7: Variable binding selectivity ──────────────┤     │
  │  Sprint A: Subsumption exploitation ──────────────────┘     │
  │                         │                                   │
  │                         ▼                                   │
  │                  Generated Ascent Code                      │
  └─────────────────────────────────────────────────────────────┘
       │
       ▼
  ┌─────────────────────────────────────────────────────────────┐
  │ Runtime  (runtime/src/)                                     │
  │                                                             │
  │  Sprint B: Term equality cache ───────── binding.rs         │
  │  Sprint 5: Two-phase run_ascent_typed ── language.rs        │
  └─────────────────────────────────────────────────────────────┘
       │
       ▼
  ┌─────────────────────────────────────────────────────────────┐
  │ Pipeline Analysis (compile-time only)                       │
  │                                                             │
  │  Sprint 8: Isomorphic WFST detection ── pipeline.rs         │
  │  Sprint 9: Integration tests ─────────── integration.rs     │
  │  Sprint C: alpha-equivalence lint ────── lint.rs            │
  └─────────────────────────────────────────────────────────────┘
```

---

## Sprint 0: Pipeline Analysis Data Export

### Intuition

The WFST pipeline already knows which rules are dead, how frequent each
constructor is, and which categories have identical dispatch topology -- but
this information was discarded after parser codegen.  Sprint 0 captures it in a
struct so downstream optimizations can use it.

### What it does

Introduces `PipelineAnalysis` in `prattail/src/lib.rs`.  After constructing
`PredictionWfst` instances and running the 4-tier dead-rule analysis, the
pipeline populates:

| Field                    | Type                                       | Source                            |
|--------------------------|--------------------------------------------|-----------------------------------|
| `dead_rule_labels`       | `HashSet<String>`                          | 4-tier WFST dead-rule detection   |
| `unreachable_categories` | `HashSet<String>`                          | All rules dead in category        |
| `constructor_weights`    | `HashMap<String, f64>`                     | `PredictionWfst` action weights   |
| `category_weights`       | `HashMap<String, f64>`                     | Per-category mean tropical weight |
| `isomorphic_groups`      | `Vec<Vec<String>>`                         | De Bruijn WFST grouping (Sp. 8)   |
| `isomorphic_action_maps` | `Vec<HashMap<u32, Vec<(String, String)>>>` | Per-group action map (Sp. 8)      |

A new entry point, `generate_parser_with_analysis()`, returns
`(TokenStream, PipelineAnalysis)`.  The macros crate's bridge function calls
this instead of `generate_parser()` and threads the analysis through to Ascent
codegen.

### Why it matters

Without a structured data channel, each downstream optimization would need to
re-derive WFST analysis from scratch -- duplicating pipeline logic, increasing
compile time, and risking inconsistency.  The struct is the single source of
truth for all WFST-informed optimizations.

### Pipeline integration

- **Produced by**: `pipeline::run_pipeline_with_analysis()` in `prattail/src/pipeline.rs`
- **Consumed by**: `generate_ascent_source()` in `macros/src/logic/mod.rs`
- **Bridge**: `macros/src/gen/syntax/parser/prattail_bridge.rs` calls
  `generate_parser_with_analysis()` and returns the pair

### Implementation summary

1. Defined `PipelineAnalysis` struct with 6 fields
2. Added `collect_pipeline_analysis()` to `pipeline.rs` that gathers data
   from `dead_rule_labels`, `PredictionWfst::actions()`, and
   `canonical_structure()` calls
3. Updated the bridge in `prattail_bridge.rs` to return the pair
4. `macros/src/logic/mod.rs` accepts `Option<&PipelineAnalysis>` throughout

### Key files

- `prattail/src/lib.rs` -- `PipelineAnalysis` definition, `generate_parser_with_analysis()`
- `prattail/src/pipeline.rs` -- `collect_pipeline_analysis()`, `run_pipeline_with_analysis()`
- `macros/src/gen/syntax/parser/prattail_bridge.rs` -- bridge function update
- `macros/src/gen/mod.rs` -- threading analysis into Ascent generation

### Test counts

4 `PipelineAnalysis` integration tests in `prattail/src/tests/integration_tests.rs`
(Sprint 9a).

---

## Sprint 1: Dead-Rule DCE

### Intuition

If the WFST pipeline already proved a constructor is dead (unreachable, no
native type, etc.), there is no reason to generate Ascent rules for it.
Skipping dead constructors reduces the SCC size, lowers compile time, and
eliminates pointless fixpoint iterations.

### What it does

During Ascent codegen, checks each constructor label against
`PipelineAnalysis.dead_rule_labels`.  Dead constructors are skipped in three
code-generation sites:

1. **HOL step rules** (`macros/src/logic/mod.rs`): Binary/unary/N-ary HOL
   step rules whose constructor label is dead are not emitted
2. **Congruence rules** (`macros/src/logic/equations.rs`): Match arms for
   dead constructors are omitted from the congruence pool
3. **Deconstruction arms** (`macros/src/logic/mod.rs`): Deconstruction rules
   that destructure dead constructors are skipped

Additionally, `unreachable_categories` (categories where ALL rules are dead)
allow entire relation families to be elided.

### Why it matters

Dead rules inflate the Ascent SCC (strongly connected component).  Each
additional rule increases semi-naive iteration cost quadratically in the worst
case.  DCE prunes rules that provably never fire, shrinking the working set.

The 4-tier analysis identifies dead rules conservatively:

| Tier | Name                | Description                                                |
|------|---------------------|------------------------------------------------------------|
| 1    | LiteralNoNativeType | Literal constructor whose category has no native type      |
| 2    | UnreachableCategory | Category unreachable from any FIRST set                    |
| 3    | WfstUnreachable     | No dispatch transition leads to the constructor            |
| 4    | SemanticLiveness    | Transitive dependency analysis via equation/rewrite groups |

Only Tiers 1 and 2 are used for codegen DCE to avoid false-positive risk.

### Pipeline integration

- **Consumes**: `PipelineAnalysis.dead_rule_labels`, `.unreachable_categories`
- **Affects**: HOL step rule count, congruence match arm count, deconstruction
  rule count

### Implementation summary

1. Guard each HOL step rule emission with `dead_rule_labels.contains(&label)`
2. Filter congruence pool constructors against dead set
3. Filter deconstruction match arms against dead set
4. If all constructors in a category are dead, skip the category entirely

### Key files

- `macros/src/logic/mod.rs` -- HOL step rules, deconstruction filtering
- `macros/src/logic/equations.rs` -- congruence pool filtering
- `macros/src/logic/common.rs` -- dead-rule helper functions

### Test counts

Covered by existing language tests (calculator, lambda, RhoCalc, ambient).  Dead
rules are correctly omitted without affecting passing test behavior.

---

## Sprint 2: Premise Cost Ordering

### Intuition

Ascent evaluates body clauses left-to-right.  If a cheap check that usually
fails is placed first, the engine avoids expensive downstream joins.
Sprint 2 sorts condition clauses by estimated cost so the cheapest fail-fast
checks come first.

### What it does

Introduces `condition_cost()` in `macros/src/logic/rules.rs` that assigns a
scalar cost to each condition variant:

| Condition   | Cost             | Rationale                                           |
|-------------|------------------|-----------------------------------------------------|
| `Freshness` | 1                | O(1) -- single `free_vars().contains()` check       |
| `EnvQuery`  | 10               | O(\|relation\|) -- scans relation for matching rows |
| `ForAll`    | 100 + body\_cost | O(\|collection\| x body\_cost) -- iterates + checks |

Condition clauses are topologically sorted respecting data dependencies (a
clause that binds variable `x` must precede any clause that reads `x`), then
stable-sorted by cost within each dependency level.

### Why it matters

Without cost ordering, condition clauses appear in declaration order, which may
interleave cheap and expensive checks arbitrarily.  A single misplaced `ForAll`
early in the body can cause Ascent to iterate over large intermediate tuple
sets before reaching the cheap `Freshness` check that would have pruned them.

The cost model ensures fail-fast evaluation: cheaper checks that are more likely
to prune the search space run first.

### Pipeline integration

- **Consumes**: nothing from `PipelineAnalysis` directly (cost model is
  structural)
- **Affects**: condition clause order within HOL step rule bodies

### Implementation summary

1. `condition_cost()` computes recursive cost
2. `condition_bindings()` collects variables each condition produces
3. `sort_conditions_by_cost()` performs topological sort with cost-based
   tiebreaking
4. HOL step rule codegen applies the sorted order

### Key files

- `macros/src/logic/rules.rs` -- `condition_cost()`, `condition_bindings()`,
  `sort_conditions_by_cost()`

### Test counts

All existing HOL step rule tests pass with reordered conditions.

---

## Sprint 3: Rule Ordering for Cache Locality

### Intuition

Ascent processes rules in declaration order within an SCC.  If the most
frequently used constructors are processed first, their intermediate tuples
remain hot in the CPU cache when subsequent rules reference the same relations.

### What it does

Sorts constructors within HOL step rule groups (binary, unary, N-ary) and
congruence rule groups by their WFST tropical weight.  Lower weight means the
constructor is dispatched to more frequently and should be evaluated first.

```
Before (declaration order):     After (weight-sorted):
  HOL step: FloatAdd (w=3.2)      HOL step: IntAdd   (w=0.7)
  HOL step: BoolOr  (w=2.1)      HOL step: BoolOr   (w=2.1)
  HOL step: IntAdd  (w=0.7)      HOL step: FloatAdd  (w=3.2)
```

### Why it matters

Modern CPUs have 32--64KB L1 data caches.  When Ascent evaluates a rule, it
accesses the relation's backing store.  If the next rule accesses the same
relation (because the next constructor belongs to the same category), the data
is still in L1.  Weight-sorting maximizes this overlap by clustering
high-frequency constructors together.

Secondary benefit: better branch prediction.  CPUs predict forward branches
as not-taken; placing the most common case first aligns with this heuristic.

### Pipeline integration

- **Consumes**: `PipelineAnalysis.constructor_weights`
- **Affects**: HOL step rule emission order, congruence match arm order

### Implementation summary

1. Each HOL step rule stores `(weight, TokenStream)` instead of raw
   `TokenStream`
2. After collecting all rules per arity group, sort by weight ascending
3. Congruence rule match arms are sorted similarly within each pool

### Key files

- `macros/src/logic/mod.rs` -- `binary_rust_rules`, `unary_rust_rules`,
  `nary_rust_rules` with weight-based sorting at lines ~761--974
- `macros/src/logic/equations.rs` -- `sorted_constructors` at lines ~163--170

### Test counts

All existing language tests pass.  Rule ordering does not affect semantics,
only evaluation order.

---

## Sprint 4: Body Clause Ordering

### Intuition

In congruence rules, equality checks for child fields can be reordered.
Checking the field whose category has the most constructors first maximizes
the probability that the check fails, pruning the cross-product earlier.

### What it does

Reorders equality checks in congruence rules by category diversity.  Category
diversity is approximated by `category_weights` from `PipelineAnalysis`:
higher weight indicates more distinct constructors (more diverse), so equality
checks for higher-weight categories are placed first.

```
Congruence rule for Add(left: Expr, right: Expr):
  Before:  eq_expr(s.left, t.left), eq_expr(s.right, t.right)
  After:   sorted by category weight -- no change for same-type fields,
           but for mixed-type constructors like If(cond: Bool, then: Expr, else: Expr),
           the Bool field (fewer constructors, lower weight) moves last.
```

### Why it matters

Ascent's semi-naive evaluation forms cross-products of `cat(s), cat(t)` pairs.
The cross-product has O(|cat|^2) tuples.  Each equality check filters non-matching
pairs.  Placing the most discriminating check first (highest diversity) prunes
the largest fraction of pairs on the first pass, reducing the number of
subsequent equality lookups.

### Pipeline integration

- **Consumes**: `PipelineAnalysis.category_weights`
- **Affects**: equality check order within congruence rule bodies

### Implementation summary

1. Collect `(field_index, field_type_string)` pairs for each congruence pool
2. Sort by `category_weights[field_type]` descending (highest weight first)
3. Emit `eq_checks` in the sorted order

### Key files

- `macros/src/logic/equations.rs` -- `eq_check_pairs` sorting at lines ~223--253

### Test counts

All existing congruence tests pass.  Reordering equality checks does not
affect semantics.

---

## Sprint 5: Ground Rewrite Pre-Stratum

### Intuition

Ground HOL step rules match only literal arguments and produce only literal
results.  They converge in O(depth) iterations because no new non-literal
terms are ever created.  Evaluating them in a separate, smaller Ascent struct
before the main fixpoint reduces the main SCC's iteration count.

### What it does

Generates a two-phase `run_ascent_typed()`:

```
Phase 1: Pre-Stratum (ground rules only)
  ┌──────────────────────────────────────┐
  │ Ascent struct: GroundPreStratum      │
  │  - Deconstruction rules              │
  │  - Ground HOL step rules             │
  │  - Category expansion rules          │
  │  - Reflexivity rules                 │
  │ Converges in O(depth) iterations     │
  └──────────────────────────────────────┘
              │ seeds main fixpoint
              ▼
Phase 2: Main Fixpoint (all rules)
  ┌──────────────────────────────────────┐
  │ Ascent struct: Full                  │
  │  - All HOL step rules (incl. ground) │
  │  - Congruence rules                  │
  │  - User-defined rewrites             │
  │  - Equation rules                    │
  └──────────────────────────────────────┘
```

The main fixpoint retains ground rules for correctness: congruence and
user-defined rewrites can create new terms that trigger ground rules again
during fixpoint.

### Why it matters

The pre-stratum's Ascent struct has far fewer rules (ground HOL step only),
producing a smaller SCC with fewer relations.  This reduces the per-iteration
cost of the pre-stratum.  The main fixpoint then starts with a populated
result set, reducing its iteration count because ground rewrites have already
converged.

Without the pre-stratum, the main fixpoint must evaluate all rules together,
including ground rules that generate intermediate tuples that never interact
with non-ground rules until convergence.

### Pipeline integration

- **Consumes**: `PipelineAnalysis` (indirectly, for dead-rule filtering of
  ground rules)
- **Produces**: `AscentSourceOutput.pre_stratum_content: Option<TokenStream>`
- **Affects**: `run_ascent_typed()` structure in `macros/src/gen/runtime/language.rs`

### Implementation summary

1. `is_ground_hol_step_rule()` checks that all arguments are literal patterns
   and the result is a literal construction
2. `generate_ground_hol_step_rules()` collects ground rules separately
3. `generate_pre_stratum_content()` generates the pre-stratum Ascent struct
   with deconstruction, ground HOL step, category expansion, and reflexivity
   rules
4. `run_ascent_typed()` calls the pre-stratum first, then seeds the main
   fixpoint with its results

### Key files

- `macros/src/logic/mod.rs` -- `generate_pre_stratum_content()`,
  `generate_ground_hol_step_rules()`, `is_ground_hol_step_rule()`
- `macros/src/gen/runtime/language.rs` -- two-phase `run_ascent_typed()`
- `macros/src/logic/common.rs` -- ground-rule identification helpers

### Test counts

All existing language tests pass.  The pre-stratum produces identical results
to the single-phase fixpoint for ground-only inputs.

---

## Sprint 6: De Bruijn Pattern Trie (6a--6f)

### Intuition

Equations and rewrites whose LHS patterns are alpha-equivalent (identical up to
variable renaming) can share matching code.  Patterns that are strict
generalizations of other patterns subsume them, enabling elimination.  A trie
indexed by De Bruijn-canonicalized byte paths makes these relationships
discoverable at compile time.

### What it does

Sprint 6 introduces three new modules:

- **`pattern_codec.rs`** (6b): Serializes `Pattern`/`PatternTerm` into byte
  sequences where alpha-equivalent patterns produce identical bytes.  Uses a
  MORK-compatible 2-bit prefix tag scheme:

  ```
  0b00_aaaaaa (0x00-0x3F)  Arity(a)      -- Apply with a children
  0b10_iiiiii (0x80-0xBF)  VarRef(i)     -- Reference to i-th variable
  0b11_000000 (0xC0)       NewVar        -- Introduce a fresh variable
  0b11_ssssss (0xC1-0xFE)  SymbolSize(s) -- Next s bytes = constructor name
  0b01_tttttt (0x40-0x4B)  PraTTaIL ext  -- Collection, Rest, Map, Zip, Lambda, Subst
  ```

  Alpha-equivalence guarantee: `encode(p) == encode(q)` iff `p` is alpha-
  equivalent to `q`.

- **`bloom_filter.rs`** (6c): O(1) negative rejection before PathMap descent.
  3 hash functions, ~1.2 bytes per element, ~1% false positive rate.

- **`pattern_trie.rs`** (6d--6f): PathMap indexed by De Bruijn byte paths.
  `PatternIndex` wraps a `PathMap<RuleIdSet>` and a `BloomFilter`.  Provides:

  - `compute_fine_dependency_groups()` -- union-find over constructor labels
    to identify independent rule groups
  - `find_alpha_equivalent_groups()` -- collision classes in LHS trie (same
    byte path = same alpha-class)
  - `detect_subsumption()` -- prefix/matching queries for general-subsumes-
    specific relationships

### Why it matters

Without the pattern trie, the system cannot detect that two equations with
different variable names have identical matching structure.  This means:

1. Redundant matching code for alpha-equivalent patterns
2. No subsumption detection -- a general rule silently overlaps a specific one,
   causing unnecessary Ascent iterations for the specific rule
3. Coarse dependency groups (entire language treated as one SCC instead of
   independent sub-problems)

Fine-grained dependency groups reduce SCC sizes.  Alpha-equivalent groups
enable shared matching (deferred to multi-stratum sprint).  Subsumption
detection enables Sprint A's equation elimination.

### Pipeline integration

- **Consumes**: `language.equations`, `language.rewrites`
- **Produces**: dependency groups, alpha-equivalent groups, subsumption pairs
- **Used by**: Sprint A (subsumption exploitation), diagnostic warnings

### Implementation summary

1. `pattern_to_debruijn_bytes()` in `pattern_codec.rs` encodes patterns
2. `PatternIndex::build()` indexes all equation/rewrite LHS patterns
3. `compute_fine_dependency_groups()` uses union-find over shared constructor
   labels
4. `find_alpha_equivalent_groups()` collects `RuleId` lists per byte path
5. `detect_subsumption()` checks prefix relationships between byte paths
6. Subsumption warnings emitted to stderr during compilation

Sprints 6g/6h (multi-stratum evaluation via per-group Ascent structs) deferred
due to insufficient group sizes in current grammars (25/66 groups in RhoCalc
are singletons).

### Key files

- `macros/src/logic/pattern_codec.rs` -- De Bruijn byte encoding
- `macros/src/logic/bloom_filter.rs` -- Bloom filter for negative rejection
- `macros/src/logic/pattern_trie.rs` -- PathMap-based pattern index, union-find,
  subsumption detection
- `macros/src/logic/mod.rs` -- integration point (build index, compute groups,
  emit warnings)

### Test counts

15 pattern\_codec/trie tests in `macros/src/logic/pattern_trie.rs`.

---

## Sprint 7: Variable Binding Selectivity

### Intuition

When a pattern variable appears more than once on the LHS, the system must
check that all occurrences refer to the same term.  If this equality check is
deferred until after the full LHS is destructured, the engine wastes work on
terms that will ultimately fail the check.  Interleaving the check at the
earliest valid position enables fail-fast evaluation.

### What it does

In `macros/src/ast/pattern.rs`, when emitting Ascent clause sequences for
pattern matching, the system tracks variable bindings.  On the first occurrence
of a variable, it emits a destructuring clause that binds the variable.  On
subsequent occurrences, instead of deferring the equality check to a batch at
the end, it emits the check inline -- immediately after the second occurrence's
destructuring clause.

```
Pattern: f(x, g(x))

Before (deferred):
  cat(s), for (x0, x1) in deconstruct_f(s),
  cat_inner(x1), for (x2) in deconstruct_g(x1),
  eq(x0, x2)                                    // ← deferred to end

After (interleaved, Sprint 7):
  cat(s), for (x0, x1) in deconstruct_f(s),
  cat_inner(x1), for (x2) in deconstruct_g(x1),
  eq(x0, x2)                                    // ← at earliest valid position
```

In this simple example the position is the same, but for patterns with
multiple repeated variables across different branches, interleaving places each
check immediately after both sides are bound, failing before deeper
destructuring proceeds.

### Why it matters

Without interleaving, all equality checks are batched at the end of the clause
sequence.  For deeply nested patterns with multiple repeated variables, this
means the engine fully destructures the entire term tree before discovering
that a shallow variable mismatch invalidates the match.  Fail-fast evaluation
prunes the search space earlier, reducing intermediate tuple counts.

### Pipeline integration

- **Consumes**: nothing from `PipelineAnalysis` directly (structural optimization)
- **Affects**: Ascent clause sequence order in equation/rewrite pattern matching

### Implementation summary

1. `pattern.rs` tracks a `HashMap<String, Ident>` of bound variables
2. First occurrence: emit destructuring, insert into map
3. Subsequent occurrence: immediately emit `eq(existing, term_var)` check

### Key files

- `macros/src/ast/pattern.rs` -- variable binding tracking and inline
  eq check emission (~lines 950--965)

### Test counts

All existing pattern-matching tests pass.  The interleaved checks produce
identical results to deferred checks.

---

## Sprint 8: Isomorphic WFST Detection (8a--8b)

### Intuition

Categories with identical dispatch structure (same tokens, same transitions,
same weights) but different action labels have isomorphic WFSTs.  If
detected at compile time, a single template can generate code for all members
of the group, with action labels substituted as parameters.

### What it does

Sprint 8 introduces De Bruijn action indices and canonical WFST structures:

- **`CanonicalWfstStructure`** (`prattail/src/wfst.rs`): Replaces concrete
  action indices with sequential De Bruijn indices (0, 1, 2, ...) assigned in
  deterministic traversal order (state 0 first, sorted by `token_id` within
  each state).  Records `CanonicalActionShape` (Direct/Lookahead/Cast/etc.)
  for each De Bruijn position.

- **`canonical_structure()`**: Produces the canonical form of a `PredictionWfst`.
  Two WFSTs are alpha-equivalent iff their canonical structures are equal.

- **`canonical_hash()`**: 64-bit hash of the canonical structure for fast
  candidate identification.

- **`group_isomorphic_wfsts()`** (`pipeline.rs`): Groups categories by
  canonical structure equality.  Only groups with >= 2 members are returned.

- **`build_isomorphic_action_maps()`** (`pipeline.rs`): For each group, maps
  De Bruijn index to `Vec<(category, rule_label)>` across group members.

```
Example: Int and Float categories with identical +, -, * dispatch topology

  CanonicalWfstStructure:
    states: [State(start), State(final, w=0.0)]
    transitions: [(Plus, db0, s1, 0.0), (Minus, db1, s1, 0.0), (Star, db2, s1, 0.0)]
    action_shapes: [Direct, Direct, Direct]

  Isomorphic group: ["Float", "Int"]
  Action map: { 0: [("Float","FloatAdd"), ("Int","IntAdd")],
                1: [("Float","FloatSub"), ("Int","IntSub")],
                2: [("Float","FloatMul"), ("Int","IntMul")] }
```

Sprints 8c--8g (template instantiation via `macro_rules!`) deferred pending
grammar complexity analysis.

### Why it matters

Without isomorphic detection, each category gets independent codegen even when
the generated code is structurally identical.  Template instantiation (future
sprint) would reduce generated code volume, improving compile time and
instruction-cache utilization.  Sprint 8 provides the detection infrastructure.

### Pipeline integration

- **Consumes**: `PredictionWfst` instances per category
- **Produces**: `PipelineAnalysis.isomorphic_groups`,
  `.isomorphic_action_maps`
- **Future consumer**: Template instantiation (8c--8g)

### Implementation summary

1. `CanonicalWfstStructure` with `CanonicalState` and `CanonicalActionShape`
2. `canonical_structure()` on `PredictionWfst` performs De Bruijn renaming
3. `canonical_hash()` for fast candidate filtering
4. `group_isomorphic_wfsts()` groups by canonical structure equality
5. `build_isomorphic_action_maps()` records per-group action correspondences

### Key files

- `prattail/src/wfst.rs` -- `CanonicalWfstStructure`, `canonical_structure()`,
  `canonical_hash()`
- `prattail/src/pipeline.rs` -- `group_isomorphic_wfsts()`,
  `build_isomorphic_action_maps()`

### Test counts

6 canonical WFST tests in `prattail/src/tests/integration_tests.rs` (Sprint 9).

---

## Sprint 9: Integration Testing

### Intuition

Individual sprint implementations need cross-cutting tests that verify
`PipelineAnalysis` data is correctly populated and that the various
optimization components interact correctly.

### What it does

Adds integration tests that exercise the full pipeline and verify analysis
output:

1. **`test_pipeline_analysis_populated`** -- Verifies `constructor_weights`
   and `category_weights` are non-empty for the calculator spec
2. **`test_pipeline_analysis_isomorphic_groups_simple`** -- Single-category
   spec has no isomorphic groups (need >= 2)
3. **`test_pipeline_analysis_isomorphic_two_categories`** -- Two categories
   with identical dispatch topology are grouped
4. **`test_pipeline_analysis_dead_rules_absent`** -- Calculator spec has no
   dead rules (all reachable)

### Why it matters

Unit tests within individual sprints test components in isolation.  Integration
tests verify that the pipeline correctly populates all `PipelineAnalysis`
fields and that optimizations compose correctly.

Benchmarking sprints 9h/9i deferred -- perf profiling infrastructure from the
profiling sprints covers the same ground.

### Pipeline integration

- **Consumes**: `generate_parser_with_analysis()` output
- **Validates**: all `PipelineAnalysis` fields

### Implementation summary

1. Helper function `calculator_spec()` builds a minimal `LanguageSpec`
2. Helper function for two-category spec (Int + Float with identical dispatch)
3. Assertions on `constructor_weights`, `category_weights`,
   `isomorphic_groups`, `dead_rule_labels`

### Key files

- `prattail/src/tests/integration_tests.rs` -- all Sprint 9 tests

### Test counts

4 `PipelineAnalysis` integration tests, 15 pattern\_codec/trie tests,
6 canonical WFST tests.  Total Sprint 9 contribution: 25 tests.

---

## Sprint A: N10 Subsumption Exploitation

### Intuition

When Sprint 6's `detect_subsumption()` finds that equation A's LHS pattern
subsumes equation B's LHS pattern, equation B is redundant: any term matching B
also matches A, and equations are symmetric (both sides are interchangeable).
Sprint A uses this to skip subsumed equations in codegen.

### What it does

Builds a `HashSet<usize>` of subsumed equation indices by calling
`detect_subsumption()` on the pattern trie and collecting equation indices
where both the general and specific rules are equations (not rewrites).
Subsumed equation indices are passed to `generate_congruence_rules()` and
`generate_equation_hol_step_rules()`, which skip them.

```
Example:
  equation eq1: f(x, y) = g(y, x)     // general pattern
  equation eq2: f(a, a) = g(a, a)     // specific pattern (subsumed by eq1)

  eq2 is skipped in codegen: any term matching f(a, a) also matches f(x, y),
  and equation symmetry guarantees the RHS subsumption is automatic.
```

Only equations are eligible -- rewrites are directional, so RHS subsumption
requires separate analysis (deferred).

### Why it matters

Subsumed equations generate Ascent rules that produce tuples already derivable
from the general equation.  These redundant tuples waste iteration time and
memory in the fixpoint computation.  Eliminating them reduces the number of
rules in the SCC.

### Pipeline integration

- **Consumes**: `detect_subsumption()` output from Sprint 6's pattern trie
- **Affects**: equation count in Ascent codegen

### Implementation summary

1. `compute_subsumed_equations()` in `macros/src/logic/mod.rs` builds the
   subsumed index set
2. Congruence codegen checks `subsumed_indices.contains(&eq_idx)` before
   emitting each equation's rules
3. HOL step equation codegen similarly filters

### Key files

- `macros/src/logic/mod.rs` -- `compute_subsumed_equations()`
- `macros/src/logic/equations.rs` -- subsumed equation filtering
- `macros/src/logic/rules.rs` -- subsumed equation filtering in HOL step rules
- `macros/src/logic/pattern_trie.rs` -- `detect_subsumption()`

### Test counts

1,331 -> 1,339 tests (8 new tests covering subsumption exploitation).

---

## Sprint B: R1 Term Equality Cache

### Intuition

During Ascent fixpoint evaluation, `Scope::term_eq()` is called repeatedly
for the same term pairs (equality checks in congruence rules).  A thread-local
cache keyed by structural hash pairs avoids redundant deep comparisons.

### What it does

Adds a TLS `Cell<HashMap<(u64, u64), bool>>` in `runtime/src/binding.rs`:

- **`TERM_EQ_CACHE`**: Thread-local cache using the `Cell<HashMap>` take/set
  pattern (zero borrow-tracking overhead, same pattern as pipeline TLS
  buffer pools)
- **`structural_scope_hash()`**: Computes a 64-bit hash of a `Scope`'s
  `unsafe_pattern` and `unsafe_body` fields
- **`cached_term_eq()`**: Checks cache before calling `term_eq()`.  Cache key
  is canonicalized `(min(h_a, h_b), max(h_a, h_b))` so `(a, b)` and `(b, a)`
  share the same entry
- **`clear_term_eq_cache()`**: Called at the start of each `run_ascent_typed()`
  to prevent stale entries from a previous evaluation

Collision probability: ~N^2/2^64 for N distinct terms.  For N = 10,000:
~5.4 x 10^-12.

### Why it matters

`Scope::term_eq()` performs deep structural comparison traversing the entire
term tree.  In Ascent's semi-naive evaluation, the same term pair may be
compared many times across iterations as new tuples are derived.  The cache
reduces these to O(1) lookups after the first comparison.

The `Cell<HashMap>` take/set pattern avoids `RefCell` borrow-tracking overhead,
matching the performance characteristics of the pipeline's TLS buffer pools.

### Pipeline integration

- **Runtime only**: no compile-time `PipelineAnalysis` dependency
- **Cleared at**: start of `run_ascent_typed()` (both standard and
  core-discriminated variants)
- **Used by**: every `eq_*` relation check in Ascent-generated congruence rules

### Implementation summary

1. `TERM_EQ_CACHE` thread-local with `Cell<HashMap>`
2. `structural_scope_hash()` hashes pattern + body
3. `cached_term_eq()` with canonical key ordering
4. `clear_term_eq_cache()` with take/clear/set
5. `term_eq_cache_size()` for diagnostics
6. Specialized `BoundTerm<String>` impl for the common case

### Key files

- `runtime/src/binding.rs` -- `TERM_EQ_CACHE`, `cached_term_eq()`,
  `clear_term_eq_cache()`, `structural_scope_hash()`
- `macros/src/gen/runtime/language.rs` -- `clear_term_eq_cache()` call at
  start of `run_ascent_typed()`

### Test counts

Covered by existing language tests.  Cache behavior is transparent -- identical
results with or without caching.

---

## Sprint C: C1 Alpha-Equivalence Lint

### Intuition

Two grammar rules may have different variable names but identical binding
structure.  Sprint C detects this using De Bruijn encoding of `SyntaxItemSpec`
sequences, complementing the existing G07 lint (exact string match) with finer
structural equivalence detection.

### What it does

Adds lint **G24** (`alpha-equivalent-rules`) to `prattail/src/lint.rs`.
Uses a `DebruijnEnv` that assigns sequential encounter-order slots to
variables:

- First occurrence of a variable: tag `0xC0` (NewVar)
- Subsequent occurrences: tag `0x80 | slot` (VarRef)
- Terminals, NonTerminals, Sep/Map/Zip, Optional, BinderCollection:
  deterministic tag bytes

```
Example:
  rule A in Expr: x "+" y   →  bytes: [NewVar, Terminal("+"), NewVar]
  rule B in Expr: a "+" b   →  bytes: [NewVar, Terminal("+"), NewVar]
  ⇒ G24 fires: A and B are alpha-equivalent

  rule C in Expr: x "+" x   →  bytes: [NewVar, Terminal("+"), VarRef(0)]
  ⇒ C is NOT alpha-equivalent to A/B (binding structure differs)
```

G24 runs after G07 to avoid double-reporting: groups where all members have
identical string signatures (G07's domain) are excluded.  G24 only fires for
groups where De Bruijn bytes match but string signatures differ -- true
alpha-equivalence that G07 misses.

### Why it matters

Without G24, two rules with identical structure but different variable names
go undetected.  G07 catches exact duplicates (same variable names), but misses
the case where `rule A: x "+" y` and `rule B: a "+" b` are structurally
identical.  Alpha-equivalent rules are likely copy-paste errors and generate
redundant parser/Ascent code.

### Pipeline integration

- **Compile-time lint**: runs during `lint::run_lints()`
- **Complements**: G07 (exact string match -- catches `x "+" y` == `x "+" y`)
- **G24 catches**: `x "+" y` is alpha-equivalent to `a "+" b` (different names,
  same structure)

### Implementation summary

1. `DebruijnEnv` struct with `var_slots: HashMap<String, u8>` and `next_slot`
2. `syntax_item_debruijn_bytes()` encodes a `&[SyntaxItemSpec]` into De Bruijn
   bytes
3. `encode_syntax_item()` handles all `SyntaxItemSpec` variants with
   deterministic tags
4. `lint_g24_alpha_equivalent_rules()` groups rules by category, computes
   De Bruijn bytes, detects collision classes, excludes G07-covered groups

### Key files

- `prattail/src/lint.rs` -- `DebruijnEnv`, `syntax_item_debruijn_bytes()`,
  `encode_syntax_item()`, `lint_g24_alpha_equivalent_rules()`

### Test counts

8 new lint tests for G24.  Total test count after Sprint C: 1,339.

---

## Summary Table

| Sprint | Name                         | Type       | Consumes from PipelineAnalysis               | Key Effect                             |
|--------|------------------------------|------------|----------------------------------------------|----------------------------------------|
| 0      | Pipeline Analysis Export     | Infra      | --                                           | Data channel for all downstream opts   |
| 1      | Dead-Rule DCE                | Codegen    | `dead_rule_labels`, `unreachable_categories` | Prunes dead Ascent rules               |
| 2      | Premise Cost Ordering        | Codegen    | (structural)                                 | Fail-fast condition evaluation         |
| 3      | Rule Ordering                | Codegen    | `constructor_weights`                        | Cache locality, branch prediction      |
| 4      | Body Clause Ordering         | Codegen    | `category_weights`                           | Fail-fast equality checks              |
| 5      | Ground Rewrite Pre-Stratum   | Codegen+RT | (indirect)                                   | Two-phase evaluation, O(depth) pre     |
| 6      | De Bruijn Pattern Trie       | Analysis   | (structural)                                 | Dependency groups, subsumption         |
| 7      | Variable Binding Selectivity | Codegen    | (structural)                                 | Inline eq checks at earliest point     |
| 8      | Isomorphic WFST Detection    | Analysis   | `PredictionWfst`                             | Template instantiation infrastructure  |
| 9      | Integration Testing          | Testing    | all fields                                   | Cross-cutting validation               |
| A      | Subsumption Exploitation     | Codegen    | Sprint 6 subsumption pairs                   | Eliminates redundant equations         |
| B      | Term Equality Cache          | Runtime    | --                                           | Memoizes deep comparisons              |
| C      | Alpha-Equivalence Lint       | Lint       | (structural)                                 | Detects alpha-equivalent grammar rules |
