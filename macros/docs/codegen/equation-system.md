# Equation Extraction and Optimization

**Source**: [`macros/src/logic/equations.rs`](../../src/logic/equations.rs)

## 1. Overview / Purpose

The equation module generates all equality-related Ascent Datalog rules for
a grammar. These rules establish and propagate equivalence relations over
terms in each category. The module generates three kinds of rules:

1. **Reflexivity**: `eq_cat(t, t) <-- cat(t)` -- every term equals itself
2. **Equality congruence**: If constructor arguments are equal, the constructed
   terms are equal. This is auto-generated for all constructors.
3. **User-defined equations**: Pattern-based equivalences from the grammar spec

The module implements several compile-time optimizations:

- **Sprint A (N10)**: Subsumed equation elimination
- **Sprint 1**: Dead constructor elimination (with WFST analysis)
- **BCG03**: Equation-active constructor filtering for congruence pruning
- **BCG06**: SCC-based stratification for intra-struct rule ordering
- **ART04**: Bloom filter discriminant pre-check for congruence rules
- **ART06**: Demand-driven category filtering

## 2. Architecture and Data Flow

```
 LanguageDef + PipelineAnalysis + subsumed_equations + cancellation_equations
     |
     v
 generate_equation_rules(language, cat_filter, analysis, subsumed, cancellation,
                         emit_diagnostics, demanded, strat_info)
     |
     +---> generate_reflexivity_rules(language, cat_filter, demanded)
     |         |
     |         v
     |     eq_cat(t, t) <-- cat(t)   for each demanded category
     |
     +---> generate_congruence_rules(language, cat_filter, analysis,
     |                                emit_diagnostics, demanded, strat_info)
     |         |
     |         +---> compute_equation_active_constructors(language)  // BCG03
     |         +---> Group constructors by (category, field_types)
     |         +---> Build per-category BloomFilter                  // ART04
     |         +---> Sort groups by dependency depth                 // BCG06
     |         +---> Sort constructors by WFST weight                // Sprint 3/4
     |         +---> Generate consolidated rules with:
     |         |         - discriminant equality guard               // ART04
     |         |         - matches!() subset guard                   // ART04
     |         |         - TLS pool extraction
     |         |         - eq_field checks (reordered by diversity)  // Sprint 4
     |         +---> Emit G36 (BCG03), G37 (ART04) diagnostics
     |         |
     |         v
     |     Vec<TokenStream>
     |
     +---> rules::generate_equation_rules(language, cat_filter,
     |                                     subsumed, cancellation, demanded, strat_info)
     |         |
     |         +---> Filter: skip subsumed (N10), cancellation, non-demanded (ART06)
     |         +---> Sort by stratum index (BCG06)
     |         +---> For each equation: generate_rule_clause (forward + backward)
     |         |
     |         v
     |     Vec<TokenStream>
     |
     v
 TokenStream (all equation rules combined)
```

### Stratification Pipeline (BCG06)

```
 stratify_equation_rules(language)
     |
     +---> Phase 1: Classify rules
     |         - Reflexivity: one per category, reads cat, writes eq_cat
     |         - Congruence: per (cat, field_types) group, reads eq_field, writes eq_cat
     |         - UserDefined: per equation, reads referenced eq_cats, writes eq_cat
     |
     +---> Phase 2: Build dependency graph
     |         - Edge (i -> j) when rule i reads eq_cat that rule j writes
     |
     +---> Phase 3: Tarjan SCC computation
     |         - Yields SCCs in reverse topological order
     |
     +---> Phase 4: Topological sort of SCCs into strata
     |
     v
 StratificationInfo { total_rules, strata, scc_count, ... }
```

## 3. Key Types and Functions

### `EqRuleKind`

```rust
pub enum EqRuleKind {
    Reflexivity,   // eq_cat(t, t) <-- cat(t)
    Congruence,    // eq_cat(s, t) <-- cat(s), cat(t), eq_field(sf, tf)
    UserDefined,   // user equation pattern matching
}
```

### `ClassifiedEqRule`

```rust
pub struct ClassifiedEqRule {
    pub id: usize,
    pub kind: EqRuleKind,
    pub label: String,                        // e.g., "reflexivity:Proc"
    pub writes_category: String,              // eq_cat relation written
    pub reads_eq_categories: BTreeSet<String>, // eq_field relations read
}
```

### `Stratum`

```rust
pub struct Stratum {
    pub index: usize,
    pub rules: Vec<ClassifiedEqRule>,
}
```

### `StratificationInfo`

```rust
pub struct StratificationInfo {
    pub total_rules: usize,
    pub reflexivity_count: usize,
    pub congruence_count: usize,
    pub user_defined_count: usize,
    pub strata: Vec<Stratum>,
    pub scc_count: usize,
}
```

### Public API

| Function                        | Returns                | Purpose                            |
|---------------------------------|------------------------|------------------------------------|
| `generate_equation_rules`       | `TokenStream`          | Main entry: all equation rules     |
| `generate_equation_rules_reflexivity_only` | `TokenStream` | Reflexivity only (pre-stratum)    |
| `stratify_equation_rules`       | `StratificationInfo`   | BCG06 SCC-based analysis           |

### Internal Functions

| Function                                | Purpose                                        |
|-----------------------------------------|------------------------------------------------|
| `generate_reflexivity_rules`            | `eq_cat(t,t)` for each demanded category       |
| `generate_congruence_rules`             | Consolidated equality congruence               |
| `compute_equation_active_constructors`  | BCG03: transitive closure for equation activity |
| `collect_pattern_eq_deps`               | Collect eq_cat deps from patterns              |
| `tarjan_scc`                            | Tarjan's SCC algorithm                         |

## 4. Algorithm Description

### Reflexivity Rules

```
for each category in language.types:
    if category NOT in demanded set: skip  // ART06
    if category NOT in cat_filter: skip
    emit: eq_cat(t.clone(), t.clone()) <-- cat(t);
```

### BCG03: Equation-Active Constructor Filtering

The equation-active set determines which constructors need congruence match arms:

```
Step 1: Direct activity
    directly_active = constructors appearing in any equation LHS or RHS pattern

Step 2: Category activation
    active_categories = categories containing directly_active constructors

Step 3: Transitive closure (fixpoint)
    loop:
        for each constructor C not yet active:
            if C has a field whose category is active:
                mark C as equation-active
                mark C's result category as active
        if no new categories activated: break

Return: equation_active set
```

**Invariant**: A constructor is equation-active if and only if non-trivial
equalities could flow through it (directly from equations, or transitively
from field categories with non-trivial equalities).

### Congruence Rule Generation

```
1. Group constructors by (category, field_type_vector)
2. BCG03: Skip equation-inert constructors
3. ART04: Build bloom filter per category, generate guards
4. BCG06: Sort groups by dependency depth (fewer eq_* reads first)
5. Sprint 3/4: Sort constructors within groups by WFST weight

For each group:
    Build TLS pool arms: extract (s_f0, ..., t_f0, ...) from (s, t) pairs
    Build equality checks: eq_field(s_fi, t_fi) for each field
    Sprint 4: Reorder checks by category diversity (most diverse first)
    Generate consolidated Ascent rule with:
        - cat(s), cat(t)
        - discriminant(s) == discriminant(t)        // ART04
        - matches!(s, CtorA(..) | CtorB(..))       // ART04 (if subset)
        - for bindings in TLS_POOL.extract(s, t)
        - eq_field checks
```

### BCG06: SCC-Based Stratification

```
Phase 1: Classify all equation rules
    reflexivity: (id, Reflexivity, "reflexivity:Cat", writes=Cat, reads={})
    congruence:  (id, Congruence, "congruence:Cat(F1,F2)", writes=Cat, reads={F1,F2})
    user:        (id, UserDefined, "user:EqName", writes=Cat, reads=pattern_deps)

Phase 2: Build dependency graph
    writers_by_cat: HashMap<category, Vec<rule_id>>
    For each rule r with reads_eq R:
        For each writer w of eq_R:
            add edge r -> w (r depends on w)

Phase 3: Tarjan SCC
    Compute SCCs using Tarjan's algorithm
    SCCs returned in reverse topological order (dependencies first)

Phase 4: Map SCCs to strata
    Each SCC becomes one Stratum with an index
    Strata ordered so dependencies precede dependents
```

### Sprint A (N10): Subsumed Equation Elimination

Computed in `mod.rs::compute_subsumed_equations()` using the `PatternIndex`:

```
1. Build PatternIndex from all equations and rewrites
2. detect_subsumption: find pairs where general's LHS matches strict superset
3. For equation-equation pairs where general subsumes specific:
   Add specific's index to subsumed set
4. In generate_equation_rules: skip indices in subsumed set
```

### Cancellation Pair Suppression

Equations of the form `Outer(Inner(X)) = X` are detected by
`detect_cancellation_pairs()` in `pattern.rs` and suppressed from eqrel
generation because their symmetric expansion would cause non-convergence.

## 5. Generated Code Patterns

### Reflexivity:

```rust
eq_proc(t.clone(), t.clone()) <-- proc(t);
```

### Equality Congruence (consolidated, with ART04 guards):

```rust
eq_proc(s.clone(), t.clone()) <--
    proc(s),
    proc(t),
    if std::mem::discriminant(s) == std::mem::discriminant(t),
    if matches!(s, Proc::PDrop(..) | Proc::POutput(..)),
    for (s_f0, t_f0) in {
        thread_local! {
            static POOL_PROC_EQ_CONG_0: std::cell::Cell<Vec<(Name, Name)>> =
                const { std::cell::Cell::new(Vec::new()) };
        }
        // ... TLS pool extraction ...
    }.into_iter(),
    eq_name(s_f0, t_f0);
```

### User Equation (forward direction):

```rust
eq_proc(s.clone(), t.clone()), proc(t.clone()) <--
    proc(s),
    if let Proc::PDrop(f0) = s,
    let f0_deref = &**f0,
    if let Name::NQuote(f0_f0) = f0_deref,
    let p = f0_f0.clone(),
    // BCG05 dedup guard
    if { /* hash-based dedup */ },
    let t = (p.clone()).normalize();
```

Note: User equations also emit `cat(t)` to seed the category relation with
the equation-produced term, enabling deconstruction and reflexivity.

### User Equation (backward direction):

The same equation generates a symmetric rule with LHS and RHS swapped.
Variable-only sides (just `X`) are skipped to avoid matching everything.

## 6. Integration with Pipeline

### Main Entry Point

Called from `mod.rs::generate_ascent_source()`:

```rust
let equation_rules = generate_equation_rules(
    language, None, analysis,
    &subsumed_equations, &cancellation_equations,
    true, &demanded, Some(&strat_info),
);
```

### Pre-Stratum (reflexivity only)

The pre-stratum needs reflexivity to initialize eq relations but not full
congruence or user equations:

```rust
let pre_eq = generate_equation_rules_reflexivity_only(language, None, &demanded);
```

### WFST Analysis Integration

When `analysis` is provided:
- **Sprint 1 DCE**: Dead constructors (from WFST 4-tier detection) are
  skipped in congruence rule generation
- **Sprint 3**: Congruence groups are sorted by WFST category weight
- **Sprint 4**: Equality checks are reordered by category diversity

## 7. Diagnostic Emissions

| Lint ID | Name                               | Severity | Trigger                           |
|---------|------------------------------------|----------|-----------------------------------|
| G25     | `cancellation-pair-detected`       | Note     | Cancellation pair suppressed      |
| G26     | `equation-subsumed`                | Note     | Subsumed equation eliminated      |
| G31     | `subsumed-equations-eliminated`    | Note     | Summary of N10 elimination count  |
| G36     | `equation-inert-congruence-pruned` | Note     | BCG03 pruned constructor count    |
| G37     | `bloom-filter-eq-congruence-guard` | Note     | ART04 equality guard summary      |
| G42     | `eq-strata-analysis`               | Note     | BCG06 stratification summary      |
| W09     | `cancellation-pair-missing-rewrite`| Warning  | Suppressed pair without rewrite   |

## 8. Test Coverage

The equation module is tested through:

- **Integration tests**: All language compilations (RhoCalc, Lambda, Calculator,
  etc.) exercise equation generation end-to-end
- **Edge case tests**: `languages/tests/edge_case_tests.rs` tests cancellation
  pairs, subsumed equations, and demand-driven filtering
- **Common module tests**: `common.rs` contains unit tests for demand analysis,
  reachability computation, and category filtering
- **Equations.rs tests**: The Tarjan SCC implementation has implicit coverage
  through stratification tests

## 9. Source References

- **Primary source**: [`macros/src/logic/equations.rs`](../../src/logic/equations.rs) (~900 lines)
- **User equation generation**: [`macros/src/logic/rules.rs`](../../src/logic/rules.rs), `generate_equation_rules()`
- **Demand analysis**: [`macros/src/logic/common.rs`](../../src/logic/common.rs), `compute_demanded_categories()`
- **Bloom filter**: [`macros/src/logic/bloom_filter.rs`](../../src/logic/bloom_filter.rs)
- **Rocq proofs**:
  - [`formal/rocq/codegen_optimizations/theories/BCG03_EqCongruencePrune.v`](../../../formal/rocq/codegen_optimizations/theories/BCG03_EqCongruencePrune.v)
  - [`formal/rocq/codegen_optimizations/theories/BCG06_EqStrata.v`](../../../formal/rocq/codegen_optimizations/theories/BCG06_EqStrata.v)
  - [`formal/rocq/codegen_optimizations/theories/ART06_DemandAnalysis.v`](../../../formal/rocq/codegen_optimizations/theories/ART06_DemandAnalysis.v)

## 10. Cross-References

- [bloom-filter.md](bloom-filter.md) -- ART04 bloom filter construction and verification
- [congruence-closure.md](congruence-closure.md) -- rewrite congruences (explicit, not auto-generated)
- [rule-generation.md](rule-generation.md) -- `generate_rule_clause` for user equation codegen
- [rule-fusion.md](rule-fusion.md) -- equations appear in BCG02 consumer map
- [antipattern-detection.md](antipattern-detection.md) -- C-AP03 relates to congruence chain depth
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- BCG03, BCG06, ART04, ART06 entries
