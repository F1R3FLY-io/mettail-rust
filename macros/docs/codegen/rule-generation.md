# Rule Classification and Generation

**Source**: [`macros/src/logic/rules.rs`](../../src/logic/rules.rs)

## 1. Overview / Purpose

The rules module provides the unified rule generation core that transforms
Pattern-based equations and rewrites into Ascent Datalog clauses. It is the
shared engine used by both `equations.rs` (for user-defined equations) and
`mod.rs` (for base rewrites).

The key architectural insight is that equations and rewrites differ only in:

1. The relation they write to (`eq_cat` vs `rw_cat`)
2. Whether they are bidirectional (equations) or directional (rewrites)
3. Whether they match via `cat(s)` (equations) or `eq_cat(s_orig, s)` (rewrites)

Everything else -- pattern matching, condition evaluation, RHS construction --
is shared through `generate_rule_clause`.

The module implements several codegen optimizations:

- **BCG01**: Condition cost ordering (fail-fast evaluation)
- **BCG04**: Ground-LHS rewrite seeds (direct initialization)
- **BCG05**: Normalize-on-insert deduplication guards
- **ART05**: Compile-time depth delta analysis
- **ART06**: Demand-driven equation/rewrite filtering

## 2. Architecture and Data Flow

```
 Pattern (LHS)  +  Pattern (RHS)  +  Conditions  +  relation_name
     |                 |                 |                |
     v                 v                 v                v
 generate_rule_clause(left, right, conditions, relation, language, use_eq_matching)
     |
     +---> Determine category from LHS
     +---> Find duplicate variables across LHS + RHS
     +---> left.to_ascent_clauses()  -->  AscentClauses {clauses, bindings, eq_checks}
     |
     +---> sort_conditions_by_cost(conditions)               // BCG01
     |         |
     |         v
     |     Topological sort by cost with dependency respect
     |
     +---> generate_positioned_condition_clauses(sorted, lhs) // BCG01
     |         |
     |         v
     |     Vec<PositionedClause { clause, earliest_position }>
     |
     +---> right.to_ascent_rhs(all_bindings)  -->  RHS expression
     |
     +---> Build BCG05 dedup guard
     |
     +---> interleave_body_clauses(first, lhs, eq_checks,    // BCG01
     |                              positioned, rhs_binding)
     |         |
     |         v
     |     Interleaved body clauses with conditions at earliest valid positions
     |
     +---> Insert BCG05 guard before RHS binding
     |
     v
 TokenStream: head <-- body1, body2, ..., rhs_binding;
```

### Equation Generation Path

```
 rules::generate_equation_rules(language, cat_filter, subsumed, cancellation,
                                 demanded, strat_info)
     |
     +---> Filter: skip subsumed (N10), cancellation, non-demanded (ART06)
     +---> Sort by stratum index (BCG06)
     +---> For each eligible equation:
     |         Forward:  generate_rule_clause_with_category(left, right, eq_rel, cat, false)
     |         Backward: generate_rule_clause_with_category(right, left, eq_rel, cat, false)
     |         (skip variable-only sides)
     v
 Vec<TokenStream>
```

### Rewrite Generation Path

```
 rules::generate_base_rewrites(language, cat_filter)
     |
     +---> For each rewrite (skip congruence rules):
     |         generate_rule_clause(left, right, conditions, rw_rel, language, true)
     v
 Vec<TokenStream>
```

## 3. Key Types and Functions

### `PositionedClause` (internal)

```rust
struct PositionedClause {
    clause: TokenStream,
    earliest_position: usize,  // Earliest LHS clause index where all vars available
}
```

### `DepthDeltaResult`

```rust
pub struct DepthDeltaResult {
    pub rule_name: String,
    pub is_equation: bool,
    pub lhs_depth: u32,
    pub rhs_depth: u32,
    pub delta: i32,         // rhs_depth - lhs_depth (positive = depth-increasing)
}
```

### Public API

| Function                        | Returns                        | Purpose                          |
|---------------------------------|--------------------------------|----------------------------------|
| `generate_rule_clause`          | `TokenStream`                  | Unified rule codegen (auto-category) |
| `generate_rule_clause_with_category` | `TokenStream`             | Unified rule codegen (explicit category) |
| `generate_equation_rules`       | `Vec<TokenStream>`             | User equation rules (forward + backward) |
| `generate_base_rewrites`        | `Vec<TokenStream>`             | Non-congruence rewrite rules     |
| `generate_ground_rewrite_seeds` | `(Vec<TokenStream>, usize)`    | BCG04: ground-LHS seed tuples    |
| `analyze_depth_delta`           | `Vec<DepthDeltaResult>`        | ART05: depth delta for all rules |
| `is_depth_bounded`              | `bool`                         | ART05: all deltas non-positive?  |

### Internal Functions

| Function                          | Optimization | Purpose                                  |
|-----------------------------------|--------------|------------------------------------------|
| `condition_cost`                  | BCG01        | Estimate condition evaluation cost        |
| `condition_binds`                 | BCG01        | Variables produced by a condition         |
| `condition_requires`              | BCG01        | Variables consumed by a condition         |
| `sort_conditions_by_cost`         | BCG01        | Topological sort by cost with dep respect |
| `condition_earliest_position`     | BCG01        | Earliest LHS clause for a condition       |
| `generate_positioned_condition_clauses` | BCG01  | Pair conditions with earliest positions   |
| `interleave_body_clauses`         | BCG01        | Merge LHS, conditions, RHS into body      |
| `generate_freshness_clause`       | --           | Freshness condition codegen               |
| `generate_forall_clause`          | --           | ForAll condition codegen                  |
| `pattern_depth`                   | ART05        | Constructor nesting depth of a pattern    |

## 4. Algorithm Description

### BCG01: Condition Cost Ordering (Fail-Fast)

The goal is to place cheap conditions as early as possible in the rule body
to reject non-matching tuples before expensive pattern destructuring.

**Cost model**:

| Condition Type | Cost | Rationale                                      |
|----------------|------|-------------------------------------------------|
| Pattern guard  | 1    | Single pattern match (implicit, in LHS clauses) |
| Let binding    | 0    | Free, deterministic                              |
| Freshness      | 2    | O(1) `free_vars().contains()` check              |
| EnvQuery       | 5    | O(|relation|) scan with index help               |
| ForAll         | 10+  | O(|collection| * body_cost) iteration            |

**Sorting algorithm**:

```
sort_conditions_by_cost(conditions):
    Pre-compute: costs[], binds[], requires[] for each condition

    available_from_conditions = {}
    emitted = [false; N]
    result = []

    for _ in 0..N:
        // Find cheapest unemitted condition whose inter-condition deps are met
        best = argmin over unemitted i where:
            all requirements from other conditions are in available_from_conditions
        by cost[i]

        if best found:
            emit best, add its bindings to available_from_conditions
        else:
            // Cycle or unsatisfied deps: emit remaining in declaration order
            break
```

### BCG01: Positioned Condition Interleaving

After sorting by cost, each condition is paired with its earliest valid
position in the LHS clause sequence:

```
condition_earliest_position(condition, lhs_clauses):
    required = condition_requires(condition)
    return max(lhs_clauses.binding_clause_index[var] for var in required)
```

Then `interleave_body_clauses` slots conditions at their earliest positions:

```
interleave_body_clauses(first_clause, lhs_clauses, eq_checks, positioned, rhs):
    body = [first_clause]

    // Group conditions by target slot
    for each positioned condition pc:
        slot = pc.earliest_position

    // Slot 0: conditions satisfied before any LHS clause
    body.extend(conditions at slot 0)

    // Interleave
    for (i, lhs_clause) in lhs_clauses:
        body.push(lhs_clause)
        body.extend(conditions at slot i+1)

    body.extend(eq_checks)    // backward compat (typically empty since Sprint 7)
    body.push(rhs_binding)
    return body
```

### BCG04: Ground-LHS Rewrite Seeds

A ground-LHS rewrite has a LHS pattern with no variables (all concrete
constructors and literals). Its result is statically known.

```
generate_ground_rewrite_seeds(language):
    for each non-congruence rewrite:
        if rewrite.left.is_ground():
            lhs_term = rewrite.left.to_ground_term()
            rhs_term = rewrite.right.to_ground_term()
            cat_rel = category.to_lowercase()
            yield: prog.rw_cat.push((lhs_term.normalize(), rhs_term.normalize()));
            yield: prog.cat.push((lhs_term.normalize(),));
            yield: prog.cat.push((rhs_term.normalize(),));
```

The original Ascent rule is **preserved** for soundness (equation-equivalent
terms still need to fire the rule). The seed makes the result available at
iteration 0 without scanning.

### BCG05: Normalize-on-Insert Deduplication

Each rule body includes a hash-based dedup guard before the RHS binding:

```rust
if {
    use std::hash::{Hash, Hasher};
    let mut __bcg05_h = std::hash::DefaultHasher::new();
    s.hash(&mut __bcg05_h);
    let __bcg05_hash = __bcg05_h.finish();
    thread_local! {
        static __BCG05_RULE: RefCell<(u64, HashSet<u64>)> =
            RefCell::new((0, HashSet::new()));
    }
    let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(|s| {
        let mut guard = s.borrow_mut();
        if guard.0 != __epoch {
            guard.0 = __epoch;
            guard.1.clear();       // Clear per-epoch
        }
        guard.1.insert(__bcg05_hash)
    })
}
```

The epoch mechanism ensures the HashSet is cleared between Ascent evaluations,
preventing stale entries from blocking valid rule firings.

### ART05: Depth Delta Analysis

```
analyze_depth_delta(language):
    for each equation/rewrite:
        lhs_depth = pattern_depth(rule.left)
        rhs_depth = pattern_depth(rule.right)
        delta = rhs_depth - lhs_depth
        yield DepthDeltaResult { rule_name, is_equation, lhs_depth, rhs_depth, delta }

pattern_depth(pattern):
    match pattern:
        Var => 0
        Apply { args } => 1 + max(pattern_depth(arg) for arg in args)
        Lambda { body } => 1 + pattern_depth(body)
        Collection { elements } => 1 + max(pattern_depth(elem) for elem in elements)
        Map { body } => 1 + pattern_depth(body)
        Zip { first, second } => 1 + max(pattern_depth(first), pattern_depth(second))

is_depth_bounded(results):
    return !any(r.delta > 0 for r in results)
```

## 5. Generated Code Patterns

### Equation Rule (forward direction, with BCG01 interleaving):

```rust
eq_proc(s.clone(), t.clone()), proc(t.clone()) <--
    proc(s),                                     // first clause
    if let Proc::PDrop(f0) = s,                  // LHS clause 0
    if !free_vars(&p).contains(&x),              // freshness at slot 1 (BCG01)
    let f0_deref = &**f0,                        // LHS clause 1
    if let Name::NQuote(f0_f0) = f0_deref,       // LHS clause 2
    let p = f0_f0.clone(),                        // LHS clause 3
    // BCG05 dedup guard
    if { /* hash + epoch check */ },
    let t = (p.clone()).normalize();              // RHS binding
```

### Rewrite Rule (with equation matching):

```rust
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),                          // match via equation relation
    if let Proc::PDrop(f0) = s,
    let f0_deref = &**f0,
    if let Name::NQuote(f0_f0) = f0_deref,
    let p = f0_f0.clone(),
    // BCG05 dedup guard
    if { /* hash + epoch check */ },
    let t = (p.clone()).normalize();
```

### Ground Rewrite Seed (BCG04):

```rust
// At Ascent initialization (iteration 0):
prog.rw_int.push((Int::NumLit(0).normalize(), Int::NumLit(1).normalize()));
prog.int.push((Int::NumLit(0).normalize(),));
prog.int.push((Int::NumLit(1).normalize(),));
```

## 6. Integration with Pipeline

### Rule Generation

Called from `mod.rs::generate_ascent_source()`:

```rust
let rewrite_rules = generate_rewrite_rules(language, None, analysis, true, &demanded);
```

Which internally calls:

```rust
let base_rewrites = rules::generate_base_rewrites(language, cat_filter);
let congruence_rules = congruence::generate_all_explicit_congruences(language, cat_filter, emit_diagnostics);
```

### Ground Seeds

Called from `mod.rs::generate_ascent_source()`:

```rust
let (ground_rewrite_seeds, ground_count) = rules::generate_ground_rewrite_seeds(language);
```

Seeds are stored in `AscentSourceOutput.ground_rewrite_seeds` and injected
into the Ascent struct initialization by the runtime code generator.

### Depth Delta Analysis

Called from `mod.rs::emit_depth_delta_lints()`:

```rust
let results = rules::analyze_depth_delta(language);
let is_bounded = rules::is_depth_bounded(&results);
```

### ART06 Demand Filtering

For user equations, the demanded set filters which categories receive rules:

```rust
if !demanded.contains(&category.to_string()) {
    continue;
}
```

### BCG06 Stratum Ordering

User equations are sorted by their stratum index for faster convergence:

```rust
eligible.sort_by_key(|(_, eq)| {
    eq_stratum_order.get(&eq.name.to_string()).copied().unwrap_or(usize::MAX)
});
```

## 7. Diagnostic Emissions

| Lint ID | Name                            | Severity | Trigger                           |
|---------|---------------------------------|----------|-----------------------------------|
| G35     | `ground-rewrite-short-circuit`  | Note     | BCG04: ground-LHS rewrites seeded |
| G41     | `normalize-dedup-active`        | Note     | BCG05: dedup guards emitted       |
| A01     | `depth-increasing-rule`         | Note     | ART05: positive depth delta       |
| A01     | `depth-bounded-grammar`         | Note     | ART05: all deltas non-positive    |
| A01     | `depth-unbounded-grammar`       | Warning  | ART05: depth-increasing rules exist |

## 8. Test Coverage

The rules module includes unit tests in `rules.rs::tests` covering:

- Demand analysis with equations and rewrites
- Category reachability computation
- Depth delta analysis
- Ground rewrite detection

Integration tests in `languages/tests/` exercise all rule generation paths
through complete language compilations (RhoCalc, Lambda, Calculator, etc.).

## 9. Source References

- **Primary source**: [`macros/src/logic/rules.rs`](../../src/logic/rules.rs) (~1000 lines)
- **Common utilities**: [`macros/src/logic/common.rs`](../../src/logic/common.rs) -- `generate_tls_pool_iter`, `compute_demanded_categories`
- **Pattern infrastructure**: [`macros/src/ast/pattern.rs`](../../src/ast/pattern.rs) -- `to_ascent_clauses`, `to_ascent_rhs`
- **Runtime epoch**: [`runtime/src/lib.rs`](../../../runtime/src/lib.rs) -- `bcg05_epoch()`
- **Rocq proof**: [`formal/rocq/codegen_optimizations/theories/ART05_DepthBound.v`](../../../formal/rocq/codegen_optimizations/theories/ART05_DepthBound.v)

## 10. Cross-References

- [equation-system.md](equation-system.md) -- equations use `generate_rule_clause` for both directions
- [congruence-closure.md](congruence-closure.md) -- congruence rules are generated separately but share `common.rs` utilities
- [rule-fusion.md](rule-fusion.md) -- fused rules include BCG05 dedup guards
- [bloom-filter.md](bloom-filter.md) -- ART04 guards complement BCG01 interleaving
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- BCG01, BCG04, BCG05 entries
