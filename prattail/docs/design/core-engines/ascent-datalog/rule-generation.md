# Rule Generation from `language!` Definitions

The `language!` macro generates Ascent Datalog rules from user-defined grammars, equations, rewrites, and logic blocks. This document describes each category of generated rules and the optimizations applied during generation.

**Prerequisites:** [Ascent Overview](overview.md), [Relation Schema](relation-schema.md)

---

## 1. Category Exploration Rules

**Source:** `macros/src/logic/categories.rs`

Exploration rules decompose terms into their subterms, populating category relations. For each constructor, a rule is generated that matches the constructor and inserts its children:

```text
// For Proc::PNew(name, body):
proc(body.clone()) <-- proc(s), if let Proc::PNew(_name, body) = s;
name(name.clone()) <-- proc(s), if let Proc::PNew(name, _body) = s;
```

### Demand-Driven Filtering (ART06)

Not all cross-category extractions are needed. ART06 computes which `(source_cat, target_cat)` pairs are actually referenced by equations/rewrites/logic rules and only generates deconstruction rules for demanded pairs:

```text
// Reachability graph:  Proc → Name → Proc  (full cycle)
// Demanded set:        {Name}  (only Name appears in user rules)
// Generated:           Proc → Name  (yes)
//                      Name → Proc  (pruned: no rule reads Proc via Name)
```

The lint diagnostic G34 reports pruned pairs.

### Collection Element Iteration

For constructors with collection fields (e.g., `PPar(HashBag<Proc>)`), iteration rules extract elements:

```text
proc(elem.clone()) <-- proc(s), if let Proc::PPar(bag) = s,
                       for elem in bag.iter();

ppar_contains(s.clone(), elem.clone()) <-- proc(s),
    if let Proc::PPar(bag) = s, for elem in bag.iter();
```

---

## 2. Reflexivity Rules

**Source:** `macros/src/logic/equations.rs`

For each category, reflexivity seeds the equivalence relation:

```text
eq_proc(t.clone(), t) <-- proc(t);
eq_name(t.clone(), t) <-- name(t);
```

With the `eqrel` annotation, Ascent handles symmetry and transitivity automatically. Reflexivity only needs to be stated once per category.

ART06: Reflexivity rules are skipped for categories not in the demanded set.

---

## 3. Congruence Rules

**Source:** `macros/src/logic/equations.rs` (equality), `macros/src/logic/congruence.rs` (rewrite)

### Equality Congruence (Auto-Generated)

For every constructor with nonterminal fields, congruence rules are generated:

```text
// For Proc::PNew(Name, Proc):
// If a ≡ a' and b ≡ b', then PNew(a, b) ≡ PNew(a', b')
eq_proc(Proc::PNew(a.clone(), b.clone()), Proc::PNew(a_prime.clone(), b_prime.clone()))
    <-- eq_name(a, a_prime),
        eq_proc(b, b_prime),
        if let Proc::PNew(a_orig, b_orig) = ... ;
```

Equality congruence is always sound: if sub-terms are equal, constructed terms are equal.

### Rewrite Congruence (User-Declared)

Rewrite congruences are NOT auto-generated. Users explicitly declare where rewrites propagate:

```text
// User declares in language!:
congruences {
    if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})
}
```

This generates an Ascent rule that propagates rewrites through `PPar` collections.

### Bloom Filter Guard (ART04)

Congruence rules use a bloom filter to build `matches!()` guards on constructor discriminants, eliminating cross-constructor pairs that cannot participate:

```text
// Without guard: tries all Proc variants against eq_proc
// With bloom guard: only tries constructors known to have equatable fields
eq_proc(...) <-- eq_proc(a, b),
    if matches!(a, Proc::PNew(..) | Proc::PPar(..) | ...),  // bloom-filtered
    ...;
```

---

## 4. User-Defined Equation Rules

**Source:** `macros/src/logic/rules.rs`

Equations from the `equations { ... }` block are compiled into Ascent rules via `generate_rule_clause()`:

### The `generate_rule_clause()` Function

This is the core abstraction (`rules.rs:50-71`). It takes:
- `left`: LHS pattern to match
- `right`: RHS pattern to construct
- `conditions`: freshness/environment conditions
- `relation_name`: target relation (`eq_cat` or `rw_cat`)
- `use_equation_matching`: whether to match via `eq_cat(s_orig, s)` instead of `cat(s)`

### Example: `(PDrop (NQuote P)) == P`

```text
eq_proc(s.clone(), t) <--
    proc(s),
    if let Proc::PDrop(f0) = s,
    let f0_deref = &**f0,
    if let Name::NQuote(f0_f0) = f0_deref,
    let p = f0_f0.clone(),
    let t = p.clone();
```

### Bidirectionality

Equations are bidirectional: both `LHS = RHS` and `RHS = LHS` directions are generated (writing to `eq_cat`, which is symmetric via `eqrel`).

### Duplicate Variable Detection

When a variable appears multiple times (e.g., `f(x, x)`), the generated code adds equality checks for co-referential occurrences.

---

## 5. Rewrite Rules

Rewrites from the `rewrites { ... }` block differ from equations:

1. **Directional**: only `LHS → RHS` is generated (writing to `rw_cat`)
2. **Equation matching**: rewrites use `eq_cat(s_orig, s)` instead of `cat(s)` to apply to equation-equivalent terms without expensive closure rules

```text
// Rewrite: (PInput ch body) => (POutput ch body)
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),          // match via equivalence class
    if let Proc::PInput(ch, body) = s,
    let t = Proc::POutput(ch.clone(), body.clone());
```

---

## 6. Fold/Big-Step Rules

For constructors annotated with `fold` evaluation mode:

```text
// For Add(Int, Int) with fold mode:
fold_int(s.clone(), result) <--
    int(s),
    if let Int::Add(a, b) = s,
    fold_int(a_orig, a_val),      // recursively fold left
    fold_int(b_orig, b_val),      // recursively fold right
    if let Int::Lit(x) = a_val,
    if let Int::Lit(y) = b_val,
    let result = Int::Lit(x + y);
```

Fold rules implement native evaluation: they pattern-match on constructor structure and produce a result via Rust computation (not further rewriting).

---

## 7. Conditions and Guards

Equation and rewrite rules can have conditions:

| Condition type | Syntax | Generated code |
|---------------|--------|---------------|
| Freshness | `where x # ch` | Freshness check on variable binding |
| Linear | `where linear(x)` | Linear resource check |
| Refinement | `where refined(x)` | Refinement type membership query |
| Behavioral guard | `guard(...)` | LogicT evaluation (see [Guards and Predicates](guards-and-predicates.md)) |

---

## 8. Optimizations

### ART06: Extended Demand Filtering

Categories not referenced by any user rule have their exploration, reflexivity, and congruence rules suppressed. This is applied at the *rule* level (relations are still declared).

### BCG06: Stratum-Ordered Rule Generation

When stratification information is available, rules are ordered by dependency depth:
- Congruence groups with fewer `eq_*` reads are placed first
- User equations are sorted by stratum index

This improves convergence speed by ensuring foundational facts are derived before rules that depend on them.

### Dead Constructor Elimination (DCE)

When pipeline analysis identifies dead constructors (unreachable from any seed term), congruence and exploration rules for those constructors are skipped.

### Subsumed Equation Elimination (N10)

If the pattern trie detects that equation A subsumes equation B (A matches every term B matches), equation B is eliminated from code generation.

### Cancellation Pair Suppression

Equation pairs that form cancellation cycles (A → B → A) are suppressed from `eqrel` generation to prevent non-convergence via symmetric expansion.

### TLS Pool Iteration

Congruence rules that iterate over multiple constructors use thread-local storage pools for the match task stack, avoiding per-iteration allocation.

### SCC Splitting

When the relation dependency graph has multiple strongly connected components, separate Ascent structs are generated for each SCC. This enables independent evaluation and potentially parallelism.

---

## Key Source Files

| File | Role |
|------|------|
| `macros/src/logic/rules.rs` | `generate_rule_clause()`, unified equation/rewrite generation |
| `macros/src/logic/equations.rs` | Reflexivity, equality congruence, equation orchestration |
| `macros/src/logic/congruence.rs` | Explicit rewrite congruence rules |
| `macros/src/logic/categories.rs` | Category exploration and deconstruction |
| `macros/src/logic/common.rs` | Shared utilities, demand analysis, TLS pool helpers |

---

**Next:** [Guards and Predicates](guards-and-predicates.md) — behavioral predicates, quantified formulas, and LogicT evaluation.
