# Behavioral Predicates, Quantified Formulas, and LogicT

PraTTaIL supports rich guard conditions on equations and rewrites via behavioral predicates. These range from simple relation queries to full first-order logic formulas with universal and existential quantification, evaluated at runtime via the LogicT fair backtracking framework.

**Prerequisites:** [Rule Generation](rule-generation.md)

---

## 1. BehavioralPred Enum

The `BehavioralPred` type (`macros/src/ast/language.rs:227-267`) represents guard expressions:

```rust
pub enum BehavioralPred {
    RelationQuery { relation_name: Ident, args: Vec<PredArg>, negated: bool },
    Quantified { quantifier: Quantifier, var: Ident, domain: Option<Ident>,
                 bound: Option<usize>, body: Box<BehavioralPred> },
    And(Box<BehavioralPred>, Box<BehavioralPred>),
    Or(Box<BehavioralPred>, Box<BehavioralPred>),
    Not(Box<BehavioralPred>),
    Implies(Box<BehavioralPred>, Box<BehavioralPred>),
    AcMatch { bag: Ident, elements: Vec<Ident>, rest: Option<Ident> },
}
```

| Variant | Syntax | Semantics |
|---------|--------|-----------|
| `RelationQuery` | `safe(x)` or `~reachable(x,y)` | Check/negate Ascent relation membership |
| `Quantified` | `∀y ∈ nodes. body` | FOL quantification over domain |
| `And` | `a /\ b` | Short-circuit conjunction |
| `Or` | `a \/ b` | Short-circuit disjunction |
| `Not` | `~a` | Negation as finite failure |
| `Implies` | `a => b` | Sugar for `~a \/ b` |
| `AcMatch` | `ac_match(bag, {x,y,...rest})` | Associative-commutative decomposition |

---

## 2. Guard Syntax in Rules

Guards appear as premises in equation and rewrite rules:

```text
// Simple relation query guard:
equations {
    f(x) == g(x) where guard(safe(x))
}

// Quantified guard:
equations {
    approve(x) == ok(x) where guard(forall y in nodes. (reachable(x, y) => safe(y)))
}

// AC-matching guard:
rewrites {
    PPar({x, y, ...rest}) => PPar({comm(x, y), ...rest})
        where guard(ac_match(bag, {x, y, ...rest}))
}
```

Guards are evaluated after the LHS pattern match succeeds and before the RHS is constructed. A rule fires only if the guard evaluates to `true`.

---

## 3. QuantifiedFormula: Runtime Representation

At runtime, behavioral predicates are evaluated via `QuantifiedFormula` (`logict.rs:519-546`):

```rust
pub enum QuantifiedFormula {
    Atom { relation: String, args: Vec<QuantifiedArg> },
    And(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    Or(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    Not(Box<QuantifiedFormula>),
    Implies(Box<QuantifiedFormula>, Box<QuantifiedFormula>),
    ForAll { var: String, domain: QuantifiedDomain, body: Box<QuantifiedFormula> },
    Exists { var: String, domain: QuantifiedDomain, body: Box<QuantifiedFormula> },
}
```

The `BehavioralPred::to_quantified_formula()` method generates Rust code that constructs a `QuantifiedFormula` at runtime, which is then evaluated by `evaluate_quantified()`.

### Evaluation Strategy

| Formula | Evaluation |
|---------|-----------|
| `Atom(R, args)` | Query Ascent relation fixpoint for `R(args)` |
| `And(a, b)` | Short-circuit: evaluate `a`, if true evaluate `b` |
| `Or(a, b)` | Short-circuit: evaluate `a`, if false evaluate `b` |
| `Not(a)` | Evaluate `a`, negate result |
| `Implies(a, b)` | Desugar to `Or(Not(a), b)` |
| `ForAll(x, D, body)` | Enumerate all `x ∈ D`, check `body(x)` for ALL |
| `Exists(x, D, body)` | Enumerate all `x ∈ D`, check `body(x)` for ANY |

The universal quantifier `∀x ∈ D. φ(x)` is evaluated as its dual: `¬∃x ∈ D. ¬φ(x)`.

---

## 4. LogicT Fair Backtracking

**Source:** `prattail/src/logict.rs`

LogicT implements fair backtracking search based on Kiselyov, Shan, Friedman & Sabry (ICFP 2005).

### The Fairness Problem

Standard depth-first search (as in Prolog) can starve late branches. If branch A produces infinite results, branch B is never explored:

```text
Depth-first: [a₁, a₂, a₃, a₄, ...]   — branch B starved
Fair:        [a₁, b₁, a₂, b₂, ...]   — both explored
```

### LogicStream

`LogicStream<T>` (`logict.rs:86-89`) is a fair search stream backed by a `VecDeque<Branch<T>>`:

```rust
pub struct LogicStream<T> {
    branches: VecDeque<Branch<T>>,  // Round-robin branch queue
}
```

Branches are either `Ready(value)` (immediate result) or `Suspended(closure)` (deferred computation).

### Core Operations

All LogicT operations derive from `msplit` — the fundamental "peek + remainder" primitive:

| Operation | Signature | Semantics |
|-----------|-----------|-----------|
| `msplit()` | `self → Option<(T, LogicStream<T>)>` | Peek at first result + remainder |
| `mzero()` / `empty()` | `→ LogicStream<T>` | Empty stream (failure) |
| `mplus()` | `self, other → LogicStream<T>` | Unfair concatenation |
| `interleave()` | `self, other → LogicStream<T>` | **Fair** alternating disjunction |
| `fair_conjoin()` | `self, f → LogicStream<U>` | Fair conjunction (>>-) |
| `ifte()` | `self, then, else → LogicStream<U>` | Soft cut (if-then-else) |
| `once()` | `self → LogicStream<T>` | Commit to first result (hard cut) |
| `gnot()` | `self → LogicStream<()>` | Negation as finite failure |

### Fairness Guarantee

`interleave(A, B)` alternates branches from `A` and `B` in round-robin fashion:

```text
For streams A = [a₁, a₂, a₃, ...] and B = [b₁, b₂, b₃, ...]:
  interleave(A, B) = [a₁, b₁, a₂, b₂, a₃, b₃, ...]
```

Both streams are explored infinitely often, preventing starvation when one branch produces results faster.

### Fair Conjunction

`fair_conjoin(f)` applies `f` to each result, then interleaves all resulting streams:

```text
fair_conjoin([a, b, c], f) = interleave(f(a), interleave(f(b), f(c)))
```

This prevents `f(a)` from starving `f(b)` and `f(c)`.

---

## 5. ConstraintTheory Trait

**Source:** `prattail/src/logict.rs:463-495`

`ConstraintTheory` bridges domain-specific constraint solvers with LogicT search:

```rust
pub trait ConstraintTheory: Clone + Debug + Send + Sync + 'static {
    type Constraint;     // Guard predicates
    type Assignment;     // Witness values
    type Store;          // Accumulated constraints

    fn empty_store(&self) -> Self::Store;
    fn propagate(&self, store: &Self::Store, c: &Self::Constraint) -> Option<Self::Store>;
    fn is_consistent(&self, store: &Self::Store) -> bool;
    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment>;
    fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint>;
    fn evaluate(&self, c: &Self::Constraint, assignment: &Self::Assignment) -> bool;
}
```

### Design: Propagation vs. Labeling

The trait separates two concerns:

- **Propagation** (`propagate`): deterministic constraint narrowing. For decidable theories (like unification), propagation alone determines satisfiability.
- **Labeling** (`label`): non-deterministic search choices. For theories requiring search, `label()` produces a `LogicStream` of alternatives explored via LogicT's fair backtracking.

### Implementations

| Theory | Constraint | Store | Labeling? |
|--------|-----------|-------|-----------|
| `UnificationTheory` | `UnificationEquation` | `UnificationStore` | No (decidable) |
| `TheoryAlgebra<T>` | `BooleanAlgebra` predicate | SFA state | No (decidable) |

---

## 6. AC-Matching for Collections

**Source:** `prattail/src/logict.rs` (`multiset_partitions`, `multiset_select`)

Associative-commutative matching decomposes multisets into selected elements and remainders:

```text
ac_match(bag, {x, y, ...rest})
```

This enumerates all ways to select 2 elements from `bag`, binding them to `x` and `y`, with the remainder bound to `rest`.

### Algorithm

`multiset_partitions()` generates all partitions of a multiset into a fixed number of selected elements plus a remainder. For a bag of size n selecting k elements:

- Enumerate all k-combinations (with multiplicity for repeated elements)
- For each combination, compute the remainder by multiset subtraction
- Yield `(selected, remainder)` pairs

### Cost Model

AC-matching has combinatorial cost `C(n, k)` where n is the bag size and k is the number of selected elements. The cost estimate is 25 (fixed) in the predicate dispatch selectivity model, reflecting that AC-matching is expensive but bounded.

### Feature Gate

AC-matching requires the `logict` feature flag.

---

## 7. Evaluation Pipeline

The full pipeline from macro definition to runtime evaluation:

```text
language! {
    guard(forall y in nodes. (reachable(x,y) => safe(y)))
}
           │
           ▼   (Parse)
    BehavioralPred::Quantified {
        quantifier: ForAll,
        var: "y",
        domain: Some("nodes"),
        body: Implies(RelationQuery("reachable",...), RelationQuery("safe",...))
    }
           │
           ▼   (Codegen: to_quantified_formula())
    quote! {
        QuantifiedFormula::ForAll {
            var: "y".into(),
            domain: QuantifiedDomain::Relation("nodes".into()),
            body: Box::new(QuantifiedFormula::Implies(
                Box::new(QuantifiedFormula::Atom { relation: "reachable", ... }),
                Box::new(QuantifiedFormula::Atom { relation: "safe", ... }),
            ))
        }
    }
           │
           ▼   (Runtime: evaluate_quantified())
    For each y in nodes:
        if reachable(x, y):
            if not safe(y):
                return false
    return true
```

---

## References

1. **Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A.** (2005). "Backtracking, Interleaving, and Terminating Monad Transformers." *ICFP 2005*. DOI: 10.1145/1086365.1086390 — The `msplit`-based LogicT design.

2. **Hemann, J. & Friedman, D. P.** (2013). "μKanren: A Minimal Functional Core for Relational Programming." *Scheme Workshop 2013*. — Minimal relational programming core that influenced the ConstraintTheory design.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `macros/src/ast/language.rs` | 227-267 | `BehavioralPred` enum, `Quantifier`, `PredArg` |
| `prattail/src/logict.rs` | 1-550+ | `LogicStream`, `ConstraintTheory`, `QuantifiedFormula`, `evaluate_quantified` |
| `prattail/src/logict.rs` | — | `multiset_partitions`, `multiset_select` (AC-matching) |

---

**Next:** [Pattern Matching Overview](../pattern-matching/overview.md) — unification and matching theory.
