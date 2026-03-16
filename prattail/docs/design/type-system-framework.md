# Pluggable Type System Framework -- Architecture Overview

**Sprint:** Gap 5 / Sprints RT1–RT11
**Status:** IMPLEMENTED
**Feature gates:** `type-system`, `set-theoretic-types`
**Key files:** `type_system.rs`, `pipeline.rs` (refinement analysis), `lint.rs` (RT01–RT06), `macros/src/ast/language.rs` (RefinementTypeDef parser), `macros/src/logic/rules.rs` (refinement codegen)

---

## Why a Pluggable Type System?

PraTTaIL's `ConstraintTheory` trait provides a pluggable framework for
constraint domains (Presburger arithmetic, structural unification, subtype
lattices). However, constraint theories reason about *values* — they answer
"does value `v` satisfy constraint `C`?" The missing piece is reasoning about
*types* — answering "does term `t` have type `T`?" and "is type `S` a subtype
of `T`?"

Different languages need radically different type disciplines:

| Language | Type System | Key Features |
|----------|-------------|--------------|
| Rholang | Structural-behavioral | Connective predicates, no static types |
| MeTTa HE | Gradual, optional | Meta-types, `%Undefined%` matches anything |
| MeTTaTron | Compiled MeTTa | Bloom filters, fixpoint inference, NaN-boxing |
| ML family | Hindley-Milner | Principal types, let-polymorphism |
| Liquid Types | Refinement | `{ x: T \| P(x) }` with SMT-backed predicates |
| CDuce/XDuce | Set-theoretic | `∪/∩/¬` types as tree automata languages |

The `TypeSystem` trait provides a single abstraction that lets all of these plug
into PraTTaIL's pipeline — getting lints, SFA integration, and codegen for free.

---

## Architecture

```
                    ┌──────────────────────────────────────────────────┐
                    │             TypeSystem Trait                       │
                    │                                                    │
                    │  check(env, term, type) → bool                    │
                    │  infer(env, term) → Vec<Type>                     │
                    │  is_subtype(env, sub, sup) → bool                 │
                    │  join(env, a, b) → Option<Type>                   │
                    │  meet(env, a, b) → Option<Type>                   │
                    │  extend(env, var, type) → TypeEnv                 │
                    │  is_inhabited(env, type) → bool                   │
                    │  top() / bottom() → Option<Type>                  │
                    └────────────┬─────────────────────────────────────┘
                                 │
              ┌──────────────────┼──────────────────────┐
              │                  │                      │
    ┌─────────▼──────┐  ┌───────▼────────┐  ┌──────────▼──────────┐
    │ LatticeType     │  │ Refinement     │  │ SetTheoreticType    │
    │ System          │  │ TypeSystem     │  │ System              │
    │                 │  │ <S, T>         │  │                     │
    │ Wraps           │  │ Composes base  │  │ Tree automata       │
    │ LatticeTheory   │  │ TypeSystem +   │  │ Types = states      │
    │                 │  │ Constraint     │  │ Subtype = inclusion  │
    │ Finite subtype  │  │ Theory for     │  │ ∪/∩/¬ types         │
    │ lattice         │  │ { x:T | P(x) } │  │                     │
    └────────┬────────┘  └───────┬────────┘  └──────────┬──────────┘
             │                   │                      │
             └───────────────────┼──────────────────────┘
                                 │
                    ┌────────────▼──────────────────────┐
                    │  TypeSystemAlgebra<S>              │
                    │  (TypeSystem → BooleanAlgebra)     │
                    │                                    │
                    │  Analogous to TheoryAlgebra<T>     │
                    │  for ConstraintTheory              │
                    └────────────┬──────────────────────┘
                                 │
              ┌──────────────────┼──────────────────────┐
              │                  │                      │
    ┌─────────▼──────┐  ┌───────▼────────┐  ┌──────────▼──────────┐
    │ Pipeline        │  │ SFA Dispatch   │  │ Codegen              │
    │ Analysis        │  │ Analysis       │  │                      │
    │                 │  │                │  │ is_refined_* rels    │
    │ RT01–RT06       │  │ Disjointness   │  │ Population rules     │
    │ lints           │  │ Subsumption    │  │ Guard evaluation     │
    │                 │  │ Overlap        │  │ Substitution props   │
    └─────────────────┘  └────────────────┘  └─────────────────────┘
```

---

## TypeSystem Trait

The core abstraction, defined in `prattail/src/type_system.rs`:

```rust
pub trait TypeSystem: Clone + fmt::Debug + Send + Sync + 'static {
    type Type: Clone + fmt::Debug + Eq + Hash + Send + Sync + 'static;
    type TypeEnv: Clone + fmt::Debug + Send + Sync + 'static;
    type Term: Clone + fmt::Debug + Send + Sync + 'static;

    fn empty_env(&self) -> Self::TypeEnv;
    fn check(&self, env: &Self::TypeEnv, term: &Self::Term, ty: &Self::Type) -> bool;
    fn infer(&self, env: &Self::TypeEnv, term: &Self::Term) -> Vec<Self::Type>;
    fn is_subtype(&self, env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool;
    fn join(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;
    fn meet(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;
    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv;
    fn is_inhabited(&self, env: &Self::TypeEnv, ty: &Self::Type) -> bool;
    fn top(&self) -> Option<Self::Type>;
    fn bottom(&self) -> Option<Self::Type>;
}
```

### Design Principles

1. **Nondeterministic inference**: `infer()` returns `Vec<Type>` rather than a
   single type. This supports gradual type systems (MeTTa) where a term may
   have multiple valid types, and union types where each branch contributes.

2. **Environment threading**: `TypeEnv` carries variable-to-type bindings. The
   `extend()` method produces a new environment (functional style), supporting
   scoped type checking without mutation.

3. **Lattice operations**: `join()` (LUB) and `meet()` (GLB) enable type
   compatibility checking and narrowing. They return `None` when no finite
   join/meet exists (e.g., in non-lattice type systems).

4. **Inhabitedness**: `is_inhabited()` answers whether a type has at least one
   value. Critical for refinement types where `{ x: T | false }` is empty.

---

## Implementation 1: LatticeTypeSystem

Wraps the existing `LatticeTheory` (from `lattice_theory.rs`) into a
`TypeSystem`. This is the simplest implementation — a finite subtype lattice
where types are named nodes and subtyping is transitive closure.

- **Type** = `TypeId` (usize index into the lattice)
- **TypeEnv** = `HashMap<String, TypeId>`
- **Term** = `TermExpr` (constructor application or variable)

Key behaviors:
- `is_subtype(S, T)` delegates to `LatticeStore::is_subtype()` via Warshall
  transitive closure
- `join(S, T)` / `meet(S, T)` delegate to `LatticeStore::join()` /
  `LatticeStore::meet()`
- `infer()` matches constructor names against the lattice to determine types
- `top()` / `bottom()` return the lattice extrema (if they exist)

---

## Implementation 2: RefinementTypeSystem\<S, T\>

Composes a base `TypeSystem S` with a `ConstraintTheory T` to produce
refinement types `{ x: S::Type | T::Constraint }`.

- **Type** = `RefType<S::Type, T::Constraint>` (either `Base(ty)` or
  `Refined { base, var, predicate }`)
- **TypeEnv** = base `S::TypeEnv`
- **Term** = base `S::Term`

### Subtyping Rules

```
{ x: S | P(x) } <: { x: T | Q(x) }
  iff  S <: T    (base subtype via TypeSystem S)
  AND  ∀x. P(x) ⟹ Q(x)  (predicate entailment via TheoryAlgebra<T>)
```

Base types lift implicitly: `T` is equivalent to `{ x: T | true }`.

### Key Methods

- **`apply_substitution(ty, var, constraint_value)`**: When a refinement-typed
  variable is substituted with a concrete value, the predicate is specialized.
  Returns `None` if the predicate is provably unsatisfied after substitution.

- **`value_satisfies_refinement(base_ty, constraint)`**: Checks whether a
  concrete value (represented as a constraint) satisfies a refinement predicate.
  Used at Comm-rule fire time.

### Convenience Factories

```rust
RefinementTypeSystem::with_presburger(base, bit_width)  // numeric refinements
RefinementTypeSystem::with_unification(base, sig)       // structural refinements
```

---

## Implementation 3: SetTheoreticTypeSystem

CDuce/XDuce-style types modeled as regular tree languages. Types are sets of
values; subtyping is set inclusion; union, intersection, and negation are
set-theoretic operations.

- **Type** = `SetType` (Atom | Union | Intersection | Negation | Arrow | Top | Bottom)
- **TypeEnv** = `HashMap<String, SetType>`
- **Term** = `SetTerm` (constructor application or variable)

### Core Idea

For a term algebra with finitely many constructors, the set of values of each
type forms a regular tree language. The existing `WeightedTreeAutomaton<BooleanWeight>`
models these directly:

- **States** = types
- **Transitions** = constructor rules: `C(q₁, ..., qₙ) → q`
- **Subtype** = language inclusion: `S <: T` iff `L(A_S) ⊆ L(A_T)` iff
  `L(A_S ∩ ¬A_T) = ∅`

All operations (intersection, complement, emptiness) are decidable for tree
automata, making this a fully decidable type system for algebraic data types.

---

## TypeSystemAlgebra\<S\> Bridge

Bridges `TypeSystem` to `BooleanAlgebra`, analogous to `TheoryAlgebra<T>` for
`ConstraintTheory`. This enables SFA-based analysis of type predicates.

```rust
pub struct TypeSystemAlgebra<S: TypeSystem> {
    pub type_system: S,
    pub env: S::TypeEnv,
}

// TypePred<S>: HasType(ty), Subtype(sub, sup), And/Or/Not, True, False
impl<S: TypeSystem> BooleanAlgebra for TypeSystemAlgebra<S> {
    type Predicate = TypePred<S>;
    fn is_satisfiable(&self, pred: &Self::Predicate) -> bool { ... }
    fn witness(&self, pred: &Self::Predicate) -> Option<S::Type> { ... }
    // ...
}
```

This bridge enables:
- **Satisfiability**: Is a type inhabited? → `is_satisfiable(HasType(ty))`
- **Subsumption**: Is `S <: T`? → `implies(HasType(S), HasType(T))`
- **Overlap**: Do `S` and `T` share values? → `is_satisfiable(And(HasType(S), HasType(T)))`

---

## Pipeline Integration

### Compile-Time Analysis

The PraTTaIL pipeline analyzes refinement types during `language!` macro
expansion via `analyze_refinement_types()` in `pipeline.rs`:

1. Build `LatticeTypeSystem` from the language's category hierarchy
2. For each `RefinementTypeSpec`, classify its predicate domain
3. For Presburger predicates: check satisfiability (RT01) and tautology (RT02)
4. Pairwise analysis: empty intersection (RT03), subsumption (RT04)
5. Decidability tier classification (RT05)
6. Name shadowing detection (RT06)
7. Dispatch analysis: group by base type, detect disjointness/overlap

Results are stored in `RefinementAnalysisResult` and
`RefinementDispatchAnalysis`, consumed by lints and codegen.

### Lints (RT01–RT06)

| ID | Severity | Name | Description |
|----|----------|------|-------------|
| RT01 | Warning | unsatisfiable-refinement-predicate | `{ x: T \| false }` — empty type |
| RT02 | Note | tautological-refinement-predicate | `{ x: T \| true }` — equivalent to base type |
| RT03 | Warning | empty-refinement-intersection | Two refinement types have no shared values |
| RT04 | Note | refinement-subtype-detected | One refinement type is a subtype of another |
| RT05 | Note | refinement-decidability-tier | Predicate's decidability classification (T1–T4) |
| RT06 | Warning | refinement-type-shadows-base | Refinement type name collides with base type |

See `prattail/docs/diagnostics/refinement/` for detailed per-lint documentation.

### Codegen — Runtime Artifacts

The **only runtime artifacts** from the type system framework are generated
Ascent Datalog code:

For each refinement type `PosInt = { x: Int | x > 0 }`:

```rust
// Relation declaration
relation is_refined_posint(Int);

// Population rule
is_refined_posint(x.clone()) <--
    int(x),
    if { *x > 0 };
```

Guard types by predicate kind:

| Predicate Kind | Example | Generated Guard | Runtime Cost |
|----------------|---------|-----------------|--------------|
| Presburger (inline) | `x > 0` | `if { *var > 0 }` | O(1) |
| Behavioral (relation) | `safe(x)` | `if { ascent_prog.relation.contains(...) }` | O(1) hash |
| Behavioral (quantified) | `∀y. P(x,y)` | `if { evaluate_quantified(...) }` | O(domain_size) |
| Compound (And/Or/Not) | `x > 0 /\ safe(x)` | `if { expr1 && expr2 }` | Sum of components |

### Substitution Propagation

When a Comm rule fires with a refinement-typed variable, the generated code
checks the concrete value against the refinement predicate. This is wired
via `generate_refinement_join_clause()` and
`generate_refinement_membership_check()` in `macros/src/logic/rules.rs`.

### Dispatch Analysis

When multiple refinement types refine the same base type, the pipeline
performs pairwise overlap analysis via `analyze_refinement_dispatch()` in
`type_system.rs`. This detects:

- **Disjoint pairs**: complement predicates (e.g., `x > 0` vs `x <= 0`)
- **Subtype pairs**: one predicate entails the other
- **Overlapping pairs**: predicates may both be satisfied

Results inform dispatch safety: disjoint refinements can be dispatched without
ambiguity; overlapping refinements require priority ordering or explicit
disambiguation.

---

## Compile-Time vs Runtime Classification

All `TypeSystem` trait implementations and the `TypeSystemAlgebra` bridge
execute **exclusively at compile time** during `language!` macro expansion.
They are not present in the generated binary.

| Component | Phase | Notes |
|-----------|-------|-------|
| `TypeSystem` trait + all impls | Compile-time | Analysis infrastructure |
| `TypeSystemAlgebra<S>` bridge | Compile-time | BooleanAlgebra adapter |
| `RefinementDispatchAnalysis` | Compile-time | Pairwise overlap analysis |
| Pipeline lints RT01–RT06 | Compile-time | Diagnostic messages |
| `is_refined_*` relations | **Codegen → Runtime** | One relation per refinement type |
| Population rules | **Codegen → Runtime** | One rule per refinement type |
| Guard evaluation functions | **Codegen → Runtime** | Inline arithmetic / relation lookup |

---

## Feature Gates

```toml
type-system = ["logict", "lattice-theory"]
set-theoretic-types = ["type-system", "tree-automata"]
```

Both are included in the `predicated-types` and `full-analysis` convenience
groups.

---

## References

- Rondon, P., Kawaguchi, M., & Jhala, R. (2008). "Liquid Types." PLDI 2008.
- Freeman, T. & Pfenning, F. (1991). "Refinement Types for ML." PLDI 1991.
- Frisch, A., Castagna, G., & Benzaken, V. (2008). "Semantic subtyping." JACM 55(4).
- Castagna, G. (2018). CDuce/XDuce set-theoretic type systems.
- Xi, H. & Pfenning, F. (1999). "Dependent Types in Practical Programming." POPL 1999.
- Comon, H. et al. (2007). "Tree Automata Techniques and Applications." (TATA).

---

## Related Documentation

- [Constraint Theory Suite](constraint-theories/README.md) — analogous framework for constraint domains
- [Symbolic Automata](symbolic-automata.md) — BooleanAlgebra trait and SFA operations
- [Diagnostics: Refinement](../diagnostics/refinement/) — RT01–RT06 lint documentation
