# Constraint Theory Suite -- Architecture Overview

**Sprint:** Gap 1 / Sprint 12
**Status:** IMPLEMENTED
**Feature gates:** `logict`, `presburger`, `unification`, `lattice-theory`
**Key files:** `logict.rs`, `presburger.rs`, `unification.rs`, `lattice_theory.rs`, `symbolic.rs` (ProductAlgebra)

---

## Why Constraint Theories?

PraTTaIL's symbolic automata framework provides the `BooleanAlgebra` trait -- a decision procedure interface that enables all standard automata algorithms (emptiness, intersection, complement, determinization, equivalence) to work over infinite domains without enumerating every element. The four built-in algebras -- `IntervalAlgebra` (single-variable integer ranges), `CharClassAlgebra` (Unicode characters), `KatBooleanAlgebra` (propositional atoms), and `DispatchAlgebra` (module signatures) -- cover many common cases but leave three critical domains uncovered:

1. **Multi-variable linear arithmetic** -- guards like `x + y <= 100` that relate multiple integer variables cannot be expressed in `IntervalAlgebra`, which handles only one variable at a time.

2. **Structural pattern matching** -- MeTTa and Rholang patterns involve constructor decomposition, variable binding, and occurs checking. No existing algebra captures unification constraints.

3. **Type hierarchies** -- subtype lattices with join/meet operations are needed for type compatibility checking in languages with subtype polymorphism. `IntervalAlgebra` cannot express `Nat <= Number <= Any`.

The Constraint Theory Suite fills these gaps with a unified architecture that reuses the existing `BooleanAlgebra` and `SymbolicAutomaton` infrastructure rather than introducing an external SMT solver dependency.

---

## Architecture

```
                         ┌───────────────────────────────────────────┐
                         │          BooleanAlgebra trait              │
                         │   (is_satisfiable, witness, evaluate,     │
                         │    and, or, not)                           │
                         └──────────┬────────────────┬───────────────┘
                                    │                │
                     ┌──────────────┴────┐    ┌──────┴──────────────┐
                     │  Direct impls     │    │  TheoryAlgebra<T>   │
                     │  (fast path)      │    │  bridge             │
                     ├──────────────────┤    ├─────────────────────┤
                     │ IntervalAlgebra  │    │ Wraps any           │
                     │ CharClassAlgebra │    │ ConstraintTheory    │
                     │ KatBooleanAlg.   │    │ into BooleanAlgebra │
                     │ DispatchAlgebra  │    │ via propagation +   │
                     │ PresburgerAlg.   │◄───┤ LogicT search       │
                     └──────────────────┘    └──────┬──────────────┘
                                                    │
                                   ┌────────────────┼─────────────────┐
                                   │                │                 │
                         ┌─────────┴──┐  ┌──────────┴───┐  ┌─────────┴────┐
                         │ Presburger │  │ Unification  │  │ Lattice      │
                         │ Theory     │  │ Theory       │  │ Theory       │
                         │            │  │              │  │              │
                         │ label():   │  │ label():     │  │ label():     │
                         │ empty()    │  │ CustomMatch  │  │ empty()      │
                         │ (decidable)│  │ alternatives │  │ (decidable)  │
                         └────────────┘  └──────────────┘  └──────────────┘

              ProductAlgebra<A, B>: composes any two BooleanAlgebra instances
              LogicStream<T>:       fair backtracking search (Kiselyov et al.)
```

The architecture has two complementary paths for connecting constraint domains to symbolic automata:

**Direct path (fast).** A domain implements `BooleanAlgebra` directly, providing its own satisfiability decision procedure. `PresburgerAlgebra` takes this path, using NFA-based satisfiability (Buchi's construction + emptiness check) for maximal performance.

**Theory bridge (generic).** A domain implements `ConstraintTheory` -- a simpler trait with `propagate`, `label`, `witness`, and `evaluate` -- and `TheoryAlgebra<T>` automatically lifts it to `BooleanAlgebra`. For decidable theories (where `label()` returns `empty()`), the bridge uses propagation alone. For non-decidable theories, it drives LogicT's fair backtracking search.

---

## Component Summary

| Component | Feature Gate | Module | Purpose | Decidable? |
|-----------|-------------|--------|---------|------------|
| **LogicT** | `logict` | `logict.rs` | Fair backtracking monad: `msplit`, `interleave`, `fair_conjoin`, `ifte`, `once`, `gnot` | N/A (infrastructure) |
| **ConstraintTheory** | `logict` | `logict.rs` | Pluggable constraint domain trait: `propagate`, `label`, `witness`, `evaluate` | N/A (trait) |
| **TheoryAlgebra** | `logict` + `symbolic-automata` | `logict.rs` | Bridge: `ConstraintTheory` to `BooleanAlgebra` | N/A (adapter) |
| **PresburgerTheory** | `presburger` | `presburger.rs` | Multi-variable linear integer arithmetic via NFA construction | Yes |
| **PresburgerAlgebra** | `presburger` + `symbolic-automata` | `presburger.rs` | Direct `BooleanAlgebra` fast path (NFA emptiness check) | Yes |
| **UnificationTheory** | `unification` | `unification.rs` | Structural unification (Martelli-Montanari), pattern matching | Yes |
| **LatticeTheory** | `lattice-theory` | `lattice_theory.rs` | Subtype lattice: join/meet, Warshall closure, exhaustiveness | Yes |
| **ProductAlgebra** | (always-on) | `symbolic.rs` | Compose two `BooleanAlgebra` instances over independent domains | Derived |

---

## Relationship to Existing Algebras

The Constraint Theory Suite integrates with, rather than replaces, the existing Boolean algebras:

| Algebra | Domain | Variables | Integration |
|---------|--------|-----------|-------------|
| `IntervalAlgebra` | `i64` ranges in `[min, max)` | 1 | Presburger delegates single-variable cases |
| `CharClassAlgebra` | Unicode `char` ranges | 1 | Independent; composable via `ProductAlgebra` |
| `KatBooleanAlgebra` | `HashMap<String, bool>` | finite propositional | Independent |
| `DispatchAlgebra` | `PredicateSignature` | module bitfield | Independent; `M12`/`M13`/`M14` bits route to constraint theories |
| `PresburgerAlgebra` | `IntAssignment` | k (multi-var) | *New* -- NFA-based decision for linear arithmetic |
| `TheoryAlgebra<Unif>` | `Substitution` | structural | *New* -- first-order syntactic unification |
| `TheoryAlgebra<Lat>` | `TypeAssignment` | finite lattice | *New* -- subtype join/meet |
| `ProductAlgebra<A,B>` | `(A::Domain, B::Domain)` | composed | *New* -- combine independent domains |

---

## Feature Gate Dependency Diagram

```
                    ┌──────────────────┐
                    │      logict      │
                    │  (LogicT monad,  │
                    │  ConstraintTheory│
                    │  trait)          │
                    └──┬──────┬──────┬─┘
                       │      │      │
            ┌──────────┘      │      └──────────┐
            ▼                 ▼                  ▼
   ┌────────────────┐ ┌─────────────┐  ┌─────────────────┐
   │  presburger    │ │ unification │  │ lattice-theory   │
   │  (Presburger   │ │ (Martelli-  │  │ (Warshall        │
   │  NFA + Theory) │ │  Montanari) │  │  closure, LUB/   │
   └────────┬───────┘ └─────────────┘  │  GLB)            │
            │                          └──────────────────┘
            │
            ├── (+ symbolic-automata) ──→ PresburgerAlgebra
            │
            └── (via TheoryAlgebra)  ──→ BooleanAlgebra impl

   ┌────────────────────────────────────┐
   │  predicated-types (convenience)   │
   │  = symbolic-automata + weighted-  │
   │    mso + parity-tree-automata +   │
   │    register-automata + multi-tape │
   │    + multiset-automata + two-way  │
   │    + presburger + unification +   │
   │    lattice-theory                 │
   └────────────────────────────────────┘
```

The `logict` feature is the root dependency. Each constraint theory depends on `logict` for the `ConstraintTheory` trait and `LogicStream` type. The `symbolic-automata` feature is needed only for the `BooleanAlgebra` bridge (`TheoryAlgebra`) and the direct `PresburgerAlgebra` -- the theories themselves work without it.

---

## Predicate Dispatch Integration

The predicate dispatch automaton (`predicate_dispatch.rs`) routes guard predicates to the appropriate constraint theories via three signature bits:

| Bit | Module | Theory | Trigger |
|-----|--------|--------|---------|
| 11 | M12 | Presburger | Linear arithmetic in guards (`x + y <= 100`) |
| 12 | M13 | Unification | Structural patterns (`App(f, Var(x))`) |
| 13 | M14 | Lattice | Subtype constraints (`Nat <= Number`) |

When `classify_grammar()` detects guards requiring these theories, it sets the corresponding bits in the `PredicateSignature`, causing the pipeline to activate the appropriate theory modules.

---

## Document Index

| Document | Content |
|----------|---------|
| [LogicT Framework](logict-framework.md) | Fair backtracking search, `msplit`, `ConstraintTheory` trait, `TheoryAlgebra` bridge |
| [Presburger Algebra](presburger-algebra.md) | Buchi's theorem, NFA construction, Boolean operations, dual implementation |
| [Unification Theory](unification-theory.md) | Martelli-Montanari algorithm, occurs check, subsumption, MeTTa/Rholang examples |
| [Lattice Theory](lattice-theory.md) | Subtype lattices, Warshall closure, join/meet, exhaustiveness |
| [Product Algebra](product-algebra.md) | Composing independent constraint domains |
| [Theories Proposal](theories-proposal.md) | Future `language! { theories { ... } }` syntax (design proposal) |
| [PathMap Integration](pathmap-integration.md) | PathMap-backed constraint stores, term encoding |

---

## Why Automata Instead of SMT

| Criterion | SMT (Z3/CVC5) | Constraint Theory Suite |
|-----------|---------------|------------------------|
| External deps | z3-sys (~1.5GB), platform build complexity | Zero -- pure Rust |
| Deployment | Shared lib, platform-specific | Cross-platform, WASM-compatible |
| Performance | FFI call per check-sat, ~1ms startup per context | In-process, cacheable automata |
| Formal basis | Solver completeness as black-box | Provably decidable (Buchi 1960) |
| Integration | SMT-LIB2 serialization + model parsing | Direct `BooleanAlgebra` impl |
| Scope match | Over-powered (arrays, UF, bitvectors) | Exact fit for guard predicates |
| Extensibility | Fixed theory set, FFI boundary | Open `ConstraintTheory` trait |

---

## Citations

- Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005). "Backtracking, Interleaving, and Terminating Monad Transformers." *ICFP 2005*. DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
- Buchi, J. R. (1960). "Weak second-order arithmetic and finite automata." *Zeitschrift fur mathematische Logik und Grundlagen der Mathematik*, 6, 66--92.
- Martelli, A. & Montanari, U. (1982). "An Efficient Unification Algorithm." *ACM TOPLAS*, 4(2), 258--282. DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)
- Warshall, S. (1962). "A Theorem on Boolean Matrices." *JACM*, 9(1), 11--12.
- D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and transducers." *CAV 2017*.
