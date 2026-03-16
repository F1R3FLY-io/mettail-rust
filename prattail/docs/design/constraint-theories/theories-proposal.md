# Theories Proposal -- Pluggable Constraint Theories in the `language!` Macro

**Status:** DESIGN PROPOSAL -- not yet implemented in `language!`
**Depends on:** `logict`, `symbolic-automata`, `predicate-dispatch`

---

## 1. Intuition: Why Language Spec Authors Need Pluggable Theories

PraTTaIL's constraint theory suite provides three built-in theories --
Presburger arithmetic, structural unification, and subtype lattices -- each
implementing the `ConstraintTheory` trait from `logict.rs`. These theories
integrate with the symbolic automata framework via `TheoryAlgebra<T>`, which
lifts any `ConstraintTheory` to a `BooleanAlgebra` for guard analysis, lint
diagnostics, and codegen.

Today, wiring a constraint theory into the pipeline requires:

1. Implementing `ConstraintTheory` in a Rust module.
2. Registering the module in `lib.rs` behind a feature gate.
3. Adding signature bits in `predicate_dispatch.rs` (`PredicateSignature`).
4. Manually threading the theory through `classify_grammar()` and `extract_features()`.
5. Updating lint dispatch tables to route theory-specific diagnostics.

This five-step process couples domain-specific constraint knowledge to
PraTTaIL's internals. A language spec author who needs resource counting,
session types, linear capabilities, or region constraints must modify
PraTTaIL source code rather than declaring their needs in the grammar.

The `theories { }` block eliminates steps 3--5 by letting the `language!`
macro handle theory registration, pipeline wiring, and lint integration
automatically. The spec author writes their `ConstraintTheory` impl (step 1),
declares it in the grammar (step 2), and the macro does the rest.

### Motivating Examples

**Resource counting.** A language with bounded-resource semantics needs to
verify that every process respects a fuel budget. The constraint `cost(P) <= 100`
involves domain-specific cost analysis that no built-in theory covers.

**Session types.** A language with session-typed channels requires duality
checking (`!A.S` dual to `?A.S`), which is a structural constraint beyond
unification's scope (it involves polarity inversion, not just pattern matching).

**Linear capabilities.** Rholang's bundles carry read/write capabilities that
must be tracked linearly -- each capability is consumed exactly once. This
requires multiplicative (non-idempotent) constraint propagation, which the
existing additive theories do not support.

In each case, the domain expert knows how to write `propagate`, `label`,
`witness`, and `evaluate`. What they should not need to know is how PraTTaIL's
pipeline threads constraint results through 14 analysis phases.

---

## 2. Three-Layer Architecture

```
╔═══════════════════════════════════════════════════════════════════════╗
║                                                                       ║
║  Layer 3: Pipeline Wiring (automatic)                                 ║
║                                                                       ║
║    language! macro expansion                                          ║
║         │                                                             ║
║         ▼                                                             ║
║    classify_grammar()                                                 ║
║         │  inspect guard predicates, set PredicateSignature bits      ║
║         ▼                                                             ║
║    extract_features()                                                 ║
║         │  map each guard to its declared theory                      ║
║         ▼                                                             ║
║    TheoryAlgebra<T>::is_satisfiable()                                 ║
║         │  BooleanAlgebra bridge (automatic)                          ║
║         ▼                                                             ║
║    lint analysis ──▶ codegen                                          ║
║                                                                       ║
╠═══════════════════════════════════════════════════════════════════════╣
║                                                                       ║
║  Layer 2: language! Declaration                                       ║
║                                                                       ║
║    language! {                                                        ║
║        theories {                                                     ║
║            arithmetic: PresburgerAlgebra,                             ║
║            patterns:   UnificationTheory,                             ║
║            types:      LatticeTheory,                                 ║
║            resources:  ResourceTheory,     // user-defined            ║
║        }                                                              ║
║    }                                                                  ║
║                                                                       ║
╠═══════════════════════════════════════════════════════════════════════╣
║                                                                       ║
║  Layer 1: Rust Implementation                                         ║
║                                                                       ║
║    impl ConstraintTheory for ResourceTheory {                         ║
║        type Constraint = ResourceConstraint;                          ║
║        type Assignment = ResourceAssignment;                          ║
║        type Store      = ResourceStore;                               ║
║                                                                       ║
║        fn propagate(..) -> Option<Store> { .. }                       ║
║        fn label(..)     -> LogicStream<Constraint> { .. }             ║
║        fn witness(..)   -> Option<Assignment> { .. }                  ║
║        fn evaluate(..)  -> bool { .. }                                ║
║    }                                                                  ║
║                                                                       ║
╚═══════════════════════════════════════════════════════════════════════╝
```

### Layer 1: Rust Implementation

The spec author implements `ConstraintTheory` (defined in `logict.rs`) for
their domain. No marker traits, no registration macros, no FFI. The same trait
used by the built-in theories (PresburgerTheory, UnificationTheory,
LatticeTheory) is the only requirement:

```rust
use mettail_prattail::logict::{ConstraintTheory, LogicStream};

pub struct ResourceTheory {
    pub max_budget: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ResourceConstraint {
    CostAtMost(String, u64),    // cost(name) <= bound
    CostAtLeast(String, u64),   // cost(name) >= bound
}

#[derive(Clone, Debug)]
pub struct ResourceStore {
    upper_bounds: HashMap<String, u64>,
    lower_bounds: HashMap<String, u64>,
}

#[derive(Clone, Debug)]
pub struct ResourceAssignment {
    costs: HashMap<String, u64>,
}

impl ConstraintTheory for ResourceTheory {
    type Constraint = ResourceConstraint;
    type Assignment = ResourceAssignment;
    type Store = ResourceStore;

    fn propagate(&self, store: &Self::Store, c: &Self::Constraint)
        -> Option<Self::Store>
    {
        let mut new_store = store.clone();
        match c {
            ResourceConstraint::CostAtMost(name, bound) => {
                let entry = new_store.upper_bounds
                    .entry(name.clone()).or_insert(self.max_budget);
                *entry = (*entry).min(*bound);
            }
            ResourceConstraint::CostAtLeast(name, bound) => {
                let entry = new_store.lower_bounds
                    .entry(name.clone()).or_insert(0);
                *entry = (*entry).max(*bound);
            }
        }
        // Consistency: forall name, lower <= upper
        for (name, lower) in &new_store.lower_bounds {
            if let Some(&upper) = new_store.upper_bounds.get(name) {
                if *lower > upper {
                    return None; // inconsistent
                }
            }
        }
        Some(new_store)
    }

    fn is_consistent(&self, store: &Self::Store) -> bool {
        store.lower_bounds.iter().all(|(name, lower)| {
            store.upper_bounds.get(name).map_or(true, |upper| lower <= upper)
        })
    }

    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment> {
        if !self.is_consistent(store) { return None; }
        let costs = store.upper_bounds.keys()
            .chain(store.lower_bounds.keys())
            .map(|name| {
                let lower = store.lower_bounds.get(name).copied().unwrap_or(0);
                (name.clone(), lower) // pick smallest feasible cost
            })
            .collect();
        Some(ResourceAssignment { costs })
    }

    fn label(&self, _store: &Self::Store) -> LogicStream<Self::Constraint> {
        LogicStream::empty() // decidable: interval propagation suffices
    }

    fn evaluate(&self, c: &Self::Constraint, a: &Self::Assignment) -> bool {
        match c {
            ResourceConstraint::CostAtMost(name, bound) =>
                a.costs.get(name).map_or(true, |cost| *cost <= *bound),
            ResourceConstraint::CostAtLeast(name, bound) =>
                a.costs.get(name).map_or(false, |cost| *cost >= *bound),
        }
    }
}
```

By implementing `ConstraintTheory`, the author automatically gains
`BooleanAlgebra` (via `TheoryAlgebra<ResourceTheory>`) and therefore
`SymbolicAutomaton` integration, minterm computation, and lint analysis -- all
without writing a single line of automata code.

### Layer 2: language! Declaration

The `language!` macro gains a `theories { }` block. Each entry maps a
user-visible theory name (used in error messages and guard annotations) to a
Rust type path implementing `ConstraintTheory`:

```rust
language! {
    name: RholangLike,
    types { Proc, Name, Bundle },

    theories {
        arithmetic: PresburgerAlgebra,
        patterns:   UnificationTheory,
        types:      LatticeTheory,
        resources:  ResourceTheory,
    },

    rules {
        // guards reference theories by name or via type-directed dispatch
        Proc => {
            resource_bounded: "cost" "(" Proc ")" "<=" Num
                => guard(resources: cost_at_most($1, $4)),
        },
    },

    tokens { /* ... */ },
}
```

### Layer 3: Automatic Pipeline Wiring

The macro expands `theories { }` into:

1. A `Vec<TheoryRegistration>` in the generated `LanguageDef` struct.
2. Theory initialization code that constructs each `TheoryAlgebra<T>`.
3. Guard dispatch logic mapping guard predicate AST nodes to theories.
4. Lint message formatting keyed by theory name.

The pipeline phases then operate generically over registered theories:

```
┌──────────────────────┐      ┌───────────────────────────┐
│  language! expansion │      │  Vec<TheoryRegistration>  │
│  (proc-macro time)   │─────▶│  per-theory metadata      │
└──────────────────────┘      └──────────┬────────────────┘
                                         │
        ┌────────────────────────────────┤
        ▼                                ▼
┌───────────────────┐          ┌────────────────────────┐
│ classify_grammar()│          │ extract_features()     │
│ set signature bits│          │ guard → theory mapping  │
│ per theory        │          │                        │
└────────┬──────────┘          └──────────┬─────────────┘
         │                                │
         └──────────┬─────────────────────┘
                    ▼
         ┌──────────────────────────┐
         │ TheoryAlgebra<T> per     │
         │ registered theory        │
         │                          │
         │ is_satisfiable(guard)    │
         │ witness(guard)           │
         │ overlap/subsumption      │
         └──────────┬───────────────┘
                    │
           ┌────────┼────────┐
           ▼        ▼        ▼
        ┌──────┐ ┌──────┐ ┌──────┐
        │ Lint │ │WFST  │ │Code  │
        │ diag │ │dead  │ │gen   │
        │      │ │guard │ │      │
        └──────┘ └──────┘ └──────┘
```

---

## 3. TheoryRegistration Type

```rust
/// Metadata for a constraint theory declared in a `theories { }` block.
///
/// Created by the `language!` macro during expansion and stored in the
/// generated `LanguageDef` struct. The pipeline reads these registrations
/// to wire theories into symbolic analysis, lint diagnostics, and codegen.
pub struct TheoryRegistration {
    /// User-visible name for this theory (from the `theories { }` block).
    ///
    /// Used in error messages, lint diagnostics, and guard annotations.
    /// Example: `"arithmetic"`, `"patterns"`, `"resources"`.
    pub name: Ident,

    /// Rust type path implementing `ConstraintTheory`.
    ///
    /// The macro verifies at expansion time that this path resolves to a type
    /// implementing `ConstraintTheory`. Example: `PresburgerAlgebra`,
    /// `crate::theories::ResourceTheory`.
    pub theory_type: Path,

    /// Optional configuration attributes from the declaration.
    ///
    /// Supports key-value pairs for theory-specific configuration:
    /// - `search_bound`: maximum labeling steps for non-decidable theories
    /// - `decidable`: explicit decidability annotation (overrides heuristic)
    /// - `priority`: dispatch priority when multiple theories match a guard
    ///
    /// Example: `resources: ResourceTheory { search_bound = 100, decidable = true }`
    pub options: HashMap<String, AttributeValue>,
}

/// A typed attribute value from a theory declaration.
#[derive(Clone, Debug)]
pub enum AttributeValue {
    /// Boolean flag: `decidable = true`
    Bool(bool),
    /// Integer parameter: `search_bound = 100`
    Int(i64),
    /// String parameter: `category = "linear"`
    Str(String),
    /// Float parameter: `weight = 0.8`
    Float(f64),
}
```

The `name` field is an `Ident` (from `proc_macro2`) rather than a `String`
because the macro needs span information for error reporting. The `theory_type`
is a `Path` for the same reason -- it carries source location data that enables
"theory `ResourceTheory` not found" diagnostics pointing to the exact location
in the `language!` invocation.

### Relationship to PredicateSignature

The existing `PredicateSignature` bitfield (14 bits for modules M1--M14) is
extended with dynamically allocated bits for user-defined theories. Bits 0--13
remain fixed (M1--M14). Bits 14+ are assigned at macro expansion time based on
the `theories { }` declarations:

```
Bits 0--13:  Fixed modules (M1 Symbolic ... M14 Lattice)
Bits 14+:    User-defined theories (allocated in declaration order)

Example for RholangLike with 4 theories:
  Bit 11: M12 → arithmetic (PresburgerAlgebra)     [built-in]
  Bit 12: M13 → patterns   (UnificationTheory)     [built-in]
  Bit 13: M14 → types      (LatticeTheory)         [built-in]
  Bit 14:      → resources  (ResourceTheory)        [user-defined]
```

The `PredicateSignature` type widens from `u16` to `u32` to accommodate up to
18 user-defined theories (bits 14--31), which is more than sufficient for any
practical grammar.

---

## 4. Pipeline Wiring Detail

### 4.1 classify_grammar: Theory Feature Extraction

```
Input:   Grammar rules with guard predicates + Vec<TheoryRegistration>
Output:  Per-category PredicateSignature with theory bits set

for each rule R with guard predicates:
    for each guard predicate G in R:
        for each registered theory T in registrations:
            if G.theory_annotation == T.name:
                // Explicit annotation: guard(arithmetic: x + y <= 100)
                signature.set(T.signature_bit)
            else if T.matches_heuristic(G):
                // Fallback: keyword-based matching
                signature.set(T.signature_bit)
```

Explicit annotation (via `guard(theory_name: ...)` syntax) is preferred
over heuristic matching. Heuristic matching is retained for backward
compatibility with grammars that predate the `theories { }` block.

### 4.2 extract_features: Guard-to-Theory Mapping

```
Input:   Guard predicate AST node + Vec<TheoryRegistration>
Output:  (theory_name, TheoryAlgebra<T>)

for each guard AST node G:
    T = lookup_theory(G.theory_annotation, registrations)
    algebra = TheoryAlgebra::new(T.instance, T.search_bound)
    return (T.name, algebra)
```

The `TheoryAlgebra<T>` wraps the user's `ConstraintTheory` implementation
and provides `BooleanAlgebra::is_satisfiable`, `witness`, `evaluate`, etc.
This is the same bridge used by the built-in theories.

### 4.3 Lint Integration

Existing lint codes extend with theory-keyed messages. The theory name from
`TheoryRegistration` is interpolated into diagnostic messages:

| Lint   | Scope     | Condition             | Message Template                                   |
|--------|-----------|-----------------------|----------------------------------------------------|
| SYM01  | Any       | Guard unsatisfiable   | "Guard `{guard}` via theory `{name}` is always false" |
| SYM02  | Any       | Guards overlap        | "Guards `{g1}` and `{g2}` overlap in `{name}`"    |
| SYM03  | Any       | Guard subsumed        | "Guard `{g1}` subsumed by `{g2}` in `{name}`"     |
| LA01   | Presburger| Dead linear guard     | "Arithmetic guard eliminable"                      |
| UN01   | Unification| Occurs-check / clash | "Pattern never matches"                            |
| LT01   | Lattice   | Exhaustiveness gap    | "Subtype `{T}` not covered"                       |
| USR01  | User      | Domain-specific       | "Theory `{name}`: {theory.diagnostic_message()}"   |

User-defined theories can optionally implement a `diagnostic_message()` method
on their `ConstraintTheory` impl to provide domain-specific lint text.

---

## 5. Example Language Specs

### 5.1 RholangLike: 4 Theories

```rust
language! {
    name: RholangLike,
    types { Proc, Name, Bundle },

    theories {
        // Multi-variable linear arithmetic for guard predicates
        arithmetic: PresburgerAlgebra { bit_width = 16 },

        // Structural pattern matching for quoted process decomposition
        patterns: UnificationTheory,

        // Subtype hierarchy for bundle capabilities
        types: LatticeTheory::new(
            // Universe: Read, Write, ReadWrite, Opaque
            vec![0, 1, 2, 3],
            HashMap::from([(0, "Read"), (1, "Write"), (2, "ReadWrite"), (3, "Opaque")]),
        ),

        // Linear resource tracking for channels
        linearity: LinearityTheory { multiplicity = 1 },
    },

    tokens { /* ... */ },
    rules  { /* ... */ },
}
```

### 5.2 MeTTaLike: 3 Theories

```rust
language! {
    name: MeTTaLike,
    types { Atom, Expr, Type },

    theories {
        // Structural unification for (= pattern target) matching
        matching: UnificationTheory,

        // Subtype lattice for (: x Type) and (<: Sub Super) declarations
        types: LatticeTheory,

        // Arithmetic for bounded quantifiers: exists_{k=N}
        bounds: PresburgerAlgebra { bit_width = 8 },
    },

    tokens { /* ... */ },
    rules  { /* ... */ },
}
```

### 5.3 SessionTyped: Custom Theories

```rust
language! {
    name: SessionTyped,
    types { Proc, Channel, Session },

    theories {
        // Type hierarchy for session protocol states
        sessions: LatticeTheory::new(
            vec![0, 1, 2, 3, 4],
            HashMap::from([
                (0, "Send"), (1, "Recv"), (2, "Choice"),
                (3, "Select"), (4, "End"),
            ]),
        ),

        // Session duality checking (custom theory)
        duality: DualityTheory,

        // Linear channel usage (each channel consumed exactly once)
        linearity: LinearityTheory { multiplicity = 1 },
    },

    tokens { /* ... */ },
    rules  { /* ... */ },
}
```

---

## 6. LogicT label() Patterns

The `label()` method on `ConstraintTheory` determines whether the theory
requires search (non-decidable) or can resolve constraints by propagation
alone (decidable). The following table summarizes the patterns for both
built-in and expected user-defined theories:

| Theory             | Decidable? | `label()` Return               | Rationale                                                |
|--------------------|------------|----------------------------------|----------------------------------------------------------|
| `PresburgerTheory` | Yes        | `LogicStream::empty()`           | NFA-based satisfiability; no search needed               |
| `LatticeTheory`    | Yes        | `LogicStream::empty()`           | Finite universe; Warshall closure resolves all queries    |
| `UnificationTheory`| Yes (base) | `LogicStream::empty()`           | Martelli-Montanari is deterministic                      |
| `UnificationTheory`| Partial    | `LogicStream::from_iter(alts)`   | Extended: `CustomMatch` enumerates alternative patterns  |
| `LinearityTheory`  | Yes        | `LogicStream::empty()`           | Multiplicity count is decidable by propagation           |
| `DualityTheory`    | Yes        | `LogicStream::empty()`           | Polarity inversion is a decidable structural check       |
| `ResourceTheory`   | Yes        | `LogicStream::empty()`           | Interval-based cost bounds; propagation suffices         |
| `TypeInference`    | No         | `LogicStream::from_iter(vars)`   | Polymorphic instantiation may require variable choice    |
| `RegionTheory`     | No         | `LogicStream::from_iter(regions)`| Region assignment requires exploring allocation choices  |

### Code Examples for label() Patterns

**Decidable theory (no search):**

```rust
fn label(&self, _store: &Self::Store) -> LogicStream<Self::Constraint> {
    LogicStream::empty()
}
```

**Non-decidable theory (bounded search):**

```rust
fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint> {
    // Enumerate unresolved type variables as labeling choices
    let unresolved: Vec<_> = store.unresolved_variables()
        .flat_map(|var| {
            store.candidate_types(var)
                .map(move |ty| TypeConstraint::Assign(var, ty))
        })
        .collect();
    LogicStream::from_iter(unresolved)
}
```

**Non-decidable theory with fair interleaving:**

```rust
fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint> {
    let var_streams: Vec<LogicStream<RegionConstraint>> = store
        .unassigned_regions()
        .map(|region| {
            let candidates = store.candidate_allocations(region);
            LogicStream::from_iter(
                candidates.map(move |alloc| RegionConstraint::Allocate(region, alloc))
            )
        })
        .collect();

    // Interleave all region assignment streams fairly
    var_streams.into_iter().fold(
        LogicStream::empty(),
        |acc, stream| acc.interleave(stream),
    )
}
```

---

## 7. Interaction with Existing Infrastructure

The `theories { }` proposal does **not** modify:

- The `BooleanAlgebra` trait (unchanged).
- The `ConstraintTheory` trait (unchanged).
- The `TheoryAlgebra<T>` bridge (unchanged).
- Existing Boolean algebra implementations (IntervalAlgebra, CharClassAlgebra, etc.).
- The `ProductAlgebra` combinator (unchanged).

It **adds**:

- `TheoryRegistration` struct and `AttributeValue` enum for pipeline metadata.
- `theories { }` block parsing in the `language!` macro proc-macro expansion.
- Automatic `TheoryAlgebra<T>` instantiation in the pipeline.
- Dynamic `PredicateSignature` bit allocation for user-defined theories.
- Theory-keyed lint message formatting.

The proposal is **backward-compatible**: languages without `theories { }` blocks
continue to work exactly as before. The built-in theories remain accessible via
their feature gates (`presburger`, `unification`, `lattice-theory`) without
requiring a `theories { }` declaration -- the declaration is syntactic sugar for
automatic pipeline wiring.

---

## 8. Open Design Questions

1. **Theory composition.** Should the `theories { }` block support explicit
   `ProductAlgebra` declarations for cross-domain guards? Example:
   `combined: ProductAlgebra<arithmetic, resources>`. Alternatively, the
   pipeline could infer composition automatically when a guard references
   multiple theories. The latter is simpler for the spec author but requires
   a composition heuristic.

2. **Guard syntax.** How does a guard predicate reference a specific theory?
   Three options:
   - **Explicit annotation:** `guard(arithmetic: x + y <= 100)` -- most
     precise, most verbose.
   - **Implicit keyword matching:** the pipeline infers the theory from
     keywords (`+`, `<=` suggest arithmetic). Error-prone for overlapping
     domains.
   - **Type-directed dispatch:** the guard's AST type determines the theory.
     Requires typed guard predicates, which adds parsing complexity.

   The recommendation is explicit annotation with implicit fallback.

3. **Runtime codegen.** For non-decidable theories where `label()` produces a
   non-empty `LogicStream`, what code does the codegen emit?
   - **Inline LogicT search:** emit the `VecDeque`-based search loop directly.
     Simple but generates large code for complex theories.
   - **Runtime theory interpreter:** emit a call to a generic solver that
     accepts a `Box<dyn ConstraintTheory>`. Flexible but incurs dynamic
     dispatch overhead.
   - **Compile to AWA:** transform the search into an Alternating Weighted
     Automaton. Elegant but complex to implement.

4. **Theory versioning.** When a theory's constraint semantics change between
   language spec versions, how are existing analyses invalidated? The
   `TheoryRegistration` could carry a version hash computed from the theory's
   type definition, allowing the pipeline to detect stale analysis caches.

These questions are deferred to the implementation sprint.

---

## 9. Citations

- Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005). "Backtracking,
  Interleaving, and Terminating Monad Transformers." *ICFP 2005*. ACM,
  pp. 192--203. DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
- D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and
  transducers." *CAV 2017*. LNCS 10427, pp. 47--67. DOI:
  [10.1007/978-3-319-63390-9_3](https://doi.org/10.1007/978-3-319-63390-9_3)
- Martelli, A. & Montanari, U. (1982). "An Efficient Unification Algorithm."
  *ACM TOPLAS*, 4(2), 258--282. DOI:
  [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)
- Gay, S. & Vasconcelos, V. T. (2010). "Linear Type Theory for Asynchronous
  Session Types." *Journal of Functional Programming*, 20(1), 19--50. DOI:
  [10.1017/S0956796809990268](https://doi.org/10.1017/S0956796809990268)
- Eilenberg, S. (1976). *Automata, Languages, and Machines, Volume B*.
  Academic Press.
