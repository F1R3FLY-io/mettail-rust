# Compile-Time Guard Analysis: Algebras, Automata, and Algorithms per Data Type

**Companion to:** [Why Automata Instead of Solvers](why-automata-instead-of-solvers.md),
[Dispatch Optimization Analysis](dispatch-optimization-analysis.md)
**See also:** [Heyting Algebra Extensions](heyting-algebra-extensions.md)
**Status:** §2 describes implemented baselines; §§3-7 describe proposals
and research analysis.

---

The [dispatch optimization document](dispatch-optimization-analysis.md) explores
*runtime* indexing structures for fast guard evaluation.  This companion
covers the *compile-time* side: what algebraic backends (`BooleanAlgebra`,
`HeytingAlgebra`, `ConstraintTheory`), automata, and algorithms are needed
to analyze guard predicates over each data type **before** code is generated.

The five compile-time analysis questions (from the main document §2.3) are:

1. **Satisfiability (SAT):** Can any value satisfy `φᵢ`?  If not → dead guard.
2. **Overlap:** Can `φᵢ` and `φⱼ` both match the same value?
3. **Subsumption:** Does `φᵢ` shadow `φⱼ`?  (`⟦φⱼ⟧ ⊆ ⟦φᵢ⟧`)
4. **Exhaustiveness:** Do the guards cover the entire domain?
5. **Minterms:** Can the domain be partitioned into regions where each guard
   behaves identically?

The following abbreviations are used; terms defined in the main document are
cross-referenced:

- **MGU** — Most General Unifier (the simplest substitution making two terms equal)
- **NNF** — Negation Normal Form (negation pushed to atoms)

> **Terminology from the main document:** `BooleanAlgebra`, `HeytingAlgebra`,
> `ConstraintTheory`, `ProductAlgebra`, `TheoryAlgebra`, SFA, SFT, minterm,
> T1–T4 — defined in
> [Why Automata Instead of Solvers](why-automata-instead-of-solvers.md) §1.

---

## 1. Current Analysis Capability

The following table summarizes what the pipeline can currently analyze at
compile time for each guard domain:

| Domain | Algebra | SAT | Overlap | Subsumption | Exhaustiveness | Minterms | Status |
|--------|---------|-----|---------|-------------|----------------|----------|--------|
| Integer (1 var) | `IntervalAlgebra` | ✓ | ✓ | ✓ | ✓ | ✓ | **Complete** |
| Integer (k vars) | `PresburgerAlgebra` | ✓ | ✓ | ✓ | — | — | **Complete** |
| Character | `CharClassAlgebra` | ✓ | ✓ | ✓ | ✓ | ✓ | **Complete** |
| Propositional | `KatBooleanAlgebra` | ✓ | ✓ | ✓ | ✓ | ✓ | **Complete** |
| ADT/constructor | `UnificationTheory` | ✓ | — | — | — | — | **Partial** |
| String | — | — | — | — | — | — | **Gap** |
| Container | M9 (automaton only) | — | — | — | — | — | **Gap** |
| Graph/reachability | Ascent (runtime) | — | — | — | — | — | **Gap** |
| Product | `ProductAlgebra` | ✓ | ✓ | ✓ | ✓ | ✓ | **Complete** |

The **complete** entries implement the full `BooleanAlgebra` trait and
support all five analysis questions.  The **partial** entries implement
`ConstraintTheory` (lifted to `BooleanAlgebra` via `TheoryAlgebra`) but
lack some operations.  The **gap** entries have no compile-time algebraic
backend.

> **Cross-reference:** The main document's §3.3 lists the implemented
> `BooleanAlgebra` implementations.  This document focuses on extending
> analysis to the gap domains.

---

## 2. Implemented Baselines

### 2.1 IntervalAlgebra (Integers, Single Variable)

**Domain:** `i64` values within `[min_val, max_val)`.
**Predicates:** Unions of half-open intervals `[lo, hi)`.
**SAT:** Check whether the normalized interval list is non-empty.  Cost: `O(k)`
for `k` intervals.
**Complement:** Invert intervals against the universe bounds.  Cost: `O(k)`.
**Minterms:** Interval endpoints partition the domain into at most `2m + 1`
atomic intervals.  Each atomic interval is a minterm.

This is the simplest and most frequently used algebra.  Guards like
`x ≥ 10 ∧ x < 100` compile directly to interval predicates.

### 2.2 PresburgerAlgebra (Integers, Multiple Variables)

**Domain:** `ℤᵏ` (integer tuples).
**Predicates:** Boolean combinations of linear constraints `Σ aᵢ · xᵢ ≤ b`.
**SAT:** Compile to NFA via Büchi/Bartzis-Bultan construction, check emptiness
via BFS.  Cost: `O(w · R · 2ᵏ)` where `w` = bit width, `R` = reachable
remainders.
**Complement:** NFA complement (determinize + flip accepting states).

This algebra handles guards like `x + y ≤ 100 ∧ x ≥ 10` that relate
multiple integer variables — the central topic of the main document.

### 2.3 CharClassAlgebra (Unicode Characters)

**Domain:** Unicode code points `[0, 0x10FFFF]`.
**Predicates:** Unions of code-point ranges (e.g., `[a-z]`, `[α-ω]`).
**Operations:** Identical to `IntervalAlgebra` but over `u32` code points.

### 2.4 KatBooleanAlgebra (Propositional Atoms)

**Domain:** Truth assignments over named atoms `{p, q, r, …}`.
**Predicates:** Boolean formulas over atoms.
**SAT:** Exhaustive `2ⁿ` enumeration for `n` atoms.
**Minterms:** The `2ⁿ` truth assignments ARE the minterms.

Tractable for small atom sets (`n < 10`), which is typical for grammar-level
KAT guards.

---

## 3. String Guard Analysis

> **Status:** Not implemented.  This section proposes a `StringAlgebra`.

Strings are the most significant gap in the current analysis pipeline.
Guards like `name = "cowboy"`, `prefix(name, "cow")`, and
`matches(name, "cow.*")` have no compile-time algebraic backend — the
compiler cannot determine whether two string guards overlap or whether a
string guard is dead.

### 3.1 The Algebra Needed: StringAlgebra

A **string algebra** over alphabet `Σ` would provide:

- **Domain:** `Σ*` (finite strings over `Σ`)
- **Predicates:** Regular languages (the natural predicate class for strings)
- **Representation:** NFA or DFA over `Σ` (or SFA over `CharClassAlgebra`
  for Unicode)

The `BooleanAlgebra` operations map to standard automata operations:

| `BooleanAlgebra` operation | `StringAlgebra` implementation |
|---|---|
| `true_pred()` | Universal NFA `Σ*` |
| `false_pred()` | Empty NFA `∅` |
| `and(φ, ψ)` | NFA product (intersection) |
| `or(φ, ψ)` | NFA union |
| `not(φ)` | DFA complement (determinize + flip) |
| `is_satisfiable(φ)` | NFA non-emptiness (BFS reachability) |
| `witness(φ)` | Shortest accepting path in NFA |
| `evaluate(φ, s)` | NFA simulation on string `s` |

The key insight is that **regular languages are closed under all Boolean
operations** — they form a Boolean algebra.  This means `StringAlgebra`
satisfies the `BooleanAlgebra` trait, and all SFA operations (minterms,
determinization, equivalence) work automatically.

### 3.2 Lifting CharClassAlgebra to Strings

MeTTaIL already has `CharClassAlgebra` for single characters.  A string
guard is a sequence of character guards — an SFA over `CharClassAlgebra`:

```
  Character level:   CharClassAlgebra (single char predicates)
       │
       │  lift to sequences
       ▼
  String level:      SFA<CharClassAlgebra> (string predicates = regular languages)
       │
       │  BooleanAlgebra operations
       ▼
  StringAlgebra:     NFA product, complement, emptiness, minterms
```

The SFA framework already provides product, complement, and emptiness for
any `BooleanAlgebra` backend.  `StringAlgebra` is essentially
`SymbolicAutomaton<CharClassAlgebra>` with the `BooleanAlgebra` trait
implemented by delegating to SFA operations.

### 3.3 Specific String Guard Types

| Guard type | Automaton representation | Example |
|---|---|---|
| Exact equality | Single-path DFA | `name = "cowboy"` → 7-state DFA |
| Prefix | DFA with accepting prefix states | `prefix(name, "cow")` → 4-state DFA, accept at state 3+ |
| Suffix | Reversed-string DFA | `suffix(name, "boy")` → reversed 4-state DFA |
| Regex | NFA from regex compilation | `matches(name, "cow.*")` → standard regex→NFA |
| Length constraint | Counting DFA | `len(name) ≥ 3` → DFA with 4 states |

All of these produce NFAs/DFAs that are instances of
`SymbolicAutomaton<CharClassAlgebra>`.  The `BooleanAlgebra` operations
(intersection, complement, satisfiability) follow from the SFA framework.

### 3.4 Word Equations and Decomposition Guards

Guards like `x · y = "cowboy"` (string decomposition) are **word equations**
— decidable (Makanin, 1977) but PSPACE-hard (Plandowski, 2004).

For compile-time analysis, the key question is not "solve the equation" but
"is the equation satisfiable?" and "do two decomposition guards overlap?"
For a fixed target string of length `n`, there are `n + 1` possible split
points — enumeration is `O(n)`.  Satisfiability reduces to: does any split
point produce a valid `(x, y)` pair satisfying all additional constraints?

When additional constraints exist on `x` and `y` (e.g., `len(x) ≥ 3`),
the analysis combines the decomposition enumeration with the
`StringAlgebra` intersection: for each split point, check whether the
prefix satisfies `x`'s constraints and the suffix satisfies `y`'s
constraints.

### 3.5 Analysis Capabilities with StringAlgebra

| Analysis | Method | Cost |
|---|---|---|
| SAT | NFA non-emptiness (BFS) | `O(\|Q\| + \|δ\|)` |
| Overlap | `SAT(φᵢ ∧ φⱼ)` = NFA product + emptiness | `O(\|Q₁\| · \|Q₂\| · \|Σ\|)` |
| Subsumption | `SAT(φⱼ ∧ ¬φᵢ)` = product with complement + emptiness | `O(2^{\|Q_i\|} · \|Q_j\|)` |
| Exhaustiveness | `SAT(¬φ₁ ∧ ⋯ ∧ ¬φₘ)` | `O(2^{Σ\|Q_i\|})` worst case |
| Minterms | SFA minterm computation | Standard SFA algorithm |

---

## 4. ADT Guard Analysis

> **Status:** `UnificationTheory` implements SAT.  Overlap, subsumption, and
> exhaustiveness are not yet implemented.

### 4.1 Current: Satisfiability via Unification

The `UnificationTheory` (Martelli & Montanari, 1982) determines whether a
guard pattern is satisfiable — whether any ground term matches the pattern.
The algorithm decomposes the pattern into unification equations and solves
them in `O(n · α(n))` amortized time (with path compression).

### 4.2 Overlap Detection via Unification

Two guard patterns `P₁` and `P₂` overlap iff there exists a term matching
both.  This reduces to: **can `P₁` and `P₂` be unified?**

```
╔══════════════════════════════════════════════════════════════════════════╗
║  ADT_OVERLAP(P₁, P₂) → bool                                             ║
║                                                                          ║
║  Determine whether two ADT guard patterns can match the same term.       ║
║                                                                          ║
║  1. Rename variables in P₂ to avoid clashes with P₁                      ║
║  2. Attempt to unify P₁ and P₂ via Martelli-Montanari                    ║
║  3. If unification succeeds (MGU σ exists): patterns overlap             ║
║     If unification fails (clash or occurs check): patterns are disjoint  ║
║                                                                          ║
║  Cost: O(n · α(n)) where n = |P₁| + |P₂|                                ║
╚══════════════════════════════════════════════════════════════════════════╝
```

**Example:** `App(f, Var(x))` and `App(g, Const(a))` — unification fails
at the first argument (`f ≠ g` if `f` and `g` are distinct constructors,
or succeeds if `f` is a variable).  The MGU determines the overlap region.

### 4.3 Subsumption via Matching

Pattern `P₁` **subsumes** `P₂` iff every term matching `P₂` also matches
`P₁`.  This is equivalent to: `P₁` can be instantiated to `P₂` (one-way
matching, not bidirectional unification).

```
╔══════════════════════════════════════════════════════════════════════════╗
║  ADT_SUBSUMES(P₁, P₂) → bool                                            ║
║                                                                          ║
║  Determine whether P₁ subsumes P₂ (P₁ is more general).                 ║
║                                                                          ║
║  Attempt to match P₁ against P₂ (one-directional):                      ║
║  • Variables in P₁ may be instantiated to subterms of P₂                 ║
║  • Variables in P₂ are treated as constants (not instantiable)           ║
║                                                                          ║
║  If matching succeeds: P₁ subsumes P₂ (every P₂-match is a P₁-match)    ║
║  If matching fails: P₁ does not subsume P₂                               ║
║                                                                          ║
║  Cost: O(|P₁| + |P₂|)                                                    ║
╚══════════════════════════════════════════════════════════════════════════╝
```

**Example:** `App(f, _)` subsumes `App(g, Const(a))` because the wildcard
`_` matches any second argument.

### 4.4 Exhaustiveness via Tree Automata

**Exhaustiveness** asks: do the patterns `P₁, …, Pₘ` cover every possible
term of the ADT?  This requires computing the complement of the union of
all pattern languages and checking emptiness.

For **recursive ADTs** (e.g., lists, trees), the set of all terms is
infinite and the pattern languages are tree languages.  **Tree automata**
(M5 Parity Alternating Tree Automaton from the main document §7.6) provide
the natural formalism:

1. Build a tree automaton `A_i` accepting all terms matching pattern `P_i`
2. Compute the union `A₁ ∪ ⋯ ∪ Aₘ`
3. Compute the complement `¬(A₁ ∪ ⋯ ∪ Aₘ)` w.r.t. the type's universe
4. Check emptiness: if empty, the patterns are exhaustive

This is the standard approach for exhaustiveness checking in ML-family
pattern matching (Maranget, 2007).  The complement operation requires
determinization of the tree automaton — feasible for finite-depth ADTs,
but potentially exponential for deeply recursive types.

### 4.5 Algebraic vs. Abstract Data Types

The analysis techniques in §4.1–4.4 apply to **algebraic data types** —
types defined by constructors (`Option<T> = None | Some(T)`,
`List<T> = Nil | Cons(T, List<T>)`) where the compiler can see the full
internal structure.  Guards pattern-match on constructors, and the
compiler can enumerate all possible shapes.

**Abstract data types** — types defined by an interface (`Stack` with
`push`, `pop`, `isEmpty`) where the internal representation is hidden —
require a fundamentally different analysis.  The compiler can only reason
about **observable properties** (method return values), not internal state.

This distinction maps precisely to the Boolean/Heyting boundary:

| Property | Algebraic DT | Abstract DT |
|---|---|---|
| Compiler visibility | Full (constructors) | Interface only (methods) |
| Guard form | `@{Some(x)}` (pattern match) | `stack.isEmpty()` (observation) |
| Algebra | `BooleanAlgebra` (exact) | `HeytingAlgebra` (conservative) |
| Complement | Enumerate non-matching constructors | Pseudo-complement: strongest observable contradiction |
| Overlap | Decidable via unification (§4.2) | Conservative via `¬¬` approximation |
| Exhaustiveness | Decidable via tree automata (§4.4) | Undecidable in general |

For abstract data types, the observable properties form the open sets of a
topology — a Heyting algebra.  The compiler cannot compute the Boolean
complement of `isEmpty()` (that would require enumerating all non-empty
internal states, which the abstraction barrier hides).  Instead, the Heyting
pseudo-complement gives the strongest *observable* property contradicting
`isEmpty()` — "observably non-empty" — without crossing the abstraction
barrier.

The `BooleanApproximation` bridge lifts abstract DT guards to conservative
Boolean analysis: `SAT(¬¬φ) = false ⟹ SAT(φ) = false`.  This enables
sound dead guard detection and overlap analysis for abstract types, at the
cost of potential incompleteness (some dead guards may go undetected).

> **Cross-reference:**
> [Heyting Algebra Extensions](heyting-algebra-extensions.md) §6 provides
> the full treatment of abstract data type guards as a Heyting algebra use
> case, with concrete Rholang examples.

---

## 5. Container Guard Analysis

> **Status:** M9 Multiset Automata exist but are not integrated as a
> `BooleanAlgebra` or `ConstraintTheory`.

### 5.1 List Predicates

Guards over lists combine several sub-domains:

| Predicate | Sub-domain | Existing algebra |
|---|---|---|
| `len(xs) ≥ 3` | Length (integer) | `PresburgerAlgebra` (k=1) |
| `xs[2] = "foo"` | Positional element | `StringAlgebra` (proposed, §3) |
| `prefix(xs, [1,2,3])` | List prefix | Lift `StringAlgebra` to list elements |
| `elem(42, xs)` | Membership | No existing algebra |
| `sorted(xs)` | Ordering property | Undecidable in general |

**Length predicates** reduce to `PresburgerAlgebra` with one variable (the
list length).  **Positional predicates** reduce to the element type's
algebra at the given index.  **Membership predicates** are harder: "does the
list contain 42?" requires existential quantification over positions.

### 5.2 Set and Multiset Predicates

| Predicate | Algebra approach |
|---|---|
| `elem(x, S)` (membership) | Existential over elements |
| `S₁ ⊆ S₂` (subset) | Universal: every element of S₁ is in S₂ |
| `\|S\| ≥ k` (cardinality) | `PresburgerAlgebra` on cardinality |
| `S₁ ∩ S₂ = ∅` (disjointness) | Universal: no shared elements |

Cardinality predicates can be analyzed via `PresburgerAlgebra` by treating
the set size as an integer variable.  Membership and subset predicates
require the element type's algebra composed with existential/universal
quantification — which the `LogicT` framework provides via
`TheoryAlgebra` (bounded search for T3 guards).

### 5.3 Proposed: ContainerAlgebra Trait Hierarchy

```
╔══════════════════════════════════════════════════════════════════════════╗
║  CONTAINER ALGEBRA HIERARCHY (proposed)                                  ║
║                                                                          ║
║      ConstraintTheory                                                    ║
║           │                                                              ║
║           ├── ListTheory<E: BooleanAlgebra>                               ║
║           │   • length constraints (delegate to PresburgerAlgebra)        ║
║           │   • positional constraints (delegate to E)                    ║
║           │   • prefix/suffix (delegate to sequence SFA)                  ║
║           │                                                              ║
║           ├── SetTheory<E: BooleanAlgebra>                                ║
║           │   • cardinality (delegate to PresburgerAlgebra)               ║
║           │   • membership (existential over E)                           ║
║           │   • subset (universal over E)                                 ║
║           │                                                              ║
║           └── MultisetTheory<E: BooleanAlgebra>                           ║
║               • multiplicity bounds (Presburger on counts)                ║
║               • feature multiplicities (existing M9 infrastructure)      ║
║                                                                          ║
║  Each is lifted to BooleanAlgebra via TheoryAlgebra<T>.                  ║
║  Quantified constraints use LogicT fair backtracking (bounded search).   ║
╚══════════════════════════════════════════════════════════════════════════╝
```

The key design principle: container algebras are **parameterized** by the
element type's algebra `E`.  A `ListTheory<IntervalAlgebra>` analyzes
integer lists; a `ListTheory<StringAlgebra>` analyzes string lists.  The
`TheoryAlgebra` bridge lifts each to `BooleanAlgebra` for SFA integration.

### 5.4 Decidability Boundaries

| Predicate class | Decidability | Approach |
|---|---|---|
| Length only | T1 (compile-time) | `PresburgerAlgebra` |
| Positional + length | T1/T2 | Compose position algebra + Presburger |
| Membership (bounded) | T3 (bounded search) | `LogicT` with depth bound |
| Sorted, permutation | T4 (undecidable) | Trust wrapper |

---

## 6. Graph/Reachability and Non-Boolean Guard Analysis via Heyting SFAs

> **Status:** Not implemented.  The theoretical framework is established in
> [Heyting Algebra Extensions](heyting-algebra-extensions.md).

### 6.1 The Gap

Graph/reachability guards — `reachable(x, target)`,
`bisimilar(x, P)`, `connectivity_closure(ch, target)` — are currently
evaluated at runtime via Ascent fixpoint relation lookups (T2 tier).  No
compile-time analysis exists: the compiler cannot determine whether a
reachability guard is dead, whether two reachability guards overlap, or
whether a set of reachability guards is exhaustive.

### 6.2 The Heyting SFA Approach

The [Heyting Algebra Extensions](heyting-algebra-extensions.md) document
establishes the theoretical framework for compile-time analysis of
non-Boolean guard domains:

1. **`HeytingAlgebra` trait** — provides `∧`, `∨`, `→` (implication),
   `¬` (pseudo-complement), and `SAT`.  Differs from `BooleanAlgebra` in
   that `¬¬φ ≥ φ` (not equality).

2. **`BooleanApproximation<H>` bridge** — lifts any `HeytingAlgebra` to a
   `BooleanAlgebra` via double-negation closure `¬¬`.  This enables SFA
   operations (minterms, determinization, overlap) with **conservative**
   guarantees:

       SAT(¬¬φ) = false  ⟹  SAT(φ) = false     (dead guard: sound)
       SAT(¬¬φᵢ ∧ ¬¬φⱼ) = false  ⟹  disjoint    (overlap: sound)

   The approximation may produce false positives (reporting a dead guard
   as possibly satisfiable) but never false negatives.

3. **`MixedProductAlgebra<B, H>`** — composes a Boolean domain (integers,
   characters) with a Heyting domain (graphs, reachability) in a single
   product algebra.  The Boolean side provides exact analysis; the Heyting
   side provides conservative analysis.

### 6.3 Concrete Applications

**Reachability closure.** The set of processes from which a target is
reachable forms an upward-closed set in the subprocess ordering — a Heyting
algebra.  The double-negation closure `¬¬(reachable)` includes processes
that are reachable "in the limit" (via infinite chains).  The
`BooleanApproximation` uses this closure for compile-time analysis: if
`¬¬(reachable)` is empty, the guard is definitely dead.

**Bisimulation.** Observable properties (confirmable in finite observations)
form the open sets of a topology — a Heyting algebra.  A guard
`bisimilar(x, P)` checks an observable property whose boundary (processes
distinguishable only by infinite observation) is topologically meaningful.

**Channel connectivity.** The connectivity closure of a channel (reachable
via finite or infinite forwarding chains) is a Heyting property.
Compile-time analysis via `¬¬` determines whether any process can possibly
reach the target channel.

**Observable properties.** Guards over "the process can output 42"
(observable = open) vs. "the process never outputs 42" (co-observable =
closed) live in the Heyting algebra of open sets.  The pseudo-complement
`¬φ` stays within the topology — it doesn't cross the observability
boundary.

> **Cross-reference:** [Heyting Algebra Extensions](heyting-algebra-extensions.md)
> §4 (graph analysis examples), §6 (five "beyond Boolean" use cases), §7
> (soundness proof).

### 6.4 Static Graphs: Finite Transitive Closure

When the process graph is **statically known** (e.g., a fixed network
topology declared at compile time), reachability analysis becomes T1
(compile-time decidable):

1. Compute the **transitive closure** of the graph's edge relation
   (Floyd-Warshall: `O(n³)`, or matrix multiplication: `O(n^ω)`)
2. For each reachability guard `reachable(x, target)`, check whether
   `(x, target)` is in the transitive closure
3. Dead guard: if `(x, target)` is not in the closure for any `x`
4. Overlap: if the reachable sets of two guards share vertices

This is exact (Boolean, not Heyting) because the graph is finite and fully
known.  The Heyting approach is needed only when the graph is dynamic or
partially known.

### 6.5 Limitations

The `BooleanApproximation` via `¬¬` is **sound but incomplete**:

- Dead guard detection may miss some dead guards (false positives in SAT)
- Overlap detection may report disjoint guards as overlapping
- Minterms have gaps (the pseudo-complement is not involutive, so minterm
  regions may not perfectly partition the domain)

These limitations are inherent to the Heyting algebra — they reflect the
genuine topological structure of the guard domain.  For compile-time
analysis, conservative approximation is acceptable: no incorrect code is
generated, and the runtime behavioral layer (Ascent) provides exact
evaluation.

---

## 7. Cross-Domain and Heterogeneous Analysis

### 7.1 Current: ProductAlgebra (2-ary)

`ProductAlgebra<A, B>` composes two `BooleanAlgebra` instances into a
new `BooleanAlgebra` over the Cartesian product domain.  Satisfiability
factors per-component: `SAT(Both(a, b)) = SAT_A(a) ∧ SAT_B(b)`.

This handles guards like `x ≥ 10 ∧ ch ∈ [a-z]` (integer + character) by
composing `IntervalAlgebra` with `CharClassAlgebra`.

**Limitation:** `ProductAlgebra` is 2-ary — composing three or more algebras
requires nesting: `ProductAlgebra<A, ProductAlgebra<B, C>>`.  This works but
is syntactically awkward and may not optimize well.

### 7.2 Cross-Domain Constraints

The most challenging case is **shared variables** across domains:
`x ≥ 10 ∧ len(name) = x` — where `x` appears in both an integer constraint
and a string length constraint.

`ProductAlgebra` cannot handle this because it assumes independent domains.
Shared-variable constraints require **theory combination** — the SMT
approach (Nelson-Oppen) or a more specialized mechanism.

The existing `LogicT` framework can handle this via constraint propagation:
the `PresburgerTheory` propagates `x ≥ 10`, and the `ListTheory` propagates
`len(name) = x`, with shared variables synchronized through the constraint
store.  This is T3-tier analysis (bounded search), not the T1/T2 exact
analysis that `ProductAlgebra` provides.

### 7.3 When to Use Heyting vs. Boolean

| Domain property | Algebra type | Rationale |
|---|---|---|
| Finite, fully known | Boolean | Exact analysis, full SFA operations |
| Infinite but regular | Boolean | SFA/NFA represent infinite sets finitely |
| Topological (closure, limits) | Heyting | `¬¬φ ≠ φ`; conservative approximation |
| Observable (open-set semantics) | Heyting | Pseudo-complement stays in topology |
| Partial information | Heyting | Evaluable on filters, not just points |
| Mixed | `MixedProductAlgebra<B, H>` | Boolean for exact, Heyting for approx |

---

## 8. Analysis Capability Matrix (Proposed)

With the proposed extensions (§§3-6), the compile-time analysis landscape
would expand to:

| Domain | Algebra | Type | SAT | Overlap | Subsume | Exhaust | Minterms |
|--------|---------|------|-----|---------|---------|---------|----------|
| Integer (1 var) | `IntervalAlgebra` | Boolean | ✓ | ✓ | ✓ | ✓ | ✓ |
| Integer (k vars) | `PresburgerAlgebra` | Boolean | ✓ | ✓ | ✓ | — | — |
| Character | `CharClassAlgebra` | Boolean | ✓ | ✓ | ✓ | ✓ | ✓ |
| Propositional | `KatBooleanAlgebra` | Boolean | ✓ | ✓ | ✓ | ✓ | ✓ |
| **String** | **`StringAlgebra`** | **Boolean** | **✓** | **✓** | **✓** | **✓** | **✓** |
| **Algebraic DT** | **`UnificationTheory`** (ext.) | **Boolean** | ✓ | **✓** | **✓** | **✓** | — |
| **Abstract DT** | **`HeytingAlgebra`** | **Heyting** | **≈** | **≈** | **≈** | — | — |
| **Container** | **`ContainerTheory<E>`** | **Theory** | **✓** | **≈** | **≈** | — | — |
| **Graph/reach** | **`HeytingAlgebra`** | **Heyting** | **≈** | **≈** | — | — | **≈** |
| Product | `ProductAlgebra` | Boolean | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Mixed** | **`MixedProductAlgebra`** | **Mixed** | **✓** | **≈** | **≈** | — | **≈** |

Legend: ✓ = exact, ≈ = conservative approximation, — = not feasible.
**Bold** = proposed extensions.

---

## 9. Research Priorities

| Priority | Extension | Impact | Effort | Source |
|----------|-----------|--------|--------|--------|
| 1 | `StringAlgebra` via SFA over `CharClassAlgebra` | High | Medium | SFA framework already exists |
| 2 | ADT overlap/subsumption via unification/matching | High | Low | Algorithms well-known |
| 3 | ADT exhaustiveness via tree automata (M5) | Medium | Medium | Maranget (2007) |
| 4 | `ContainerTheory<E>` with Presburger length | Medium | Medium | Compose existing algebras |
| 5 | `HeytingAlgebra` for graph/reachability | Medium | High | Original research (§6) |
| 6 | `MixedProductAlgebra<B, H>` | Low | Low | Straightforward extension |
| 7 | Cross-domain shared-variable constraints | Low | High | Requires theory combination |

---

## 10. References

1. Baader, F. & Snyder, W. (2001). ["Unification
   Theory."](https://doi.org/10.1016/b978-044450813-3/50010-2) In *Handbook
   of Automated Reasoning*, vol. 1, ch. 8. Elsevier.
   DOI: [10.1016/b978-044450813-3/50010-2](https://doi.org/10.1016/b978-044450813-3/50010-2).

2. D'Antoni, L. & Veanes, M. (2014). ["Minimization of symbolic
   automata."](https://doi.org/10.1145/2535838.2535849) *Proceedings of
   POPL*, pp. 541-553. ACM.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849).

3. Esakia, L. (2019). [*Heyting Algebras: Duality
   Theory*](https://doi.org/10.1007/978-3-030-12096-2). Springer.
   DOI: [10.1007/978-3-030-12096-2](https://doi.org/10.1007/978-3-030-12096-2).

4. Martelli, A. & Montanari, U. (1982). ["An efficient unification
   algorithm."](https://doi.org/10.1145/357162.357169) *ACM TOPLAS*,
   4(2):258-282.
   DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169).

5. Sekar, R., Ramakrishnan, I. V. & Voronkov, A. (2001). ["Term
   Indexing."](https://doi.org/10.1016/B978-044450813-3/50028-X) In
   *Handbook of Automated Reasoning*, vol. 2, ch. 26. Elsevier.
   DOI: [10.1016/B978-044450813-3/50028-X](https://doi.org/10.1016/B978-044450813-3/50028-X).

6. Veanes, M. (2013). ["Applications of symbolic finite
   automata."](https://doi.org/10.1007/978-3-642-39274-0_3) *CIAA 2013*,
   LNCS 7982, pp. 16-23. Springer.
   DOI: [10.1007/978-3-642-39274-0_3](https://doi.org/10.1007/978-3-642-39274-0_3).
