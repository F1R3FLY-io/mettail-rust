# Weighted Automata over Featured Multiset Semirings — Theoretical Foundations

## Motivation

Many computational phenomena involve **multiplicities**: a resource may be consumed multiple times, a process may spawn multiple copies, or a grammar rule may apply at different frequencies. Standard semirings (Tropical, Boolean, Counting) assign scalar weights to computation paths, but when weights must track **per-feature multiplicities** — how many times each distinct feature occurs along a path — a richer algebraic structure is needed.

**Core question**: How can we define semiring operations over multisets of features so that automata-theoretic algorithms (shortest path, intersection, Kleene closure) generalize correctly to multiplicity-aware computation?

**Historical context**: The featured multiset semiring was introduced by Müller, Weiß & Lochau (2024) in the context of software product line analysis, where features have cardinality constraints (each feature must appear between `min` and `max` times). Their key insight is that multisets over a feature set F form a semiring when equipped with pointwise operations, and weighted automata over this semiring naturally model cardinality-bounded feature interactions. The tropical variant `(ℝ₊∞^F, min, +, +∞̄, 0̄)` extends the classical tropical semiring to vector-valued costs.

**Connection to the Chomsky hierarchy**: Weighted automata over multiset semirings recognize the same structural languages as classical finite automata — the state graph determines acceptance, while the multiset weights provide quantitative annotations. The multiset structure does not increase the class of recognized languages but enriches the weight domain to capture multiplicity information that scalar semirings cannot express.

## Definitions

**Definition 9.1** (Multiset over Feature Set). Given a finite feature set F = {f₁, f₂, ..., f_k}, a **multiset** over F is a function m : F → ℕ₀ assigning a non-negative integer multiplicity to each feature. The set of all multisets over F is denoted ℕ₀^F.

*Intuition*: A multiset records "how many times" each feature appears. For example, if F = {alloc, send, recv}, then m = {alloc ↦ 3, send ↦ 1, recv ↦ 0} says: three allocations, one send, no receives.

In MeTTaIL: `MultisetWeight` stores multiplicities as `HashMap<String, u64>`, where absent keys have implicit multiplicity 0.

**Definition 9.2** (Natural-Number Multiset Semiring; Müller, Weiß & Lochau, 2024, Definition 3.1). The **natural-number multiset semiring** over feature set F is the tuple (ℕ₀^F, ⊕, ⊗, 0̄, 1̄) where:
- **⊕ = pointwise max**: (m₁ ⊕ m₂)(f) = max(m₁(f), m₂(f))
- **⊗ = pointwise add**: (m₁ ⊗ m₂)(f) = m₁(f) + m₂(f)
- **0̄ = zero multiset**: 0̄(f) = 0 for all f ∈ F (identity for max)
- **1̄ = zero multiset**: 1̄(f) = 0 for all f ∈ F (identity for addition)

*Intuition*: When combining parallel paths (⊕), we take the worst-case (maximum) multiplicity for each feature — if one path allocates 3 resources and another allocates 5, the combined requirement is 5. When sequencing paths (⊗), multiplicities accumulate additively — a path segment that allocates 3 followed by one that allocates 2 yields 5 total allocations.

*Note on identities*: Both 0̄ and 1̄ are the zero multiset, which is unusual. This is because max(0, x) = x (the zero multiset is the identity for pointwise max) and 0 + x = x (the zero multiset is also the identity for pointwise addition). The semiring is **zero-sum free** but **not** a ring (no additive inverses exist over ℕ₀).

In MeTTaIL: `MultisetWeight::zero()` returns an empty HashMap (all features implicitly 0). `MultisetWeight::one()` also returns an empty HashMap. The `plus()` method computes pointwise max; `times()` computes pointwise add.

**Definition 9.3** (Tropical Multiset Semiring). The **tropical multiset semiring** over feature set F is the tuple (ℝ₊∞^F, ⊕, ⊗, 0̄, 1̄) where:
- **⊕ = pointwise min**: (m₁ ⊕ m₂)(f) = min(m₁(f), m₂(f))
- **⊗ = pointwise add**: (m₁ ⊗ m₂)(f) = m₁(f) + m₂(f)
- **0̄ = infinite multiset**: 0̄(f) = +∞ for all f ∈ F (identity for min)
- **1̄ = zero-cost multiset**: 1̄(f) = 0.0 for all f ∈ F (identity for add)

*Intuition*: This is the vector-valued generalization of the classical tropical semiring (ℝ₊∞, min, +, +∞, 0). Combining parallel paths selects the minimum cost per feature (optimistic combination), while sequencing paths accumulates costs additively per feature.

In MeTTaIL: `TropicalMultisetWeight` stores costs as `HashMap<String, f64>`, with absent keys having implicit cost +∞ for zero() and 0.0 for one().

**Definition 9.4** (Cardinality Constraint). A **cardinality constraint** over feature set F is a tuple (f, min, max) where f ∈ F and min, max ∈ ℕ₀ ∪ {∞}. A multiset m **satisfies** the constraint if min ≤ m(f) ≤ max.

*Intuition*: Cardinality constraints bound how many times a feature may appear. For grammar analysis: a rule might require "at least 1 and at most 3 applications of the allocation pattern."

In MeTTaIL: `CardinalityConstraint { feature, min, max }` struct, checked by `satisfies_cardinality()`.

**Definition 9.5** (HeapSemiring Trait). Because multiset weights are stored as `HashMap<String, _>`, they cannot implement Rust's `Copy` trait. The **HeapSemiring** trait mirrors the `Semiring` trait but relaxes the `Copy` bound:

```
HeapSemiring: Clone + Debug + PartialEq + Send + Sync {
    fn zero() → Self
    fn one() → Self
    fn plus(&self, &Self) → Self
    fn times(&self, &Self) → Self
    fn is_zero(&self) → bool
}
```

*Rationale*: Standard semiring operations in MeTTaIL require `Copy` for efficiency (weights are small scalars: f64, bool, u64). Multiset weights are variable-size heap allocations, so a separate trait hierarchy accommodates them without imposing `Copy` on the rest of the semiring infrastructure.

## Key Theorems

**Theorem 9.1** (Multiset Semiring Laws; Müller, Weiß & Lochau, 2024, Theorem 3.2):
The natural-number multiset semiring (ℕ₀^F, max, +, 0̄, 0̄) satisfies all semiring axioms:
1. (ℕ₀^F, max, 0̄) is a commutative monoid
2. (ℕ₀^F, +, 0̄) is a commutative monoid
3. Distributivity: m₁ + (m₂ max m₃) = (m₁ + m₂) max (m₁ + m₃) (pointwise)
4. Annihilation: m + 0̄ = m = 0̄ + m

*Proof sketch*: Each axiom follows from the corresponding property of (ℕ₀, max, +, 0, 0) applied pointwise. Commutativity: max and + are commutative over ℕ₀. Associativity: max and + are associative over ℕ₀. Distributivity: for each feature f, m₁(f) + max(m₂(f), m₃(f)) = max(m₁(f) + m₂(f), m₁(f) + m₃(f)) by the standard distributivity of addition over max in ℕ₀. Identity: max(0, x) = x and 0 + x = x. Annihilation: 0̄ is both the additive and multiplicative identity, so annihilation holds trivially.

*Consequence for MeTTaIL*: The `MultisetWeight` implementation is verified to satisfy these laws. The `HeapSemiring` methods `plus()` and `times()` are the ⊕ (pointwise max) and ⊗ (pointwise add) operations respectively.

*Reference*: Müller, C., Weiß, B. & Lochau, M. (2024). "Mapping Cardinality-based Feature Models to Weighted Automata over Featured Multiset Semirings." *Software and Systems Modeling* (SoSyM).

**Theorem 9.2** (Tropical Multiset Semiring Laws):
The tropical multiset semiring (ℝ₊∞^F, min, +, +∞̄, 0̄) satisfies all semiring axioms, by the same pointwise argument applied to the scalar tropical semiring (ℝ₊∞, min, +, +∞, 0).

*Proof sketch*: Identical structure to Theorem 9.1, substituting min for max and ℝ₊∞ for ℕ₀. Distributivity: a + min(b, c) = min(a + b, a + c) holds in ℝ₊∞ because addition is monotone. The +∞ element is absorbing for min (identity) and neutral for addition in the extended reals (∞ + x = ∞ serves as annihilator).

*Consequence for MeTTaIL*: `TropicalMultisetWeight` uses this for minimum-cost path analysis where costs are per-feature vectors rather than scalars.

**Theorem 9.3** (Idempotency of ⊕):
Both multiset semirings have idempotent addition:
- max(m, m) = m for all m ∈ ℕ₀^F
- min(m, m) = m for all m ∈ ℝ₊∞^F

*Consequence*: These are both **idempotent semirings** (also called **dioids**). In an idempotent semiring, the Kleene star (closure) operation is well-defined and computes shortest/cheapest paths. The generic algorithms in `forward_backward.rs` and `wfst.rs` that rely on idempotent convergence work correctly with multiset weights.

**Theorem 9.4** (Cardinality Constraint Decidability):
Given a multiset automaton M over the natural-number multiset semiring and a cardinality constraint (f, min, max), the problem "does there exist an accepting run of M whose total weight satisfies min ≤ w(f) ≤ max?" is decidable in time O(|Q|² · |δ| · max) via a product construction with a counter automaton tracking m(f).

*Proof sketch*: Construct M' = M × C_f where C_f is a counter automaton with states {0, 1, ..., max+1} tracking the cumulative multiplicity of feature f. Transitions in M that add k to feature f advance the counter by k (saturating at max+1). M' accepts iff it reaches a state (q_final, c) with min ≤ c ≤ max. The product has O(|Q| · (max+1)) states, so emptiness is decidable in O(|Q|·max + |δ|·max).

*Consequence for MeTTaIL*: The `satisfies_cardinality()` method implements a simplified version of this check. For grammar analysis, cardinality constraints bound how many times a pattern or rule may fire.

**Theorem 9.5** (Feature Interaction Detection):
For two features f₁, f₂ ∈ F, the **interaction** between f₁ and f₂ along accepting runs of M can be characterized by the projection of the total multiset weight onto the pair (f₁, f₂). If there exist accepting runs r₁, r₂ such that the weight vectors (w_r₁(f₁), w_r₁(f₂)) and (w_r₂(f₁), w_r₂(f₂)) are incomparable in the product order, then f₁ and f₂ exhibit a **trade-off** interaction.

*Intuition*: Two features interact when increasing one's multiplicity requires decreasing the other's (or vice versa). This captures the notion that certain grammatical features are in tension — for example, increasing the depth of nesting (feature f₁) may require more stack frames (feature f₂), but the relationship is not monotone across all derivation paths.

*Consequence for MeTTaIL*: The `feature_interaction()` method computes the set of all (f₁-multiplicity, f₂-multiplicity) pairs across accepting runs and reports whether a trade-off exists.

## Algorithms

### Algorithm 1: Multiset Weight Evaluation

```
PROCEDURE MULTISET-EVAL(M, w)
  INPUT:  Multiset automaton M over HeapSemiring, input word w
  OUTPUT: Total acceptance weight (multiset)

  1. configs ← {(q, 0) → I(q) : q ∈ initial states}
     // (state, input position) → accumulated multiset weight
  2. For pos = 0 to |w| - 1:
       For each ((q, pos), m) ∈ configs:
         For each transition t = (q, label, q', m_t):
           If label = w[pos] or label = ε:
             pos' ← pos + (if label ≠ ε then 1 else 0)
             configs[(q', pos')] ← configs[(q', pos')].plus(m.times(m_t))
  3. total ← HeapSemiring::zero()
     For each ((q, |w|), m) where q ∈ final:
       total ← total.plus(m.times(F(q)))
  4. Return total

  COMPLEXITY: O(|w| · |Q| · |δ|) time, O(|Q| · |F|) space per configuration
```

### Algorithm 2: Multiplicity Extraction

```
PROCEDURE MULTIPLICITY-OF(M, feature, w)
  INPUT:  Multiset automaton M, feature f ∈ F, input word w
  OUTPUT: Maximum multiplicity of f across all accepting runs

  1. total_weight ← MULTISET-EVAL(M, w)
  2. Return total_weight.counts.get(feature).unwrap_or(0)

  COMPLEXITY: Same as MULTISET-EVAL
```

*Intuition*: Because ⊕ = pointwise max, the total weight aggregates the maximum multiplicity of each feature across all accepting runs. To extract the multiplicity of a specific feature, simply look up its entry in the resulting multiset.

### Algorithm 3: Cardinality Constraint Checking

```
PROCEDURE SATISFIES-CARDINALITY(M, constraint, w)
  INPUT:  Multiset automaton M, constraint (f, min, max), input word w
  OUTPUT: Boolean — does the total multiplicity of f satisfy the constraint?

  1. total_weight ← MULTISET-EVAL(M, w)
  2. count ← total_weight.counts.get(f).unwrap_or(0)
  3. Return min ≤ count ≤ max

  COMPLEXITY: Same as MULTISET-EVAL
```

### Algorithm 4: Feature Interaction Analysis

```
PROCEDURE FEATURE-INTERACTION(M, f₁, f₂)
  INPUT:  Multiset automaton M, features f₁, f₂ ∈ F
  OUTPUT: Set of (multiplicity₁, multiplicity₂) pairs across all accepting runs

  1. For each accepting run r of M:
       Compute weight(r) by ⊗-accumulating transition weights
       Record (weight(r)(f₁), weight(r)(f₂))
  2. Return the set of recorded pairs

  COMPLEXITY: O(|runs| · |path_length|)
  Note: In general, |runs| can be exponential in |Q|.
```

### Algorithm 5: Tropical Projection

```
PROCEDURE TROPICAL-PROJECTION(M_multiset)
  INPUT:  MultisetAutomaton<MultisetWeight>
  OUTPUT: MultisetAutomaton<TropicalMultisetWeight>

  1. Create M' with same states, transitions, initial/final structure
  2. For each transition t with MultisetWeight w:
       Convert w to TropicalMultisetWeight:
         For each (feature, count) in w.counts:
           tropical_w[feature] = count as f64
  3. Return M'

  COMPLEXITY: O(|δ| · |F|)
```

*Intuition*: Tropical projection maps the natural-number domain to the real-valued tropical domain, enabling min-cost analysis over the same feature structure. This is useful when the goal shifts from "maximum multiplicity" to "minimum cost" while preserving the per-feature granularity.

## Decidability Analysis

| Property | Natural ℕ₀^F | Tropical ℝ₊∞^F | Tier |
|----------|:------------:|:---------------:|:----:|
| Emptiness | O(\|Q\|+\|δ\|) | O(\|Q\|+\|δ\|) | T1 |
| Membership (word acceptance) | O(\|w\|·\|Q\|·\|δ\|) | O(\|w\|·\|Q\|·\|δ\|) | T1 |
| Cardinality satisfaction | O(\|w\|·\|Q\|·\|δ\|) | O(\|w\|·\|Q\|·\|δ\|) | T1 |
| Feature multiplicity query | O(\|w\|·\|Q\|·\|δ\|) | O(\|w\|·\|Q\|·\|δ\|) | T1 |
| Equivalence (weight equality) | Decidable (idempotent) | Decidable (idempotent) | T2 |
| Feature interaction detection | Exponential (run enumeration) | Exponential (run enumeration) | T2 |
| Universality (all multisets) | Undecidable | Undecidable | T4 |

*Note*: Emptiness and membership are T1 because they depend only on the state graph structure and individual weight computations, not on the structure of the multiset semiring. Equivalence is T2 because the idempotent semiring admits polynomial minimization and comparison algorithms (Mohri, 2009), but the per-feature vector comparison adds an O(|F|) factor. Feature interaction is T2 because it requires enumerating accepting runs, which may be exponential but is always finite for a finite automaton and finite input.

## Diagrams

### Multiset Semiring Operations

```
Feature set F = {alloc, send, recv}

m₁ = {alloc: 3, send: 1, recv: 0}
m₂ = {alloc: 1, send: 2, recv: 4}

⊕ (pointwise max):
  m₁ ⊕ m₂ = {alloc: max(3,1), send: max(1,2), recv: max(0,4)}
           = {alloc: 3, send: 2, recv: 4}

⊗ (pointwise add):
  m₁ ⊗ m₂ = {alloc: 3+1, send: 1+2, recv: 0+4}
           = {alloc: 4, send: 3, recv: 4}

0̄ = {} = {alloc: 0, send: 0, recv: 0}  (identity for max)
1̄ = {} = {alloc: 0, send: 0, recv: 0}  (identity for add)
```

### Multiset Automaton for Process Multiplicity

```
Grammar: PPar alloc* | send recv

  ┌────┐  alloc/{alloc:1}  ┌────┐  send/{send:1}  ┌────┐  recv/{recv:1}  ┌────┐
  │ q₀ │─────────────────▶│ q₁ │────────────────▶│ q₂ │────────────────▶│ q₃*│
  └────┘                   └─┬──┘                  └────┘                 └────┘
                              │ alloc/{alloc:1}
                              ▼
                           ┌────┐
                           │ q₁ │ (self-loop: accumulates alloc count)
                           └────┘

  Word: alloc alloc send recv
  Path: q₀ → q₁ → q₁ → q₂ → q₃
  Weight: {alloc:0} ⊗ {alloc:1} ⊗ {alloc:1} ⊗ {send:1} ⊗ {recv:1}
        = {alloc:2, send:1, recv:1}

  Constraint: (alloc, 1, 5) → satisfied (2 ∈ [1,5])
              (recv, 0, 1)  → satisfied (1 ∈ [0,1])
```

### HeapSemiring vs Semiring Trait Hierarchy

```
┌──────────────────────────────────┐
│         Semiring (Copy)          │
│  TropicalWeight, BooleanWeight,  │
│  CountingWeight, LogWeight, ...  │
│                                  │
│  Used by: WFST, Pipeline,       │
│  ForwardBackward, Compose, ...   │
└──────────────────────────────────┘

┌──────────────────────────────────┐
│     HeapSemiring (Clone only)    │
│  MultisetWeight, TropicalMulti-  │
│  setWeight                       │
│                                  │
│  Used by: MultisetAutomaton,     │
│  Feature interaction analysis    │
│                                  │
│  Reason: HashMap<String, _>      │
│  cannot implement Copy           │
└──────────────────────────────────┘
```

### Feature Interaction Visualization

```
Feature interaction between alloc and send:

  alloc multiplicity
    5 │         ×
    4 │     ×       ×
    3 │ ×               ×
    2 │         ×   ×
    1 │     ×
    0 └─┬───┬───┬───┬───┬──▶ send multiplicity
      0   1   2   3   4

  × = observed (alloc, send) pair across accepting runs
  Non-monotone distribution → trade-off interaction detected
```

## Connections

**To Semiring module**: `MultisetWeight` and `TropicalMultisetWeight` extend the semiring hierarchy with vector-valued weights. The `HeapSemiring` trait parallels the `Semiring` trait for heap-allocated weights that cannot implement `Copy`. The existing scalar semirings (TropicalWeight, CountingWeight) are special cases with |F| = 1.

**To Module 7 (Probabilistic)**: The tropical multiset semiring enables per-feature cost analysis analogous to the log-domain probability computations in `probabilistic.rs`. A natural extension would be a probabilistic multiset semiring where each feature carries a log-probability, enabling per-feature likelihood analysis.

**To Module 8 (Multi-Tape)**: Multi-tape automata can be combined with multiset weights to track per-tape feature multiplicities. Each tape could contribute distinct features to the multiset, enabling cross-tape resource analysis.

**To Pipeline**: The `MultisetAutomaton` supports resource-bounded grammar analysis. Cardinality constraints can express grammar-level bounds (e.g., "each recursive non-terminal may expand at most k times"), which feed into lint rules and cost-benefit analysis.

**Open problems**:
1. **Weighted closure over multiset semirings**: The Kleene star m* should converge for idempotent multiset semirings (max is idempotent), but formal convergence proofs for the general case with unbounded feature multiplicities require care.
2. **Partial-order multiset semirings**: Replacing pointwise max with a lattice meet or join operation would enable richer feature combination strategies (e.g., type-theoretic lattice analysis).
3. **Streaming multiset evaluation**: Online computation where the feature set F itself may grow dynamically as new features are discovered during parsing.

## Bibliography

1. Müller, C., Weiß, B. & Lochau, M. (2024). "Mapping Cardinality-based Feature Models to Weighted Automata over Featured Multiset Semirings." *Software and Systems Modeling* (SoSyM).

2. Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213–254. Springer.

3. Droste, M. & Kuich, W. (2009). "Semirings and Formal Power Series." In *Handbook of Weighted Automata*, Chapter 1, pp. 3–28. Springer.

4. Golan, J.S. (1999). *Semirings and their Applications*. Kluwer Academic Publishers.

5. Hoare, C.A.R. (1985). *Communicating Sequential Processes*. Prentice Hall. (Motivates the process-algebraic view of resource multiplicities.)
