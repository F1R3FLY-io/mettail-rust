# Semiring Catalog

Comprehensive reference for all semiring types and trait hierarchy extensions
in PraTTaIL's WFST pipeline.

## 1. Implemented Semirings

### 1.1 TropicalWeight
- **Algebra:** `(ℝ⁺ ∪ {+∞}, min, +, +∞, 0)`
- **Properties:** commutative, idempotent, complete, star
- **Use case:** Primary dispatch ranking, shortest-path Viterbi, beam pruning
- **Consumers:** `wfst.rs`, `lattice.rs`, `prediction.rs`, `compose.rs`, `cost_benefit.rs`, `decision_tree.rs`

### 1.2 CountingWeight
- **Algebra:** `(ℕ, +, ×, 0, 1)` with saturating arithmetic
- **Properties:** commutative, NOT idempotent, star (saturates for non-zero)
- **Use case:** Ambiguity detection (count > 1 = ambiguous)
- **Consumers:** `prediction.rs`, `lint.rs`, `cost_benefit.rs`

### 1.3 BooleanWeight
- **Algebra:** `({false, true}, ∨, ∧, false, true)`
- **Properties:** commutative, idempotent, complete, star (always true)
- **Use case:** Dead-rule detection, reachability analysis
- **Consumers:** `pipeline.rs`, `lint.rs`

### 1.4 EditWeight
- **Algebra:** `(ℕ ∪ {∞}, min, +, ∞, 0)`
- **Properties:** commutative, idempotent, complete, star (always zero edits)
- **Use case:** Minimum-cost error recovery (edit distance)
- **Consumers:** `recovery.rs`

### 1.5 ProductWeight\<S1, S2\>
- **Algebra:** Component-wise `(S1 × S2, plus₁×plus₂, times₁×times₂, (0₁,0₂), (1₁,1₂))`
- **Properties:** Inherits from components (idempotent if both idempotent, etc.)
- **Use case:** Multi-criteria optimization
- **Consumers:** `cost_benefit.rs` (`Tropical×Tropical`), `recovery.rs` (`Tropical×Edit`)

### 1.6 ContextWeight
- **Algebra:** `(𝒫(128), ∪, ∩, ∅, U)` — 128-bit bitset powerset
- **Properties:** commutative, idempotent, complete, star (always universal)
- **Use case:** Follow-set tightening, rule participation tracking
- **Consumers:** `recovery.rs`

### 1.7 ComplexityWeight
- **Algebra:** `(ℕ ∪ {∞}, min, max, ∞, 0)` — bottleneck semiring
- **Properties:** commutative, idempotent, complete, star (always zero)
- **Use case:** Lookahead depth bounding, parsing effort estimation
- **Consumers:** `trampoline.rs`

### 1.8 LogWeight *(feature: `wfst-log`)*
- **Algebra:** `(ℝ⁺ ∪ {+∞}, logsumexp, +, +∞, 0)` — negative log-probabilities
- **Properties:** commutative, NOT idempotent, complete, star (`-ln(1/(1-p))`)
- **Use case:** Forward-backward scoring, weight training
- **Consumers:** `training.rs`, `log_push.rs`

### 1.9 EntropyWeight *(feature: `wfst-log`)*
- **Algebra:** `(ℝ×ℝ, ⊕, ⊗, (∞,0), (0,0))` — expectation semiring
- **Properties:** commutative, NOT idempotent, complete, star (fixed-point derivation)
- **Use case:** Shannon entropy computation, adaptive beam width
- **Consumers:** `wfst.rs` (`compute_entropy`)

### 1.10 NbestWeight\<N\>
- **Algebra:** `(Sorted[N], merge, cross, [], [(0,0)])` — N-best paths
- **Properties:** commutative, NOT idempotent, NOT complete
- **Use case:** Lazy disambiguation, confidence gap computation
- **Consumers:** `wfst.rs`, `trampoline.rs`

### 1.11 ViterbiWeight *(new)*
- **Algebra:** `([0,1], max, ·, 0, 1)` — probability-domain most-likely-path
- **Properties:** commutative, idempotent, complete, star (always 1.0)
- **Use case:** Direct probability I/O, recovery confidence scoring
- **Isomorphism:** `TropicalWeight` via `w = -ln(p)` (bidirectional conversion provided)

### 1.12 ArcticWeight *(new)*
- **Algebra:** `(ℝ ∪ {-∞}, max, +, -∞, 0)` — dual of tropical (longest path)
- **Properties:** commutative, idempotent, complete, star (`0` if `a ≤ 0`)
- **Use case:** Critical-path analysis, maximum-benefit optimization, worst-case propagation

### 1.13 FuzzyWeight *(new)*
- **Algebra:** `([0,1], max, min, 0, 1)` — possibilistic/confidence semiring
- **Properties:** commutative, idempotent, complete, star (always 1.0)
- **Use case:** Dispatch confidence scoring, recovery plausibility, lint true-positive likelihood

### 1.14 TruncationWeight\<K\> *(new)*
- **Algebra:** `({0,...,K}, max, min(a+b,K))` — bounded ambiguity counting
- **Properties:** commutative, idempotent, complete
- **Use case:** Tiered ambiguity severity (1/2/3/K+)
- **Note:** `zero = one = 0`; does NOT satisfy full zero-annihilation axiom

### 1.15 AmplitudeWeight *(feature: `quantum`)*
- **Algebra:** `(ℂ, +, ×, 0+0i, 1+0i)` — complex amplitude semiring
- **Properties:** commutative, NOT idempotent (`z + z = 2z ≠ z`), NOT complete, NOT star
- **Use case:** Quantum CTMC simulation (MeTTaIL-Gillespie), amplitude propagation through reaction lattices
- **Measurement:** Born rule `|z|²` collapses to classical probability
- **Caveat:** Viterbi does not apply directly; use forward propagation + Born-rule measurement, or `ProductWeight<AmplitudeWeight, TropicalWeight>` with a classical priority channel
- **Dependencies:** `num-complex = "0.4"` (feature-gated)
- **Conversions:** `from_probability(p)` → `√p + 0i`; `to_probability()` → `|z|²`; `from_log_weight(w)` (requires `quantum` + `wfst-log`)

## 2. Deferred Semirings

### D1. Formal Language Semiring `(𝒫(Σ*), ∪, ·, ∅, {ε})`
- **Rationale:** Not `Copy` (heap-allocated sets). Infinite carrier for recursive
  grammars. Undecidable equality for context-free languages. Existing FIRST/FOLLOW
  sets provide the practical finite approximation.
- **MeTTaIL-Gillespie Connection:** The Gillespie fuzzer
  (`MeTTaIL-Gillespie/src/fuzzer.rs`) performs weighted grammar enumeration —
  generating terms from production rules with associated weights. This is
  semantically a weighted variant of the formal language semiring: each production
  contributes a weighted set of strings, and the fuzzer explores the language by
  sampling from these weighted sets. A future symbolic representation (e.g.,
  weighted regular expressions or weighted DFA carrier) could formalize this
  connection and enable:
  1. Exact coverage analysis: which subset of the language has been explored
  2. Completeness bounds: probability mass of unexplored language regions
  3. Grammar equivalence: verify that a spec and its implementation generate
     the same weighted language (connects to weighted bisimilarity)
- **Revisit when:** Symbolic representation (e.g., regex/DFA carrier) designed and
  `Copy` bound relaxed; or when the MeTTaIL-Gillespie fuzzer needs formal
  coverage guarantees beyond sampling-based exploration.

### D2. Łukasiewicz Semiring `([0,1], min, max{a+b-1, 0})`
- **Rationale:** Many-valued logic with bounded conjunction. No current pipeline
  consumer needs "degree of grammaticality" semantics.

### D3. Relation Semiring `(Rel_A, ∪, ∘, ∅, I_A)`
- **Rationale:** Not `Copy` (`Set<(A,A)>` carrier). The `DispatchAction` structure
  already encodes input-output transductions concretely.

### D4. Matrix Semiring `(S^{n×n}, ⊕, ⊗, 0, 1)`
- **Rationale:** Implemented as the standalone algorithm `matrix_star()` instead of
  a semiring type. This avoids the `Copy` constraint for non-trivial matrix sizes
  while providing the same all-pairs computation capability.

### D5–D7. Polynomial / Division / Fusion Semirings
- **Rationale:** No parser-generator application. Polynomial requires variable-length
  data (not `Copy`). Division is number-theoretic. Fusion is morphological.

## 3. Rejected / Subsumed Semirings

| Candidate                           | Subsumed By                    | Reason                                                   |
|-------------------------------------|--------------------------------|----------------------------------------------------------|
| Standard Arithmetic `(ℕ/ℤ/ℝ, +, ·)` | CountingWeight / LogWeight     | No new functionality                                     |
| Powerset Lattice `(𝒫(S), ∪, ∩)`     | ContextWeight                  | Already a 128-bit powerset lattice                       |
| Boolean Algebra                     | BooleanWeight                  | Identical                                                |
| Probability `(ℝ≥0, +, ·, 0, 1)`     | LogWeight                      | Numerically unstable; LogWeight is the stable version    |
| Bottleneck `(ℝ, max, min)`          | FuzzyWeight + ComplexityWeight | Covered by both                                          |
| Equivalence / Mod2 / Wrappers       | —                              | Utility newtypes, no new semiring functionality          |
| Extended Naturals `(ℕ∪{∞}, +, ·)`   | CountingWeight                 | Saturating arithmetic at `u64::MAX`                      |
| Multiset / Cardinal / Burnside      | —                              | No parser-generator application                          |
| Endomorphism `End(M)`               | —                              | Not `Copy` (function objects)                            |
| Directed Semiring                   | matrix_star approach           | Subsumed by matrix-over-semiring                         |
| Conway Semiring (trait)             | —                              | All our complete star semirings are automatically Conway |

## 4. Trait Hierarchy

```
Semiring (existing base trait)
  ├── DetectableZero      (marker: is_zero() is O(1) and reliable)
  ├── IdempotentSemiring  (marker: a ⊕  a = a)
  ├── CompleteSemiring    (marker: infinite sums converge)
  └── StarSemiring        (Kleene closure: a* = 1 ⊕  a ⊕  a² ⊕  ...)
        ├── fn star(&self) -> Self
        └── fn plus_star(&self) -> Self  (default: a ⊗  a*)
```

### Implementation Matrix

| Type             | DetectableZero | Idempotent | Complete | Star |
|------------------|:--------------:|:----------:|:--------:|:----:|
| TropicalWeight   |       ✓        |     ✓      |    ✓     |  ✓   |
| CountingWeight   |       ✓        |     —      |    —     |  ✓¹  |
| BooleanWeight    |       ✓        |     ✓      |    ✓     |  ✓   |
| EditWeight       |       ✓        |     ✓      |    ✓     |  ✓   |
| ProductWeight    |       ✓²       |     ✓²     |    ✓²    |  ✓²  |
| ContextWeight    |       ✓        |     ✓      |    ✓     |  ✓   |
| ComplexityWeight |       ✓        |     ✓      |    ✓     |  ✓   |
| LogWeight        |       ✓        |     —      |    ✓     |  ✓   |
| EntropyWeight    |       ✓        |     —      |    ✓     |  ✓   |
| NbestWeight      |       ✓        |     —      |    —     |  —   |
| ViterbiWeight    |       ✓        |     ✓      |    ✓     |  ✓   |
| ArcticWeight     |       ✓        |     ✓      |    ✓     |  ✓   |
| FuzzyWeight      |       ✓        |     ✓      |    ✓     |  ✓   |
| TruncationWeight |       ✓        |     ✓      |    ✓     |  —   |
| AmplitudeWeight  |       ✓        |     —      |    —     |  —   |

¹ Saturates at `u64::MAX` for non-zero values
² Conditional on both components implementing the trait

### Generic Algorithm: `matrix_star()`

```rust
pub fn matrix_star<W: StarSemiring>(adj: &[Vec<W>]) -> Vec<Vec<W>>
```

Generalized Floyd-Warshall (Lehmann 1977, Byorgey 2016) computes the transitive
closure of an n×n adjacency matrix over any star semiring in O(n³).

**Semiring-specific interpretations:**
- `BooleanWeight` → reachability (reflexive-transitive closure)
- `TropicalWeight` → all-pairs shortest paths
- `ArcticWeight` → all-pairs longest paths
- `CountingWeight` → path counts (saturates for reachable pairs)
- `EditWeight` → all-pairs minimum edit distance

## 5. Sources

- CMU CDM: Sutner, "Semirings, Rings, Fields" (2025)
- Wikipedia: "Semiring" — comprehensive examples, star/Conway/complete semirings
- Haskell `semirings-0.7` package — `Data.Semiring`, `Data.Star` typeclass design
- Byorgey (2016): "The network reliability problem and star semirings"
- Li & Eisner (2009): "First- and Second-Order Expectation Semirings"
- Goodman (1999): "Semiring Parsing"
- Foundations of Computational Linguistics (ch. 46–47): semiring parsing for CYK/Viterbi/Inside
- Lehmann (1977): "Algebraic structures for transitive closure" (generalized Floyd-Warshall)
