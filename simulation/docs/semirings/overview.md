# Semirings: Algebraic Framework for Weighted Automata

## What Is It?

A **semiring** is an algebraic structure (S, ⊕, ⊗, 0̄, 1̄) consisting of a carrier set S, two binary operations (addition ⊕ and multiplication ⊗), and two distinguished elements (additive identity 0̄ and multiplicative identity 1̄). Semirings provide a unifying algebraic framework for weighted automata, enabling a single algorithmic pipeline to solve diverse problems (shortest paths, counting, probability, resource tracking) by simply varying the semiring.

The simulation crate defines four new semiring types that extend the base semirings in `prattail`:

| Semiring            | Carrier              | ⊕                        | ⊗                  | 0̄       | 1̄      |
|---------------------|----------------------|--------------------------|--------------------|---------|--------|
| `ExpectationWeight` | (f64, f64)           | logsumexp / weighted avg | add / add          | (+∞, 0) | (0, 0) |
| `ParikhWeight<D>`   | [u64; D]             | component-wise max       | component-wise add | [0; D]  | [0; D] |
| `StreamingWeight`   | (n, μ, M₂, min, max) | parallel merge           | sequential merge   | empty   | empty  |
| `FreeWeight`        | AST (FreeExpr)       | symbolic plus            | symbolic times     | Zero    | One    |

## What Does It Do?

Each semiring provides `plus`, `times`, `zero`, and `one` operations that can be plugged into any weighted automaton algorithm. This means the same shortest-path algorithm, when instantiated with different semirings, computes:

- Shortest path (TropicalWeight)
- Most probable path (LogWeight)
- Expected cost (ExpectationWeight)
- Maximum resource usage (ParikhWeight)
- Running statistics (StreamingWeight)
- Symbolic provenance (FreeWeight)

## Why Semirings?

### The Unification Insight

Mohri (2002) demonstrated that most problems in weighted automata (shortest-distance, string-to-weight mapping, composition, determinization) can be expressed as generic algorithms parameterized by a semiring. The semiring axioms guarantee that these algorithms are correct for any conforming implementation.

This is profoundly economical: rather than writing separate algorithms for shortest path, probability, resource counting, etc., we write each algorithm **once** and instantiate it with the appropriate semiring.

### Semiring Axioms

∀ a, b, c ∈ S:

```
Associativity of ⊕:     (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
Commutativity of ⊕:     a ⊕ b = b ⊕ a
Identity of ⊕:          a ⊕ 0̄ = a
Associativity of ⊗:     (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
Identity of ⊗:          a ⊗ 1̄ = a = 1̄ ⊗ a
Left distributivity:    a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
Right distributivity:   (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
Annihilation by 0̄:      a ⊗ 0̄ = 0̄ = 0̄ ⊗ a
```

### Connection to Shortest-Path Algorithms

Consider the single-source shortest path problem. Dijkstra's algorithm can be viewed as computing the semiring sum (⊕ = min) of all path weights (⊗ = +) from the source to each vertex. The tropical semiring (ℝ⁺ ∪ {+∞}, min, +, +∞, 0) makes this explicit:

```
distance(s, t) = ⊕ over all paths p from s to t: ⊗ over all edges e in p: weight(e)
               = min over all paths p: Σ edge weights
```

By replacing the tropical semiring with the expectation semiring, the same algorithm computes expected costs. By using the Parikh semiring, it computes maximum resource usage along any path. The algorithm is identical; only the semiring changes.

## The Semiring Trait

The `Semiring` trait in `prattail` requires `Copy`:

```rust
pub trait Semiring: Clone + Copy + Debug + PartialEq + Send + Sync + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

The `Copy` bound enables efficient pass-by-value in automaton algorithms, avoiding reference counting overhead. This is appropriate for small, fixed-size carriers like `f64`, `(f64, f64)`, and `[u64; D]`.

## The SemiringRef Trait for Non-Copy Carriers

For semirings whose carrier type requires heap allocation (like `FreeWeight` with its AST of symbolic expressions), the `SemiringRef` trait drops the `Copy` requirement:

```rust
pub trait SemiringRef: Clone + Debug + PartialEq + Send + Sync + 'static {
    fn zero_ref() -> Self;
    fn one_ref() -> Self;
    fn plus_ref(&self, other: &Self) -> Self;
    fn times_ref(&self, other: &Self) -> Self;
    fn is_zero_ref(&self) -> bool;
    fn is_one_ref(&self) -> bool;
}
```

All operations take `&self` references and return owned values. This avoids unnecessary cloning while still satisfying the semiring axioms.

### Design Rationale

The two-trait design (Semiring + SemiringRef) reflects a practical tension in Rust:

- **Automaton algorithms want Copy**: they manipulate weights frequently, storing them in arrays and passing them to functions. Copy semantics eliminate clone overhead.
- **Some carriers are not Copy**: symbolic expressions (trees of `Box<FreeExpr>`) and large vectors cannot be copied cheaply.

Rather than forcing all semirings into one trait (either penalizing Copy types with unnecessary references or requiring non-Copy types to implement Copy unsafely), the system provides both traits and lets each semiring choose the appropriate one.

## Trait Hierarchy Extensions

The `prattail` crate defines additional marker traits:

| Trait                | Meaning                                | Examples                        |
|----------------------|----------------------------------------|---------------------------------|
| `DetectableZero`     | `is_zero()` is O(1) and reliable       | All built-in semirings          |
| `IdempotentSemiring` | `a ⊕ a = a` for all a                  | Tropical, Boolean, ParikhWeight |
| `CompleteSemiring`   | Infinite sums are well-defined         | All idempotent semirings        |
| `StarSemiring`       | Kleene closure `a* = 1̄ ⊕ a ⊕ a² ⊕ ...` | Tropical, Boolean               |

`IdempotentSemiring` is particularly important: it guarantees that fixpoint algorithms (like Ascent's Datalog evaluation) converge. Non-idempotent semirings (like `StreamingWeight`) require explicit convergence criteria.

## The Four Simulation Semirings

### ExpectationWeight

Combines a log-domain weight with an expected cost. Used for risk-aware analysis and gradient computation. See [expectation.md](expectation.md).

### ParikhWeight<D>

Fixed-dimensional counter vectors. Used for resource counting, transition frequency analysis, and Parikh image computation. See [parikh.md](parikh.md).

### StreamingWeight

Online statistics (mean, variance, min, max) via Welford's algorithm. Used for runtime monitoring and anomaly detection. See [streaming.md](streaming.md).

### FreeWeight

Symbolic expression trees. The universal (initial) semiring. Used for provenance tracking and symbolic computation. See [free.md](free.md).

## References

- Mohri, M. (2002). "Semiring Frameworks and Algorithms for Shortest-Distance Problems." Journal of Automata, Languages and Combinatorics, 7(3), pp. 321-350.
- Kuich, W. and Salomaa, A. (1986). Semirings, Automata, Languages. Springer-Verlag.
- Goodman, J. (1999). "Semiring Parsing." Computational Linguistics, 25(4), pp. 573-605.
- Droste, M., Kuich, W., and Vogler, H. (2009). Handbook of Weighted Automata. Springer.
