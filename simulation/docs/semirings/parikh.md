# ParikhWeight and Parikh Image Automata

## What Is It?

The `ParikhWeight<D>` is a semiring whose carrier is a D-dimensional vector of `u64` counters. Addition (⊕) is component-wise maximum, and multiplication (⊗) is component-wise addition. It is used for tracking resource consumption, transition counts, and symbol frequencies along automaton paths.

Located in `simulation/src/semiring/parikh.rs`.

## What Does It Do?

The Parikh weight semiring tracks **how many times** each of D distinct events (rule firings, channel operations, resource allocations) occurs along an execution path. The ⊕ operation aggregates parallel paths by taking the component-wise maximum (worst-case resource usage), while ⊗ accumulates counts along a sequential path.

## Why Was It Chosen?

### Parikh's Theorem

Parikh (1966) proved a foundational result in formal language theory:

**Theorem (Parikh (1966)).** The Parikh image of every context-free language is a **semilinear set**.

The Parikh image of a word w over alphabet Σ = {a₁, ..., aₙ} is the vector (|w|_{a₁}, ..., |w|_{aₙ}) counting occurrences of each letter. A semilinear set is a finite union of linear sets, where each linear set has the form:

```
L(b, P) = { b + k₁·p₁ + k₂·p₂ + ... + kₘ·pₘ  |  kᵢ ∈ ℕ }
```

for a base vector b and period vectors p₁, ..., pₘ.

This theorem means that the "counting behavior" of any context-free language can be described by a finite number of linear constraints. For MeTTaIL languages (which are at most context-free in their rewrite behavior), this provides a complete characterization of which rule-firing patterns are achievable.

### Application to Coverage Analysis

By assigning each rewrite rule a unique dimension in the Parikh weight, the Parikh image of the rewrite trace reveals exactly how many times each rule can fire. The semilinear set of achievable Parikh vectors characterizes the space of all possible rule-firing patterns, enabling:

- **Completeness checking**: "Can every rule fire at least once?"
- **Boundedness checking**: "Is the total number of rewrites bounded?"
- **Balance checking**: "Do sends and receives on a channel always match?"

## Mathematical Definition

### Carrier

```
S = ℕ^D = {(c₁, c₂, ..., c_D) : cᵢ ∈ {0, 1, 2, ...}}
```

In the implementation, ℕ is approximated by `u64` with saturating arithmetic.

### Operations

**Plus (⊕): component-wise maximum**

```
(a₁, ..., a_D) ⊕ (b₁, ..., b_D) = (max(a₁, b₁), ..., max(a_D, b_D))
```

**Intuition:** When merging parallel paths, we record the worst-case (maximum) resource usage across all alternatives.

**Times (⊗): component-wise addition**

```
(a₁, ..., a_D) ⊗ (b₁, ..., b_D) = (a₁ + b₁, ..., a_D + b_D)
```

**Intuition:** When sequencing two path segments, resource counts accumulate.

**Zero (0̄) = One (1̄) = (0, 0, ..., 0)**

This is a degenerate case where 0̄ = 1̄ = [0; D]. This is valid because:
- max(0, a) = a (zero is identity for ⊕)
- a + 0 = a (zero is identity for ⊗)

### Properties

**Idempotent:** a ⊕ a = max(a, a) = a. This means ParikhWeight satisfies the `IdempotentSemiring` marker trait, guaranteeing convergence of fixpoint algorithms.

**Partially ordered:** The component-wise ≤ relation forms a partial order:
```
a ≤ b  iff  ∀ i: aᵢ ≤ bᵢ
```

This is used by `ParikhWeight::leq()` for containment checks.

**Saturating arithmetic:** The ⊗ operation uses `u64::saturating_add` to prevent overflow:
```
u64::MAX + 1 = u64::MAX  (not 0)
```

### Const Generic Dimensionality

The `D` parameter is a const generic, enabling stack allocation for common cases:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParikhWeight<const D: usize> {
    pub counters: [u64; D],
}
```

Typical usage: `ParikhWeight<3>` for a language with 3 rule categories, `ParikhWeight<8>` for one with 8 distinct resources. The compile-time dimensionality avoids heap allocation and enables the compiler to optimize inner loops.

## Key Methods

### Unit Vectors

```rust
// Unit vector: 1 in dimension dim, 0 elsewhere
ParikhWeight::<3>::unit(1)  // → [0, 1, 0]

// Scaled unit vector: count in dimension dim, 0 elsewhere
ParikhWeight::<3>::scaled_unit(1, 5)  // → [0, 5, 0]
```

### Norms

```rust
let w = ParikhWeight::<3>::new([1, 5, 3]);
w.total()           // L₁ norm: 1 + 5 + 3 = 9
w.max_component()   // L∞ norm: max(1, 5, 3) = 5
```

### Partial Order

```rust
let a = ParikhWeight::<3>::new([1, 2, 3]);
let b = ParikhWeight::<3>::new([2, 3, 4]);
a.leq(&b)  // true: all components of a ≤ corresponding components of b
b.leq(&a)  // false: 2 > 1
```

## Semilinear Sets

A semilinear set is a finite union of linear sets (see [automata/parikh-automaton.md](../automata/parikh-automaton.md) for the full Parikh automaton documentation):

```
SemilinearSet<D> = ∪ᵢ LinearSet<D>ᵢ

LinearSet<D> = { base + k₁·p₁ + ... + kₘ·pₘ | kⱼ ∈ ℕ }
```

The `ParikhWeight<D>` type serves as the element type for both the base and period vectors of linear sets. The `LinearSet::contains()` method checks membership by solving the integer linear system:

```
PROCEDURE LinearSet.contains(target):
    IF NOT base ≤ target THEN RETURN false
    diff ← target - base
    IF periods is empty THEN RETURN diff == 0

    IF |periods| == 1 THEN
        // Check if diff is a non-negative scalar multiple of periods[0]
        RETURN ∃ k ∈ ℕ: diff = k · periods[0]

    ELSE
        // Bounded search over coefficient space
        RETURN bounded_search(diff, periods, max_coeff)
```

## Use in Simulation

### Rule Firing Counts

Assign dimension i to rewrite rule i. Each transition in the Parikh automaton carries a unit vector `ParikhWeight::unit(i)` for the rule it represents. After simulation, the accumulated weight tells how many times each rule fired.

### Channel Balance

For a process algebra with send/receive channels, assign dimension 2i to "send on channel i" and dimension 2i+1 to "receive on channel i". The Parikh weight tracks the balance; a balanced execution has equal counts in each send/receive pair.

### Boundedness

If the semilinear set projection has no period vectors (all linear sets are singletons), the system is bounded: there is a finite set of achievable resource vectors. If period vectors are present, the system can grow unboundedly in those dimensions.

## References

- Parikh, R.J. (1966). "On Context-Free Languages." Journal of the ACM, 13(4), pp. 570-581.
- Ginsburg, S. and Spanier, E.H. (1966). "Semigroups, Presburger Formulas, and Languages." Pacific Journal of Mathematics, 16(2), pp. 285-296.
- Klaedtke, F. and Ruess, H. (2003). "Monadic Second-Order Logics with Cardinalities." Proceedings of ICALP, pp. 681-696.
