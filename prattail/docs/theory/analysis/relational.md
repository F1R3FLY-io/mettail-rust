# Relational Semiring Analysis

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `relational`                           |
| Source file    | `prattail/src/relational.rs` (~407 lines) |
| Pipeline phase | Post-WPDS analysis (when enabled)      |
| Lint codes     | (indirect, via WPDS verification)      |

## Rationale

Standard semirings like `TropicalWeight` and `CountingWeight` implement `Copy` and model scalar quantities. The relational weight domain operates over binary relations on a finite set `G`, where combine is union and extend is relational composition. This is the weight domain used by Boolean program analysis (SLAM/BLAST-style): weights represent sets of (source, target) state pairs encoding state transformations. Since `HashSet<(G, G)>` is heap-allocated and cannot implement `Copy`, a separate `HeapSemiring` trait mirrors the `Semiring` interface without the `Copy` bound. In PraTTaIL, relational weights model the operational semantics of `language!`-defined grammars as WPDS rules weighted by state transformations.

## Theoretical Foundations

**Definition (Relational Weight Domain, Reps et al. 2007, Definition 7).** The relational weight domain on a finite set `G` is the semiring `(2^{G x G}, union, ;, emptyset, id)`:
- Carrier: `2^{G x G}` -- sets of (source, target) state pairs
- Plus (`oplus`): set union -- any pair reachable via either relation
- Times (`otimes`): relational composition -- `(a,c) in R_1 ; R_2 iff exists b: (a,b) in R_1 and (b,c) in R_2`
- Zero: `emptyset` -- no state pairs (unreachable)
- One: `id = {(g, g) | g in G}` -- identity relation (no state change)

**Theorem (Semiring Laws).** The relational domain satisfies all semiring axioms:
1. `(2^{G x G}, union, emptyset)` is a commutative monoid (additive)
2. `(2^{G x G}, ;, id)` is a monoid (multiplicative)
3. Composition distributes over union: `R_1 ; (R_2 union R_3) = (R_1 ; R_2) union (R_1 ; R_3)`
4. Zero annihilates: `R ; emptyset = emptyset ; R = emptyset`

**Definition (HeapSemiring).** A trait mirroring `Semiring` without the `Copy` bound:

    trait HeapSemiring: Clone + Debug + PartialEq + Send + Sync {
        fn zero() -> Self;
        fn one() -> Self;
        fn plus(&self, other: &Self) -> Self;
        fn times(&self, other: &Self) -> Self;
        fn is_zero(&self) -> bool;
        fn is_one(&self) -> bool;
        fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
    }

**Definition (Relational Operations).**
- `domain(R) = {a | exists b: (a,b) in R}` -- set of source elements
- `range(R) = {b | exists a: (a,b) in R}` -- set of target elements
- `image(R, a) = {b | (a,b) in R}` -- forward image of element `a`
- `preimage(R, b) = {a | (a,b) in R}` -- backward image of element `b`

### References

1. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*, Definition 7.
2. Ball, T. & Rajamani, S.K. (2001). "The SLAM toolkit." *CAV*.
3. Henzinger, T.A. et al. (2002). "Lazy abstraction." *POPL*.

## Algorithm Pseudocode

### 1. Relational Composition (Times)

```
FUNCTION times(R1, R2):
    result := empty set
    FOR EACH (a, b) in R1:
        FOR EACH (b', c) in R2:
            IF b == b':
                result.insert((a, c))
    RETURN RelationalWeight(result, universe)
```

### 2. Relational Union (Plus)

```
FUNCTION plus(R1, R2):
    result := R1.pairs UNION R2.pairs
    RETURN RelationalWeight(result, universe)
```

### 3. Identity Relation Construction

```
FUNCTION identity(universe):
    pairs := { (g, g) | g in universe }
    RETURN RelationalWeight(pairs, universe)
```

## Complexity Analysis

| Operation    | Time           | Space            |
|--------------|----------------|------------------|
| `plus`       | O(P_1 + P_2)   | O(P_1 + P_2)    |
| `times`      | O(P_1 . P_2)   | O(|G|^2)         |
| `identity`   | O(|G|)         | O(|G|)           |
| `singleton`  | O(1)           | O(1)             |
| `domain`     | O(P)           | O(|G|)           |
| `range`      | O(P)           | O(|G|)           |
| `image`      | O(P)           | O(|G|)           |
| `preimage`   | O(P)           | O(|G|)           |
| `is_one`     | O(|G|)         | O(1)             |
| `is_zero`    | O(1)           | O(1)             |

Where P = number of pairs in the relation, P_1/P_2 = pairs in each operand, |G| = size of the universe.

## Relational Composition Diagram

```
  Relational Composition: R₁ ; R₂

  R₁ = {(0,1), (0,2)}          R₂ = {(1,2), (2,0)}

  State 0 ──▶ State 1          State 1 ──▶ State 2
  State 0 ──▶ State 2          State 2 ──▶ State 0

  R₁ ; R₂:
    (0,1) ; (1,2) = (0,2)   ✓  (matching intermediate: 1)
    (0,2) ; (2,0) = (0,0)   ✓  (matching intermediate: 2)

  Result: {(0,2), (0,0)}

  ┌───┐         ┌───┐         ┌───┐
  │ 0 │──R₁───▶│ 1 │──R₂───▶│ 2 │
  │   │         └───┘         └───┘
  │   │──R₁───▶┌───┐──R₂───▶┌───┐
  └───┘         │ 2 │         │ 0 │
                └───┘         └───┘

  Composed: 0 ──(R₁;R₂)──▶ 2, 0 ──(R₁;R₂)──▶ 0
```

## Semiring Laws Diagram

```
  ┌──────────────────────────────────────────────────────────┐
  │              Relational Semiring (2^{G×G}, ∪, ;, ∅, id) │
  │                                                          │
  │  Plus (∪):                    Times (;):                 │
  │  ┌───┐   ┌───┐   ┌───┐      ┌───┐   ┌───┐   ┌───┐    │
  │  │R₁ │ ∪ │R₂ │ = │R₃ │      │R₁ │ ; │R₂ │ = │R₃ │    │
  │  └───┘   └───┘   └───┘      └───┘   └───┘   └───┘    │
  │  (set union)                  (relational composition)  │
  │                                                          │
  │  Zero (∅):  annihilates ;     One (id):  neutral for ;  │
  │  R ; ∅ = ∅ ; R = ∅           R ; id = id ; R = R       │
  │                                                          │
  │  Distributivity:                                         │
  │  R₁ ; (R₂ ∪ R₃) = (R₁ ; R₂) ∪ (R₁ ; R₃)             │
  └──────────────────────────────────────────────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

The relational module does not have a direct pipeline bridge function. Instead, it provides the weight domain infrastructure for:

- **HeapWpds<W>**: A Weighted Pushdown System using heap-allocated weight domains, mirroring `Wpds<W>` with `HeapSemiring` bound instead of `Semiring`.
- **EWPDS integration**: When the `relational` feature is enabled alongside `wpds-extended`, the EWPDS merge functions can operate over relational weights, modeling state transformations with proper local/global variable scoping.

### Lint Emission

Relational weights contribute indirectly to lint codes via WPDS verification. When the relational domain is used, safety checks (S01/S02) operate over state-transformation pairs rather than scalar reachability, providing more precise diagnostics.

## Rust Implementation Notes

| Type                    | Role                                                     |
|-------------------------|----------------------------------------------------------|
| `HeapSemiring`          | Trait: non-Copy semiring (zero, one, plus, times, is_zero, is_one, approx_eq) |
| `RelationalWeight<G>`   | Binary relation `HashSet<(G, G)>` with universe `Vec<G>` |
| `HeapWpds<W>`           | WPDS with HeapSemiring weights                           |
| `HeapWpdsRule<W>`       | PDS rule variants (Pop, Replace, Push) with HeapSemiring weights |

## Worked Example

Model a simple 3-state abstract domain.

**Step 1: Define universe and relations.**

```
Universe G = {0, 1, 2}
Identity = {(0,0), (1,1), (2,2)}
```

**Step 2: Build state transformations.**

Rule A transforms state 0 to state 1: `R_A = {(0, 1)}`
Rule B transforms state 1 to state 2: `R_B = {(1, 2)}`

**Step 3: Compose (sequential application).**

```
R_A ; R_B = {(a, c) | exists b: (a,b) in R_A and (b,c) in R_B}
         = {(0, 2)}   // 0 -> 1 via R_A, then 1 -> 2 via R_B
```

**Step 4: Union (alternative paths).**

```
R_A ∪ R_B = {(0, 1), (1, 2)}
```

This represents: from state 0, we can reach state 1; from state 1, we can reach state 2.

**Step 5: Verify semiring laws.**

```
// Identity is neutral
R_A ; id = {(0, 1)} ; {(0,0), (1,1), (2,2)} = {(0, 1)}  ✓
id ; R_A = {(0,0), (1,1), (2,2)} ; {(0, 1)} = {(0, 1)}  ✓

// Zero annihilates
R_A ; ∅ = ∅  ✓

// Distributivity
R_A ; (R_B ∪ R_C) = (R_A ; R_B) ∪ (R_A ; R_C)  ✓
```

**Step 6: WPDS integration.**

A `HeapWpdsRule::Replace` with weight `R_A` models a category transition that transforms abstract state 0 to state 1. Poststar accumulates relational compositions along execution paths, yielding the net state transformation from initial to final configuration.

## References

1. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*.
2. Ball, T. & Rajamani, S.K. (2001). "The SLAM toolkit." *CAV*.
3. Henzinger, T.A. et al. (2002). "Lazy abstraction." *POPL*.
4. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.
5. Reps, T., Horwitz, S. & Sagiv, M. (1995). "Precise interprocedural dataflow analysis via graph reachability." *POPL*.
