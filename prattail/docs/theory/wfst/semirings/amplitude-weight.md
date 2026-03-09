# Amplitude Semiring: AmplitudeWeight

## 1. Intuition & Motivation

The amplitude semiring provides a *quantum interference algebra* for
complex-valued amplitude computation.  Unlike classical semirings
where parallel paths are resolved by selection (min, max) or
accumulation (addition), the amplitude semiring uses *complex
addition* -- enabling constructive and destructive interference
between paths.

The two fundamental operations capture quantum composition rules:

- **Combining alternatives** (parallel paths) uses complex addition --
  amplitudes interfere, potentially cancelling or reinforcing each
  other.
- **Chaining sequential segments** (a path through multiple arcs)
  uses complex multiplication -- amplitudes compose by multiplying
  magnitudes and adding phases.

Within PraTTaIL, the amplitude semiring enables quantum continuous-time
Markov chain (CTMC) simulation for the MeTTaIL-Gillespie integration:

```
amplitude z = re + im*i
probability = |z|² = re² + im²    (Born rule)
```

This is fundamentally different from classical semirings because
*paths can cancel*.  Two paths with amplitudes `0.5 + 0i` and
`-0.5 + 0i` produce zero total amplitude -- complete destructive
interference -- even though each path individually has non-zero
probability.

**Feature gate**: AmplitudeWeight requires the `quantum` feature flag
and depends on `num-complex = "0.4"`.

---

## 2. Formal Definition

The amplitude semiring is the algebraic structure

```
Q  =  ( C,  +,  x,  0+0i,  1+0i )
```

where:

| Component                   | Symbol | Concrete value              | Meaning                              |
|-----------------------------|--------|-----------------------------|--------------------------------------|
| Carrier set                 | K      | C (complex numbers)         | All complex amplitudes               |
| Addition (⊕)                | +      | (a+bi) + (c+di) = (a+c)+(b+d)i | Quantum interference           |
| Multiplication (⊗)          | x      | (a+bi)(c+di) = (ac-bd)+(ad+bc)i | Sequential amplitude composition|
| Additive identity (0-bar)   | 0+0i   | `Complex64::new(0.0, 0.0)`  | No amplitude (unreachable)           |
| Multiplicative identity (1-bar) | 1+0i | `Complex64::new(1.0, 0.0)` | Unit amplitude (no phase change)     |

Technically, this is a *ring* (it has additive inverses: `-z`), but
it satisfies all semiring axioms and is used as such in the PraTTaIL
framework.  The ring structure provides the destructive interference
that distinguishes quantum from classical computation.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let z1 = 0.6 + 0.8i, z2 = -0.3 + 0.4i, z3 = 0.5 + 0.0i.

### (A1) Associativity of ⊕

```
(z1 ⊕  z2) ⊕  z3
    =  ((0.6 + 0.8i) + (-0.3 + 0.4i)) + (0.5 + 0.0i)
    =  (0.3 + 1.2i) + (0.5 + 0.0i)
    =  0.8 + 1.2i

z1 ⊕  (z2 ⊕  z3)
    =  (0.6 + 0.8i) + ((-0.3 + 0.4i) + (0.5 + 0.0i))
    =  (0.6 + 0.8i) + (0.2 + 0.4i)
    =  0.8 + 1.2i   ✓
```

Holds because complex addition is associative.

### (A2) Commutativity of ⊕

```
z1 ⊕  z2  =  (0.6 + 0.8i) + (-0.3 + 0.4i)  =  0.3 + 1.2i
z2 ⊕  z1  =  (-0.3 + 0.4i) + (0.6 + 0.8i)  =  0.3 + 1.2i   ✓
```

Holds because complex addition is commutative.

### (A3) ⊕  Identity

```
0-bar ⊕  z1  =  (0 + 0i) + (0.6 + 0.8i)  =  0.6 + 0.8i  =  z1   ✓
z1 ⊕  0-bar  =  (0.6 + 0.8i) + (0 + 0i)  =  0.6 + 0.8i  =  z1   ✓
```

The complex zero is the identity for complex addition.

### (M1) Associativity of ⊗

```
(z1 ⊗  z2) ⊗  z3
    =  ((0.6 + 0.8i) * (-0.3 + 0.4i)) * (0.5 + 0.0i)
    =  ((0.6)(-0.3) - (0.8)(0.4) + ((0.6)(0.4) + (0.8)(-0.3))i) * (0.5 + 0.0i)
    =  (-0.18 - 0.32 + (0.24 - 0.24)i) * (0.5 + 0.0i)
    =  (-0.50 + 0.00i) * (0.5 + 0.0i)
    =  -0.25 + 0.00i

z1 ⊗  (z2 ⊗  z3)
    =  (0.6 + 0.8i) * ((-0.3 + 0.4i) * (0.5 + 0.0i))
    =  (0.6 + 0.8i) * (-0.15 + 0.20i)
    =  ((0.6)(-0.15) - (0.8)(0.20) + ((0.6)(0.20) + (0.8)(-0.15))i)
    =  (-0.09 - 0.16 + (0.12 - 0.12)i)
    =  -0.25 + 0.00i   ✓
```

Holds because complex multiplication is associative.

### (M2) ⊗  Identity

```
1-bar ⊗  z1  =  (1 + 0i) * (0.6 + 0.8i)  =  0.6 + 0.8i  =  z1   ✓
z1 ⊗  1-bar  =  (0.6 + 0.8i) * (1 + 0i)  =  0.6 + 0.8i  =  z1   ✓
```

The complex one is the identity for complex multiplication.

### (D1) Left Distributivity: ⊗  distributes over ⊕  from the left

```
z1 ⊗  (z2 ⊕  z3)
    =  (0.6 + 0.8i) * ((-0.3 + 0.4i) + (0.5 + 0.0i))
    =  (0.6 + 0.8i) * (0.2 + 0.4i)
    =  (0.12 - 0.32 + (0.24 + 0.16)i)
    =  -0.20 + 0.40i

(z1 ⊗  z2) ⊕  (z1 ⊗  z3)
    =  (-0.50 + 0.00i) + ((0.6 + 0.8i) * (0.5 + 0.0i))
    =  (-0.50 + 0.00i) + (0.30 + 0.40i)
    =  -0.20 + 0.40i   ✓
```

Holds because complex multiplication distributes over complex
addition.

### (D2) Right Distributivity: ⊗  distributes over ⊕  from the right

```
(z1 ⊕  z2) ⊗  z3
    =  ((0.6 + 0.8i) + (-0.3 + 0.4i)) * (0.5 + 0.0i)
    =  (0.3 + 1.2i) * (0.5 + 0.0i)
    =  0.15 + 0.60i

(z1 ⊗  z3) ⊕  (z2 ⊗  z3)
    =  ((0.6 + 0.8i)(0.5 + 0.0i)) + ((-0.3 + 0.4i)(0.5 + 0.0i))
    =  (0.30 + 0.40i) + (-0.15 + 0.20i)
    =  0.15 + 0.60i   ✓
```

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
0-bar ⊗  z1  =  (0 + 0i) * (0.6 + 0.8i)  =  0 + 0i  =  0-bar   ✓
z1 ⊗  0-bar  =  (0.6 + 0.8i) * (0 + 0i)  =  0 + 0i  =  0-bar   ✓
```

Any complex number multiplied by zero is zero.  An unreachable state
remains unreachable regardless of what amplitudes follow.

All eight axioms are satisfied. Q is a valid semiring (in fact, a
commutative ring).

> For the parsing-specific interpretation of these axioms, see
> [4. Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity

**Claim**: The amplitude semiring is commutative (⊗  is commutative).

**Proof**: For all z1, z2 in C:

```
z1 ⊗  z2  =  z1 * z2  =  z2 * z1  =  z2 ⊗  z1
```

Complex multiplication is commutative.   ∎

### 4.2 NOT Idempotent

**Claim**: The amplitude semiring is NOT idempotent.

**Proof**: For z = 0.5 + 0.0i:

```
z ⊕  z  =  (0.5 + 0.0i) + (0.5 + 0.0i)  =  1.0 + 0.0i  ≠  z
```

Complex addition is not idempotent: `z + z = 2z ≠ z` for z ≠ 0.   ∎

This non-idempotency is physically meaningful: combining two identical
paths produces constructive interference, doubling the amplitude.
This is the fundamental difference between quantum and classical
computation.

### 4.3 NOT a Star Semiring

**Claim**: AmplitudeWeight does NOT implement `StarSemiring`.

**Proof**: The Kleene star requires the infinite sum:

```
star(z) = ⊕_{n=0}^{∞} z^n = 1 + z + z² + z³ + ...
```

This is the geometric series `1/(1-z)`, which converges only when
`|z| < 1`.  For `|z| >= 1`, the series diverges.  Since the carrier
set includes all complex numbers, convergence is not guaranteed, and
the implementation correctly omits `StarSemiring`.

### 4.4 NOT Complete

**Claim**: AmplitudeWeight is NOT a complete semiring.

**Proof**: Consider the sequence z_n = 1/n.  The infinite sum
`sum_{n=1}^{∞} 1/n` (harmonic series) diverges.  Since infinite ⊕
sums do not generally converge over C, the semiring is not complete.   ∎

### 4.5 Only DetectableZero

AmplitudeWeight implements only `DetectableZero` (the minimal marker
trait) -- not `IdempotentSemiring`, `CompleteSemiring`, or
`StarSemiring`.  This is the weakest trait set of any PraTTaIL
semiring, reflecting the complex domain's lack of the structural
properties that classical semirings enjoy.

### 4.6 Total Ordering (Reversed, by Born Rule)

AmplitudeWeight implements `Ord` based on the Born rule (`|z|^2`),
with **reversed** ordering so that higher probability = "lower"
(better):

```
Ordering logic:
  1. Primary: other.norm_sqr().total_cmp(&self.norm_sqr())  [reversed]
  2. Tiebreak on real part (ascending)
  3. Tiebreak on imaginary part (ascending)
```

This ordering is for compatibility with generic min-based algorithms
and deterministic comparison in `BTreeMap` keys.  However, it does NOT
respect the semiring structure -- `Ord` is not a semiring homomorphism
because `|z1 + z2|^2 ≠ |z1|^2 + |z2|^2` in general (interference).

**Caveat**: This ordering should be used only for prioritization and
data structure compatibility, NOT for Viterbi-style path selection
(see [Section 7: Quantum Interference Caveat]).

---

## 5. Amplitude-Probability Table

AmplitudeWeight relates to classical probability through the Born
rule: the probability of observing a state is the squared magnitude
of its amplitude.

### Amplitude-to-Probability Mapping

| Amplitude z              | |z|²         | Classical Probability | Interpretation            |
|--------------------------|--------------|----------------------|---------------------------|
| 1.0 + 0.0i               | 1.0          | 100%                 | Certain observation       |
| 0.707 + 0.707i            | ~1.0         | ~100%                | Phase-shifted certainty   |
| 0.6 + 0.8i                | 1.0          | 100%                 | Pure phase rotation       |
| 0.5 + 0.0i                | 0.25         | 25%                  | Quarter probability       |
| 0.0 + 0.5i                | 0.25         | 25%                  | Same prob, different phase|
| 0.0 + 0.0i                | 0.0          | 0%                   | Impossible (unreachable)  |

### Key Insight: Phase Matters for Interference

Two amplitudes with the same `|z|^2` but different phases produce
different interference patterns when combined:

```
Constructive:  (0.5 + 0.0i) + (0.5 + 0.0i)  =  1.0 + 0.0i    |z|² = 1.0
Destructive:   (0.5 + 0.0i) + (-0.5 + 0.0i) =  0.0 + 0.0i    |z|² = 0.0
Partial:       (0.5 + 0.0i) + (0.0 + 0.5i)   =  0.5 + 0.5i    |z|² = 0.5
```

In classical semirings, combining two identical paths always increases
the total weight (or at least doesn't decrease it).  In the amplitude
semiring, combining paths can *decrease* the total -- a phenomenon
with no classical analogue.

### Conversion Functions

```rust
impl AmplitudeWeight {
    /// Create from classical probability: √p + 0i
    pub fn from_probability(p: f64) -> Self { ... }  // √p + 0i

    /// Collapse to classical probability: |z|²
    pub fn to_probability(self) -> f64 { ... }       // re² + im²
}
```

---

## 6. Zero Annihilation

The zero element `0 + 0i` represents an *unreachable* state with
zero amplitude.  Its annihilation property guarantees that unreachable
paths remain unreachable:

```
0-bar ⊗  z  =  (0 + 0i) * z  =  0 + 0i  =  0-bar     for all z ∈ C
z ⊗  0-bar  =  z * (0 + 0i)  =  0 + 0i  =  0-bar     for all z ∈ C
```

In the implementation, `is_zero()` checks both components:

```rust
fn is_zero(&self) -> bool {
    self.0.re == 0.0 && self.0.im == 0.0
}
```

---

## 7. Quantum Interference -- Worked Example

### Path Amplitude Computation with Interference

Consider a 4-node quantum CTMC graph with two alternative transition
paths.  The paths have different phases, leading to partial
destructive interference:

```
                        ┌─────────────────────────────────┐
                        │        Quantum CTMC             │
                        │     (amplitude graph)           │
                        └─────────────────────────────────┘

  Path 1 (direct):        q₀ ──(0.6+0.0i)──▶ q₁ ──(0.5+0.0i)──▶ q₃
  Path 2 (via q₂):        q₀ ──(0.0+0.4i)──▶ q₂ ──(0.0+0.5i)──▶ q₃


         ┌──────┐  0.6+0.0i   ┌──────┐
         │      │─────────────▶│      │
         │  q₀  │              │  q₁  │──┐
         │      │              │      │  │  0.5+0.0i
         └──────┘              └──────┘  │
            │                            │
            │                     ┌──────▼──────┐
            │  0.0+0.4i           │             │
            │                     │     q₃      │
            │                     │  (observe)  │
            │                     └──────▲──────┘
            │                            │
            ▼                            │  0.0+0.5i
         ┌──────┐                        │
         │      │────────────────────────┘
         │  q₂  │
         │      │
         └──────┘
```

**Path 1** (direct):

```
z₁  =  (0.6 + 0.0i) ⊗  (0.5 + 0.0i)
     =  (0.6)(0.5) - (0.0)(0.0) + ((0.6)(0.0) + (0.0)(0.5))i
     =  0.30 + 0.00i

|z₁|² = 0.09       (9% probability if measured alone)
```

**Path 2** (via q2):

```
z₂  =  (0.0 + 0.4i) ⊗  (0.0 + 0.5i)
     =  (0.0)(0.0) - (0.4)(0.5) + ((0.0)(0.5) + (0.4)(0.0))i
     =  -0.20 + 0.00i

|z₂|² = 0.04       (4% probability if measured alone)
```

**Combining alternatives** (⊕ -- quantum interference):

```
z*  =  z₁ ⊕  z₂  =  (0.30 + 0.00i) + (-0.20 + 0.00i)  =  0.10 + 0.00i

|z*|² = 0.01       (1% probability after interference!)
```

### Interference Analysis

```
┌────────────────────────────────────────────────────────────────┐
│  Classical (Viterbi):  max(0.09, 0.04)  =  0.09  (9%)        │
│  Classical (sum):      0.09 + 0.04      =  0.13  (13%)       │
│  Quantum (amplitude):  |0.30 - 0.20|²  =  0.01  (1%)        │
│                                                                │
│  Destructive interference reduced probability by 92%!          │
└────────────────────────────────────────────────────────────────┘
```

The two paths partially cancel because they arrive with opposite signs
(0.30 and -0.20).  A classical analysis would predict either 9%
(Viterbi) or 13% (forward) probability, but quantum interference
reduces it to just 1%.

### Constructive Interference Example

If Path 2 instead had the same phase as Path 1:

```
z₂' = +0.20 + 0.00i
z*' = 0.30 + 0.20 = 0.50 + 0.00i
|z*'|² = 0.25  (25%)
```

Constructive interference *increases* the probability beyond what
either path alone provides.  This is impossible in classical
semirings.

---

## 8. Dispatch Weight Table

AmplitudeWeight is not used for parse dispatch (that role belongs to
TropicalWeight and ViterbiWeight).  Instead, it serves the quantum
CTMC simulation layer.  The following table maps quantum states to
their amplitudes:

| Quantum State               | Amplitude             | |z|²   | Interpretation                    |
|------------------------------|-----------------------|--------|-----------------------------------|
| Ground state (initialized)   | 1.0 + 0.0i            | 1.0    | Fully occupied, no phase shift    |
| Excited state (transitioned) | varies                 | varies | Transition amplitude              |
| Superposition                | normalized sum         | < 1    | Multiple states simultaneously    |
| Decayed (measured)           | collapsed to one state | 0 or 1 | Post-measurement                  |
| Unreachable                  | 0.0 + 0.0i            | 0.0    | Zero amplitude, impossible        |

---

## 9. Comparison with ViterbiWeight and LogWeight

AmplitudeWeight occupies a fundamentally different position from
classical weight types:

| Property            | ViterbiWeight              | LogWeight                     | AmplitudeWeight                  |
|---------------------|----------------------------|-------------------------------|----------------------------------|
| Carrier set         | [0, 1]                     | R+ ∪ {+∞}                     | C (complex numbers)              |
| ⊕  (addition)       | max(a, b)                  | -ln(e^(-a) + e^(-b))         | z1 + z2 (complex add)            |
| ⊗  (multiplication) | a * b                      | a + b                         | z1 * z2 (complex mul)            |
| 0-bar (zero)        | 0.0                        | +∞                            | 0 + 0i                           |
| 1-bar (one)         | 1.0                        | 0.0                           | 1 + 0i                           |
| Idempotent ⊕?       | Yes                        | No                            | No                               |
| Star?               | Yes                        | Yes                           | No                               |
| Complete?           | Yes                        | Yes                           | No                               |
| Interference?       | No                         | No                            | Yes (constructive + destructive) |
| Domain              | Probability                | Negative log-probability      | Complex amplitude                |
| Feature gate        | Always                     | `wfst-log`                    | `quantum`                        |
| Use case            | Recovery confidence        | Forward-backward, training    | Quantum CTMC simulation          |

### Why Viterbi Path Selection Fails for Amplitudes

In classical semirings, the Viterbi algorithm works because ⊕ is
idempotent (selecting the single best path is well-defined) and ⊗ is
monotone (extending a path never improves the ⊕ value).

In the amplitude semiring:

1. **⊕ is not idempotent**: `z + z = 2z ≠ z`.  Merging duplicate paths
   changes the amplitude.

2. **Interference can cancel**: Two individually high-amplitude paths
   can cancel to zero amplitude when combined.

3. **Phase matters**: The "best" path cannot be determined by magnitude
   alone -- its phase determines how it interferes with other paths.

Therefore, quantum amplitude computation requires *full forward
propagation* (summing all path amplitudes), not Viterbi-style path
selection.  The Born rule is applied *after* propagation to obtain
classical probabilities.

### Conversion via Born Rule

```
AmplitudeWeight → ViterbiWeight:  ViterbiWeight(|z|²)
AmplitudeWeight → TropicalWeight: TropicalWeight(-ln(|z|²))
```

These conversions are *lossy* -- phase information is discarded.
They should only be applied after all interference effects have been
accounted for.

---

## 10. Pseudocode: Forward Propagation with Born-Rule Measurement

The forward propagation algorithm computes the total amplitude
reaching each node by summing (not selecting) all path amplitudes.
Measurement via the Born rule converts amplitudes to classical
probabilities.

```
ALGORITHM QuantumForwardPropagation(G, start, observe_set)
────────────────────────────────────────────────────────────
  Input:  DAG G = (V, E, z) with nodes V, edges E,
          amplitude function z : E → C
          start node s ∈ V
          observation set O ⊆ V
  Output: Classical probability for each o ∈ O

  // Phase 1: Forward propagation (amplitude domain)
  1.  for each v ∈ V do
  2.      amp[v] ← 0 + 0i                    // amplitude zero
  3.  amp[s] ← 1 + 0i                         // amplitude one

  4.  for each node u ∈ V in topological order do
  5.      if amp[u] = 0 + 0i then continue    // skip zero-amplitude nodes
  6.      for each edge (u, v, z_uv) ∈ E do
  7.          amp[v] ← amp[v] ⊕  (amp[u] ⊗  z_uv)
  8.                 // = amp[v] + (amp[u] * z_uv)   [interference!]

  // Phase 2: Born-rule measurement (collapse to classical)
  9.  for each o ∈ O do
 10.      prob[o] ← |amp[o]|²                 // Born rule: re² + im²

  // Phase 3: Normalization (optional)
 11.  total ← sum of prob[o] for all o ∈ O
 12.  if total > 0 then
 13.      for each o ∈ O do
 14.          prob[o] ← prob[o] / total

 15.  return prob
```

**Complexity**: O(|V| + |E|) for forward propagation, plus O(|O|) for
measurement.

**Key difference from Viterbi**: Step 7 uses ⊕ (addition) to
*accumulate* all path amplitudes at each node, rather than selecting
the best one.  This is necessary because quantum interference requires
all paths to contribute to the final amplitude.

**Post-measurement**: After Born-rule collapse, classical semirings
(ViterbiWeight, TropicalWeight) can be used for further analysis.

---

## 11. Rust Implementation

The following is the complete `AmplitudeWeight` implementation from
`prattail/src/automata/semiring.rs`.  All items are gated behind
`#[cfg(feature = "quantum")]`.

```rust
/// Complex-amplitude semiring `(C, +, *, 0+0i, 1+0i)` for quantum CTMC
/// simulation.
///
/// **Algebra:**
/// - `plus` (parallel): complex addition -- models quantum interference
/// - `times` (sequential): complex multiplication -- models sequential
///   amplitude composition
/// - `zero`: `0 + 0i` -- no amplitude (unreachable state)
/// - `one`: `1 + 0i` -- unit amplitude (identity for composition)
///
/// This is technically a ring (additive inverses exist: `-z`), but satisfies
/// all `Semiring` trait requirements.
///
/// **Properties:**
/// - NOT idempotent: `z + z = 2z != z` in general
/// - NOT a star semiring: geometric series diverges for `|z| >= 1`
/// - NOT complete: infinite sums do not generally converge
///
/// **Measurement (Born rule):** `|z|^2 = re^2 + im^2` gives the classical
/// observation probability.
///
/// **Ordering:** By `norm_sqr()` (Born rule probability), *reversed* so that
/// higher probability = "better" (lower in `Ord`).
#[cfg(feature = "quantum")]
#[derive(Clone, Copy)]
pub struct AmplitudeWeight(pub num_complex::Complex64);

#[cfg(feature = "quantum")]
impl AmplitudeWeight {
    /// Create an amplitude weight from real and imaginary parts.
    #[inline]
    pub fn new(re: f64, im: f64) -> Self {
        AmplitudeWeight(num_complex::Complex64::new(re, im))
    }

    /// Squared magnitude (Born rule): `|z|^2 = re^2 + im^2`.
    #[inline]
    pub fn norm_sqr(self) -> f64 {
        self.0.norm_sqr()
    }

    /// Create from a classical probability `p in [0, 1]`.
    ///
    /// Produces a real amplitude `sqrt(p) + 0i` whose Born rule gives `p`.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&p),
            "AmplitudeWeight::from_probability: p must be in [0, 1], got {p}"
        );
        AmplitudeWeight(num_complex::Complex64::new(p.sqrt(), 0.0))
    }

    /// Collapse to classical probability via the Born rule: `|z|^2`.
    #[inline]
    pub fn to_probability(self) -> f64 {
        self.0.norm_sqr()
    }
}

/// Convert from a `LogWeight` (negative log-probability) to a real amplitude.
///
/// `AmplitudeWeight(sqrt(exp(-w)) + 0i)` = `AmplitudeWeight(exp(-w/2) + 0i)`.
/// The resulting amplitude's Born rule gives `exp(-w)`, the original probability.
#[cfg(all(feature = "quantum", feature = "wfst-log"))]
impl AmplitudeWeight {
    #[inline]
    pub fn from_log_weight(w: LogWeight) -> Self {
        if w.is_zero() {
            AmplitudeWeight::zero()
        } else {
            AmplitudeWeight(num_complex::Complex64::new((-w.value() / 2.0).exp(), 0.0))
        }
    }
}

#[cfg(feature = "quantum")]
impl Semiring for AmplitudeWeight {
    #[inline]
    fn zero() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(0.0, 0.0))
    }

    #[inline]
    fn one() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(1.0, 0.0))
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 + other.0)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 * other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.re == 0.0 && self.0.im == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.re == 1.0 && self.0.im == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0.re - other.0.re).abs() <= epsilon
            && (self.0.im - other.0.im).abs() <= epsilon
    }
}

/// Higher Born-rule probability = "better" (lower in ordering).
/// Reversed so generic min-based algorithms select highest probability.
/// Ties broken by real part then imaginary part for determinism.
#[cfg(feature = "quantum")]
impl Ord for AmplitudeWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_norm = self.0.norm_sqr();
        let other_norm = other.0.norm_sqr();
        // Reverse: higher norm^2 = "lower" (better)
        match other_norm.total_cmp(&self_norm) {
            Ordering::Equal => {
                // Tiebreak: real part then imaginary part (ascending)
                match self.0.re.total_cmp(&other.0.re) {
                    Ordering::Equal => self.0.im.total_cmp(&other.0.im),
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

#[cfg(feature = "quantum")]
impl Hash for AmplitudeWeight {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.re.to_bits().hash(state);
        self.0.im.to_bits().hash(state);
    }
}

#[cfg(feature = "quantum")]
impl Default for AmplitudeWeight {
    fn default() -> Self {
        Self::one()
    }
}

#[cfg(feature = "quantum")]
impl DetectableZero for AmplitudeWeight {}
```

### Implementation Notes

- **Feature gate `quantum`**: All AmplitudeWeight items are conditional
  on `#[cfg(feature = "quantum")]`.  The `from_log_weight` conversion
  additionally requires the `wfst-log` feature.

- **`num-complex` dependency**: Uses `num_complex::Complex64` (a pair
  of `f64`) for efficient complex arithmetic.  The dependency is
  gated: `dep:num-complex` is only pulled in when `quantum` is
  enabled.

- **Reversed `Ord` by `norm_sqr`**: Higher Born-rule probability =
  "lower" in ordering.  The tiebreaker on real part then imaginary
  part ensures deterministic comparison for `BTreeMap` keys.

- **Hash via `to_bits`**: Both `re` and `im` components are hashed via
  `f64::to_bits()`, ensuring consistency with the component-wise `Eq`.

- **Only `DetectableZero`**: No `IdempotentSemiring`, `CompleteSemiring`,
  or `StarSemiring` -- the weakest trait set in PraTTaIL, correctly
  reflecting the complex domain's properties.

- **`Default = one()`**: A newly created weight represents "unit
  amplitude" (1 + 0i, the multiplicative identity), the natural
  starting point for amplitude propagation.

- **`approx_eq` is component-wise**: Both real and imaginary parts must
  be within epsilon, rather than checking `norm_sqr` difference.  This
  is stricter but avoids false positives from phase differences.

---

## 12. Integration into PraTTaIL

AmplitudeWeight integrates with PraTTaIL through the quantum CTMC
simulation layer for MeTTaIL-Gillespie integration.

### 12.1 Quantum CTMC Simulation

The primary consumer is the MeTTaIL-Gillespie quantum CTMC engine,
which uses AmplitudeWeight for transition amplitudes:

```rust
// Transition matrix entries are AmplitudeWeights
let transition = AmplitudeWeight::new(0.6, 0.8);  // amplitude with phase
let accumulated = current_amplitude.times(&transition);  // sequential composition
```

### 12.2 Born-Rule Measurement Bridge

After amplitude propagation, results are collapsed to classical
probabilities for integration with the tropical-native pipeline:

```rust
let amplitude = AmplitudeWeight::new(0.3, 0.4);
let prob = amplitude.to_probability();   // |z|² = 0.09 + 0.16 = 0.25
let viterbi = ViterbiWeight::new(prob);  // Classical probability weight
```

### 12.3 LogWeight Conversion (dual-gated)

When both `quantum` and `wfst-log` features are enabled, direct
conversion from LogWeight is available:

```rust
let log_w = LogWeight::new(0.693);           // -ln(0.5) ≈ 0.693
let amp = AmplitudeWeight::from_log_weight(log_w);
// amp ≈ AmplitudeWeight(exp(-0.693/2) + 0i) ≈ AmplitudeWeight(0.707 + 0i)
// amp.to_probability() ≈ 0.5
```

### 12.4 Product Weight Pairing

For hybrid quantum-classical analysis, AmplitudeWeight can be paired
with TropicalWeight via `ProductWeight<AmplitudeWeight, TropicalWeight>`,
using the amplitude for quantum propagation and the tropical weight for
classical dispatch priority.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 2502--2698
- **Struct**: `AmplitudeWeight(pub num_complex::Complex64)`
- **Feature gate**: `#[cfg(feature = "quantum")]` on all items
- **Trait impl**: `impl Semiring for AmplitudeWeight` (lines 2590--2625)
- **Ordering**: `impl Ord for AmplitudeWeight` via reversed `norm_sqr` (lines 2663--2679)
- **Born rule**: `norm_sqr()` (line 2550), `to_probability()` (line 2568)
- **Conversions**: `from_probability()` (line 2558), `from_log_weight()` (lines 2580--2587)
- **Hashing**: `impl Hash` via `re.to_bits()` + `im.to_bits()` (lines 2682--2687)
- **Tests**: lines 4528--4690 (core), lines 4690--4714 (log-weight), lines 5542+ (proptest)

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Viterbi Weight Theory](viterbi-weight.md) -- Classical
  probability-domain semiring (compare: no interference)
- [Log Weight Theory](log-weight.md) -- Log-probability semiring
  (compare: no phase information)
- [Tropical Weight Theory](tropical-weight.md) -- Cost-based
  shortest-path semiring
- [Product Weight Theory](product-weight.md) -- Multi-dimensional
  weight for hybrid quantum-classical pairing
- [Semiring Catalog](../../../docs/design/semiring-catalog.md) --
  Overview of all semiring types including AmplitudeWeight

### References

- Born, M. (1926). "Zur Quantenmechanik der Stossvorgange."
  *Zeitschrift fur Physik*, 37(12), 863--867.
- Feynman, R. P. (1948). "Space-time approach to non-relativistic
  quantum mechanics." *Reviews of Modern Physics*, 20(2), 367--387.
- Nielsen, M. A. & Chuang, I. L. (2000). *Quantum Computation and
  Quantum Information*. Cambridge University Press.
- Mohri, M. (2002). "Semiring frameworks and algorithms for
  shortest-distance problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350.
- Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted
  Automata*. Springer. (Complex and matrix semirings.)
