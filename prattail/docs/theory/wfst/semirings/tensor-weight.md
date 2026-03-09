# Tensor Product Semiring: TensorWeight

## 1. Intuition & Motivation

The tensor product semiring provides a *correlated multi-analysis
algebra* that tracks interactions between two independent weight
dimensions. Its carrier set consists of formal sums of elementary
tensors (pairs of weights), and its two operations implement
bilinear composition:

- **Combining alternative results** (parallel paths) uses term list
  concatenation and simplification -- all terms from both operands are
  preserved, with matching first-component terms merged.
- **Sequencing segments** (a path through multiple arcs) uses bilinear
  expansion -- every pair of terms from the two operands is multiplied
  component-wise, producing all cross-products.

Within PraTTaIL, tensor weights answer correlated questions that
product weights cannot:

```
"How many derivations achieve cost 2.0 specifically?"
"What is the best cost among the 3-derivation paths?"
```

A product weight `(best_cost, total_count)` tells you the best cost
and total count independently. A tensor weight preserves the
per-cost-level breakdown:

```
TW(1.0) ⊗ CW(2)  +  TW(3.0) ⊗ CW(5)
```

This says: "2 derivations have cost 1.0, and 5 derivations have
cost 3.0." The correlation between cost and count is preserved.

---

## 2. Formal Definition

Given semirings `(S_1, ⊕_1, ⊗_1, 0_1, 1_1)` and
`(S_2, ⊕_2, ⊗_2, 0_2, 1_2)`, the tensor product semiring is:

```
T  =  ( Sigma_i S_1 ⊗ S_2,  ⊕,  bilinear_⊗,  0,  1_1 ⊗ 1_2 )
```

where:

| Component                   | Symbol        | Concrete value                     | Meaning                                 |
|-----------------------------|---------------|------------------------------------|-----------------------------------------|
| Carrier set                 | K             | Formal sums of S_1 x S_2 pairs    | Correlated weight pairs                 |
| Addition (⊕)                | concatenate   | term list union + simplification   | Combine alternative analyses            |
| Multiplication (⊗)          | bilinear      | all pairwise component products    | Sequence with cross-correlation         |
| Additive identity (0)       | empty sum     | no terms                           | No analysis result                      |
| Multiplicative identity (1) | 1_1 ⊗ 1_2    | single term (1_1, 1_2)            | Identity transformation in both dims    |

Each element is a formal sum of elementary tensors:

```
w  =  Sigma_i  a_i ⊗ b_i     where a_i in S_1, b_i in S_2
```

The bilinear multiplication rule is:

```
(Sigma_i a_i ⊗ b_i) ⊗ (Sigma_j c_j ⊗ d_j)
  = Sigma_{i,j}  (a_i ⊗_1 c_j) ⊗ (b_i ⊗_2 d_j)
```

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete numerical examples.
Let S_1 = TropicalWeight, S_2 = CountingWeight, and define:

```
t_1 = TW(1.0) ⊗ CW(2)
t_2 = TW(3.0) ⊗ CW(4)
t_3 = TW(2.0) ⊗ CW(1)
```

For multi-term elements:

```
u = t_1 + t_2 = TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4)
v = t_3       = TW(2.0)⊗CW(1)
```

### (A1) Associativity of ⊕

```
(u ⊕ v) ⊕ t_1
  = (TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4) + TW(2.0)⊗CW(1)) ⊕ TW(1.0)⊗CW(2)
  = TW(1.0)⊗CW(4) + TW(3.0)⊗CW(4) + TW(2.0)⊗CW(1)
  (after simplification: TW(1.0) terms merged: CW(2)+CW(2)=CW(4))

u ⊕ (v ⊕ t_1)
  = u ⊕ (TW(2.0)⊗CW(1) + TW(1.0)⊗CW(2))
  = TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4) + TW(2.0)⊗CW(1) + TW(1.0)⊗CW(2)
  = TW(1.0)⊗CW(4) + TW(3.0)⊗CW(4) + TW(2.0)⊗CW(1)
  (after simplification)   ✓
```

Holds because term list concatenation is associative and
simplification is order-independent (merges by first-component
equality).

### (A2) Commutativity of ⊕

```
t_1 ⊕ t_2  =  TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4)
t_2 ⊕ t_1  =  TW(3.0)⊗CW(4) + TW(1.0)⊗CW(2)
```

After simplification (no matching first components to merge), both
contain the same two terms.   ✓

### (A3) ⊕ Identity

```
0 ⊕ t_1  =  {} + TW(1.0)⊗CW(2)  =  TW(1.0)⊗CW(2)  =  t_1   ✓
t_1 ⊕ 0  =  TW(1.0)⊗CW(2) + {}  =  TW(1.0)⊗CW(2)  =  t_1   ✓
```

The empty sum (no terms) is the identity for term list concatenation.

### (M1) Associativity of ⊗

```
(t_1 ⊗ t_2) ⊗ t_3

t_1 ⊗ t_2:
  TW(1.0+3.0) ⊗ CW(2*4)  =  TW(4.0) ⊗ CW(8)

(TW(4.0)⊗CW(8)) ⊗ t_3:
  TW(4.0+2.0) ⊗ CW(8*1)  =  TW(6.0) ⊗ CW(8)

t_1 ⊗ (t_2 ⊗ t_3)

t_2 ⊗ t_3:
  TW(3.0+2.0) ⊗ CW(4*1)  =  TW(5.0) ⊗ CW(4)

t_1 ⊗ (TW(5.0)⊗CW(4)):
  TW(1.0+5.0) ⊗ CW(2*4)  =  TW(6.0) ⊗ CW(8)   ✓
```

Holds because component-wise multiplication is associative in both
S_1 and S_2.

### (M2) ⊗ Identity

```
1 = TW(0.0) ⊗ CW(1)    (the one element)

1 ⊗ t_1:
  TW(0.0+1.0) ⊗ CW(1*2)  =  TW(1.0) ⊗ CW(2)  =  t_1   ✓

t_1 ⊗ 1:
  TW(1.0+0.0) ⊗ CW(2*1)  =  TW(1.0) ⊗ CW(2)  =  t_1   ✓
```

The elementary tensor of both component identities is the
multiplicative identity.

### (D1) Left Distributivity: ⊗ distributes over ⊕ from the left

```
t_3 ⊗ (t_1 ⊕ t_2)
  = TW(2.0)⊗CW(1) ⊗ (TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4))

Bilinear expansion:
  TW(2.0+1.0)⊗CW(1*2) + TW(2.0+3.0)⊗CW(1*4)
  = TW(3.0)⊗CW(2) + TW(5.0)⊗CW(4)

(t_3 ⊗ t_1) ⊕ (t_3 ⊗ t_2)
  = (TW(2.0+1.0)⊗CW(1*2)) + (TW(2.0+3.0)⊗CW(1*4))
  = TW(3.0)⊗CW(2) + TW(5.0)⊗CW(4)   ✓
```

### (D2) Right Distributivity: ⊗ distributes over ⊕ from the right

```
(t_1 ⊕ t_2) ⊗ t_3
  = (TW(1.0)⊗CW(2) + TW(3.0)⊗CW(4)) ⊗ TW(2.0)⊗CW(1)

Bilinear expansion:
  TW(1.0+2.0)⊗CW(2*1) + TW(3.0+2.0)⊗CW(4*1)
  = TW(3.0)⊗CW(2) + TW(5.0)⊗CW(4)

(t_1 ⊗ t_3) ⊕ (t_2 ⊗ t_3)
  = TW(3.0)⊗CW(2) + TW(5.0)⊗CW(4)   ✓
```

### (Z) Zero Annihilation

```
0 ⊗ t_1  =  {} ⊗ TW(1.0)⊗CW(2)  =  {}  =  0   ✓
t_1 ⊗ 0  =  TW(1.0)⊗CW(2) ⊗ {}  =  {}  =  0   ✓
```

Bilinear expansion over an empty term list produces no terms.

All eight axioms are satisfied. T is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [Section 4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity (Conditional)

**Claim**: The tensor product semiring is commutative if and only if
both component semirings are commutative.

**Proof**: For elementary tensors a ⊗ b and c ⊗ d:

```
(a ⊗ b) ⊗_T (c ⊗ d) = (a ⊗_1 c) ⊗ (b ⊗_2 d)
(c ⊗ d) ⊗_T (a ⊗ b) = (c ⊗_1 a) ⊗ (d ⊗_2 b)
```

These are equal iff `a ⊗_1 c = c ⊗_1 a` and `b ⊗_2 d = d ⊗_2 b`,
i.e., iff both component semirings are commutative.   ∎

Since TropicalWeight and CountingWeight are both commutative,
`TensorWeight<TropicalWeight, CountingWeight>` is commutative.

### 4.2 Non-Idempotency (In General)

**Claim**: The tensor product semiring is *not* idempotent in general.

**Proof by counterexample**: Let t = TW(1.0) ⊗ CW(3):

```
t ⊕ t  (before simplification):
  TW(1.0)⊗CW(3) + TW(1.0)⊗CW(3)

After simplification (merge TW(1.0) terms):
  TW(1.0)⊗CW(3+3) = TW(1.0)⊗CW(6)

Since CW(6) != CW(3), we have t ⊕ t != t.   ∎
```

However, if both component semirings are idempotent (e.g.,
TropicalWeight and BooleanWeight), then the tensor product is also
idempotent. This follows because simplification merges equal first
components using S_2's ⊕, which is idempotent.

### 4.3 Fixed Capacity

**Claim**: TensorWeight stores at most MAX_TENSOR_TERMS = 8
elementary terms.

**Consequence**: Operations that would generate more than 8 terms
must either simplify (merge equal first components) or truncate
(discard excess terms). Truncation is a sound over-approximation:

- For ⊕ (plus): Truncated terms are lost derivation alternatives.
  The result under-counts but never over-counts.
- For ⊗ (times): Truncated cross-products are lost joint derivations.
  The result is a subset of the exact result.

The fixed capacity satisfies the `Copy` bound required by the
`Semiring` trait, enabling use with Viterbi, forward-backward, and
all standard algorithms.

### 4.4 Copy Semantics

**Claim**: TensorWeight implements `Copy` when both component
semirings implement `Copy`.

**Proof**: The internal representation is a fixed-size array
`[(W1, W2); 8]` plus a `usize` length field. When W1 and W2 are
`Copy`, the array is `Copy`, and the struct is `Copy`. No heap
allocation is used.

Memory layout for `TensorWeight<TropicalWeight, CountingWeight>`:

```
┌──────────────────────────────────────────────┐
│ terms[0]: (f64, u64)  = 16 bytes              │
│ terms[1]: (f64, u64)  = 16 bytes              │
│ ...                                           │
│ terms[7]: (f64, u64)  = 16 bytes              │
│ len: usize            =  8 bytes              │
│ Total: 8 * 16 + 8 = 136 bytes (stack)         │
└──────────────────────────────────────────────┘
```

---

## 5. Bilinearity

The defining property of the tensor product is bilinearity of
multiplication:

```
(a_1 ⊗ b_1 + a_2 ⊗ b_2) ⊗_T (c ⊗ d)
  = (a_1 ⊗_1 c) ⊗ (b_1 ⊗_2 d) + (a_2 ⊗_1 c) ⊗ (b_2 ⊗_2 d)
```

This generates two output terms from two input terms (one per term
in the left operand). In general, multiplying an m-term tensor by
an n-term tensor produces up to m * n terms before simplification.

### Why Bilinearity Matters

Bilinearity is what distinguishes TensorWeight from ProductWeight.
In a product semiring:

```
(a, b) * (c, d)  =  (a *_1 c, b *_2 d)
```

One input pair always produces one output pair. The components never
interact. In the tensor product, each left term interacts with every
right term, preserving which specific (S_1, S_2) correlations arise
in the computation.

### Worked Example

```
X = TW(1.0)⊗CW(2) + TW(2.0)⊗CW(3)
Y = TW(0.0)⊗CW(1) + TW(1.0)⊗CW(2)

X ⊗ Y (bilinear expansion, 2 x 2 = 4 terms):
  (1.0+0.0)⊗(2*1) = TW(1.0)⊗CW(2)
  (1.0+1.0)⊗(2*2) = TW(2.0)⊗CW(4)
  (2.0+0.0)⊗(3*1) = TW(2.0)⊗CW(3)
  (2.0+1.0)⊗(3*2) = TW(3.0)⊗CW(6)

After simplification (merge TW(2.0) terms: CW(4)+CW(3)=CW(7)):
  TW(1.0)⊗CW(2) + TW(2.0)⊗CW(7) + TW(3.0)⊗CW(6)
```

The result has 3 terms: at cost 1.0 there are 2 derivations, at
cost 2.0 there are 7, and at cost 3.0 there are 6. ProductWeight
would collapse this to `(min(1.0,2.0,3.0), 2+7+6) = (1.0, 15)`,
losing the per-cost breakdown.

---

## 6. Zero Annihilation

The zero element (empty term list) represents a state where no
analysis result exists. Its annihilation property guarantees:

```
0 ⊗ w  =  0     for all w in T
w ⊗ 0  =  0     for all w in T
```

Bilinear expansion over an empty term list generates zero
cross-products. Additionally, within bilinear expansion, individual
zero-component terms are filtered:

```
if w1.is_zero() or w2.is_zero():
    skip this elementary tensor  (it equals 0 by bilinearity)
```

This optimization saves capacity for non-trivial terms.

---

## 7. Path Correlation Computation

### Worked Example

Consider a WFST with two parse paths for the same input, tracked
with `TensorWeight<TropicalWeight, CountingWeight>`:

```
Path 1: cost 2.0, uses 3 rules
Path 2: cost 5.0, uses 1 rule
```

Encoded as tensor weights on edges:

```
         ┌──────┐    TW(1.0)⊗CW(1)    ┌──────┐
         │      │─────────────────────▶│      │
         │  q_0 │                      │  q_1 │──┐
         │      │                      │      │  │ TW(1.0)⊗CW(2)
         └──────┘                      └──────┘  │
            │                                    │
            │                            ┌───────▼──────┐
            │  TW(5.0)⊗CW(1)            │              │
            │                            │     q_3      │
            │                            │   (accept)   │
            │                            └───────▲──────┘
            │                                    │
            ▼                                    │ TW(0.0)⊗CW(1)
         ┌──────┐                                │
         │      │────────────────────────────────┘
         │  q_2 │
         │      │
         └──────┘
```

**Path 1** (q_0 -> q_1 -> q_3):

```
w_1 = (TW(1.0)⊗CW(1)) ⊗_T (TW(1.0)⊗CW(2))
    = TW(1.0+1.0) ⊗ CW(1*2)
    = TW(2.0) ⊗ CW(2)
```

**Path 2** (q_0 -> q_2 -> q_3):

```
w_2 = (TW(5.0)⊗CW(1)) ⊗_T (TW(0.0)⊗CW(1))
    = TW(5.0+0.0) ⊗ CW(1*1)
    = TW(5.0) ⊗ CW(1)
```

**Combining alternatives** (⊕):

```
w* = w_1 ⊕ w_2
   = TW(2.0)⊗CW(2) + TW(5.0)⊗CW(1)
```

The result preserves the correlation: 2 derivations at cost 2.0,
1 derivation at cost 5.0.

**Projections**:

```
project_left(w*)  = min(2.0, 5.0) = TW(2.0)     (best cost)
project_right(w*) = 2 + 1 = CW(3)                (total derivations)
right_given_left(w*, TW(2.0)) = CW(2)            (derivations at cost 2.0)
left_given_right(w*, CW(1))   = TW(5.0)          (best cost for single-derivation paths)
```

---

## 8. Simplification

Simplification is a key operation that maintains the term count
within the MAX_TENSOR_TERMS = 8 capacity:

```
┌─────────────────────────────────────────────────────────────────┐
│ Pass 1: Remove zero terms                                       │
│                                                                 │
│   For each term (w1, w2):                                       │
│     if w1.is_zero() or w2.is_zero():                            │
│       drop the term                                             │
│                                                                 │
│ Pass 2: Merge terms with equal first components                 │
│                                                                 │
│   For each unmerged term i:                                     │
│     For each later term j:                                      │
│       if terms[i].0 == terms[j].0:                              │
│         terms[i].1 = terms[i].1 ⊕_2 terms[j].1                 │
│         mark j as merged                                        │
│     if combined w2 is not zero:                                 │
│       emit (terms[i].0, combined_w2)                            │
└─────────────────────────────────────────────────────────────────┘
```

**Algebraic justification** for merging: The identity

```
a ⊗ b_1  +  a ⊗ b_2  =  a ⊗ (b_1 ⊕_2 b_2)
```

follows from the bilinearity of the tensor product. This is the
right-distributivity of ⊗ over ⊕ restricted to terms sharing a
common first component.

**Complexity**: O(n^2) where n = MAX_TENSOR_TERMS = 8, effectively
O(1) since n is bounded by a constant.

---

## 9. Comparison with ProductWeight

| Property            | ProductWeight               | TensorWeight                         |
|---------------------|-----------------------------|--------------------------------------|
| Carrier set         | S_1 x S_2 (single pair)    | Sigma_i (S_1 x S_2) (sum of pairs)  |
| ⊕ (addition)        | component-wise              | concatenation + simplification       |
| ⊗ (multiplication)  | component-wise              | bilinear (all pairwise)              |
| Size per element    | 2 scalars                   | up to 8 x 2 scalars + length        |
| Memory (TW x CW)   | 16 bytes                    | 136 bytes                            |
| Correlation         | Lost (independent)          | Preserved (correlated)               |
| Conditional queries | Not possible                | `left_given_right`, `right_given_left` |
| Exact?              | Yes                         | Approximate if > 8 terms (truncation)|
| Copy?               | Yes (if components are Copy)| Yes (fixed array, if components Copy)|
| StarSemiring?       | If both components support it | Yes, bounded power series (K=32)    |

**Decision rule**: Use ProductWeight when the two analyses are
independent. Use TensorWeight when you need to answer conditional
questions about the relationship between the two dimensions.

---

## 10. Pseudocode: Bilinear Multiplication

```
ALGORITHM TensorTimes(X, Y)
─────────────────────────────
  Input:  Tensor weights X = {(a_1,b_1), ..., (a_m,b_m)}
          Tensor weights Y = {(c_1,d_1), ..., (c_n,d_n)}
  Output: X ⊗ Y (bilinear product)

  1.  result <- empty list (capacity MAX_TENSOR_TERMS)

  2.  for i = 1 to m do
  3.      for j = 1 to n do
  4.          w1_new <- a_i ⊗_1 c_j
  5.          w2_new <- b_i ⊗_2 d_j
  6.          if w1_new.is_zero() or w2_new.is_zero() then
  7.              continue    // zero by bilinearity
  8.          if |result| >= MAX_TENSOR_TERMS then
  9.              Simplify(result)  // try to free capacity
 10.              if |result| >= MAX_TENSOR_TERMS then
 11.                  continue    // truncate (lose this term)
 12.          result.append((w1_new, w2_new))
 13.      end for
 14.  end for

 15.  Simplify(result)
 16.  return result
```

**Complexity**: O(m * n) where m, n are the active term counts.
In the worst case (both operands have 8 terms), up to 64 products
are computed, of which at most 8 survive. Simplification is O(n^2)
but n <= 8, so effectively O(1).

---

## 11. Rust Implementation

The following shows the core `TensorWeight` implementation from
`prattail/src/tensor.rs`.

```rust
/// Tensor product of two semirings with fixed-capacity inline storage.
pub struct TensorWeight<W1: Semiring, W2: Semiring> {
    /// Elementary tensor terms stored inline.
    terms: [(W1, W2); MAX_TENSOR_TERMS],
    /// Number of active terms. Invariant: len <= MAX_TENSOR_TERMS.
    len: usize,
}

impl<W1: Semiring, W2: Semiring> Semiring for TensorWeight<W1, W2> {
    fn zero() -> Self { /* empty term list, len = 0 */ }
    fn one() -> Self  { /* single term (W1::one(), W2::one()), len = 1 */ }

    fn plus(&self, other: &Self) -> Self {
        // Concatenate term lists, then simplify.
    }

    fn times(&self, other: &Self) -> Self {
        // Bilinear expansion: all (i, j) pairwise products.
        // Zero-component terms are skipped.
        // Intermediate simplification when capacity is exhausted.
    }

    fn is_zero(&self) -> bool {
        self.len == 0 || self.terms[..self.len].iter().all(|(w1, w2)|
            w1.is_zero() || w2.is_zero())
    }

    fn is_one(&self) -> bool {
        self.len == 1 && self.terms[0].0.is_one() && self.terms[0].1.is_one()
    }
}

/// StarSemiring via bounded power series (STAR_ITERATION_LIMIT = 32).
impl<W1: StarSemiring, W2: StarSemiring> StarSemiring for TensorWeight<W1, W2> {
    fn star(&self) -> Self {
        // star(x) = sum_{k=0}^{limit} x^k
        // Converges when next_sum approx_eq sum (epsilon = 1e-10).
    }
}
```

### Implementation Notes

- **Fixed-size array, not Vec**: The `[(W1, W2); 8]` array enables
  `Copy` semantics. Unused slots are padded with zero values and
  ignored. The `len` field tracks active terms.

- **Simplification on every operation**: Both `plus` and `times` run
  simplification (Pass 1: remove zeros, Pass 2: merge equal first
  components) to keep term counts within capacity.

- **Zero optimization in times**: Before adding a bilinear product
  term, both components are checked with `is_zero()`. Zero terms are
  skipped immediately, saving capacity for non-trivial terms.

- **Truncation is sound**: When capacity is exhausted during `times`,
  excess terms are silently dropped. This produces a subset of the
  exact result -- an under-approximation that never introduces false
  information.

- **Default = one()**: A newly created tensor weight is the
  multiplicative identity `(W1::one(), W2::one())`.

---

## 12. Integration into PraTTaIL

TensorWeight participates in three main use cases:

### 12.1 Cost-Count Correlation

`TensorWeight<TropicalWeight, CountingWeight>` tracks how many
derivations achieve each cost level. This enables conditional
queries like "how many derivations have cost <= 2.0?" that pure
ProductWeight cannot answer.

### 12.2 Multi-Pass Fusion

`TensorWeight<W_disambiguation, W_recovery>` jointly scores
disambiguation and recovery paths, preserving their correlation.
This enables recovery strategies that are aware of disambiguation
confidence.

### 12.3 Viterbi and Forward-Backward

TensorWeight implements `Semiring` (with `Copy`), so it integrates
with `viterbi_generic()` and `forward_scores()`. However, it does
not implement `Ord` by default -- a custom ordering must be provided
(typically by projecting to a scalar via `project_left()`).

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/tensor.rs`
- **Struct**: `TensorWeight<W1, W2> { terms: [(W1, W2); 8], len: usize }`
- **Constants**: `MAX_TENSOR_TERMS = 8`, `STAR_ITERATION_LIMIT = 32`
- **Semiring impl**: lines 278--437
- **StarSemiring impl**: lines 441--478
- **Projections**: `project_left`, `project_right`,
  `left_given_right`, `right_given_left` (lines 224--274)
- **Tests**: 26+ tests covering all axioms, bilinearity,
  projections, simplification, and StarSemiring

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom definitions
  and classification of all semirings
- [Product Weight Theory](product-weight.md) -- Independent
  component-wise composition (no correlation)
- [Tropical Weight Theory](tropical-weight.md) -- Common first
  component for cost analysis
- [Counting Weight Theory](counting-weight.md) -- Common second
  component for derivation counting
- [Boolean Weight Theory](boolean-weight.md) -- Common component for
  reachability analysis
- [Provenance Weight Theory](provenance-weight.md) -- Full derivation
  history; can be projected through TensorWeight
- [Tensor Design Doc](../../../design/wfst/semirings/tensor-weight.md) --
  Implementation decisions and pipeline integration details
- [Lattice/Viterbi](../../../src/lattice.rs) -- Generic Viterbi
  works with any `Semiring + Ord`

### Academic References

- M. Mohri, F. Pereira, and M. Riley. "Weighted Finite-State
  Transducers in Speech Recognition." Computer Speech & Language,
  16(1), 2002, pp. 69--88. (Semiring-generic WFST framework)
