# Tensor Product Semiring Analysis

| Property | Value |
|----------|-------|
| **Feature gate** | `tensor` |
| **Source file** | `prattail/src/tensor.rs` (~1316 lines) |
| **Pipeline phase** | Correlated multi-analysis (internal weight domain) |
| **Lint codes** | (internal -- no direct lint output) |

## 1. Rationale

PraTTaIL often needs to run two independent analyses simultaneously and capture
**correlations** between them. The standard `ProductWeight<S1, S2>` runs both
analyses independently (component-wise operations), losing any cross-analysis
information. The tensor product `S1 tensor S2` represents elements as formal
sums of elementary tensors `sum_i (a_i tensor b_i)`, with bilinear
multiplication that preserves correlations. This enables queries like "what is
the minimum cost (Tropical) conditioned on exactly 3 paths (Counting)?"

## 2. Theoretical Foundations

### 2.1. Algebraic Definition

**Definition (Tensor Product Semiring).** Given semirings
`(S1, oplus_1, otimes_1, 0_1, 1_1)` and `(S2, oplus_2, otimes_2, 0_2, 1_2)`,
the tensor product semiring `S1 tensor S2` has:

- **Elements**: formal sums of elementary tensors:
  `sum_i (a_i tensor b_i)` where `a_i in S1`, `b_i in S2`
- **Plus** (`oplus`): concatenation of term lists, then simplification
- **Times** (`otimes`): bilinear expansion:
  ```
  (sum_i a_i tensor b_i) otimes (sum_j c_j tensor d_j)
    = sum_{i,j} (a_i otimes_1 c_j) tensor (b_i otimes_2 d_j)
  ```
- **Zero**: empty sum (no terms)
- **One**: `1_1 tensor 1_2` (single elementary tensor of identities)

### 2.2. Comparison with Product Weight

| Property | `ProductWeight<S1, S2>` | `TensorWeight<S1, S2>` |
|----------|-------------------------|------------------------|
| Representation | Single pair `(s1, s2)` | Sum of pairs `sum (s1_i, s2_i)` |
| Plus | Component-wise | Union of term lists + merge |
| Times | Component-wise | Bilinear (all pairwise) |
| Interaction | None (independent) | Cross-analysis correlation |
| Projections | Trivial (`left`/`right`) | Marginalizes: `sum s1_i` or `sum s2_i` |
| Conditional | Not possible | `left_given_right`, `right_given_left` |

### 2.3. Simplification

To keep representations finite, terms with equal first components are merged
by summing their second components:

```
... + (a tensor b_1) + (a tensor b_2) + ...
  = ... + (a tensor (b_1 oplus_2 b_2)) + ...
```

Zero terms (where either component is the semiring zero) are removed.

### 2.4. Capacity Bound

The maximum number of elementary tensors is bounded by `MAX_TENSOR_TERMS = 8`.
When the bilinear product would exceed this limit, the result is truncated.
This makes the tensor product a **bounded approximation** of the ideal algebraic
tensor product, trading exactness for bounded memory.

### 2.5. Projections

**Definition (Marginal Projection).**
- `project_left: TensorWeight<S1, S2> -> S1`:
  `project_left(sum a_i tensor b_i) = oplus_1 a_i`
- `project_right: TensorWeight<S1, S2> -> S2`:
  `project_right(sum a_i tensor b_i) = oplus_2 b_i`

**Definition (Conditional Projection).**
- `left_given_right(r): TensorWeight<S1, S2> -> S1`:
  `oplus_1 {a_i | b_i == r}` (left components where right component equals `r`)
- `right_given_left(l): TensorWeight<S1, S2> -> S2`:
  `oplus_2 {b_i | a_i == l}` (right components where left component equals `l`)

## 3. Algorithm Pseudocode

### 3.1. Tensor Plus (Combine)

```
function plus(self: TensorWeight<W1, W2>, other: TensorWeight<W1, W2>)
    -> TensorWeight<W1, W2>:

    if self.is_zero(): return other
    if other.is_zero(): return self

    // Concatenate term lists
    result := empty tensor weight
    for term in self.terms:
        result.add_term(term)
    for term in other.terms:
        result.add_term(term)

    return result.simplify()
```

### 3.2. Tensor Times (Bilinear)

```
function times(self: TensorWeight<W1, W2>, other: TensorWeight<W1, W2>)
    -> TensorWeight<W1, W2>:

    if self.is_zero() or other.is_zero(): return zero()
    if self.is_one(): return other
    if other.is_one(): return self

    // Bilinear expansion: all pairwise products
    result := empty tensor weight
    for (a, b) in self.terms:
        for (c, d) in other.terms:
            w1 := a otimes_1 c
            w2 := b otimes_2 d
            if not w1.is_zero() and not w2.is_zero():
                result.add_term((w1, w2))

    return result.simplify()
```

### 3.3. Simplification

```
function simplify(self: TensorWeight<W1, W2>) -> TensorWeight<W1, W2>:
    // Step 1: Remove zero terms
    terms := filter(self.terms, |(a, b)| !a.is_zero() && !b.is_zero())

    // Step 2: Merge terms with equal first components
    merged := HashMap<W1, W2>
    for (a, b) in terms:
        if a in merged:
            merged[a] := merged[a] oplus_2 b
        else:
            merged[a] := b

    // Step 3: Sort by first component for canonical ordering
    result := sort(merged.entries(), by first component)

    // Step 4: Remove terms where merged second component became zero
    result := filter(result, |(_, b)| !b.is_zero())

    return TensorWeight(result, truncated to MAX_TENSOR_TERMS)
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `plus` | O(T1 + T2) | O(T1 + T2) |
| `times` (bilinear) | O(T1 * T2) | O(T1 * T2) |
| `simplify` | O(T * log T) | O(T) |
| `project_left` | O(T) | O(1) |
| `project_right` | O(T) | O(1) |
| `left_given_right` | O(T) | O(1) |
| `right_given_left` | O(T) | O(1) |
| `is_zero` | O(1) | O(1) |
| `is_one` | O(1) | O(1) |

Where: T = number of elementary tensors (bounded by `MAX_TENSOR_TERMS = 8`),
T1 and T2 = term counts in the two operands.

Since `MAX_TENSOR_TERMS = 8`, all operations are effectively O(1) in practice.

## 5. Unicode Diagrams

### 5.1. Tensor Product vs. Product Weight

```
    ProductWeight<Tropical, Counting>

    ┌─────────────────────────────────┐
    │  Single pair: (cost, count)     │
    │  (3.0, 5)                       │
    │                                 │
    │  plus: (min(a1,b1), a2+b2)      │
    │  times: (a1+b1, a2*b2)          │
    │  No correlation information     │
    └─────────────────────────────────┘

    TensorWeight<Tropical, Counting>

    ┌─────────────────────────────────┐
    │  Sum of pairs:                  │
    │  (3.0 tensor 2) + (5.0 tensor 3)│
    │                                 │
    │  "Cost 3.0 via 2 paths,         │
    │   cost 5.0 via 3 paths"         │
    │                                 │
    │  Conditional: left_given_right(2)│
    │  = 3.0 (cheapest 2-path cost)   │
    └─────────────────────────────────┘
```

### 5.2. Bilinear Multiplication

```
    (a1 tensor b1 + a2 tensor b2) otimes (c1 tensor d1)

    = (a1 otimes c1) tensor (b1 otimes d1)
      + (a2 otimes c1) tensor (b2 otimes d1)

    Tropical x Counting example:
    ((1.0 tensor 2) + (3.0 tensor 4)) otimes (0.5 tensor 3)

    = (1.0+0.5) tensor (2*3) + (3.0+0.5) tensor (4*3)
    = (1.5 tensor 6) + (3.5 tensor 12)

    "Path of cost 1.5 contributes 6 derivations,
     path of cost 3.5 contributes 12 derivations"
```

### 5.3. Simplification Example

```
    Before simplification:
    (1.0 tensor 2) + (1.0 tensor 5) + (2.0 tensor 7)

    Step 1: Merge terms with equal first component (1.0):
    (1.0 tensor (2+5)) + (2.0 tensor 7)
    = (1.0 tensor 7) + (2.0 tensor 7)

    After simplification: 2 terms (down from 3)
```

### 5.4. Architecture

```
    Analysis 1 (Tropical: min-cost)
          │
          │     ┌─────────────────────────────────┐
          ├────>│   TensorWeight<Tropical, Counting> │
          │     │                                 │
    Analysis 2  │   Captures correlations:        │
    (Counting:  │   "which costs come from which  │
     path count)│    multiplicities?"              │
          │     │                                 │
          ├────>│   Projections:                   │
          │     │     project_left() -> min cost   │
                │     project_right() -> total paths│
                │     left_given_right(k) -> min    │
                │       cost among k-path bundles   │
                └─────────────────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `TensorWeight::elementary(w1, w2)` -- Creates a single elementary tensor.
- `TensorWeight::from_pairs(pairs)` -- Creates from a slice of `(W1, W2)` pairs.
- `TensorWeight::plus(other)` -- Semiring combine (term list concatenation + simplify).
- `TensorWeight::times(other)` -- Semiring extend (bilinear expansion + simplify).
- `TensorWeight::project_left()` -- Marginal projection to S1.
- `TensorWeight::project_right()` -- Marginal projection to S2.
- `TensorWeight::left_given_right(r)` -- Conditional projection.
- `TensorWeight::right_given_left(l)` -- Conditional projection.
- `TensorWeight::simplify()` -- Merge equal first components, remove zeros.

### 6.2. Lint Emission

No direct lint output. The tensor product is used internally by other analyses
(e.g., CEGAR with correlated weights, Newton's method with tensor product
semirings).

### 6.3. Repair Integration

No repairs. The tensor product is a weight domain, not a verifier.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `TensorWeight<W1, W2>` | Array-backed sum of elementary tensors: `terms: [(W1, W2); MAX_TENSOR_TERMS]`, `len: usize` |
| `MAX_TENSOR_TERMS` | Capacity constant = 8 |

The implementation uses a **fixed-size array** (`[(W1, W2); MAX_TENSOR_TERMS]`)
rather than a `Vec` to avoid heap allocation. The `len` field tracks the
actual number of valid terms. This makes `TensorWeight` `Copy`-able when both
`W1` and `W2` are `Copy`.

Equality (`PartialEq`) is implemented via sorted comparison: both tensor weights
are sorted by first component, then compared element-wise.

The `Semiring` trait is implemented for `TensorWeight<W1, W2>` where both
`W1: Semiring` and `W2: Semiring`. The `is_zero()` check tests `len == 0`.
The `is_one()` check tests `len == 1` and both components are one.

## 8. Worked Example

**Scenario:** Analyze a grammar with both minimum cost (Tropical) and path
count (Counting) simultaneously.

```
Two parse paths:
  Path A: cost 2.0, appears in 3 derivations
  Path B: cost 5.0, appears in 7 derivations
```

**Tensor representation:**
```
t = (2.0 tensor 3) + (5.0 tensor 7)
```

**Queries:**

```
// What is the minimum cost across all paths?
t.project_left() = min(2.0, 5.0) = 2.0

// How many total derivations?
t.project_right() = 3 + 7 = 10

// How many derivations have cost 2.0?
t.right_given_left(2.0) = 3

// What is the minimum cost among 7-derivation paths?
t.left_given_right(7) = 5.0
```

**Composition with another tensor:**
```
u = (1.0 tensor 2)

t * u = (2.0+1.0 tensor 3*2) + (5.0+1.0 tensor 7*2)
      = (3.0 tensor 6) + (6.0 tensor 14)

"Composed path: cost 3.0 with 6 derivations, cost 6.0 with 14 derivations"
```

**Simplification example:**
```
v = (2.0 tensor 3) + (2.0 tensor 5) + (5.0 tensor 7)

v.simplify():
  Merge terms with equal first component 2.0:
  (2.0 tensor (3+5)) + (5.0 tensor 7)
  = (2.0 tensor 8) + (5.0 tensor 7)

  Result: 2 terms.
```

## 9. References

1. Reps, T., Turetsky, E. & Prabhu, P. (2016).
   "Newtonian Program Analysis via Tensor Product."
   *Proc. 43rd ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)*, pp. 663--677.

2. Esparza, J., Kiefer, S. & Luttenberger, M. (2010).
   "Newtonian Program Analysis."
   *Journal of the ACM*, 57(6), Article 33.

3. Green, T.J., Karvounarakis, G. & Tannen, V. (2007).
   "Provenance Semirings."
   *Proc. 26th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database
   Systems (PODS)*, pp. 31--40.

4. Droste, M. & Kuich, W. (2009).
   "Semirings and Formal Power Series."
   In *Handbook of Weighted Automata*, Springer, pp. 3--28.

5. Mohri, M. (2009).
   "Weighted Automata Algorithms."
   In *Handbook of Weighted Automata*, Springer, pp. 213--254.
