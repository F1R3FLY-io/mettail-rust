# ProductWeight -- Design & Pipeline Integration

The product semiring `S1 x S2` computes two metrics simultaneously, applying
`plus` and `times` component-wise. PraTTaIL uses it for joint optimization:
finding the parse that is both highest-priority (TropicalWeight) AND satisfies
a secondary criterion (CountingWeight for confidence, EditWeight for repair
quality).

---

## 1. Role in Pipeline

ProductWeight enables multi-objective optimization via `viterbi_generic()` in
`lattice.rs:484-535`. Rather than running two separate Viterbi passes (one per
metric) and reconciling results, a single pass over the product semiring yields
the jointly optimal path.

| Instantiation | Semantics | Use Case |
|---------------|-----------|----------|
| `ProductWeight<TropicalWeight, CountingWeight>` | Best parse + "was it unique?" | Confidence metric for dispatch decisions |
| `ProductWeight<TropicalWeight, EditWeight>` | Best parse + fewest repairs | Optimal error recovery |

Both instantiations compose naturally because ProductWeight satisfies all
semiring axioms when its components do.

---

## 2. Design Decision: Lexicographic Ord

`Ord` compares the left component first, then the right (`semiring.rs:590-594`):

```rust
impl<S1: Semiring + Ord, S2: Semiring + Ord> Ord for ProductWeight<S1, S2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left.cmp(&other.left)
            .then_with(|| self.right.cmp(&other.right))
    }
}
```

**Rationale**:

Lexicographic ordering makes the left component the **primary discriminator**.
For `ProductWeight<TropicalWeight, EditWeight>`:

1. First, select the path with the lowest tropical weight (best parse quality).
2. Among paths with equal tropical weight, select the one with the fewest edits.

This is the correct priority for error recovery: parse quality dominates edit
count. Two paths with tropical costs 1.0 and 2.0 are not comparable by edit
count -- the 1.0-cost path wins regardless of how many edits it required.

**Note on component-wise plus**: The `plus` operation is component-wise
(`semiring.rs:548-552`), which means it applies `min` to each component
independently. This is the standard product semiring definition. The
lexicographic ordering is used only by `Ord` (for Viterbi and sorting), not by
`plus`. The distinction matters: `plus` defines the semiring algebra, while
`Ord` defines the path comparison used by shortest-path algorithms.

---

## 3. Design Decision: Component-Wise is_zero

A product weight is zero if **either** component is zero (`semiring.rs:564-566`):

```rust
fn is_zero(&self) -> bool {
    self.left.is_zero() || self.right.is_zero()
}
```

**Rationale**:

The zero-annihilation axiom requires `zero * a = a * zero = zero`. Since
`times` is component-wise:

```
(zero_L, x_R) * (a_L, b_R) = (zero_L * a_L, x_R * b_R) = (zero_L, ...)
```

The left component is already zero, so the product must be zero regardless of
the right component. Using `||` (either-zero) correctly implements this: if any
dimension is unreachable, the entire product path is unreachable.

The `is_one` check uses `&&` (`semiring.rs:569-571`) for the dual reason:
both components must be the multiplicative identity for the product to be the
identity.

---

## 4. Generic Viterbi Support

`viterbi_generic()` (`lattice.rs:484-535`) works with any semiring that
implements `Semiring + Ord`:

```rust
pub fn viterbi_generic<T: Clone, S: Clone, W: Semiring + Ord>(
    lattice: &TokenLattice<T, S, W>,
    final_node: usize,
) -> Option<ViterbiPath<T, S, W>> {
    // ...
    let mut dist = vec![W::zero(); num_nodes];
    dist[0] = W::one();
    // Relaxation: for each edge, dist[to] = dist[to].plus(&dist[from].times(&edge.weight))
    // ...
}
```

**Key invariant**: Viterbi requires `zero` to be the "worst" value (identity for
`plus`, which selects the "best"). For min-semirings (Tropical, Edit), zero =
infinity, which is correctly the largest value under `Ord`. The algorithm
initializes all distances to zero (infinity), then relaxes toward one (0.0).

### CountingWeight Caveat

CountingWeight has `zero = 0` and `one = 1`. Under natural `u64` ordering,
`0 < 1`, meaning zero is the **smallest** value. But Viterbi initialization
sets `dist[i] = zero` for all non-start nodes, expecting zero to be "worse
than any real path." With CountingWeight, `zero = 0` is actually **better**
than `one = 1` under `Ord`, so the algorithm immediately considers all nodes
"reached by a 0-count path" and produces nonsensical results.

**Workaround**: Never use CountingWeight directly in `viterbi_generic()`. Instead,
compose it with TropicalWeight via ProductWeight:

```rust
type Confidence = ProductWeight<TropicalWeight, CountingWeight>;
```

The lexicographic ordering ensures TropicalWeight (which has correct
zero > one ordering) dominates, making the product safe for Viterbi. The
CountingWeight component is carried along as metadata, not used for path
selection.

This caveat is tested in `lattice.rs:1014-1025`:

```rust
// Verify that viterbi_generic returns None (node 2 appears "already
// reached" at zero=0 which is smallest under Ord)
let mut lattice: TokenLattice<TestToken, TestSpan, CountingWeight> = TokenLattice::new();
// ... add edges ...
let result = viterbi_generic(&lattice, 2);
// result behavior is undefined for CountingWeight — do not rely on it
```

---

## 5. Instantiation Patterns

### 5a. Tropical x Counting: Confidence Metric

```rust
type Confidence = ProductWeight<TropicalWeight, CountingWeight>;

// Usage: "Is the best parse unique?"
let pw = Confidence::new(
    TropicalWeight::new(1.0),   // best path cost
    CountingWeight::new(1),     // 1 derivation = unique
);
```

If `right.count() == 1`, the best parse is unambiguous. If `count > 1`,
multiple rules competed and the tropical winner may not be the intended parse.

This is currently used at codegen time in `predict_with_confidence()`
(`wfst.rs:169-173`). Runtime Viterbi over this product type is reserved for
future incremental re-parsing where confidence scores guide cache invalidation.

### 5b. Tropical x Edit: Error Tolerance

```rust
type Recovery = ProductWeight<TropicalWeight, EditWeight>;

// Usage: "Best parse with fewest repairs"
let pw = Recovery::new(
    TropicalWeight::new(2.0),   // repair path cost
    EditWeight::new(3),         // 3 token-level edits
);
```

Two repair strategies with equal tropical cost (e.g., both 2.0) are
distinguished by edit count. The strategy requiring fewer edits wins. This
prevents the optimizer from choosing a "clever" repair (e.g., substitute 5
tokens) over a simpler one (skip 2 tokens) when both reach the same sync point.

---

## 6. Component-Wise Plus vs Lexicographic Ord

It is important to distinguish the `plus` operation from the `Ord` comparison:

| Operation | Behavior | Used By |
|-----------|----------|---------|
| `plus` | Component-wise: `(min(L), min(R))` for Tropical x Edit | Semiring algebra, path merging |
| `Ord::cmp` | Lexicographic: left first, then right | Viterbi relaxation, sorting |

For `plus`, the result may not be a "real" weight seen on any single path -- it
is the component-wise best. This is the standard product semiring definition and
is algebraically correct.

For `Ord`, the comparison answers "which of two weights is better?" and uses
lexicographic ordering. Viterbi uses `Ord` to decide whether a new path improves
the current best at each node.

---

## 7. Hash and Eq Consistency

ProductWeight derives `Hash` component-wise (`semiring.rs:596-603`) and `Eq`
via `PartialEq` (`semiring.rs:512, 578`). The consistency invariant
`a == b => hash(a) == hash(b)` holds because both delegate to the component
types' implementations.

Both TropicalWeight and EditWeight have consistent `Eq`/`Hash` (via `total_cmp`
and native `u32` respectively), so their product inherits consistency.

---

## 8. Source Reference & See Also

- **Type definition**: `semiring.rs:492-620`
- **Lexicographic Ord**: `semiring.rs:586-594`
- **Generic Viterbi**: `lattice.rs:484-535`
- **Lattice generics**: `lattice.rs:225-240, 315-327` (`TokenLattice<T, S, W>`)
- **Product tests**: `semiring.rs:1148-1245` (7 tests covering laws, is_zero, ordering)
- **Viterbi generic tests**: `lattice.rs:955-1067` (EditWeight, ProductWeight, CountingWeight caveat)
- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- section 10
- **Component semirings**: `tropical-weight.md`, `edit-weight.md`, `counting-weight.md`
