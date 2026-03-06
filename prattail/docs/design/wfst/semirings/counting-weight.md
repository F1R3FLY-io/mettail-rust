# CountingWeight -- Design & Pipeline Integration

The counting semiring `(N, +, x, 0, 1)` counts distinct derivations through the
prediction automaton. It answers: "How many rules can handle this token in this
category?" A count greater than 1 signals ambiguity that the tropical semiring
must resolve.

---

## 1. Role in Pipeline

CountingWeight serves two codegen-time analysis functions:

| Function                   | Location                  | Description                                                                                                                   |
|----------------------------|---------------------------|-------------------------------------------------------------------------------------------------------------------------------|
| **Ambiguity warnings**     | `prediction.rs:1545-1569` | `compute_composed_dispatch()` counts per-(category, token) derivations; count > 1 emits a diagnostic                          |
| **Confidence annotations** | `wfst.rs:158-173`         | `predict_with_confidence()` annotates each action with the total derivation count for downstream product-semiring composition |

CountingWeight is **not** used for Viterbi path extraction because its natural
ordering is incompatible with shortest-path initialization (see section on
ProductWeight for the workaround).

---

## 2. Design Decision: Saturating Arithmetic

Both `plus` (addition) and `times` (multiplication) use saturating operations
(`semiring.rs:247-253`):

```rust
fn plus(&self, other: &Self) -> Self {
    CountingWeight(self.0.saturating_add(other.0))
}

fn times(&self, other: &Self) -> Self {
    CountingWeight(self.0.saturating_mul(other.0))
}
```

**Rationale**:

Pathological grammars with deep cross-category overlaps can produce combinatorial
derivation counts. Consider a grammar with N ambiguous tokens across M
categories: the product of counts grows as `O(N^M)`. Without saturation,
multiplying large intermediate counts would wrap to small values, producing
incorrect ambiguity diagnostics.

Saturating to `u64::MAX` preserves the invariant: "if the count saturates, the
grammar has serious ambiguity issues." The exact count does not matter beyond the
threshold of `count > 1` used for warning emission.

---

## 3. Design Decision: u64 Not u32

CountingWeight uses `u64` internally (`semiring.rs:219`):

```rust
pub struct CountingWeight(pub u64);
```

**Rationale**:

- **Multiplicative growth**: `times` multiplies segment counts along a path.
  Even moderate grammars (20 categories, 50 tokens each) can produce
  intermediate products exceeding `u32::MAX` (~4.3 billion) before saturation.
- **No space penalty**: CountingWeight is a codegen-time analysis type, not
  embedded in generated code or stored in runtime lattices. The extra 4 bytes
  per weight have zero impact on parser performance or binary size.
- **Alignment**: On 64-bit targets, `u64` aligns naturally. A `u32` field would
  often be padded to 8 bytes anyway in structs containing pointers.

---

## 4. Codegen-Time Ambiguity Warnings

The composed dispatch computation in `prediction.rs:1454-1577` uses
CountingWeight to detect and report ambiguity:

```
compute_composed_dispatch()
└─ for each (category, DFA_state):
   ├─ collect entries from all matching rules
   ├─ sort entries by TropicalWeight (lowest first)
   ├─ let derivation_count = CountingWeight::new(entries.len())  // L1548
   └─ if derivation_count.count() > 1:
      └─ emit warning with:
         ├─ N-way ambiguity count
         ├─ category and DFA state
         ├─ per-alternative: token variant, rule label, weight
         └─ resolution: tropical shortest-path winner
```

Example warning output:

```
warning: 2-way ambiguity at (Bool, DFA state 3): 2 derivations
  - Token::Ident → rule Eq (weight 0.50)
  - Token::Ident → rule CastBool (weight 1.00)
  Resolved by tropical shortest path -> Eq
```

The counting semiring formalizes what would otherwise be an ad-hoc
`entries.len() > 1` check. This matters because:

1. CountingWeight satisfies all semiring axioms, ensuring the count is
   well-defined under path composition and alternative merging.
2. The `predict_with_confidence()` method (see next section) propagates the
   count to downstream consumers, maintaining the semiring abstraction.

---

## 5. Relationship to Composed Dispatch

The composed dispatch table (`prediction.rs:1718-1738`) resolves ambiguous
tokens by selecting the tropical shortest-path winner:

```
resolve_dispatch_winners()
  for each (category, state_id, entries):
    for each entry:
      key = (category, token_variant_name)
      if entry.weight < existing winner's weight:
        update winner
  returns: BTreeMap<(category, token), (winning_rule, weight)>
```

CountingWeight informs this process at the diagnostic level -- it identifies
**which** (category, token) pairs need resolution. The resolution itself uses
TropicalWeight to pick the winner.

`predict_with_confidence()` (`wfst.rs:169-173`) bridges the two semirings:

```rust
pub fn predict_with_confidence(&self, token_name: &str)
    -> Vec<(&WeightedAction, CountingWeight)>
{
    let actions = self.predict(token_name);
    let count = CountingWeight::new(actions.len() as u64);
    actions.into_iter().map(|a| (a, count)).collect()
}
```

Each action carries both its TropicalWeight (for ranking) and the total
CountingWeight (for ambiguity awareness). This enables composition via
`ProductWeight<TropicalWeight, CountingWeight>` -- the "confidence metric"
pattern described in `product-weight.md`.

---

## 6. Non-Idempotency

Unlike TropicalWeight and EditWeight, CountingWeight is **not** idempotent:

```
plus(3, 3) = 6, not 3
```

This is correct: merging two paths that each contribute 3 derivations yields 6
total derivations. Idempotency would incorrectly collapse the count.

This property makes CountingWeight unsuitable for direct Viterbi shortest-path:
the Viterbi algorithm relies on `plus(a, a) = a` (or at minimum, monotonic
relaxation). CountingWeight violates this because `zero = 0` is the smallest
value under natural ordering, but Viterbi initialization requires zero to be the
largest (worst) value. The workaround is composition via ProductWeight -- see
`product-weight.md` section 4.

---

## 7. Source Reference & See Also

- **Type definition**: `semiring.rs:200-281`
- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- section 6
- **Composed dispatch**: `prattail/docs/design/composed-dispatch.md`
- **Product semiring**: `product-weight.md` -- Tropical x Counting composition
- **Prediction design**: `prattail/docs/design/wfst/prediction.md` (if present)
