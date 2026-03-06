# EditWeight -- Design & Pipeline Integration

The edit-distance semiring `(N U {inf}, min, +, inf, 0)` counts the minimum
number of token-level edits required for error recovery. It is isomorphic to
the tropical semiring over the naturals but carries distinct semantics: values
represent discrete edit operations, not arbitrary continuous costs.

---

## 1. Role in Pipeline

EditWeight is exposed through `RepairAction::edit_cost()` in `recovery.rs:141-161`.
Each repair action produced by the recovery WFST is annotated with its edit
distance:

```rust
pub fn edit_cost(&self) -> EditWeight {
    match self {
        RepairAction::SkipToSync { skip_count, .. } => EditWeight::new(*skip_count as u32),
        RepairAction::DeleteToken => EditWeight::delete(),
        RepairAction::InsertToken { .. } => EditWeight::insert(),
        RepairAction::SubstituteToken { .. } => EditWeight::substitute(),
    }
}
```

This method runs at parse time, only when an error triggers recovery. The happy
path (no errors) never allocates or consults EditWeight.

---

## 2. Design Decision: u32 Not f64

EditWeight wraps `u32` (`semiring.rs:385`):

```rust
pub struct EditWeight(pub u32);
```

**Rationale**:

- **Discrete operations**: An edit is a whole operation -- you cannot perform
  half a token insertion. Integer representation enforces this at the type level.
- **Exact comparison**: Integer equality and ordering are exact. Float comparison
  requires epsilon thresholds, which adds complexity for no benefit when values
  are inherently integral.
- **No precision drift**: Accumulating many small float costs (e.g., 0.5 + 0.5
  + ...) can drift due to floating-point representation. Integer addition is
  exact for all values below `u32::MAX`.

The tradeoff is that EditWeight cannot represent fractional costs. This is
intentional: the cost model assigns whole-number costs to each operation, and
fractional weighting is the domain of TropicalWeight.

---

## 3. Design Decision: Asymmetric Costs

The four repair operations have asymmetric costs (`semiring.rs:403-425`):

| Operation      | Cost        | Method                     | Rationale                                              |
|----------------|-------------|----------------------------|--------------------------------------------------------|
| **Skip**       | 1 per token | `EditWeight::skip()`       | Advance past unexpected tokens -- minimally disruptive |
| **Delete**     | 1           | `EditWeight::delete()`     | Remove one unexpected token -- equivalent to skip      |
| **Insert**     | 2           | `EditWeight::insert()`     | Fabricate a missing token -- requires guessing intent  |
| **Substitute** | 2           | `EditWeight::substitute()` | Replace wrong token with expected -- requires guessing |

**Design rationale**:

Skip and delete are cheap because they only discard information. The parser
advances past tokens it does not understand, which is always valid (the skipped
tokens may be irrelevant trailing content).

Insert and substitute are expensive because they require the recovery system to
**guess** what the user intended. Inserting a missing semicolon or substituting
a `}` for a `)` may be correct, but the recovery system has limited information
to make this judgment. The higher cost biases the Viterbi shortest-path toward
skip/delete strategies, which are more conservative.

The `SkipToSync` variant accumulates cost linearly: skipping 5 tokens costs 5
edits. This naturally penalizes long skip sequences while still allowing them
when no better repair exists.

---

## 4. Design Decision: u32::MAX as Infinity

The additive identity (zero element) is `u32::MAX` (`semiring.rs:389`):

```rust
pub const INFINITY: EditWeight = EditWeight(u32::MAX);
```

**Rationale**:

- `u32::MAX` serves as a sentinel for "impossible repair" -- no sequence of
  finite edits can produce this value via saturating addition.
- Saturating arithmetic (`semiring.rs:446`) ensures that `INFINITY + n = INFINITY`
  for any `n`, preserving the zero-annihilation axiom.
- Using `u32::MAX` instead of `Option<u32>` avoids an extra byte of tag and
  keeps the type `Copy` with a simple 4-byte representation.

---

## 5. Parallel Cost Systems

PraTTaIL maintains two parallel cost systems for error recovery:

| Property      | TropicalWeight                                | EditWeight                            |
|---------------|-----------------------------------------------|---------------------------------------|
| **Domain**    | `f64` (continuous)                            | `u32` (discrete)                      |
| **Semantics** | Arbitrary priority costs                      | Token-level edit operations           |
| **Used by**   | Viterbi dispatch, beam pruning                | Repair quality metric                 |
| **Values**    | Skip: 0.5, Delete: 1.0, Sub: 1.5, Insert: 2.0 | Skip: 1, Delete: 1, Sub: 2, Insert: 2 |

The TropicalWeight costs are tuned for Viterbi shortest-path in the recovery
WFST (`recovery.rs` repair cost constants). They use fractional values (0.5 for
skip) to create finer-grained distinctions between repair strategies.

EditWeight counts raw edits regardless of strategy quality. The two systems can
be unified via `ProductWeight<TropicalWeight, EditWeight>`:

```rust
// Joint optimization: best parse quality AND minimum edits
type JointRecovery = ProductWeight<TropicalWeight, EditWeight>;
```

The product semiring's lexicographic ordering selects the best tropical cost
first, then breaks ties by minimum edit distance. This means two repairs with
equal tropical cost are distinguished by edit count -- the one requiring fewer
token changes wins.

---

## 6. Connection to liblevenshtein

EditWeight provides the formal foundation for future integration with the
`liblevenshtein` crate (`/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`).

**Current state**: EditWeight counts coarse token-level edits (skip/delete/insert
/substitute entire tokens). It does not consider character-level similarity
between tokens.

**Future direction**: Compose the recovery WFST with a Levenshtein automaton
from liblevenshtein for token-level fuzzy matching:

1. When the parser encounters an unexpected `Token::Ident("functoin")`, the
   recovery system queries a `DynamicDawg` dictionary of expected keywords.
2. The Levenshtein automaton finds `"function"` at edit distance 1.
3. The substitute cost becomes `EditWeight::new(1)` (character-level) instead
   of `EditWeight::substitute()` (fixed cost 2), enabling cheaper recovery
   for likely typos.

This would bridge the token-level edit model (EditWeight) with character-level
error correction (liblevenshtein's Levenshtein/phonetic automata), composing
naturally via the semiring's `times` operation.

---

## 7. Semiring Isomorphism

EditWeight is isomorphic to TropicalWeight restricted to non-negative integers:

```
phi: EditWeight(n) -> TropicalWeight(n as f64)
phi(a.plus(b))  = phi(a).plus(phi(b))    // min commutes
phi(a.times(b)) = phi(a).times(phi(b))   // add commutes
phi(zero)       = TropicalWeight::infinity()
phi(one)        = TropicalWeight::one()
```

Despite this isomorphism, the types are kept separate because:

1. **Type safety**: A function accepting `EditWeight` cannot accidentally receive
   a TropicalWeight and vice versa, preventing semantic confusion.
2. **Integer precision**: EditWeight arithmetic is exact; TropicalWeight loses
   precision for large values.
3. **Documentation**: The type name communicates intent -- `edit_cost()` returns
   an EditWeight, not a generic weight.

---

## 8. Source Reference & See Also

- **Type definition**: `semiring.rs:365-490`
- **Pipeline usage**: `recovery.rs:141-161` (`RepairAction::edit_cost()`)
- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- section 8
- **Product composition**: `product-weight.md` -- Tropical x Edit joint optimization
- **Error recovery design**: `prattail/docs/design/wfst/error-recovery.md` (if present)
- **liblevenshtein**: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`
