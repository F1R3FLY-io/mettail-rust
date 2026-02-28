# EditWeight: Edit-Distance Semiring

> **Source**: `prattail/src/automata/semiring.rs`, lines 369--490
> **Carrier**: `EditWeight(pub u32)` -- discrete token-level edit counts

---

## 1. Intuition & Motivation

When a parser encounters a syntax error, it must *recover*: skip tokens,
insert missing ones, delete unexpected ones, or substitute wrong tokens for
correct ones.  Each of these repair actions has an inherent cost.  EditWeight
bridges the worlds of **parsing** and **error correction** by encoding those
costs as a semiring, enabling the same WFST shortest-path machinery that
handles token dispatch to also find the minimum-cost repair strategy.

Unlike TropicalWeight, which assigns arbitrary real-valued costs tuned for
Viterbi optimization, EditWeight counts **discrete operations**.  A skip costs
1.  A delete costs 1.  An insert costs 2.  A substitute costs 2.  These are
not abstract priorities -- they are concrete edit operations that the parser
must perform.  This semantic grounding makes EditWeight directly interpretable:
"this recovery required 3 edits" is a meaningful statement, whereas "this
recovery cost 2.7 tropical units" is not.

---

## 2. Formal Definition

The edit-distance semiring is the algebraic structure:

    E = (N union {infinity}, min, +, infinity, 0)

where N = {0, 1, 2, 3, ...} denotes the natural numbers.  Concretely:

| Component         | Symbol | Meaning                         |
|-------------------|--------|---------------------------------|
| Carrier set       | K      | N union {infinity}              |
| Addition          | ⊕      | min (minimum)                   |
| Multiplication    | ⊗      | + (saturating addition)         |
| Additive identity | 0      | infinity (impossible repair)    |
| Multiplicative id | 1      | 0 (no edits needed)             |

In WFST terms:

- **⊕ = min** selects the repair strategy with the fewest total edits.
- **⊗ = +** accumulates edit counts along a repair path (if segment A
  requires 2 edits and segment B requires 3 edits, the path costs 5).
- **0 = infinity** represents an impossible repair -- the additive identity
  (min(infinity, x) = x for all x).
- **1 = 0** represents a perfect match -- the multiplicative identity
  (0 + x = x for all x).

### 2.1 Structural isomorphism with Tropical

EditWeight over N union {infinity} and TropicalWeight over R+ union {+infinity}
share the same algebraic skeleton: (K, min, +, infinity, 0).  They are
structurally isomorphic as semirings -- the operations have the same names and
satisfy the same laws.  The distinction is **semantic**, not algebraic:

| Aspect          | TropicalWeight         | EditWeight                |
|-----------------|------------------------|---------------------------|
| Carrier         | R+ (continuous)        | N (discrete)              |
| Values mean     | Priority / cost        | Edit operation counts     |
| Precision       | f64 (64-bit float)     | u32 (32-bit unsigned int) |
| Overflow        | IEEE 754 infinity      | Saturating at u32::MAX    |
| Interpretation  | "lower is better"      | "fewer edits is better"   |

This isomorphism is exploited in PraTTaIL: since both semirings use min/+,
the same Viterbi shortest-path algorithm works for both dispatch (Tropical)
and recovery (Edit), and they can be composed via ProductWeight.

---

## 3. Semiring Axiom Verification

We verify the semiring axioms with concrete integer examples.

### 3.1 (K, ⊕, 0) is a commutative monoid

**Closure**: min maps (N union {infinity})^2 into N union {infinity}.

**Associativity**: min(a, min(b, c)) = min(min(a, b), c)

    Example: min(3, min(1, 5)) = min(3, 1) = 1
             min(min(3, 1), 5) = min(1, 5) = 1    Check.

This holds for all a, b, c since min is associative over any totally ordered
set.

**Identity**: min(infinity, a) = a and min(a, infinity) = a

    Example: min(infinity, 7) = 7.  Check.
    Example: min(7, infinity) = 7.  Check.

**Commutativity**: min(a, b) = min(b, a)

    Example: min(3, 5) = 3 = min(5, 3).  Check.

### 3.2 (K, ⊗, 1) is a monoid

**Closure**: saturating_add maps (N union {infinity})^2 into N union {infinity}.

**Associativity**: (a + b) + c = a + (b + c)

    Example: (2 + 3) + 4 = 5 + 4 = 9
             2 + (3 + 4) = 2 + 7 = 9              Check.

Saturating addition is associative: if overflow occurs, the result saturates
to u32::MAX regardless of grouping.

**Identity**: 0 + a = a and a + 0 = a

    Example: 0 + 5 = 5.  Check.

### 3.3 Distributivity

**Left**: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c), i.e., a + min(b, c) = min(a + b, a + c)

    Example: 2 + min(3, 5) = 2 + 3 = 5
             min(2 + 3, 2 + 5) = min(5, 7) = 5    Check.

General proof: WLOG assume b <= c.  Then min(b, c) = b, so
LHS = a + b.  Also a + b <= a + c (monotonicity of addition), so
min(a + b, a + c) = a + b = RHS.

**Right**: follows by commutativity of addition.

### 3.4 Zero annihilation: 0 ⊗ a = a ⊗ 0 = 0

    infinity + a = infinity   (saturating: u32::MAX + anything = u32::MAX)
    a + infinity = infinity   (likewise)

    Example: u32::MAX + 5 = u32::MAX.  Check.

All semiring axioms hold.  QED.

---

## 4. Key Properties

### 4.1 Commutativity of ⊗

Addition on N is commutative (a + b = b + a), and saturating addition
preserves this property.  Therefore EditWeight is a **commutative semiring**.

    Proof: For all a, b in N union {infinity},
           a.saturating_add(b) = b.saturating_add(a).
    This follows from commutativity of integer addition and the symmetric
    definition of saturation.

### 4.2 Idempotency of ⊕

Addition ⊕ = min is idempotent:

    min(a, a) = a    for all a in N union {infinity}

    Proof: min selects the smaller of two values.  When both are equal,
    the result is that value.  Formally, a <= a, so min(a, a) = a.

Idempotency means that discovering the same repair path twice does not change
the optimal cost.  This is the correct semantics for optimization: we want the
minimum, not a sum of alternatives.

### 4.3 Integer-valued (unlike Tropical's reals)

EditWeight is restricted to N union {infinity} rather than R+ union {+infinity}.
This has practical consequences:

1. **Exact comparison**: No floating-point epsilon needed.  `approx_eq` simply
   checks `self.0 == other.0`.
2. **Deterministic hashing**: `u32` hashes deterministically, unlike `f64`
   which requires `to_bits()` normalization.
3. **Bounded range**: u32::MAX = 4,294,967,295, which is sufficient for any
   practical repair sequence (a 4-billion-edit recovery would not be useful).
4. **Semantic clarity**: "3 edits" is unambiguous; "3.0 tropical weight" is
   not.

---

## 5. Edit Operations & Costs

PraTTaIL defines four token-level repair actions with asymmetric costs:

| Operation      | Method                | Cost | Rationale                          |
|----------------|-----------------------|------|------------------------------------|
| **Skip**       | `EditWeight::skip()`  | 1    | Skip past unexpected token         |
| **Delete**     | `EditWeight::delete()` | 1   | Remove unexpected token            |
| **Insert**     | `EditWeight::insert()` | 2   | Fabricate a missing token          |
| **Substitute** | `EditWeight::substitute()` | 2 | Replace wrong token with correct one |

### 5.1 Cost asymmetry rationale

Skip and delete cost 1 because they consume a concrete token that already
exists in the input stream -- the parser simply ignores it.  This is a
relatively safe operation: the token was produced by the lexer, is syntactically
well-formed, and its removal affects at most the local parse context.

Insert and substitute cost 2 because they **fabricate** information:

- **Insert**: creates a phantom token that was never in the input.  This is
  more disruptive because the inserted token may not match the programmer's
  intent -- it is a guess.
- **Substitute**: replaces a real token with a different one, which both
  removes the original (cost 1) and fabricates a replacement (cost 1),
  yielding a combined cost of 2.

This 1:2 ratio biases the recovery system toward consuming existing tokens
(skip/delete) over inventing new ones (insert/substitute), which aligns with
the principle of minimal surprise: it is better to silently skip a misplaced
semicolon than to invent one where none was written.

### 5.2 SkipToSync: variable cost

The SkipToSync action has a variable cost equal to the number of tokens
skipped.  If the parser skips 4 tokens to reach a synchronization point,
the edit cost is EditWeight::new(4).  This linearly penalizes long skips,
preferring shorter recoveries.

---

## 6. Edit Transducer

The edit-distance computation can be modeled as a single-state WFST (a
**transducer**) with four self-loop arcs -- one per edit operation:

```
                  ┌─────────────────────────────────────┐
                  │                                     │
        ε:t / 2  │    a:ε / 1     a:a / 0    a:b / 2  │
     ┌───────────>│<──────────┐ ┌──────────┐ ┌─────────┘
     │            │           │ │          │ │
     │          ┌─┴─┐        │ │          │ │
     └──────────│ q │────────┘ └──────────┘ └──────────>
                └───┘
                 (F)

    Legend:
      a:a / 0  = match (input a, output a, cost 0)
      a:ε / 1  = delete (input a, output empty, cost 1)
      ε:t / 2  = insert (input empty, output t, cost 2)
      a:b / 2  = substitute (input a, output b, cost 2)
```

Here `a` denotes any input token, `b` denotes a different expected token,
`t` denotes an expected sync token, and `ε` denotes the empty string.

- **Match arc** (a:a / 0): when the input token matches the expected token,
  pass it through at zero cost.  This is the identity (⊗-identity = 0).
- **Delete arc** (a:epsilon / 1): consume one input token, produce nothing.
  Cost = 1.
- **Insert arc** (epsilon:t / 2): consume no input, produce an expected token.
  Cost = 2.
- **Substitute arc** (a:b / 2): consume one input token, produce a different
  expected token.  Cost = 2.

The Viterbi shortest path through this transducer, when composed with the
parser's expectation automaton, yields the minimum-cost repair sequence.

---

## 7. Minimum-Repair Parsing

### 7.1 Composition model

Given:
- **E**: the edit transducer from Section 6 (single-state WFST)
- **P**: the parser's prediction automaton (from prediction WFST)

The composition **E circle P** produces a transducer that maps erroneous input
sequences to the closest valid parse, weighted by EditWeight.

The Viterbi shortest path through E circle P gives the **minimum-repair parse**:
the valid parse tree that requires the fewest token-level edits from the actual
input.

### 7.2 Worked example

Consider a parser expecting the token sequence `INT PLUS INT` and receiving
the erroneous input `INT INT PLUS INT`:

```
Input:    INT   INT   PLUS   INT
Expected: INT   PLUS  INT

Step 1: INT matches INT.          Cost: 0    Running total: 0
Step 2: INT does not match PLUS.
  - Delete INT (cost 1)   -> total 1, remaining: PLUS INT
  - Substitute INT->PLUS (cost 2) -> total 2, remaining: INT
  - Skip INT (cost 1)     -> total 1, remaining: PLUS INT
Step 3 (after delete/skip): PLUS matches PLUS.  Cost: 0.  Total: 1
Step 4: INT matches INT.          Cost: 0    Running total: 1

Optimal repair: delete the extra INT at position 2.  Total cost: 1 edit.
```

Diagram of the repair lattice:

```
  State 0         State 1         State 2         State 3         State 4
  (start)                                                         (accept)
    │               │               │               │               │
    │  INT:INT/0    │  INT:ε/1      │  PLUS:PLUS/0  │  INT:INT/0    │
    ├──────────────>├──────────────>├──────────────>├──────────────>│
    │               │               │               │               │
    │               │  INT:PLUS/2   │               │               │
    │               ├──────────────>│               │               │
    │                               │  INT:INT/0    │               │
    │                               ├──────────────>│               │
    │                                                               │
    └── Viterbi best path: 0 + 1 + 0 + 0 = 1 edit ────────────────┘
```

The Viterbi algorithm selects the path through state 1 that deletes the extra
INT, yielding a total cost of EditWeight(1).

---

## 8. Connection to liblevenshtein

PraTTaIL's EditWeight semiring shares deep structural connections with the
`liblevenshtein` library (located at
`/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`), which implements
Levenshtein and related automata for error correction of strings and byte
arrays.

### 8.1 Shared algebraic foundation

Both systems use the same (N union {infinity}, min, +, infinity, 0) semiring.
In `liblevenshtein`, the carrier represents character-level edit distances
(insert, delete, substitute a character).  In PraTTaIL, the carrier represents
token-level edit distances (insert, delete, substitute a token).  The
semiring operations are identical; only the granularity of the edited units
differs.

### 8.2 Integration points

**Dictionary lookup for token correction**: `liblevenshtein`'s `DynamicDawg`
(ASCII) and `DynamicDawgChar` (UTF-8) support fuzzy dictionary lookup in
linear time on the length of the query term.  This can be composed with
PraTTaIL's token-level edit transducer to provide **two-level error
correction**:

1. **Token level** (PraTTaIL): find the minimum-edit repair sequence
   (skip, delete, insert, substitute tokens).
2. **Character level** (liblevenshtein): for substitute actions, find the
   closest valid token spelling using Levenshtein automata over the language's
   keyword dictionary.

### 8.3 Automaton composition

The composition would work as follows:

```
Token-level edit WFST (PraTTaIL)
    │
    │  substitute(wrong_token, expected_token)
    │  cost = EditWeight(2)
    │
    ▼
Character-level Levenshtein automaton (liblevenshtein)
    │
    │  DynamicDawg.fuzzy_search(wrong_token.text, max_distance=2)
    │  returns: [(candidate, char_distance), ...]
    │
    ▼
Refined cost = EditWeight(2) ⊗ EditWeight(char_distance)
             = EditWeight(2 + char_distance)
```

This two-level composition enables error messages like:
"Expected `function`, found `fnction` (did you mean `function`?)"

### 8.4 Bounded error correction

`liblevenshtein`'s automata support bounded edit distance (max_distance
parameter), which aligns with PraTTaIL's recovery philosophy: we only attempt
corrections within a bounded cost to avoid expensive searches on badly
malformed input.

---

## 9. Connection to PraTTaIL Recovery

### 9.1 RepairAction::edit_cost()

The `edit_cost()` method on `RepairAction` in `recovery.rs` (line 153) maps
each repair action to its EditWeight:

```rust
pub fn edit_cost(&self) -> crate::automata::semiring::EditWeight {
    use crate::automata::semiring::EditWeight;
    match self {
        RepairAction::SkipToSync { skip_count, .. } => EditWeight::new(*skip_count as u32),
        RepairAction::DeleteToken => EditWeight::delete(),
        RepairAction::InsertToken { .. } => EditWeight::insert(),
        RepairAction::SubstituteToken { .. } => EditWeight::substitute(),
    }
}
```

This method provides a **semantic** cost for each repair action, complementing
the **operational** tropical cost used by `find_best_recovery()`.  The tropical
cost is tuned for Viterbi shortest-path quality; the edit cost counts actual
token-level disruptions.

### 9.2 Cost mapping summary

| RepairAction        | Tropical cost        | Edit cost              |
|---------------------|----------------------|------------------------|
| SkipToSync(n)       | n * 0.5              | EditWeight(n)          |
| DeleteToken         | 1.0                  | EditWeight(1)          |
| InsertToken         | 2.0                  | EditWeight(2)          |
| SubstituteToken     | 1.5                  | EditWeight(2)          |

Note the divergence for SubstituteToken: the tropical cost (1.5) is lower than
insert (2.0) to prefer substitution over insertion when the parser has a
concrete token to work with.  The edit cost (2) treats substitute and insert
equally since both fabricate a token not present in the original input.

### 9.3 Dual-cost recovery via ProductWeight

By composing the two cost models via `ProductWeight<TropicalWeight, EditWeight>`,
the recovery system can simultaneously optimize for:

1. **Parse quality** (TropicalWeight): find the recovery that leads to the
   best overall parse tree.
2. **Repair minimality** (EditWeight): among recoveries of equal parse quality,
   prefer the one with the fewest actual edits.

The lexicographic ordering of ProductWeight (left component first, then right)
ensures that parse quality is the primary criterion and edit count is the
tiebreaker.

---

## 10. Comparison Table

| Property                  | EditWeight              | TropicalWeight         | BooleanWeight        |
|---------------------------|-------------------------|------------------------|----------------------|
| **Carrier**               | N union {infinity}      | R+ union {+infinity}   | {false, true}        |
| **⊕ (plus)**              | min                     | min                    | ∨ (OR)               |
| **⊗ (times)**             | + (saturating)          | + (IEEE 754)           | ∧ (AND)              |
| **0 (zero)**              | infinity (u32::MAX)     | +infinity (f64)        | false                |
| **1 (one)**               | 0                       | 0.0                    | true                 |
| **Commutative**           | Yes                     | Yes                    | Yes                  |
| **Idempotent (⊕)**        | Yes (min(a,a) = a)     | Yes (min(a,a) = a)    | Yes (a ∨ a = a)     |
| **Precision**             | Exact (u32)             | Approximate (f64)      | Exact (bool)         |
| **Semantics**             | Edit operation count    | Priority / cost        | Reachability         |
| **PraTTaIL use**          | Recovery cost metric    | Dispatch + Viterbi     | Dead-rule detection  |
| **Rust Display**          | integer / infinity          | float / inf            | ⊤ / ⊥                |
| **Isomorphic to Tropical**| Yes (over N)            | --                     | No                   |

---

## 11. Rust Implementation

### 11.1 EditWeight struct

The complete implementation from `prattail/src/automata/semiring.rs`:

```rust
/// Edit-distance semiring `(N union {infinity}, min, +, infinity, 0)`.
///
/// Counts minimum token-level edits needed for error recovery. Isomorphic to
/// tropical over N but semantically distinct -- values represent edit operations
/// rather than arbitrary costs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EditWeight(pub u32);
```

**Constants and constructors**:

```rust
impl EditWeight {
    /// Infinite edit distance (unreachable / zero element).
    pub const INFINITY: EditWeight = EditWeight(u32::MAX);

    /// Create an edit weight with the given distance.
    #[inline]
    pub const fn new(distance: u32) -> Self {
        EditWeight(distance)
    }

    /// Get the edit distance value.
    #[inline]
    pub const fn distance(self) -> u32 {
        self.0
    }

    /// Cost of skipping one input token.
    #[inline]
    pub const fn skip() -> Self { EditWeight(1) }

    /// Cost of deleting an unexpected token.
    #[inline]
    pub const fn delete() -> Self { EditWeight(1) }

    /// Cost of inserting a missing token.
    #[inline]
    pub const fn insert() -> Self { EditWeight(2) }

    /// Cost of substituting a wrong token.
    #[inline]
    pub const fn substitute() -> Self { EditWeight(2) }
}
```

**Semiring trait implementation**:

```rust
impl Semiring for EditWeight {
    #[inline]
    fn zero() -> Self { Self::INFINITY }             // impossible repair

    #[inline]
    fn one() -> Self { EditWeight(0) }                // no edits needed

    #[inline]
    fn plus(&self, other: &Self) -> Self {             // min: best repair
        EditWeight(self.0.min(other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {            // +: accumulate edits
        EditWeight(self.0.saturating_add(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool { self.0 == u32::MAX }

    #[inline]
    fn is_one(&self) -> bool { self.0 == 0 }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0  // exact comparison (integer-valued)
    }
}
```

**Ordering**: uses the natural u32 ordering, which means lower edit distances
sort before higher ones -- the correct optimization direction (fewer edits is
better):

```rust
impl PartialOrd for EditWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EditWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}
```

**Display**: renders infinity as the unicode infinity symbol:

```rust
impl fmt::Display for EditWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}
```

**Default**: returns `one()` (= 0 edits), consistent with the convention that
the default weight is the multiplicative identity:

```rust
impl Default for EditWeight {
    fn default() -> Self { Self::one() }
}
```

### 11.2 RepairAction::edit_cost() (recovery.rs)

```rust
impl RepairAction {
    /// Return the semantic edit-distance cost of this repair action.
    ///
    /// Unlike tropical weights in `costs::*` which are tuned for Viterbi
    /// shortest-path, `EditWeight` counts discrete token-level edits:
    /// - Skip: 1 edit per skipped token
    /// - Delete: 1 edit (remove one unexpected token)
    /// - Insert: 2 edits (fabricate a missing token -- more disruptive)
    /// - Substitute: 2 edits (replace wrong token -- moderate disruption)
    ///
    /// Compose with `ProductWeight<TropicalWeight, EditWeight>` to jointly
    /// optimize parse quality and repair minimality.
    pub fn edit_cost(&self) -> crate::automata::semiring::EditWeight {
        use crate::automata::semiring::EditWeight;
        match self {
            RepairAction::SkipToSync { skip_count, .. } =>
                EditWeight::new(*skip_count as u32),
            RepairAction::DeleteToken =>
                EditWeight::delete(),
            RepairAction::InsertToken { .. } =>
                EditWeight::insert(),
            RepairAction::SubstituteToken { .. } =>
                EditWeight::substitute(),
        }
    }
}
```

---

## 12. Integration into PraTTaIL

### 12.1 How find_best_recovery() uses edit costs

The `RecoveryWfst::find_best_recovery()` method in `recovery.rs` evaluates
all four repair strategies (skip, delete, insert, substitute) and selects the
one with the minimum **tropical** cost.  After the winning strategy is chosen,
its `edit_cost()` can be queried for diagnostic reporting:

```
Parse error at position P
        │
        ▼
RecoveryWfst::find_best_recovery(tokens, pos)
        │
        ├─ Evaluate SkipToSync:  tropical = n * 0.5,  edit = n
        ├─ Evaluate DeleteToken: tropical = 1.0,       edit = 1
        ├─ Evaluate InsertToken: tropical = 2.0,       edit = 2
        ├─ Evaluate Substitute:  tropical = 1.5,       edit = 2
        │
        ├─ Select minimum tropical cost
        │
        ▼
RepairResult { action, new_pos, cost }
        │
        ├─ action.edit_cost()  ->  EditWeight for diagnostics
        │
        ▼
Error message: "recovered by deleting token (1 edit)"
```

### 12.2 ProductWeight composition for optimal recovery

The full dual-cost optimization composes TropicalWeight and EditWeight:

```rust
type RecoveryCost = ProductWeight<TropicalWeight, EditWeight>;

// When comparing two recoveries:
let recovery_a = RecoveryCost::new(
    TropicalWeight::new(1.0),  // skip 2 tokens
    EditWeight::new(2),
);
let recovery_b = RecoveryCost::new(
    TropicalWeight::new(1.5),  // substitute 1 token
    EditWeight::new(2),
);

// ProductWeight::plus selects component-wise min:
//   left:  min(1.0, 1.5) = 1.0
//   right: min(2, 2) = 2
// ProductWeight::Ord uses lexicographic: recovery_a wins (lower tropical)
assert!(recovery_a < recovery_b);
```

When tropical costs are equal, EditWeight breaks the tie:

```rust
let recovery_c = RecoveryCost::new(
    TropicalWeight::new(1.0),
    EditWeight::new(1),        // delete: 1 edit
);
let recovery_d = RecoveryCost::new(
    TropicalWeight::new(1.0),
    EditWeight::new(2),        // substitute: 2 edits
);
// Same tropical cost; lexicographic Ord prefers fewer edits
assert!(recovery_c < recovery_d);
```

### 12.3 Multi-step Viterbi recovery

The `viterbi_recovery()` function in `recovery.rs` builds a multi-step repair
lattice and runs Viterbi shortest-path to find the globally optimal repair
sequence.  Each edge in the lattice carries a tropical cost; the corresponding
EditWeight can be computed post-hoc by summing `edit_cost()` over the
chosen path's actions:

    total_edits = ⊗_{actions on path} action.edit_cost()
                = sum of individual edit costs (saturating)

This gives the language designer both a quality metric (tropical) and an
interpretability metric (edit count) for every recovery.

### 12.4 Future: full WFST recovery over ProductWeight

The current implementation selects recoveries by tropical cost and reports
edit cost as a secondary diagnostic.  A natural extension is to run Viterbi
directly over ProductWeight<TropicalWeight, EditWeight>, making the edit count
a first-class optimization criterion.  This would require:

1. Parameterizing `RecoveryWfst` over `W: Semiring` (currently hardcoded to
   TropicalWeight).
2. Constructing edge weights as `ProductWeight::new(tropical_cost, edit_cost)`
   during lattice construction.
3. Using `ProductWeight::Ord` (lexicographic) for the Viterbi priority queue.

The semiring machinery is already in place; only the plumbing needs updating.

---

## 13. Source Reference & See Also

**Source files**:
- `prattail/src/automata/semiring.rs`, lines 369--490 (EditWeight definition)
- `prattail/src/recovery.rs`, line 153 (RepairAction::edit_cost())

**Cross-references**:
- [ProductWeight theory](./product-weight.md) -- composing EditWeight with
  TropicalWeight for dual-cost optimization
- [BooleanWeight theory](./boolean-weight.md) -- the simplest semiring
  (reachability only)
- [TropicalWeight theory](./tropical-weight.md) -- the primary semiring for
  dispatch priority and Viterbi shortest-path
- [Semirings overview](../semirings.md) --
  comprehensive survey of all semirings in PraTTaIL
- [Error recovery design](../../../design/wfst/semirings/edit-weight.md) --
  design document for recovery integration
- [liblevenshtein](https://github.com/F1R3FLY-io/liblevenshtein-rust) --
  character-level edit-distance automata for token spelling correction

**Tests**: `prattail/src/automata/semiring.rs`, lines 1067--1142
  - `test_edit_semiring_laws` -- zero/one identity, zero annihilation, commutativity
  - `test_edit_plus_is_min` -- ⊕ = min verification
  - `test_edit_times_is_add` -- ⊗ = + verification
  - `test_edit_idempotent` -- ⊕ idempotency
  - `test_edit_operation_costs` -- skip/delete/insert/substitute cost values
  - `test_edit_infinity` -- INFINITY constant = zero element
  - `test_edit_saturating` -- overflow protection via saturating_add
  - `test_edit_ordering` -- natural u32 ordering for Viterbi
