# BooleanWeight: Reachability Semiring

> **Source**: `prattail/src/automata/semiring.rs`, lines 287--363
> **Carrier**: `BooleanWeight(pub bool)` -- a single bit of information

---

## 1. Intuition & Motivation

Every grammar rule exists for a reason, but not every rule is necessarily
reachable during parsing.  A rule may be shadowed by a higher-priority
alternative, rendered unreachable by the FIRST-set topology, or simply dead
code left over from a grammar refactor.  Detecting such rules at compile time
saves the language designer from silent, hard-to-diagnose bugs.

The BooleanWeight semiring is the **cheapest possible reachability analysis**.
It stores exactly one bit per state -- "can this fire?" -- and propagates that
bit through the WFST using logical OR (for parallel alternatives) and logical
AND (for sequential composition).  No cost accumulation, no counting, no
floating-point arithmetic.  Just reachability.

In PraTTaIL's pipeline, BooleanWeight is used exclusively for **dead-rule
detection**: after the prediction WFST is constructed, the pipeline iterates
over every non-infix, non-variable, non-literal rule, queries whether any
token in the rule's FIRST set dispatches to it, and emits a compile-time
warning if the answer is `false` for all tokens.

---

## 2. Formal Definition

The Boolean semiring is the algebraic structure:

    B = ({false, true}, ∨, ∧, false, true)

where:

| Component         | Symbol | Meaning                  |
|-------------------|--------|--------------------------|
| Carrier set       | K      | {false, true}            |
| Addition          | ⊕      | ∨ (logical OR)           |
| Multiplication    | ⊗      | ∧ (logical AND)          |
| Additive identity | 0      | false                    |
| Multiplicative id | 1      | true                     |

In WFST terms:

- **⊕ = ∨** combines parallel paths: if *any* alternative is reachable, the
  result is reachable.
- **⊗ = ∧** sequences path segments: a path is reachable only if *both* of
  its segments are reachable.
- **0 = false** is the "unreachable" weight -- the additive identity
  (false ∨ x = x).
- **1 = true** is the "reachable" weight -- the multiplicative identity
  (true ∧ x = x).

---

## 3. Semiring Axiom Verification

We verify all required semiring axioms exhaustively.  Since |K| = 2, every
quantified statement reduces to at most 4 or 8 concrete cases.

### 3.1 (K, ⊕, 0) is a commutative monoid

**Closure**: ∨ maps {false, true} x {false, true} into {false, true}.

**Associativity**: a ∨ (b ∨ c) = (a ∨ b) ∨ c

| a     | b     | c     | a ∨ (b ∨ c) | (a ∨ b) ∨ c | equal |
|-------|-------|-------|-------------|-------------|-------|
| false | false | false | false       | false       | yes   |
| false | false | true  | true        | true        | yes   |
| false | true  | false | true        | true        | yes   |
| false | true  | true  | true        | true        | yes   |
| true  | false | false | true        | true        | yes   |
| true  | false | true  | true        | true        | yes   |
| true  | true  | false | true        | true        | yes   |
| true  | true  | true  | true        | true        | yes   |

**Identity**: 0 ⊕ a = a ⊕ 0 = a

| a     | false ∨ a | a ∨ false | equal |
|-------|-----------|-----------|-------|
| false | false     | false     | yes   |
| true  | true      | true      | yes   |

**Commutativity**: a ⊕ b = b ⊕ a

| a     | b     | a ∨ b | b ∨ a | equal |
|-------|-------|-------|-------|-------|
| false | false | false | false | yes   |
| false | true  | true  | true  | yes   |
| true  | false | true  | true  | yes   |
| true  | true  | true  | true  | yes   |

### 3.2 (K, ⊗, 1) is a monoid

**Closure**: ∧ maps {false, true} x {false, true} into {false, true}.

**Associativity**: a ∧ (b ∧ c) = (a ∧ b) ∧ c

| a     | b     | c     | a ∧ (b ∧ c) | (a ∧ b) ∧ c | equal |
|-------|-------|-------|-------------|-------------|-------|
| false | false | false | false       | false       | yes   |
| false | false | true  | false       | false       | yes   |
| false | true  | false | false       | false       | yes   |
| false | true  | true  | false       | false       | yes   |
| true  | false | false | false       | false       | yes   |
| true  | false | true  | false       | false       | yes   |
| true  | true  | false | false       | false       | yes   |
| true  | true  | true  | true        | true        | yes   |

**Identity**: 1 ⊗ a = a ⊗ 1 = a

| a     | true ∧ a | a ∧ true | equal |
|-------|----------|----------|-------|
| false | false    | false    | yes   |
| true  | true     | true     | yes   |

### 3.3 Distributivity: ⊗ distributes over ⊕

**Left**: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c), i.e., a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)

| a     | b     | c     | a ∧ (b ∨ c) | (a ∧ b) ∨ (a ∧ c) | equal |
|-------|-------|-------|-------------|-------------------|-------|
| false | false | false | false       | false             | yes   |
| false | false | true  | false       | false             | yes   |
| false | true  | false | false       | false             | yes   |
| false | true  | true  | false       | false             | yes   |
| true  | false | false | false       | false             | yes   |
| true  | false | true  | true        | true              | yes   |
| true  | true  | false | true        | true              | yes   |
| true  | true  | true  | true        | true              | yes   |

**Right**: (b ⊕ c) ⊗ a = (b ⊗ a) ⊕ (c ⊗ a) follows identically by
commutativity of ∧.

### 3.4 Zero annihilation: 0 ⊗ a = a ⊗ 0 = 0

| a     | false ∧ a | a ∧ false | both false |
|-------|-----------|-----------|------------|
| false | false     | false     | yes        |
| true  | false     | false     | yes        |

All semiring axioms hold.  QED.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity of ⊗

The multiplication ⊗ = ∧ is commutative, as verified by the full truth table:

| a     | b     | a ∧ b | b ∧ a | equal |
|-------|-------|-------|-------|-------|
| false | false | false | false | yes   |
| false | true  | false | false | yes   |
| true  | false | false | false | yes   |
| true  | true  | true  | true  | yes   |

Therefore B is a **commutative semiring**.

### 4.2 Idempotency of ⊕

Addition ⊕ = ∨ is idempotent:

    a ∨ a = a    for all a in {false, true}

Proof by exhaustion:
- false ∨ false = false = false.  Check.
- true  ∨ true  = true  = true.   Check.

Idempotency means that combining a path with itself yields the same
reachability.  This is semantically correct: knowing a state is reachable
twice is no different from knowing it is reachable once.

### 4.3 Smallest non-trivial semiring

The Boolean semiring has |K| = 2.  The only smaller semiring is the trivial
semiring {0} where 0 = 1 (which forces all elements to collapse).  Since
BooleanWeight distinguishes false from true, it is the smallest non-trivial
semiring, making it the cheapest carrier for reachability analysis.

### 4.4 Boolean ring structure

Observe that ⊗ also distributes over a derived "subtraction" operation
(XOR / symmetric difference), making ({false, true}, XOR, ∧, false, true)
a Boolean ring (in fact, the field GF(2)).  However, the semiring structure
({false, true}, ∨, ∧, false, true) is the one used for WFST reachability, not
the ring structure.

---

## 5. Reachability Semantics

Given a WFST W = (Q, Sigma, Delta, q_0, F, w) and a projection
pi: W -> B that maps every non-zero weight to `true` and zero to `false`,
the resulting Boolean WFST answers the question:

    "Does there exist at least one accepting path from q_0 to some q_f in F
     that reads this input sequence?"

### 5.1 Forward pass (reachability from initial state)

Compute forward[q] = ⊕_{all paths q_0 -> q} ⊗_{edges on path} w(e)

Under the Boolean semiring this becomes:

    forward[q_0] = true
    forward[q]   = ∨_{(p, a, q, w) in Delta} (forward[p] ∧ w)

A state q is **live** (forward-reachable) iff forward[q] = true.

### 5.2 Backward pass (reachability to final states)

Compute backward[q] = ⊕_{all paths q -> q_f in F} ⊗_{edges on path} w(e)

Under the Boolean semiring:

    backward[q_f] = true    for q_f in F
    backward[q]   = ∨_{(q, a, p, w) in Delta} (w ∧ backward[p])

A state q is **co-reachable** iff backward[q] = true.

### 5.3 Live states and dead states

A state is **useful** iff it is both forward-reachable and co-reachable:

    useful[q] = forward[q] ∧ backward[q]

States with useful[q] = false are dead and can be safely pruned.

### 5.4 Reachability diagram

```
  ┌──────────────────────────────────────────────────────────┐
  │  WFST States                                             │
  │                                                          │
  │    ┌──┐  true   ┌──┐  true   ┌──┐  true   ┌──────┐     │
  │ ──>│q0│───────>│q1│───────>│q2│───────>│ q3(F) │     │
  │    └──┘        └──┘        └──┘        └──────┘     │
  │     ⊤           ⊤           ⊤            ⊤          │
  │                                                          │
  │    ┌──┐  true   ┌──┐                                     │
  │    │q4│───────>│q5│   backward = ⊥ (no path to F)       │
  │    └──┘        └──┘                                      │
  │     ⊥           ⊥   <- dead states                      │
  └──────────────────────────────────────────────────────────┘
```

In this example, q4 and q5 are forward-reachable from q0 but not
co-reachable (no path leads from them to any final state q3).  The Boolean
backward pass marks them `false`, and the conjunction forward ∧ backward
yields `false` -- they are dead.

---

## 6. Dead-Rule Detection

PraTTaIL uses BooleanWeight semantics (though not the BooleanWeight struct
directly) in `pipeline.rs` to detect dead grammar rules at compile time.
Detection uses a three-tier architecture implemented in `detect_dead_rules()`
(`pipeline.rs:106–207`), surfaced through the unified lint layer as lint
W01 (`lint.rs:786–832`).

### 6.1 Three-Tier Algorithm

The algorithm classifies each rule into exactly one tier:

```
for each rule R in grammar:

    // Tier 1: Literal rules
    if R.is_literal:
        dead if R.category has no native_type
        continue

    // Tier 2: Same-category infix/var rules
    if (R.is_infix and not R.is_cross_category) or R.is_var:
        dead if R.category ∉ reachable_categories
        continue
        where reachable_categories = μX. {C | FIRST(C) ≠ ∅}
                                       ∪ {C | ∃ cast/cross-cat rule r:
                                              r.source ∈ X ∧ r.target = C}

    // Tier 3: Prefix/cast/cross-category rules (implicit Boolean projection)
    let wfst = prediction_wfst[R.category]
    reachable = ∨_{T ∈ FIRST(R.category)} [wfst.predict(T) routes to R]
    if not reachable:
        warn WfstUnreachable
```

Tier 3 is the Boolean reachability query from sections 4–5: the predicate
`∨_{T ∈ FIRST(C)} [wfst.predict(T) routes to R]` is equivalent to
projecting each WFST transition weight onto BooleanWeight via
`w → BooleanWeight(w ≠ zero)` and computing `plus` (disjunction) across
all transitions.

### 6.2 Dead rules detected in practice

**Calculator language** (8 dead rules, all Tier 3):

| Rule | Category | Reason |
|------|----------|--------|
| FloatToStr | Str | Cast shadowed by higher-priority alternatives |
| FloatToBool | Bool | Cast shadowed by higher-priority alternatives |
| StrToBool | Bool | Cast shadowed by higher-priority alternatives |
| IntId | Int | Identity rule shadowed by direct parse |
| FloatId | Float | Identity rule shadowed by direct parse |
| BoolId | Bool | Identity rule shadowed by direct parse |
| StrId | Str | Identity rule shadowed by direct parse |
| POutput | Proc | Output rule unreachable via prefix dispatch |

**RhoCalc language** (36 dead rules, all Tier 3):

The RhoCalc grammar detects 36 dead rules, primarily cross-category
comparison operators and cast rules where higher-priority direct
alternatives shadow the cross-category dispatch path.

### 6.3 Lint layer integration

Dead-rule warnings are no longer emitted via inline `eprintln!` calls.
Instead, `detect_dead_rules()` returns `Vec<DeadRuleWarning>` (three
variants: `LiteralNoNativeType`, `UnreachableCategory`, `WfstUnreachable`),
which `lint_w01_dead_rule()` wraps into `LintDiagnostic` entries with
variant-specific hints.  The unified `run_lints()` entry point in
`lint.rs:136–176` invokes all 23 lints including W01.

See [../../../design/wfst/dead-rule-detection.md](../../../design/wfst/dead-rule-detection.md)
for the full design document.

---

## 7. Relationship to Counting

The Boolean semiring is the **quotient** of the counting semiring under the
equivalence relation that collapses all positive integers to `true`:

    pi: N -> {false, true}
    pi(n) = (n > 0)

This projection is a semiring homomorphism:

    pi(a + b) = (a + b > 0) = (a > 0) ∨ (b > 0) = pi(a) ∨ pi(b)
    pi(a * b) = (a * b > 0) = (a > 0) ∧ (b > 0) = pi(a) ∧ pi(b)
    pi(0) = false
    pi(1) = true

Proof of the ∨ case: a + b > 0 iff a > 0 or b > 0 (since a, b >= 0).
Proof of the ∧ case: a * b > 0 iff a > 0 and b > 0 (since a, b >= 0).

Conversely, CountingWeight generalizes BooleanWeight: if you only need
"is it reachable?" you project counting down to boolean.  If you need
"*how many* paths are reachable?" you use counting directly.

---

## 8. Pseudocode: Forward-Backward Reachability

```
BOOLEAN-FORWARD(WFST W = (Q, Sigma, Delta, q0, F)):
    forward : Q -> {false, true}
    for each q in Q:
        forward[q] <- false
    forward[q0] <- true

    // Topological or BFS order over states
    worklist <- {q0}
    while worklist is not empty:
        p <- worklist.dequeue()
        for each (p, a, q, w) in Delta:
            new_val <- forward[q] ∨ (forward[p] ∧ w)
            if new_val != forward[q]:
                forward[q] <- new_val
                worklist.enqueue(q)
    return forward

BOOLEAN-BACKWARD(WFST W = (Q, Sigma, Delta, q0, F)):
    backward : Q -> {false, true}
    for each q in Q:
        backward[q] <- false
    for each q_f in F:
        backward[q_f] <- true

    // Reverse topological or BFS order
    worklist <- F
    while worklist is not empty:
        q <- worklist.dequeue()
        for each (p, a, q, w) in Delta:   // edges INTO q
            new_val <- backward[p] ∨ (w ∧ backward[q])
            if new_val != backward[p]:
                backward[p] <- new_val
                worklist.enqueue(p)
    return backward

DEAD-STATES(W):
    fwd <- BOOLEAN-FORWARD(W)
    bwd <- BOOLEAN-BACKWARD(W)
    dead <- {}
    for each q in Q:
        if not (fwd[q] ∧ bwd[q]):
            dead <- dead ∪ {q}
    return dead
```

Convergence is guaranteed because:
1. forward/backward values can only transition from false to true (monotone).
2. Each state enters the worklist at most once (after its value flips to true).
3. Therefore the algorithm terminates in O(|Q| + |Delta|) time.

---

## 9. Comparison Table

| Property                  | BooleanWeight      | CountingWeight       | TropicalWeight         |
|---------------------------|--------------------|----------------------|------------------------|
| **Carrier**               | {false, true}      | N (natural numbers)  | R+ union {+infinity}   |
| **⊕ (plus)**              | ∨ (OR)             | + (addition)         | min                    |
| **⊗ (times)**             | ∧ (AND)            | x (multiplication)   | + (addition)           |
| **0 (zero)**              | false              | 0                    | +infinity              |
| **1 (one)**               | true               | 1                    | 0.0                    |
| **Commutative**           | Yes                | Yes                  | Yes                    |
| **Idempotent (⊕)**        | Yes                | No (3+3=6 != 3)     | Yes (min(a,a) = a)    |
| **Size**                  | 2 elements         | Countably infinite   | Uncountably infinite   |
| **Semantics**             | Reachability       | Path counting        | Shortest path / cost   |
| **PraTTaIL use**          | Dead-rule detection| Ambiguity counting   | Priority dispatch      |
| **Rust Display**          | ⊤ / ⊥              | integer              | float / inf            |

---

## 10. Rust Implementation

The complete implementation from `prattail/src/automata/semiring.rs`:

```rust
/// Boolean semiring `({false, true}, ∨, ∧, false, true)`.
///
/// Tests reachability / language emptiness.
///
/// - `plus = ∨` (disjunction): any reachable path makes the state reachable
/// - `times = ∧` (conjunction): both segments must be reachable
/// - `zero = false`: unreachable (identity for ∨)
/// - `one = true`: reachable (identity for ∧)
///
/// **Application**: Dead-rule detection at codegen time. For each grammar rule,
/// project the prediction WFST onto the boolean semiring. Rules where
/// `predict(token).weight == BooleanWeight(false)` for all tokens are
/// unreachable and can be flagged with a compile-time warning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BooleanWeight(pub bool);
```

**Constructor and accessor**:

```rust
impl BooleanWeight {
    /// Create a boolean weight.
    #[inline]
    pub const fn new(reachable: bool) -> Self {
        BooleanWeight(reachable)
    }

    /// Whether this weight represents a reachable state.
    #[inline]
    pub const fn is_reachable(self) -> bool {
        self.0
    }
}
```

**Semiring trait implementation**:

```rust
impl Semiring for BooleanWeight {
    #[inline]
    fn zero() -> Self { BooleanWeight(false) }     // unreachable

    #[inline]
    fn one() -> Self { BooleanWeight(true) }        // reachable

    #[inline]
    fn plus(&self, other: &Self) -> Self {           // ∨: any path suffices
        BooleanWeight(self.0 || other.0)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {          // ∧: both segments needed
        BooleanWeight(self.0 && other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool { !self.0 }

    #[inline]
    fn is_one(&self) -> bool { self.0 }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0  // exact comparison (no floating point)
    }
}
```

**Display**: renders as unicode logical constants for clarity in diagnostics:

```rust
impl fmt::Display for BooleanWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", if self.0 { "⊤" } else { "⊥" })
    }
}
```

**Default**: returns `one()` (= true), which is consistent with the convention
that the default weight is the multiplicative identity -- a "zero-cost" or
"fully reachable" starting point:

```rust
impl Default for BooleanWeight {
    fn default() -> Self { Self::one() }
}
```

**Derived traits**: `Debug`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`
are all auto-derived.  The ordering is the natural `bool` ordering where
`false < true`, which means unreachable states sort before reachable ones.

---

## 11. Integration into PraTTaIL

### 11.1 Dead-rule detection in the pipeline

The dead-rule detection logic lives in `pipeline.rs` within the
`generate_parser` state machine, immediately after prediction WFSTs are
constructed.  The relevant code (simplified):

```rust
// Dead-rule detection via boolean semiring projection.
for rule_info in &bundle.rule_infos {
    // Skip rules handled outside prefix dispatch prediction
    if rule_info.is_infix || rule_info.is_var || rule_info.is_literal
        || rule_info.is_cross_category || rule_info.is_cast
    {
        continue;
    }

    let wfst = match prediction_wfsts.get(&rule_info.category) {
        Some(w) => w,
        None => continue,
    };

    // Boolean reachability: OR over all tokens in FIRST set
    let reachable = first_sets
        .get(&rule_info.category)
        .map_or(false, |fs| {
            fs.tokens.iter().any(|tok| {
                wfst.predict(tok)
                    .iter()
                    .any(|a| a.action.rule_label() == rule_info.label)
            })
        });

    if !reachable {
        eprintln!(
            "warning: rule {} in category {} is unreachable (dead code) -- \
             no token in FIRST({}) dispatches to it via prediction WFST",
            rule_info.label, rule_info.category, rule_info.category,
        );
    }
}
```

### 11.2 Why not use BooleanWeight directly?

The pipeline's dead-rule check operates at the *rule* level rather than the
*state* level.  It asks "does any FIRST-set token route to this rule?" rather
than "is this WFST state reachable?"  The `any()` iterator combinator is
semantically equivalent to Boolean ⊕ (disjunction), and the label equality
check is a predicate filter.  Using the `BooleanWeight` struct would add no
benefit here since the query is already naturally expressed as a boolean
expression.

However, the *concept* is purely Boolean semiring reachability: the pipeline
is computing the image of the prediction WFST under the projection
pi: TropicalWeight -> BooleanWeight and checking whether the image at each
rule is `true` or `false`.

### 11.3 Future applications

- **Language emptiness testing**: project an entire grammar WFST onto Boolean
  to determine if the language accepts any string at all.
- **Trim operation**: use forward-backward Boolean reachability (Section 5) to
  remove dead states from the WFST before codegen, reducing generated code.
- **Feature-flag pruning**: when grammar rules are conditionally enabled,
  Boolean reachability can verify that disabling a feature does not create
  dead rules in the remaining grammar.

---

## 12. Source Reference & See Also

**Source file**: `prattail/src/automata/semiring.rs`, lines 287--363

**Cross-references**:
- [CountingWeight theory](./counting-weight.md) -- BooleanWeight is the
  quotient of CountingWeight under n > 0 (Section 7)
- [TropicalWeight theory](./tropical-weight.md) -- the primary semiring used
  for dispatch priority
- [Semirings overview](../semirings.md) --
  comprehensive survey of all semirings in PraTTaIL
- [Dead-rule detection design](../../../design/wfst/semirings/boolean-weight.md) --
  design document for the pipeline integration

**Pipeline integration**: `prattail/src/pipeline.rs`, lines 552--589

**Tests**: `prattail/src/automata/semiring.rs`, lines 1002--1061
  - `test_boolean_semiring_laws` -- zero/one identity, zero annihilation
  - `test_boolean_plus_is_or` -- exhaustive ∨ truth table
  - `test_boolean_times_is_and` -- exhaustive ∧ truth table
  - `test_boolean_idempotent` -- ⊕ idempotency
  - `test_boolean_reachability` -- `is_reachable()` accessor
