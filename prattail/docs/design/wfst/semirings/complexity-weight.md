# ComplexityWeight -- Design & Pipeline Integration

**Date:** 2026-03-01

The bottleneck semiring `(N U {inf}, min, max, inf, 0)` measures parsing
complexity along dispatch paths. It answers: "What is the hardest dispatch
decision on this path?" Lower values indicate simpler, more deterministic
paths. The bottleneck property (`times = max`) ensures that path complexity
is dominated by its most complex segment, not accumulated across segments.

---

## Table of Contents

1. [Role in Pipeline](#1-role-in-pipeline)
2. [Design Decision: u32 Representation](#2-design-decision-u32-representation)
3. [Design Decision: Named Constructors](#3-design-decision-named-constructors)
4. [Design Decision: Natural Ordering](#4-design-decision-natural-ordering)
5. [Display Format](#5-display-format)
6. [Pipeline Integration: PredictionWfst Construction](#6-pipeline-integration-predictionwfst-construction)
7. [Lookahead Budget Allocation](#7-lookahead-budget-allocation)
8. [ProductWeight Composition](#8-productweight-composition)
9. [Idempotency and Viterbi Compatibility](#9-idempotency-and-viterbi-compatibility)
10. [Test Coverage](#10-test-coverage)
11. [Source Reference & See Also](#11-source-reference--see-also)

---

## 1. Role in Pipeline

ComplexityWeight serves as the quantitative bridge between the D1
cost-benefit framework (`cost_benefit.rs`) and the B1 multi-token
lookahead optimization. It answers the gating question: "Does this dispatch
point benefit from extended lookahead, or is single-token dispatch
sufficient?"

| Function                           | Location                                          | Description                                                             |
|------------------------------------|---------------------------------------------------|-------------------------------------------------------------------------|
| **Dispatch complexity annotation** | `semiring.rs:781-888`                             | Assigns complexity levels to WFST transitions based on ambiguity degree |
| **Lookahead budget gating**        | D1 framework (`cost_benefit.rs`)                  | ComplexityWeight > threshold triggers B1 multi-token lookahead          |
| **Bottleneck identification**      | Via `times = max`                                 | Path complexity = worst segment, identifying dispatch bottlenecks       |
| **Product composition**            | `ProductWeight<TropicalWeight, ComplexityWeight>` | Joint optimization: best priority AND least-complex path                |

ComplexityWeight is a **codegen-time analysis type**. It is not embedded in
generated parser code or consulted at runtime. Its purpose is to inform
pipeline decisions about where to invest compile-time analysis effort.

---

## 2. Design Decision: u32 Representation

ComplexityWeight wraps a bare `u32` (`semiring.rs:781`):

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ComplexityWeight(u32);
```

**Rationale**:

- **Discrete levels**: Parsing complexity is inherently categorical --
  deterministic (0), single lookahead (1), multi-token lookahead (2+),
  or infinite (u32::MAX). There is no meaningful concept of "fractional
  lookahead depth." Integer representation enforces this at the type level.
- **Copy semantics**: `u32` is `Copy` with a 4-byte footprint, enabling
  zero-allocation semiring arithmetic. No heap allocation, no reference
  counting, no lifetime parameters.
- **Exact comparison**: Integer equality and ordering are exact. Unlike
  TropicalWeight's `f64`, there are no NaN hazards, no epsilon thresholds,
  and no need for `total_cmp` workarounds.
- **u32::MAX as infinity**: The sentinel `u32::MAX` (~4.3 billion) is
  well beyond any realistic lookahead depth, providing a natural encoding
  for "infinite complexity / unreachable" without `Option` wrapping.

**Why not u64**: Unlike CountingWeight (which uses `u64` due to
multiplicative growth from `times = multiplication`), ComplexityWeight's
`times = max` never produces values larger than its inputs. The maximum
possible value is bounded by the largest constructor argument, making `u32`
more than sufficient. The 4-byte saving is irrelevant at codegen time but
maintains consistency with EditWeight's `u32` representation.

---

## 3. Design Decision: Named Constructors

ComplexityWeight provides four named constructors that encode the semantic
complexity levels (`semiring.rs:796-818`):

```rust
/// Complexity for a deterministic (unambiguous) dispatch point.
pub const fn deterministic() -> Self { ComplexityWeight(0) }

/// Complexity for a dispatch point requiring single-token lookahead.
pub const fn single_lookahead() -> Self { ComplexityWeight(1) }

/// Complexity for a dispatch point requiring multi-token lookahead.
pub const fn multi_lookahead(depth: u32) -> Self { ComplexityWeight(depth) }

/// Infinite complexity (unreachable path).
pub const fn infinite() -> Self { ComplexityWeight(u32::MAX) }
```

**Rationale**:

Named constructors serve as **self-documenting API**. Rather than scattering
magic constants (`ComplexityWeight::new(0)`, `ComplexityWeight::new(1)`)
throughout pipeline code, the intent is explicit:

| Constructor          | Value    | Dispatch Behavior                                                        |
|----------------------|----------|--------------------------------------------------------------------------|
| `deterministic()`    | 0        | Unique token dispatches to exactly one rule. No ambiguity.               |
| `single_lookahead()` | 1        | Token is shared by 2+ rules, but the next token resolves the ambiguity.  |
| `multi_lookahead(n)` | n        | Requires examining n tokens ahead to disambiguate.                       |
| `infinite()`         | u32::MAX | No finite lookahead can resolve; requires backtracking or NFA spillover. |

The `multi_lookahead(n)` constructor takes an explicit depth parameter
because multi-token lookahead cost is proportional to the number of tokens
examined. A dispatch point requiring 2-token lookahead is cheaper to resolve
than one requiring 5-token lookahead.

All constructors are `const fn`, enabling use in `const` and `static`
contexts without runtime cost.

---

## 4. Design Decision: Natural Ordering

`Ord` uses the natural `u32` ordering (`semiring.rs:867-872`):

```rust
/// Natural ordering: lower complexity = lower (better).
impl Ord for ComplexityWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}
```

**Rationale**:

- Lower complexity is "better" (simpler, faster dispatch), which aligns
  with the convention that lower weight = higher priority across all
  PraTTaIL semirings (TropicalWeight, EditWeight).
- The ordering is:
  ```
  deterministic(0) < single_lookahead(1) < multi_lookahead(n) < infinite(u32::MAX)
  ```
  This means `plus = min` selects the least-complex alternative, and
  Viterbi shortest-path naturally prefers simpler dispatch paths.
- Unlike CountingWeight (where `zero = 0` is the smallest, causing Viterbi
  incompatibility), ComplexityWeight's `zero = u32::MAX` is the **largest**
  value under natural ordering. This makes ComplexityWeight directly
  compatible with `viterbi_generic()` -- no ProductWeight workaround
  needed (see section 9).

---

## 5. Display Format

Display formats finite values as plain integers and `u32::MAX` as the
infinity symbol (`semiring.rs:874-882`):

```rust
impl fmt::Display for ComplexityWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == u32::MAX {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}
```

Examples:

| Value                                  | Display |
|----------------------------------------|---------|
| `ComplexityWeight::deterministic()`    | `0`     |
| `ComplexityWeight::single_lookahead()` | `1`     |
| `ComplexityWeight::multi_lookahead(3)` | `3`     |
| `ComplexityWeight::infinite()`         | `∞`     |

This format is consistent with EditWeight's display (integer for finite,
`∞` for the zero element) and enables readable diagnostic output in
the D1 cost-benefit framework's `eprintln` messages.

---

## 6. Pipeline Integration: PredictionWfst Construction

ComplexityWeight is assigned to WFST transitions during
`build_prediction_wfsts()` based on the degree of dispatch ambiguity at
each (category, token) pair. The assignment algorithm:

```
for each (category, token) in dispatch table:
    actions = prediction_wfst.predict(token)

    complexity = match actions.len():
        0 => ComplexityWeight::infinite()      // unreachable token
        1 => ComplexityWeight::deterministic()  // unique dispatch
        n => ComplexityWeight::single_lookahead()  // ambiguous (default)
             // upgraded to multi_lookahead(k) by B1 analysis
```

### Ambiguity-driven assignment

The key insight is that ComplexityWeight directly mirrors the
`predict().len()` ambiguity count already computed by the WFST:

| `predict().len()` | ComplexityWeight               | Interpretation                              |
|-------------------|--------------------------------|---------------------------------------------|
| 0                 | `infinite()`                   | Dead token -- no rule handles it            |
| 1                 | `deterministic()`              | Single dispatch target, no lookahead needed |
| 2+                | `single_lookahead()` (initial) | Ambiguous -- may need extended lookahead    |

The initial assignment is conservative: all ambiguous dispatch points
start at `single_lookahead()`. The B1 multi-token lookahead pass
(when activated by D1) refines these to `multi_lookahead(k)` based on
actual disambiguation depth analysis.

### Relationship to CountingWeight

ComplexityWeight and CountingWeight provide complementary views of
ambiguity:

| Property       | CountingWeight                      | ComplexityWeight             |
|----------------|-------------------------------------|------------------------------|
| **Question**   | "How many rules compete?"           | "How hard is it to resolve?" |
| **Domain**     | Derivation count (N)                | Lookahead depth (N)          |
| **times**      | Multiplication (path count product) | Max (bottleneck)             |
| **Grows with** | Grammar size (combinatorial)        | Ambiguity depth (bounded)    |

CountingWeight measures **breadth** of ambiguity (how many alternatives).
ComplexityWeight measures **depth** (how many tokens of lookahead to
resolve). A 10-way ambiguity resolvable by one token is complexity 1;
a 2-way ambiguity requiring 5 tokens of lookahead is complexity 5.

---

## 7. Lookahead Budget Allocation

The D1 cost-benefit framework (`cost_benefit.rs`) uses ComplexityWeight
to decide whether B1 (multi-token lookahead) is applicable and beneficial
for a given grammar.

### Budget allocation algorithm

```
1. For each ambiguous (category, token) pair:
      assign initial complexity = single_lookahead()

2. Aggregate per-category bottleneck:
      category_complexity = times over all transitions
                          = max(complexities in category)

3. Grammar-wide complexity:
      grammar_complexity = plus over all categories
                         = min(category complexities)
      // "What is the easiest category's bottleneck?"

4. Budget gate:
      if grammar_complexity > threshold:
          B1 multi-token lookahead is applicable
          budget = min(grammar_complexity.value(), MAX_LOOKAHEAD_DEPTH)
```

### Threshold semantics

The threshold determines when lookahead effort is worthwhile:

| Threshold                                  | Meaning                                                           |
|--------------------------------------------|-------------------------------------------------------------------|
| `ComplexityWeight::deterministic()` (0)    | All categories are fully deterministic -- B1 is inapplicable      |
| `ComplexityWeight::single_lookahead()` (1) | At least one category has single-token ambiguity -- B1 may help   |
| `ComplexityWeight::multi_lookahead(k)` (k) | At least one category needs k-token lookahead -- B1 is beneficial |

The D1 framework's B1 applicability predicate (`cost_benefit.rs:281`) uses
`ambiguous_fraction > 0.1 AND ambiguous_count < 10`. ComplexityWeight
refines this by providing per-dispatch-point granularity: only extend the
WFST at dispatch points where `complexity > deterministic()`, avoiding
wasted analysis on already-resolved points.

### Selective extension

The budget allocation enables **selective WFST extension**: rather than
extending all prediction WFSTs to k-token lookahead (O(k * |T| * |C|)
cost), only the specific (category, token) pairs with
`complexity >= single_lookahead()` are extended. This reduces the B1
pass cost from proportional to grammar size to proportional to ambiguity
count.

---

## 8. ProductWeight Composition

`ProductWeight<TropicalWeight, ComplexityWeight>` combines priority ranking
with complexity measurement in a single semiring:

```rust
type PriorityComplexity = ProductWeight<TropicalWeight, ComplexityWeight>;
```

### Semiring operations

The product semiring applies operations component-wise:

| Operation | Left (Tropical)        | Right (Complexity)  | Combined                                                   |
|-----------|------------------------|---------------------|------------------------------------------------------------|
| **plus**  | min (best priority)    | min (least complex) | `(min, min)` -- best weight AND least-complex alternative  |
| **times** | add (accumulated cost) | max (bottleneck)    | `(add, max)` -- accumulated cost AND bottleneck complexity |
| **zero**  | +inf (unreachable)     | u32::MAX (infinite) | `(+inf, ∞)` -- fully unreachable                           |
| **one**   | 0.0 (zero cost)        | 0 (deterministic)   | `(0.0, 0)` -- no cost, no complexity                       |

### Worked example

Consider two dispatch alternatives for a token in category `Expr`:

```rust
let direct = PriorityComplexity::new(
    TropicalWeight::new(0.5),              // moderate priority
    ComplexityWeight::deterministic(),      // unique dispatch
);
let cross_cat = PriorityComplexity::new(
    TropicalWeight::new(1.0),              // lower priority
    ComplexityWeight::single_lookahead(),   // requires lookahead
);
```

**plus** (select best alternative):
```
direct.plus(&cross_cat) = (min(0.5, 1.0), min(0, 1)) = (0.5, 0)
```
The direct path wins on both dimensions.

**times** (compose sequential segments):
```
direct.times(&cross_cat) = (0.5 + 1.0, max(0, 1)) = (1.5, 1)
```
The composed path has accumulated cost 1.5 and bottleneck complexity 1
(the cross-category segment is the hardest part).

### Lexicographic ordering

The product's lexicographic `Ord` (`semiring.rs:586-594`) ensures that
TropicalWeight dominates: among paths with equal tropical cost, the
one with lower complexity is preferred. This means:

1. First, select the path with the best parse quality (lowest tropical
   weight).
2. Among equally good paths, select the one requiring less lookahead
   effort (lowest complexity weight).

This ordering is correct for the intended use case: parse quality is
the primary objective, and complexity is a secondary tiebreaker
reflecting compilation cost rather than runtime cost.

---

## 9. Idempotency and Viterbi Compatibility

ComplexityWeight is **idempotent**: `plus(a, a) = min(a, a) = a`. This
is the same property that TropicalWeight and EditWeight satisfy but
CountingWeight does not.

### Viterbi compatibility

Unlike CountingWeight, ComplexityWeight is **directly compatible** with
`viterbi_generic()` (`lattice.rs:484-535`):

```
zero = u32::MAX  (largest under Ord)   -- "worst" / unvisited
one  = 0         (smallest under Ord)  -- "best" / start node
```

Viterbi initialization sets all distances to `zero` (u32::MAX), then
relaxes toward `one` (0). Since `zero > one` under natural ordering,
the algorithm correctly treats unvisited nodes as "worse than any real
path." No ProductWeight workaround is needed (contrast with
CountingWeight -- see `product-weight.md` section 4).

This means `ComplexityWeight` can be used as a standalone lattice weight
type for complexity-aware path extraction:

```rust
let lattice: TokenLattice<Token, Span, ComplexityWeight> = /* ... */;
let path = viterbi_generic(&lattice, final_node);
// path.cost = bottleneck complexity of the simplest-dispatch parse
```

### Bottleneck semiring properties

The bottleneck semiring `(N U {inf}, min, max, inf, 0)` has additional
structure beyond the standard semiring axioms:

- **Idempotent plus**: `min(a, a) = a` -- the semiring is selective
  (a k-closed semiring with k=0).
- **Idempotent times**: `max(a, a) = a` -- both operations are
  idempotent, making it a **doubly idempotent** semiring.
- **Distributivity**: `max(a, min(b, c)) = min(max(a, b), max(a, c))`
  -- verified by test `test_complexity_weight_distributivity`.
- **Commutative**: Both min and max are commutative.

---

## 10. Test Coverage

Eight tests in `semiring.rs:1615-1717` cover ComplexityWeight:

| Test                                           | Lines     | Validates                                                        |
|------------------------------------------------|-----------|------------------------------------------------------------------|
| `test_complexity_weight_semiring_laws`         | 1616-1640 | Zero identity, one identity, zero annihilation, commutativity    |
| `test_complexity_weight_min_max`               | 1643-1652 | `plus = min`, `times = max` with concrete values (3, 7)          |
| `test_complexity_weight_idempotent_plus`       | 1655-1659 | `min(5, 5) = 5` -- idempotency of plus                           |
| `test_complexity_weight_constructors`          | 1662-1670 | All 4 named constructors: values and identity properties         |
| `test_complexity_weight_distributivity`        | 1673-1681 | `max(a, min(b, c)) = min(max(a, b), max(a, c))`                  |
| `test_complexity_weight_ordering`              | 1685-1692 | `2 < 5 < inf` -- natural ordering with zero as largest           |
| `test_complexity_weight_display`               | 1695-1699 | `"3"`, `"∞"`, `"0"` -- integer and infinity formatting           |
| `test_complexity_weight_product_with_tropical` | 1702-1717 | `ProductWeight<TropicalWeight, ComplexityWeight>` plus and times |

### Axiom coverage

| Axiom                                     | Test                                     |
|-------------------------------------------|------------------------------------------|
| Additive identity: `zero + a = a`         | `test_complexity_weight_semiring_laws`   |
| Multiplicative identity: `one * a = a`    | `test_complexity_weight_semiring_laws`   |
| Zero annihilation: `zero * a = zero`      | `test_complexity_weight_semiring_laws`   |
| Commutativity of plus                     | `test_complexity_weight_semiring_laws`   |
| Commutativity of times                    | `test_complexity_weight_semiring_laws`   |
| Distributivity: `a * (b + c) = a*b + a*c` | `test_complexity_weight_distributivity`  |
| Idempotency of plus                       | `test_complexity_weight_idempotent_plus` |

---

## 11. Source Reference & See Also

- **Type definition**: `semiring.rs:759-888`
- **Named constructors**: `semiring.rs:796-818` (`deterministic`, `single_lookahead`, `multi_lookahead`, `infinite`)
- **Semiring impl**: `semiring.rs:821-858` (`plus = min`, `times = max`, `zero = u32::MAX`, `one = 0`)
- **Ord impl**: `semiring.rs:861-872` (natural `u32` ordering)
- **Display impl**: `semiring.rs:874-882` (integer or `∞`)
- **Tests**: `semiring.rs:1615-1717` (8 tests)
- **Product composition test**: `semiring.rs:1702-1717` (`ProductWeight<TropicalWeight, ComplexityWeight>`)
- **D1 cost-benefit framework**: `cost_benefit.rs` -- B1 applicability gating
- **Optimization pipeline**: `prattail/docs/architecture/wfst/optimization-pipeline.md` -- C2 entry, dependency graph
- **Theory**: `prattail/docs/theory/wfst/semirings.md`
- **Product semiring**: `product-weight.md` -- generic `ProductWeight` design
- **Tropical weight**: `tropical-weight.md` -- the primary left component in product composition
- **Counting weight**: `counting-weight.md` -- complementary ambiguity breadth metric
- **Cost-benefit framework**: `../cost-benefit-framework.md` -- D1 meta-optimization using ComplexityWeight for B1 gating
