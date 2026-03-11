# Multiset Automata -- Feature-Weighted Computation with Cardinality Constraints

## Quick Start

Multiset automata provide feature-weighted computation for process multiplicity and resource analysis. The module implements two featured multiset semirings from Mueller, Weiss & Lochau (2024): `MultisetWeight` (natural-number multiset with pointwise max/add) and `TropicalMultisetWeight` (tropical min/add over multisets). These are non-Copy semirings backed by `HashMap`, so they implement the `HeapSemiring` trait rather than the standard `Semiring` trait. The module provides `MultisetAutomaton<W>` with operations: `multiplicity_of()` (feature counting along paths), `satisfies_cardinality()` (bound checking), `feature_interaction()` (correlation detection), and `tropical_projection()` (domain projection).

**Motivating example**: In a PraTTaIL grammar, features correspond to grammar constructs (operator occurrences, nesting depth). A cardinality constraint `{operator: [1, 5]}` ensures that an operator appears between 1 and 5 times in any valid parse. The multiset automaton tracks feature multiplicities along paths and verifies these constraints.

```
Feature set F = {f1, f2, ..., fk}
      |
      v
MultisetAutomaton<W>
      |
      +---> multiplicity_of(feature, word)     (count feature along path)
      +---> satisfies_cardinality(constraint)   (check min/max bounds)
      +---> feature_interaction(f1, f2)         (detect correlated features)
      +---> tropical_projection()               (project to tropical domain)
      +---> analyze(constraints, word)           (full analysis report)
```

## Intuition

Think of a multiset automaton as a bakery production line with ingredient counters. Each station (state) on the line may add certain ingredients (features) to the recipe. As a batch moves through the line (following transitions), ingredient counters accumulate. A quality inspector (cardinality constraint) checks that each ingredient falls within required bounds -- not too little flour, not too much sugar. The `MultisetWeight` tracks *how many* of each ingredient are added; the `TropicalMultisetWeight` tracks the *minimum cost* of each ingredient.

**Before this module**: Feature multiplicity analysis was performed by ad-hoc counting passes that could not compose with the semiring-weighted automata pipeline.

**After this module**: Feature multiplicities are first-class semiring weights with proper algebraic structure. Cardinality constraints are checked systematically, and the tropical projection connects multiset analysis to shortest-path optimization.

**Key insight**: The `HeapSemiring` trait enables semirings backed by `HashMap` (non-Copy types), bridging the gap between the standard `Semiring` trait (which requires `Copy`) and the heap-allocated multiset domains.

## Theoretical Foundations

**Definition 9.1 (Featured Multiset Semiring, Mueller et al. 2024).** The multiset semiring over feature set `F` is `(N_0^F, ⊕, ⊗, 0-bar, 1-bar)` where:
- Elements are maps `F -> N_0` (feature multiplicities)
- `⊕ = pointwise max`: combining parallel paths selects the maximum multiplicity
- `⊗ = pointwise add`: sequencing paths accumulates multiplicities
- `0-bar = empty map`: all features have multiplicity 0 (identity for max)
- `1-bar = empty map`: all features have multiplicity 0 (identity for add)

**Definition 9.2 (Tropical Multiset Semiring).** The tropical variant is `(R_+inf^F, ⊕, ⊗, +inf-bar, 0-bar)` where:
- Elements are maps `F -> R ∪ {+inf}` (feature costs)
- `⊕ = pointwise min`: parallel paths select minimum cost
- `⊗ = pointwise add`: sequential paths accumulate costs
- `0-bar = all +inf`: unreachable (identity for min)
- `1-bar = all 0.0`: zero cost (identity for add)

**Definition 9.3 (HeapSemiring Trait).** A `HeapSemiring` is a semiring whose elements are heap-allocated (Clone but not Copy):

```rust
pub trait HeapSemiring: Clone + Debug + PartialEq + Send + Sync + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

**Definition 9.4 (Cardinality Constraint).** A constraint `(f, min, max)` specifies that feature `f`'s multiplicity along any accepting path must satisfy `min <= count(f) <= max`. Either bound may be `None` (unbounded).

**Definition 9.5 (Feature Interaction).** Features `f1` and `f2` interact if there exists a transition that contributes non-zero effects to both features simultaneously.

## Design

### Core types

```rust
pub struct MultisetWeight {
    pub features: HashMap<String, u64>,    // feature -> multiplicity
}

pub struct TropicalMultisetWeight {
    pub features: HashMap<String, f64>,    // feature -> tropical cost
    is_zero_flag: bool,                    // all features = +inf
}

pub struct MultisetState {
    pub id: usize,
    pub is_accepting: bool,
    pub label: Option<String>,
}

pub struct MultisetTransition<W: HeapSemiring> {
    pub from: usize,
    pub to: usize,
    pub label: Option<String>,
    pub weight: W,
    pub feature_effects: HashMap<String, u64>,
}

pub struct CardinalityConstraint {
    pub feature: String,
    pub min: Option<u64>,
    pub max: Option<u64>,
}

pub struct MultisetAutomaton<W: HeapSemiring> {
    pub states: Vec<MultisetState>,
    pub alphabet: HashSet<String>,
    pub transitions: Vec<MultisetTransition<W>>,
    pub initial_state: Option<usize>,
    pub accepting_states: HashSet<usize>,
    pub feature_set: Vec<String>,
}
```

### Semiring operation tables

```
MultisetWeight (N_0^F):
  ⊕ = pointwise max     ⊗ = pointwise add
  {a:2, b:1} ⊕ {a:1, b:3} = {a:2, b:3}
  {a:2, b:1} ⊗ {a:1, b:3} = {a:3, b:4}

TropicalMultisetWeight (R_+inf^F):
  ⊕ = pointwise min     ⊗ = pointwise add
  {a:2.0, b:1.0} ⊕ {a:1.0, b:3.0} = {a:1.0, b:1.0}
  {a:2.0, b:1.0} ⊗ {a:1.0, b:3.0} = {a:3.0, b:4.0}
```

## Algorithms

### Feature Multiplicity Counting

```
Input:  MultisetAutomaton<W>, feature name, word[0..n]
Output: u64 (maximum multiplicity along any accepting path)

1. BFS queue: (state, position, accumulated_features)
2. Precompute transition index: source_state -> transitions
3. While queue not empty:
   (state, pos, accum) = pop
   Process epsilon transitions from state (label = None):
     Update accum by adding feature_effects
   If pos == n and state is accepting:
     max_multiplicity = max(max_multiplicity, accum[feature])
     Continue
   Try labeled transitions matching word[pos]:
     Update accum, advance position, push successor
4. Return max_multiplicity
```

**Complexity**: O(|w| * |Q| * |delta| * |F|).

### Cardinality Constraint Checking

```
Input:  MultisetAutomaton<W>, CardinalityConstraint, word
Output: bool

1. count = multiplicity_of(constraint.feature, word)
2. Return constraint.min.map_or(true, |m| count >= m)
       && constraint.max.map_or(true, |m| count <= m)
```

### Feature Interaction Detection

```
Input:  MultisetAutomaton<W>, feature f1, feature f2
Output: bool

Return transitions.any(|t|
    t.feature_effects[f1] > 0 && t.feature_effects[f2] > 0
)
```

**Complexity**: O(|delta|).

### Tropical Projection

```
Input:  MultisetAutomaton<MultisetWeight>
Output: MultisetAutomaton<TropicalMultisetWeight>

For each transition:
  Map MultisetWeight to TropicalMultisetWeight:
    For each (feature, count) in weight.features:
      tropical.features[feature] = count as f64
```

## Integration

- **WFST module** (`wfst.rs`): The tropical projection connects multiset analysis to the WFST shortest-path pipeline.
- **Pipeline** (`pipeline.rs`): `MultisetAnalysisResult` reports feature interactions and unsatisfied cardinality constraints.
- **Semiring module**: `HeapSemiring` complements the standard `Semiring` trait for non-Copy weight domains.

## Diagnostics

No dedicated lint codes. The `MultisetAnalysisResult` report includes:
- `num_states`: Number of states
- `num_features`: Number of features in the feature set
- `feature_interactions`: Pairs of co-occurring features
- `unsatisfiable_constraints`: Constraints not satisfied by the analyzed word

## Examples

### Example 1: Feature multiplicity counting

```rust
let mut ma = MultisetAutomaton::<MultisetWeight>::new(
    vec!["ops".into(), "depth".into()],
);
let q0 = ma.add_state(false, Some("start".into()));
let q1 = ma.add_state(false, None);
let q2 = ma.add_state(true, Some("accept".into()));
ma.initial_state = Some(q0);

let mut effects = HashMap::new();
effects.insert("ops".into(), 1);
ma.add_transition(q0, q1, Some("op".into()),
    MultisetWeight::new().with_feature("ops", 1), effects.clone());

effects.clear();
effects.insert("ops".into(), 1);
ma.add_transition(q1, q2, Some("op".into()),
    MultisetWeight::new().with_feature("ops", 1), effects);

let count = ma.multiplicity_of("ops", &["op", "op"]);
assert_eq!(count, 2); // two "ops" features accumulated
```

### Example 2: Cardinality constraint checking

```rust
let constraint = CardinalityConstraint::new("ops", Some(1), Some(3));
assert!(ma.satisfies_cardinality(&constraint, &["op", "op"]));  // 2 in [1,3]

let strict = CardinalityConstraint::new("ops", Some(3), Some(5));
assert!(!ma.satisfies_cardinality(&strict, &["op", "op"]));  // 2 < 3
```

### Example 3: Tropical projection

```rust
let tropical_ma = ma.tropical_projection();
// MultisetWeight {ops: 1} -> TropicalMultisetWeight {ops: 1.0}
// Now supports min-plus analysis over features
```

## Advanced Topics

**Edge cases**: Both `MultisetWeight::zero()` and `MultisetWeight::one()` are the empty map. This is correct because the empty map is the identity for both pointwise max (⊕) and pointwise add (⊗). For `TropicalMultisetWeight`, the `is_zero_flag` distinguishes the additive identity (all +inf) from the multiplicative identity (all 0.0), since both have empty feature maps in the representation.

**Interaction with other modules**: The `HeapSemiring` trait enables future non-Copy semiring types beyond multisets (e.g., polynomial weights, matrix weights). The feature interaction analysis connects to the symbolic automata module's guard overlap detection.

**Performance**: Feature multiplicity counting via BFS is polynomial for fixed feature sets. The main cost is the HashMap cloning during BFS exploration. For grammars with small feature sets (< 20 features), this is negligible.

**Future extensions**: `HeapStarSemiring` for matrix-star closure over multiset weights, enabling cycle analysis in feature-weighted automata.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `multiplicity_of(feature, word)` | `&str, &[&str]` | `u64` | O(\|w\| * \|Q\| * \|delta\| * \|F\|) |
| `satisfies_cardinality(c, word)` | constraint + word | `bool` | O(\|w\| * \|Q\| * \|delta\|) |
| `feature_interaction(f1, f2)` | `&str, &str` | `bool` | O(\|delta\|) |
| `tropical_projection()` | `&self` | `MultisetAutomaton<TropicalMultisetWeight>` | O(\|delta\| * \|F\|) |
| `analyze(constraints, word)` | constraints + word | `MultisetAnalysisResult` | O(\|F\|^2 * \|delta\| + \|C\| * eval) |

### Feature gate

`multiset-automata` (depends on `wfst-log`).

### Citations

- Mueller, T., Weiss, B. & Lochau, M. (2024). "Mapping cardinality-based feature models to weighted automata over featured multiset semirings."
