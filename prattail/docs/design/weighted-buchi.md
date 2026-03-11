# Weighted Buchi Automata -- Omega-Regular Acceptance with Semiring Weights

## Quick Start

Buchi automata extend finite automata to infinite words. A run is accepting if it visits at least one accepting state infinitely often, making Buchi automata the standard formalism for specifying liveness and fairness properties. This module generalizes the classical (unweighted) model to `WeightedBuchiAutomaton<W>`, parameterized over any semiring `W`. The unweighted case is recovered via `BuchiAutomaton = WeightedBuchiAutomaton<BooleanWeight>`.

The key operations are: `construct_buchi` / `construct_weighted_buchi` for construction, `buchi_intersect` for product (3-counter construction), `check_emptiness` for SCC-based emptiness checking, and `total_accepting_weight` for quantitative analysis via `StarSemiring` and `matrix_star()`.

**Motivating example**: In PraTTaIL, LTL formulas expressing "every recursive category eventually terminates" are compiled to Buchi automata via `ltl_to_buchi()`, then intersected with the WPDS call-graph automaton. Emptiness of the product verifies the property; non-emptiness yields a counterexample trace.

```
LTL formula (ltl module)
      │
      ▼
ltl_to_buchi()
      │
      ▼
BuchiAutomaton  (= WeightedBuchiAutomaton<BooleanWeight>)
      │
      ├──→ buchi_intersect() (product with system model)
      │         │
      │         ▼
      │    check_emptiness() ──→ true/false
      │
      └──→ total_accepting_weight() (StarSemiring quantitative analysis)
```

## Intuition

Imagine a train that loops forever around a circular track with labeled stations. An unweighted Buchi automaton is like a ticket inspector who requires that the train pass through at least one "checkpoint" station infinitely often. A weighted Buchi automaton additionally assigns a cost to each segment of track; `total_accepting_weight` computes the aggregate cost of all possible infinite-loop journeys through checkpoints.

**Before this module**: Temporal properties of grammars were checked ad hoc, without a systematic automata-theoretic framework for infinite-behavior specifications.

**After this module**: LTL liveness/fairness properties are compiled to Buchi automata, intersected with system models, and checked via Tarjan SCC-based emptiness. Quantitative analysis (minimum-cost cycles, derivation counting) is available via `total_accepting_weight` with `TropicalWeight` or `CountingWeight`.

**Key insight**: The 3-counter product construction correctly handles Buchi acceptance for intersection, and the `matrix_star()` Kleene closure computes cycle weights for quantitative analysis.

## Theoretical Foundations

**Definition 2.1 (Weighted Nondeterministic Buchi Automaton).** A weighted NBA over semiring `(W, ⊕, ⊗, 0, 1)` is a tuple `A = (Q, Sigma, delta, Q₀, F)` where:
- `Q` is a finite set of states
- `Sigma` is the input alphabet (strings)
- `delta: Q x Sigma -> 2^(Q x W)` is the weighted transition relation
- `Q₀ ⊆ Q` are initial states
- `F ⊆ Q` are accepting states

A run `rho` on an infinite word `w = a₀ a₁ a₂ ...` is a sequence `q₀ q₁ q₂ ...` with `q₀ in Q₀` and `(qᵢ, aᵢ, qᵢ₊₁, wᵢ) in delta`. The run is accepting iff `inf(rho) ∩ F ≠ emptyset` (the run visits some accepting state infinitely often).

**Definition 2.2 (3-Counter Product Construction).** Given two weighted NBAs `A₁` and `A₂`, the product `A₁ x A₂` has states `Q₁ x Q₂ x {0, 1, 2}`. The phase counter tracks which automaton's accepting condition has been satisfied since the last reset:
- Phase 0: waiting for `A₁` to visit an accepting state
- Phase 1: `A₁` accepted, now waiting for `A₂`
- Phase 2: both accepted -- accepting state; reset to 0

Transition weights are combined via `W::times()`.

**Theorem 2.1 (Emptiness via SCC).** A Buchi automaton is non-empty iff there exists an SCC that is (1) reachable from an initial state, (2) contains an accepting state, and (3) has at least one edge (non-trivial or self-loop). Tarjan's algorithm computes SCCs in O(|Q| + |delta|).

**Theorem 2.2 (Total Accepting Weight via Matrix Star).** For a `StarSemiring W`, the total weight of all accepting cycles through an accepting SCC is computed by the diagonal entries of the matrix Kleene closure (`matrix_star`) of the intra-SCC adjacency matrix. The overall total is `⊕` over all accepting states in all accepting SCCs.

## Activation: Recursive Categories → M2

M2 (Büchi) is activated by predicate dispatch when the grammar or its predicates
indicate ω-regular (infinite-word) structure requiring liveness analysis.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features()
      │                                 │
      ▼                                 ▼
DirectRecursion(C)               ForallInfinite / ExistsInfinite
  C references itself              ω-quantification
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M2_BUCHI bit set
```

**Grammar heuristic**: A category C is recursive if C ∈ refs(C) — i.e., some rule
in category C has a `NonTerminal` or `Binder` referencing C itself. Recursive
categories can generate derivations of unbounded depth, whose corresponding
predicate language requires ω-regular analysis to verify liveness/fairness properties.

**Predicate trigger**: `ForallInfinite { .. }` or `ExistsInfinite { .. }` quantifiers
directly require Büchi acceptance for omega-regular property verification.

**Example grammar rule triggering M2**:
```
("ExprAdd", "Expr", [NonTerminal("Expr", "left"), Terminal("+"), NonTerminal("Expr", "right")])
   ↑ category "Expr" references itself → recursive → M2 activated
```

**Theoretical justification**: A recursive category C with C →* C generates strings
of unbounded length. By Büchi's theorem (1962), properties over such unbounded
derivations require ω-regular analysis — precisely what Büchi automata provide.

## Design

### Core types

```rust
pub struct BuchiState {
    pub id: usize,
    pub is_accepting: bool,
    pub label: Option<String>,
}

pub struct BuchiTransition {
    pub from: usize,
    pub to: usize,
    pub label: Option<String>,  // None = epsilon
}

pub struct WeightedBuchiAutomaton<W: Semiring> {
    pub states: Vec<BuchiState>,
    pub alphabet: HashSet<String>,
    pub transitions: HashMap<(usize, Option<String>), Vec<(usize, W)>>,
    pub initial_states: HashSet<usize>,
    pub accepting_states: HashSet<usize>,
}

pub type BuchiAutomaton = WeightedBuchiAutomaton<BooleanWeight>;
```

### Pipeline bridge

```rust
pub struct BuchiAnalysis {
    pub num_states: usize,
    pub num_accepting: usize,
    pub has_accepting_cycle: bool,
}
```

`from_wpds(wpds_analysis)` converts the WPDS call graph into a Buchi automaton where categories are states, call-graph edges are transitions, and root categories (zero fan-in) are both initial and accepting states.

## Algorithms

### Emptiness Check (Tarjan SCC)

```
Input:  WeightedBuchiAutomaton<W>
Output: true if L(buchi) = emptyset

1. BFS from initial states to find reachable states R
2. Build adjacency list restricted to R; track self-loops
3. Run Tarjan's SCC algorithm (iterative, explicit stack)
4. For each SCC:
   a. Check has_cycle: |SCC| > 1 or (|SCC| = 1 and self-loop)
   b. Check has_accepting: any state in SCC ∩ F
   c. If both: return false (non-empty)
5. Return true (empty)
```

**Complexity**: O(|Q| + |delta|) for BFS + Tarjan.

### Total Accepting Weight

```
Input:  WeightedBuchiAutomaton<W> where W: StarSemiring
Output: W (aggregate cycle weight)

1. BFS reachability from initial states
2. Tarjan SCC decomposition on reachable subgraph
3. For each accepting SCC (has cycle + has accepting state):
   a. Build intra-SCC adjacency matrix M[i][j] = ⊕ weights(i → j)
   b. Compute M* = matrix_star(M)  (generalized Floyd-Warshall)
   c. For each accepting state q in SCC:
      total <- total ⊕ M*[q_local][q_local]
4. Return total
```

**Complexity**: O(|Q| + |delta| + Sigma_SCC |SCC|^3)

### 3-Counter Intersection

```
Input:  A = WeightedBuchiAutomaton<W>, B = WeightedBuchiAutomaton<W>
Output: WeightedBuchiAutomaton<W> accepting L(A) ∩ L(B)

1. Product states: |Q_A| x |Q_B| x 3
2. Initial: (q_a, q_b, 0) for q_a in I_A, q_b in I_B
3. Accepting: states with phase = 2
4. For each transition pair (q1,a,q1',w_a) in A, (q2,a,q2',w_b) in B:
   For each phase p in {0,1,2}:
     next_p = match p {
       0 => if q1 in F_A then 1 else 0,
       1 => if q2 in F_B then 2 else 1,
       2 => 0,
     };
     Add transition (q1,q2,p) --a/(w_a⊗w_b)--> (q1',q2',next_p)
```

**Complexity**: O(|Q_A| * |Q_B| * |delta_A| * |delta_B|)

## Integration

- **LTL module** (`ltl.rs`): LTL formulas compile to Buchi automata for temporal verification.
- **WPDS module** (`wpds.rs`): `from_wpds()` converts the call graph to a Buchi automaton for liveness checking.
- **Pipeline** (`pipeline.rs`): `BuchiAnalysis` reports state counts and cycle properties.

## Diagnostics

No dedicated lint codes. The Buchi analysis feeds the pipeline's temporal property diagnostics:
- Non-empty product with a negated property automaton indicates a liveness violation.
- `has_accepting_cycle = false` in `BuchiAnalysis` confirms termination of recursive categories.

## Examples

### Example 1: Emptiness check

```rust
let buchi = construct_buchi(
    3,
    HashSet::from([1]),          // state 1 is accepting
    HashSet::from([0]),          // state 0 is initial
    vec![
        (0, Some("a".into()), 1),
        (1, Some("b".into()), 2),
        (2, Some("a".into()), 1), // cycle through accepting state
    ],
);
assert!(!check_emptiness(&buchi)); // Non-empty: cycle 1->2->1 visits F
```

### Example 2: Weighted analysis

```rust
use crate::automata::semiring::TropicalWeight;

let buchi = construct_weighted_buchi::<TropicalWeight>(
    2,
    HashSet::from([0]),
    HashSet::from([0]),
    vec![
        (0, Some("a".into()), 1, TropicalWeight::new(1.0)),
        (1, Some("b".into()), 0, TropicalWeight::new(2.0)),
    ],
);
let w = total_accepting_weight(&buchi);
// Cycle weight: 1.0 + 2.0 = 3.0 (tropical times = addition)
```

## Advanced Topics

**Edge cases**: An SCC with a single state and no self-loop is a trivial SCC and cannot produce an infinite accepting run. The emptiness check correctly excludes it.

**Interaction with other modules**: Buchi automata are the target of LTL compilation and the property specification formalism for WPDS model checking. The `buchi_intersect` function is used by the LTL module to compose property and system automata.

**Performance**: Tarjan's SCC is O(V+E). The bottleneck is `total_accepting_weight`, which is O(|SCC|^3) per accepting SCC due to `matrix_star`. For the small automata typical in grammar analysis (< 100 states), this is negligible.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `construct_buchi(n, acc, init, trans)` | sizes, sets, transitions | `BuchiAutomaton` | O(n + \|trans\|) |
| `construct_weighted_buchi(...)` | same + weights | `WeightedBuchiAutomaton<W>` | O(n + \|trans\|) |
| `buchi_intersect(a, b)` | two automata | product automaton | O(\|Q_A\|\|Q_B\|\|delta\|) |
| `check_emptiness(buchi)` | automaton | `bool` | O(\|Q\| + \|delta\|) |
| `total_accepting_weight(buchi)` | `StarSemiring` automaton | `W` | O(\|Q\| + \|delta\| + SCC^3) |
| `from_wpds(analysis)` | `WpdsAnalysis` | `BuchiAutomaton` | O(\|categories\| + \|edges\|) |

### Feature gate

Always available (core module).

### Citations

- Buchi, J.R. (1962). "On a decision method in restricted second order arithmetic." *Proc. Int. Congress on Logic, Method. and Phil. of Science*.
- Thomas, W. (1990). "Automata on infinite objects." *Handbook of Theoretical Computer Science*, Vol. B.
- Vardi, M.Y. & Wolper, P. (1994). "Reasoning about infinite computations." *Information and Computation*, 115(1), 1--37.
- Chatterjee, K., Doyen, L. & Henzinger, T.A. (2010). "Quantitative languages." *ACM Trans. Comput. Logic*, 11(4), 1--38.
