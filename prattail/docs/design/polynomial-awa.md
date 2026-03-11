# Polynomial Alternating Automata -- Universal/Existential Branching with Semiring Weights

## Quick Start

Alternating automata extend nondeterministic automata by allowing both existential (disjunctive) and universal (conjunctive) branching. A transition from an existential state requires that *some* successor accepts; a transition from a universal state requires that *all* successors accept. This module generalizes the model to `WeightedAlternatingAutomaton<W>`, where existential states combine successor weights via `⊕` (semiring plus) and universal states via `⊗` (semiring times), following the polynomial transition function formulation of Kostolanyi & Misun (2018).

The module provides emptiness checking (parity-game reduction), bisimulation games for language equivalence, weighted emptiness via monotone fixpoint iteration, and word evaluation with memoized recursion. The type alias `AlternatingAutomaton = WeightedAlternatingAutomaton<BooleanWeight>` preserves backward compatibility.

**Motivating example**: In PraTTaIL, a type-checking specification like "every function application node has at least one valid argument type" maps naturally to alternating automata. The "every application" constraint is universal; "at least one valid type" is existential. Weights quantify type-checking costs.

```
CTL/mu-calculus formula
      │
      ▼
WeightedAlternatingAutomaton<W>
      │
      ├──→ check_emptiness()          (Boolean: parity game)
      ├──→ weighted_emptiness()       (general: monotone fixpoint)
      ├──→ evaluate_word()            (bottom-up word evaluation)
      └──→ bisimulation_game()        (language equivalence)
```

## Intuition

Think of an alternating automaton as a game between two players. Player Existential controls existential states and wins if she can find *some* path to acceptance. Player Universal controls universal states and wins only if *all* paths lead to acceptance. The automaton is non-empty iff Player Existential has a winning strategy from the initial state.

**Before this module**: PraTTaIL's branching analyses relied on ad-hoc tree-walking algorithms that could not express "all branches must satisfy" constraints alongside "some branch suffices" constraints in a unified framework.

**After this module**: Universal and existential branching are first-class concepts with formal semantics, parity acceptance, and quantitative weights. The bisimulation game provides language equivalence checking for grammar refactoring.

**Key insight**: The two-mode formulation (Q⊕ and Q⊗) maps the polynomial transition function semantics directly to semiring operations, recovering classical Boolean semantics for `BooleanWeight` while enabling quantitative analysis for `TropicalWeight`, `CountingWeight`, etc.

## Theoretical Foundations

**Definition 3.1 (Weighted Alternating Automaton).** A weighted alternating automaton over semiring `W` is `A = (Q⊕, Q⊗, Sigma, delta, q₀, Omega, tau)` where:
- `Q = Q⊕ ∪ Q⊗` partitions states into existential (sum) and universal (product)
- `Sigma` is the input alphabet
- `delta` is the weighted transition relation
- `q₀` is the initial state
- `Omega: Q -> N` is the priority function (parity acceptance)
- `tau: Q -> W` maps terminal states to acceptance weights

**Definition 3.2 (Polynomial Transition Function, Kostolanyi & Misun 2018).** A polynomial transition function is:

```
delta(q, a) = Sigma_i c_i * Pi_j x_{s_j}^{e_j}
```

where `c_i in W` is a coefficient and `x_{s_j}` is the state variable for state `s_j` with exponent `e_j`. In the two-mode formulation:
- Existential states: the sum `⊕` over monomials selects the best alternative
- Universal states: the product `⊗` within each monomial sequences all branches

**Theorem 3.1 (Two-Mode Equivalence, Kostolanyi & Misun 2018, Thm 5.17).** Every weighted alternating automaton with polynomial transitions is equivalent to a two-mode automaton where states are partitioned into Q⊕ and Q⊗, and transitions carry semiring weights.

**Definition 3.3 (Parity Acceptance).** A run is accepting iff the minimum priority visited infinitely often is even. For finite words, this reduces to: a state with even priority can accept as a leaf; a state with odd priority must continue through transitions to eventually reach even-priority dominance.

**Theorem 3.2 (Emptiness via Parity Games).** Emptiness of an alternating parity automaton reduces to solving a parity game. Player 0 (Existential) controls Q⊕; Player 1 (Universal) controls Q⊗. The automaton is non-empty iff Player 0 has a winning strategy from the initial state.

## Activation: ≥3 Non-Terminal Rules → M3

M3 (AWA) is activated by predicate dispatch when the grammar or its predicates
indicate universal branching requiring alternating acceptance.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features()
      │                                 │
      ▼                                 ▼
HighBranching(≥3)                ForallFinite / ForallInfinite
  ≥3 NT children                   Universal quantification
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M3_AWA bit set
```

**Grammar heuristic**: A rule with ≥3 `NonTerminal` or `Binder` children suggests
branching structure where properties must hold across all branches — the hallmark
of universal quantification that alternating automata capture directly.

**Predicate trigger**: `ForallFinite { .. }` (bounded universal) or
`ForallInfinite { .. }` (unbounded universal) quantifiers.

**Example grammar rule triggering M3**:
```
("Ternary", "Expr", [NT("Expr","cond"), Terminal("?"), NT("Expr","then"), Terminal(":"), NT("Expr","else")])
   ↑ 3 non-terminal children → M3 activated
```

**Theoretical justification**: If a property must hold "for all children" of a
branching construct (type-correctness, invariant preservation), alternating
acceptance captures this directly — existential states handle disjunctive choice
while universal states enforce conjunctive requirements across all branches.

## Design

### Core types

```rust
pub enum BranchingMode { Existential, Universal }

pub struct AlternatingState {
    pub id: usize,
    pub branching: BranchingMode,
    pub priority: u32,
    pub label: Option<String>,
}

pub struct WeightedAlternatingTransition<W: Semiring> {
    pub from: usize,
    pub label: Option<String>,
    pub successors: Vec<usize>,
    pub weight: W,
}

pub struct PolynomialTransition<W: Semiring> {
    pub from: usize,
    pub label: Option<String>,
    pub monomials: Vec<(W, Vec<(usize, u32)>)>,
}

pub struct WeightedAlternatingAutomaton<W: Semiring> {
    pub states: Vec<AlternatingState>,
    pub alphabet: HashSet<String>,
    pub transitions: Vec<WeightedAlternatingTransition<W>>,
    pub initial_state: Option<usize>,
    pub terminal_weights: HashMap<usize, W>,
}

pub type AlternatingAutomaton = WeightedAlternatingAutomaton<BooleanWeight>;
```

### State machine diagram

```
     ┌─────────┐         ┌─────────┐
     │ Q⊕ (∃)  │── a ──▶│ Q⊗ (∀)  │
     │ priority │         │ priority │
     │   = 0    │         │   = 1    │
     └─────────┘         └────┬────┘
                              │
                    ┌─────────┼─────────┐
                    ▼         ▼         ▼
              ┌────────┐┌────────┐┌────────┐
              │ succ₁  ││ succ₂  ││ succ₃  │
              │  (ALL   ││  must  ││ accept)│
              └────────┘└────────┘└────────┘
```

## Algorithms

### Boolean Emptiness Check

```
Input:  AlternatingAutomaton (BooleanWeight)
Output: true if L(automaton) = emptyset

1. Initialize accepting[s] for all leaf states:
   - No outgoing transitions + even priority => accepting
   - No outgoing transitions + odd priority => not accepting
2. Fixpoint iteration:
   For each non-leaf state s:
     If Existential: accepting[s] <- any transition has all successors accepting
     If Universal:   accepting[s] <- all transitions have all successors accepting
3. Return !accepting[initial_state]
```

**Complexity**: O(|Q|^2 * |delta|) worst case for fixpoint convergence.

### Weighted Emptiness (Monotone Fixpoint)

```
Input:  WeightedAlternatingAutomaton<W>
Output: W (total language weight from initial state)

1. Initialize weights[s] = terminal_weights[s] for leaf states
2. Fixpoint iteration (max |Q|^2 + 1 rounds):
   For each non-leaf state s:
     If Existential: w[s] = ⊕_t (t.weight ⊗ ⊗_{s' in t.successors} w[s'])
     If Universal:   w[s] = ⊗_t (t.weight ⊗ ⊗_{s' in t.successors} w[s'])
   Check convergence (approx_eq with epsilon 1e-10)
3. Return weights[initial_state]
```

### Word Evaluation (Memoized)

```
Input:  WeightedAlternatingAutomaton<W>, word[0..n]
Output: W (total acceptance weight)

eval(state, pos):
  if pos == n: return terminal_weights[state]
  matching = transitions from state with label == word[pos]
  if Existential: return ⊕_t (t.weight ⊗ ⊗_{s' in t.successors} eval(s', pos+1))
  if Universal:   return ⊗_t (t.weight ⊗ ⊗_{s' in t.successors} eval(s', pos+1))

Memo table: state x position -> W
```

**Complexity**: O(|Q| * |w| * |delta|) with memoization.

### Bisimulation Game

```
Input:  AlternatingAutomaton A, AlternatingAutomaton B
Output: true if A and B are bisimilar

1. Game positions: (state_in_A, state_in_B)
2. Attacker wins position (pA, pB) if:
   - A has a transition label that B cannot match, or vice versa
3. Backward propagation (attractor computation):
   - Attacker wins if she can force play to a winning position
4. Bisimilar iff initial position is NOT an Attacker win
```

**Complexity**: O(|Q_A|^2 * |Q_B|^2 * |delta|^2) worst case.

## Integration

- **Pipeline** (`pipeline.rs`): `analyze_from_bundle` builds alternating automata from grammar categories and reports non-bisimilar pairs.
- **Parity tree module** (`parity_tree.rs`): Extends alternation from words to trees; reuses `BranchingMode`.
- **LTL/CTL model checking**: CTL formulas naturally compile to alternating automata where universal path quantifiers become universal states.

## Diagnostics

No dedicated lint codes. The `AlternatingAnalysis` report includes:
- `non_bisimilar_pairs`: Category pairs whose rule structures are not bisimilar (potential refactoring candidates or intentional asymmetry).
- `state_count`: Size of the game automaton.

## Examples

### Example 1: Existential acceptance

```rust
let mut awa = AlternatingAutomaton::new();
let q0 = awa.add_state(BranchingMode::Existential, 0); // even priority
let q1 = awa.add_state(BranchingMode::Existential, 0);
awa.initial_state = Some(q0);
awa.add_transition(q0, Some("a".into()), vec![q1]);
// q1 is a leaf with even priority => accepting
assert!(!check_emptiness(&awa)); // L is non-empty: "a" is accepted
```

### Example 2: Universal requirement

```rust
let mut awa = AlternatingAutomaton::new();
let q0 = awa.add_state(BranchingMode::Universal, 0);
let q1 = awa.add_state(BranchingMode::Existential, 0); // accepting leaf
let q2 = awa.add_state(BranchingMode::Existential, 1); // rejecting leaf
awa.initial_state = Some(q0);
awa.add_transition(q0, Some("a".into()), vec![q1, q2]);
// Universal: both q1 AND q2 must accept. q2 has odd priority => rejecting.
assert!(check_emptiness(&awa)); // L is empty: universal branch fails
```

### Example 3: Weighted evaluation

```rust
use crate::automata::semiring::TropicalWeight;

let mut awa = WeightedAlternatingAutomaton::<TropicalWeight>::new();
let q0 = awa.add_state(BranchingMode::Existential, 0);
let q1 = awa.add_state(BranchingMode::Existential, 0);
awa.initial_state = Some(q0);
awa.set_terminal_weight(q1, TropicalWeight::new(0.0));
awa.add_weighted_transition(q0, Some("x".into()), vec![q1], TropicalWeight::new(5.0));

let w = evaluate_word(&awa, &["x"]);
// w = 5.0 + 0.0 = 5.0 (tropical times = addition)
```

## Advanced Topics

**Edge cases**: An automaton with no initial state has empty language. Invalid state IDs (>= num_states) are treated as rejecting.

**Interaction with other modules**: The `BranchingMode` enum is shared with the parity tree module (`parity_tree.rs`). The polynomial transition function formulation connects to the algebraic semiring infrastructure.

**Performance**: Boolean emptiness is polynomial (fixpoint on |Q| states). Weighted emptiness converges in at most |Q|^2 + 1 iterations for acyclic graphs; convergence for cyclic graphs depends on the semiring.

**Future extensions**: Integration with the CEGAR refinement loop for lazy emptiness checking on large alternating automata.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `check_emptiness(awa)` | `AlternatingAutomaton` | `bool` | O(\|Q\|^2 * \|delta\|) |
| `weighted_emptiness(awa)` | `WeightedAlternatingAutomaton<W>` | `W` | O(\|Q\|^3 * \|delta\|) |
| `evaluate_word(awa, word)` | automaton + `&[&str]` | `W` | O(\|Q\| * \|w\| * \|delta\|) |
| `bisimulation_game(a, b)` | two automata | `bool` | O(\|Q_A\|^2\|Q_B\|^2\|delta\|^2) |
| `analyze_from_bundle(...)` | grammar data | `AlternatingAnalysis` | O(\|categories\|^2) |

### Feature gate

Always available (core module).

### Citations

- Chandra, A.K., Kozen, D.C. & Stockmeyer, L.J. (1981). "Alternation." *Journal of the ACM*, 28(1), 114--133.
- Muller, D.E. & Schupp, P.E. (1987). "Alternating automata on infinite trees." *Theoretical Computer Science*, 54(2-3), 267--276.
- Kupferman, O. & Vardi, M.Y. (2001). "Weak alternating automata are not that weak." *ACM Trans. Comput. Logic*, 2(3), 408--429.
- Jurdzinski, M. (2000). "Small progress measures for solving parity games." *STACS 2000*, LNCS 1770, 290--301.
- Kostolanyi, P. & Misun, F. (2018). "Weighted alternating automata with polynomial transition functions." *DLT 2018*.
