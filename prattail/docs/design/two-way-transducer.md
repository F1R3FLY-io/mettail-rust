# Weighted Two-Way Transducers -- Bidirectional Constraint Propagation

## Quick Start

Weighted Two-Way Transducers (W2T) generalize classical one-way transducers by allowing the input head to move both forward and backward. The module provides `WeightedTwoWayTransducer<W>`, parameterized over any semiring `W`, with operations: `transduce()` (BFS simulation with crossing sequence loop detection), `sum()` (disjoint union), `compose_one_way()` (composition with a one-way FST), `to_one_way()` (crossing sequence conversion), and `analyze_join_pattern()` (channel dependency analysis with deadlock detection).

The state set is partitioned into forward states `Q->` (head moves right) and backward states `Q<-` (head moves left). The input tape is enhanced with endmarkers: `|-- a_1 a_2 ... a_n --|`, where `|--` (left endmarker) and `--|` (right endmarker) allow boundary detection. Initial and final states must be forward states (Feng & Maletti, Definition 2.1).

**Motivating example**: In Rholang, cross-channel constraint propagation requires bidirectional scanning. A two-way transducer can read a channel's contents forward to collect constraints, then scan backward to apply those constraints to earlier positions. Join pattern analysis uses the constraint graph to detect deadlock cycles and optimize channel consumption order.

```
Channel dependencies
      |
      v
WeightedTwoWayTransducer<W>
      |
      +---> transduce(input)              (BFS simulation)
      +---> sum(m1, m2)                   (disjoint union)
      +---> compose_one_way(fst)          (output composition)
      +---> to_one_way()                  (crossing sequence conversion)
      +---> analyze()                     (structural analysis)
      +---> analyze_join_pattern(channels) (deadlock detection)
```

## Intuition

Think of a two-way transducer as a librarian scanning a bookshelf. A one-way librarian can only walk from left to right, reading titles. A two-way librarian can walk in both directions -- she might scan right to find a reference, then walk back left to verify a citation, then continue rightward. The endmarkers are the walls at each end of the shelf. Each scan produces output (notes) with a cost weight.

**Before this module**: Cross-channel constraints in Rholang were propagated in a single left-to-right pass, missing backward dependencies.

**After this module**: Bidirectional constraint propagation is formalized with crossing sequence semantics. Deadlock detection via Tarjan SCC on the channel dependency graph identifies circular dependencies. The `to_one_way()` conversion provides an equivalent one-way representation when the state space permits.

**Key insight**: The state partition `Q-> ∪ Q<-` determines head movement direction -- the direction is a property of the source state, not the transition. This clean separation enables the crossing sequence construction for converting two-way to one-way automata.

## Theoretical Foundations

**Definition 11.1 (Weighted Two-Way Transducer, Feng & Maletti 2022).** A W2T over semiring `W` is `M = (Q->, Q<-, A, B, T, I, F)` where:
- `Q-> ⊆ Q` are forward states (head moves right after transition)
- `Q<- ⊆ Q` are backward states (head moves left after transition)
- `A` is the input alphabet
- `B` is the output alphabet
- `T ⊆ Q x (A ∪ {|-, -|}) x B* x Q x W` is the weighted transition relation
- `I: Q-> -> W` is the initial weight function (forward states only)
- `F: Q-> -> W` is the final weight function (forward states only)

**Definition 11.2 (Enhanced Input Tape).** The input word `w = a_1 ... a_n` is enhanced to `|- a_1 a_2 ... a_n -|` with positions 0 (left endmarker) through n+1 (right endmarker). The transducer begins at position 0 in an initial state and accepts when the head moves past position n+1 in a final state.

**Definition 11.3 (Crossing Sequence).** A crossing sequence at boundary `i` is the sequence of states the head visits as it crosses boundary `i` during a run. The head "crosses boundary i from left to right" when it moves from position i to i+1, and "from right to left" when it moves from i+1 to i.

**Theorem 11.1 (Two-Way to One-Way, Shepherdson 1959, Feng & Maletti Section 3).** Every two-way transducer with `n` states can be converted to a one-way transducer. The one-way construction tracks crossing sequences, yielding at most `2^(O(n))` states. For small `n`, this is tractable.

**Theorem 11.2 (Closure under Sum, Feng & Maletti Theorem 4.1).** The class of weighted two-way transductions is closed under semiring sum (union): `[[sum(M_1, M_2)]] = [[M_1]] ⊕ [[M_2]]`. The construction takes the disjoint union of states and transitions.

**Theorem 11.3 (Composition with One-Way).** A W2T `M: A* -> B*` can be composed with a one-way FST `F: B* -> C*` via product construction: each state in the result is a pair `(w2t_state, fst_state)`, and W2T output symbols are threaded through the FST.

## Design

### Core types

```rust
pub enum HeadDirection {
    Forward,    // Q->: head moves right
    Backward,   // Q<-: head moves left
}

pub struct TwoWayState {
    pub id: usize,
    pub direction: HeadDirection,
    pub label: Option<String>,
}

pub enum TwoWayInput {
    Symbol(String),      // regular input symbol
    LeftEndmarker,       // |- (position 0)
    RightEndmarker,      // -| (position n+1)
}

pub struct TwoWayTransition<W: Semiring> {
    pub from: usize,
    pub to: usize,
    pub input: TwoWayInput,
    pub output: Vec<String>,
    pub weight: W,
}

pub struct WeightedTwoWayTransducer<W: Semiring> {
    pub states: Vec<TwoWayState>,
    pub transitions: Vec<TwoWayTransition<W>>,
    pub initial_weights: HashMap<usize, W>,
    pub final_weights: HashMap<usize, W>,
    pub input_alphabet: HashSet<String>,
    pub output_alphabet: HashSet<String>,
}
```

### Head movement diagram

```
  Position:  0    1    2    3    4    5
  Tape:     |-    a    b    c    a   -|

  Forward state (Q->):
    Read symbol at pos, then move pos -> pos+1

  Backward state (Q<-):
    Read symbol at pos, then move pos -> pos-1

  +---------+       +---------+       +---------+
  | q0 (->)  | --a-> | q1 (<-)  | --b-> | q2 (->)  |
  | pos: 1  |       | pos: 2  |       | pos: 1  |
  +---------+       +---------+       +---------+
  (read 'a',         (read 'b',         (read 'a',
   move right)        move left!)        move right)
```

### RhoCalc integration types

```rust
pub struct ChannelConstraint<W: Semiring> {
    pub channels: Vec<String>,
    pub transducer: WeightedTwoWayTransducer<W>,
}

pub struct JoinPatternAnalysis<W: Semiring> {
    pub optimal_order: Vec<usize>,
    pub reorder_cost: W,
    pub deadlock_cycles: Vec<Vec<usize>>,
    pub constraint_graph: HashMap<(usize, usize), W>,
}
```

## Algorithms

### Transduction (BFS Simulation)

```
Input:  WeightedTwoWayTransducer<W>, input word
Output: Vec<(output_word, weight)>

1. Enhanced tape: [|-, input[0], ..., input[n-1], -|]
   Positions: 0 to n+1
2. Build transition index: from_state -> transitions
3. BFS queue: (state, position, output, weight, visited_set)
4. Seed with initial states at position 0
5. While queue not empty:
   config = pop
   If position == n+2 (past right endmarker) and state is final:
     Add (output, weight * final_weight) to results
   If position >= tape_len: continue
   Read tape_symbol(position)
   For each matching transition from current state:
     new_pos = match source_state.direction:
       Forward -> position + 1
       Backward -> position - 1 (skip if position == 0)
     Crossing sequence check: if (to_state, new_pos) already visited,
       skip (loop detected)
     Push successor configuration
6. Bound exploration at max_configs = |Q| * tape_len * 1000
```

**Complexity**: O(|Q| * |w| * |delta|) per accepted path, bounded by max_configs.

### Sum (Disjoint Union)

```
Input:  WeightedTwoWayTransducer<W> M1, M2
Output: WeightedTwoWayTransducer<W>

1. offset = |M1.states|
2. Copy M1's states and transitions unchanged
3. Copy M2's states with IDs offset by |M1.states|
4. Copy M2's transitions with offset state IDs
5. Merge initial_weights, final_weights, alphabets
```

**Complexity**: O(|Q1| + |Q2| + |delta1| + |delta2|).

### Composition with One-Way FST

```
Input:  W2T self: A* -> B*, one-way FST: B* -> C*
Output: W2T: A* -> C*

1. Product states: |Q_w2t| x |Q_fst|
   product_id(w2t_id, fst_id) = w2t_id * fst_num_states + fst_id
2. Initial: (w2t_init, fst_init) with w2t initial weight
3. Final: (w2t_final, fst_final) with w2t final weight
4. For each W2T transition:
   If output is empty (epsilon): FST state unchanged
   If output is non-empty: thread output symbols through FST
     Find all FST paths consuming the output sequence
     For each path: create composed transition with accumulated output
   Combined weight = w2t_weight ⊗ fst_path_weight
```

**Complexity**: O(|Q_w2t| * |Q_fst| * |delta_w2t| * |delta_fst|^max_output_len).

### Join Pattern Analysis

```
Input:  channels: &[String], constraints: &[ChannelConstraint<W>]
Output: JoinPatternAnalysis<W>

1. Build channel index: name -> index
2. For each constraint with channels [ch_i, ch_j]:
   Add weighted edges (i, j) and (j, i) to constraint graph
3. Detect deadlock cycles via Tarjan's SCC on dependency graph
4. Find optimal consumption order via topological sort
5. Compute reorder cost: sum of constraint weights along chosen order
```

**Complexity**: O(|channels| + |constraints| * |channels|^2).

### To One-Way Conversion

```
Input:  WeightedTwoWayTransducer<W>
Output: Option<Vec<(input, output, weight)>>

If no backward states: enumerate one-way paths directly
Else: crossing sequence construction (exponential worst case)
  Max crossing sequences bounded by 2^(|Q| * 2)
  If too large: return None
  Else: enumerate all accepting runs on short inputs
```

## Integration

- **Pipeline** (`pipeline.rs`): `TwoWayAnalysis` reports forward/backward state counts, one-way equivalence, and deadlock cycles.
- **Multi-tape module** (`multi_tape.rs`): Multi-tape automata model multi-channel synchronization; two-way transducers model bidirectional constraint flow within channels.
- **WPDS module** (`wpds.rs`): Channel dependency analysis complements WPDS call-graph analysis for concurrent process verification.

## Diagnostics

No dedicated lint codes. The `TwoWayAnalysis` report includes:
- `num_states`: Total state count
- `num_forward`: Forward state count (|Q->|)
- `num_backward`: Backward state count (|Q<-|)
- `is_one_way_equivalent`: True if no backward states
- `deadlock_cycles`: Circular channel dependencies detected

## Examples

### Example 1: Simple forward transduction

```rust
use crate::automata::semiring::TropicalWeight;

let mut w2t = WeightedTwoWayTransducer::<TropicalWeight>::new();
let q0 = w2t.add_state(HeadDirection::Forward, Some("start".into()));
let q1 = w2t.add_state(HeadDirection::Forward, Some("end".into()));
w2t.set_initial(q0, TropicalWeight::one());
w2t.set_final(q1, TropicalWeight::one());

// Read left endmarker, output nothing
w2t.add_transition(q0, q0, TwoWayInput::LeftEndmarker,
    vec![], TropicalWeight::one());
// Read "a", output "A"
w2t.add_transition(q0, q1, TwoWayInput::Symbol("a".into()),
    vec!["A".into()], TropicalWeight::new(1.0));

let results = w2t.transduce(&["a".into()]);
// results contains (["A"], weight)
```

### Example 2: Bidirectional scanning

```rust
let mut w2t = WeightedTwoWayTransducer::<BooleanWeight>::new();
let q0 = w2t.add_state(HeadDirection::Forward, Some("scan_right".into()));
let q1 = w2t.add_state(HeadDirection::Backward, Some("scan_left".into()));
let q2 = w2t.add_state(HeadDirection::Forward, Some("done".into()));

w2t.set_initial(q0, BooleanWeight::one());
w2t.set_final(q2, BooleanWeight::one());

// Forward: read "a", switch to backward
w2t.add_transition(q0, q1, TwoWayInput::Symbol("a".into()),
    vec!["saw_a".into()], BooleanWeight::one());
// Backward: read left endmarker, switch to forward
w2t.add_transition(q1, q2, TwoWayInput::LeftEndmarker,
    vec!["back_at_start".into()], BooleanWeight::one());
// Forward: read right endmarker to accept
// (acceptance occurs when head passes right endmarker in a final state)
```

### Example 3: Join pattern deadlock detection

```rust
let channels = vec!["ch1".into(), "ch2".into(), "ch3".into()];
let constraint = ChannelConstraint {
    channels: vec!["ch1".into(), "ch2".into()],
    transducer: WeightedTwoWayTransducer::<BooleanWeight>::new(),
};
let analysis = analyze_join_pattern(&channels, &[constraint]);
// analysis.deadlock_cycles reports circular dependencies
// analysis.optimal_order provides consumption ordering
```

## Advanced Topics

**Edge cases**: A transducer with no initial states produces no results. The head cannot move left past position 0 (left endmarker boundary). The crossing sequence check prevents infinite loops by tracking visited `(state, position)` pairs per path. The `max_configs` bound prevents runaway exploration on pathological inputs.

**Interaction with other modules**: The `ChannelConstraint` and `JoinPatternAnalysis` types connect to Rholang's process algebra semantics. The `compose_one_way` operation connects to the WFST pipeline for post-processing transducer output.

**Performance**: BFS simulation is bounded by `|Q| * tape_len * 1000` configurations. The `to_one_way()` conversion is exponential in state count (crossing sequences); for transducers with > 20 states, it returns `None`. Composition with a one-way FST is polynomial in the product of state counts.

**Future extensions**: Determinization of two-way transducers (Filiot & Reynier 2016), streaming evaluation for long inputs, and bounded look-ahead optimization.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `transduce(input)` | `&[String]` | `Vec<(Vec<String>, W)>` | O(\|Q\| * \|w\| * \|delta\|) |
| `sum(m1, m2)` | two W2Ts | W2T | O(\|Q1\| + \|Q2\| + \|delta\|) |
| `compose_one_way(fst)` | FST params | W2T | O(\|Q_w2t\| * \|Q_fst\| * \|delta\|) |
| `to_one_way()` | `&self` | `Option<Vec<...>>` | O(2^\|Q\| * \|A\|^4) |
| `analyze()` | `&self` | `TwoWayAnalysis` | O(\|Q\|) |
| `analyze_join_pattern(...)` | channels + constraints | `JoinPatternAnalysis` | O(\|ch\|^2 + \|C\| * \|ch\|) |

### Feature gate

`two-way-transducer` (depends on `wfst-log`).

### Citations

- Feng, B. & Maletti, A. (2022). "Weighted two-way transducers." *CAI 2022*.
- Feng, B. & Maletti, A. (2023). "Weighted two-way transducers." *Information & Computation*, 293, 105064.
- Shepherdson, J.C. (1959). "The reduction of two-way automata to one-way automata." *IBM J. Res. Dev.*, 3(2), 198--200.
- Filiot, E. & Reynier, P.-A. (2016). "Transducers, logic and algebra for functions of finite words." *ACM SIGLOG News*, 3(3), 4--19.
