# Weighted Multi-Tape Automata -- Synchronized Multi-Stream Computation

## Quick Start

Weighted multi-tape automata generalize WFSTs (K=2) to an arbitrary number of synchronized tapes. Each transition reads one symbol (or epsilon) from each of the K tapes simultaneously, with an associated semiring weight. The module provides `WeightedMultiTapeAutomaton<W, K>` with const generic `K`, plus the operations: `pair()` (combine two 1-tape automata into a 2-tape automaton), `project()` (extract single-tape behavior), `auto_intersect()` (constrain two tapes to share labels), `multi_tape_intersect()` (K-tape product construction), and `evaluate()` (BFS evaluation on K concrete input streams).

**Motivating example**: Multi-channel receives in Rholang/MeTTaIL -- `for (@x <- ch1, @y <- ch2) { ... }` -- naturally map to multi-tape automata: ch1 becomes tape 1, ch2 becomes tape 2. The automaton synchronizes consumption across channels, with semiring weights encoding priority, probability, or cost.

```
Channel ch1 (tape 1)  +  Channel ch2 (tape 2)
      |                       |
      v                       v
WeightedMultiTapeAutomaton<W, 2>
      |
      +---> pair(a1, a2)              (2-tape product construction)
      +---> project(tape_idx)         (single-tape projection)
      +---> auto_intersect(i, j)      (constrain tapes i,j to match)
      +---> multi_tape_intersect(a,b) (K-tape product)
      +---> evaluate(inputs)          (BFS over (state, positions))
      +---> analyze()                 (disconnected/overlapping tapes)
```

## Intuition

Think of a multi-tape automaton as a DJ with K turntables. Each turntable plays a different record (tape). On each step, the DJ can advance any subset of turntables (reading their next symbol) while leaving others paused (epsilon). The DJ selects transitions that match the current symbols on all active turntables simultaneously. The weight on each transition represents the DJ's preference for that particular mix.

**Before this module**: Multi-channel consumption in Rholang was analyzed channel-by-channel without a unified synchronization framework. Cross-channel constraints required ad-hoc product constructions.

**After this module**: K-channel synchronization is formalized in a single automaton with const-generic K. The `pair`, `project`, and `auto_intersect` operations from Kempe (2004) provide algebraic compositionality.

**Key insight**: The const generic `K` ensures that the number of tapes is fixed at compile time, enabling the compiler to optimize array operations and catch tape-index errors statically.

## Theoretical Foundations

**Definition 8.1 (Weighted K-Tape Automaton, Kempe 2004).** A weighted K-tape automaton over semiring `W` is `M = (Q, (Sigma_1, ..., Sigma_K), delta, I, F)` where:
- `Q` is a finite set of states
- `Sigma_k` is the alphabet for tape k (1 <= k <= K)
- `delta ⊆ Q x (Sigma_1 ∪ {epsilon}) x ... x (Sigma_K ∪ {epsilon}) x Q x W` is the weighted transition relation
- `I: Q -> W` is the initial weight function
- `F: Q -> W` is the final (accepting) weight function

A transition `(q, a_1, ..., a_K, q', w)` reads symbol `a_k` from tape `k` (or epsilon if `a_k = None`) simultaneously, moving to state `q'` with weight `w`.

**Definition 8.2 (Pair Construction, Kempe 2004, Definition 3).** Given two 1-tape automata `A_1` and `A_2`, the pair construction produces a 2-tape automaton with:
- States: `|Q_1| x |Q_2|` (all pairs)
- Synchronized transitions: both tapes advance
- Epsilon-extended: one tape advances, the other stays
- Weights: `w_1 ⊗ w_2` (semiring multiplication)

**Definition 8.3 (Auto-Intersection, Kempe 2004).** Given a K-tape automaton `M` and tape indices `i`, `j`, `auto_intersect(M, i, j)` retains only transitions where `labels[i] == labels[j]`, constraining tapes `i` and `j` to consume identical symbol sequences.

**Theorem 8.1 (Product Construction).** The K-tape product of automata `A` and `B` has states `|Q_A| x |Q_B|` and transitions synchronized on all K tapes. Weights are combined via `w_A ⊗ w_B`. The language of the product is the intersection of the component languages on each tape.

## Design

### Core types

```rust
pub struct MultiTapeState {
    pub id: usize,
    pub label: Option<String>,
}

pub struct MultiTapeTransition<W: Semiring, const K: usize> {
    pub from: usize,
    pub to: usize,
    pub labels: [Option<String>; K],    // one per tape, None = epsilon
    pub weight: W,
}

pub struct WeightedMultiTapeAutomaton<W: Semiring, const K: usize> {
    pub states: Vec<MultiTapeState>,
    pub transitions: Vec<MultiTapeTransition<W, K>>,
    pub initial: HashMap<usize, W>,
    pub accepting: HashMap<usize, W>,
}
```

### Multi-tape transition diagram (K=2)

```
                tape 1: "a"    tape 2: "x"
                    |              |
  +--------+       v              v       +--------+
  | (q1,q2)| ---["a", "x"] / w -------> | (q1',q2')|
  +--------+                              +--------+

                tape 1: "a"    tape 2: epsilon
                    |              |
  +--------+       v              .       +--------+
  | (q1,q2)| ---["a", None] / w ------> | (q1',q2)|
  +--------+                              +--------+
```

## Algorithms

### Pair Construction (2-tape from 1-tape)

```
Input:  A1 = WeightedMultiTapeAutomaton<W, 1>
        A2 = WeightedMultiTapeAutomaton<W, 1>
Output: WeightedMultiTapeAutomaton<W, 2>

1. Create |Q1| x |Q2| product states
   product_id(q1, q2) = q1 * |Q2| + q2
2. Initial states: (i1, i2) with weight w_i1 ⊗ w_i2
3. Accepting states: (f1, f2) with weight w_f1 ⊗ w_f2
4. Synchronized transitions (both tapes advance):
   For each (t1 in A1.transitions, t2 in A2.transitions):
     Add transition (t1.from, t2.from) --[t1.label, t2.label]--> (t1.to, t2.to)
     weight = t1.weight ⊗ t2.weight
5. Epsilon-extended (A1 advances, A2 stays):
   For each t1 in A1.transitions, for each q2 in Q2:
     Add transition (t1.from, q2) --[t1.label, None]--> (t1.to, q2)
6. Epsilon-extended (A2 advances, A1 stays):
   For each t2 in A2.transitions, for each q1 in Q1:
     Add transition (q1, t2.from) --[None, t2.label]--> (q1, t2.to)
```

**Complexity**: O(|Q1| * |Q2| * (|delta1| * |delta2| + |delta1| * |Q2| + |delta2| * |Q1|)).

### Evaluation (BFS over K-tape configurations)

```
Input:  WeightedMultiTapeAutomaton<W, K>, inputs: [Vec<String>; K]
Output: W (total acceptance weight)

1. Seed: (state, [0; K]) for each initial state
2. BFS queue: (state, positions_per_tape, path_weight)
3. While queue not empty:
   (state, positions, weight) = pop
   If all tapes fully consumed and state is accepting:
     result ⊕= weight ⊗ accept_weight[state]
   For each transition from state:
     Check: for each tape k, if label[k] is Some(s),
       then positions[k] < inputs[k].len() and inputs[k][positions[k]] == s
     If all match: advance positions, weight = weight ⊗ t.weight
4. Return result
```

**Complexity**: O(|Q| * prod_k |input_k| * |delta|).

### Auto-Intersection

```
Input:  WeightedMultiTapeAutomaton<W, K>, tape_i, tape_j
Output: WeightedMultiTapeAutomaton<W, K> (filtered)

1. Copy all states, initial weights, accepting weights
2. For each transition t:
   If t.labels[tape_i] == t.labels[tape_j]:
     Keep transition
   Else:
     Discard transition
```

**Complexity**: O(|Q| + |delta|).

## Integration

- **WFST module** (`wfst.rs`): Multi-tape automata generalize 2-tape WFSTs to K tapes.
- **Pipeline** (`pipeline.rs`): `MultiTapeAnalysis` reports disconnected and overlapping tapes.
- **Two-way transducer module** (`two_way_transducer.rs`): Multi-tape automata model multi-channel synchronization; two-way transducers model bidirectional constraint flow.

## Diagnostics

No dedicated lint codes. The `MultiTapeAnalysis` report includes:
- `num_states`: Number of states
- `num_tapes`: K (number of tapes)
- `disconnected_tapes`: Tapes that are always epsilon (could be analyzed independently)
- `overlapping_tapes`: Tape pairs with identical labels on every transition (could be merged)

## Examples

### Example 1: Two-channel synchronization

```rust
use crate::automata::semiring::TropicalWeight;

// Channel 1: accepts "a" then "b"
let mut ch1 = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
let q0 = ch1.add_state(Some("ch1_start".into()));
let q1 = ch1.add_state(Some("ch1_mid".into()));
let q2 = ch1.add_state(Some("ch1_end".into()));
ch1.set_initial(q0, TropicalWeight::one());
ch1.set_accepting(q2, TropicalWeight::one());
ch1.add_transition(q0, q1, [Some("a".into())], TropicalWeight::new(1.0));
ch1.add_transition(q1, q2, [Some("b".into())], TropicalWeight::new(2.0));

// Channel 2: accepts "x"
let mut ch2 = WeightedMultiTapeAutomaton::<TropicalWeight, 1>::new();
let r0 = ch2.add_state(None);
let r1 = ch2.add_state(None);
ch2.set_initial(r0, TropicalWeight::one());
ch2.set_accepting(r1, TropicalWeight::one());
ch2.add_transition(r0, r1, [Some("x".into())], TropicalWeight::new(0.5));

// Combine into 2-tape automaton
let combined = pair(&ch1, &ch2);
```

### Example 2: Auto-intersection constraint

```rust
use crate::automata::semiring::BooleanWeight;

let mut mta = WeightedMultiTapeAutomaton::<BooleanWeight, 3>::new();
let q0 = mta.add_state(None);
let q1 = mta.add_state(None);
mta.set_initial(q0, BooleanWeight::one());
mta.set_accepting(q1, BooleanWeight::one());

// Tape 0 = "a", tape 1 = "a", tape 2 = "b"
mta.add_transition(q0, q1,
    [Some("a".into()), Some("a".into()), Some("b".into())],
    BooleanWeight::one());

// Constrain tapes 0 and 1 to match -- this transition survives
let constrained = mta.auto_intersect(0, 1);
assert_eq!(constrained.transitions.len(), 1);
```

## Advanced Topics

**Edge cases**: An automaton with no initial states evaluates to `W::zero()`. The `pair()` construction includes epsilon-extended transitions, so both tapes can advance independently. The `evaluate()` BFS uses visited-set deduplication but records only the first weight for each `(state, positions)` pair -- for exact semiring evaluation, a more sophisticated algorithm (Dijkstra for tropical) would be needed.

**Interaction with other modules**: Multi-tape automata extend the WFST framework from 2 tapes to K tapes. The `auto_intersect` operation connects to the symbolic automata module's predicate conjunction -- constraining tapes is analogous to conjoining guard predicates.

**Performance**: The `pair` construction produces O(|Q1| * |Q2|) states and O(|delta1| * |delta2| + |delta1| * |Q2| + |delta2| * |Q1|) transitions. For K tapes, the configuration space is O(|Q| * prod_k |input_k|), which is polynomial for fixed K but grows with tape lengths.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `pair(a1, a2)` | two 1-tape automata | 2-tape automaton | O(\|Q1\|\|Q2\| * \|delta\|) |
| `project(tape_idx)` | `&self, usize` | 1-tape automaton | O(\|Q\| + \|delta\|) |
| `auto_intersect(i, j)` | `&self, usize, usize` | `Self` | O(\|Q\| + \|delta\|) |
| `multi_tape_intersect(a, b)` | two K-tape automata | K-tape automaton | O(\|Q_A\|\|Q_B\| * \|delta_A\|\|delta_B\|) |
| `evaluate(inputs)` | `&[Vec<String>; K]` | `W` | O(\|Q\| * prod \|input_k\| * \|delta\|) |
| `analyze()` | `&self` | `MultiTapeAnalysis` | O(K^2 * \|delta\|) |

### Feature gate

`multi-tape` (depends on `wfst-log`).

### Citations

- Kempe, A. (2004). "Weighted multi-tape automata and transducers for NLP." *Proceedings of the 2004 Conference on Empirical Methods in NLP*.
- Rabin, M.O. & Scott, D. (1959). "Finite automata and their decision problems." *IBM Journal of Research and Development*, 3(2), 114--125.
