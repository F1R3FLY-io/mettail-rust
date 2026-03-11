# Weighted Visibly Pushdown Automata -- Decidable Nested-Word Analysis with Semiring Weights

## Quick Start

Visibly Pushdown Automata (VPA) are a subclass of pushdown automata where the input alphabet is partitioned into call, return, and internal symbols. The stack discipline is determined entirely by the input word -- call symbols push, return symbols pop, internal symbols leave the stack unchanged. This visible stack discipline yields a class closed under all Boolean operations with decidable equivalence and inclusion, making VPAs ideal for verifying bracket/delimiter-structure properties of PraTTaIL grammars.

The module generalizes the classical Boolean-weighted VPA to `WeightedVpa<W>`, where each transition carries a semiring weight. The type alias `Vpa = WeightedVpa<BooleanWeight>` preserves backward compatibility. Weighted extensions enable shortest-path parsing (`TropicalWeight`), derivation counting (`CountingWeight`), and probabilistic parsing (`LogWeight`).

**Motivating example**: In a PraTTaIL grammar with parenthesized expressions, `(`, `{`, `[` are call symbols and `)`, `}`, `]` are return symbols. The VPA determinization guarantees that bracket-matching analysis remains polynomial, and weighted inclusion checking ensures error recovery never accepts inputs rejected by the original grammar.

```
Grammar bracket structure
      |
      v
VpaAlphabet (call / return / internal partition)
      |
      v
WeightedVpa<W>
      |
      +---> determinize()            (subset construction for VPA)
      +---> weighted_run()           (semiring evaluation on word)
      +---> weighted_determinize()   (weight-propagating determinization)
      +---> weighted_inclusion()     (IdempotentSemiring inclusion test)
      +---> reachable_states()       (BFS reachability)
      +---> trim()                   (dead-state elimination)
```

## Intuition

Think of a VPA as a security guard at a building with revolving doors (call/return symbols) and hallways (internal symbols). The guard can verify that every person who enters through a revolving door eventually exits through the matching revolving door, because the doors themselves dictate push/pop behavior. The guard does not need to know the building's internal layout -- the visible door types determine the stack. Weights assign a cost to each passage.

**Before this module**: PraTTaIL's bracket-matching analysis used ad-hoc parenthesis counting that could not express weighted nesting properties or verify structural equivalence between grammar variants.

**After this module**: Bracket structure is formalized with decidable equivalence, determinization, and weighted inclusion. Error recovery can be verified to never accept structurally malformed inputs that the original grammar rejects.

**Key insight**: The visible stack discipline -- where the input alone determines push/pop behavior -- is the crucial restriction that makes VPAs closed under complement, intersection, and determinization, while general pushdown automata are not.

## Theoretical Foundations

**Definition 4.1 (Partitioned Alphabet).** A VPA alphabet is a triple `(Sigma_c, Sigma_r, Sigma_int)` where the input alphabet `Sigma = Sigma_c ∪ Sigma_r ∪ Sigma_int` is partitioned into:
- `Sigma_c` (call symbols): trigger a push onto the stack
- `Sigma_r` (return symbols): trigger a pop from the stack
- `Sigma_int` (internal symbols): leave the stack unchanged

**Definition 4.2 (Weighted Visibly Pushdown Automaton).** A weighted VPA over semiring `W` is `M = (Q, Sigma, Gamma, delta, Q_0, Z_0, F)` where:
- `Q` is a finite set of states
- `Sigma = Sigma_c ∪ Sigma_r ∪ Sigma_int` is the partitioned alphabet
- `Gamma` is the stack alphabet
- `delta` consists of three weighted transition functions:
  - `delta_c: Q x Sigma_c -> 2^(Q x Gamma x W)` (call: push `gamma`, weight `w`)
  - `delta_r: Q x Sigma_r x Gamma -> 2^(Q x W)` (return: pop `gamma`, weight `w`)
  - `delta_int: Q x Sigma_int -> 2^(Q x W)` (internal: no stack change, weight `w`)
- `Q_0 ⊆ Q` are initial states with weights `initial_weights: Q -> W`
- `Z_0 in Gamma` is the initial stack symbol
- `F ⊆ Q` are accepting states with weights `accepting_weights: Q -> W`

**Theorem 4.1 (Closure Properties, Alur & Madhusudan 2004).** The class of visibly pushdown languages is effectively closed under union, intersection, complement, concatenation, and Kleene star. Equivalence and inclusion are decidable.

**Theorem 4.2 (Determinization).** Every nondeterministic VPA can be determinized via a subset construction adapted to the visible stack discipline. The determinized VPA has at most `2^|Q|` macro-states, and the visible stack discipline ensures that stack height is determined by the input, preventing exponential stack blow-up.

**Theorem 4.3 (Weighted Inclusion, Idempotent Semirings).** For idempotent semirings `W` (where `a ⊕ a = a`), weighted inclusion `L_w(A) ⊆ L_w(B)` is decidable: for every word `w`, `A.weighted_run(w) ⊕ B.weighted_run(w) = B.weighted_run(w)`. This reduces to a product construction + weighted emptiness check.

## Activation: Paired Bracket Terminals → M4

M4 (VPA) is activated by predicate dispatch when the grammar or its predicates
indicate visible pushdown structure requiring balanced-delimiter analysis.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features() / walk_mso()
      │                                 │
      ▼                                 ▼
PairedDelimiters                 is_fixpoint_relation()
  "()" / "{}" / "[]"              "letprop" / "fixpoint" / "mu" / "nu"
  "begin"..."end"                  Recursive predicate scope
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M4_VPA bit set
```

**Grammar heuristic**: Scan terminal symbols for paired brackets — `(` and `)`,
`{` and `}`, `[` and `]`, `begin` and `end`, `do` and `done`. Both a call symbol
and a return symbol must be present; an unpaired bracket does not trigger VPA.

**Predicate trigger**: Relations named `letprop`, `fixpoint`, `mu`, `nu`, `letrec`,
or `recursive` indicate recursive predicate definitions with scope nesting.

**Example grammar rule triggering M4**:
```
("Paren", "Expr", [Terminal("("), NonTerminal("Expr","inner"), Terminal(")")])
   ↑ has "(" and ")" → paired brackets → M4 activated
```

**Theoretical justification**: Paired delimiters create a visible pushdown structure.
The Alur-Madhusudan theorem (2004) shows VPA is the right model for bracket-matching:
neither weaker (regular) nor stronger (full CFL) captures the structure with
full Boolean closure and decidable equivalence.

## Design

### Core types

```rust
pub struct VpaAlphabet {
    pub call_symbols: HashSet<String>,
    pub return_symbols: HashSet<String>,
    pub internal_symbols: HashSet<String>,
}

pub enum SymbolKind { Call, Return, Internal }

pub struct VpaState {
    pub id: usize,
    pub label: Option<String>,
}

pub struct WeightedVpa<W: Semiring> {
    pub states: Vec<VpaState>,
    pub alphabet: VpaAlphabet,
    pub call_transitions: HashMap<(usize, String), Vec<(usize, String, W)>>,
    pub return_transitions: HashMap<(usize, String, String), Vec<(usize, W)>>,
    pub internal_transitions: HashMap<(usize, String), Vec<(usize, W)>>,
    pub initial_states: HashSet<usize>,
    pub accepting_states: HashSet<usize>,
    pub initial_stack_symbol: String,
    pub initial_weights: HashMap<usize, W>,
    pub accepting_weights: HashMap<usize, W>,
}

pub type Vpa = WeightedVpa<BooleanWeight>;
```

### State machine diagram

```
  Internal         Call (push gamma)         Return (pop gamma)
     |                  |                         |
     v                  v                         v
 +--------+     +--------+     +--------+     +--------+
 | q0     | -a->| q1     | -(->| q2     | -)->| q3     |
 | (init) |     |        |     |stack:   |     | (acc)  |
 +--------+     +--------+     |[Z0,gamma]+    +--------+
                                                  |
   Sigma_int         Sigma_c        Sigma_r       |
   no stack          push           pop            v
   change            gamma          gamma       accept
```

## Algorithms

### Determinization (Subset Construction for VPA)

```
Input:  Nondeterministic WeightedVpa<W>
Output: Deterministic WeightedVpa<W>

1. Create dead/sink macro-state {} (ID 0)
2. Create initial macro-state S_0 = {q | q in Q_0}
3. Worklist <- {S_0, {}}
4. While worklist not empty:
   a. S <- pop(worklist)
   b. For each internal symbol a:
      T <- {q' | q in S, (q,a,q') in delta_int}
      Add transition S --a--> T
   c. For each call symbol c:
      T <- {q' | q in S, (q,c,q',gamma) in delta_c}
      Push stack symbol "M{id(S)}"
      Add call transition S --c/push M{id(S)}--> T
   d. For each return symbol r, for each stack symbol M{caller_id}:
      T <- {q' | q in S, caller_q in S_caller, (q,r,gamma,q') in delta_r}
      Add return transition S --r/pop M{caller_id}--> T
   e. Acceptance: S is accepting iff S ∩ F != emptyset
5. Result is total and deterministic
```

**Complexity**: O(2^|Q| * |Sigma| * |Q|) worst case; typically much smaller due to reachability pruning.

### Weighted Run Simulation

```
Input:  WeightedVpa<W>, word w = a_1 ... a_n
Output: W (total acceptance weight)

1. configs <- {(q0, [Z0]) -> initial_weights[q0] | q0 in Q_0}
2. For each symbol a_i in w:
   next_configs <- {}
   Match classify(a_i):
     Internal: for each (q, stack, w) in configs:
       for each (q', tw) in delta_int(q, a_i):
         next_configs[(q', stack)] ⊕= w ⊗ tw
     Call: for each (q, stack, w) in configs:
       for each (q', gamma, tw) in delta_c(q, a_i):
         next_configs[(q', stack ++ gamma)] ⊕= w ⊗ tw
     Return: for each (q, stack, w) in configs:
       if |stack| > 1:
         top = stack.last()
         for each (q', tw) in delta_r(q, a_i, top):
           next_configs[(q', stack.pop())] ⊕= w ⊗ tw
   configs <- next_configs
3. Return ⊕_{(q,_,w) in configs, q in F} w ⊗ accepting_weights[q]
```

**Complexity**: O(|w| * |configs| * |delta|). The number of distinct stack configurations is bounded by the nesting depth of the word.

### Weighted Inclusion Check

```
Input:  WeightedVpa<W> A, B where W: IdempotentSemiring
Output: true if L_w(A) ⊆ L_w(B)

1. Product BFS over (state_a, state_b?, stack_a, stack_b)
2. state_b = None represents dead/sink (no matching transition in B)
3. For each accepting config where A accepts:
   a. Compute total_a = w_a ⊗ accept_weight_a
   b. If B is dead or not accepting: inclusion violated
   c. Else: total_b = w_b ⊗ accept_weight_b
      If total_a ⊕ total_b != total_b: inclusion violated
4. Return true iff no violation found
```

**Complexity**: O(|Q_A| * |Q_B| * depth * |delta|) with bounded exploration depth.

## Integration

- **Pipeline** (`pipeline.rs`): `VpaAnalysis` reports bracket structure properties and inclusion violations.
- **Decision tree** (`decision_tree.rs`): VPA determinization feeds into bracket-dispatch optimization.
- **Lint module** (`lint.rs`): V05 (weighted transition anomaly) and V06 (weighted inclusion violation) diagnostics.

## Diagnostics

### V05 -- Weighted Transition Anomaly

**Severity**: Warning. Fires when a weighted VPA has transitions with anomalous weights (all-zero outgoing weights from a non-dead state, or vacuous identity weights). Indicates dead weighted paths or effectively unweighted structure.

### V06 -- Weighted Inclusion Violation

**Severity**: Error. Fires when `weighted_inclusion(A, B)` detects `L_w(A) not⊆ L_w(B)` -- there exists a word with higher weight in A than B. Guards grammar transformations that must preserve or reduce weights.

## Examples

### Example 1: Bracket matching

```rust
let alpha = VpaAlphabet::new(
    HashSet::from(["(".into()]),  // call
    HashSet::from([")".into()]),  // return
    HashSet::from(["x".into()]), // internal
);
let mut vpa = Vpa::new(alpha);
let q0 = vpa.add_state(Some("start".into()));
let q1 = vpa.add_state(Some("inside".into()));
vpa.initial_states.insert(q0);
vpa.accepting_states.insert(q0);
// ( pushes, x is internal, ) pops
// After "(x)", stack returns to Z0 and we are in accepting state
```

### Example 2: Weighted inclusion check

```rust
use crate::automata::semiring::TropicalWeight;

let alpha = VpaAlphabet::new(
    HashSet::from(["(".into()]),
    HashSet::from([")".into()]),
    HashSet::from(["a".into()]),
);
let mut a = WeightedVpa::<TropicalWeight>::new(alpha.clone());
let mut b = WeightedVpa::<TropicalWeight>::new(alpha);
// Configure A with higher weights than B
// weighted_inclusion(&a, &b) checks that A's weights
// are absorbed by B under the tropical natural order
```

## Advanced Topics

**Edge cases**: A VPA with no initial states has empty language. Return transitions on an empty stack (only Z_0) are blocked -- the automaton halts. Unknown symbols (not in any partition) cause all configurations to die.

**Interaction with other modules**: VPA determinization connects to the WPDS module for context-free reachability analysis. The `weighted_run()` method shares the semiring evaluation pattern with the WFST pipeline.

**Performance**: Determinization is exponential in the worst case (subset construction) but is typically small for PraTTaIL grammars with bounded bracket nesting. The `trim()` method removes unreachable states to minimize the VPA before expensive operations.

**Future extensions**: Myhill-Nerode minimization for VPAs (Alur, Kumar, Madhusudan & Viswanathan 2005) would complement the existing determinization.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `determinize()` | `&self` | `WeightedVpa<W>` | O(2^\|Q\| * \|Sigma\|) |
| `is_deterministic()` | `&self` | `bool` | O(\|delta\|) |
| `reachable_states()` | `&self` | `HashSet<VpaState>` | O(\|Q\| + \|delta\|) |
| `trim()` | `&self` | `WeightedVpa<W>` | O(\|Q\| + \|delta\|) |
| `weighted_run(word)` | `&self, &[&str]` | `W` | O(\|w\| * \|Q\| * \|delta\|) |
| `weighted_determinize()` | `&self` | `WeightedVpa<W>` | O(2^\|Q\| * \|Sigma\|) |
| `weighted_inclusion(other)` | `&self, &WeightedVpa<W>` | `bool` | O(\|Q_A\|\|Q_B\| * depth) |

### Lint codes

| Code | Severity | Description |
|------|----------|-------------|
| V05 | Warning | Weighted transition anomaly (dead/vacuous weights) |
| V06 | Error | Weighted inclusion violation |

### Feature gate

Always available (core module).

### Citations

- Alur, R. & Madhusudan, P. (2004). "Visibly pushdown languages." *STOC 2004*, 202--211.
- Alur, R. & Madhusudan, P. (2009). "Adding nesting structure to words." *Journal of the ACM*, 56(3), 1--43.
- Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005). "Congruences for visibly pushdown languages." *ICALP 2005*, LNCS 3580, 1102--1114.
