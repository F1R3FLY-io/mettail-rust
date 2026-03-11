# Register Automata -- Data-Aware Finite-State Computation with Register Storage

## Quick Start

Register automata extend classical finite automata with a fixed number of registers that can store and compare data values from the input. This enables data-dependent transitions -- matching opening/closing tags, enforcing variable binding consistency, or tracking context-sensitive constraints that go beyond the power of ordinary finite automata. The module provides `RegisterAutomaton<W>`, parameterized over any semiring `W`, with operations: `evaluate()` for nondeterministic BFS simulation, `check_equivalence()` for symmetric-difference equivalence, `dead_registers()` for dead-store analysis, `normalize()` for dead-store elimination, and `find_unbound_references()` for detecting tests of uninitialized registers.

**Motivating example**: In a PraTTaIL grammar for XML-like languages, the pattern `<tag> ... </tag>` requires matching the opening and closing tag names. A register automaton stores the opening tag in register 0 via `Store`, then verifies the closing tag matches via `TestEq`. Classical finite automata cannot express this over an infinite tag alphabet.

```
Data word: [(Some("open"), Symbol("div")), (Some("close"), Symbol("div"))]

RegisterAutomaton (1 register)
      |
      +---> evaluate(data_word)          -> W (acceptance weight)
      +---> check_equivalence(other)     -> bool
      +---> dead_registers()             -> Vec<usize>
      +---> normalize()                  -> () (remove dead stores)
      +---> find_unbound_references()    -> Vec<(trans_idx, reg_idx)>
```

## Intuition

Think of a register automaton as a customs agent with a clipboard (registers). When a traveler (data value) arrives, the agent can write the traveler's passport number on the clipboard (`Store`), check if a new traveler has the same passport number as one already recorded (`TestEq`), verify they are different (`TestNeq`), or confirm the traveler is entirely new -- not matching any recorded number (`TestFresh`). The clipboard has a fixed number of slots, but the domain of passport numbers is infinite.

**Before this module**: Context-sensitive constraints like tag matching were handled by ad-hoc name-comparison logic outside the automata framework.

**After this module**: Data-dependent constraints participate in the formal automata pipeline with semiring weights, equivalence checking, and dead-register analysis.

**Key insight**: The fixed number of registers ensures decidability of emptiness (and, for the deterministic case, equivalence), while the infinite data domain gives expressive power beyond classical finite automata. The guard/assignment separation (check guards first, then apply stores) ensures clean operational semantics.

## Theoretical Foundations

**Definition 6.1 (Data Word).** A data word over structural alphabet `Sigma` and data domain `D` is a sequence `(a_1, d_1)(a_2, d_2)...(a_n, d_n)` where `a_i in Sigma` and `d_i in D`.

**Definition 6.2 (Register Automaton).** A register automaton with `k` registers over semiring `W` is `A = (Q, Sigma, D, k, delta, q_0, R_0, F)` where:
- `Q` is a finite set of states
- `Sigma` is the structural alphabet (labels)
- `D = {Integer(i64), Symbol(String), Unit}` is the data domain
- `k` is the number of registers
- `delta ⊆ Q x Sigma x Ops^k x Q x W` is the weighted transition relation, where `Ops = {Nop, Store, TestEq, TestNeq, TestFresh}`
- `q_0` is the initial state
- `R_0 in (D ∪ {bottom})^k` is the initial register valuation
- `F ⊆ Q` are accepting states

**Definition 6.3 (Register Operations).** Each transition carries a vector of `k` operations:
- `Nop`: no effect on this register
- `Store`: copy the current input data value into this register
- `TestEq`: guard -- current input must equal this register's value
- `TestNeq`: guard -- current input must NOT equal this register's value
- `TestFresh`: guard -- current input must not equal ANY register's value

Guards are checked before the transition fires; stores are applied after all guards pass.

**Definition 6.4 (Configuration).** A configuration is `(q, rho)` where `q in Q` and `rho: [0..k) -> D ∪ {bottom}` is the register valuation. The configuration space is `|Q| x (|D| + 1)^k`.

**Theorem 6.1 (Decidability, Kaminski & Francez 1994).** Emptiness of register automata is decidable. For deterministic register automata, equivalence is also decidable.

**Theorem 6.2 (Equivalence via Symmetric Difference).** Two register automata `A` and `B` are equivalent iff the symmetric difference `L(A) Delta L(B)` is empty, which is checked via product construction over configurations.

## Activation: Binder Items → M6

M6 (Register) is activated by predicate dispatch when the grammar or its predicates
indicate name-binding patterns requiring data-equality and freshness tracking.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features()
      │                                 │
      ▼                                 ▼
NameBinding                      Relation_eq / Relation_neq / Relation_fresh
  Binder items present             Equality/freshness comparisons
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M6_REGISTER bit set
```

**Grammar heuristic**: Presence of `Binder` items in any rule indicates that the
grammar introduces variable scopes. Register automata are needed to verify
scope-correctness (every use within scope, no variable capture) and freshness
(newly introduced names are distinct from existing ones).

**Predicate trigger**: Relations named `eq`, `neq`, `equal`, `not_equal`, `fresh`,
`==`, `!=`, `equals`, or `related`. Also, any unknown relation name defaults to
M6 (conservative: register automata handle general data predicates).

**Example grammar rule triggering M6**:
```
("Lambda", "Expr", [Terminal("\\"), Binder("x","Expr",false), Terminal("."), NT("Expr","body")])
   ↑ Binder item introduces variable scope → M6 activated
```

**Theoretical justification**: Binder items introduce variable scopes — exactly the
situation where register automata (Kaminski & Francez 1994) provide decidable
verification. Scope-correctness and capture-avoidance cannot be expressed by finite
automata over an unbounded name alphabet; register storage enables data comparison.

## Design

### Core types

```rust
pub enum DataValue {
    Integer(i64),
    Symbol(String),
    Unit,
}

pub enum RegisterOp {
    Nop,         // no operation
    Store,       // write input data to register
    TestEq,      // guard: input == register
    TestNeq,     // guard: input != register
    TestFresh,   // guard: input not in any register
}

pub struct RegisterState {
    pub id: usize,
    pub is_accepting: bool,
    pub label: Option<String>,
}

pub struct RegisterTransition<W: Semiring> {
    pub from: usize,
    pub to: usize,
    pub label: Option<String>,
    pub ops: Vec<RegisterOp>,    // one per register
    pub weight: W,
}

pub struct RegisterAutomaton<W: Semiring> {
    pub num_registers: usize,
    pub states: Vec<RegisterState>,
    pub alphabet: HashSet<String>,
    pub transitions: Vec<RegisterTransition<W>>,
    pub initial_state: Option<usize>,
    pub initial_registers: Vec<Option<DataValue>>,
    pub accepting_states: HashSet<usize>,
}
```

### Transition semantics diagram

```
       label = "open"
       ops = [Store, Nop]
       weight = w
  +--------+                  +--------+
  | q0     | --- open/[S,-] ->| q1     |
  | regs:  |                  | regs:  |
  | [_,_]  |                  | [d,_]  |
  +--------+                  +--------+
                                  |
                                  | label = "close"
                                  | ops = [TestEq, Nop]
                                  v
                              +--------+
                              | q2 (*) |
                              | regs:  |
                              | [d,_]  |
                              +--------+
```

## Algorithms

### Nondeterministic BFS Evaluation

```
Input:  RegisterAutomaton<W>, data_word = [(label_1, d_1), ..., (label_n, d_n)]
Output: W (sum of weights over all accepting runs)

1. current = {(initial_state, initial_registers) -> W::one()}
2. For each (label_i, d_i) in data_word:
   next = {}
   For each ((state, regs), path_weight) in current:
     For each transition t from state with matching label:
       If check_guards(t.ops, regs, d_i):
         new_regs = apply_stores(t.ops, regs, d_i)
         new_weight = path_weight ⊗ t.weight
         next[(t.to, new_regs)] ⊕= new_weight
   current = next
3. Return ⊕_{(state, regs, w) in current, state in F} w
```

**Complexity**: O(|w| * |configs| * |delta|). The number of configurations can be exponential in k (registers), but is typically small for PraTTaIL grammars.

### Equivalence Check (Product + Symmetric Difference)

```
Input:  RegisterAutomaton<W> A, B
Output: true if L(A) = L(B)

1. Product configs: (Option<state_A>, Option<state_B>, regs_A, regs_B)
   - None represents dead/sink state (no transitions, non-accepting)
2. Collect representative data values from both automata
   (including a fresh sentinel)
3. BFS over product configurations:
   For each config, check:
     acc_A = A accepting at state_A
     acc_B = B accepting at state_B
     If acc_A != acc_B: return false (symmetric difference non-empty)
4. For each (label, data_val) pair:
   Compute successors for both A and B
   Case 1: both have successors -> pair them
   Case 2: only A -> B enters dead sink
   Case 3: only B -> A enters dead sink
5. Return true if BFS exhausts without finding a difference
```

**Complexity**: O(|Q_A| * |Q_B| * |test_values| * |delta|) with configuration explosion bounded by |D|^(k_A + k_B).

### Dead Register Analysis

```
Input:  RegisterAutomaton<W>
Output: Vec<usize> (indices of dead registers)

1. stored = {i | exists transition with ops[i] = Store}
2. tested = {i | exists transition with ops[i] in {TestEq, TestNeq, TestFresh}}
3. dead = stored \ tested (stored but never tested)
4. Return sorted(dead)
```

### Unbound Reference Detection

```
Input:  RegisterAutomaton<BooleanWeight>
Output: Vec<(trans_idx, reg_idx)>

1. BFS from initial state, tracking "possibly stored" register sets
2. For each reachable state q:
   stored[q] = union of register stores on paths to q
3. For each transition t from state q:
   For each register i where ops[i] in {TestEq, TestNeq, TestFresh}:
     If i not in stored[q] and initial_registers[i] is None:
       Flag (t.index, i) as unbound reference
```

## Integration

- **Nominal module** (`nominal.rs`): Register automata complement the orbit-finite symmetry model with an operational approach to name binding. Registers track concrete bindings; the nominal module tracks equivalence classes.
- **Pipeline** (`pipeline.rs`): `RegisterAnalysis` reports dead registers and unbound references as diagnostics.
- **Symbolic module** (`symbolic.rs`): Register operations can be viewed as predicate guards over an infinite data domain, connecting to the symbolic automata framework.

## Diagnostics

No dedicated lint codes. The `RegisterAnalysis` report includes:
- `num_states`: Number of states
- `num_registers`: Number of registers
- `dead_registers`: Indices of registers that are stored but never tested
- `unbound_references`: Transitions that test registers that may not have been initialized

## Examples

### Example 1: Tag matching

```rust
let mut ra = RegisterAutomaton::<BooleanWeight>::new(1);
let q0 = ra.add_state(false, Some("start".into()));
let q1 = ra.add_state(false, Some("tag_stored".into()));
let q2 = ra.add_state(true, Some("matched".into()));
ra.initial_state = Some(q0);

// open: store tag name in register 0
ra.add_transition(q0, q1, Some("open".into()),
    vec![RegisterOp::Store], BooleanWeight::one());
// close: test that tag name matches register 0
ra.add_transition(q1, q2, Some("close".into()),
    vec![RegisterOp::TestEq], BooleanWeight::one());

let word = vec![
    (Some("open".into()), DataValue::Symbol("div".into())),
    (Some("close".into()), DataValue::Symbol("div".into())),
];
let w = ra.evaluate(&word);
assert_eq!(w, BooleanWeight::one()); // matching tags accepted
```

### Example 2: Freshness constraint

```rust
let mut ra = RegisterAutomaton::<BooleanWeight>::new(2);
let q0 = ra.add_state(false, None);
let q1 = ra.add_state(false, None);
let q2 = ra.add_state(true, None);
ra.initial_state = Some(q0);

// First binding: store in r0
ra.add_transition(q0, q1, Some("bind".into()),
    vec![RegisterOp::Store, RegisterOp::Nop], BooleanWeight::one());
// Second binding: must be fresh (not equal to r0), store in r1
ra.add_transition(q1, q2, Some("bind".into()),
    vec![RegisterOp::TestFresh, RegisterOp::Store], BooleanWeight::one());

// "x" then "y" (fresh) -> accepted
let word = vec![
    (Some("bind".into()), DataValue::Symbol("x".into())),
    (Some("bind".into()), DataValue::Symbol("y".into())),
];
assert_eq!(ra.evaluate(&word), BooleanWeight::one());

// "x" then "x" (not fresh) -> rejected
let word2 = vec![
    (Some("bind".into()), DataValue::Symbol("x".into())),
    (Some("bind".into()), DataValue::Symbol("x".into())),
];
assert_eq!(ra.evaluate(&word2), BooleanWeight::zero());
```

## Advanced Topics

**Edge cases**: An automaton with no initial state returns `W::zero()` for all data words. A transition label of `None` matches any input label (wildcard). Registers initially set to `None` (unbound) cause `TestEq` and `TestNeq` to fail -- the register must be explicitly initialized via `Store` before testing.

**Interaction with other modules**: Register automata connect to the symbolic automata module (`symbolic.rs`) -- register guards can be viewed as predicates over data values. The VPA module handles structural nesting; register automata add data-awareness on top of structural constraints.

**Performance**: Nondeterministic evaluation is exponential in the number of registers (each register can hold any data value). For PraTTaIL grammars with 1--3 registers, evaluation is fast. The `normalize()` method removes dead stores, reducing the effective register count.

**Future extensions**: Deterministic register automaton minimization and symbolic BFS for large data domains.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `evaluate(data_word)` | `&[(Option<String>, DataValue)]` | `W` | O(\|w\| * \|configs\| * \|delta\|) |
| `check_equivalence(other)` | `&RegisterAutomaton<W>` | `bool` | O(\|Q_A\|\|Q_B\| * \|D\|^k * \|delta\|) |
| `dead_registers()` | `&self` | `Vec<usize>` | O(\|delta\| * k) |
| `normalize()` | `&mut self` | `()` | O(\|delta\| * k) |
| `analyze(automaton)` | `&RegisterAutomaton<BooleanWeight>` | `RegisterAnalysis` | O(\|Q\| + \|delta\|) |

### Feature gate

Always available (core module).

### Citations

- Kaminski, M. & Francez, N. (1994). "Finite-memory automata." *Theoretical Computer Science*, 134(2), 329--363.
- Neven, F., Schwentick, T. & Vianu, V. (2004). "Finite state machines for strings over infinite alphabets." *ACM Trans. Comput. Logic*, 5(3), 403--435.
- Segoufin, L. (2006). "Automata and logics for words and trees over an infinite alphabet." *CSL 2006*, LNCS 4207, 41--57.
