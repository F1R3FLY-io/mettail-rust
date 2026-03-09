# Weighted Tree Automata

| Property | Value |
|----------|-------|
| **Feature gate** | `tree-automata` |
| **Source file** | `prattail/src/tree_automaton.rs` (~1582 lines) |
| **Pipeline phase** | Term recognition and ranking |
| **Lint codes** | V03 (`wta-unrecognized-term`), V04 (`wta-hot-path`) |

## 1. Rationale

PraTTaIL grammars produce parse trees (terms). Verifying structural properties
of these trees -- such as type well-formedness, arity consistency, and priority
ordering -- requires tree automata, which generalize finite automata from strings
to trees. Weighting transitions with semiring values enables ranked enumeration
of parse trees (e.g., most probable parse, minimum-cost derivation) and
identification of hot paths for specialization.

## 2. Theoretical Foundations

### 2.1. Tree Automata

**Definition (Bottom-Up Finite Tree Automaton).** A bottom-up FTA is a tuple
`A = (Q, Sigma, Delta, F)` where:

- `Q` is a finite set of states
- `Sigma` is a ranked alphabet (function symbols with arities)
- `Delta` is a set of transition rules:
  `f(q_1, ..., q_n) -> q` where `f in Sigma` has arity `n`, `q_i, q in Q`
- `F subseteq Q` is the set of final (accepting) states

**Definition (Weighted Tree Automaton).** A WTA over semiring
`(S, oplus, otimes, 0, 1)` extends an FTA with a weight function:

`Delta: Sigma x Q^n -> Q x S`

Each transition `f(q_1, ..., q_n) -> q` has weight `w in S`.

### 2.2. Evaluation

**Definition (Bottom-Up Evaluation).** Given a term `t = f(t_1, ..., t_n)`:

1. Recursively evaluate each subtree `t_i` to obtain state assignments
   `states(t_i) = {(q, w) | q in Q, w in S}`.
2. For each transition `f(q_1, ..., q_n) -> q` with weight `w_delta`, and
   each combination of child state assignments `(q_i, w_i)`:
   ```
   total_weight = w_delta otimes w_1 otimes ... otimes w_n
   states(t)[q] oplus= total_weight
   ```

The term is accepted iff some state in `F` has non-zero weight.

**Definition (Top-Down Propagation).** Starting from the root with accepting
state assignments, propagate state information downward to annotate each subtree
with its contributing states and weights. This enables diagnostics (which
transitions dominate at each subtree position).

### 2.3. Hot-Path Analysis

**Definition (Heat).** The `WeightHeat` trait maps semiring weights to a
comparable `f64` value:

| Semiring | Heat formula | Interpretation |
|----------|-------------|----------------|
| Tropical | `1 / (1 + value)` | Lower cost = hotter |
| Counting | `count as f64` | More derivations = hotter |
| Boolean | `{0, 1}` | Reachable = hot |
| Viterbi | probability | Higher probability = hotter |
| Edit | `1 / (1 + distance)` | Lower edit distance = hotter |

**Definition (Specialization Candidate).** A transition whose heat exceeds
`2 * mean_heat` across all transitions. These transitions dominate the
automaton's behavior and benefit from dedicated fast-path states.

## 3. Algorithm Pseudocode

### 3.1. Bottom-Up Evaluation

```
function bottom_up_evaluate(automaton: WTA<W>, term: Term)
    -> HashMap<state_id, W>:

    if term.children is empty:
        // Leaf node: find transitions with matching symbol, arity 0
        result := {}
        for trans in automaton.transitions:
            if trans.symbol == term.symbol and trans.child_states is empty:
                result[trans.target_state] oplus= trans.weight
        return result

    // Recursive case
    child_states := [bottom_up_evaluate(automaton, child)
                     for child in term.children]

    result := {}
    for trans in automaton.transitions:
        if trans.symbol != term.symbol: continue
        if trans.child_states.len != term.children.len: continue

        // Check if all child states are compatible
        combined_weight := trans.weight
        all_match := true
        for (i, required_state) in trans.child_states:
            if required_state in child_states[i]:
                combined_weight := combined_weight otimes child_states[i][required_state]
            else:
                all_match := false
                break

        if all_match:
            result[trans.target_state] oplus= combined_weight

    return result
```

### 3.2. Top-Down Propagation

```
function top_down_propagate(automaton: WTA<W>, term: Term,
    root_states: HashMap<state_id, W>)
    -> Vec<HashMap<state_id, W>>:

    // annotations[i] = states assigned to the i-th node (pre-order)
    annotations := [HashMap::new(); term.node_count()]

    propagate_recursive(automaton, term, root_states, annotations, 0)
    return annotations

function propagate_recursive(automaton, term, current_states,
    annotations, node_index):
    annotations[node_index] := current_states

    // For each parent state, find transitions targeting it
    child_state_maps := [HashMap::new(); term.children.len()]
    for (parent_state, parent_weight) in current_states:
        for trans in automaton.transitions:
            if trans.target_state != parent_state: continue
            if trans.symbol != term.symbol: continue
            if trans.child_states.len != term.children.len: continue

            propagated := parent_weight otimes trans.weight
            for (i, child_state) in trans.child_states:
                child_state_maps[i][child_state] oplus= propagated

    // Recurse into children
    next_index := node_index + 1
    for (i, child) in term.children:
        next_index := propagate_recursive(automaton, child,
            child_state_maps[i], annotations, next_index)
```

### 3.3. Hot-Path Analysis

```
function hot_path_analysis(automaton: WTA<W>) -> HotPathReport<W>:
    heats := [(i, trans.weight.to_heat()) for (i, trans) in automaton.transitions]
    ranked := sort heats descending by heat

    total_heat := sum of all heats
    mean_heat := total_heat / len(heats)
    threshold := 2.0 * mean_heat

    candidates := [trans for trans in ranked if trans.heat >= threshold]
    coverage := sum(candidate heats) / total_heat

    return HotPathReport(ranked, candidates, coverage)
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `bottom_up_evaluate` | O(|t| * |Delta| * max_arity) | O(|t| * |Q|) |
| `top_down_propagate` | O(|t| * |Delta| * max_arity) | O(|t| * |Q|) |
| `hot_path_analysis` | O(|Delta| * log(|Delta|)) | O(|Delta|) |
| `specialize` | O(|candidates| * |Delta|) | O(|Delta| + |candidates|) |
| `add_state` | O(1) | O(1) |
| `add_transition` | O(1) | O(1) |

Where: |t| = term size (number of nodes), |Delta| = number of transitions,
|Q| = number of states, max_arity = maximum arity of any symbol.

## 5. Unicode Diagrams

### 5.1. Bottom-Up Evaluation

```
    Term: f(a, g(b))

    Step 1: Evaluate leaves
      a -> {q_leaf: 1}         (transition: a() -> q_leaf, w=1)
      b -> {q_leaf: 1}         (transition: b() -> q_leaf, w=1)

    Step 2: Evaluate g(b)
      g(q_leaf) -> q_g, w=2   (transition: g(q_leaf) -> q_g, w=2)
      g(b) -> {q_g: 1*2 = 2}

    Step 3: Evaluate f(a, g(b))
      f(q_leaf, q_g) -> q_f, w=3  (transition)
      f(a, g(b)) -> {q_f: 1*2*3 = 6}

    Accept: q_f in F? If yes, term accepted with weight 6.
```

### 5.2. Hot-Path Specialization

```
    Before specialization:

    ┌────────────┐   f(q1, q2) -> q3, w=0.8    ┌──────────┐
    │ q1, q2     │ ─────────────────────────────>│   q3     │
    │ (children) │                               │ (parent) │
    └────────────┘                               └──────────┘
                     g(q1) -> q3, w=0.1
                   ───────────────────────────>

    After specialization (hot transition f):

    ┌────────────┐   f(q1, q2) -> q3_fast, w=0.8  ┌──────────────┐
    │ q1, q2     │ ────────────────────────────────>│  q3_fast     │
    │ (children) │                                  │ (fast path)  │
    └────────────┘                                  └──────────────┘
                     g(q1) -> q3, w=0.1
                   ───────────────────────────>   ┌──────────┐
                                                   │   q3     │
                                                   │ (slow)   │
                                                   └──────────┘
```

### 5.3. WTA Architecture

```
    Term (tree)
          │
          v
    ┌──────────────────┐
    │ bottom_up_evaluate│
    │ (leaves -> root)  │
    └────────┬─────────┘
             │ state assignment map
             v
    ┌──────────────────┐
    │top_down_propagate │
    │ (root -> leaves)  │
    └────────┬─────────┘
             │ annotated term
             v
    ┌──────────────────┐
    │ hot_path_analysis │
    └────────┬─────────┘
             │ specialization candidates
             v
    ┌──────────────────┐
    │    specialize     │
    │ (fast-path states)│
    └──────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `TreeAutomaton::new()` -- Creates an empty WTA.
- `TreeAutomaton::add_state(is_final)` -- Adds a state.
- `TreeAutomaton::add_transition(symbol, child_states, target, weight)` -- Adds a weighted transition.
- `bottom_up_evaluate(automaton, term)` -- Evaluates a term from leaves to root.
- `top_down_propagate(automaton, term, root_states)` -- Annotates from root to leaves.
- `TreeAutomaton::hot_path_analysis()` -- Ranks transitions by heat.
- `TreeAutomaton::specialize(candidates)` -- Creates fast-path states.
- `construct_from_grammar(categories)` -- Builds a WTA from grammar categories.

### 6.2. Lint Emission

- **V03** (`wta-unrecognized-term`): Emitted when a term is not accepted by the
  WTA (no accepting state has non-zero weight). Severity: Warning.
- **V04** (`wta-hot-path`): Emitted to report hot transitions and their coverage.
  Severity: Note.

### 6.3. Repair Integration

No automated repairs. V03 diagnostics suggest checking the term structure
against the grammar's expected tree shape.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `TreeState` | State with id, optional label, is_final flag |
| `TreeTransition<W>` | Transition: symbol, child_states, target_state, weight |
| `TreeAutomaton<W>` | Full WTA: states, transitions, final_states |
| `Term` | Tree node: symbol, children vector |
| `WeightHeat` | Trait for converting semiring weight to f64 heat |
| `SpecializationCandidate` | Hot transition: index, symbol, child pattern, relative weight |
| `HotPathReport<W>` | Ranked transitions, candidates, coverage |

The `WeightHeat` trait is implemented for all standard semiring types
(TropicalWeight, CountingWeight, BooleanWeight, EditWeight, ComplexityWeight,
ViterbiWeight, ArcticWeight, FuzzyWeight, LogWeight).

## 8. Worked Example

**Grammar-derived WTA:**
```
Symbols: add (arity 2), num (arity 0), neg (arity 1)
States: q_num, q_expr (final)

Transitions:
  num() -> q_num, weight 1.0 (tropical)
  neg(q_expr) -> q_expr, weight 0.5
  add(q_expr, q_expr) -> q_expr, weight 1.0
  num() -> q_expr, weight 0.0  (promotion: num is an expr)
```

**Evaluate `add(num, neg(num))`:**
```
1. num -> {q_num: 1.0, q_expr: 0.0}
2. neg(num):
     neg(q_expr) -> q_expr, weight 0.5
     child weight for q_expr = 0.0
     total = 0.5 + 0.0 = 0.5 (tropical times = +)
     neg(num) -> {q_expr: 0.5}
3. add(num, neg(num)):
     add(q_expr, q_expr) -> q_expr, weight 1.0
     left child q_expr = 0.0, right child q_expr = 0.5
     total = 1.0 + 0.0 + 0.5 = 1.5 (tropical)
     add(num, neg(num)) -> {q_expr: 1.5}

Accepted with weight 1.5 (q_expr is final).
```

**Hot-path analysis:**
```
Heats: num->q_num: 1/(1+1.0)=0.5, num->q_expr: 1/(1+0.0)=1.0,
       neg: 1/(1+0.5)=0.67, add: 1/(1+1.0)=0.5
Mean heat = 0.67. Threshold = 1.33.
Candidate: num->q_expr (heat 1.0 < 1.33? No, so no candidates.)
No specialization needed.
```

## 9. References

1. Comon, H., Dauchet, M., Gilleron, R., Jacquemard, F., Lugiez, D.,
   Loding, C., Tison, S. & Tommasi, M. (2007).
   *Tree Automata Techniques and Applications (TATA)*. Available online.

2. Borchardt, B. (2004).
   "The Myhill-Nerode Theorem for Recognizable Tree Series."
   *Proc. 8th International Conference on Developments in Language Theory (DLT)*,
   LNCS 3340, Springer, pp. 146--158.

3. Thatcher, J.W. & Wright, J.B. (1968).
   "Generalized Finite Automata Theory with an Application to a Decision
   Problem of Second-Order Logic."
   *Mathematical Systems Theory*, 2(1), pp. 57--81.

4. Maletti, A. (2010).
   "Survey: Tree Transducers in Machine Translation."
   *Proc. 2nd Workshop on Non-Classical Models of Automata and Applications
   (NCMA)*, pp. 11--32.

5. Fülöp, Z. & Vogler, H. (2009).
   *Weighted Tree Automata and Tree Transducers.*
   In *Handbook of Weighted Automata*, Springer, pp. 313--403.
