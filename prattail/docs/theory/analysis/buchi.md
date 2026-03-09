# Buchi Automata

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `omega`                                |
| Source file    | `prattail/src/buchi.rs` (~1017 lines)  |
| Pipeline phase | Post-WPDS analysis (via `ltl` module)  |
| Lint codes     | (indirect, via LTL property checking)  |

## Rationale

Finite automata accept or reject finite words. Many important system properties -- liveness ("something good eventually happens"), fairness ("every request is eventually served"), and persistence -- are inherently properties of infinite behaviors. Buchi automata extend finite automata to infinite words (omega-regular languages), providing the standard formalism for liveness and fairness verification in model checking. In PraTTaIL, Buchi automata serve as the property specification mechanism: LTL formulas are compiled to Buchi automata, which are intersected with system models to check whether the system satisfies the property.

## Theoretical Foundations

**Definition (Buchi Automaton).** A nondeterministic Buchi automaton (NBA) is `A = (Q, Sigma, delta, Q_0, F)` where:
- `Q` is a finite set of states
- `Sigma` is the input alphabet
- `delta: Q x Sigma -> 2^Q` is the transition function
- `Q_0 subset Q` are initial states
- `F subset Q` are accepting states

**Definition (Buchi Acceptance).** A run `rho = q_0 q_1 q_2 ...` on an infinite word `w = a_0 a_1 a_2 ...` is accepting iff `inf(rho) intersect F != emptyset`, where `inf(rho)` is the set of states visited infinitely often.

**Theorem (Buchi, 1962).** Buchi automata recognize exactly the omega-regular languages -- the omega-closure of regular languages. This coincides with the monadic second-order theory of one successor (S1S).

**Theorem (Emptiness via SCC, Vardi & Wolper 1994).** A Buchi automaton is non-empty iff there exists a strongly connected component (SCC) that: (1) is reachable from an initial state, (2) contains at least one accepting state, and (3) contains a cycle (i.e., is non-trivial or has a self-loop).

**Definition (3-Counter Product).** The intersection `A1 x A2` of two Buchi automata uses a 3-phase counter to track which automaton's accepting condition has been satisfied since the last reset:
- Phase 0: waiting for `A1` to accept
- Phase 1: `A1` accepted, waiting for `A2` to accept
- Phase 2: both accepted -- this is the accepting phase; reset to 0

### References

1. Buchi, J.R. (1962). "On a decision method in restricted second order arithmetic." *Logic, Methodology and Philosophy of Science*, Stanford University Press.
2. Thomas, W. (1990). "Automata on infinite objects." *Handbook of Theoretical Computer Science*, Vol. B.
3. Vardi, M.Y. & Wolper, P. (1994). "Reasoning about infinite computations." *Information and Computation*, 115(1).

## Algorithm Pseudocode

### 1. Emptiness Check (SCC-Based)

```
FUNCTION check_emptiness(buchi):
    IF buchi.states is empty OR initial_states is empty THEN RETURN true

    // Step 1: BFS reachability from initial states
    reachable := BFS(buchi.initial_states, buchi.transitions)

    // Step 2: Build adjacency list for reachable subgraph
    adj, has_self_loop := build_adjacency(buchi, reachable)

    // Step 3: Tarjan SCC decomposition
    sccs := tarjan_scc(adj, reachable)

    // Step 4: Check each SCC for accepting cycle
    FOR EACH scc in sccs:
        has_cycle := |scc| > 1 OR (|scc| == 1 AND has_self_loop[scc[0]])
        IF NOT has_cycle THEN CONTINUE
        IF any state in scc is in buchi.accepting_states:
            RETURN false   // Non-empty: accepting cycle found

    RETURN true   // Empty: no accepting cycle
```

### 2. Intersection (3-Counter Product)

```
FUNCTION buchi_intersect(A, B):
    n_a, n_b := |A.states|, |B.states|
    product_id(q1, q2, phase) := (q1 * n_b + q2) * 3 + phase

    // Create product states: phase 2 states are accepting
    result := new BuchiAutomaton
    FOR q1 := 0 TO n_a-1:
        FOR q2 := 0 TO n_b-1:
            FOR phase := 0 TO 2:
                result.add_state(is_accepting = (phase == 2))

    // Initial states: (q1, q2, 0) for q1 in init(A), q2 in init(B)
    FOR q1 in A.initial_states:
        FOR q2 in B.initial_states:
            result.initial_states.add(product_id(q1, q2, 0))

    // Build transitions with phase cycling
    FOR EACH (q1_from, label) -> targets_a in A.transitions:
        FOR q2_from := 0 TO n_b-1:
            b_targets := B.transitions[(q2_from, label)]
            IF b_targets is None THEN CONTINUE
            FOR q1_to in targets_a:
                FOR q2_to in b_targets:
                    FOR phase := 0 TO 2:
                        next_phase := CASE phase OF
                            0: IF q1_from in F_A THEN 1 ELSE 0
                            1: IF q2_from in F_B THEN 2 ELSE 1
                            2: 0
                        result.add_transition(
                            product_id(q1_from, q2_from, phase),
                            label,
                            product_id(q1_to, q2_to, next_phase))

    RETURN result
```

### 3. WPDS-to-Buchi Bridge

```
FUNCTION from_wpds(wpds_analysis):
    // Each category becomes a state; zero fan-in categories are accepting/initial
    cat_list := sorted(wpds_analysis.call_graph.categories)
    buchi := new BuchiAutomaton

    FOR EACH cat in cat_list:
        fan_in := wpds_analysis.call_graph.fan_in[cat] or 0
        is_accepting := (fan_in == 0)
        id := buchi.add_state(is_accepting)
        buchi.states[id].label := cat
        IF fan_in == 0: buchi.initial_states.add(id)

    FOR EACH edge in call_graph.edges:
        from_id := cat_to_id[edge.caller_cat]
        to_id := cat_to_id[edge.callee_cat]
        buchi.add_transition(from_id, "{caller}->{callee}", to_id)

    RETURN buchi
```

## Complexity Analysis

| Operation          | Time                  | Space               |
|--------------------|-----------------------|---------------------|
| `check_emptiness`  | O(V + E)              | O(V + E)            |
| `buchi_intersect`  | O(V_A . V_B . E)      | O(V_A . V_B)        |
| `construct_buchi`  | O(V + E)              | O(V + E)            |
| `from_wpds`        | O(C + E)              | O(C + E)            |
| `add_state`        | O(1)                  | O(1)                |
| `add_transition`   | O(1) amortized        | O(1)                |

Where V = states, E = transitions, C = categories, V_A/V_B = states in automata A/B.

## 3-Counter Product State Machine

```
  Phase transitions in the product A x B:

  ┌──────────────────────────────────────────────────┐
  │                                                  │
  │   ┌─────────┐     q1 in F_A     ┌─────────┐    │
  │   │ Phase 0 │ ──────────────────▶│ Phase 1 │    │
  │   │ (wait A)│                    │ (wait B)│    │
  │   └────┬────┘                    └────┬────┘    │
  │        │                              │         │
  │   q1 not in F_A                  q2 in F_B      │
  │   (self-loop)                         │         │
  │                                       ▼         │
  │                              ┌──────────────┐   │
  │                              │   Phase 2    │   │
  │                              │ (ACCEPTING)  │   │
  │                              └──────┬───────┘   │
  │                                     │           │
  │              always reset ──────────┘           │
  │              to Phase 0                         │
  └──────────────────────────────────────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`from_wpds(wpds_analysis)`** -- Converts the WPDS call graph into a Buchi automaton. Categories become states, call edges become transitions. Zero fan-in categories (root entry points) are both initial and accepting.

### Intersection Workflow

```
LTL formula ──▶ ltl_to_buchi() ──▶ BuchiAutomaton (property)
                                         │
WPDS call graph ──▶ from_wpds() ──▶ BuchiAutomaton (system)
                                         │
                    buchi_intersect() ◀──┘
                         │
                    check_emptiness()
                         │
                    true (property holds) / false (violation found)
```

## Rust Implementation Notes

| Type               | Role                                                    |
|--------------------|---------------------------------------------------------|
| `BuchiState`       | State with id, is_accepting flag, optional label        |
| `BuchiTransition`  | Transition: from, to, label (None = epsilon)            |
| `BuchiAutomaton`   | NBA: states, alphabet, transitions map, initial/accepting sets |
| `construct_buchi`  | Builder: num_states, accepting set, initial set, transitions |

## Worked Example

Model checking: "Does every reachable category eventually return to root?"

**Step 1: System Buchi (from WPDS).**
```
Categories: Expr, Type, Pat
Call graph: Expr -> Type, Type -> Pat, Pat -> (none)
Fan-in: Expr=0, Type=1, Pat=1
```
Buchi automaton:
```
q0(Expr)* ──Expr->Type──▶ q1(Type) ──Type->Pat──▶ q2(Pat)
```
q0 is initial and accepting (fan-in = 0).

**Step 2: Property Buchi.** "Always eventually visit an accepting state" = Buchi with a self-loop accepting state.

**Step 3: Intersection.** Product has 3 x 1 x 3 = 9 states. Phase cycling tracks whether the system and property accepting states have been visited.

**Step 4: Emptiness.** If the intersection is non-empty, the property holds (there exists a computation satisfying both). If empty, the system violates the liveness property.

## References

1. Buchi, J.R. (1962). "On a decision method in restricted second order arithmetic." *Logic, Methodology and Philosophy of Science*.
2. Thomas, W. (1990). "Automata on infinite objects." *Handbook of TCS*, Vol. B.
3. Vardi, M.Y. & Wolper, P. (1994). "Reasoning about infinite computations." *Inf. Comput.*, 115(1).
4. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.
5. Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms." *SIAM J. Computing*, 1(2).
