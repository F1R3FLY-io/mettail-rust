# Alternating Automata

| Property       | Value                                    |
|----------------|------------------------------------------|
| Feature gate   | `alternating`                            |
| Source file    | `prattail/src/alternating.rs` (~1062 lines) |
| Pipeline phase | Post-WPDS analysis                       |
| Lint codes     | N05 (non-bisimilar)                      |

## Rationale

Nondeterministic automata allow existential branching: a transition can lead to multiple successor states, and the run accepts if some branch accepts. Alternating automata add universal branching: a transition can require that all successor states accept. This duality provides exponential succinctness over NFAs for certain languages and naturally models game semantics, CTL model checking, and branching properties of parse trees. In PraTTaIL, alternating automata model "all branches must type-check" (universal) vs. "any valid parse suffices" (existential) constraints.

## Theoretical Foundations

**Definition (Alternating Automaton).** An alternating automaton is `A = (Q_E union Q_A, Sigma, delta, q_0, Omega)` where:
- `Q_E` are existential (disjunctive) states: the run accepts if at least one successor run accepts.
- `Q_A` are universal (conjunctive) states: the run accepts if all successor runs accept.
- `delta: Q x Sigma -> 2^Q` is the transition function (each transition specifies a set of successor states).
- `Omega: Q -> N` is the priority function for parity acceptance (even = accepting, odd = rejecting).

**Definition (Parity Acceptance).** A run is accepting iff the minimum priority seen infinitely often along the run is even. For finite words, a state with even priority and no outgoing transitions is an accepting leaf.

**Theorem (Exponential Succinctness, Chandra et al. 1981).** Alternating finite automata can be exponentially more succinct than NFAs: there exist languages recognizable by alternating automata with `n` states that require `2^n` NFA states.

**Definition (Bisimulation Game).** Two processes are bisimilar iff the Defender has a winning strategy in the bisimulation game:
- Game positions: pairs `(p, q)` of states from the two automata.
- Attacker picks a transition in one automaton; Defender must match it (same label) in the other.
- Attacker wins if Defender cannot match; Defender wins if the game continues forever.

**Theorem (Bisimulation Decidability).** Bisimulation equivalence is decidable for alternating automata over finite words via attractor computation on the game graph.

### References

1. Chandra, A.K., Kozen, D.C., & Stockmeyer, L.J. (1981). "Alternation." *JACM*, 28(1).
2. Muller, D.E. & Schupp, P.E. (1987). "Alternating automata on infinite trees." *TCS*, 54(2-3).
3. Kupferman, O. & Vardi, M.Y. (2001). "Weak alternating automata are not that weak." *ACM TOCL*, 2(3).
4. Jurdzinski, M. (2000). "Small progress measures for solving parity games." *STACS*.

## Algorithm Pseudocode

### 1. Emptiness Check (Bottom-Up Fixpoint)

```
FUNCTION check_emptiness(automaton):
    n := |automaton.states|
    IF n == 0 OR initial_state is None THEN RETURN true

    // Build adjacency: transitions_from[s] = list of successor sets
    transitions_from := build_adjacency(automaton)

    // Initialize: leaf states with even priority accept
    accepting := array[n] of false
    FOR s := 0 TO n-1:
        IF transitions_from[s] is empty:
            accepting[s] := (automaton.states[s].priority mod 2 == 0)

    // Fixpoint propagation
    REPEAT:
        changed := false
        FOR s := 0 TO n-1:
            IF accepting[s] OR transitions_from[s] is empty THEN CONTINUE

            new_status := CASE automaton.states[s].branching OF
                Existential: ANY transition in transitions_from[s] has
                             ALL successors accepting
                Universal:   ALL transitions in transitions_from[s] have
                             ALL successors accepting

            IF new_status AND NOT accepting[s]:
                accepting[s] := true
                changed := true
    UNTIL NOT changed

    RETURN NOT accepting[initial_state]
```

### 2. Bisimulation Game (Attractor Computation)

```
FUNCTION bisimulation_game(A, B):
    na, nb := |A.states|, |B.states|
    pos(pa, pb) := pa * nb + pb
    attacker_wins := array[na * nb] of false

    // Phase 1: Immediate wins (unmatched labels)
    FOR pa := 0 TO na-1:
        FOR pb := 0 TO nb-1:
            a_labels := labels of transitions from pa in A
            b_labels := labels of transitions from pb in B
            IF a_labels has label not in b_labels OR vice versa:
                attacker_wins[pos(pa, pb)] := true

    // Phase 2: Backward propagation
    REPEAT:
        changed := false
        FOR pa := 0 TO na-1:
            FOR pb := 0 TO nb-1:
                IF attacker_wins[pos(pa, pb)] THEN CONTINUE
                // Check if Attacker can force a win via any label
                IF exists_winning_attack(pa, pb, A, B, attacker_wins):
                    attacker_wins[pos(pa, pb)] := true
                    changed := true
    UNTIL NOT changed

    RETURN NOT attacker_wins[pos(init_A, init_B)]
```

### 3. Category Bisimulation Analysis

```
FUNCTION analyze_from_bundle(all_syntax, categories):
    // Phase 1: Build one alternating automaton per category
    cat_automata := []
    FOR EACH category in categories:
        aa := new AlternatingAutomaton
        root := aa.add_state(Existential, priority=0)
        aa.initial_state := root
        FOR EACH rule in category:
            rule_state := aa.add_state(Universal, priority=0)
            aa.add_transition(root, rule_label, [rule_state])
            FOR EACH item in rule.items:
                item_state := aa.add_state(Existential, priority=0)
                aa.add_transition(rule_state, item_label, [item_state])
        cat_automata.add((category.name, aa))

    // Phase 2: Pairwise bisimulation
    non_bisimilar := []
    FOR i := 0 TO |cat_automata|-1:
        FOR j := i+1 TO |cat_automata|-1:
            IF NOT bisimulation_game(cat_automata[i], cat_automata[j]):
                non_bisimilar.add((names[i], names[j]))

    RETURN AlternatingAnalysis(non_bisimilar, total_states)
```

## Complexity Analysis

| Operation               | Time              | Space             |
|-------------------------|-------------------|-------------------|
| `check_emptiness`       | O(V^2 . E)        | O(V + E)          |
| `bisimulation_game`     | O(V_A . V_B . E)  | O(V_A . V_B)      |
| `analyze_from_bundle`   | O(C^2 . V . E)    | O(C . V)          |
| `add_state`             | O(1)              | O(1)              |
| `add_transition`        | O(1)              | O(k) for k succs  |

Where V = states, E = transitions, C = categories, V_A/V_B = states in automata A/B.

## State Machine Diagram

```
  Grammar Category "Expr" as Alternating Automaton:

    q0 [E, p=0]  (root, existential: try any rule)
    ├── "Add" ──▶ q1 [A, p=0]  (universal: all items must match)
    │              ├── "NT:Expr" ──▶ q3 [E, p=0]
    │              ├── "T:+"    ──▶ q4 [E, p=0]
    │              └── "NT:Expr" ──▶ q5 [E, p=0]
    │
    └── "Num" ──▶ q2 [A, p=0]  (universal: all items must match)
                   └── "T:num"  ──▶ q6 [E, p=0]

  Legend:
    [E] = Existential (at least one successor must accept)
    [A] = Universal   (all successors must accept)
    p=N = parity priority (even = accepting)
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`analyze_from_bundle(all_syntax, categories)`** -- Builds alternating automata from grammar categories and runs pairwise bisimulation. Root states are existential (try any rule), rule states are universal (all items must match). Returns `AlternatingAnalysis` with non-bisimilar category pairs.

### Lint Emission

- **N05 (non-bisimilar)**: Emitted for each pair of categories found to be non-bisimilar, indicating structurally distinct parse behavior.

## Rust Implementation Notes

| Type                      | Role                                                    |
|---------------------------|---------------------------------------------------------|
| `AlternatingState`        | State with branching mode (Existential/Universal) and parity priority |
| `BranchingMode`           | Enum: Existential (some successor), Universal (all successors) |
| `AlternatingTransition`   | Transition: from, label, successor set                  |
| `AlternatingAutomaton`    | Full automaton with states, alphabet, transitions       |
| `AlternatingAnalysis`     | Pipeline result: non-bisimilar pairs, state count       |

## Worked Example

Two categories `Expr` and `Arith` have similar but not identical rules:

```
Expr:  Add . Expr ::= Expr "+" Expr ;
       Num . Expr ::= INT ;

Arith: Sum . Arith ::= Arith "+" Arith ;
       Lit . Arith ::= INT ;
       Neg . Arith ::= "-" Arith ;
```

**Step 1:** Build alternating automata. `Expr` has 2 rules, `Arith` has 3.

**Step 2:** Run `bisimulation_game(Expr_AA, Arith_AA)`.

- Attacker picks transition `Neg` in `Arith`. Defender cannot match (no `Neg` in `Expr`).
- Result: Attacker wins. `Expr` and `Arith` are NOT bisimilar.

**Step 3:** Lint output:
```
[N05-note] categories 'Expr' and 'Arith' are not bisimilar
  hint: Arith has rules not present in Expr (e.g., Neg).
```

## References

1. Chandra, A.K., Kozen, D.C., & Stockmeyer, L.J. (1981). "Alternation." *JACM*, 28(1).
2. Muller, D.E. & Schupp, P.E. (1987). "Alternating automata on infinite trees." *TCS*, 54(2-3).
3. Kupferman, O. & Vardi, M.Y. (2001). "Weak alternating automata are not that weak." *ACM TOCL*, 2(3).
4. Jurdzinski, M. (2000). "Small progress measures for solving parity games." *STACS*.
5. Milner, R. (1989). *Communication and Concurrency.* Prentice Hall.
