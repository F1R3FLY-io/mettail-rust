# Parikh Image Automaton

## What Is It?

A Parikh automaton is a nondeterministic finite automaton (NFA) where each transition carries a D-dimensional counter vector (`ParikhWeight<D>`). The automaton accepts a word if there exists an accepting run, and the **Parikh image** of the run is the sum (⊗) of all counter vectors along the run. The set of all achievable Parikh images can be projected to a **semilinear set**, enabling decidable coverage completeness checking.

Located in `simulation/src/parikh_automaton.rs`.

## What Does It Do?

The Parikh automaton module provides:

1. **ParikhAutomaton<D>**: an NFA with D-dimensional counter transitions, supporting both labeled and epsilon transitions.
2. **NFA simulation**: `run()` and `all_runs()` compute Parikh vectors for accepting runs.
3. **Product construction**: `intersect()` builds the product of two Parikh automata.
4. **Semilinear set projection**: `project_semilinear()` computes the Parikh image as a finite union of linear sets.
5. **LinearSet and SemilinearSet**: data structures for representing and querying semilinear sets.

## Why Was It Chosen?

### From Finite Automata to Resource Counting

Standard NFAs answer the qualitative question: "Does the automaton accept this word?" Parikh automata answer the quantitative question: "How many times does each event occur along an accepting run?"

In the MeTTaIL context:
- Events = rewrite rule firings
- Dimensions = one per rule (or per rule category)
- Parikh vector = the rule-firing profile of an execution

### Semilinear Sets and Coverage

Parikh (1966) proved that the set of achievable Parikh vectors is always a semilinear set (for context-free languages and below). This means the set has a finite description:

```
{ [2, 1] + k₁·[1, 0] + k₂·[0, 1] | k₁, k₂ ∈ ℕ }
∪ { [0, 3] + k·[1, 1] | k ∈ ℕ }
```

Such a description enables:
- **Coverage completeness**: check whether a target vector (e.g., "every rule fires at least once") belongs to the semilinear set.
- **Boundedness**: check whether any dimension can grow without bound.
- **Equivalence**: compare Parikh images of two different automata.

## Data Structures

### ParikhAutomaton<D>

```rust
pub struct ParikhAutomaton<const D: usize> {
    pub states: Vec<ParikhState>,
    transitions_by_source: HashMap<StateId, Vec<ParikhTransition<D>>>,
    pub initial_state: StateId,
    pub accepting_states: HashSet<StateId>,
}
```

Transitions are indexed by source state for efficient lookup.

### ParikhTransition<D>

```rust
pub struct ParikhTransition<const D: usize> {
    pub from: StateId,
    pub to: StateId,
    pub symbol: Option<u8>,       // None for epsilon transitions
    pub weight: ParikhWeight<D>,
}
```

### LinearSet<D>

```rust
pub struct LinearSet<const D: usize> {
    pub base: ParikhWeight<D>,          // offset vector
    pub periods: Vec<ParikhWeight<D>>,  // period vectors
}
```

Represents `{ base + k₁·p₁ + k₂·p₂ + ... | kᵢ ∈ ℕ }`.

### SemilinearSet<D>

```rust
pub struct SemilinearSet<const D: usize> {
    pub components: Vec<LinearSet<D>>,  // union of linear sets
}
```

## NFA Simulation

### Epsilon Closure

Before reading each input symbol, the automaton computes the **epsilon closure**: all states reachable via epsilon transitions, with accumulated weights:

```
PROCEDURE epsilon_closure(start_configs: [(StateId, ParikhWeight)]):
    result ← HashMap::new()
    queue ← VecDeque::new()

    FOR (s, w) in start_configs:
        result[s] ← result[s] ⊕ w     // ⊕ = component-wise max
        queue.push((s, w))

    WHILE queue not empty:
        (state, weight) ← queue.pop_front()
        FOR t in epsilon_transitions_from(state):
            new_weight ← weight ⊗ t.weight    // ⊗ = component-wise add
            combined ← result[t.to] ⊕ new_weight
            IF combined ≠ result[t.to] THEN    // new information
                result[t.to] ← combined
                queue.push((t.to, new_weight))

    RETURN result.entries()
```

The fixpoint check (`combined ≠ result[t.to]`) ensures termination even with epsilon cycles, because the ⊕ operation (component-wise max) is idempotent and monotone: the values can only increase, and they are bounded by the maximum weight encountered.

### All Runs

```
PROCEDURE all_runs(input: [u8], max_configs: usize) → [ParikhWeight]:
    configs ← epsilon_closure([(initial_state, 1̄)])

    FOR byte in input:
        next_configs ← []
        FOR (state, weight) in configs:
            FOR t in transitions_from(state):
                IF t.symbol == Some(byte) THEN
                    next_configs.push((t.to, weight ⊗ t.weight))

        configs ← epsilon_closure(next_configs)

        // Bound configurations to prevent exponential blowup
        IF |configs| > max_configs THEN
            configs ← configs[0..max_configs]

    RETURN [w | (s, w) ∈ configs, s ∈ accepting_states]
```

The `max_configs` bound prevents exponential blowup on highly nondeterministic automata.

## Product Construction

The `intersect()` method builds the standard product automaton:

```
PROCEDURE intersect(A₁, A₂) → ParikhAutomaton:
    // Product states: (s₁, s₂) for all s₁ ∈ A₁, s₂ ∈ A₂
    pair_to_id(s₁, s₂) = s₁ × |A₂.states| + s₂

    // Accepting states: both components must accept
    accepting ← { pair_to_id(s₁, s₂) | s₁ ∈ F₁, s₂ ∈ F₂ }

    // Labeled transitions: synchronized on the same input symbol
    FOR s₁ in A₁.states:
        FOR t₁ in A₁.transitions_from(s₁):
            IF t₁.symbol is Some(sym) THEN
                FOR s₂ in A₂.states:
                    FOR t₂ in A₂.transitions_from(s₂):
                        IF t₂.symbol == Some(sym) THEN
                            add_transition(
                                from: pair_to_id(s₁, s₂),
                                to:   pair_to_id(t₁.to, t₂.to),
                                symbol: sym,
                                weight: t₁.weight ⊗ t₂.weight
                            )

    // Epsilon transitions: one component moves, the other stays
    FOR s₁ in A₁.states:
        FOR t₁ in A₁.epsilon_transitions_from(s₁):
            FOR s₂ in A₂.states:
                add_transition(
                    from: pair_to_id(s₁, s₂),
                    to:   pair_to_id(t₁.to, s₂),
                    symbol: None,
                    weight: t₁.weight
                )

    // Symmetric for A₂'s epsilon transitions
    ...
```

The product Parikh weight combines both automata's counter vectors via ⊗ (component-wise addition), so the product tracks the union of all counted events.

## Semilinear Set Projection

The `project_semilinear()` function computes the Parikh image of the accepted language:

```
PROCEDURE project_semilinear(automaton) → SemilinearSet:
    components ← []

    FOR accept in accepting_states:
        // DFS: find all simple paths from initial to accept
        FOR path in simple_paths(initial_state, accept):
            base ← ⊗ over all transition weights along path

            // Find simple cycles reachable from states on this path
            periods ← []
            FOR state on path:
                FOR self_loop from state:
                    IF self_loop.weight ≠ 0̄ THEN
                        periods.push(self_loop.weight)

            components.push(LinearSet { base, periods })

    // Deduplicate
    components.sort()
    components.dedup()

    RETURN SemilinearSet { components }
```

**Intuition:** Each simple path from the initial state to an accepting state contributes a base vector (the sum of weights along the path). Cycles along the path contribute period vectors (the cycle can be traversed any number of times, adding its weight each time).

### Containment Checking

```
PROCEDURE LinearSet.contains(target):
    IF NOT base ≤ target THEN RETURN false    // component-wise ≤
    diff ← target - base

    IF periods is empty THEN RETURN diff == [0; D]

    IF |periods| == 1 THEN
        // Check if diff is a scalar multiple of the single period
        ratio ← None
        FOR i in 0..D:
            IF periods[0][i] == 0 THEN
                IF diff[i] ≠ 0 THEN RETURN false
            ELSE
                r ← diff[i] / periods[0][i]
                IF diff[i] mod periods[0][i] ≠ 0 THEN RETURN false
                IF ratio is Some(prev) AND prev ≠ r THEN RETURN false
                ratio ← Some(r)
        RETURN true

    ELSE
        // Multiple periods: bounded search (heuristic)
        RETURN bounded_coefficient_search(diff, periods, max_coeff)
```

For multiple periods, the containment check reduces to an integer linear programming problem. The implementation uses a bounded search (trampoline-based enumeration of coefficient combinations up to a maximum coefficient), which is exact for small period vectors but heuristic for large ones.

## Coverage Completeness Checking

To check whether a target coverage vector (e.g., "every rule fires at least once" = [1, 1, 1, ...]) is achievable:

```
PROCEDURE is_coverage_achievable(automaton, target):
    semilinear ← project_semilinear(automaton)
    RETURN semilinear.contains(target)
```

If the target is not in the semilinear set, the coverage goal is **provably unachievable** by any input to the automaton. This is a powerful negative result that no amount of random testing can overcome.

## Reachable Parikh Vectors

For debugging and small automata, `reachable_parikh_vectors()` enumerates all achievable Parikh vectors by BFS over input words up to a given length:

```
PROCEDURE reachable_parikh_vectors(max_len, alphabet):
    result ← HashSet
    queue ← [empty_word]

    WHILE queue not empty:
        word ← queue.pop()
        FOR w in all_runs(word):
            result.insert(w)
        IF |word| < max_len THEN
            FOR sym in alphabet:
                queue.push(word ++ [sym])

    RETURN result
```

This is exponential in `max_len` and is suitable only for small automata and short inputs.

## References

- Parikh, R.J. (1966). "On Context-Free Languages." Journal of the ACM, 13(4), pp. 570-581.
- Klaedtke, F. and Ruess, H. (2003). "Monadic Second-Order Logics with Cardinalities." Proceedings of ICALP, pp. 681-696.
- Cadilhac, M., Finkel, A., and McKenzie, P. (2012). "Affine Parikh Automata." Theoretical Informatics and Applications, 46(4), pp. 511-545.
- Ginsburg, S. and Spanier, E.H. (1966). "Semigroups, Presburger Formulas, and Languages." Pacific Journal of Mathematics, 16(2), pp. 285-296.
