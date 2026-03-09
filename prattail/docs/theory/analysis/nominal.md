# Nominal Automata

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `nominal`                              |
| Source file    | `prattail/src/nominal.rs` (~1271 lines)|
| Pipeline phase | Post-WPDS analysis                     |
| Lint codes     | N03 (scope-violation), N04 (scope-narrowing) |

## Rationale

Classical finite automata operate over a fixed, finite alphabet. Languages with name binding (rho calculus, lambda calculus, pi calculus) require reasoning over an infinite set of names, where the specific identity of a name matters only up to renaming. Nominal automata solve this by operating over orbit-finite sets -- the state space has finitely many equivalence classes (orbits) under name permutation, even though the raw state space is infinite. This enables decidable emptiness, universality, and scope checking for name-passing grammars expressed in PraTTaIL.

## Theoretical Foundations

**Definition (Nominal Set).** A nominal set is a set `X` equipped with an action of the group of finite permutations on atoms (names), such that every element `x in X` has a finite support -- a finite set of atoms `supp(x)` such that any permutation fixing `supp(x)` pointwise also fixes `x`.

**Definition (Orbit).** The orbit of an element `x` under the symmetry group is `{pi . x | pi is a finite permutation}`. An orbit-finite set has finitely many orbits.

**Definition (Equivariant Transition).** A transition function `delta` is equivariant if for every permutation `pi`: `delta(pi . q, pi . a) = pi . delta(q, a)`. This ensures the automaton's behavior is independent of the particular choice of names.

**Theorem (Decidable Emptiness, Bojanczyk et al. 2014).** Emptiness and universality are decidable for nominal DFAs over equality atoms. The key insight is that orbit-finite representations yield finitely many equivalence classes to explore.

**Freshness.** A name `a` is fresh for a state `q` (written `a # q`) if `a` is not in `supp(q)`. Freshness is the dual of support membership and is the mechanism by which new names are introduced.

### References

1. Bojanczyk, M., Klin, B., & Lasota, S. (2014). "Automata theory in nominal sets." *Logical Methods in Computer Science*, 10(3).
2. Pitts, A.M. (2013). *Nominal Sets: Names and Symmetry in Computer Science.* Cambridge University Press.
3. Montanari, U. & Pistore, M. (2005). "History-dependent automata: An introduction." *Formal Methods for Components and Objects*, LNCS 3657.
4. Tzevelekos, N. (2011). "Fresh-register automata." *ACM SIGPLAN Notices*, 46(1).

## Algorithm Pseudocode

### 1. Orbit-Finite Reachability (BFS)

Computes which states are reachable from the initial state via BFS, tracking depth for scope analysis.

```
FUNCTION reachable_depths(automaton):
    depths := empty map
    IF automaton.initial_state is None THEN RETURN depths
    queue := [initial_state]
    depths[initial_state] := 0

    WHILE queue is not empty:
        state := dequeue(queue)
        FOR EACH transition (state, pattern, target) in adjacency[state]:
            IF target not in depths:
                depths[target] := depths[state] + 1
                enqueue(queue, target)

    RETURN depths
```

### 2. Scope Narrowing Analysis

Identifies which names from the global scope are actually used in reachable states and which can be eliminated.

```
FUNCTION analyze_scope(automaton):
    depths := reachable_depths(automaton)
    reachable_ids := keys(depths)

    original_set := union of all state.support for all states
    used_set := union of state.support for states in reachable_ids

    eliminated := original_set \ used_set
    savings := |eliminated|

    RETURN ScopeNarrowingResult(original_set, used_set, eliminated, savings)
```

### 3. Name Usage Computation

Builds a usage map tracking which states and transitions reference each name, with BFS depth bounds.

```
FUNCTION compute_name_usage(automaton):
    depths := reachable_depths(automaton)
    usages := empty map

    FOR EACH state in automaton.states:
        FOR EACH name in state.support:
            usage := usages.get_or_create(name)
            usage.states_using.insert(state.id)
            IF state.id in depths:
                usage.scope_depth := min(usage.scope_depth, depths[state.id])
                usage.last_use_depth := max(usage.last_use_depth, depths[state.id])

    FOR EACH (idx, transition) in automaton.transitions:
        usages[transition.input_pattern].transitions_using.add(idx)
        FOR EACH fresh in transition.fresh_names:
            usages[fresh].transitions_using.add(idx)

    RETURN usages
```

## Complexity Analysis

| Operation              | Time             | Space            |
|------------------------|------------------|------------------|
| `reachable_depths`     | O(V + E)         | O(V)             |
| `compute_name_usage`   | O(V . S + E . F) | O(N)             |
| `analyze_scope`        | O(V . S + E)     | O(V + N)         |
| `narrow_scope`         | O(V . S + E)     | O(V + E)         |
| `construct_nominal`    | O(O + E)         | O(O + E)         |
| `check_freshness`      | O(S)             | O(1)             |

Where V = states, E = transitions, S = max support size, F = max fresh names per transition, N = total distinct names, O = orbits.

## Dependency Diagram

```
  ┌──────────────────────────────────────────────────────────┐
  │                     Pipeline (ctx)                        │
  │                                                          │
  │  all_syntax ──────────────────┐                          │
  │                               ▼                          │
  │                    analyze_from_bundle()                  │
  │                     ┌─────────┴─────────┐                │
  │                     │                   │                │
  │                     ▼                   ▼                │
  │        collect_binders_recursive   scope_violations      │
  │                     │                   │                │
  │                     ▼                   ▼                │
  │              NominalAnalysis      Lint emission          │
  │            ┌────────┴────────┐    (N03, N04)             │
  │            │                 │                           │
  │            ▼                 ▼                           │
  │   scope_violations   narrowing_candidates                │
  └──────────────────────────────────────────────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`analyze_from_bundle(all_syntax)`** -- Scans grammar rules for `Binder` and `BinderCollection` items. Each unique binder name gets its own orbit. Detects scope violations (binder name appears across multiple categories) and narrowing candidates (binder used in only one rule).

### Lint Emission

- **N03 (scope-violation)**: Emitted when a binder name appears in rules across multiple categories without proper re-binding, suggesting the name escapes its intended scope.
- **N04 (scope-narrowing)**: Emitted when a binder name is used in only one rule, suggesting the PNew scope can be tightened to that production.

### Repair Integration

Scope violations and narrowing candidates feed into the repair engine for actionable suggestions (e.g., "restrict binder `x` to category `Proc`").

## Rust Implementation Notes

| Type                    | Role                                                       |
|-------------------------|------------------------------------------------------------|
| `Orbit`                 | Equivalence class under name permutation (id, representative, support_size) |
| `NominalState`          | State with orbit membership, support set, and acceptance   |
| `NominalAutomaton`      | Full automaton: orbits, states, equivariant transitions    |
| `NominalTransition`     | Transition with input pattern and freshness constraints    |
| `NameUsage`             | Per-name tracking: states using, transitions using, depth  |
| `ScopeNarrowingResult`  | Analysis output: original/narrowed/eliminated names        |
| `NominalAnalysis`       | Pipeline result: scope violations, narrowing, orbit count  |

## Worked Example

Consider a rho calculus grammar with `PNew` (name creation) and `PInput` (channel reception):

```
PNew  . Proc ::= "new" Binder(x:Name) "in" Proc(body) ;
PInput. Proc ::= Name(chan) "!" "(" Name(msg) ")" ;
PSend . Proc ::= Name(chan) "?" "(" Binder(y:Name) ")" "." Proc(cont) ;
```

**Step 1: Orbit Construction.**

- Orbit 0: empty support (initial state before any binding)
- Orbit 1: support = {x} (after `new x in ...`)
- Orbit 2: support = {x, y} (after `new x in ... ? (y). ...`)

**Step 2: Transition Construction.**

```
orbit0 ──bind_x[fresh: x]──▶ orbit1 ──bind_y[fresh: y]──▶ orbit2
```

The freshness constraint ensures `x` is genuinely new (not already in scope at orbit 0), and `y` is fresh with respect to `{x}`.

**Step 3: Scope Analysis.**

If an unreachable orbit3 with support {z} exists (from a dead rule), `analyze_scope()` identifies `z` as eliminable, producing:

```
ScopeNarrowing: 3 -> 2 names (1 eliminated)
  original: {x, y, z}
  narrowed: {x, y}
  eliminated: {z}
```

**Step 4: Lint Output.**

If binder `x` appeared in both `Proc` and `Expr` categories:

```
[N03-warning] binder 'x' appears in 2 categories: Expr, Proc
  hint: Consider re-binding 'x' in each category or unifying the scope.
```

## References

1. Bojanczyk, M., Klin, B., & Lasota, S. (2014). "Automata theory in nominal sets." *LMCS*, 10(3).
2. Pitts, A.M. (2013). *Nominal Sets: Names and Symmetry in Computer Science.* Cambridge University Press.
3. Montanari, U. & Pistore, M. (2005). "History-dependent automata." *LNCS 3657*.
4. Tzevelekos, N. (2011). "Fresh-register automata." *ACM SIGPLAN Notices*, 46(1).
5. Gabbay, M.J. & Pitts, A.M. (2002). "A new approach to abstract syntax with variable binding." *Formal Aspects of Computing*, 13(3-5).
