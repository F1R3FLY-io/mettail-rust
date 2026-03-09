# TRS Termination Analysis

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `trs-analysis`                         |
| Source file    | `prattail/src/termination.rs` (~910 lines) |
| Pipeline phase | Post-confluence analysis               |
| Lint codes     | T03 (non-terminating SCC), T04 (unknown termination) |

## Rationale

Termination analysis determines whether a term rewriting system (TRS) has only finite reduction sequences. This is a prerequisite for Newman's Lemma: local confluence + termination implies confluence. Without termination guarantees, local confluence does not suffice for global confluence, and the rewriting system may loop forever. In PraTTaIL, grammar-derived rewrite rules model category-level rewrites, and termination analysis detects potential infinite loops in rule application.

## Theoretical Foundations

**Definition (Dependency Pair).** For a TRS with defined symbols `D`, a dependency pair `<f#(args_l), g#(s_1, ..., s_m)>` is extracted from a rule `f(t_1, ..., t_n) -> r` for each subterm `g(s_1, ..., s_m)` of `r` where `g in D`. The `#`-marked symbols distinguish dependency pair heads from ordinary function symbols.

**Definition (Dependency Graph).** The dependency graph has dependency pairs as nodes. An edge from DP_i to DP_j exists iff the target of DP_i is unifiable with the source of DP_j (after variable renaming to avoid capture).

**Theorem (Dependency Pair Criterion, Arts & Giesl 2000).** A TRS is non-terminating iff there exists an infinite chain of dependency pairs. By decomposing the dependency graph into strongly connected components (SCCs), each SCC can be analyzed independently. A non-trivial SCC (size > 1, or size 1 with self-loop) requires a decreasing ordering witness.

**Definition (Subterm Criterion).** An SCC admits a structural decrease if there exists an argument position `i` such that for every pair `<f#(t_1, ..., t_n), g#(s_1, ..., s_m)>` in the SCC: (1) `s_i` is a proper subterm of `t_i` (strict decrease), or (2) `s_i = t_i` (weak decrease) -- with at least one strict decrease in the SCC.

**Definition (First-Order Unification with Occurs Check).** Terms `t_1` and `t_2` are unifiable if there exists a substitution `sigma` such that `sigma(t_1) = sigma(t_2)`. The occurs check prevents infinite terms: `x = f(x)` is not unifiable.

### References

1. Arts, T. & Giesl, J. (2000). "Termination of term rewriting using dependency pairs." *Theoretical Computer Science*, 236(1-2).
2. Hirokawa, N. & Middeldorp, A. (2005). "Automating the dependency pair method." *Information and Computation*, 199(1-2).
3. Giesl, J. et al. (2006). "Mechanizing and improving dependency pairs." *Journal of Automated Reasoning*, 37(3).

## Algorithm Pseudocode

### 1. Extract Dependency Pairs

```
FUNCTION extract_dependency_pairs(rules):
    defined_symbols := { root(lhs) | (lhs, rhs) in rules, lhs is App }
    pairs := []

    FOR EACH (rule_index, (lhs, rhs)) in rules:
        IF lhs is not App THEN CONTINUE
        source_marked := lhs with root symbol suffixed by "#"

        rhs_subterms := collect_defined_subterms(rhs, defined_symbols)
        FOR EACH subterm in rhs_subterms:
            target_marked := subterm with root symbol suffixed by "#"
            pairs.add(DependencyPair(source_marked, target_marked, rule_index))

    RETURN pairs
```

### 2. Build Dependency Graph (Tarjan SCC)

```
FUNCTION build_dependency_graph(pairs):
    n := |pairs|
    adj := [[] for i in 0..n]

    FOR i := 0 TO n-1:
        FOR j := 0 TO n-1:
            renamed_source := rename_variables(pairs[j].source, "_R")
            IF unify(pairs[i].target, renamed_source) is Some:
                adj[i].add(j)

    sccs := tarjan_scc(n, adj)

    RETURN sccs with self-loop detection
```

### 3. Check Termination via Subterm Criterion

```
FUNCTION check_termination(rules):
    IF rules is empty THEN RETURN Terminating

    pairs := extract_dependency_pairs(rules)
    IF pairs is empty THEN RETURN Terminating

    sccs := build_dependency_graph(pairs)
    problematic := []

    FOR EACH (scc_idx, scc) in sccs:
        IF |scc| == 1 AND NOT scc.has_self_loop THEN CONTINUE

        IF NOT has_structural_decrease(scc, pairs):
            problematic.add(scc_idx)

    IF problematic is empty:
        RETURN Terminating
    ELSE:
        RETURN PotentiallyNonTerminating(problematic)
```

## Complexity Analysis

| Operation                    | Time             | Space            |
|------------------------------|------------------|------------------|
| `extract_dependency_pairs`   | O(R . |rhs|)     | O(P)             |
| `build_dependency_graph`     | O(P^2 . U)       | O(P^2)           |
| `tarjan_scc`                 | O(P + E)         | O(P)             |
| `check_termination`          | O(P^2 . U + S)   | O(P^2)           |
| `has_structural_decrease`    | O(S . A)         | O(1)             |
| `unify`                      | O(|t_1| . |t_2|) | O(V)             |
| `is_proper_subterm`          | O(|t|)           | O(d)             |

Where R = rules, P = dependency pairs, U = unification cost, E = edges in DP graph, S = SCC pair count, A = min arity, V = variables, |t| = term size, d = term depth.

## Dependency Pair Framework Diagram

```
  ┌──────────────────────────────────────────────────────────────┐
  │                  Termination Analysis Pipeline                │
  │                                                              │
  │  RewriteRule set                                             │
  │       │                                                      │
  │       ▼                                                      │
  │  extract_dependency_pairs()                                  │
  │       │                                                      │
  │       ▼                                                      │
  │  Vec<DependencyPair>                                         │
  │  ⟨f#(s(x)), f#(x)⟩, ⟨g#(x), f#(x)⟩, ...                  │
  │       │                                                      │
  │       ▼                                                      │
  │  build_dependency_graph()                                    │
  │       │                                                      │
  │       ├── unify(target_i, source_j) for all i,j              │
  │       ├── rename_variables() to avoid capture                │
  │       │                                                      │
  │       ▼                                                      │
  │  Tarjan SCC decomposition                                    │
  │       │                                                      │
  │       ├── Singleton SCCs (no self-loop) → trivially OK       │
  │       ├── Non-trivial SCCs → has_structural_decrease()       │
  │       │                                                      │
  │       ▼                                                      │
  │  TerminationResult                                           │
  │  (Terminating | PotentiallyNonTerminating | Unknown)         │
  └──────────────────────────────────────────────────────────────┘
```

## SCC Classification

```
  Case 1: Singleton, no self-loop     Case 2: Singleton with self-loop

    ┌───┐                                ┌───┐
    │DP0│  (no cycle → terminating)      │DP0│──┐  (self-loop → check
    └───┘                                └───┘  │   structural decrease)
                                           ▲    │
                                           └────┘

  Case 3: Multi-node SCC (mutual recursion)

    ┌───┐         ┌───┐
    │DP0│ ──────▶ │DP1│
    └───┘         └───┘
      ▲             │
      └─────────────┘    (cycle → check structural decrease)
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`analyze_from_bundle(all_syntax)`** -- Converts grammar syntax into rewrite rules via `confluence::syntax_to_rewrite_rules`, then runs `check_termination`. Returns `None` if no rewrite rules are generated (trivially terminating).

### Lint Emission

- **T03 (non-terminating SCC)**: Emitted when a non-trivial SCC has no structural decrease -- the TRS may loop forever through this cycle of dependency pairs.
- **T04 (unknown termination)**: Emitted when the subterm criterion is insufficient to determine termination, suggesting that a more powerful ordering method (e.g., polynomial interpretation) would be needed.

## Rust Implementation Notes

| Type                | Role                                                     |
|---------------------|----------------------------------------------------------|
| `DependencyPair`    | A pair `<source, target>` with rule_index provenance     |
| `DependencyScc`     | SCC: pair_indices + has_self_loop flag                   |
| `TerminationResult` | Enum: Terminating, PotentiallyNonTerminating, Unknown    |
| `Term`              | Re-used from confluence module: Var(name), App(symbol, args) |
| `RewriteRule`       | Re-used from confluence module: lhs -> rhs               |

## Worked Example

Consider the TRS:
```
f(s(x)) -> f(x)        (Rule 0: structural recursion)
f(x) -> f(x)           (Rule 1: identity loop)
```

**Step 1: Extract dependency pairs.**

Defined symbols: `{f}`.
- Rule 0: LHS `f(s(x))`, RHS `f(x)`. Subterm `f(x)` has root `f in D`.
  DP0: `<f#(s(x)), f#(x)>`
- Rule 1: LHS `f(x)`, RHS `f(x)`. Subterm `f(x)` has root `f in D`.
  DP1: `<f#(x), f#(x)>`

**Step 2: Build dependency graph.**

- Edge DP0 -> DP0: unify(`f#(x)`, `f#(s(x_R))`). `x = s(x_R)`. Success. Edge added.
- Edge DP0 -> DP1: unify(`f#(x)`, `f#(x_R)`). `x = x_R`. Success. Edge added.
- Edge DP1 -> DP0: unify(`f#(x)`, `f#(s(x_R))`). `x = s(x_R)`. Success. Edge added.
- Edge DP1 -> DP1: unify(`f#(x)`, `f#(x_R)`). `x = x_R`. Success. Self-loop.

Tarjan SCC: one SCC `{DP0, DP1}`.

**Step 3: Check structural decrease.**

Position 0:
- DP0: source_arg = `s(x)`, target_arg = `x`. `x` is a proper subterm of `s(x)` -- strict decrease.
- DP1: source_arg = `x`, target_arg = `x`. Equal -- weak decrease.

All weakly decrease, at least one strict. Position 0 provides a valid witness.

**Result:** `Terminating` (despite Rule 1 being an identity loop, the SCC as a whole decreases because DP0 provides the strict decrease).

If Rule 0 were removed (only Rule 1 remains), then the SCC `{DP1}` with self-loop has no strict decrease at position 0 (only equality), yielding `PotentiallyNonTerminating`.

## References

1. Arts, T. & Giesl, J. (2000). "Termination of term rewriting using dependency pairs." *TCS*, 236(1-2).
2. Hirokawa, N. & Middeldorp, A. (2005). "Automating the dependency pair method." *Inf. Comput.*, 199(1-2).
3. Giesl, J. et al. (2006). "Mechanizing and improving dependency pairs." *JAR*, 37(3).
4. Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms." *SIAM J. Computing*, 1(2).
5. Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That.* Cambridge University Press.
