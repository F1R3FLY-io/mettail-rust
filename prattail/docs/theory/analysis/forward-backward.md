# Forward-Backward Analysis

| Property       | Value                                    |
|----------------|------------------------------------------|
| Feature gate   | `wfst-log`                               |
| Source file    | `prattail/src/forward_backward.rs` (~479 lines) |
| Pipeline phase | Post-lattice construction                |
| Lint codes     | (indirect, via hot-path diagnostics)     |

## Rationale

The forward-backward algorithm is the foundational algorithm for computing marginal weights in lattice structures. Given a topologically sorted DAG with semiring-weighted edges, the forward pass computes the total weight of all paths from the start to each node, and the backward pass computes the total weight of all paths from each node to the final node. Together, these scores enable hot-path identification (which edges carry the most probability mass), critical-path extraction (the single best path), and edge occupancy computation (fraction of total weight flowing through each edge). In PraTTaIL, this is used for WFST lattice analysis, identifying the most probable parse paths and guiding optimization decisions.

## Theoretical Foundations

**Definition (Forward Scores).** Given a DAG with `n` nodes (topologically ordered, node 0 = start) and edge weights from a semiring `(S, oplus, otimes, 0, 1)`:

    alpha[0] = 1 (one)
    alpha[j] = bigoplus_{(i,j) in E} alpha[i] otimes w(i,j)

`alpha[j]` is the total weight of all paths from node 0 to node `j`.

**Definition (Backward Scores).** Given a final node `f`:

    beta[f] = 1 (one)
    beta[i] = bigoplus_{(i,j) in E} w(i,j) otimes beta[j]

`beta[i]` is the total weight of all paths from node `i` to node `f`.

**Theorem (Forward-Backward Consistency).** For a correctly constructed DAG: `alpha[f] = beta[0]`. This is the total (partition function) weight of the DAG.

**Definition (Edge Expected Weight).** The expected weight of edge `(u, v)` is:

    gamma(u, v) = alpha[u] otimes w(u, v) otimes beta[v]

For `TropicalWeight`: cost of the best complete path through this edge.
For `LogWeight`: total log-probability flowing through this edge.

**Definition (Edge Occupancy).** The fraction of total weight flowing through edge `(u, v)`:

    occ(u, v) = gamma(u, v) / alpha[f]

For semirings without division (e.g., TropicalWeight), occupancy is approximated as a binary indicator: 1.0 if `gamma(u, v) = alpha[f]`, 0.0 otherwise.

**Definition (Critical Path).** The critical path is the sequence of edges from node 0 to node `f` where each edge's expected weight equals the total weight. For `TropicalWeight`, this is the minimum-cost path (Viterbi path).

### References

1. Mohri, M. (2002). "Semiring frameworks and algorithms for shortest-distance problems." *Journal of Automata, Languages and Combinatorics*, 7(3).
2. Rabiner, L.R. (1989). "A tutorial on hidden Markov models and selected applications in speech recognition." *Proceedings of the IEEE*, 77(2).
3. Eisner, J. (2002). "Parameter estimation for probabilistic finite-state transducers." *ACL*.

## Algorithm Pseudocode

### 1. Forward Pass

```
FUNCTION forward_scores(edges, num_nodes):
    alpha := [W::zero() for i in 0..num_nodes]
    alpha[0] := W::one()

    FOR node := 0 TO num_nodes - 1:
        IF alpha[node].is_zero() THEN CONTINUE
        FOR EACH (target, weight) in edges[node]:
            contribution := alpha[node] OTIMES weight
            alpha[target] := alpha[target] OPLUS contribution

    RETURN alpha
```

### 2. Backward Pass

```
FUNCTION backward_scores(edges, num_nodes, final_node):
    beta := [W::zero() for i in 0..num_nodes]
    beta[final_node] := W::one()

    FOR node := num_nodes - 1 DOWNTO 0:
        FOR EACH (target, weight) in edges[node]:
            contribution := weight OTIMES beta[target]
            beta[node] := beta[node] OPLUS contribution

    RETURN beta
```

### 3. Hot-Path Analysis

```
FUNCTION hot_path_analysis(edges, num_nodes, final_node):
    alpha := forward_scores(edges, num_nodes)
    beta := backward_scores(edges, num_nodes, final_node)
    total := alpha[final_node]

    ranked_edges := []
    FOR EACH (from, adj) in edges:
        FOR EACH (to, weight) in adj:
            expected := alpha[from] OTIMES weight OTIMES beta[to]
            ranked_edges.add(RankedEdge(from, to, weight, expected))

    SORT ranked_edges BY expected_weight ASCENDING
    RETURN HotPathReport(ranked_edges, total, num_nodes, |ranked_edges|)
```

## Complexity Analysis

| Operation            | Time        | Space        |
|----------------------|-------------|--------------|
| `forward_scores`     | O(V + E)    | O(V)         |
| `backward_scores`    | O(V + E)    | O(V)         |
| `hot_path_analysis`  | O(E log E)  | O(V + E)     |
| `critical_path`      | O(V + E)    | O(V)         |
| `edge_occupancy`     | O(V + E)    | O(E)         |
| `total_weight`       | O(1)        | O(1)         |

Where V = nodes, E = edges.

## Forward-Backward Propagation Diagram

```
  Forward Pass (alpha):
  ═══════════════════

  ┌───┐  w₁   ┌───┐  w₃   ┌───┐
  │ 0 │──────▶│ 1 │──────▶│ 3 │
  │ 1 │       │α₁ │       │α₃ │  alpha[3] = min(alpha[1]⊗w₃, alpha[2]⊗w₄)
  └─┬─┘       └───┘       └───┘
    │  w₂   ┌───┐  w₄      ▲
    └──────▶│ 2 │──────────┘
             │α₂ │
             └───┘

  Backward Pass (beta):
  ═════════════════════

  ┌───┐  w₁   ┌───┐  w₃   ┌───┐
  │ 0 │◀──────│ 1 │◀──────│ 3 │
  │β₀ │       │β₁ │       │ 1 │
  └───┘       └───┘       └─┬─┘
    ▲    w₂   ┌───┐  w₄    │
    └─────────│ 2 │◀───────┘
              │β₂ │
              └───┘

  Expected Weight (gamma):
  ═══════════════════════

  gamma(0,1) = alpha[0] ⊗ w₁ ⊗ beta[1]
  gamma(0,2) = alpha[0] ⊗ w₂ ⊗ beta[2]
  gamma(1,3) = alpha[1] ⊗ w₃ ⊗ beta[3]
  gamma(2,3) = alpha[2] ⊗ w₄ ⊗ beta[3]
```

## Semiring Interpretation Table

```
  ┌────────────────┬─────────────────┬──────────────────────────┐
  │ Semiring       │ forward_scores  │ hot_path_analysis        │
  ├────────────────┼─────────────────┼──────────────────────────┤
  │ TropicalWeight │ Viterbi         │ Cheapest path through    │
  │ (min, +, inf, 0)│ (min-cost path)│ each edge (lower = hot)  │
  ├────────────────┼─────────────────┼──────────────────────────┤
  │ LogWeight      │ Total log-prob  │ Probability mass through │
  │ (-log(e^+), +) │ (log-sum-exp)  │ each edge (lower = hot)  │
  ├────────────────┼─────────────────┼──────────────────────────┤
  │ CountingWeight │ Path count      │ Number of paths through  │
  │ (+, *, 0, 1)   │ to each node   │ each edge                │
  └────────────────┴─────────────────┴──────────────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

The forward-backward module does not have a direct `analyze_from_bundle` pipeline bridge. Instead, it is used indirectly by other modules:

- **WFST lattice analysis** uses `forward_scores` and `backward_scores` to compute Viterbi paths and total probabilities over token lattices.
- **Hot-path optimization** (Phase 5B.5) uses `hot_path_analysis` to identify the most critical edges for code generation prioritization.
- **Edge occupancy** feeds into diagnostic enrichment: edges with high occupancy are highlighted for performance attention.

### Feature Gating

The full `LogWeight` tests require the `wfst-log` feature flag. The core algorithms (`forward_scores`, `backward_scores`, `hot_path_analysis`, `critical_path`, `edge_occupancy`) work with any `Semiring + PartialOrd` type.

## Rust Implementation Notes

| Type               | Role                                                     |
|--------------------|----------------------------------------------------------|
| `RankedEdge<W>`    | Edge with expected weight: from, to, weight, expected_weight |
| `HotPathReport<W>` | Analysis result: ranked_edges, total, num_nodes, num_edges |

## Worked Example

Diamond DAG with TropicalWeight:
```
Node 0 --1.0--> Node 1 --2.0--> Node 3
Node 0 --3.0--> Node 2 --1.0--> Node 3
```

**Step 1: Forward pass.**

| Node | alpha (min-cost from 0) |
|------|------------------------|
| 0    | 0.0 (one)              |
| 1    | 0.0 + 1.0 = 1.0       |
| 2    | 0.0 + 3.0 = 3.0       |
| 3    | min(1.0+2.0, 3.0+1.0) = min(3.0, 4.0) = 3.0 |

**Step 2: Backward pass.**

| Node | beta (min-cost to 3) |
|------|---------------------|
| 3    | 0.0 (one)           |
| 2    | 1.0 + 0.0 = 1.0    |
| 1    | 2.0 + 0.0 = 2.0    |
| 0    | min(1.0+2.0, 3.0+1.0) = 3.0 |

Consistency check: `alpha[3] = beta[0] = 3.0`.

**Step 3: Hot-path analysis.**

| Edge   | gamma = alpha[u] + w + beta[v] | On critical path? |
|--------|-------------------------------|-------------------|
| 0 -> 1 | 0.0 + 1.0 + 2.0 = 3.0       | Yes (= total)     |
| 0 -> 2 | 0.0 + 3.0 + 1.0 = 4.0       | No                |
| 1 -> 3 | 1.0 + 2.0 + 0.0 = 3.0       | Yes (= total)     |
| 2 -> 3 | 3.0 + 1.0 + 0.0 = 4.0       | No                |

**Step 4: Critical path extraction.**

Path: `0 -> 1 -> 3` with total cost 3.0. Edges 0->1 and 1->3 have occupancy 1.0.

## References

1. Mohri, M. (2002). "Semiring frameworks and algorithms for shortest-distance problems." *JALC*, 7(3).
2. Rabiner, L.R. (1989). "A tutorial on hidden Markov models." *Proc. IEEE*, 77(2).
3. Eisner, J. (2002). "Parameter estimation for probabilistic finite-state transducers." *ACL*.
4. Allauzen, C. & Mohri, M. (2003). "Generalized optimization algorithm for speech recognition transducers." *ICASSP*.
5. Mohri, M., Pereira, F. & Riley, M. (2002). "Weighted finite-state transducers in speech recognition." *Computer Speech & Language*, 16(1).
