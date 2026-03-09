# Algebraic Program Analysis -- Tarjan Path Expressions

| Property | Value |
|----------|-------|
| **Feature gate** | always-on |
| **Source file** | `prattail/src/algebraic.rs` (~2056 lines) |
| **Pipeline phase** | WPDS summary computation |
| **Lint codes** | S06 (`algebraic-summary`) |

## 1. Rationale

Many analyses over PraTTaIL's WPDS reduce to computing the "summary" of all paths
between two program points. Naive fixpoint iteration (Kleene iteration) may require
many passes to converge. Algebraic program analysis decomposes the CFG into a
**path expression** -- a regular expression over semiring weights -- and evaluates
it in a single pass over the expression tree. For DAG-shaped CFGs this is linear;
for cyclic CFGs, Tarjan's SCC decomposition ensures each cycle is handled exactly
once via the Kleene star.

## 2. Theoretical Foundations

### 2.1. Path Expressions

**Definition (Path Expression).** A path expression over a semiring
`(S, oplus, otimes, 0, 1)` is defined inductively:

```
PE ::= Atom(w)            -- weight w in S
     | Seq(PE, PE)         -- sequential composition (otimes)
     | Alt(PE, PE)         -- alternative paths (oplus)
     | Star(PE)            -- loop closure (Kleene star)
     | Zero                -- no path (additive identity 0)
     | One                 -- empty path (multiplicative identity 1)
```

**Definition (Evaluation).** `evaluate(pe, W)` maps a path expression to a
semiring element:

```
evaluate(Atom(w)) = w
evaluate(Seq(a, b)) = evaluate(a) otimes evaluate(b)
evaluate(Alt(a, b)) = evaluate(a) oplus evaluate(b)
evaluate(Star(a)) = star(evaluate(a))
evaluate(Zero) = 0
evaluate(One) = 1
```

### 2.2. Semiring Instantiations

| Semiring | `oplus` | `otimes` | `0` | `1` | Analysis |
|----------|---------|----------|-----|-----|----------|
| `BooleanWeight` | OR | AND | false | true | Reachability |
| `TropicalWeight` | min | + | +inf | 0.0 | Shortest path |
| `CountingWeight` | + | * | 0 | 1 | Path counting |

### 2.3. Tarjan Decomposition

**Theorem (Tarjan 1981).** Any CFG can be decomposed into strongly connected
components (SCCs) in O(V + E) time. Within each SCC, the set of all paths
forms a regular language whose closure is captured by the Kleene star.

The algorithm processes SCCs in reverse topological order (sinks first), so that
when processing SCC `C`, all successor SCCs already have computed path
expressions.

### 2.4. Interprocedural Extension

For interprocedural analysis, each procedure has its own CFG. Call edges connect
caller nodes to callee entries; return edges connect callee exits to return
sites. The **procedure summary** for callee `f` is the path expression from
`f.entry` to `f.exit`. Interprocedural analysis composes these summaries across
call boundaries.

## 3. Algorithm Pseudocode

### 3.1. CFG Construction from WPDS

```
function build_cfg(wpds: Wpds<W>) -> ControlFlowGraph<W>:
    symbol_to_node := map stack symbols to node indices
    exit_node := |symbols|   // synthetic exit

    for rule in wpds.rules:
        match rule:
            Replace(gamma -> gamma', w):
                add edge gamma -> gamma' with weight w
            Pop(gamma, w):
                add edge gamma -> exit_node with weight w
            Push(gamma -> gamma_bottom gamma_top, w):
                add edge gamma -> gamma_top with weight w      // call
                add edge gamma_top -> gamma_bottom with weight 1  // return approx

    entry := symbol_to_node[wpds.initial_symbol]
    return CFG(nodes, edges, entry, exit_node)
```

### 3.2. Path Expression via Tarjan Decomposition

```
function path_expression(cfg: CFG<W>) -> PathExpr<W>:
    if cfg.entry == cfg.exit: return One
    sccs := tarjan_decompose(cfg)   // reverse topological order
    edge_map := combine parallel edges with oplus

    // node_expr[v] = path expression from v to exit
    node_expr[exit] := One

    for each scc in sccs (sinks first):
        if scc is singleton {v}:
            // Check for self-loop
            if (v, v) in edge_map:
                self_star := Star(Atom(edge_map[(v, v)]))
            else:
                self_star := One
            // Combine outgoing cross-SCC edges
            combined := Zero
            for (v, to, w) in outgoing edges of v where to != v:
                if node_expr[to] exists:
                    combined := Alt(combined, Seq(Atom(w), node_expr[to]))
            node_expr[v] := Seq(self_star, combined)
        else:
            // Multi-node SCC: compute internal loop body
            for each node v in scc:
                // Compute the loop body for this SCC
                internal_weight := sum of internal edge weights
                loop_star := Star(Atom(internal_weight))
                // Combine with outgoing edges
                ...

    return node_expr[entry]
```

### 3.3. All-Pairs Analysis via Matrix Star

```
function all_pairs_analysis(cfg: CFG<W>) -> Matrix<W>:
    n := |cfg.nodes|
    A := n x n matrix with A[i][j] = edge weight (i,j) or Zero
    return matrix_star(A)
    // Result[i][j] = path expression weight from node i to node j
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `build_cfg` | O(R) | O(S + R) |
| `tarjan_decompose` | O(V + E) | O(V) |
| `path_expression` | O(V + E) | O(V) |
| `evaluate` | O(|PE|) | O(depth(PE)) |
| `analyze` (single-source) | O(V + E + |PE|) | O(V) |
| `all_pairs_analysis` | O(V^3) | O(V^2) |
| `interprocedural_analyze` | O(sum V_p + sum E_p) | O(sum V_p) |

Where: R = WPDS rules, S = stack symbols, V = CFG nodes, E = CFG edges,
PE = path expression, V_p/E_p = per-procedure CFG sizes.

## 5. Unicode Diagrams

### 5.1. Architecture

```
    WPDS ───> build_cfg() ───> ControlFlowGraph<W>
                                      │
                ┌─────────────────────┼─────────────────────┐
                │                     │                     │
                v                     v                     v
      tarjan_decompose()     path_expression()     all_pairs_analysis()
                │                     │                     │
                │                     v                     │
                │              evaluate() ──> W             │
                │                                           │
                └──────────── analyze() ──> W               │
                                                            │
                              matrix_star() <───────────────┘
```

### 5.2. SCC-Based Decomposition Example

```
    CFG:    entry ──> A ──> B ──> exit
                      ^    │
                      └────┘   (cycle A <-> B)

    SCCs (reverse topological):
      SCC 0: {exit}       (sink)
      SCC 1: {A, B}       (cycle)
      SCC 2: {entry}      (source)

    Path expression:
      node_expr[exit] = One
      node_expr[A] = Star(w_AB otimes w_BA) otimes w_B_exit
      node_expr[entry] = w_entry_A otimes node_expr[A]
```

### 5.3. Path Expression Tree

```
    For path: entry --(3.0)--> A --(2.0)--> B --(1.0)--> exit

                       Seq
                      /   \
                 Atom(3.0)  Seq
                           /   \
                     Atom(2.0)  Atom(1.0)

    evaluate(Tropical): 3.0 + 2.0 + 1.0 = 6.0
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `build_cfg(wpds)` -- Extracts a CFG from a WPDS.
- `tarjan_decompose(cfg)` -- SCC decomposition (iterative, stack-safe).
- `path_expression(cfg)` -- Constructs the path expression.
- `evaluate(path_expr)` -- Evaluates over any `StarSemiring`.
- `analyze(cfg)` -- End-to-end: build path expression + evaluate.
- `all_pairs_analysis(cfg)` -- Floyd-Warshall via `matrix_star`.
- `interprocedural_analyze(ipcfg)` -- Per-procedure summaries composed across calls.

### 6.2. Lint Emission

- **S06** (`algebraic-summary`): Reports the computed algebraic summary weight
  for each procedure. Severity: Info.

### 6.3. Repair Integration

No direct repairs. The algebraic module provides analysis results consumed by
other modules (CEGAR, Newton, cost-benefit framework).

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `CfgNode` | Newtype `usize` for CFG node indices |
| `CfgEdge<W>` | Weighted directed edge (from, to, weight) |
| `ControlFlowGraph<W>` | CFG with nodes, edges, entry, exit |
| `PathExpr<W>` | Recursive enum: Atom, Seq, Alt, Star, Zero, One |
| `InterproceduralCfg<W>` | Collection of per-procedure CFGs with call/return edges |

The `PathExpr` type uses **smart constructors** (`seq`, `alt`, `star`) that
simplify expressions at construction time:
- `Seq(Zero, _) = Zero` and `Seq(One, x) = x`
- `Alt(Zero, x) = x`
- `Star(Zero) = One` and `Star(One) = One`

The Tarjan decomposition uses an **iterative** algorithm with an explicit work
stack to avoid stack overflow on large CFGs.

## 8. Worked Example

**WPDS Rules:**
```
Start -> A  (weight 1.0)
A -> B      (weight 2.0)
B -> A      (weight 0.5)   // loop
B -> End    (weight 3.0)
```

**CFG Construction:**
```
Nodes: Start(0), A(1), B(2), End(3), exit(4)
Edges: 0->1 (1.0), 1->2 (2.0), 2->1 (0.5), 2->4 (3.0)
```

**Tarjan Decomposition (reverse topological):**
```
SCC 0: {exit}   (sink)
SCC 1: {A, B}   (cycle: A->B->A)
SCC 2: {Start}  (source)
```

**Path Expression:**
```
loop_body = Seq(Atom(2.0), Atom(0.5))   // A->B->A = 2.5 (tropical +)
loop_star = Star(loop_body)              // star(2.5) = 0.0 (tropical)
exit_path = Seq(Atom(2.0), Atom(3.0))   // A->B->exit = 5.0
full = Seq(Atom(1.0), Seq(loop_star, exit_path))
```

**Evaluation (Tropical):**
```
loop_body = 2.0 + 0.5 = 2.5
star(2.5) = 0.0  (tropical star: value >= 0 -> 0.0)
exit_path = 2.0 + 3.0 = 5.0
full = 1.0 + 0.0 + 5.0 = 6.0
```

Result: minimum-cost path from Start to exit = 6.0 (tropical weight).

## 9. References

1. Kincaid, Z., Cyphert, J., Breck, J. & Reps, T. (2019).
   "Algebraic Program Analysis."
   *Proc. 31st International Conference on Computer Aided Verification (CAV)*,
   LNCS 11561, Springer, pp. 46--83.

2. Tarjan, R.E. (1981).
   "A Unified Approach to Path Problems."
   *Journal of the ACM*, 28(3), pp. 577--593.

3. Reps, T., Schwoon, S., Jha, S. & Melski, D. (2005).
   "Weighted Pushdown Systems and Their Application to Interprocedural
   Dataflow Analysis."
   *Science of Computer Programming*, 58(1--2), pp. 206--263.

4. Tarjan, R.E. (1972).
   "Depth-First Search and Linear Graph Algorithms."
   *SIAM Journal on Computing*, 1(2), pp. 146--160.

5. Cyphert, J., Breck, J., Kincaid, Z. & Reps, T. (2019).
   "Refinement of Path Expressions for Static Analysis."
   *Proc. ACM on Programming Languages (POPL)*, 3, Article 45.
