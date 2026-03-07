# WPDS Call Graph Analysis (G33)

**Date:** 2026-03-07

## Overview

G33 extracts a directed, weighted call graph from the WPDS's `Push` rules. Each edge
`caller -> callee` represents one or more cross-category references. The call graph
enables recursion detection (via Tarjan SCC), dead-rule witness traces (D15), and
structural analysis for COMP-08 refactoring suggestions.

## Data Structures

### CallEdge

```rust
pub struct CallEdge {
    pub caller_cat: String,   // Source category
    pub callee_cat: String,   // Target category
    pub call_sites: usize,    // Number of distinct Push rules for this edge
    pub total_weight: f64,    // Aggregated weight (proxy: 1.0 per non-zero Push)
}
```

### WpdsCallGraph

```rust
pub struct WpdsCallGraph {
    pub edges: Vec<CallEdge>,
    pub fan_out: HashMap<String, usize>,   // |{callee | caller->callee in E}|
    pub fan_in: HashMap<String, usize>,    // |{caller | caller->callee in E}|
    pub sccs: Vec<Vec<String>>,            // Tarjan SCC decomposition
    pub categories: HashSet<String>,       // All vertices
}
```

## Algorithm: `extract_call_graph()`

### Pseudocode

```
extract_call_graph(wpds: &Wpds<W>) -> WpdsCallGraph:
  edge_map: HashMap<(String,String), (usize, f64)> = {}
  categories: HashSet<String> = {}

  // Phase 1: Collect Push edges
  for rule in wpds.rules:
    if rule is Push { from_gamma, to_gamma_top, weight, .. }:
      caller := from_gamma.category
      callee := to_gamma_top.category
      if caller != callee and both non-empty:
        categories.insert(caller, callee)
        edge_map[(caller, callee)] += (1, if weight.is_zero() then 0.0 else 1.0)

  // Phase 2: Include Replace-only categories
  for rule in wpds.rules:
    categories.insert(rule.from_gamma().category)

  // Phase 3: Build edges, fan-in/fan-out
  edges := edge_map -> Vec<CallEdge>
  fan_out := count distinct callees per caller
  fan_in  := count distinct callers per callee

  // Phase 4: Tarjan SCC
  sccs := tarjan_scc(categories, edges)

  return WpdsCallGraph { edges, fan_out, fan_in, sccs, categories }
```

### Complexity

O(|D|) for Push-rule scan + O(|V| + |E|) for Tarjan = O(|D| + |V| + |E|).

## Tarjan SCC Decomposition

The implementation uses the standard Tarjan algorithm with recursive `strongconnect()`:

```
tarjan_scc(categories, edges):
  adj := build adjacency list from edges
  index_counter := 0
  stack, on_stack, indices, lowlinks := initialized

  for v in 0..n:
    if indices[v] == UNDEFINED:
      strongconnect(v):
        indices[v] = lowlinks[v] = index_counter++
        stack.push(v), on_stack[v] = true
        for w in adj[v]:
          if indices[w] == UNDEFINED:
            strongconnect(w)
            lowlinks[v] = min(lowlinks[v], lowlinks[w])
          elif on_stack[w]:
            lowlinks[v] = min(lowlinks[v], indices[w])
        if lowlinks[v] == indices[v]:
          pop SCC from stack until v
          emit SCC
```

**Properties:**
- O(|V| + |E|) time and space
- Each vertex appears in exactly one SCC
- SCCs are emitted in reverse topological order

## Witness Traces: `shortest_path_witness()`

For D15 diagnostics, BFS backward from the dead category on the reverse call graph:

```
shortest_path_witness(call_graph, reachable, target_cat):
  reverse_adj := { callee -> [callers] for edge in call_graph.edges }

  if target_cat in reachable: return ["{target_cat} (reachable)"]

  BFS from target_cat on reverse_adj:
    for each caller of current:
      if caller in reachable:
        reconstruct forward path: caller -> ... -> target_cat
        return path with annotations

  return ["{target_cat} has no path from any reachable category"]
```

### Path Format

```
Expr (reachable)
  -> Push to Type (missing)
  -> Push to Pattern (missing)
```

Each step represents a hypothetical `Push` rule that would need to exist.

## Worked Example

### Grammar: Mutual Recursion

```
Expr -> "x" | Decl "in" Expr
Decl -> "let" Expr
```

### Call Graph

```
  +------+        +------+
  | Expr |------->| Decl |
  |      |<-------|      |
  +------+        +------+
     |                |
     |  1 call site   |  1 call site
     |  (LetIn@0)     |  (LetDecl@1)
```

### Analysis Results

- **Edges:** `Expr->Decl` (1 site), `Decl->Expr` (1 site)
- **Fan-out:** Expr=1, Decl=1
- **Fan-in:** Expr=1, Decl=1
- **SCCs:** `[{Expr, Decl}]` -- mutual recursion
- **Categories:** {Expr, Decl}

## Cross-References

- [Depth Bounds and Cycles](depth-bounds-and-cycles.md) -- Uses SCC data from G33
- [Pipeline Integrations](pipeline-integrations.md) -- COMP-07 uses call graph for trie confirmation
- [D15 Witness Trace](../../../diagnostics/wpds/D15-wpds-witness-trace.md) -- Per-lint documentation
