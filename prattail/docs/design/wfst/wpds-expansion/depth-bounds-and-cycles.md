# Depth Bounds (G34) and Cycle Classification (G35)

**Date:** 2026-03-07

## Overview

G34 computes per-category recursion depth bounds via BFS on the G33 call graph.
G35 classifies call graph cycles as Direct or Mutual and detects left-recursion.
Together they feed RT-01 (frame pool pre-sizing) and COMP-08 (cycle-breaking suggestions).

---

## G34: Recursion Depth Bounds

### Data Structure

```rust
pub struct DepthBounds {
    pub min_depth: u32,          // BFS distance from primary (0 = top-level)
    pub max_depth: Option<u32>,  // None = unbounded (recursive or unreachable)
    pub is_recursive: bool,      // In non-trivial SCC or has self-loop
}
```

### Algorithm: `compute_depth_bounds()`

```
compute_depth_bounds(call_graph, primary_cat):
  // Step 1: BFS from primary to compute min_depth
  adj := build adjacency list from call_graph.edges
  visited := { primary_cat -> 0 }
  queue := [(primary_cat, 0)]
  while queue not empty:
    (cat, depth) := dequeue
    for callee in adj[cat]:
      if callee not in visited:
        visited[callee] := depth + 1
        enqueue(callee, depth + 1)

  // Step 2: Identify recursive categories
  recursive_cats := {}
  for scc in call_graph.sccs:
    if |scc| > 1:
      recursive_cats |= scc    // Mutual recursion
    elif |scc| = 1 and has_self_edge(scc[0]):
      recursive_cats |= scc    // Direct recursion

  // Step 3: Assign bounds
  for cat in call_graph.categories:
    min_depth := visited[cat] or u32::MAX (unreachable)
    is_recursive := cat in recursive_cats
    max_depth := if is_recursive or unreachable then None
                 else Some(min_depth)
    result[cat] := DepthBounds { min_depth, max_depth, is_recursive }
```

### RT-01 Integration

The maximum bounded depth determines the trampoline frame pool capacity:

```rust
// In TrampolineConfig:
pub frame_pool_capacity: Option<usize>,

// Computed from G34:
frame_pool_capacity = max(db.max_depth.unwrap() for db in bounded_cats) + 1
```

This enables `Vec::with_capacity(N)` instead of `Vec::new()` for the TLS frame pool,
eliminating reallocations for grammars with known maximum nesting depth.

### Worked Example

Grammar: `Expr -> Num | "(" Type ")" Expr; Type -> "int" | "float"; Decl -> "let" Expr`

```
Category  min_depth  max_depth  is_recursive
--------  ---------  ---------  ------------
Expr      0          None       false (but Expr->Expr via Add is same-cat, not cross-cat)
Type      1          Some(1)    false
Decl      1          None       depends on whether Decl->Expr->Decl cycle exists
```

---

## G35: Cycle Classification

### Data Structures

```rust
pub enum CycleKind {
    Direct,   // |SCC| = 1 with self-edge in call graph
    Mutual,   // |SCC| > 1
}

pub struct CycleInfo {
    pub categories: Vec<String>,
    pub kind: CycleKind,
    pub is_left_recursive: bool,
}
```

### Algorithm: `classify_cycles()`

```
classify_cycles(call_graph, wpds):
  cycles := []
  for scc in call_graph.sccs:
    if |scc| > 1:
      is_lr := any(has_left_recursion(cat, wpds) for cat in scc)
      cycles.push(CycleInfo { scc, Mutual, is_lr })
    elif |scc| = 1 and call_graph has edge scc[0]->scc[0]:
      is_lr := has_left_recursion(scc[0], wpds)
      cycles.push(CycleInfo { scc, Direct, is_lr })
  return cycles
```

### Left-Recursion Detection

```
has_left_recursion(category, wpds):
  entry := StackSymbol::category_entry(category)
  for Replace rule: entry -> (category, rule, 0):
    if has_replace_path_to_entry(wpds, (category, rule, 0), entry):
      return true
  return false

has_replace_path_to_entry(wpds, start, target):
  BFS from start following only Replace rules:
    if current == target: return true
  return false
```

A category is left-recursive if there exists a Replace-only path (no terminal
consumption) from a rule's position-0 back to the category entry symbol. This
corresponds to a grammar where a category can expand to itself at the leftmost
position without consuming input -- a classic left-recursion pattern.

### Worked Example

Grammar: `Expr -> "x" | Decl "in" Expr; Decl -> "let" Expr`

```
Cycle: {Expr, Decl}
Kind: Mutual
Left-recursive: false (Expr->Decl requires consuming "let", Decl->Expr requires "in")
```

Grammar with left recursion: `Expr -> Expr "+" Expr | "x"` (if Expr->Expr were cross-category)

```
Cycle: {Expr}
Kind: Direct
Left-recursive: true (Replace from entry to Expr.Add@0, then Replace back to entry)
```

## Cross-References

- [Call Graph Analysis](call-graph-analysis.md) -- G33 provides SCCs consumed by G34/G35
- [Pipeline Integrations](pipeline-integrations.md) -- RT-01 uses G34 depth bounds
- [COMP-08](../../../diagnostics/wpds/COMP-08-refactoring-suggestion.md) -- Uses G35 cycle data
