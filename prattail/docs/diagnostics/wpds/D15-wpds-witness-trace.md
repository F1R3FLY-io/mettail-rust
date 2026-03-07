# D15: wpds-witness-trace

**Severity:** Info (sub-diagnostic of W13)
**Category:** WPDS

## Description

Appends a witness trace to W13 (wpds-unreachable) diagnostics showing the shortest hypothetical `Push` chain from a reachable category to the dead category. The trace is computed via BFS on the G33 call graph (reverse adjacency) using `shortest_path_witness()`.

A witness trace answers the question: "If this category *were* reachable, what would the call chain look like?" This helps grammar authors identify exactly which cross-category reference is missing.

## Trigger Conditions

D15 fires as a sub-diagnostic whenever W13 fires. It is not emitted independently.

## Algorithm

```
shortest_path_witness(call_graph, reachable, target_cat):
  Build reverse adjacency: callee -> [callers]
  BFS backward from target_cat:
    visited := {target_cat}
    queue := [target_cat]
    while queue not empty:
      current := dequeue
      for caller in reverse_adj[current]:
        if caller in reachable:
          reconstruct path: caller -> ... -> target_cat
          return path
        if caller not in visited:
          visited.add(caller)
          enqueue(caller)
  return ["target_cat has no path from any reachable category"]
```

## Example

### Grammar

```
language! {
    primary: Expr;
    category Expr { Num = INTEGER; UseType = "(" Type ")"; }
    category Type { IntType = "int"; }
    category Pattern { PatVar = IDENT; }  // Orphan: no one calls Pattern
}
```

### Output (appended to W13)

```
warning[W13]: rule `PatVar` in category `Pattern` is unreachable via WPDS
              stack-aware analysis
  witness trace:
    Pattern has no path from any reachable category
```

If a partial path existed (e.g., `Pattern` is called by `Decl` which is itself dead):

```
  witness trace:
    Decl (reachable)
      -> Push to Pattern (missing)
```

## Resolution

See W13 resolution. The witness trace identifies which cross-category `Push` edges are missing.

## Related Lints

- [W13](../wfst/W13-wpds-unreachable.md) -- Parent diagnostic. D15 is always emitted as part of W13.
- [G02](../grammar/G02-unused-category.md) -- Structural unused-category detection.
