# ART01 -- Recursive Field Detection for Hash-Consing

## Overview

The hash-consing analysis module inspects a language definition to determine
which categories contain recursive fields (references to themselves or other
language categories) and would therefore benefit from hash-consing. Categories
with recursive structure exhibit subterm sharing -- for example, `PPar(a, a)`
shares both children -- and hash-consing eliminates redundant allocations by
interning structurally identical subterms.

This module is the **compile-time analysis** component of ART01. It feeds
into the ART01 cost-benefit gate and connects to the **runtime** interning
infrastructure in `runtime/src/hash_consing.rs`.

**Source:** `macros/src/gen/term_ops/hash_consing_analysis.rs`

## Algorithm Description

### Phase 1: Per-Category Recursive Field Scan

For each category in the language definition, the analysis examines every
grammar rule and collects references to other language categories:

```
for each category C:
    for each rule R in C:
        refs(R) = { names of grammar items whose type is a language category }
        if refs(R) is non-empty:
            recursive_variant_count += 1
            recursive_refs = recursive_refs UNION refs(R)
```

The reference collection covers three grammar item kinds:

| Item Kind | Example | Extracted Reference |
|-----------|---------|-------------------|
| `NonTerminal(X)` | `PSend(Name, Proc)` | `Name`, `Proc` |
| `Collection { element_type: X }` | `PPar(HashBag<Proc>)` | `Proc` |
| `Binder { category: X }` | `PInput(^Name.Proc)` | `Name` |

For new-syntax rules using `term_context`, the analysis traverses
`TypeExpr` trees (including `Arrow`, `MultiBinder`, and `Collection`
wrappers) to find base types that match language category names.

### Phase 2: Mutual Recursion Detection (SCC via Kosaraju)

The per-category reference sets form a directed graph: an edge `C --> D`
exists when category `C` has a rule referencing category `D`. The analysis
finds strongly connected components (SCCs) using Kosaraju's two-pass
algorithm:

```
Pass 1 (forward DFS):  Compute finish ordering
Pass 2 (reverse DFS):  Traverse reverse graph in reverse finish order
                        Each DFS tree is one SCC
```

Only SCCs of size > 1, or single-node SCCs with a self-edge, are reported
as mutual recursion groups. These groups are the primary candidates for
hash-consing because terms in mutually-recursive categories frequently
share subterms across category boundaries.

### Phase 3: Recommendation

The analysis recommends hash-consing if any category has at least one
recursive variant (`recursive_variant_count > 0`).

## Key Types

```
HashConsingReport
  +-- categories: Vec<CategoryRecursion>
  |     +-- name: String
  |     +-- recursive_variant_count: usize
  |     +-- total_variant_count: usize
  |     +-- recursive_refs: HashSet<String>
  +-- mutual_recursion_groups: Vec<Vec<String>>
  +-- recommended: bool
```

## Example Analysis

For the rho-calculus language:

```
Proc  -->  Proc (self: PSend, PInput, PPar, ...)
Proc  -->  Name (PSend, PInput, PContr, PMatch)
Name  -->  Proc (NQuote)
Name  -->  Name (self: none in typical grammar)
Int   -->  (no category refs)
Bool  -->  (no category refs)
```

Reference graph:
```
  Proc ----> Name
    ^   \      |
    |    \     |
    |     v    v
    +---- Proc (self-loop)
          Name ----> Proc
```

SCCs: `{Proc, Name}` (mutual recursion), `{Int}` (singleton, no self-ref),
`{Bool}` (singleton, no self-ref).

Report:
```
CategoryRecursion { name: "Proc", recursive_variant_count: 5, total: 12,
                    recursive_refs: {"Proc", "Name"} }
CategoryRecursion { name: "Name", recursive_variant_count: 1, total: 3,
                    recursive_refs: {"Proc"} }
CategoryRecursion { name: "Int",  recursive_variant_count: 0, total: 3,
                    recursive_refs: {} }
mutual_recursion_groups: [["Name", "Proc"]]
recommended: true
```

## Generated Code Patterns

Currently, this module is **analysis-only**: it does not emit code directly.
The `HashConsingReport` is consumed by:

1. The ART01 cost-benefit gate in `prattail/src/cost_benefit.rs`, which
   decides whether to enable hash-consing for a given language.
2. Diagnostic emission (when enabled), reporting which categories would
   benefit from hash-consing and which mutual recursion groups exist.

**Future:** When the ART01 gate is fully activated, the analysis will drive
code generation that:
- Wraps recursive fields in `Rc<T>` instead of `Box<T>`
- Emits `define_intern_table!` invocations for each recommended category
- Inserts `intern()` calls at term construction sites

## Connection to Runtime

The runtime half of ART01 lives in `runtime/src/hash_consing.rs` and provides:

- `InternTable<T>` -- thread-local hash-keyed interning table
- `bump_intern_epoch()` -- epoch advancement for garbage collection
- `define_intern_table!` -- macro for declaring per-type intern tables

See [runtime/docs/hash-consing.md](../../../runtime/docs/hash-consing.md) for
details on the runtime interning infrastructure.

## Integration with Codegen Pipeline

```
macros/src/gen/term_ops/hash_consing_analysis.rs
           |
           v
    analyze_hash_consing(language) --> HashConsingReport
           |
           +---> cost_benefit.rs (ART01 gate decision)
           +---> diagnostic emission (compile-time notes)
           +---> [future] code generation (Rc wrapping, intern calls)
```

## Source References

- Analysis module: `macros/src/gen/term_ops/hash_consing_analysis.rs`
- Runtime interning: `runtime/src/hash_consing.rs`
- Cost-benefit gate: `prattail/src/cost_benefit.rs`
- SCC algorithm: Kosaraju's algorithm (lines 174--215 of the source)
