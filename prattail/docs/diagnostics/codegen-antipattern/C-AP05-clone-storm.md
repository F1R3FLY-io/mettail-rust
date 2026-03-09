# C-AP05: clone-storm

**Severity:** Warning
**Category:** codegen-antipattern
**Feature Gate:** None (always enabled)

## Description

Detects constructors that contain collection fields (`Vec<T>`, `HashBag<T>`,
`HashSet<T>`) where the generated Ascent congruence rules will clone the entire
collection on every rule firing. This is a significant performance antipattern
for large ASTs because each congruence iteration produces a deep copy of every
collection field in every matching constructor.

The detector scans all grammar rules (both old-style `GrammarItem::Collection`
fields and new-style `term_context` parameter expressions) for collection type
annotations. When a constructor has a collection-typed field, the generated
congruence rules must clone it to produce congruent terms, even when the
collection contents are unchanged. For ASTs with many collection-bearing nodes,
this produces a "clone storm" -- O(n * k) cloning work per congruence
iteration, where n is the number of matching nodes and k is the average
collection size.

```
  Clone storm in congruence rules:

  ┌──────────────────────────────────────┐
  │  Constructor PPar(HashBag(Proc))     │
  │                                      │
  │  Congruence rule fires:              │
  │    eq_proc(t1, t2) <--              │
  │      proc(PPar(children)),           │
  │      ...                             │
  │      let t2 = PPar(children.clone()) │  <-- full collection clone
  │                                      │
  │  Per iteration: O(|children|) clone  │
  │  Per fixpoint:  O(depth * n * k)     │
  └──────────────────────────────────────┘
```

In grouped mode, all affected constructors are consolidated into a single
summary diagnostic listing each constructor and its parent category.

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one constructor with a collection-typed field:
  - `Vec<T>` (ordered sequence)
  - `HashBag<T>` (multiset)
  - `HashSet<T>` (unordered set)
- The collection field type is detected either via:
  - Old-style `GrammarItem::Collection { coll_type, element_type, .. }` items.
  - New-style `term_context` parameters with `TypeExpr::Collection { .. }` type
    annotations.
- Antipattern detection is invoked during macro expansion (always-on).

One diagnostic is emitted per unique (constructor, category) pair.

## Example

### Grammar

```rust
language! {
    name: RhoCalc,
    types {
        Proc,
        Name
    },
    terms {
        PPar  . children:HashBag(Proc) |- ... : Proc;
        NSend . args:Vec(Proc)         |- ... : Name;
        NNil  .                        |- "Nil" : Name;
    },
}
```

### Output

```
warning[C-AP05] (RhoCalc): clone storm: constructor `PPar` (category `Proc`) has a `HashBag(Proc)` collection field -- congruence rules will clone the entire collection on every rule firing
  = hint: consider wrapping the collection field in `Rc<HashBag<Proc>>` or `Arc<HashBag<Proc>>` to reduce clone overhead in congruence rules
```

When multiple constructors are affected, grouping consolidates:

```
warning[C-AP05] (RhoCalc): 2 constructors have collection fields (clone storm risk): PPar(Proc), NSend(Name)
  = hint: consider wrapping the collection field in `Rc<HashBag<Proc>>` or `Arc<HashBag<Proc>>` to reduce clone overhead in congruence rules
```

## Resolution

1. **Wrap collections in `Rc<T>` or `Arc<T>`.** Reference-counted wrappers
   reduce clone cost from O(k) to O(1) by sharing the underlying allocation.
   Use `Rc` for single-threaded evaluation, `Arc` for concurrent/parallel
   Ascent runs.

2. **Use persistent data structures.** Replace `Vec<T>` with an immutable
   vector (e.g., `im::Vector<T>`) that supports O(log n) structural sharing.
   This eliminates the clone overhead entirely for most congruence operations.

3. **Factor out collection constructors.** Move collection-bearing constructors
   into a dedicated category with a specialized congruence strategy that avoids
   full cloning (e.g., element-wise congruence instead of whole-collection
   congruence).

4. **Accept the clone overhead.** If the grammar's collection fields are
   small (bounded constant size), the clone cost is negligible and this warning
   can be safely ignored.

## Hint Explanation

The hint **"consider wrapping the collection field in `Rc<Coll<T>>` or
`Arc<Coll<T>>` to reduce clone overhead in congruence rules"** identifies the
most direct mitigation: wrapping the collection in a reference-counted pointer
so that congruence rule firings share the collection's memory rather than
duplicating it. The choice between `Rc` (single-threaded, no atomic overhead)
and `Arc` (thread-safe, required for parallel Ascent) depends on the evaluation
context.

## Related Lints

- [C-AP03](C-AP03-deep-congruence-chains.md) -- Deep congruence chains.
  Collection fields in recursive constructors compound the congruence chain
  cost: each level of nesting clones the collection again.
- [C-AP04](C-AP04-unbounded-rewrite-growth.md) -- Unbounded term growth.
  Rewrite rules that increase term depth interact with collection cloning to
  produce super-linear memory growth.
- [G41](../grammar/G41-normalize-dedup-active.md) -- Normalize-on-insert
  dedup. Hash-based deduplication can reduce the number of congruence rule
  firings, partially mitigating clone storm impact.
