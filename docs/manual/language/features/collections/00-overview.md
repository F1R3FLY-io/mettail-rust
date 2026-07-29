# Collections — Overview

Collections are multi-element term containers that gather zero or more child
terms under a single constructor.  MeTTaIL supports three collection kinds,
each with different ordering and multiplicity semantics:

| Kind        | Type         | Order     | Duplicates        | Equality       | DSL Syntax         |
|-------------|--------------|-----------|-------------------|----------------|--------------------|
| **HashBag** | `HashBag<T>` | Unordered | Allowed (counted) | Count-based    | `ps:HashBag(Proc)` |
| **HashSet** | `HashSet<T>` | Unordered | Deduplicated      | Set membership | `ss:HashSet(Name)` |

Rholang also exposes a native **`Set`** category (`Set(…)` literals backed by
`HashSetLit<Proc>`; see [set-type-design.md](../../../../design/made/native-types/set-type-design.md)).
| **Vec**     | `Vec<T>`     | Ordered   | Allowed           | Positional     | `vs:Vec(Proc)`     |

All three use the `*sep(delim)` metasyntax to specify the separator token
between elements in concrete syntax.

## Running Example

Rholang's parallel composition `PPar` uses `HashBag`, and it is the clearest
illustration of a point worth making early: **one collection node may carry more
than one surface syntax.** `PPar` carries two.

```text
PPar      . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;

PParInfix . a:Proc, b:Proc   |- a "|" b : Proc
    ![{ merge_pp_parallel(a, b) }] fold ;
```

- The **braced collection rule** is the direct one. `{ a | b | c }` enters the
  collection frame at `{`, reads elements separated by `|`, and pops at `}`,
  producing `Proc::PPar(HashBag { a, b, c })` in a single step.
- The **bare-infix rule** is the idiomatic one. `a | b | c` parses as nested
  `Proc::PParInfix(…)` nodes, which `fold` collapses through
  `merge_pp_parallel`. That helper flattens any `Proc::PPar` member it meets, so
  the nesting does not survive into the result: the same flat n-ary
  `HashBag { a, b, c }` comes out.

Both routes therefore converge on one normal form, which is what makes `|`
associative and commutative *as a matter of the data structure* rather than as a
matter of declared equations.

```text
        "{ a | b | c }" ──────────────────────────┐
                                                  ▼
                                    Proc::PPar(HashBag { a, b, c })
                                                  ▲
        "a | b | c" ──► PParInfix(PParInfix(a,b),c)┘
                              (fold: merge_pp_parallel)
```

> **Removed:** a third surface, the internal keyword rule
> `PPar . ps:HashBag(Proc) |- "__ppar" "(" ps.*sep(",") ")" : Proc`, appeared in
> earlier revisions of this page and was described as the reserved round-trip
> form for the AST. It was deleted from the grammar on 2026-07-29 as a vestige of
> the pre-braced grammar, and the description had been inaccurate for some time
> before that: `Proc::PPar` displays through the braced form, never through
> `__ppar(…)`. Nothing replaces it — the braced rule *is* the round-trip surface.

See
[exploring/rholang-rholang-style-syntax.md](../../../../../design/exploring/rholang-rholang-style-syntax.md)
for the Rholang-style alignment that drove the introduction of the braced form.

## Key Types

| Type                         | Crate                       | Purpose                                                       |
|------------------------------|-----------------------------|---------------------------------------------------------------|
| `CollectionType`             | `macros/src/ast/types.rs`   | DSL-level enum: `HashBag`, `HashSet`, `Vec`                   |
| `CollectionKind`             | `prattail/src/recursive.rs` | PraTTaIL-level enum (mirrors `CollectionType`)                |
| `HashBag<T>`                 | `mettail_runtime::hashbag`  | Runtime multiset backed by `HashMap<T, usize>`                |
| `SyntaxItemSpec::Collection` | `prattail/src/lib.rs`       | Syntax item carrying param, element category, separator, kind |

## Pipeline Diagram

```text
    DSL definition                          Source files
    ──────────────                          ────────────
    ps:HashBag(Proc) ... ps.*sep("|")       macros/src/ast/grammar.rs
            │
            ▼
    TermParam::Simple {                     macros/src/ast/grammar.rs
      ty: TypeExpr::Collection {
        coll_type: HashBag,
        element: Base(Proc) }}
            │
    PatternOp::Sep {                        macros/src/ast/grammar.rs
      collection: "ps",
      separator: "|",
      source: None }
            │
            ▼
    SyntaxItemSpec::Collection {            prattail/src/lib.rs
      param_name: "ps",
      element_category: "Proc",
      separator: "|",
      kind: HashBag }
            │
            ▼
    classify::classify_collection()         prattail/src/classify.rs
    → is_collection = true
    → collection_type = Some(HashBag)
    → separator = Some("|")
            │
            ▼
    is_simple_collection() → true           prattail/src/trampoline.rs
    → CollectionElem frame variant
    → Trampolined collection loop
            │
            ▼
    AST: Proc::PPar(HashBag<Proc>)          runtime/src/hashbag.rs
            │
            ▼
    Ascent: iter_elements() decomposition   macros/src/logic/categories.rs
    → ppar_contains(parent, elem)           macros/src/logic/congruence.rs
    → congruence + rewrite propagation
```

## Reading Guide

| Document                                                 | Content                                              |
|----------------------------------------------------------|------------------------------------------------------|
| [01-hashbag.md](01-hashbag.md)                           | Full pipeline trace for `HashBag(Proc)` using `PPar` |
| [02-hashset-and-vec.md](02-hashset-and-vec.md)           | Differences for `HashSet` and `Vec`                  |
| [03-ascent-decomposition.md](03-ascent-decomposition.md) | Ascent fixpoint rules for collection terms           |
| [Rholang collection equality](../../../../design/made/rholang-collection-equality.md) | Surface `==` / `!=` on Rholang `CastList` / `CastBag` / `CastMap` / `CastSet` (fold and guards), separate from Ascent `eq_*` |
| [Rholang collection wire](../../../../design/made/rholang-collection-wire.md) | Surface `.toByteArray()` on collection casts; protobuf `Par` bytes via `languages/src/rholang/wire.rs` |

## Rholang surface equality

Rholang programs compare collection values at the `Proc` layer with `==` and
`!=`, which fold to booleans via `compare_collection_equality`. This is
distinct from Ascent `eq_list`, `eq_bag`, `eq_map`, and `eq_set`, which
support rewriting and congruence. See
[rholang-collection-equality.md](../../../../design/made/rholang-collection-equality.md).
Collection `.toByteArray()` wire encoding is documented in
[rholang-collection-wire.md](../../../../design/made/rholang-collection-wire.md).

## Source Files

| File                                              | Role                                                           |
|---------------------------------------------------|----------------------------------------------------------------|
| `macros/src/ast/grammar.rs`                       | `GrammarItem::Collection`, `PatternOp::Sep`, `CollectionType`  |
| `macros/src/ast/types.rs`                         | `CollectionType` enum (`HashBag`, `HashSet`, `Vec`)            |
| `macros/src/gen/syntax/parser/prattail_bridge.rs` | `convert_pattern_op()`, `find_collection_info()`               |
| `prattail/src/lib.rs`                             | `SyntaxItemSpec::Collection` variant                           |
| `prattail/src/classify.rs`                        | `classify_collection()`                                        |
| `prattail/src/recursive.rs`                       | `CollectionKind`, collection parse loop, `insert_method_str()` |
| `prattail/src/trampoline.rs`                      | `is_simple_collection()`, `CollectionElem` frame variant       |
| `macros/src/logic/categories.rs`                  | `generate_collection_projection_population()`                  |
| `macros/src/logic/congruence.rs`                  | Collection congruence rules                                    |
| `runtime/src/hashbag.rs`                          | `HashBag<T>` implementation                                    |
