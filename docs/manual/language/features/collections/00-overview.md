# Collections — Overview

Collections are multi-element term containers that gather zero or more child
terms under a single constructor.  MeTTaIL supports three collection kinds,
each with different ordering and multiplicity semantics:

| Kind        | Type         | Order     | Duplicates        | Equality       | DSL Syntax         |
|-------------|--------------|-----------|-------------------|----------------|--------------------|
| **HashBag** | `HashBag<T>` | Unordered | Allowed (counted) | Count-based    | `ps:HashBag(Proc)` |
| **HashSet** | `HashSet<T>` | Unordered | Deduplicated      | Set membership | `ss:HashSet(Name)` |
| **Vec**     | `Vec<T>`     | Ordered   | Allowed           | Positional     | `vs:Vec(Proc)`     |

All three use the `*sep(delim)` metasyntax to specify the separator token
between elements in concrete syntax.

## Running Example

RhoCalc's parallel composition `PPar` uses `HashBag` and is built from the
bare-infix surface rule `PParInfix . a "|" b` which folds into the
multiset `Proc::PPar`:

```text
PParInfix . a:Proc, b:Proc |- a "|" b : Proc
    ![{ merge_pp_parallel(a, b) }] fold ;
PPar      . ps:HashBag(Proc) |- "__ppar" "(" ps.*sep(",") ")" : Proc ; // internal
```

Concrete surface syntax: `a | b | c` → `Proc::PParInfix(…)` →
(fold via `merge_pp_parallel`) → `Proc::PPar(HashBag { a, b, c })`. The
internal `__ppar(…)` form is reserved for AST round-tripping and never
appears in user input. See
[exploring/rhocalc-rholang-style-syntax.md](../../../../../design/exploring/rhocalc-rholang-style-syntax.md)
for the Rholang-style alignment that drove this split.

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
