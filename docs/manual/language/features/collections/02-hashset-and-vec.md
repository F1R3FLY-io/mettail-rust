# HashSet and Vec — Differences from HashBag

This document describes the `HashSet(T)` and `Vec(T)` collection kinds,
focusing on how they differ from `HashBag(T)` at each pipeline stage.  The
shared pipeline mechanics are documented in [01-hashbag.md](01-hashbag.md);
this document covers only the deltas.

## Comparison Table

| Property             | HashBag                           | HashSet                        | Vec                    |
|----------------------|-----------------------------------|--------------------------------|------------------------|
| **Rust type**        | `mettail_runtime::HashBag<T>`     | `std::collections::HashSet<T>` | `std::vec::Vec<T>`     |
| **Order**            | Unordered                         | Unordered                      | Ordered (insertion)    |
| **Duplicates**       | Counted                           | Deduplicated                   | Allowed                |
| **Equality**         | Count-based (`HashMap<T, usize>`) | Set membership                 | Positional             |
| **Insert method**    | `insert(item)` (increments count) | `insert(item)` (deduplicates)  | `push(item)`           |
| **Init expression**  | `HashBag::new()`                  | `HashSet::new()`               | `Vec::new()`           |
| **Ascent iteration** | `bag.iter()` → `(&T, usize)`      | `set.iter()` → `&T`            | `vec.iter()` → `&T`    |
| **DSL syntax**       | `HashBag(T)`                      | `HashSet(T)`                   | `Vec(T)`               |
| **RhoCalc usage**    | PPar (parallel composition)       | — (not used)                   | PInputs (channel list) |

## HashSet(T)

### DSL Example

```text
UniqueNames . ss:HashSet(Name) |- "[" ss.*sep(",") "]" : Proc ;
```

Concrete syntax: `[a, b, c]` — duplicates are silently dropped.

### Pipeline Differences

**Bridge** (`prattail_bridge.rs`):

`find_collection_info()` maps `CollectionType::HashSet` to
`CollectionKind::HashSet`:

```text
SyntaxItemSpec::Collection {
    param_name:       "ss",
    element_category: "Name",
    separator:        ",",
    kind:             HashSet,       ← only difference from HashBag
}
```

**Classification** (`classify.rs`):

Identical logic — `classify_collection()` returns
`(true, Some(HashSet), Some(","))`.

**Parser codegen** (`trampoline.rs`):

The `CollectionElem` frame differs only in the collection initializer and
insert method:

| Aspect           | HashBag                       | HashSet                        |
|------------------|-------------------------------|--------------------------------|
| Frame field type | `mettail_runtime::HashBag<T>` | `std::collections::HashSet<T>` |
| Initializer      | `HashBag::new()`              | `HashSet::new()`               |
| Insert call      | `elements.insert(lhs)`        | `elements.insert(lhs)`         |

Both `HashBag::insert` and `HashSet::insert` are called `insert`, but
`HashSet::insert` returns `false` for duplicates (and silently drops them)
while `HashBag::insert` always increments the count.

**Runtime**: Uses `std::collections::HashSet<T>` directly — no custom
wrapper needed.

### Ascent Decomposition

Element iteration uses `set.iter()` yielding `&T` (no count):

```text
elem_rel(elem.clone()) <--
    parent_rel(parent),
    if let Cat::UniqueNames(ref set) = parent,
    for elem in set.iter();
```

Congruence: identical to HashBag — if an element is equivalent to another, the
containing set is equivalent.  However, since duplicates are already removed,
congruence rewrites cannot increase the set size.

## Vec(T)

### DSL Example

```text
Sequence . vs:Vec(Proc) |- "[" vs.*sep(";") "]" : Proc ;
```

Concrete syntax: `[a; b; c]` — order and duplicates preserved.

### Pipeline Differences

**Bridge** (`prattail_bridge.rs`):

```text
SyntaxItemSpec::Collection {
    param_name:       "vs",
    element_category: "Proc",
    separator:        ";",
    kind:             Vec,           ← only difference
}
```

**Parser codegen** (`trampoline.rs`):

| Aspect           | HashBag                       | Vec                  |
|------------------|-------------------------------|----------------------|
| Frame field type | `mettail_runtime::HashBag<T>` | `Vec<T>`             |
| Initializer      | `HashBag::new()`              | `Vec::new()`         |
| Insert call      | `elements.insert(lhs)`        | `elements.push(lhs)` |

`Vec::push` appends to the end, preserving insertion order.

**Runtime**: Uses `std::vec::Vec<T>` directly.

### Ascent Decomposition

Element iteration uses `vec.iter()` yielding `&T`:

```text
elem_rel(elem.clone()) <--
    parent_rel(parent),
    if let Cat::Sequence(ref vec) = parent,
    for elem in vec.iter();
```

**Ordering note:** Ascent relations are unordered sets, so the positional order
of elements within the `Vec` is lost after decomposition into the element
relation.  If downstream rules need position information, the constructor must
be pattern-matched directly rather than decomposed.

### Vec in PInputs

RhoCalc's `PInputs` uses `Vec(Name)` for the channel name list:

```text
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

Here `ns` is a `Vec<Name>` — the ordering matters because the *i*-th channel
pairs with the *i*-th bound variable.  However, `ns` is not parsed via a
simple `Collection` item — it is part of the ZipMapSep pattern, which
accumulates both `ns` and `xs` in a single loop.  See
[../ZipMapSep/02-parser-and-runtime.md](../ZipMapSep/02-parser-and-runtime.md)
for the parse details.

## Lexer and Syntax Interactions

All three collection kinds share the same lexer mechanics:
- Opening and closing delimiters are terminals in the grammar
- The separator token is a terminal
- No special lexer support is needed for any collection kind

The choice of collection kind affects only:
1. The runtime type of the collection
2. The insert method used during parsing
3. The iterator shape used in Ascent decomposition

## When to Use Each Kind

| Use Case                                        | Kind    | Rationale                             |
|-------------------------------------------------|---------|---------------------------------------|
| Parallel composition (order irrelevant, dup OK) | HashBag | Models multiset semantics             |
| Unique constraints (no duplicates)              | HashSet | Deduplication at parse time           |
| Ordered sequences (position matters)            | Vec     | Preserves insertion order             |
| Paired with ZipMapSep                           | Vec     | Positional pairing with binder vector |

---

**See also:**
- [00-overview.md](00-overview.md) — Collections overview
- [01-hashbag.md](01-hashbag.md) — Full HashBag pipeline trace
- [03-ascent-decomposition.md](03-ascent-decomposition.md) — Ascent decomposition details
- [../ZipMapSep/00-overview.md](../ZipMapSep/00-overview.md) — ZipMapSep (uses Vec internally)
