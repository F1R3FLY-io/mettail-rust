# Ascent Decomposition of Collections

This document explains how the Ascent Datalog engine decomposes collection
terms during fixpoint computation.  Collection decomposition has three aspects:

1. **Category exploration** — extracting elements for recursive analysis
2. **Congruence propagation** — if an element rewrites, the collection rewrites
3. **Pattern-based rewriting** — rules like Comm that match *inside* collections

## 1. Category Exploration

**File:** `macros/src/logic/categories.rs`

### Collection Projection Population

`generate_collection_projection_population()` generates a Datalog rule that
iterates the collection's elements and records each in a projection relation.

For `PPar` (HashBag of Proc):

```text
ppar_contains(parent.clone(), elem.clone()) <--
    proc(parent),
    if let Proc::PPar(ref bag_field) = parent,
    for (elem, _count) in bag_field.iter();
```

| Clause                                   | Purpose                               |
|------------------------------------------|---------------------------------------|
| `proc(parent)`                           | Source: any known Proc term           |
| `if let Proc::PPar(ref bag_field)`       | Guard: only PPar terms                |
| `for (elem, _count) in bag_field.iter()` | Iterate unique elements (with counts) |
| `ppar_contains(parent, elem)`            | Output: parent ↔ element relation     |

The `_count` is discarded — the projection relation records distinct
*membership*, not multiplicity.  This is correct because Ascent relations are
sets: repeated insertion of the same `(parent, elem)` pair is a no-op.

### Projection Seeding

A second rule seeds each discovered element into the element category's base
relation:

```text
proc(elem.clone()) <--
    ppar_contains(_, elem);
```

This ensures that sub-terms inside a HashBag are explored recursively — the
fixpoint engine will decompose them further if they contain nested
constructors.

### HashSet and Vec Iteration

For `HashSet<T>`:

```text
for elem in set_field.iter()
```

`HashSet::iter()` yields `&T` directly (no count tuple).

For `Vec<T>`:

```text
for elem in vec_field.iter()
```

`Vec::iter()` yields `&T` directly.

### Interaction Diagram

```text
  proc(PPar({A, B, C}))         ← seed
          │
          ├→ ppar_contains(PPar({A,B,C}), A)
          ├→ ppar_contains(PPar({A,B,C}), B)
          └→ ppar_contains(PPar({A,B,C}), C)
                    │
                    ├→ proc(A)   ← recursive exploration
                    ├→ proc(B)
                    └→ proc(C)
```

## 2. Congruence Propagation

**File:** `macros/src/logic/congruence.rs`

### Consolidated Simple Congruence

`generate_consolidated_simple_congruence()` produces a single rule that
handles all constructors with same-category fields, including collection
constructors.  For PPar, the congruence works as follows:

**Extraction phase** (TLS pool iteration):

```text
for (field_val, vi) in pool_iter:
    match (lhs, vi):
        (Proc::PPar(ref bag), 0):
            for elem in bag.iter_elements():
                buf.push((elem.clone(), 0))
```

Each element of the bag is yielded as a `(field_val, variant_index)` pair for
the rewrite check.

**Rewrite check:**

```text
rw_proc(field_val, t)           ← element has been rewritten
```

**Rebuild phase:**

```text
match (lhs, vi):
    (Proc::PPar(ref bag), 0):
        let mut new_bag = mettail_runtime::HashBag::new();
        for elem in bag.iter_elements() {
            if elem == field_val {
                new_bag.insert(t.clone());   ← substitute rewritten element
            } else {
                new_bag.insert(elem.clone()); ← keep original
            }
        }
        Proc::PPar(new_bag)
```

This replaces **all** occurrences of `field_val` in the bag with `t` and
constructs a new `PPar` with the updated bag.

### Example

```text
Given:  proc(PPar({A, B, A}))     ← A appears twice
        rw_proc(A, A')            ← A rewrites to A'

Result: rw_proc(PPar({A, B, A}),
                PPar({A', B, A'}))  ← both occurrences replaced
```

### Data Flow

```text
  proc(PPar({A, B}))
          │
          ├► extraction: (A, 0), (B, 0)
          │
          ├► rw_proc(A, A')  exists?
          │       │ yes
          │       ▼
          │   rebuild PPar({A', B})
          │       │
          │       ▼
          │   rw_proc(PPar({A,B}), PPar({A',B}))
          │
          └► rw_proc(B, B')  exists?
                  │ yes
                  ▼
              rebuild PPar({A, B'})
                  │
                  ▼
              rw_proc(PPar({A,B}), PPar({A,B'}))
```

If both A and B rewrite, two separate rewrite facts are produced — they are
*not* composed into `PPar({A',B'})`.  Transitive closure of rewriting handles
the composition.

## 3. Pattern-Based Rewriting

### The Comm Rule

RhoCalc's communication rule (`Comm`) is the primary example of a rewrite rule
that pattern-matches *inside* a collection.

**Informal rule:**

```text
If a PPar bag contains both POutput(n, v) and PInputs([n, ...], Scope([x, ...], body)):
  → rewrite PPar to:  body[x := v] | ...rest
```

### Pattern Matching with `to_ascent_clauses()`

**File:** `macros/src/ast/pattern.rs`

The Comm rule's pattern match generates Ascent clauses that:

1. **Iterate bag elements** to find POutput and PInputs:

```text
proc(parent),
if let Proc::PPar(ref bag) = parent,
for (elem_0, _c0) in bag.iter(),
if let Proc::POutput(ref chan_0, ref val_0) = elem_0,
for (elem_1, _c1) in bag.iter(),
if let Proc::PInputs(ref names_1, ref scope_1) = elem_1,
if &elem_0 != &elem_1,                    ← distinctness constraint
```

2. **Match channel names** (the `n` must be the same):

```text
if names_1.contains(chan_0),
```

3. **Compute rest** (remove matched elements from the bag):

```text
let rest = {
    let mut r = bag.clone();
    r.remove(&elem_0);
    r.remove(&elem_1);
    r
};
```

4. **Construct result** (substitute value for bound variable in body):

```text
let body = scope_1.unbind();   // freshen bound variables
let result = substitute(body, x, val_0);
let new_bag = rest;
new_bag.insert(result);
rw_proc(parent, Proc::PPar(new_bag))
```

### Rest-Variable Pattern

The `...rest` pattern in collection matching is compiled to:

```text
let rest = bag.clone();
rest.remove(&matched_elem_0);
rest.remove(&matched_elem_1);
// ... remove all matched elements
```

For HashBag, `remove()` decrements the count by 1 — so if an element appears
3 times and is matched once, 2 copies remain in `rest`.

### Distinctness Constraints

When a pattern matches multiple elements from the same bag, the generated
clauses include `if &elem_i != &elem_j` guards to prevent matching the same
element twice:

```text
for (elem_0, _c0) in bag.iter(),
for (elem_1, _c1) in bag.iter(),
if &elem_0 != &elem_1,            ← cannot be the same element
```

For bags with duplicates, `iter()` yields each unique element once (with its
count), so the distinctness check prevents pairing an element with itself.  If
an element has count ≥ 2, it can match in *both* positions (e.g., `A | A`
matching POutput and PInputs) because `iter()` yields `(A, 2)` only once,
and the same `A` can be bound to both `elem_0` and `elem_1` — the
distinctness check `&elem_0 != &elem_1` would be `false`, preventing the
self-match.

### Correlated Search (Zip Pattern)

For patterns using `#zip(first, second).#map(|a,b| Body(a,b))`, the generated
clauses enumerate all valid matchings:

```text
for (a, _) in first_bag.iter(),
for (b, _) in second_bag.iter(),
if let Cat::Body(ref matched_a, ref matched_b) = some_term,
if matched_a == a && matched_b == b,
```

This is used when multiple collections must be matched in lockstep.

## Summary of Generated Relations

For a collection constructor `Label` in category `Cat`:

| Relation                    | Type       | Generated By                                  |
|-----------------------------|------------|-----------------------------------------------|
| `label_contains(Cat, Elem)` | Projection | `generate_collection_projection_population()` |
| `cat(Elem)`                 | Seeding    | Projection seeding rule                       |
| `rw_cat(Cat, Cat)`          | Congruence | `generate_consolidated_simple_congruence()`   |

## Fixpoint Convergence

Collection congruence rules can produce cascading rewrites:

```text
Iteration 1:  rw_proc(A, A')
Iteration 2:  rw_proc(PPar({A, B}), PPar({A', B}))
Iteration 3:  rw_proc(B, B')
Iteration 4:  rw_proc(PPar({A', B}), PPar({A', B'}))
```

The fixpoint converges when no new rewrite facts are produced.  Since each
rewrite strictly reduces the "distance" to normal form (or produces an already-
known fact), termination is guaranteed for well-founded rewrite systems.

---

**See also:**
- [00-overview.md](00-overview.md) — Collections overview
- [01-hashbag.md](01-hashbag.md) — Full HashBag pipeline trace
- [02-hashset-and-vec.md](02-hashset-and-vec.md) — HashSet and Vec differences
- [../binders/02-multi-binders.md](../binders/02-multi-binders.md) — PInputs decomposition
