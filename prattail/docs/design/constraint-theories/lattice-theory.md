# Lattice Theory -- Subtype Hierarchies with Join/Meet

**Feature gate:** `lattice-theory`
**Module:** `prattail/src/lattice_theory.rs`
**Dependencies:** `logict` (for `ConstraintTheory` trait)

---

## Intuition: Subtype Lattices for Type Compatibility

Languages with subtype polymorphism -- MeTTa with its `(:<)` declarations, Rholang with bundle capabilities, or any language with an inheritance hierarchy -- need to answer questions like:

- *Is `Nat` a subtype of `Number`?* (direct query)
- *What is the most specific common supertype of `Int` and `Float`?* (join / LUB)
- *What is the most general type that is a subtype of both `Readable` and `Writable`?* (meet / GLB)
- *Does a set of patterns cover all subtypes of `Value`?* (exhaustiveness)

These questions reduce to operations on a **finite partially ordered set** (poset) of types, which in the best case forms a **lattice** -- a poset where every pair of elements has both a least upper bound (join) and a greatest lower bound (meet).

Because the universe of types is finite and explicitly declared, the lattice theory is **fully decidable**: all queries reduce to graph reachability over the transitive closure of the subtype relation. No search is needed.

---

## Lattice Definitions

### Partially Ordered Set (Poset)

A **poset** `(T, <=)` is a set `T` with a binary relation `<=` that is:

- **Reflexive:** `forall a in T. a <= a`
- **Antisymmetric:** `forall a, b in T. (a <= b /\ b <= a) => a = b`
- **Transitive:** `forall a, b, c in T. (a <= b /\ b <= c) => a <= c`

### Lattice

A **lattice** is a poset where every pair of elements has:

- **Join** (least upper bound, LUB): `a \/ b` is the smallest `c` such that `a <= c` and `b <= c`
- **Meet** (greatest lower bound, GLB): `a /\ b` is the largest `c` such that `c <= a` and `c <= b`

Special elements:

| Element | Symbol | Property |
|---------|--------|----------|
| Top | `T` | `forall a. a <= T` (exists only if the lattice is bounded) |
| Bottom | `bot` | `forall a. bot <= a` (exists only if the lattice is bounded) |

### Subtype Lattice

In a subtype lattice, `a <= b` means "type `a` is a subtype of type `b`" -- every value of type `a` is also a value of type `b`. The join `a \/ b` is the *narrowest common supertype*, and the meet `a /\ b` is the *widest common subtype*.

---

## Example Lattice Diagrams

### Simple Type Hierarchy

```
                    Any (T)
                   / | \
                  /  |  \
               Number  String  Bool
              /     \
            Int    Float
             \    /
              Nat
               |
              bot
```

Subtype edges (direct, non-reflexive):

```
Nat <= Int,   Nat <= Float,   Int <= Number,   Float <= Number
Number <= Any,   String <= Any,   Bool <= Any
```

Join examples:
- `Int \/ Float = Number` (smallest common supertype)
- `Number \/ String = Any`
- `Int \/ Int = Int`

Meet examples:
- `Int /\ Float = Nat` (largest common subtype)
- `Number /\ String = bot` (if bot exists; otherwise no meet)

### Rholang Bundle Capabilities

```
          Bundle
         /      \
      Read     Write
         \      /
          ReadWrite
```

- `Read \/ Write = Bundle`
- `Read /\ Write = ReadWrite`
- `ReadWrite <= Read` and `ReadWrite <= Write`

---

## DAG Construction

The subtype relation is stored as directed edges in a `HashSet<(TypeId, TypeId)>`. Each edge `(sub, sup)` asserts `sub <= sup`.

### Transitive Closure via Warshall's Algorithm

Given direct edges, the transitive closure is computed using Warshall's algorithm to answer arbitrary `a <= b` queries:

```
function compute_closure(edges, universe):
    closure = edges union {(t, t) | t in universe}    -- reflexive

    all_types = universe union mentioned(edges)

    for k in all_types:                                -- Warshall
        predecessors = {i | (i, k) in closure}
        successors   = {j | (k, j) in closure}
        for i in predecessors:
            for j in successors:
                closure.insert((i, j))

    return closure
```

**Complexity:** O(n^3) where n = |universe|. For type hierarchies with tens to hundreds of types, this completes in microseconds. The closure is computed lazily (only when queried after an edge is added) and cached.

### Cycle Detection

After computing the closure, non-trivial cycles are detected: pairs `(a, b)` where `a <= b` and `b <= a` with `a != b`. In a proper poset, the antisymmetry axiom would forbid this. In practice, cycles indicate **type equivalences** -- `a` and `b` name the same type.

```
Detected cycles: [(a, b)] where
    closure.contains((a, b)) AND closure.contains((b, a)) AND a != b
```

Cycles are recorded but do not cause inconsistency. They are reported to downstream analyses (e.g., lint diagnostics) that may want to warn about redundant type declarations.

---

## Join/Meet Computation

### Join (LUB) Algorithm

```
function join(store, a, b):
    if a == b: return a
    if a <= b: return b                            -- a is more specific
    if b <= a: return a

    upper_bounds = {c in universe | a <= c AND b <= c}
    least = c in upper_bounds such that
        forall d in upper_bounds. d == c OR NOT(d <= c) OR c <= d

    return least (or None if no upper bound exists)
```

The least upper bound is the most specific type among all common supertypes. Results are cached in a `HashMap<(TypeId, TypeId), Option<TypeId>>` with symmetric normalization (`join(a, b) = join(b, a)`).

### Meet (GLB) Algorithm

Dual of join: find the most general type among all common subtypes.

```
function meet(store, a, b):
    if a == b: return a
    if a <= b: return a                            -- a is more specific
    if b <= a: return b

    lower_bounds = {c in universe | c <= a AND c <= b}
    greatest = c in lower_bounds such that
        forall d in lower_bounds. d == c OR NOT(c <= d) OR d <= c

    return greatest (or None if no lower bound exists)
```

---

## Decidability: Finite Universe, No Labeling

Because the universe of types is finite and explicitly provided, every lattice query reduces to finite graph operations:

| Query | Reduction | Complexity |
|-------|-----------|-----------|
| `a <= b` | Closure lookup | O(1) after O(n^3) closure |
| `join(a, b)` | Enumerate upper bounds, find least | O(n) per query (cached) |
| `meet(a, b)` | Enumerate lower bounds, find greatest | O(n) per query (cached) |
| Satisfiability | Edge addition always succeeds | O(n^3) closure recompute |
| Exhaustiveness | Check coverage of subtypes | O(n^2) |

No search is needed: `label()` returns `LogicStream::empty()`.

---

## Exhaustiveness: Covering All Subtypes

A set of patterns is **exhaustive** over type `T` if every concrete value of type `T` (or its subtypes) is matched by at least one pattern.

The lattice theory supports exhaustiveness checking by identifying **isolated types** -- types that appear in the universe but have no subtype edges:

```rust
fn isolated_types(&self, store: &LatticeStore) -> Vec<TypeId> {
    let mentioned = store.all_types();
    self.universe.iter()
        .filter(|t| !mentioned.contains(t))
        .collect()
}
```

For full exhaustiveness checking, the caller enumerates all subtypes of `T` (via the transitive closure) and verifies that every subtype is covered by some pattern. The lattice theory provides the subtype enumeration; the coverage check is performed by the pattern matching layer.

---

## ConstraintTheory Implementation

### propagate: Add Edge

`propagate(store, SubtypeConstraint { sub, sup })` adds a subtype edge and recomputes the transitive closure:

```rust
fn propagate(&self, store: &LatticeStore, c: &SubtypeConstraint) -> Option<LatticeStore> {
    let mut new_store = store.clone();
    new_store.add_edge(c.sub, c.sup);
    self.compute_closure(&mut new_store);
    Some(new_store)  // always succeeds; cycles are equivalences
}
```

Adding edges always succeeds -- cycles represent type equivalences, not contradictions.

### is_consistent: Always True

```rust
fn is_consistent(&self, _store: &LatticeStore) -> bool {
    true  // cycles are equivalences, not contradictions
}
```

### witness: Type Assignment

```rust
fn witness(&self, store: &LatticeStore) -> Option<TypeAssignment> {
    if !self.is_consistent(store) { return None; }
    // Map each type to itself as a trivial assignment
    let bindings = store.all_types().into_iter()
        .enumerate()
        .map(|(i, t)| (i, t))
        .collect();
    Some(TypeAssignment { bindings })
}
```

### evaluate: Closure Check

```rust
fn evaluate(&self, c: &SubtypeConstraint, assignment: &TypeAssignment) -> bool {
    // Check if sub <= sup holds under the assignment
    let sub = assignment.bindings.get(&(c.sub as usize)).copied().unwrap_or(c.sub);
    let sup = assignment.bindings.get(&(c.sup as usize)).copied().unwrap_or(c.sup);
    // sub == sup is always true (reflexive); otherwise check closure
    sub == sup || /* check in closure */
}
```

---

## MeTTa Examples

### Subtype Declaration

```metta
(: Nat Type)
(: Int Type)
(: Number Type)
(:<  Nat Int)       -- Nat is a subtype of Int
(:<  Int Number)    -- Int is a subtype of Number
```

As lattice constraints:

```
SubtypeConstraint { sub: Nat, sup: Int }
SubtypeConstraint { sub: Int, sup: Number }

Transitive closure: Nat <= Int <= Number
Join(Nat, Int) = Int
```

### Type Compatibility Check

```metta
(: add (-> Number Number Number))
(add 3 4.5)
-- 3 : Nat, 4.5 : Float
-- Need: Nat <= Number AND Float <= Number
-- Both hold in the closure → type-safe
```

---

## Rholang Examples

### Bundle Capabilities

Rholang bundles have four levels: `bundle+` (write-only), `bundle-` (read-only), `bundle+-` (read-write), and `bundle0` (opaque).

```
Types: { Write, Read, ReadWrite, Opaque }
Edges: ReadWrite <= Read, ReadWrite <= Write, Read <= Opaque, Write <= Opaque
```

```
Lattice:

     Opaque (T)
    /        \
  Read      Write
    \        /
   ReadWrite (bot)
```

Exhaustiveness: a receive guard matching `Read` and `Write` separately does NOT cover `Opaque` (which is neither readable nor writable). The lattice analysis detects this gap.

---

## Store Implementation Details

The `LatticeStore` maintains:

```
edges:         HashSet<(TypeId, TypeId)>     -- direct subtype edges
closure:       HashSet<(TypeId, TypeId)>     -- transitive closure (lazy)
closure_dirty: bool                          -- recompute flag
lub_cache:     HashMap<(TypeId, TypeId), Option<TypeId>>  -- join cache
glb_cache:     HashMap<(TypeId, TypeId), Option<TypeId>>  -- meet cache
cycles:        Vec<(TypeId, TypeId)>          -- detected equivalences
```

Adding a new edge marks the closure as dirty and clears both caches. The closure is recomputed on the next `is_subtype`, `join`, or `meet` query.

Cache keys are symmetrically normalized: `join(a, b)` and `join(b, a)` share the same cache entry via `key = if a <= b { (a, b) } else { (b, a) }`.

---

## Citations

- Birkhoff, G. (1940). *Lattice Theory*. American Mathematical Society Colloquium Publications, vol. 25.
- Davey, B. A. & Priestley, H. A. (2002). *Introduction to Lattices and Order*. 2nd edition. Cambridge University Press. DOI: [10.1017/CBO9780511809088](https://doi.org/10.1017/CBO9780511809088)
- Warshall, S. (1962). "A Theorem on Boolean Matrices." *Journal of the ACM*, 9(1), 11--12. DOI: [10.1145/321105.321107](https://doi.org/10.1145/321105.321107)
- Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press. Chapter 15: Subtyping.
