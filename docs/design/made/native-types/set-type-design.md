# Set Type Design

**Status:** Implemented (RhoCalc)  
**Context:** MeTTaIL collection types; see [map-type-design.md](./map-type-design.md) and [lists-and-bags-support.md](./lists-and-bags-support.md). Rholang reference: [Sets](https://rholang.org/tutorials/data-structures/#sets).

---

## 1. Goal and Scope

**Goal:** First-class **Set** category in RhoCalc with Rholang-style surface syntax and method sugar.

**Scope:** `![mettail_runtime::HashSetLit<Proc>] as Set` in `language! { types { … } }`. Default literal delimiters are `Set(`, `)`, `,` (`CollectionCategory::set_defaults()`). `Set()` is an explicit empty-set alias. Rhocalc **Bag** (`#{…}#`) remains the multiset / parallel-composition surface with no Rholang counterpart.

**Non-goals:** partial collection patterns, changing Bag syntax to Rholang `Set`. Surface `.toByteArray()` is specified in [rhocalc-collection-wire.md](./rhocalc-collection-wire.md).

---

## 2. Declaration and Runtime Type

**DSL:** `![mettail_runtime::HashSetLit<Proc>] as Set`

**Runtime:** `mettail_runtime::HashSetLit<T>` wraps `std::collections::HashSet` with deterministic `Hash`, `Ord`, and `Display` (sorted elements). Generated AST payloads use `Set::SetLit(HashSetLit<Proc>)`, not bare `HashSet`.

**Cast:** `CastSet . s:Set |- s : Proc` injects sets into `Proc`.

---

## 3. Macro and Parser Integration

- `CollectionCategory::Set` in `macros/src/ast/language.rs`
- Literal rule `SetLit` bridged to PraTTaIL `CollectionKind::HashSet` with `HashSetLit` initializers in `prattail/src/trampoline.rs`
- Display, substitution, term generation, and Ascent congruence treat `Set` like `Map` (first-class collection category), not like List/Bag-only categories

---

## 4. Operations and Method Sugar

Prefix builtins fold from method sugar in `languages/src/rhocalc.rs`:

| Rholang method | Lowering |
|----------------|----------|
| `s.add(e)` | `AddSet` |
| `s.delete(e)` | `DeleteSet` |
| `s.contains(e)` | `HasSet` |
| `s.union(t)` | `UnionSet` (also via polymorphic `MUnion` on `CastSet`) |
| `s.diff(t)` | `DiffSet` |
| `s.size()` | `MSize` / `Len` on `CastSet` |

`MContains` dispatches `CastMap` → `HasMap` and `CastSet` → `HasSet`. `Map.keys()` returns `Set` via `mk_proc_set`.

Quoted-name operands in `contains` / `delete` use the same element normalization as Bag `remove` / `count`.

---

## 5. Semantics

- Unordered membership; parse-time deduplication on literal construction
- Deterministic printing for tests and REPL (`Set(1, 2, 3)` with sorted elements)
- Receive patterns match `CastSet` / `SetLit` with strict cardinality (see `languages/src/rhocalc/receive.rs`)

---

## 6. Tests and Examples

- `languages/tests/rhocalc_tests.rs` — `native_ops::set`, pattern matching, `map.keys()` returning a set
- `repl/src/examples/rhocalc.txt` — set literals and method chains
