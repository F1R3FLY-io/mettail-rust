---
name: Map operators suggestion
overview: Suggest a set of Map operators that mirror and extend the existing List and Bag operator patterns in Calculator and RhoCalc, so Map becomes as usable as List/Bag in language definitions.
todos: []
isProject: false
---

# Suggested Map operators (aligned with List and Bag)

## Existing operators (reference)

From [languages/src/calculator.rs](languages/src/calculator.rs) and [languages/src/rhocalc.rs](languages/src/rhocalc.rs):


| Collection | Operator                             | Signature (conceptually) | Role                    |
| ---------- | ------------------------------------ | ------------------------ | ----------------------- |
| **List**   | `length(a)`                          | List → Int               | Size                    |
| **List**   | `at(a, i)`                           | List × Int → Proc        | Lookup by index         |
| **List**   | `delete(a, i)`                       | List × Int → List        | Remove by index         |
| **List**   | `concat(a, b)`                       | List × List → List       | Combine two             |
| **Bag**    | (no explicit len; count per element) | —                        | —                       |
| **Bag**    | `count(b, e)`                        | Bag × Proc → Int         | Multiplicity of element |
| **Bag**    | `remove(a, e)`                       | Bag × Proc → Bag         | Remove one occurrence   |
| **Bag**    | `union(a, b)`                        | Bag × Bag → Bag          | Combine two             |
| **Bag**    | `diff(a, b)`                         | Bag × Bag → Bag          | Multiset difference     |


The design doc [docs/design/made/map-type-design.md](docs/design/made/map-type-design.md) (Phase 3) already mentions: *"Basic operations (get, insert, remove) as term rules if needed"*.

---

## Suggested Map operators

Follow the same style: **term rules** with `Proc` (or `Map`) in semantic positions, and **congruence rules** for every argument. Use **fold** where a Map argument is consumed (like List/Bag), and decide error behaviour (e.g. `Proc::Err` or panic for missing key) to match `ElemList` / `at`.

### 1. Core (align with design doc and List/Bag)


| Operator                   | Signature                                | Description                                                                                                         | List/Bag analogue                                                            |
| -------------------------- | ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------- |
| **get**                    | `get(m, k)` : Map × Proc → Proc          | Lookup value for key. Missing key: return `Proc::Err` (or a dedicated optional) to match `at`-out-of-bounds policy. | List: `at(a, i)`                                                             |
| **length**                 | `length(m)` : Map → Int                  | Number of key-value pairs.                                                                                          | List: `length(a)`; Bag: size via iteration                                   |
| **put** (or **insert**)    | `put(m, k, v)` : Map × Proc × Proc → Map | Map with `k → v` (overwrites if present). Immutable style: return new Map.                                          | List: no direct analogue (insert_at could be added); Bag: add one occurrence |
| **delete** (or **remove**) | `delete(m, k)` : Map × Proc → Map        | Remove key `k`; return new Map. No-op or identity if key absent.                                                    | List: `delete(a, i)`; Bag: `remove(a, e)`                                    |


### 2. Combine (like concat / union)


| Operator                 | Signature                         | Description                                                                                                 | List/Bag analogue            |
| ------------------------ | --------------------------------- | ----------------------------------------------------------------------------------------------------------- | ---------------------------- |
| **merge** (or **union**) | `merge(m1, m2)` : Map × Map → Map | Combine two maps. **Recommendation: right wins** (keys in `m2` overwrite `m1`). Deterministic and standard. | List: `concat`; Bag: `union` |


### 3. Membership (natural for key-value store)


| Operator                      | Signature                       | Description                   | List/Bag analogue                                              |
| ----------------------------- | ------------------------------- | ----------------------------- | -------------------------------------------------------------- |
| **has** (or **contains_key**) | `has(m, k)` : Map × Proc → Bool | True iff `k` is a key in `m`. | Bag: `count(b, e) > 0`; List: no built-in in current languages |


### 4. Optional (Phase 2 or later)


| Operator   | Signature                | Description                                                 |
| ---------- | ------------------------ | ----------------------------------------------------------- |
| **keys**   | `keys(m)` : Map → List   | List of keys (order unspecified unless sorted for display). |
| **values** | `values(m)` : Map → List | List of values.                                             |


These require building a `List` from map iteration; useful for scripting and debugging. Can be deferred.

---

## Summary table (suggested first phase)


| Name      | Syntax idea     | Type                  | Congruence                          |
| --------- | --------------- | --------------------- | ----------------------------------- |
| GetMap    | `get(m, k)`     | Map, Proc → Proc      | CongL (m), CongR (k)                |
| LenMap    | `length(m)`     | Map → Int             | Cong (m)                            |
| PutMap    | `put(m, k, v)`  | Map, Proc, Proc → Map | CongL (m), CongKey (k), CongVal (v) |
| DeleteMap | `delete(m, k)`  | Map, Proc → Map       | CongL (m), CongR (k)                |
| MergeMap  | `merge(m1, m2)` | Map, Map → Map        | CongL, CongR                        |
| HasKeyMap | `has(m, k)`     | Map, Proc → Bool      | CongL (m), CongR (k)                |


Naming can follow existing style: e.g. `GetMap` / `ElemMap` (to mirror `ElemList`), `LenMap`, `PutMap`, `DeleteMap`, `MergeMap`, `HasMap` or `HasKeyMap`.

---

## Implementation notes

- **Where to add:** In a language that already has `![HashMap] as Map` and `ProcMap` (e.g. Calculator or RhoCalc). Same pattern as List/Bag: term rules with `![...]` Rust blocks using `HashMapLit` (or the underlying map type).
- **Runtime:** `HashMapLit` in [runtime/src/hashmap_lit.rs](runtime/src/hashmap_lit.rs) wraps `HashMap`; operations are `get`, `insert`, `remove`, `len`, iteration. No new runtime type needed; only term (and congruence) rules in the language macro.
- **Error handling:** For `get(m, k)` when `k` is missing, either (a) return `Proc::Err` so languages can test, or (b) panic to match `at(..., i)` out-of-bounds. Recommend (a) for Map so that “key absent” is a normal case.
- **Congruence:** For each new term constructor (GetMap, PutMap, etc.), add congruence rules for all argument positions so that rewrites under contexts are supported, mirroring [rhocalc.rs](languages/src/rhocalc.rs) (e.g. `ElemListCongL`, `ElemListCongR`).

---

## Recommendation

Introduce **in this order**:

1. **get**, **length**, **put**, **delete** — core map operations (design doc get/insert/remove + size).
2. **merge** — combine maps (right wins); aligns with concat/union.
3. **has** — key membership; aligns with bag count and common map usage.

Add **keys** / **values** in a later phase if needed for iteration or debugging.