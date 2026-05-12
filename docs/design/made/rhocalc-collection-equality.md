# Rhocalc Collection Equality (`==` / `!=`)

**Status:** Implemented (RhoCalc)  
**Context:** Surface comparison on `CastList`, `CastBag`, `CastMap`, and `CastSet`; see [map-type-design.md](./native-types/map-type-design.md), [set-type-design.md](./native-types/set-type-design.md), and [lists-and-bags-support.md](./native-types/lists-and-bags-support.md).

---

## 1. Goal and Scope

**Goal:** Fold-time and guard-time `==` / `!=` on all Rhocalc collection values injected into `Proc`, producing `CastBool` literals with per-kind semantics aligned with `term_eq` and receive pattern matching.

**Scope:** `Eq` / `Ne` in `languages/src/rhocalc.rs`, shared helper `compare_collection_equality` in `languages/src/rhocalc/runtime.rs`, and `eval_guard_bool` in `languages/src/rhocalc/receive.rs`.

**Non-goals:** tuples; `List(…)` constructor sugar; `++` and other missing collection operators; wire/binary serialization; equality on braced `PPar` process multisets (not `CastBag`).

---

## 2. Per-Kind Semantics

| Cast | Literal | `==` |
|------|---------|------|
| `CastList` | `ListLit` | Same length, same order, element-wise `term_eq` |
| `CastBag` | `BagLit` | Multiset equality after `normalize_bag_elements`, count-aware `term_eq` |
| `CastMap` | `MapLit` | Key/value structural `term_eq` (insertion-order independent) |
| `CastSet` | `SetLit` | Set membership `term_eq` (order independent) |

`!=` is the boolean negation of `==` on the same operands.

**Cross-type:** Any pair where at least one operand is a collection cast and the casts are not the same kind (including collection vs scalar) folds to `false` / `true` for `!=`, not `error`.

**Non-literal payloads:** If both sides share a collection cast but inner literals are not yet available, `Eq` / `Ne` yield `Proc::Err` (same contract as scalar `Eq` on non-literal `CastInt`).

---

## 3. Ascent vs Surface

Ascent relations `eq_list`, `eq_bag`, `eq_map`, and `eq_set` in generated `rhocalc-datalog.rs` support equational reasoning and congruence. They are **not** the implementation of surface `==` / `!=`.

Surface comparison is a separate `fold_proc` path on `Proc::Eq` / `Proc::Ne` that calls `compare_collection_equality` before falling back to scalar literal arms.

---

## 4. Implementation

- **Helper:** `compare_collection_equality(lhs, rhs) -> Option<bool>` — `Some` when collection rules apply; `None` when scalar `Eq` / `Ne` should handle the pair.
- **Bags:** Compare `normalize_bag_elements` of both `BagLit` payloads so nested `PPar` inside bag literals matches `Len` / `count` behavior.
- **Guards:** `eval_guard_bool` tries the helper for `Proc::Eq` / `Proc::Ne`, then `eval_cmp_order` for numeric/string scalars.

---

## 5. Tests

- `languages/tests/rhocalc_tests.rs` — per-kind fold tests, cross-type `false`, bag multiset order independence, and `where` guards on collection `==`.
- `assert_reduces_to` / `multiset_eq`: only treat two displays as equal multisets when **both** parse as braced `PPar` (`{ a | b }`); `None == None` must not match.

---

## 6. Examples

```rhocalc
[1, 2] == [1, 2]          // true
[1, 2] == [2, 1]          // false
#{1 | 2 | 2}# == #{2 | 1 | 2}#  // true
{1: 10, 2: 20} == {2: 20, 1: 10}  // true
Set(1, 2, 3) == Set(3, 2, 1)      // true
[1, 2] == Set(1, 2)       // false
```
