# Rhocalc Collection Wire / `toByteArray()`

**Status:** ★ **SUPERSEDED (2026-07-25) — the host-side encoder and its forked schema are retired.**
`.toByteArray()` is now evaluated by f1r3node's own reducer. See §7 for what replaced it and why.

**Context:** Surface `toByteArray()` on `CastList`, `CastBag`, `CastMap`, and `CastSet`; see [rhocalc-collection-equality.md](./rhocalc-collection-equality.md), [map-type-design.md](./native-types/map-type-design.md), [set-type-design.md](./native-types/set-type-design.md), and [lists-and-bags-support.md](./native-types/lists-and-bags-support.md).

**References:** [Rholang data structures](https://rholang.org/tutorials/data-structures/), [f1r3node `03-data-types`](https://github.com/F1R3FLY-io/f1r3node/blob/rust/dev/docs/rholang/03-data-types.md), [f1r3node `06-collections`](https://github.com/F1R3FLY-io/f1r3node/blob/rust/dev/docs/rholang/06-collections.md).

---

## 1. Goal and Scope

**Goal (historical):** Fold-time `.toByteArray()` on Rhocalc collection values injected into `Proc`, returning a `CastBytes` payload whose bytes match f1r3node `Par` protobuf encoding for the corresponding Rholang collection kind.

**Goal (current):** `.toByteArray()` returns exactly what Rholang's `toByteArray` returns, because it *is* Rholang's `toByteArray` — a real `GByteArray`, produced by the consensus reducer.

**Scope (current):** `MToByteArray` in [`languages/src/rhocalc.rs`](../../../languages/src/rhocalc.rs) (a pure constructor — no fold body), `lower_method` in [`rholang-runtime/src/rhocalc_ast.rs`](../../../rholang-runtime/src/rhocalc_ast.rs), and the conformance tests in [`rholang-runtime/tests/rho_rhocalc_conformance.rs`](../../../rholang-runtime/tests/rho_rhocalc_conformance.rs).

**Non-goals:** decode / `fromByteArray`; string `hexToBytes` / `toUtf8Bytes`; byte-array `slice` / `nth` / `length`; Calculator.

---

## 2. Surface Contract

| Kind | Example | `toByteArray()` |
|------|---------|-----------------|
| List | `[1, 2, 3]` | `EMethod("toByteArray")` over the lowered `EList` |
| Set | `Set(1, 2, 3)` | over the lowered `ESet`; members canonicalized by the machine's `SortedParHashSet` |
| Map | `{1: 10, 2: 20}` | over the lowered `EMap`; keys canonicalized likewise |
| Bag | `#{1 \| 2 \| 2}#` | over the lowered `EList` tagged `mettail.rhocalc.bag.v1` (`RHOCALC_BAG_ABI_TAG`), carrying `(element, count)` pairs |

The result is a **`GByteArray`** — the same carrier Rholang uses — not a hex `GString`.

---

## 3. Pipeline

```
  RhoCalc source                lowering (rhocalc_ast.rs)              f1r3node reducer
  ──────────────                ───────────────────────                ────────────────
  m.toByteArray()   ─────▶   EMethod { method_name: "toByteArray",  ─▶  method_table["toByteArray"]
                               target: ⟦m⟧, arguments: [] }              ▸ eval_expr(target)
                                                                         ▸ substitute
                                                                         ▸ Par::encode_to_vec()
                                                                        ─▶ GByteArray
```

There is no host-side encoder and no second schema. Canonical ordering is whatever
`models`' `Ordering::sort_pars` / `SortedParHashSet` decides, because the machine performs it.

---

## 4. Golden Vectors

Pinned in `rholang-runtime/tests/rho_rhocalc_conformance.rs`
(`c2_closed_to_byte_array_is_the_reducers_own_encoding`,
`c2_closed_to_byte_array_uses_the_machines_canonical_order`,
`c2_closed_bag_to_byte_array_keeps_the_bag_abi_tag`) against the real reducer.

| Source | Bytes |
|---|---|
| `[1, 2, 3].toByteArray()` | `2a1ba201180a062a049a0201010a062a049a0201020a062a049a020103` |
| `Set(1, 2, 3)` / `Set(3, 2, 1)` | `2a1bb201180a062a049a0201010a062a049a0201020a062a049a020103` |
| `{1: 10, 2: 20}` / `{2: 20, 1: 10}` | `2a27ba01240a100a062a049a02010112062a049a02010a0a100a062a049a02010212062a049a020114` |
| `[[1, 2], [3]]` | `2a29a201260a152a13a201100a062a049a0201010a062a049a0201020a0d2a0ba201080a062a049a020103` |
| `[]` | `2a03a20100` |
| `Set(0 - 2, 1)` | `2a13b201100a062a049a0201010a062a049a0201fe` |

Reading the list vector: `2a 1b` is `Par.exprs` (field 5) length 27; `a2 01 18` is
`ExprInstance.e_list_body` (field 20) length 24; each `0a 06 2a 04 9a 02 01 0N` is one element
`Par` whose single expr is a **`GBigInt`** (`9a 02`) leaf. `GBigInt` — not `GInt` — because a plain
RhoCalc integer literal is arbitrary-precision (Rholang 1.4's default).

---

## 5. Tests

- `rholang-runtime/tests/rho_rhocalc_conformance.rs` — the golden vectors above, asserted with
  `assert_eq!` against the real reducer's output.
- `languages/tests/rhocalc_tests.rs` — only `native_ops::collection_wire::unsupported_receiver_errors`
  remains (it uses `assert_never_reaches`, an exact-display comparison).

---

## 6. Examples

```rhocalc
[1, 2, 3].toByteArray()
Set(3, 2, 1).toByteArray()
{2: 20, 1: 10}.toByteArray()
#{1 | 2 | 2}#.toByteArray()
```

Each lowers to `EMethod("toByteArray")` and is evaluated by the reducer, yielding a `GByteArray`.

---

## 7. ★ Why the original design was retired

The v1 design compiled a hand-mirrored **fork** of f1r3node's `rhoapi` schema
(`languages/proto/rhocalc_wire.proto`, 7 of `RhoTypes.proto`'s 62 messages) via
`languages/build.rs` into a *second* `rhoapi::Par` type inside the same workspace, and encoded
against it in `languages/src/rhocalc/wire.rs`. It is retired under the "different carriers, ONE
evaluator" convergence. Three independent defects, all measured on 2026-07-25:

| # | Defect | Evidence | Consequence |
|---|---|---|---|
| 1 | the fork's `.proto` had **no `g_big_int` field**, and `proc_to_par` matched only `Proc::CastInt(Int::NumLit(_))` | `[1, 2]` parses/folds to `CastList(ListLit([CastBigInt(NumLit(1)), CastBigInt(NumLit(2))]))` | `.toByteArray()` folded to `error` for every collection the grammar produces — the encoder was unreachable from source |
| 2 | set/map members sorted by raw **protobuf byte order** (`wire.rs:19-25`) | Rholang sorts by `ScoredTerm` **value** order (`models/src/rust/sorted_par_hash_set.rs:22`) | two canonical orders for one conceptual sorted set; they disagree on negative integers |
| 3 | the result was a **hex `GString`** (`wire.rs:136-139`) | Rholang's `toByteArray` returns a `GByteArray` (`reduce.rs:4137-4160`) | the wrong carrier; RhoCalc also skipped the reducer's `substitute` step |
| 4 | bag encoding **expanded the multiset** into a bare `EList` | the real lowering tags it `mettail.rhocalc.bag.v1` with `(element, count)` pairs | the bytes decoded back to a list, not a bag |

The old goldens (e.g. `2a15a201120a042a0210020a042a0210040a042a021006` for `[1,2,3]`) are not merely
stale: they encode a **different Rholang term** — `GInt` elements (`sint64` zigzag `02 04 06`)
where RhoCalc means `GBigInt`.

Additionally, the goldens' `collection_wire` integration tests were **vacuous**.
`assert_reduces_to` reaches its verdict through a disjunction ending in `bag_multiset_eq`, which
returns `to_sorted_bag_elements(a) == to_sorted_bag_elements(b)` — `None == None` ⟹ `true` —
whenever neither side is a `#{…}#` bag literal. `assert_reduces_to("1 + 2", "999")` passes.
The wire goldens were therefore green against a fold result of `error`.

Tag numbers in the fork (`e_list_body = 20`, `e_set_body = 22`, `e_map_body = 23`,
`g_byte_array = 25`) were correct only by manual maintenance; any upstream `RhoTypes.proto` change
would have been a **silent** divergence. Routing through `EMethod` removes the schema, the encoder,
the `protoc` build dependency, and the whole divergence class by construction.
