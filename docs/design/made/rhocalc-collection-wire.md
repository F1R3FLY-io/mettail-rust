# Rhocalc Collection Wire / `toByteArray()`

**Status:** Implemented (RhoCalc)  
**Context:** Surface `toByteArray()` on `CastList`, `CastBag`, `CastMap`, and `CastSet`; see [rhocalc-collection-equality.md](./rhocalc-collection-equality.md), [map-type-design.md](./native-types/map-type-design.md), [set-type-design.md](./native-types/set-type-design.md), and [lists-and-bags-support.md](./native-types/lists-and-bags-support.md).

**References:** [Rholang data structures](https://rholang.org/tutorials/data-structures/), [f1r3node `03-data-types`](https://github.com/F1R3FLY-io/f1r3node/blob/rust/dev/docs/rholang/03-data-types.md), [f1r3node `06-collections`](https://github.com/F1R3FLY-io/f1r3node/blob/rust/dev/docs/rholang/06-collections.md).

---

## 1. Goal and Scope

**Goal:** Fold-time `.toByteArray()` on Rhocalc collection values injected into `Proc`, returning a `CastBytes` payload whose bytes match f1r3node `Par` protobuf encoding for the corresponding Rholang collection kind.

**Scope:** `MToByteArray` in [`languages/src/rhocalc.rs`](../../languages/src/rhocalc.rs), encoder in [`languages/src/rhocalc/wire.rs`](../../languages/src/rhocalc/wire.rs), and `collection_wire` tests in [`languages/tests/rhocalc_tests.rs`](../../languages/tests/rhocalc_tests.rs).

**Non-goals:** tuples; PathMap / Zipper; full rho-calculus `Par` wire; decode / `fromByteArray`; string `hexToBytes` / `toUtf8Bytes`; byte-array `slice` / `nth` / `length`; Calculator; equality on braced `PPar` multisets (not `CastBag`).

---

## 2. Surface Contract

| Kind | Example | `toByteArray()` |
|------|---------|-----------------|
| List | `[1, 2, 3]` | zero-arg method; protobuf `EList { ps }` |
| Set | `Set(1, 2, 3)` | zero-arg method; protobuf `ESet { ps }` with sorted `Par` keys |
| Map | `{1: 10, 2: 20}` | zero-arg method; protobuf `EMap { kvs }` with sorted keys |
| Bag | `#{1 \| 2 \| 2}#` | Rhocalc extension: multiset expanded to `EList` after `normalize_bag_elements` |

Results are injected as `CastBytes` with a `Bytes::StringLit` **lowercase hex** display (no Rholang byte literal syntax in v1).

---

## 3. Encoder Pipeline

1. Fold receiver to a ground collection cast (`CastList` / `CastBag` / `CastMap` / `CastSet` with literal payloads).
2. Map ground `Proc` leaves to minimal `rhoapi::Par` / `ExprInstance` messages (subset of `RhoTypes.proto` generated in `languages/build.rs`).
3. `Par::encode_to_vec()` (prost) produces wire bytes.
4. Hex-encode bytes into `Bytes::StringLit` and wrap with `CastBytes`.

Set/map entries are sorted by encoded `Par` bytes before serialization. Bag multiplicity is preserved by repeating element `Par` values in an `EList`.

---

## 4. Golden Vectors

Golden bytes are pinned against **f1r3fly-models 0.1.0** / f1r3node `rust/dev` for scalar list/set/map cases (`list_123`, `set_123`, `map_12`). Additional Rhocalc-only vectors cover nested lists and bag multiset expansion in `rhocalc::wire` unit tests and `collection_wire` integration tests.

Enable `rholang-wire` on `mettail-languages` only when running golden-byte integration checks that depend on the reference crate (default tests use the in-tree encoder).

---

## 5. Tests

- `languages/src/rhocalc/wire.rs` — direct encoder golden-byte unit tests.
- `languages/tests/rhocalc_tests.rs` — `native_ops::collection_wire` fold tests, order-independence for set/map, nested list, bag expansion, unsupported receiver errors.

---

## 6. Examples

```rhocalc
[1, 2, 3].toByteArray()
Set(3, 2, 1).toByteArray()
{2: 20, 1: 10}.toByteArray()
#{1 | 2 | 2}#.toByteArray()
```

Each folds to a quoted hex string representing the protobuf-encoded ground `Par` for that collection.
