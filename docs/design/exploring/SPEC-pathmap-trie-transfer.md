# SPEC: PathMap Trie Transfer — Task Specification

**Status:** Draft (for cross-project handoff)  
**Source:** Analysis of f1r3node Rholang PathMap implementation (`new_parser_pathmap_fix` branch context)  
**Audience:** Developer porting or reimplementing PathMap as a trie in another codebase

---

## 1. Objective

Port or reimplement the **Rholang PathMap** as a **radix trie** (`pathmap` crate, v0.2.2) keyed by encoded paths with **`Par` payloads**, including optional **zipper** navigation and collection algebra (union, intersection, restriction, etc.).

This document captures **observed behavior**, **architecture**, and **design gaps** discovered during review of `pathmap-demo.rho` and the Rust integration layer—not an idealized path/value split API.

---

## 2. Executive Summary (Critical Semantics)

| Question | Answer in current f1r3node implementation |
|----------|---------------------------------------------|
| Does PathMap store values? | **Yes** — trie type is `PathMap<Par>` (key → `Par`). |
| Is there separate path vs value in `{| ... |}` syntax? | **No** — each literal element is one `Par`; no `path : value` form. |
| For `["a", "b", "c"]`, is `"c"` the value? | **No** — all list elements are **path segments** via `par_to_path`. |
| Is path identical to value? | **Not identical types** (bytes vs `Par`), but for **plain string lists** the value `Par` redundantly contains the same segments used to build the key. |
| Can key be recovered from value? | **Mostly yes** for list entries: `par_to_path(value)` + `0xFF` separators. |
| Can value be recovered from key alone? | **Only approximately** for simple strings (decode segments → rebuild list). Arbitrary `Par` shapes require the stored value. |

**Demo mental model vs implementation:** `pathmap-demo.rho` treats the last segment as “status” (`done`, `todo`). The engine does **not** implement that split—it stores the **full list** as both trie key material and leaf `Par`.

---

## 3. Reference Example (from `pathmap-demo.rho`)

```rholang
{| ["backend", "api", "done"],
   ["backend", "database", "in-progress"],
   ["frontend", "ui", "todo"],
   ["frontend", "tests", "todo"] |}
```

**What the implementation actually stores (per entry):**

| Entry | Trie key (conceptual segments) | Stored value (`Par`) |
|-------|-------------------------------|----------------------|
| 1 | `backend` → `api` → `done` | `EList["backend", "api", "done"]` |
| 2 | `backend` → `database` → `in-progress` | `EList["backend", "database", "in-progress"]` |
| … | … | … |

**Zipper operations used in demo (must be ported or reimplemented):**

- `readZipper()` / `readZipperAt(path)`
- `writeZipper()` / `writeZipperAt(path)`
- `getSubtrie()` — prefix query
- `setLeaf(pathPar)` — write entry at zipper position
- `setSubtrie(pathmap)` — replace subtrie at prefix
- `graft(zipper)` — merge another PathMap
- `getLeaf()` — value at current path (when implemented against trie)

---

## 4. Architecture (f1r3node)

### 4.1 Layer stack

```
Rholang source:  {| elem1, elem2, ... |}
       ↓ parser + normalizer
Protobuf/AST:    EPathMap { ps: Vec<Par>, remainder, locally_free, connective_used }
       ↓ PathMapCrateTypeMapper::e_pathmap_to_rholang_pathmap
Runtime trie:    pathmap::PathMap<Par>   (alias RholangPathMap)
       ↓ optional
Zipper API:      ReadZipperUntracked / WriteZipperUntracked (via RholangReadZipper / RholangWriteZipper)
```

### 4.2 Core types

| Type | Location | Role |
|------|----------|------|
| `EPathMap` | `models` proto / `rhoapi` | Serializable collection: flat `ps: Vec<Par>` |
| `RholangPathMap` | `models/src/rust/pathmap_integration.rs` | `PathMap<Par>` trie |
| `PathMapCreationResult` | same | `{ map, connective_used, locally_free }` |
| `EZipper` | `rhoapi` | `{ pathmap, current_path, is_write_zipper, ... }` |
| `PathMapCrateTypeMapper` | `models/src/rust/pathmap_crate_type_mapper.rs` | `EPathMap` ↔ trie conversion |

### 4.3 Path encoding (`par_to_path`)

**File:** `models/src/rust/pathmap_integration.rs`

```rust
pub fn par_to_path(par: &Par) -> Vec<Vec<u8>>
```

Rules:

1. **If `par` is a single `EList`:** each child element → one segment (S-expr encoded via `ParToSExpr` → `SExpr::encode()`).
2. **Otherwise:** entire `par` → **one** segment (S-expr of whole term).

**Trie key construction** (`create_pathmap_from_elements`):

```rust
let segments = par_to_path(par);
let key: Vec<u8> = segments.into_iter().flat_map(|mut seg| {
    seg.push(0xFF);  // segment separator — must not appear in encoded input
    seg
}).collect();
map.insert(key, par.clone());
```

**Implication:** Key derivation and stored value use the **same source `par`** at insert time.

### 4.4 EPathMap round-trip

- **To trie:** `create_pathmap_from_elements(&e_pathmap.ps, remainder)`
- **From trie:** `rholang_pathmap_to_e_pathmap` collects `map.iter()` → `ps` vector (values only; order depends on trie iteration)

### 4.5 Dependency

- **Crate:** `pathmap = "0.2.2"` (`models/Cargo.toml`)
- Provides: radix trie, `join` / `meet` / `subtract` / `restrict`, zippers

---

## 5. Key Source Files (f1r3node)

| Area | Path |
|------|------|
| Path encoding + trie build | `models/src/rust/pathmap_integration.rs` |
| Proto ↔ trie mapper | `models/src/rust/pathmap_crate_type_mapper.rs` |
| Zipper wrappers | `models/src/rust/pathmap_zipper.rs` |
| Parser/normalizer | `rholang/src/rust/interpreter/compiler/normalizer/collection_normalize_matcher.rs` |
| Runtime methods | `rholang/src/rust/interpreter/reduce.rs` (search: `readZipper`, `setLeaf`, `setSubtrie`, `getSubtrie`, `graft`) |
| Demo contract | `rholang/examples/pathmap-demo.rho` |
| Demo tests | `rholang/tests/demo_verification.rs` |
| Integration tests | `models/tests/pathmap_integration_tests.rs` |
| Zipper tests | `rholang/tests/zipper_*_spec.rs`, `rholang/tests/setsubtrie_spec.rs` |

---

## 6. Transfer Tasks (Suggested Checklist)

### Phase A — Data model

- [ ] **A1.** Define trie type: `Trie<PathKey, Payload>` — in f1r3node, `PathKey = Vec<u8>`, `Payload = Par` (or your target language’s AST/value type).
- [ ] **A2.** Implement `value_to_path(value) -> Vec<Segment>` mirroring `par_to_path` rules (list = multi-segment; atom = single segment).
- [ ] **A3.** Implement `segments_to_key(segments) -> Vec<u8>` with **0xFF separator** (or document alternative separator strategy).
- [ ] **A4.** Implement `insert(entry)`: `key = segments_to_key(value_to_path(entry))`, `trie[key] = entry`.
- [ ] **A5.** Decide explicit API shape for target project:
  - **Option 1 (current):** literal entries only; path/value conflation for lists.
  - **Option 2 (recommended for new project):** explicit `{ path: [...], value: ... }` or path keys + leaf payload only.

### Phase B — Collection literal / serialization

- [ ] **B1.** Parse `{| ... |}` as ordered set of elements (f1r3node sorts inner elements for canonical form).
- [ ] **B2.** Support remainder / connective metadata if needed (`remainder`, `connective_used`, `locally_free`).
- [ ] **B3.** Round-trip: literal → trie → literal; verify stable semantics for your chosen path/value model.

### Phase C — Trie algebra

Port tests from `models/tests/pathmap_integration_tests.rs`:

- [ ] **C1.** Union (`join`)
- [ ] **C2.** Intersection (`meet`)
- [ ] **C3.** Subtraction (`subtract`)
- [ ] **C4.** Restriction by prefix (`restrict`)

### Phase D — Zipper API

- [ ] **D1.** Read zipper at path prefix; `getSubtrie`, `hasVal`, `pathExists`, `getLeaf`
- [ ] **D2.** Write zipper at path; `setLeaf`, `setSubtrie` (remove keys under prefix, re-insert with prepended `current_path`)
- [ ] **D3.** `graft` — merge foreign trie at current position
- [ ] **D4.** Path management: `createPath`, `prunePath`, `reset` (see `zipper_path_management_spec.rs`)

**Note:** Some `setLeaf` paths in `reduce.rs` currently push to `EPathMap.ps` without full trie update—verify against trie when porting.

### Phase E — Edge cases & validation

- [ ] **E1.** Empty: `{||}`
- [ ] **E2.** Single non-list: `{| 42 |}` — one segment key, value = `42`
- [ ] **E3.** Single-element list: `{| ["some string"] |}` — path `["some string"]`, value = same list
- [ ] **E4.** Prefix overlap: `["a","b"]` and `["a","b","c"]` coexist as distinct keys
- [ ] **E5.** `readZipperAt(["backend"]).getSubtrie()` returns entries whose keys start with prefix (demo 1)
- [ ] **E6.** Reconcile demo expectations if adopting explicit path+value model

---

## 7. Design Decisions for Target Project

### 7.1 Why key and value both exist (even when redundant)

| Role | Key (bytes) | Value (payload) |
|------|-------------|-----------------|
| Purpose | Trie indexing, prefix ops | Canonical source term / rich AST |
| Used by | `get`, prefix scan, algebra | Serialization, connectives, exact round-trip |

For **string-only list entries**, duplication is mostly historical/convenience (single literal form, generic insert). A greenfield design should **not** duplicate unless needed.

### 7.2 Recommended greenfield API (if not tied to Rholang syntax)

```
Entry = { path: Vec<Segment>, value: Value }
Trie key = encode(path)
Trie value = value   // NOT full path list unless value truly is the path
```

Maps cleanly to demo semantics: `path = ["frontend","ui"]`, `value = "done"`.

### 7.3 If must stay compatible with f1r3node

- Keep `par_to_path` + `0xFF` encoding **byte-identical** for cross-node consensus.
- Keep `EPathMap.ps` as `Vec<Par>` flat list for protobuf.
- Document that list literals encode **path only** (all elements), not path+value.

---

## 8. Known Gaps / Technical Debt (f1r3node)

1. **Tests disagree with implementation:** Some tests build `["a", "value1"]` expecting path `["a"]` + value `"value1"`; `par_to_path` uses **all** list elements as path (see comments in `zipper_query_methods_spec.rs`).
2. **`setLeaf` on `EPathMap`:** May append to `ps` without updating trie consistently—confirm in `reduce.rs` before relying on.
3. **Display vs operations:** Zipper stores complete `EPathMap` with `current_path` as byte segments; display may show absolute paths while subtrie ops use prefix keys.
4. **No documented pathmap spec in `docs/`** prior to this file—demo implies domain semantics (status field) not enforced by type system.

---

## 9. Acceptance Criteria (Transfer Done When)

1. Trie insert/lookup/remove matches `create_pathmap_from_elements` behavior for list and non-list entries.
2. Prefix query equivalent to `getSubtrie` at `["backend"]` returns exactly the backend rows from demo PathMap.
3. `setSubtrie` at prefix replaces all keys under prefix and inserts new entries with absolute paths.
4. Collection algebra tests (union/intersection/subtraction/restriction) pass against reference vectors in `pathmap_integration_tests.rs`.
5. Documented decision: **conflated path+value (f1r3node compatible)** vs **explicit path/value (demo-friendly)** — with migration notes.

---

## 10. Prompt Snippet for New Chat

Copy into a new session to resume:

```
I am porting the Rholang PathMap trie from f1r3node. Read SPEC-pathmap-trie-transfer.md.

Key facts:
- Runtime: pathmap::PathMap<Par>, keys = par_to_path(par) segments joined with 0xFF.
- Literal {| ["a","b","c"] |} uses ALL list elements as path segments; stored value is the full Par (redundant for string lists).
- EPathMap.ps is Vec<Par> flat list; trie built on demand via PathMapCrateTypeMapper.
- Demo pathmap-demo.rho assumes last segment is "status" but implementation does NOT split path/value.

Tasks: [pick Phase A–E from spec]. Target: [describe language/runtime].
Compatibility required: [yes/no with f1r3node bytes].
```

---

## 11. References

- Demo: `rholang/examples/pathmap-demo.rho`
- Path encoding: `models/src/rust/pathmap_integration.rs` — `par_to_path`, `create_pathmap_from_elements`
- Mapper: `models/src/rust/pathmap_crate_type_mapper.rs`
- External crate: `pathmap` 0.2.2 (radix trie + zippers)
