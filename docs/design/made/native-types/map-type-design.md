# Map Type Design

**Status:** Implemented (Calculator and RhoCalc)  
**Context:** MeTTaIL collection types; List and Bag are implemented with configurable delimiters (defaults `list(…)`, `bag(…)`; see [lists-and-bags-support.md](./lists-and-bags-support.md)).

---

## 1. Goal and Scope

**Goal:** First-class **Map** category for key-value collections — **met** in the current tree.

**Scope:** Map is a native-backed collection type. In source languages you write `![HashMap<Proc, Proc>] as Map` **or** shorthand `![HashMap] as Map`; the macro normalizes both to the runtime newtype `mettail_runtime::HashMapLit<Proc, Proc>` (deterministic `Hash` / `Ord` for Ascent). Default literal delimiters are `map(`, `)`, `,` between entries, and `:` between key and value (see `CollectionCategory::map_defaults()` in `macros/src/ast/language.rs`). Optional `[ "open", "close", "sep", "key_val_sep" ]` overrides the four strings.

---

## 2. Declaration and Parameters

### 2.1 Implicit parameters (as implemented)

**Syntax:** `![HashMap] as Map` **or** explicit `![HashMap<Proc, Proc>] as Map` (both accepted).

**Rationale:** List and Bag use a single element type (`Proc`). Map is fixed to **Proc–Proc** entries for the current languages.

**Effective type:** `mettail_runtime::HashMapLit<Proc, Proc>` in generated code (wrapper around `HashMap` with a stable hasher). Key and value categories are `Proc` for literal parsing and for Calculator / RhoCalc map operations.

| Option | Syntax | Pros | Cons |
|--------|--------|------|------|
| A. Implicit | `![HashMap] as Map` | Minimal; no type syntax to parse; consistent with user preference | Key/value must be Proc; no Map(Int,Str) without extension |
| B. Explicit | `![HashMap<Name,Proc>] as Map` | Flexible; supports typed keys (e.g. Name) | Parsing `HashMap<K,V>` in macro is non-trivial; diverges from List/Bag simplicity |
| C. Single param | `![HashMap<Proc>] as Map` (K=V) | Simpler than B | Restricts to same key/value type; uncommon for maps |

**Decision:** Option A. Implicit `HashMap<Proc, Proc>`. If typed keys/values are needed later, extend with explicit syntax (Option B) as a follow-up.

**Risk:** Languages that need `Map<Name, Proc>` (e.g. name-to-process bindings) cannot use Map in Phase 1. Mitigation: document as limitation; add typed Map in a future iteration if demanded.

---

## 3. Literal Syntax and Default Delimiters

### 3.1 Keyword-Prefixed Disambiguation

Collections are disambiguated by keyword-prefixed delimiters. Defaults:

| Collection | Syntax | Delimiters |
|------------|--------|------------|
| List | `list(1, 2, "hi")` | open `"list("`, close `")"`, sep `","` |
| Bag | `bag(1, 2, 5)` | open `"bag("`, close `")"`, sep `","` |
| Map | `map(1:"hi", 2:"world")` | open `"map("`, close `")"`, entry_sep `","`, key_val_sep `":"` |

Examples: `list()`, `bag(1, 1, 2)`, `map(a:1, b:2)` (empty and non-empty).

#### 3.1.1 RhoCalc Rholang-style Override

To align rhocalc's surface syntax with [Rholang](https://rholang.io), the
`Map` type declaration in `languages/src/rhocalc.rs` overrides the default
delimiters via a braced dictionary (`open_parts`, `close_parts`, `sep`, `key_val_sep`):

```rust
![HashMap<Proc, Proc>] as Map {
    open_parts: ["{"],
    close_parts: ["}"],
    sep: ",",
    key_val_sep: ":",
}
```

Resulting literal forms: `{}` (empty), `{k: v}`, `{k₁: v₁, k₂: v₂}`. An
explicit `Map()` alias is provided for chained method calls
(`Map().set("a", 1).set("b", 2)`).

This override is possible because the rhocalc grammar reserves `{` `}` for
the empty `Map` literal at expression position; the body braces of
`for(…) { P }` and `new(…) in { P }` are absorbed by those keyword-prefixed
rules and never participate in the expression-level `{` dispatch. The
previously-existing braced parallel-composition rule `{ P | Q }` was
**removed**; bare infix `P | Q` (`PParInfix`, folding into `Proc::PPar`) is
the canonical Rholang-style form. See
[exploring/rhocalc-rholang-style-syntax.md](../../exploring/rhocalc-rholang-style-syntax.md).

### 3.2 Delimiter Model

`CollectionDelimiters` has `open_parts`, `close_parts`, `sep`, and for Map `key_val_sep`. Each string in `open_parts` / `close_parts` is a separate lexer terminal, so optional whitespace may appear between adjacent segments (e.g. `Set (`).

| Field | List | Bag | Map |
|-------|------|-----|-----|
| open_parts | `["list", "("]` | `["bag", "("]` | `["map", "("]` |
| close_parts | `[")"]` | `[")"]` | `[")"]` |
| sep | `,` (element separator) | `,` (element separator) | `,` (entry separator) |
| key_val_sep | N/A | N/A | `:` |

**Decision:** `key_val_sep: Option<String>` on `CollectionDelimiters`. Default `":"` for Map; `None` for List/Bag/Set. Parsing and codegen branch on `key_val_sep.is_some()`.

---

## 4. Type System Integration

### 4.1 CollectionCategory

Extend `CollectionCategory`:

```rust
pub enum CollectionCategory {
    List(CollectionDelimiters),
    Bag(CollectionDelimiters),
    Map(CollectionDelimiters),  // key_val_sep must be Some
}
```

Parser and type logic branch on `CollectionCategory::Map`; same pattern as List/Bag.

### 4.2 CollectionType

Extend `CollectionType` in `macros/src/ast/types.rs`:

```rust
pub enum CollectionType {
    HashBag,
    HashSet,
    Vec,
    HashMap,
}
```

Used in `TypeExpr::Collection` and grammar items (e.g. `HashMap(Proc, Proc)` or equivalent).

### 4.3 Native Type Extraction

`element_ident_from_native_type` currently extracts one type parameter (e.g. `Vec<Proc>` -> Proc). For `HashMap<Proc, Proc>`, we need both. Options:

- **A.** New helper `map_params_from_native_type(native_type) -> Option<(Ident, Ident)>` returning `(key_type, value_type)`.
- **B.** Reuse element extraction for value only; key fixed to Proc for implicit case.

**Decision:** For implicit Map, no extraction needed — both are Proc. If explicit `HashMap<K,V>` is added later, implement Option A.

---

## 5. Parser and Trampoline

### 5.1 Parse Model

Map is not a simple `*sep(delim)` collection. Each "element" is a pair `key : value`.

**Options:**

| Option | Model | Pros | Cons |
|--------|-------|------|------|
| A. Pair collection | Parse sequence of `key : value` with `,` between pairs | Reuses collection loop with pair element | Trampoline must handle two subterms per element; `CollectionElem` assumes one |
| B. Nested collection | Outer collection of pairs; pair is `(key, value)` term | Fits existing "element" abstraction | Requires pair syntax or constructor; more complex |
| C. Dedicated Map rule | New grammar rule for Map literal | Clear semantics | New parser path; more codegen |

**Decision:** Option A. Extend the collection machinery to support "pair mode": when `CollectionKind::HashMap`, each element is a `key : value` with two sub-parses. `CollectionElem` frame (or a new `MapEntryElem`) would parse `key : value`, insert `(key, value)` into the map.

**Implementation sketch:** `SyntaxItemSpec::Collection` gains `kind: HashMap` and `key_val_sep`. When `kind == HashMap`, the trampoline parses `key : value` per entry instead of a single element. `insert` becomes `map.insert(key, value)`.

### 5.2 CollectionKind

`prattail` crate has `CollectionKind` (HashBag, HashSet, Vec). Add `HashMap`. Bridge and classify logic map `CollectionCategory::Map` to `CollectionKind::HashMap`.

---

## 6. Runtime and AST

### 6.1 Rust type

Category **Map** uses the wrapper **`HashMapLit<Proc, Proc>`** from `mettail-runtime` (`runtime/src/hashmap_lit.rs`), not a raw `std::collections::HashMap` in the enum payload, so `Eq`/`Hash`/`Ord` match Ascent’s needs.

### 6.2 Enum variant

Generated languages use a **Map** enum with **`MapLit`** payload (e.g. `Map::MapLit` holding `HashMapLit<Proc, Proc>`). Calculator injects maps into **Proc** via **`ProcMap`**; RhoCalc uses **`CastMap`** for `Proc`-level map values.

### 6.3 Congruence and Substitution

- **Congruence:** Map elements are key-value pairs. Congruence on each key and value; map equality is key-wise equality of values.
- **Substitution:** Map over values (and keys if they contain binders). `subst(map, x, t)` = substitute in each key and value.

---

## 7. Delimiter Conflicts

With keyword-prefixed defaults (`list(`, `bag(`, `map(`), collections are lexically distinct. No conflict with PPar (`{`, `}`) or other constructs. Languages may override defaults via a braced delimiter dictionary in the type declaration (see RhoCalc `Bag` / `Map` / `List` in `languages/src/rhocalc.rs`).

---

## 8. Implementation phases (status)

**Done — foundation & parser:** `CollectionCategory::Map`, `CollectionType::HashMap`, `key_val_sep` on `CollectionDelimiters`, `![HashMap] as Map` / `![HashMap<Proc, Proc>] as Map`, default `map(…)` literals, `CollectionKind::HashMap` and trampoline support in PraTTaIL, `MapLit` / `HashMapLit` in generated code.

**Done — operations (at least Calculator):** `get`, `put`, `delete`, `merge`, `has`, `keys`, `values`, `maplength`, plus congruence rules — see `languages/src/calculator.rs`. RhoCalc exposes map operations on **`CastMap`** / `Map::MapLit` in `languages/src/rhocalc.rs`.

**Done — RhoCalc surface alignment with Rholang (May 2026):** brace-delimited
Map literals (`{k: v}`), `Map()` alias, eight-method method-call sugar
(`m.get(k)`, `m.set(k, v)`, `m.contains(k)`, `m.delete(k)`, `m.union(n)`,
`m.size()`, `m.keys()`, `m.values()`), plus `Nil` (replacing `{}` for
`PZero`) and removal of braced `PPar`. Unary methods are implemented via the
extended mixfix detector (1-NT/3+T shape, dispatched inline without a frame
push). See
[exploring/rhocalc-rholang-style-syntax.md](../../exploring/rhocalc-rholang-style-syntax.md).

**Optional later:** extra delimiter overrides per language beyond defaults; pattern matching on maps in rewrite rules (still out of scope for many use cases).

---

## 9. Alternatives Considered

### 9.1 Bracket-Only Syntax

**Rejected.** Bracket-only forms (`[`, `]`, `{`, `}`) cause conflicts with PPar and between collections. Keyword-prefixed defaults (`list(`, `bag(`, `map(`) eliminate ambiguity.

### 9.2 Explicit Parameters from the Start

**Deferred.** `![HashMap<K,V>]` would require parsing generic type parameters in the macro. More complex; implicit Map is sufficient for initial scope.

### 9.3 BTreeMap

**Rejected for Phase 1.** HashMap is standard; ordering is rarely required for initial use. BTreeMap can be added later if ordered iteration is needed.

---

## 10. Open Questions

1. **Ascent decomposition:** How does Map decompose for congruence? Each `(key, value)` pair yields a relation; key equality is part of the equivalence.
2. **Display:** Iteration order of HashMap is unordered. Deterministic output may require sorting by key (needs `Ord` on Proc or key type).
3. **Pattern matching:** Matching on Map in rewrites (e.g. extract a key-value pair) is out of scope for Phase 1; document as future work.
4. **Resolved (May 2026):** Disambiguation between `{}` for PZero and the Map
   literal was resolved by renaming PZero to `Nil`, removing braced `PPar`, and
   reserving `{`...`}` at expression position exclusively for Map literals. See
   [exploring/rhocalc-rholang-style-syntax.md](../../exploring/rhocalc-rholang-style-syntax.md).

---

## 11. References

- [lists-and-bags-support.md](./lists-and-bags-support.md) — List/Bag design
- [exploring/rhocalc-rholang-style-syntax.md](../../exploring/rhocalc-rholang-style-syntax.md) — RhoCalc Rholang-style syntax (Phase 1: Map)
- `docs/manual/language/features/collections/00-overview.md` — Collection pipeline
- `macros/src/ast/language.rs` — `CollectionCategory`, `LangType`, `map_defaults`
- `prattail` — `CollectionKind::HashMap`, collection / map entry parsing in the trampoline
- `languages/src/calculator.rs`, `languages/src/rhocalc.rs` — concrete Map terms and `Proc` injection
