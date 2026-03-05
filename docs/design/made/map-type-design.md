# Map Type Design

**Status:** Design  
**Context:** MeTTaIL collection types; List and Bag already implemented via `![Vec<Proc>] as List` and `![HashBag<Proc>] as Bag`.

---

## 1. Goal and Scope

**Goal:** Add a first-class **Map** category for key-value collections.

**Scope:** Map as a native-backed collection type, declared via `![HashMap] as Map` with implicit key and value types. Collections (List, Bag, Map) are disambiguated by keyword-prefixed delimiters.

---

## 2. Declaration and Parameters

### 2.1 Implicit Parameters

**Proposal:** `![HashMap] as Map` — parameters left implicit.

**Rationale:** List and Bag use single element type (Proc). Map has two parameters (K, V). Making both implicit keeps the declaration minimal and aligns with "leave parameters implicit for all of them."

**Implicit convention:** `HashMap<Proc, Proc>`. Key and value categories are Proc. This matches Proc-centric languages (RhoCalc, Calculator) where all values flow through Proc.

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

### 3.2 Delimiter Model

`CollectionDelimiters` has `open`, `close`, `sep`. Map requires a fourth: `key_val_sep`.

| Field | List | Bag | Map |
|-------|------|-----|-----|
| open | `list(` | `bag(` | `map(` |
| close | `)` | `)` | `)` |
| sep | `,` (element separator) | `,` (element separator) | `,` (entry separator) |
| key_val_sep | N/A | N/A | `:` |

**Decision:** Add `key_val_sep: Option<String>` to `CollectionDelimiters`. Default `":"` for Map; `None` for List/Bag. Parsing and codegen branch on `key_val_sep.is_some()`.

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

### 6.1 Rust Type

`std::collections::HashMap<Proc, Proc>` (or `HashMap<Box<Proc>, Box<Proc>>` if boxing is required for recursion). Use `rustc_hash::FxHasher` / `BuildHasherDefault` if needed for consistency with HashBag.

### 6.2 Enum Variant

`Proc::MapLit(HashMap<Proc, Proc>)` — analogous to `ListLit` and `BagLit`.

### 6.3 Congruence and Substitution

- **Congruence:** Map elements are key-value pairs. Congruence on each key and value; map equality is key-wise equality of values.
- **Substitution:** Map over values (and keys if they contain binders). `subst(map, x, t)` = substitute in each key and value.

---

## 7. Delimiter Conflicts

With keyword-prefixed defaults (`list(`, `bag(`, `map(`), collections are lexically distinct. No conflict with PPar (`{`, `}`) or other constructs. Languages may override defaults via custom delimiters in the type declaration (e.g. `as Bag [ "#{", "}#", "|" ]` for RhoCalc).

---

## 8. Implementation Phases

### Phase 1: Foundation

- Add `CollectionCategory::Map` and `CollectionType::HashMap`
- Extend `CollectionDelimiters` with `key_val_sep: Option<String>`
- Parse `![HashMap] as Map` in types; default delimiters `map(`, `)`, `,`, `:`
- Add `MapLit` variant and `HashMap<Proc, Proc>` to generated enum
- Update List and Bag defaults to `list(`, `)`, `,` and `bag(`, `)`, `,` respectively

### Phase 2: Parser

- Add `CollectionKind::HashMap` in prattail
- Extend trampoline for Map entry parsing (`key : value`)
- Bridge: map `CollectionCategory::Map` to `SyntaxItemSpec::Collection` with `kind: HashMap`

### Phase 3: Operations and Congruence

- Substitution for Map (key and value)
- Congruence for Map
- Basic operations (get, insert, remove) as term rules if needed

### Phase 4: Delimiter Parsing

- Support 4-tuple delimiter syntax for Map: `[ "open", "close", "entry_sep", "key_val_sep" ]`
- Ensure keyword-prefixed defaults (`list(`, `bag(`, `map(`) parse correctly

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

---

## 11. References

- `docs/design/made/lists-and-bags-support.md` — List/Bag design
- `docs/manual/language/features/collections/00-overview.md` — Collection pipeline
- `macros/src/ast/language.rs` — `CollectionCategory`, `LangType`
- `prattail/src/recursive.rs` — `CollectionKind`, collection parse loop
