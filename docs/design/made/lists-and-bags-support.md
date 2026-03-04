# Lists and Bags: Design for Language Support

**Status:** Implemented  
**Context:** MeTTaIL → Rholang 1.4; list/bag design aligns with Rholang data structures and arbitrary processes. List = ordered sequence (duplicates allowed). Bag = multiset (unordered). Literal syntax is configurable via open/close/separator delimiters; bag multiplicity is represented by repeated elements (e.g. `{ 1, 1, 2 }`) or, with custom delimiters, by language-specific syntax.

---

## 1. Goal and scope

**Goal:** First-class **List** and **Bag** categories so languages can have list/bag values (literals, operations, judgements, equations, rewrites).

**Scope:** Only **List** and **Bag** with element type **Proc** (i.e. `Vec<Proc>` and `HashBag<Proc>`). No List(Int), Bag(Float), or other typed collections. Same **Proc** type across languages (Calculator, rhocalc). Grammar supports arbitrary Rholang processes and general constructors (user-defined names, delimiters).

---

## 2. Representation and semantics

**Runtime:** List and Bag use the **native Rust types directly** (no separate wrapper): List = `Vec<Proc>`, Bag = `mettail_runtime::HashBag<Proc>`. `HashBag` provides **union**, **remove_one**, and **diff**; list operations use `Vec` methods. Same pattern as other native types (e.g. Int, Float).

**Semantics:** List equality: same length and element-wise equality. Bag = multiset equality (element, count). Element bounds: Bag requires `Clone + Eq + Hash`; List elements in relations need `Eq + Hash`.

**Type declaration (language macro):** In **types**, collection categories are declared as:
- `![Vec<Proc>] as List` — List, default delimiters `[`, `]`, `,`.
- `![mettail_runtime::HashBag<Proc>] as Bag` — Bag, default `{`, `}`, `,`.
- Optional custom delimiters: `as Bag [ "#{", "}#", "|" ]` (e.g. rhocalc). One parameterised PraTTaIL rule per collection kind; element category can differ from collection category (e.g. parse **Proc** into List/Bag via ElemParse frame and `pending_elem` in the trampoline).

**Literals:** Elements separated by the delimiter; empty `[]` and `{}` valid. List: `[ a, b, c ]`. Bag: repeated elements denote multiplicity, e.g. `{ 1, 1, 2 }` = 1 twice, 2 once. Custom delimiters allow language-specific surface syntax (e.g. element|count).

**Rewrites:** **Rewrites allowed everywhere** within list elements (single global policy; no per-list knob). Aligns with [f1r3node/rholang](https://github.com/F1R3FLY-io/f1r3node/tree/rust/dev/rholang) (element-wise normalization).

**Built-in vs user-defined:** "Built-in" = mettail_runtime types and methods (e.g. `HashBag::union`, `remove_one`, `diff`, `count`); "user-defined" = syntax and term rules in each language whose Rust blocks use those types.

| Layer | List | Bag |
|-------|------|-----|
| **Runtime / native type** | `Vec<Proc>` — concat (extend), len, index, delete_at. | `HashBag<Proc>` — **union**, **remove_one**, **diff**, **count**. |
| **User-defined (language)** | Literals `[ ... ]` and term rules (e.g. `concat`, `length`, `at`, `delete`). Languages may add **insert_at**, **take**, **drop**, **filter**, **index_of**. | Literals `{ ... }` (or custom, e.g. `#{ ... }#`) and term rules (**union**, **remove**, **diff**, **count**). |

**Operations (general):** List/bag operations are terms with Rust blocks using the native type API. No equations for list/bag in the initial implementation (congruence only).

---

## 3. Calculator-specific decisions

- **Proc:** Calculator has a unified **Proc** variant; List and Bag inject via **ProcList** and **ProcBag**. All concrete types (Int, Float, Bool, Str, List, Bag) inject into Proc.
- **Proc casts:** Unified **ProcToInt**, **ProcToFloat**, **ProcToBool**, **ProcToStr** (fold rules); they handle Proc variants including **ElemList** (list element at index). Error-free for basic types; panic on unsupported variant or out-of-bounds index.
- **ElemList/DeleteList index:** 0-based; **panic** if out of bounds.
- **Bag remove:** **RemoveBag** removes **one** occurrence.
- **bag_diff:** Multiset difference; no negative counts.

**Example types and terms (snippet):** List literals e.g. `[ 1, 2, 3 ]`; bag literals e.g. `{ 1, 1, 2 }` (repeated elements = multiplicity).

```rust
types {
    Proc
    ![Vec<Proc>] as List
    ![mettail_runtime::HashBag<Proc>] as Bag
    // ... Int, Float, Bool, Str
},
terms {
    ProcList . l:List |- l : Proc ;
    ProcBag  . b:Bag |- b : Proc ;
    ConcatList . a:List, b:List |- "concat" "(" a "," b ")" : List ![{ ... }] fold;
    LenList    . a:List |- "length" "(" a ")" : Int ![a.len() as i32] fold;
    ElemList   . a:List, i:Int |- "at" "(" a "," i ")" : Proc ![{ ... }] fold;
    DeleteList . a:List, i:Int |- "delete" "(" a "," i ")" : List ![{ ... }] fold;
    UnionBag   . a:Bag, b:Bag |- "union" "(" a "," b ")" : Bag ![a.union(&b)] fold;
    RemoveBag  . a:Bag, e:Proc |- "remove" "(" a "," e ")" : Bag ![a.remove_one(&e)] fold;
    DiffBag    . a:Bag, b:Bag |- "diff" "(" a "," b ")" : Bag ![a.diff(&b)] fold;
    CountBag   . b:Bag, e:Proc |- "count" "(" b "," e ")" : Int ![{ HashBag::count(&b, &e) as i32 }] fold;
    ProcToInt  . a:Proc |- "int" "(" a ")" : Int ![{ ... }] fold;  // includes ElemList
    // ... ProcToFloat, ProcToBool, ProcToStr, other casts
}
```

---

## 4. Congruence coverage

**Chosen: Option A — All positions.** Congruence for every argument of every List/Bag/Proc constructor. Rewrites are allowed everywhere within list/bag elements.

**Implementation.** The macro congruence generator branches on collection type: **Vec** (List) uses index-based iteration and replace-at-index rebuild; **HashBag** (Bag) uses iterate, remove one, reinsert. Auto-congruence rules are generated for every constructor and every argument position (simple, collection, binding) for List/Bag/Proc via `congruence::generate_auto_congruence_rules`, in addition to user-declared congruence rules. For languages that inject List/Bag into Proc (e.g. Calculator, rhocalc), congruence on **ProcList** and **ProcBag** (and on each list/bag term's arguments) gives rewrites in all positions. Fold and step rules pass collection payloads through (no literal unwrap for List/Bag in HOL step); collection categories use literal variants **ListLit** and **BagLit**.

---

## 5. Relation generation and Rholang alignment

**Generated:** Category relations, `eq_list_*`, `rw_list_*` (and bag equivalents); congruence for all positions (Option A). Collection categories get **ListLit** / **BagLit** enum variants and fold/step rules that pass payloads. Projection relations (e.g. list_nth, bag_count) can be added later if needed.

**Rholang (f1r3node):** List/Set/Tuple/Map/PathMap = collections of Par; element-wise normalization. Touchpoints: `reduce.rs`, `spatial_matcher.rs`, `list_match.rs`, `collection_normalize_matcher.rs`, `pretty_printer.rs`.

**Reconciliation:** List → List(Proc); Set → Bag(Proc) or Set(Proc); Tuple → List(Proc); Map/PathMap/arbitrary Par to be detailed in proposal.

---

## 6. Implementation (done)

1. **Runtime:** List = `Vec<Proc>`, Bag = `HashBag<Proc>` (native types). `HashBag` extended with **union**, **remove_one**, **diff**. `Language` trait has optional **get_env_term** for exec (e.g. bound names like empty collections).
2. **Macro/types:** `LangType` has optional **collection_kind** (`CollectionCategory::List(delimiters)` / `Bag(delimiters)`). List/Bag map to `Vec<Proc>` and `HashBag<Proc>`; generated enum variants **ListLit**, **BagLit** and relations (eq, rw, congruence). **Substitution** and **term_ops** traverse Vec/HashBag elements.
3. **Parser (PraTTaIL):** One parameterised rule per collection kind (open, close, sep from types). **ElemParse** frame and **pending_elem** when element category ≠ collection category (e.g. Proc inside List/Bag). Empty collection handling (close immediately after open). Trampoline config **has_var** = false for List/Bag.
4. **Languages:** Calculator and rhocalc have List/Bag types, literals, and operations (concat, length/len, at, delete, union, remove, diff, count). rhocalc uses Bag delimiters `#{`, `}#`, `|` and extends **len** to lists; **concat** for strings preserved.
5. **Tests:** `exec_empty_collection.rs` (parse/exec empty list and bag, round-trip); calculator and rhocalc tests updated.

