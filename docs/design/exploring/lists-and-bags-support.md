# Lists and Bags: Design for Language Support

**Status:** Design  
**Context:** MeTTaIL → Rholang 1.4; list/bag design must align with Rholang data structures and arbitrary processes. List = ordered sequence (duplicates allowed). Bag = multiset (unordered); literal syntax `{ elem:count, ... }`, e.g. `{ x:2, y:1 }`.

---

## 1. Goal and scope

**Goal:** First-class **List** and **Bag** categories so languages can have list/bag values (literals, operations, judgements, equations, rewrites).

**Scope:** Only **List(Proc)** and **Bag(Proc)**. No List(Int), Bag(Float), or other typed collections. Same **Proc** type across languages (Calculator, rhocalc). Grammar supports arbitrary Rholang processes and general constructors (user-defined names, delimiters).

---

## 2. Representation and semantics

**Runtime:** List = **wrapper type** (newtype around `Vec<Proc>`). Bag = **wrapper type** (newtype around `HashBag<Proc>`). Same pattern as Float ([CanonicalFloat64](https://github.com/F1R3FLY-io/mettail-rust/tree/float-support-ascent)).

**Semantics:** List equality: `eq_list(list1, list2)` iff same length and `eq(list1[k], list2[k])` for all k. Bag = multiset equality (element, count). Element bounds: Bag requires `Clone + Eq + Hash`; List elements in relations need `Eq + Hash`.

**Literals:** Delimiters in **types** section: `![list] as List["open", "close", "sep"]`, `![Bag] as Bag["open", "close", "sep"]` (open, close, separator). Defaults: List `["[", "]", ","]` — e.g. `[ a, b, c ]`. Bag `["{", "}", ","]` — syntax **element:count** pairs, e.g. `{ x:2, y:1 }` (x twice, y once). One **parameterised** PraTTaIL-generated rule per collection kind. Empty `[]` and `{}` are valid.

**Rewrites:** **Rewrites allowed everywhere** within list elements (single global policy; no per-list knob). Aligns with [f1r3node/rholang](https://github.com/F1R3FLY-io/f1r3node/tree/rust/dev/rholang) (element-wise normalization).

**Built-in vs user-defined operations:** As with `CanonicalFloat64`, "built-in" means provided by **mettail_runtime** (wrapper types + methods/trait impls); "user-defined" means syntax and term rules in each language, whose Rust blocks call the built-in type.

| Layer | List | Bag |
|-------|------|-----|
| **Built-in (runtime)** | Wrapper type + **concat**, **len**, **elem_at**, **delete_at** (by index). Implemented as methods or trait impls on the wrapper so any language can call them from term blocks. | Wrapper type + **union**, **remove_one**, **diff**. Same idea: methods/impls on the wrapper. |
| **User-defined (language)** | All **syntax**: literals `[ ... ]` and term rules (e.g. `a "+" b`, `a "[" i "]"`, `"len" "(" a ")"`, `"Delete" "(" a "," i ")"`). Languages may add more terms (e.g. **insert_at**, **take**, **drop**, **filter**, **index_of**) whose blocks use built-in or custom helpers. | All **syntax**: literals `{ elem:count, ... }` and term rules (e.g. `a "+" b`, `"Delete" "(" a "," x ")"`). Users may add terms such as **count** (multiplicity of element), **card** (total count), **contains**, etc. |

**Operations (general):** List/bag operations are **terms with Rust blocks** like any other; their blocks call the built-in wrapper methods/impls. No equations for list/bag in initial implementation (congruence only).

---

## 3. Calculator-specific decisions

- **Proc casts:** Error-free. Example: Proc string → Float: `"2.0"` ⇒ 2.0, `"hello world"` ⇒ 0.0.
- **GetType:** Fixed set: `"Int"`, `"Float"`, `"Bool"`, `"Str"`, `"List"`, `"Bag"`, `"Proc"`.
- **ElemList/DeleteList index:** 0-based; **panic** if out of bounds.
- **DeleteBag:** Remove **one** occurrence.
- **bag_diff:** Multiset difference; no negative counts.

**Example types and terms (snippet):** List literals e.g. `[ 1, 2, 3 ]`; bag literals e.g. `{ x:2, y:1 }`.

```rust
types {
    Proc
    ![list] as List["[", "]", ","]
    ![Bag] as Bag["{", "}", ","]   // literal: { elem:count, ... }
    // ... Int, Float, Bool, Str
},
terms {
    AppendList . a:List, b:List |- a "+" b : List ![concat(a, b)] fold;
    ElemList   . a:List, b:Int |- a "[" b "]" : Proc ![elem_at(a, b)] fold;
    LenList    . a:List |- "len" "(" a ")" : Int ![list_len(a)] fold;
    UnionBag   . a:Bag, b:Bag |- a "+" b : Bag ![bag_union(a, b)] fold;
    DeleteBag  . a:Bag, b:Proc |- "Delete" "(" a "," b ")" : Bag ![bag_remove_one(a, b)] fold;
    GetType    . a:Proc |- "type" "(" a ")" : Str ![type_of_proc(a)] step;
    ProcToFloat. a:Proc |- "float" "(" a ")" : Float ![proc_to_float(a)] step;
    // ... other Proc casts and List/Bag ops
}
```

---

## 4. Congruence coverage

**Chosen: Option A — All positions.** Congruence for every argument of every List/Bag/Proc constructor. This matches the policy that rewrites are allowed everywhere within list/bag elements.

**Congruence premises (implementation).** The macro’s congruence generator currently supports only **HashBag** for collection positions (iterate, remove one, reinsert). To allow rewrites inside **List** literals and align with option A, the generator must branch on collection type: **Vec** uses index-based iteration and replace-at-index rebuild; **HashBag** keeps the existing bag logic. Projection relations (e.g. `*_contains`, `*_nth`) must be generated per collection kind so elements of both List and Bag are visible to rewrites. Option A is then satisfied by auto-generating congruence for every constructor and every argument position (simple, collection, binding) for List/Bag/Proc, in addition to any user-declared congruence rules.

---

## 5. Relation generation and Rholang alignment

**Generated:** `list_*`, `eq_list_*`, `rw_list_*` (and bag equivalents); congruence for all positions (option A). Projection relations (list_nth, bag_count) optional later.

**Rholang (f1r3node):** List/Set/Tuple/Map/PathMap = collections of Par; element-wise normalization. Touchpoints: `reduce.rs`, `spatial_matcher.rs`, `list_match.rs`, `collection_normalize_matcher.rs`, `pretty_printer.rs`.

**Reconciliation (for written proposal):** List → List(Proc); Set → Bag(Proc) or Set(Proc); Tuple → List(Proc); Map/PathMap/arbitrary Par → to be detailed in proposal.

---

## 6. Implementation outline

1. **Runtime:** Add List (wrapper around `Vec<Proc>`) and Bag (wrapper around `HashBag<Proc>`) in mettail_runtime.
2. **Macro/types:** Map List/Bag to wrapper types; generate enum variants and relations (eq_list, eq_bag, congruence).
3. **Parser:** One parameterised PraTTaIL rule for list/bag literals (open, close, sep from types).
4. **Substitution/term_ops:** Traverse list/bag elements; reuse Vec/HashBag traversal.
5. **Tests:** At least one language (e.g. Calculator) with List/Bag: parse literal, equate, run Ascent.

