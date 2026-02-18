# Lists and Bags: Design for Language Support

**Status:** Design  
**Context:** Types usable in languages such as rhocalc and calculator. List = ordered sequence (duplicates allowed). Bag = multiset (unordered, count-based).

---

## 1. Goal and scope

**Goal:** Add **first-class List and Bag categories** so languages (e.g. rhocalc, calculator) can have list and bag **values**: types that appear in judgements, equations, and rewrites, with literals and operations.

**In scope:**
- Parameterised categories `List(Elem)` and `Bag(Elem)` (or a fixed set such as `List(Int)`, `Bag(Int)`) where `Elem` is an existing category.
- Literal syntax and parsing/display for list and bag values.
- Minimal operations (construct, deconstruct, equality); relation generation (eq_list, eq_bag) and projection relations where needed.
- Mapping to existing runtime types (Vec, HashBag) and element bounds (Eq/Hash for bag elements).
- Use cases: calculator (expressions that evaluate to list/bag of numbers), rhocalc (bag values alongside constructor-based `PPar(HashBag(Proc))`).

**Out of scope:** General collection metasyntax (map/filter/zip); that is covered in collection-metasyntax.md. This doc focuses on first-class list and bag categories and their integration.

---

## 2. Current state

- **Bags:** Represented by `HashBag<T>` in `mettail_runtime`. Used in constructors (e.g. rhocalc `PPar . ps:HashBag(Proc)`). Element type must be `Clone + Eq + Hash`. Equality is multiset equality (same elements, same counts). Parsing/display use `sep` (e.g. `|`); no outer delimiters required.
- **Lists:** Represented by `Vec<T>`. Supported in the macro layer (grammar, types, subst, parser, var inference). Used in constructors (e.g. rhocalc `PInputs . ns:Vec(Name), ...`). Order is significant; equality is element-wise. Parsing typically uses `sep` and optional `delim` (e.g. `[`, `]`).
- **Gap this design addresses:** No first-class List/Bag categories—no `List(Int)` or `Bag(Int)` as a language type with literals and dedicated operations. The design below introduces those categories, reusing Vec and HashBag as the representation.

---

## 3. Semantics and constraints

| Aspect | List (Vec) | Bag (HashBag) |
|--------|------------|---------------|
| Order | Significant | Ignored |
| Duplicates | Allowed | Counted (multiset) |
| Equality | Same length, same elements in order | Same (element, count) pairs |
| Element bounds | Any `Clone` (for term use: `Eq + Hash` if in relations) | `Clone + Eq + Hash` (required by HashBag) |
| Syntax | `[a, b, c]` | `{ a, b, c }` |

**Constraint:** Any type used inside HashBag must implement `Eq` and `Hash`. Categories that use canonical wrappers (e.g. Float) already satisfy this; raw f64 does not. Lists can hold any element type the language defines; if list elements appear in Ascent relations, the same Eq/Hash requirement applies to the inner type.

---

## 4. First-class List and Bag: design choices

### 4.1 Parameterised vs fixed categories

**Parameterised:** `List(Elem)`, `Bag(Elem)` where `Elem` is any existing category. One declaration per collection kind; e.g. calculator could have `List(Int)`, `List(Float)`, `Bag(Int)`.

- **Pros:** Flexible; one mechanism for all element types. Reuses the same List/Bag term constructors and relations modulo element type.
- **Cons:** Macro and type system must support type parameters in categories (new concept). Inner enum and relation generation must instantiate per element type.
- **Risks:** Interaction with existing multi-category design (inner enum, Term) and with constructor parameter types `Vec(Cat)` / `HashBag(Cat)`; name or kind collisions if not clearly separated.

**Fixed:** A fixed set of categories, e.g. `ListInt`, `BagInt`, `ListFloat`, `BagFloat`, each declared like a normal category with a dedicated enum and relations.

- **Pros:** No new parameterised-category machinery; each is a normal category. Easiest to implement with current macro pipeline.
- **Cons:** Proliferation of categories and duplicated term/relation logic per (List/Bag, Elem) pair. Less scalable.

**Recommendation:** Parameterised categories are the right long-term shape; if the macro cannot support them yet, start with one or two fixed instances (e.g. `List(Int)`, `Bag(Int)`) and factor to parameterised once the type system allows it.

---

### 4.2 Representation and element bounds

List and Bag categories are represented by `Vec<T>` and `HashBag<T>` respectively; no new runtime types. Element type `T` is the Rust type of the element category (e.g. the Int enum, or canonical float for Float).

- **List elements:** Must be `Clone`; if list terms appear in Ascent relations, element type must also be `Eq + Hash` (same as today for any category in relations).
- **Bag elements:** Must be `Clone + Eq + Hash` (HashBag requirement). Categories that already work in constructors with HashBag (e.g. Proc with canonical types) already satisfy this.

**Risk:** Introducing a first-class Bag(Elem) for an element type that does not implement Eq/Hash (e.g. a future type without a canonical wrapper) would fail at codegen or at runtime; the language macro or type checker should enforce that only valid element categories can be used in `Bag(Elem)`.

---

### 4.3 Literals and minimal operations

**Literals:** List and bag values need surface syntax, e.g. `[1, 2, 3]` for list, `{ 1, 2, 1 }` for bag. Parsing and display are per-language; the macro must generate or hook into literal rules for the new categories (e.g. a `ListLit` / `BagLit` term or special handling in the parser for these categories).

**Minimal operations:** Keep the first version small to avoid scope creep. Suggested minimum:
- **Construct:** Literal syntax plus possibly a term that builds list/bag from elements (or from another constructor that already produces Vec/HashBag).
- **Deconstruct:** Either pattern matching in rewrites (e.g. rest patterns; see collection-metasyntax.md) or projection relations (e.g. list_nth(List, Int, Elem), bag_count(Bag, Elem, Int)) so that equations/rewrites can inspect contents.
- **Equality:** Generated `eq_list(List, List)` and `eq_bag(Bag, Bag)` (and congruence rules) so that list/bag values participate in equations and rewrites like other categories.

**Risks:** Literal syntax and parsing are language-specific; the design must specify how a language opts in (e.g. by declaring `List(Int)` and a literal rule) and how generated code is wired. Too many operations (cons, snoc, append, count, membership, …) increase implementation and testing cost; stick to the minimal set and add operations later.

---

### 4.4 Relation generation and congruence

For each first-class category `List(Elem)` and `Bag(Elem)` the macro must generate:
- Relations analogous to existing categories: e.g. `list_int(ListInt)`, `eq_list_int(ListInt, ListInt)`, `rw_list_int(ListInt, ListInt)` (and similarly for bag), so that Ascent can store and equate list/bag terms.
- Congruence rules for any term constructors that take list or bag arguments (e.g. if a term is `Cons(e, L)` with `L : List(Int)`, then congruence for the second argument).

Projection relations (list_nth, bag_count) are optional for the first slice but useful for rewrites that need to inspect or deconstruct list/bag values; they can be added in a follow-up.

---

## 5. Implementation outline

1. **Type system / macro:** Add support for parameterised categories (or, as a stepping stone, fixed `ListInt`/`BagInt`). Map `List(Elem)` to `Vec<ElemRust>`, `Bag(Elem)` to `HashBag<ElemRust>` in generated code. Enforce element bounds (Bag elements must be Eq+Hash); reject or document unsupported element categories.
2. **Terms and enums:** Generate enum variants (e.g. `ListLit(Vec<...>)` or a single representation for list/bag values) and ensure they derive Eq, Hash, and any other derives required by the inner enum and Term.
3. **Parser / display:** Add literal rules for list and bag (syntax and delimiters configurable per language). Wire parser actions to build the generated list/bag type; display to emit the chosen surface syntax.
4. **Relations:** Generate `list_*`, `eq_list_*`, `rw_list_*` (and bag equivalents) for each list/bag category. Ensure congruence generation includes list/bag arguments.
5. **Substitution / term_ops:** Extend substitution and other term ops so that list/bag values are traversed and substituted in element positions where the element category has binders or substitution semantics; reuse existing Vec/HashBag traversal where possible.
6. **Tests:** At least one language (e.g. calculator) with a first-class list or bag category: parse literal, equate two list/bag values, run Ascent (relations populated). Optional: one rewrite that deconstructs or uses list/bag.

---

## 6. Summary

The design adds **first-class List and Bag categories** only. List and Bag are types that can appear as values in judgements, equations, and rewrites, with literal syntax and minimal operations (construct, deconstruct, equality). Representation reuses Vec and HashBag; element types must satisfy existing bounds (Eq/Hash for bag elements and for any category used in relations). Main design decisions: parameterised vs fixed categories (prefer parameterised; fixed as stepping stone), minimal operation set to avoid scope creep, and clear integration with relation generation and congruence. Risks: parameterised categories may require macro/type-system changes; literal and operation set must stay scoped so the first slice remains implementable.
