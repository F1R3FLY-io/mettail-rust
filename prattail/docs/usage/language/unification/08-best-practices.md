# Best Practices for Grammar Composition

This document provides guidance on selecting the right composition mechanism for
your use case, identifies common anti-patterns, and offers a step-by-step
migration path from monolithic grammars to composed fragments.

## Decision Tree

The following table maps concrete scenarios to their recommended composition
mechanism with rationale:

| Scenario                                                  | Mechanism                        | Rationale                                             |
|-----------------------------------------------------------|----------------------------------|-------------------------------------------------------|
| Building a language family (core + extensions)            | `extends:`                       | Full semantic inheritance ensures consistency         |
| Sharing syntax across languages with different semantics  | `includes:`                      | Import grammar shape, provide own equations/rewrites  |
| Reusable operator libraries (arithmetic, boolean, string) | `language_fragment!` + `mixins:` | Fragments are lightweight, composable building blocks |
| Combining independently developed languages               | `compose_languages!`             | No recompilation, independent evolution               |
| Programmatic grammar construction in tests/tools          | `compose_languages()` API        | Runtime flexibility, incremental FIRST/FOLLOW         |
| Adding comparison operators across categories             | Cross-category rules             | Automatic dispatch via FIRST set analysis             |
| Allowing one type where another is expected               | Cast rules                       | Implicit type coercion via category embedding         |

## Decision Flowchart

```
Do your grammars share operators (same terminal tokens)?
  |
  +-- Yes --> Do you need shared equations/rewrites?
  |           |
  |           +-- Yes --> extends:
  |           |
  |           +-- No --> Do you have reusable fragments?
  |                       |
  |                       +-- Yes --> mixins:
  |                       |
  |                       +-- No --> includes:
  |
  +-- No --> Do sub-languages need to evolve independently?
              |
              +-- Yes --> compose_languages!
              |
              +-- No --> compose_languages() API
```

## Anti-Patterns

### 1. Deep Cast Chains

```
Int -> Float -> Str -> Proc -> Name -> ...
```

**Problem:** Each additional cast link increases dispatch complexity and WFST
weight. Lint P03 warns when cast depth exceeds 3.

**Fix:** Use direct cast rules for common paths (e.g., `IntToProc` instead of
`Int -> Float -> Str -> Proc`).

### 2. Circular extends

```rust
language! { name: A, extends: [B], ... }
language! { name: B, extends: [A], ... }  // Infinite loop!
```

**Problem:** The registry lookup creates an infinite recursion during macro
expansion.

**Fix:** Ensure extends relationships form a DAG (directed acyclic graph).

### 3. Oversharing with includes

```rust
language! {
    name: Kitchen_Sink,
    includes: [Lang1, Lang2, Lang3, Lang4, Lang5],  // Too many!
    ...
}
```

**Problem:** Importing many grammars creates a massive merged grammar with large
FIRST set overlaps, excessive backtracking, and many dead rules.

**Fix:** Use `language_fragment!` + `mixins:` with minimal, focused fragments.
Or use `compose_languages!` for truly independent sub-languages.

### 4. Duplicate Labels Across Fragments

```rust
language_fragment! { name: Frag1, terms { Add . ... } }
language_fragment! { name: Frag2, terms { Add . ... } }  // Same label!

language! { name: Combined, mixins: [Frag1, Frag2], ... }
// Override: Frag2's Add silently replaces Frag1's Add
```

**Problem:** With `DuplicateStrategy::Override`, the last fragment's definition
wins silently.

**Fix:** Use unique labels across fragments, or use `extends:` (Error strategy)
to catch conflicts.

### 5. Using compose_languages! with Shared Operators

```rust
// Both languages define "+"
compose_languages! { languages: [ArithLang, StringConcatLang] }
```

**Problem:** Delegation tries languages in order. If both parse `"1 + 2"`
successfully, only the first language's parse is returned. The second language
never sees the input.

**Fix:** Use `extends:` or `includes:` so both `+` operators are in the same
parser with proper dispatch.

## Performance Considerations

| Approach                         | Parser Count     | Compilation Cost        | Runtime Cost            | Dispatch          |
|----------------------------------|------------------|-------------------------|-------------------------|-------------------|
| `extends:`/`includes:`/`mixins:` | 1 (merged)       | Higher (larger grammar) | Optimal (single parse)  | WFST-weighted     |
| `compose_languages!`             | N (per-sub-lang) | Lower (independent)     | Higher (sequential try) | Declaration order |
| `compose_languages()` API        | 1 (merged)       | At API call time        | Optimal (single parse)  | WFST-weighted     |

**Merge composition** produces a single parser with WFST-weighted dispatch --
optimal runtime performance but higher compilation cost for large grammars.

**Delegation composition** avoids recompilation but has sequential try-each
overhead. Best when sub-languages have completely disjoint concrete syntax.

## Migration Guide: Monolithic to Composed Fragments

Step-by-step process for converting a monolithic grammar to composed fragments.

### Step 1: Identify Operator Groups

Group rules by semantic domain: arithmetic, boolean, string, comparison,
structural.

### Step 2: Extract Fragments

```rust
// Before: monolithic
language! {
    name: BigLang,
    types { ![i32] as Int, ![bool] as Bool, ![str] as Str },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int;
        Sub . a:Int, b:Int |- a "-" b : Int;
        And . a:Bool, b:Bool |- a "&&" b : Bool;
        Or  . a:Bool, b:Bool |- a "||" b : Bool;
        // ... many more rules
    },
    // ... equations, rewrites, logic
}

// After: fragments + consuming language
language_fragment! {
    name: IntOps,
    types { ![i32] as Int },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int;
        Sub . a:Int, b:Int |- a "-" b : Int;
    },
}

language_fragment! {
    name: BoolOps,
    types { ![bool] as Bool },
    terms {
        And . a:Bool, b:Bool |- a "&&" b : Bool;
        Or  . a:Bool, b:Bool |- a "||" b : Bool;
    },
}

language! {
    name: BigLang,
    mixins: [IntOps, BoolOps],
    types { ![str] as Str },
    terms { /* str-specific and cross-category rules */ },
    equations { /* all equations */ },
    rewrites { /* all rewrites */ },
    logic { /* all logic */ },
}
```

### Step 3: Add Cross-Category Rules in the Consuming Language

Cross-category rules (like `Eq . a:Int, b:Int |- a "==" b : Bool`) should be in
the consuming language, not in fragments, because they reference multiple
categories.

### Step 4: Provide Rewrites in the Consuming Language

Fragments do not carry semantics. Add all equations, rewrites, and logic in the
consuming `language!` definition.

### Step 5: Verify with Tests

Run `cargo test` to verify the composed grammar produces identical parse trees
and evaluation results.

## Pattern: Shared Fragments + Language-Specific Semantics

The recommended architecture for language families:

```
  +----------------+  +----------------+  +----------------+
  | IntOps         |  | BoolOps        |  | StrOps         |
  | (fragment)     |  | (fragment)     |  | (fragment)     |
  +-------+--------+  +-------+--------+  +-------+--------+
          |                    |                    |
          +----------+---------+----------+---------+
                     |                    |
            +--------v-------+   +--------v-------+
            | LangA          |   | LangB          |
            | mixins: [all]  |   | mixins: [all]  |
            | own rewrites   |   | own rewrites   |
            | own logic      |   | own logic      |
            +----------------+   +----------------+
```

Both LangA and LangB share the same syntax (fragments) but define their own
operational semantics (rewrites) and analysis (logic).
