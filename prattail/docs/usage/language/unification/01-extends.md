# Full Language Inheritance (`extends:`)

## Intuition

"extends is like class inheritance -- you get everything from the base." When language B extends language A, B inherits A's types, terms, equations, rewrites, and logic rules. B can add its own definitions but cannot override A's (DuplicateStrategy::Error).

## Why Important

- Language families where a core grammar is shared (e.g., BaseMath -> ExtMath)
- Additive extensions that build on established semantics
- Shared operational semantics (equations and rewrites are inherited)

## Syntax

```rust
language! {
    name: ExtMath,
    extends: [BaseMath],      // Inherit everything from BaseMath
    types { },                // Additional types (or empty to inherit all)
    terms { },                // Additional terms
    equations { },            // Additional equations
    rewrites { },             // Additional rewrites
}
```

Multiple bases: `extends: [Base1, Base2]` -- applied left-to-right, each with DuplicateStrategy::Error.

## Merge Semantics

- `DuplicateStrategy::Error` -- same label in both base and extension is a compilation error
- What gets merged: types, terms, equations, rewrites, logic (everything)
- `merge_language_defs(base, extension, DuplicateStrategy::Error)` in `macros/src/ast/merge.rs`
- `apply_extends()` is called during macro expansion, before validation

## Merge Algorithm Pseudocode

```
fn apply_extends(def):
    for base_name in def.extends_names:
        base = REGISTRY.lookup(base_name)
        def = merge_language_defs(base, def, Error)?
    def.extends_names.clear()
    return def

fn merge_language_defs(base, ext, strategy):
    types = merge_types(base.types, ext.types)    // union by name, check native_type match
    terms = merge_terms(base.terms, ext.terms, strategy)    // Error strategy rejects duplicates
    equations = merge_equations(base.equations, ext.equations, strategy)
    rewrites = merge_rewrites(base.rewrites, ext.rewrites, strategy)
    logic = merge_logic(base.logic, ext.logic)    // union relations, concatenate content
    return LanguageDef { types, terms, equations, rewrites, logic, ... }
```

## End-to-End Example

From `languages/src/composition/base_lang.rs` and `extended_lang.rs`:

**BaseMath** (base):
```rust
language! {
    name: BaseMath,
    types { ![i32] as Num },
    terms {
        Add . a:Num, b:Num |- a "+" b : Num;
        Sub . a:Num, b:Num |- a "-" b : Num;
    },
    rewrites {
        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);
        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);
        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);
        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);
    },
}
```

**ExtMath** (extension):
```rust
language! {
    name: ExtMath,
    extends: [BaseMath],
    types { },
    terms { },
}
```

**Result**: ExtMath has the same types (Num), terms (Add, Sub), and rewrites (AddCongL, etc.) as BaseMath. ExtMath can parse `1 + 2 - 3` and evaluate using the inherited rewrite rules.

## Error Cases

| Error                        | Condition                                  | Example                                        |
|------------------------------|--------------------------------------------|------------------------------------------------|
| `CategoryNativeTypeMismatch` | Same category name, different native types | Base: `![i32] as Num`, Ext: `![i64] as Num`    |
| `DuplicateRuleLabel`         | Same rule label in both                    | Base has `Add`, Ext also defines `Add`         |
| `DuplicateEquationName`      | Same equation name in both                 | Base has `CommAdd`, Ext also defines `CommAdd` |

## Diagram: Merge Data Flow

```
  ┌───────────┐     ┌───────────┐
  │ BaseMath  │     │ ExtMath   │
  │           │     │           │
  │ types:    │     │ types:    │
  │  Num{i32} │     │  (empty)  │
  │ terms:    │     │ terms:    │
  │  Add, Sub │     │  (empty)  │
  │ rewrites: │     │ rewrites: │
  │  4 congs  │     │  (empty)  │
  └─────┬─────┘     └─────┬─────┘
        │                 │
        └────────┬────────┘
                 │
                 ▼
    merge_language_defs(base, ext, Error)
                 │
                 ▼
    ┌───────────────────────────────┐
    │ Merged LanguageDef            │
    │                               │
    │ types: Num{i32}               │
    │ terms: Add, Sub               │
    │ rewrites: AddCongL, AddCongR, │
    │           SubCongL, SubCongR  │
    └──────────────┬────────────────┘
                   │
                   ▼
           run_pipeline()
                   │
                   ▼
           Generated Parser
```

## Integration

The merged `LanguageDef` flows through the entire PraTTaIL pipeline:
1. `project_to_language_spec()` -> `LanguageSpec`
2. `run_pipeline()`: Extract -> Generate (FIRST/FOLLOW, WFST, lint, codegen) -> Finalize
3. Result: a single parser that handles all rules from both base and extension
