# G30: isomorphic-wfst-groups

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports groups of categories that have **isomorphic WFST dispatch topology**
-- their prediction WFSTs have identical structure (same states, transitions,
and weight patterns) even though they operate on different categories. This
means the categories share the same parsing dispatch logic and could
potentially share a single WFST instance parameterized over the category
type, reducing generated code size.

The isomorphism analysis is performed during Sprint 8 (canonical WFST
analysis) in the macro phase. It compares the structural fingerprints of
prediction WFSTs across categories and groups those with identical
fingerprints.

```
  Category "Expr"                     Category "Type"
  ┌──────────────────────┐           ┌──────────────────────┐
  │ WFST States: 5       │           │ WFST States: 5       │
  │ Transitions:         │           │ Transitions:         │
  │   "+" → rule1 (0.3)  │           │   "+" → rule4 (0.3)  │
  │   "-" → rule2 (0.5)  │           │   "-" → rule5 (0.5)  │
  │   "*" → rule3 (0.7)  │           │   "*" → rule6 (0.7)  │
  └──────────────────────┘           └──────────────────────┘
        Identical topology → isomorphic WFST group
```

The diagnostic lists each group with its member categories, making it easy
to identify candidates for code deduplication.

## Trigger Conditions

All of the following must hold:

- The macro phase runs WFST analysis (Sprint 8).
- The analysis detects at least one group of two or more categories with
  isomorphic prediction WFSTs.

One diagnostic is emitted per grammar (summary level), listing all isomorphic
groups.

## Example

### Grammar

```rust
language! {
    name: TypedCalc,
    types {
        ![i32] as Int
        ![f64] as Float
    },
    terms {
        AddInt   . a:Int,   b:Int   |- a "+" b : Int;
        SubInt   . a:Int,   b:Int   |- a "-" b : Int;
        AddFloat . a:Float, b:Float |- a "+" b : Float;
        SubFloat . a:Float, b:Float |- a "-" b : Float;
    },
}
```

Both `Int` and `Float` have identical dispatch topology: two tokens (`+` and
`-`), each mapping to one rule, with the same weight structure.

### Output

```
note[G30] (TypedCalc): 1 isomorphic WFST group(s) detected (2 categories total) -- these categories share identical dispatch topology
  group 0: [Float, Int]
  = hint: categories with identical topology can share a single WFST
```

## Resolution

No action is required. This is an informational diagnostic. The compiler can
use this information to optimize code generation.

To exploit the isomorphism:

1. **Parameterize the parser.** If the categories differ only in their
   type parameter, consider using a generic parser function parameterized
   over the category:

   ```rust
   fn parse_binop<T: Category>(input: &str) -> T { ... }
   ```

2. **Share WFST instances.** The compiler could generate a single WFST and
   instantiate it for each category in the group, reducing binary size.

3. **Accept as informational.** If code size is not a concern, the
   diagnostic is purely informational and requires no action.

## Hint Explanation

> categories with identical topology can share a single WFST

The hint explains that when multiple categories have structurally identical
prediction WFSTs, the generated dispatch code is duplicated. A single WFST
template, instantiated per category, would reduce both generated code size
and compilation time. This is analogous to template instantiation in C++:
the same generic dispatch logic is shared, with only the category-specific
rule labels varying.

## Related Lints

- [G32](G32-prefix-isomorphism.md) -- detects categories with structurally
  identical dispatch **tries** (the PathMap-based decision tree counterpart
  of WFST isomorphism)
- [G29](G29-dependency-groups.md) -- fine-grained dependency groups (a
  different structural analysis)
- [G28](G28-alpha-equivalent-groups.md) -- alpha-equivalent LHS pattern
  groups (rule-level structural sharing)
