# G28: alpha-equivalent-groups

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports the total number of **alpha-equivalent LHS pattern groups** detected
across the entire grammar during the pattern trie analysis phase (Sprint 6).
An alpha-equivalent group is a set of rules whose LHS patterns are identical
up to variable renaming -- they share the same De Bruijn encounter-order
encoding, meaning they have identical matching structure despite using
different variable names.

This is a **summary-level** lint emitted once per grammar by the macro phase.
It aggregates the results of `find_alpha_equivalent_groups()` from the
`PatternIndex` and reports the group count and total rule count. The per-rule
counterpart is [G24](G24-alpha-equivalent-rules.md), which fires in the
pipeline phase for individual groups within categories.

```
  Alpha-equivalent group 1:          Alpha-equivalent group 2:
  ┌─────────────────────────┐       ┌─────────────────────────┐
  │ Add(x, y)   [eq #1]    │       │ Neg(a)      [rw #3]     │
  │ Plus(a, b)  [eq #2]    │       │ Minus(z)    [rw #4]     │
  └─────────────────────────┘       └─────────────────────────┘
  Same De Bruijn encoding           Same De Bruijn encoding

  G28 reports: "2 alpha-equivalent LHS pattern group(s) detected (4 rules total)"
```

The alpha-equivalent groups are useful for two optimizations:

- **Shared matching code**: rules in the same group can share a single
  pattern-matching function, reducing generated code size.
- **Redundancy detection**: if rules in the same group also have identical
  RHS expressions (up to renaming), they are redundant and can be merged.

## Trigger Conditions

All of the following must hold:

- The grammar defines equations or rewrites.
- The `PatternIndex` is built and `find_alpha_equivalent_groups()` returns
  at least one group with 2 or more rules.

One diagnostic is emitted per grammar (summary level).

## Example

### Grammar

```rust
language! {
    name: Lambda,
    types { ![Term] as Term },
    terms {
        App   . f:Term, x:Term |- f x : Term;
        Lam   . x:Term |- "\\" x "." x : Term;
    },
    equations {
        // These two equations have alpha-equivalent LHS patterns:
        BetaXY . f:Term, x:Term |- App(Lam(f), x) = f;
        BetaAB . g:Term, a:Term |- App(Lam(g), a) = g;
    },
}
```

### Output

```
note[G28] (Lambda): 1 alpha-equivalent LHS pattern group(s) detected (2 rules total) -- these rules share identical matching structure
  = hint: rules in each group can share pattern-matching code; consider merging redundant rules
```

## Resolution

No action is required. This is an informational diagnostic. The compiler
uses the alpha-equivalent group information internally to optimize codegen.

If the redundancy is unintended:

1. **Merge redundant rules.** If rules in the same group have identical RHS
   expressions (up to renaming), keep only one:

   ```
   equations {
       Beta . f:Term, x:Term |- App(Lam(f), x) = f;
       // Remove BetaAB -- it is alpha-equivalent to Beta
   }
   ```

2. **Differentiate the patterns.** If the rules should be distinct, add
   structural differences to their LHS patterns.

## Hint Explanation

> rules in each group can share pattern-matching code; consider merging
> redundant rules

The hint communicates two points: (1) the compiler can exploit the shared
structure for code generation optimization (generating one match function
shared by all rules in the group), and (2) the author should review whether
the alpha-equivalent rules are intentionally distinct or represent accidental
duplication that can be reduced.

## Related Lints

- [G24](G24-alpha-equivalent-rules.md) -- per-category alpha-equivalence
  detection in the pipeline phase (fires for individual groups, not a
  summary)
- [G07](G07-identical-rules.md) -- detects rules with identical string
  signatures (a stricter check that G24/G28 extend to variable-renamed
  patterns)
- [G29](G29-dependency-groups.md) -- fine-grained dependency groups (a
  different structural analysis from the same pattern trie infrastructure)
