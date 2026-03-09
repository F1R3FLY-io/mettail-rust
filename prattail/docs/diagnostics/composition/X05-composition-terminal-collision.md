# X05: composition-terminal-collision

**Severity:** Warning
**Category:** Composition
**Feature Gate:** (none -- always active when composition lints run)

## Description

Detects when the same terminal string is used with different semantic roles
across two composed grammars. A **terminal collision** occurs when grammar A
uses a token (e.g., `+`) as one syntactic construct (e.g., infix operator)
and grammar B uses the same token as a different construct (e.g., prefix
operator or delimiter). While the parser can technically handle this through
WFST-weighted dispatch, the semantic inconsistency may cause confusion and
unexpected parse results.

For each terminal string shared between grammars A and B, the lint collects
the **semantic roles** (infix, prefix, postfix, delimiter, etc.) and the
categories in which each role appears:

    For terminal t ∈ terminals_A ∩ terminals_B:
        roles_A = {role | (category, role) ∈ semantics_A[t]}
        roles_B = {role | (category, role) ∈ semantics_B[t]}

        If roles_A ≠ roles_B:  → terminal collision

```
  Terminal "+"
  ┌────────────────────────────────────┐
  │ Grammar A: infix in [Int]          │
  │ Grammar B: prefix in [Str]         │
  └────────────────────────────────────┘
  Collision: same token, different semantic roles
```

The diagnostic lists all roles and categories from both grammars to help the
author understand the full scope of the collision.

## Trigger Conditions

All of the following must hold:

- Two grammars A and B are composed via the composition lint framework.
- A `CompositionLintContext` is provided with terminal semantics maps from
  both source grammars.
- At least one terminal string appears in both `terminal_semantics_a` and
  `terminal_semantics_b`.
- The set of semantic roles for that terminal differs between A and B
  (i.e., at least one role appears in one grammar but not the other).

One diagnostic is emitted per colliding terminal.

## Example

### Grammar

```rust
// Grammar A: "+" is infix addition in Int
language! {
    name: ArithA,
    types { ![i32] as Int },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int;
    },
}

// Grammar B: "+" is prefix "positive" operator in Float
language! {
    name: ArithB,
    types { ![f64] as Float },
    terms {
        Pos . f:Float |- "+" f : Float;
    },
}
```

### Output

```
warning[X05] (MergedArith): terminal `+` has different semantic roles across grammars: A uses it as [infix] in [Int], B uses it as [prefix] in [Float]
  = hint: consider renaming the terminal in one grammar to avoid semantic confusion in the composed grammar
```

## Resolution

1. **Rename the terminal in one grammar.** Use a distinct token to avoid
   the collision:

   ```
   // In Grammar B, use a different token for "positive"
   Pos . f:Float |- "+." f : Float;
   ```

2. **Unify the semantic roles.** If both grammars should use the same role,
   adjust the rule syntax so the terminal has consistent semantics:

   ```
   // Both grammars use "+" as infix
   Add   . a:Int, b:Int     |- a "+" b : Int;
   AddF  . a:Float, b:Float |- a "+" b : Float;
   ```

3. **Accept the collision.** If the grammars intentionally use the same
   token with different roles in different categories (e.g., `+` is infix
   in numeric categories and prefix in string categories), the warning is
   informational. The WFST dispatch will resolve the ambiguity by category
   context.

## Hint Explanation

> consider renaming the terminal in one grammar to avoid semantic confusion
> in the composed grammar

The hint recommends the simplest fix: choosing a different terminal string
for one of the conflicting uses. When the same token has different semantic
roles (e.g., infix vs prefix), the parser must rely entirely on category
context and WFST weights to disambiguate. While this works mechanically,
it makes the grammar harder to read and reason about. A distinct terminal
for each semantic role eliminates the ambiguity at the lexical level.

## Related Lints

- [X01](X01-composition-ambiguity-introduction.md) -- detects new FIRST set
  tokens introduced by composition (related but measures ambiguity growth,
  not semantic role conflicts)
- [X02](X02-composition-priority-shadowing.md) -- detects priority shadowing
  between rules from different grammars for the same token
- [G10](../grammar/G10-ambiguous-associativity.md) -- single-grammar
  associativity ambiguity (a related form of operator confusion)
