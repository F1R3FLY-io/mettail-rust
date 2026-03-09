# A10: unreachable-equation-variable

**Severity:** Note
**Category:** Ascent / Equation Variables
**Feature Gate:** none (always active)

## Description

Detects variables in rule syntax (captured via `IdentCapture` or `Binder`
items) that appear **only once** and do not match any nonterminal parameter
name, suggesting they may be **unreachable** in the equation's right-hand
side.  In equational reasoning, a variable that is captured on the LHS but
never referenced on the RHS is semantically inert -- it binds a sub-term but
the binding is never used, which often indicates a **typo** in variable names
across the equation's two sides.

```
  Rule: Apply . x:Proc, y:Proc |- x "(" y ")" : Proc;

  If equation is:  Apply(x, y) = Apply(y, x)
  Both x and y are referenced on both sides -> OK

  But if:          Apply(x, y) = Apply(z, x)
  Variable "y" is captured on LHS but absent from RHS -> A10 fires
  Variable "z" appears on RHS but not captured on LHS -> different issue
```

The lint checks each `IdentCapture` and `Binder` parameter name against
the set of `NonTerminal` parameter names in the same rule.  If a capture
name appears exactly once AND does not match any NT parameter name AND
there are multiple captures in the rule, it is flagged.

The requirement for multiple captures avoids false positives on rules with a
single capture (where the variable is trivially the only binding and cannot
be "unreachable" in any meaningful sense).

## Trigger Conditions

All of the following must hold:

- The rule has **more than one** `IdentCapture` or `Binder` parameter.
- A specific capture name appears **exactly once** in the list of captures.
- That capture name does **not** match any `NonTerminal` parameter name in
  the same rule.

One diagnostic is emitted per unreachable variable.

## Example

### Grammar

```rust
language! {
    name: LambdaLang,
    types { ![String] as Expr },
    terms {
        Lam . x:ident, y:ident, body:Expr |- "lam" x y "." body : Expr;
    },
    equations {
        // If equation references "x" and "body" but not "y",
        // then "y" is captured but unreachable in the RHS
        |- Lam(x, y, body) = Lam(x, z, body);
    },
}
```

### Output

```
note[A10] (LambdaLang): variable `x` in rule `Lam` is captured but may not be referenced in RHS
  = hint: check for typos in variable names across equation LHS and RHS

note[A10] (LambdaLang): variable `y` in rule `Lam` is captured but may not be referenced in RHS
  = hint: check for typos in variable names across equation LHS and RHS
```

## Resolution

1. **Fix the typo.**  The most common cause is a misspelled variable name.
   Check the equation's LHS and RHS for matching variable names.  Correcting
   a name like `y` to `z` (or vice versa) will make the binding reachable and
   silence the diagnostic.

2. **Use a wildcard.**  If the variable is intentionally unused (the sub-term
   at that position is irrelevant to the equation), consider renaming it to
   `_` or a convention like `_unused` to signal intent.

3. **Remove the capture.**  If the binding serves no purpose in any equation
   or rewrite, remove the `IdentCapture` / `Binder` from the rule's syntax.
   This simplifies the generated code and avoids confusion.

4. **Ignore the note.**  If the variable is used in a context not visible to
   the lint (e.g., a runtime pattern match that the lint's static analysis
   cannot see), the diagnostic is a false positive and can be safely ignored.

## Hint Explanation

The hint **"check for typos in variable names across equation LHS and RHS"**
targets the most common root cause: a variable is captured under one name in
the rule syntax but referenced under a different (misspelled) name in the
equation.  Since PraTTaIL equations reference variables by name string,
a single-character typo can silently break the binding, causing the equation
to behave differently than intended.

## Related Lints

- [A05](A05-self-referential-equation.md) -- A trivial identity rule where
  all variables are self-referentially matched; A10 detects the complementary
  case where a variable is captured but not used.
- [A06](A06-missing-equation-congruence.md) -- Missing congruence can also
  cause variables to be "dead" in practice even if structurally referenced,
  since equalities cannot propagate through the field.
- [G24](../grammar/G24-alpha-equivalent-rules.md) -- Alpha-equivalent rules
  may share variable names that look unreachable because they are captured
  under different names in different rules.
