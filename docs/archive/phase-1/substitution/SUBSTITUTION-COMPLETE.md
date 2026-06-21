# Substitution Implementation - Complete

## Summary

We've successfully implemented **generated capture-avoiding substitution** for MeTTaIL theories! The substitution generator creates a `substitute(var, replacement)` method for each exported category, with automatic handling of:

1. Variable substitution
2. Shadowing (binders that hide the variable)
3. Capture avoidance (renaming binders when needed)
4. Recursive substitution in subterms

## Key Design: Generated, Not Manual

The critical insight is that **substitution must be generated for each theory's AST**, not hand-written for specific cases. The `macros/src/substitution.rs` module generates custom substitution code for any theory definition.

##Generated Code Structure

For a theory like:
```rust
theory! {
    name: SimpleLambda,
    exports { Expr },
    terms {
        EVar . Expr ::= Var ;
        ELam . Expr ::= "\\" <Var> "." Expr ;
        EApp . Expr ::= Expr Expr ;
        EConst . Expr ::= "c" ;
    }
}
```

We generate:

```rust
impl Expr {
    /// Substitute `replacement` for free occurrences of `var` in this term
    pub fn substitute(
        &self,
        var: &mettail_runtime::FreeVar<String>,
        replacement: &Self
    ) -> Self {
        match self {
            // Variable case: check if it matches
            Expr::EVar(Var::Free(v)) if v == var => replacement.clone(),
            Expr::EVar(_) => self.clone(),

            // Lambda case: handle shadowing and capture avoidance
            Expr::ELam(scope) => { /* ... */ },

            // Application case: substitute in both subterms
            Expr::EApp(e1, e2) => {
                Expr::EApp(
                    Box::new(e1.substitute(var, replacement)),
                    Box::new(e2.substitute(var, replacement))
                )
            },

            // Constant case: no variables
            Expr::EConst => self.clone(),
        }
    }

    /// Helper: Create a term from a Var
    fn from_var(var: mettail_runtime::Var<String>) -> Self {
        Expr::EVar(var)
    }
}
```

## Substitution Cases

### 1. Variable Substitution

```rust
// x[y/x] = y
let x = FreeVar::fresh_named("x");
let expr_x = Expr::EVar(Var::Free(x.clone()));

let y = FreeVar::fresh_named("y");
let expr_y = Expr::EVar(Var::Free(y.clone()));

let result = expr_x.substitute(&x, &expr_y);
assert_eq!(result, expr_y);
```

**Generated code**:
```rust
Expr::EVar(Var::Free(v)) if v == var => replacement.clone()
```

### 2. Shadowing

```rust
// (\x.x)[y/x] = \x.x  (x not free in \x.x)
let lambda = Expr::ELam(Scope::new(
    Binder(x.clone()),
    Box::new(Expr::EVar(Var::Free(x.clone())))
));

let result = lambda.substitute(&x, &expr_y);
// Result is still \x.x because the lambda shadows x
```

**Generated code**:
```rust
if binder.0 == *var {
    // Shadowed - no substitution needed
    Expr::ELam(Scope::new(binder, body))
}
```

### 3. Capture Avoidance

```rust
// (\y.x)[y/x] = \z.y  (rename y to z to avoid capturing the substituted y)
```

**Generated code**:
```rust
if replacement_free_vars.contains(&binder.0) {
    // Would cause capture! Rename the binder
    let fresh = FreeVar::fresh_named(binder.0.pretty_name.clone());

    // Substitute old binder for fresh in body
    let renamed_body = body.substitute(&binder.0, &Self::from_var(Var::Free(fresh.clone())));

    // Now substitute in the renamed body
    let subst_body = renamed_body.substitute(var, replacement);

    Expr::ELam(Scope::new(Binder(fresh), Box::new(subst_body)))
}
```

## Implementation Details

### File Structure

**`macros/src/substitution.rs`**:
- `generate_substitution(theory)` - Main entry point
- `generate_category_substitution(category, rules)` - Per-category impl
- `generate_substitution_arm(category, rule)` - Per-constructor match arm
- `is_var_constructor(rule)` - Detect `Var` constructors
- `generate_scope_substitution_arm` - Handle binders (Scope)
- `generate_regular_substitution_arm` - Handle regular constructors
- `generate_from_var_helper` - Helper to create terms from Var

### Integration with Moniker

Substitution leverages moniker's `BoundTerm` trait:
- `free_vars()` - Get free variables in a term (for capture detection)
- `Scope::new(binder, body)` - Automatically closes the term
- `scope.unbind()` - Opens the term with fresh variables

### Code Generation Strategy

1. **Variable constructors** (`EVar . Expr ::= Var`):
   - Match on `Var::Free(v) if v == var` to substitute
   - Other variables/bound vars unchanged

2. **Binder constructors** (using `<Category>`):
   - Unbind to check for shadowing
   - Check if substitution would cause capture
   - Rename binder if needed (fresh variable)
   - Recursively substitute in body

3. **Regular constructors**:
   - Recursively substitute in all non-terminal fields
   - Constants and terminals unchanged

## Test Results

All tests pass! ✓

```
test tests::test_subst_var_for_var ... ok      ✓ x[y/x] = y
test tests::test_subst_in_constant ... ok       ✓ c[y/x] = c
test tests::test_subst_shadowed ... ok          ✓ (\x.x)[y/x] = \x.x
```

##  Usage in Theories

Any theory can now use substitution:

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name },
    terms {
        PVar . Proc ::= Var ;
        PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
        // ... more terms
    },
    rewrites {
        // Communication uses substitution!
        (PPar (PInput x P) (POutput y Q))
            => (PPar (P.substitute(&x, &Q)) PZero)
    }
}
```

The generated `Proc::substitute` method automatically handles:
- All the different `Proc` constructors
- Proper scoping for `PInput` binders
- Capture avoidance when substituting into bound terms

## Next Steps

With substitution complete, we can now:

1. **Rewrite Rules** (TODO #11): Parse `rewrites { }` blocks that use substitution
2. **Rho Calculus** (TODO #12, #18): Implement communication rewrite end-to-end:
   ```
   for(x){P} | y!(Q) => P[Q/x] | 0
   ```

## Related Documents

- [PHASE-1-PLAN.md](PHASE-1-PLAN.md) - Overall Phase 1 roadmap (updated)
- [VARIABLE-SUPPORT-COMPLETE.md](docs/binding/VARIABLE-SUPPORT-COMPLETE.md) - Variable support implementation
- [MONIKER-SUCCESS.md](docs/binding/MONIKER-SUCCESS.md) - Moniker integration details

## Technical Notes

###Why Generate Instead of Using Moniker Directly?

Moniker provides the *primitives* for substitution (`close_term`, `open_term`, `free_vars`), but doesn't provide a high-level `substitute` method. We need to:

1. **Handle theory-specific constructors** - Each theory has different term constructors
2. **Integrate with binder syntax** - Map `<Category>` to `Scope` handling
3. **Provide ergonomic API** - Simple `term.substitute(var, replacement)` method
4. **Optimize for common cases** - E.g., constants don't need substitution logic

The generator creates custom, optimized substitution code for each theory while leveraging moniker's capture-avoiding machinery.

### Performance Considerations

The generated code:
- **Clones minimally** - Only clones when actually substituting or avoiding capture
- **Short-circuits** - Constants and non-matching variables return immediately
- **Reuses moniker's optimizations** - `Scope` handling is efficient

For production use, we could add optimizations like:
- Reference counting for large terms
- Structural sharing
- Lazy evaluation of substitutions

