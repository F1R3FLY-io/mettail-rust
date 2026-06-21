# Substitution in Rewrite Rules - Complete ✅

**Date:** 2025-10-26
**Status:** DONE

---

## Summary

Successfully implemented **substitution expressions** (`subst`) in rewrite rules! This allows rewrite rules to express term transformations that involve variable substitution, which is essential for implementing operational semantics like communication in Rho Calculus.

## What Was Implemented

### 1. Extended `Expr` AST

Added `Subst` variant to expression AST:

```rust
pub enum Expr {
    Var(Ident),
    Apply { constructor: Ident, args: Vec<Expr> },
    Subst {              // NEW
        term: Box<Expr>,        // Term to substitute into
        var: Ident,             // Variable to replace
        replacement: Box<Expr>, // What to replace with
    },
}
```

### 2. Parsing

Extended `parse_expr` to recognize `subst`:

```rust
// Syntax: (subst term var replacement)
(subst P x (NQuote Q))  // Substitute @Q for x in P
```

**How it works:**
- When parsing `(constructor args...)`, check if `constructor == "subst"`
- If yes, parse three components: term (expr), var (ident), replacement (expr)
- Otherwise, parse as regular constructor application

### 3. Validation

Extended validator to handle `Subst`:

```rust
Expr::Subst { term, var: _, replacement } => {
    validate_expr(term, theory)?;
    validate_expr(replacement, theory)?;
    // var is just an identifier, no validation needed
    Ok(())
}
```

Also updated `collect_vars` to include variables from all three components.

### 4. Type-Checking

Implemented sophisticated type-checking for substitution:

**Key insight:** The variable and replacement must have the **same type**, but that type is independent of the term's type.

```rust
// Example: subst(P:Proc, x:Name, @Q:Name) is valid
//   We're replacing Name x with Name @Q inside Proc P
//   Result type is Proc (same as term type)

Expr::Subst { term, var, replacement } => {
    let term_type = infer_type(term, context)?;
    let replacement_type = infer_type(replacement, context)?;

    // Variable and replacement must have same type
    if let Some(var_type) = context.get(var) {
        check_type(replacement_type, var_type)?;
    } else {
        context.insert(var, replacement_type);
    }

    // Result has same type as term
    Ok(term_type)
}
```

### 5. Rho Calculus Example

Successfully implemented communication with substitution:

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name },
    terms {
        PZero . Proc ::= "0" ;
        PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        PPar . Proc ::= Proc "|" Proc ;
        PDrop . Proc ::= "*" Name ;
        NQuote . Name ::= "@" Proc ;
        NVar . Name ::= Var ;
    },
    equations {
        (PPar P Q) == (PPar Q P) ;
        (PPar P PZero) == P ;
    },
    rewrites {
        // Communication: for(x){P} | y!(Q) => P[@Q/x] | 0
        if x # Q then (PPar (PInput x P) (POutput y Q))
            => (PPar (subst P x (NQuote Q)) PZero)
    }
}
```

**This compiles successfully!** ✅

## Test Results

```bash
$ cargo run --bin test_rho_rewrites
Rho Calculus with substitution in rewrites compiled successfully!
  - Parsed subst(P, x, y) in rewrite rules
  - Type-checked substitution expressions
  - Validated freshness constraints

Rewrite rule:
  if x # Q then: for(x){P} | y!(Q) => P[@Q/x] | 0
  Syntax: (subst P x (NQuote Q)) represents P[@Q/x]
  Type-checks: x and @Q are both Names, P is a Proc

✓ Substitution in rewrite rules working!
```

All existing tests still pass! ✅

## Type-Checking Examples

### Valid:
```rust
// P:Proc, x:Name, @Q:Name => Proc
(subst P x (NQuote Q))  ✅

// E:Expr, y:Var, z:Var => Expr
(subst E y z)  ✅
```

### Invalid:
```rust
// P:Proc, x:Name, Q:Proc => TYPE ERROR
// Can't substitute Proc for Name
(subst P x Q)  ❌
```

## What's Still NOT Implemented

This implementation handles **syntax, parsing, and validation** of substitution in rewrites. What's not implemented:

- ❌ **Rewrite application/evaluation** - Actually running rewrites on terms
- ❌ **Pattern matching** - Matching LHS against concrete terms
- ❌ **Rewrite strategies** - How/when to apply rewrites

These are for future phases - Phase 1 was about getting the **foundation** right, which is now complete!

## Technical Details

### Substitution Semantics

The `subst` expression in rewrites is **declarative**, not operational:

```rust
rewrites {
    LHS => (subst P x Q)
}
```

This **declares** that the rewrite produces a term where `Q` is substituted for `x` in `P`. The actual substitution is performed by the generated `.substitute()` method we implemented earlier!

**Connection to generated code:**
```rust
// The rewrite rule says:
(subst P x (NQuote Q))

// This MEANS (at runtime):
P.substitute(&x_as_freevar, &NQuote(Q))
//            ^^^^^^^^^^^^^^  ^^^^^^^^^^^^
//            from moniker    generated AST
```

So `subst` in rewrites is syntax-level, while `.substitute()` is the runtime operation.

### Why This Design?

1. **Separation of concerns**: Rewrite syntax is declarative, implementation is generated
2. **Type safety**: Substitution is validated at macro expansion time
3. **Flexibility**: Can extend with other operations (e.g., `apply`, `unfold`, etc.)
4. **Correctness**: Leverages proven `moniker` library for capture avoidance

## Files Modified

- `macros/src/ast.rs` - Added `Expr::Subst`, parsing
- `macros/src/validator.rs` - Added validation for subst
- `macros/src/typechecker.rs` - Added type-checking for subst
- `examples/test_rho_rewrites.rs` - Updated with substitution example
- `docs/PHASE-1-PLAN.md` - Updated (coming next)

## Phase 1 Status

**COMPLETE!** 🎉

All major features implemented:
1. ✅ Type-Checking
2. ✅ Equations
3. ✅ Parser Generation (basic)
4. ✅ Binders & Variables
5. ✅ Substitution
6. ✅ Rewrite Rules
7. ✅ **Rho Calculus with Communication**

---

**Time:** 1 day (faster than expected due to reusing equation infrastructure)

**Next:** Phase 2 - Rewrite application, pattern matching, more examples!

