# Binder Implementation Design

## Executive Summary

We will integrate the **moniker** library for proper binding and substitution in MeTTaIL, using its **locally nameless representation**. This is the correct, battle-tested approach for implementing binders in language implementations.

---

## Why Moniker?

### The Locally Nameless Representation

Moniker uses a hybrid approach that combines the best of two worlds:

1. **Free Variables**: Use unique identifiers (like `x$42`)
2. **Bound Variables**: Use De Bruijn indices (like `@1.0`)

### Key Insight from Lambda Calculus Example

```rust
// Lambda: \x => x
Expr::Lam(Scope::new(
    Binder(x.clone()),           // Pattern: what we're binding
    Expr::Var(Var::Free(x))      // Body: initially has free var
))

// Internally after `Scope::new`:
// - Body is "closed": Free(x) → Bound(@0.0)
// - When we unbind: Bound(@0.0) → Free(x') with fresh x'
```

### Why This is Perfect for MeTTaIL

1. **Automatic capture-avoidance**: Moniker handles it
2. **Alpha-equivalence**: Built-in
3. **Substitution**: Correct by construction
4. **Well-tested**: Used in production (Pikelet lang)

---

## Architecture

### Core Types from Moniker

```rust
use moniker::{
    Var,        // Var::Free(x) or Var::Bound(@1.0)
    FreeVar,    // Unique identifier + pretty name
    Binder,     // Declares a binding
    Scope,      // Scope<Pattern, Body>
    BoundTerm,  // Trait for terms with variables
};
```

### MeTTaIL Integration

#### 1. Grammar Syntax (User-facing)

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }
    terms {
        // Binder syntax: (Bind x Name)
        PInput . Proc ::= "for" "(" (Bind x Name) ")" "{" (x)Proc "}" ;
        //                          ^^^^^^^^^^^^^           ^^^
        //                          Binder declaration       Bound var
    }
}
```

#### 2. Generated AST (with Moniker)

```rust
#[derive(Debug, Clone, BoundTerm)]  // Auto-derive from moniker
pub enum Proc {
    PInput {
        // Scope: binds a Name variable in a Proc body
        scope: Scope<Binder<String>, Box<Proc>>
    },
    // ... other variants
}
```

#### 3. Substitution (via Moniker)

```rust
impl Proc {
    pub fn substitute(&self, var: &FreeVar<String>, value: &Proc) -> Proc {
        match self {
            Proc::PInput { scope } => {
                // Unbind the scope
                let (binder, body) = scope.clone().unbind();

                // Check if the bound variable shadows the substitution var
                if &binder.0 == var {
                    // Don't substitute (shadowed)
                    self.clone()
                } else {
                    // Substitute in body, then re-bind
                    let new_body = body.substitute(var, value);
                    Proc::PInput {
                        scope: Scope::new(binder, new_body)
                    }
                }
            }
            // ... other cases
        }
    }
}
```

---

## Implementation Plan

### Phase 1: Add Moniker Dependency

```toml
# runtime/Cargo.toml
[dependencies]
moniker = "0.10"
```

### Phase 2: Update AST for Binders

```rust
// macros/src/ast.rs

#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),

    // NEW: Binder declaration
    Binder {
        var: Ident,        // The variable name (e.g., x)
        category: Ident,   // What type it binds (e.g., Name)
    },

    // NEW: Bound variable usage
    BoundVar {
        var: Ident,        // Which binder this refers to (e.g., x)
    },
}
```

### Phase 3: Parse Binder Syntax

Update parser to recognize:
- `(Bind x Cat)` → `GrammarItem::Binder { var: x, category: Cat }`
- `(x)Term` → `GrammarItem::BoundVar { var: x }`

### Phase 4: Generate Moniker-Based AST

```rust
// For a rule with binders:
PInput . Proc ::= "for" "(" (Bind x Name) ")" "{" (x)Proc "}" ;

// Generate:
#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    PInput(Scope<Binder<String>, Box<Proc>>),
}
```

### Phase 5: Generate Substitution Using Moniker

```rust
impl Proc {
    pub fn substitute(&self, var: &FreeVar<String>, value: &Proc) -> Proc {
        // Use moniker's unbind/rebind operations
    }
}
```

---

## Example: Rho Calculus

### Input Theory

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }
    terms {
        PZero . Proc ::= "0" ;
        PDrop . Proc ::= "*" (Name) ;
        PInput . Proc ::= "for" "(" (Bind x Name) ")" "{" (x)Proc "}" ;
        POutput . Proc ::= (Name) "!" "(" (Proc) ")" ;
        PPar . Proc ::= (Proc) "|" (Proc) ;
        NQuote . Name ::= "@" (Proc) ;
    }
    rewrites {
        // Communication: x!(Q) | for(y){P} => P[Q/y]
        (PPar
            (POutput x (NQuote Q))
            (PInput scope))
        => {
            let (binder, P) = scope.unbind();
            if binder.0 == x {
                P.substitute(&binder.0, &Q)
            } else {
                // Names don't match, no communication
                self.clone()
            }
        }
    }
}
```

### Generated Code

```rust
#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    PZero,
    PDrop(Name),
    PInput(Scope<Binder<String>, Box<Proc>>),
    POutput(Name, Box<Proc>),
    PPar(Box<Proc>, Box<Proc>),
}

#[derive(Debug, Clone, BoundTerm)]
pub enum Name {
    NQuote(Box<Proc>),
}

impl Proc {
    pub fn rewrite_once(&self) -> Option<Proc> {
        match self {
            Proc::PPar(left, right) => {
                match (&**left, &**right) {
                    (
                        Proc::POutput(x, Q),
                        Proc::PInput(scope)
                    ) => {
                        let (binder, P) = scope.clone().unbind();
                        if &binder.0.pretty_name == &x.pretty_name {
                            Some(P.substitute(&binder.0, Q))
                        } else {
                            None
                        }
                    }
                    _ => None
                }
            }
            _ => None
        }
    }
}
```

---

## Benefits

1. **Correctness**: Moniker is battle-tested and theoretically sound
2. **Simplicity**: We don't reimplement substitution from scratch
3. **Performance**: Locally nameless is efficient
4. **Alpha-equivalence**: Free via `BoundTerm::term_eq`
5. **Pretty-printing**: Free variables carry names for debugging

---

## Implementation Steps

### Week 4, Day 1-2: Integration

1. Add moniker dependency to `runtime`
2. Update `GrammarItem` for `Binder` and `BoundVar`
3. Update parser to recognize binder syntax
4. Write tests for parsing

### Week 4, Day 3-4: Code Generation

5. Update `codegen.rs` to generate `Scope<Binder<...>, ...>` fields
6. Add `#[derive(BoundTerm)]` to generated enums
7. Generate substitution using moniker's `unbind`/`Scope::new`

### Week 4, Day 5-6: Rewrite Rules

8. Parse `rewrites { }` blocks
9. Generate rewrite application code
10. Handle pattern matching in rewrite LHS

### Week 4, Day 7: Rho Calculus

11. Define complete Rho Calculus theory
12. Implement communication rewrite
13. End-to-end test: `for(x){*x} | @0!(5)` → `*@5`

---

## References

- [Moniker README](../moniker/README.md)
- [The Locally Nameless Representation](https://www.chargueraud.org/research/2009/ln/main.pdf)
- [Moniker Lambda Calculus Example](../moniker/moniker/examples/lc.rs)

---

**Status**: Ready to implement! This is the correct foundation for binders in MeTTaIL.

