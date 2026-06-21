# Binder Implementation: Moniker Integration Plan

## Status: Design Complete, Ready for Implementation

---

## Key Insights from Moniker Review

### 1. **Locally Nameless Representation**

Moniker uses a hybrid approach that's perfect for MeTTaIL:

- **Free variables**: `Var::Free(FreeVar { unique_id, pretty_name })`
  - Has a globally unique ID for equality checking
  - Has an optional name for pretty-printing

- **Bound variables**: `Var::Bound(BoundVar { scope, binder, pretty_name })`
  - Uses De Bruijn indices (`scope` = depth, `binder` = index)
  - Automatically avoids capture

### 2. **The Scope Type**

```rust
pub struct Scope<P, T> {
    pub unsafe_pattern: P,    // The binder pattern
    pub unsafe_body: T,        // The term with bound vars
}
```

**Key Operations:**
- `Scope::new(pattern, body)`: Close free vars in body → bound vars
- `scope.unbind()`: Open bound vars → fresh free vars

### 3. **How It Works**

```rust
// Creating a scope (lambda \x => x)
let x = FreeVar::fresh_named("x");
let scope = Scope::new(
    Binder(x.clone()),                  // Pattern: what we bind
    Expr::Var(Var::Free(x.clone()))    // Body: initially free
);

// Inside `Scope::new`:
// 1. body.close_term(...) converts Var::Free(x) → Var::Bound(@0.0)
// 2. Stores the closed body

// When unbinding:
let (binder, body) = scope.unbind();
// 1. Freshens the binder: Binder(x) → Binder(x')
// 2. body.open_term(...) converts Var::Bound(@0.0) → Var::Free(x')
```

### 4. **Substitution is Correct by Construction**

```rust
impl RcExpr {
    fn subst(&self, name: &FreeVar<String>, replacement: &RcExpr) -> RcExpr {
        match *self.inner {
            Expr::Var(ref var) if var == name => replacement.clone(),
            Expr::Var(_) => self.clone(),
            Expr::Lam(ref scope) => {
                // Unbind gets fresh variables automatically!
                let (binder, body) = scope.clone().unbind();
                RcExpr::from(Expr::Lam(Scope::new(
                    binder,
                    body.subst(name, replacement)  // Substitute in body
                )))
            }
            // ...
        }
    }
}
```

**Why this avoids capture:**
1. `unbind()` freshens the binder with a new unique ID
2. The freshened binder can never equal the substitution variable
3. Therefore, no accidental capture!

---

## MeTTaIL Integration Strategy

### Phase 1: Add Moniker ✅ DONE

```toml
# runtime/Cargo.toml
[dependencies]
moniker = { path = "../../moniker/moniker" }
```

```rust
// runtime/src/lib.rs
pub use moniker::{
    Var, FreeVar, Binder, Scope, BoundTerm, BoundPattern,
};
```

### Phase 2: Update AST for Binder Syntax

```rust
// macros/src/ast.rs

#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),

    /// Binder declaration: (Bind x Cat)
    Binder {
        var: Ident,        // Variable name (e.g., x)
        category: Ident,   // What type it binds (e.g., Name)
    },

    /// Bound variable usage: (x)Term
    BoundVar {
        var: Ident,        // Which binder this refers to
    },
}
```

### Phase 3: Parse Binder Syntax

Update `macros/src/ast.rs` parser to recognize:

```rust
// Input:  (Bind x Name)
// Output: GrammarItem::Binder { var: x, category: Name }

// Input:  (x)Proc
// Output: GrammarItem::BoundVar { var: x }
```

### Phase 4: Generate Moniker-Based AST

For a rule with binders:
```rust
PInput . Proc ::= "for" "(" (Bind x Name) ")" "{" (x)Proc "}" ;
```

Generate:
```rust
#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    // Scope binds a Name variable in a Proc body
    PInput(Scope<Binder<String>, Box<Proc>>),
    // ... other variants
}
```

**Key Point**: We use `#[derive(BoundTerm)]` from moniker-derive to auto-generate
the traversal logic!

### Phase 5: Generate Substitution

```rust
impl Proc {
    pub fn substitute(&self, var: &FreeVar<String>, value: &Proc) -> Proc {
        match self {
            Proc::PInput(scope) => {
                let (binder, body) = scope.clone().unbind();
                Proc::PInput(Scope::new(
                    binder,
                    body.substitute(var, value)
                ))
            }
            Proc::PDrop(name) => Proc::PDrop(name.substitute(var, value)),
            // ... other cases
        }
    }
}
```

---

## Example: Rho Calculus End-to-End

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
    equations {
        // Structural congruence
        (PPar P Q) == (PPar Q P)
        (PPar P (PPar Q R)) == (PPar (PPar P Q) R)
        (PPar P PZero) == P
    }
    rewrites {
        // Communication: x!(Q) | for(y){P} => P[Q/y]
        comm:
            (PPar
                (POutput x (NQuote Q))
                (PInput scope))
            => {
                let (binder, P) = scope.unbind();
                if binder.0.pretty_name == x.pretty_name {
                    P.substitute(&binder.0, &Q)
                } else {
                    // Names don't match
                    None
                }
            }
    }
}
```

### Generated AST

```rust
use mettail_runtime::{Var, FreeVar, Binder, Scope, BoundTerm};

#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    PZero,
    PDrop(Name),
    PInput(Scope<Binder<String>, Box<Proc>>),  // ← Moniker scope!
    POutput(Name, Box<Proc>),
    PPar(Box<Proc>, Box<Proc>),
}

#[derive(Debug, Clone, BoundTerm)]
pub enum Name {
    NQuote(Box<Proc>),
}
```

### Generated Rewrite

```rust
impl Proc {
    pub fn rewrite_comm(&self) -> Option<Proc> {
        match self {
            Proc::PPar(left, right) => {
                if let (Proc::POutput(x, q), Proc::PInput(scope)) = (&**left, &**right) {
                    let (binder, p) = scope.clone().unbind();

                    // Check if names match
                    if binder.0.pretty_name.as_ref() == x.pretty_name() {
                        // Perform substitution
                        Some(p.substitute(&binder.0, q))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None
        }
    }
}
```

### Test Case

```rust
#[test]
fn test_rho_communication() {
    use mettail_runtime::FreeVar;

    // Create: @0!(5)
    let five = Proc::PZero;  // Simplified for example
    let zero_name = Name::NQuote(Box::new(five.clone()));
    let output = Proc::POutput(zero_name, Box::new(five));

    // Create: for(x){*x}
    let x = FreeVar::fresh_named("x");
    let body = Proc::PDrop(Name::Var(Var::Free(x.clone())));
    let input = Proc::PInput(Scope::new(
        Binder(x.clone()),
        Box::new(body)
    ));

    // Create: @0!(5) | for(x){*x}
    let parallel = Proc::PPar(
        Box::new(output),
        Box::new(input)
    );

    // Rewrite: should get *@5
    let result = parallel.rewrite_comm().unwrap();
    // Assert result matches expected
}
```

---

## Implementation Timeline

### Days 1-2: Parser and AST ✅ IN PROGRESS

- [x] Add moniker dependency
- [ ] Extend `GrammarItem` for `Binder` and `BoundVar`
- [ ] Update parser to recognize binder syntax
- [ ] Write parser tests

### Days 3-4: Code Generation

- [ ] Update `codegen.rs` to generate `Scope<Binder<...>, ...>` fields
- [ ] Add `#[derive(BoundTerm)]` to generated enums
- [ ] Generate helper functions for construction

### Days 5-6: Substitution and Rewrite Rules

- [ ] Generate substitution methods using `unbind`/`Scope::new`
- [ ] Parse `rewrites { }` blocks in theory syntax
- [ ] Generate rewrite application code

### Day 7: Rho Calculus Test

- [ ] Define complete Rho Calculus theory
- [ ] Implement communication rewrite
- [ ] End-to-end test: `for(x){*x} | @0!(5)` → `*@5`

---

## Benefits of This Approach

1. **Correctness**: Moniker is battle-tested (used in Pikelet)
2. **Simplicity**: We don't reimplement locally nameless from scratch
3. **Performance**: Efficient representation
4. **Alpha-equivalence**: Free via `BoundTerm::term_eq`
5. **Pretty-printing**: Variables carry names for debugging
6. **Type-safety**: Rust's type system prevents misuse

---

## References

- [Moniker Repository](../../moniker/)
- [The Locally Nameless Representation (Paper)](https://www.chargueraud.org/research/2009/ln/main.pdf)
- [Binders Unbound (Paper)](http://www.seas.upenn.edu/~sweirich/papers/icfp11.pdf)
- [Moniker Lambda Calculus Example](../../moniker/moniker/examples/lc.rs)

---

**Next Step**: Extend the AST parser to recognize binder syntax, then update code generation!

