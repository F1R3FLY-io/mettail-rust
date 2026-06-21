# Corrected Binder Design for MeTTaIL

## The Problem with Original Design

**WRONG:**
```rust
PInput . Proc ::= "for" "(" (Bind x Name) ")" "{" (x)Proc "}" ;
//                          ^^^^^^^^^^^^
// This makes no sense - we're defining PInput in general,
// not for a particular variable "x"
```

The `x` here is a **meta-variable** in the grammar specification, not part of the concrete syntax!

---

## Correct Understanding

### What We're Actually Specifying

In BNF/grammar notation:
- **Meta-variables** (like `x`, `P`, `Q`) are placeholders in the grammar
- **Concrete syntax** (`"for"`, `"("`, etc.) is what appears in actual programs

### Lambda Calculus Example

Traditional notation:
```text
e ::= x              variables
    | λx.e           lambda abstraction (x binds in e)
    | e₁ e₂          application
```

This means:
- `λ` is concrete syntax
- `x` is a **meta-variable** representing "any variable name"
- The `.` indicates that `x` binds in the following `e`

### In Moniker's Rust

```rust
#[derive(Debug, Clone, BoundTerm)]
pub enum Expr {
    Var(Var<String>),                              // x
    Lam(Scope<Binder<String>, RcExpr>),           // λx.e
    //      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //      Scope binds ONE variable in the body
    App(RcExpr, RcExpr),                           // e₁ e₂
}
```

The `Scope<Binder<String>, RcExpr>` means:
- "This constructor binds a String-named variable"
- "The body is an RcExpr"
- No specific variable name is mentioned!

---

## Corrected MeTTaIL Syntax

### Grammar Rule Specification

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }
    terms {
        // Correct: Scope<Category> indicates binding
        PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
        //                          ^^^^^^        ^^^^
        //                          Binder        Body (where Name is bound)

        // Alternative notation (more explicit):
        PInput . Proc ::= "for" "(" Bind<Name> ")" "{" Proc "}" ;

        // Or following the MeTTaIL Scala convention:
        PInput . Proc ::= "for" "(" Name ")" "{" Proc "}" [bind 0 in 1] ;
        //                                                  ^^^^^^^^^^^^
        //                                                  Annotation: arg 0 binds in arg 1
    }
}
```

### Key Insight: Binding is a Property of the Constructor

The binding structure is:
1. **Which argument** is the binder
2. **Which arguments** it binds in

For `PInput`:
- Argument 0 (the Name) is a **binder**
- It binds in argument 1 (the Proc body)

---

## Proposed Syntax Options

### Option 1: Implicit (Scope-based)

```rust
// Use angle brackets to indicate a binder position
PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
//                          ^^^^^^
//                          This Name is a binder for the following Proc
```

**Generated AST:**
```rust
#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    PInput(Scope<Binder<String>, Box<Proc>>),
    // The Scope handles binding automatically
}
```

### Option 2: Explicit Annotation (Like Scala MeTTaIL)

```rust
// Use an attribute to specify binding
PInput . Proc ::= "for" "(" Name ")" "{" Proc "}" ;
#[bind(0, 1)]  // Arg 0 binds in arg 1
```

**Generated AST:**
```rust
#[derive(Debug, Clone, BoundTerm)]
pub enum Proc {
    PInput(Scope<Binder<String>, Box<Proc>>),
}
```

### Option 3: Inline Annotation

```rust
// Inline binding annotation
PInput . Proc ::= "for" "(" Name ")" "{" Proc "}" [bind 0 in 1] ;
```

---

## Recommended: Option 1 (Angle Brackets)

### Why This is Best

1. **Clean syntax**: `<Cat>` clearly marks binders
2. **Unambiguous**: No confusion with meta-variables
3. **Self-documenting**: The rule shows binding structure
4. **Easy to parse**: Simple syntactic marker

### Full Rho Calculus Example

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }
    terms {
        PZero . Proc ::= "0" ;

        PDrop . Proc ::= "*" (Name) ;

        // Input: binds a Name in the Proc body
        PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
        //                          ^^^^^^        ^^^^
        //                          Binder        Body

        POutput . Proc ::= (Name) "!" "(" (Proc) ")" ;

        PPar . Proc ::= (Proc) "|" (Proc) ;

        NQuote . Name ::= "@" (Proc) ;
    }
    equations {
        (PPar P Q) == (PPar Q P)
        (PPar P (PPar Q R)) == (PPar (PPar P Q) R)
        (PPar P PZero) == P
    }
    rewrites {
        // Communication
        comm:
            (PPar
                (POutput x Q)
                (PInput scope))
            => {
                let (binder, P) = scope.unbind();
                // Check if names match (alpha-equivalence)
                if binder.0.pretty_name == x.pretty_name {
                    Some(P.substitute(&binder.0, &Q))
                } else {
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
    PInput(Scope<Binder<String>, Box<Proc>>),  // ← Scope for binding!
    POutput(Name, Box<Proc>),
    PPar(Box<Proc>, Box<Proc>),
}

#[derive(Debug, Clone, BoundTerm)]
pub enum Name {
    // Name is actually a variable! It can be:
    // - Var::Free(x) for free variables
    // - Var::Bound(@n.m) for bound variables
    Var(Var<String>),
    NQuote(Box<Proc>),
}
```

---

## Important Realization: Name is a Variable Category

In Rho Calculus, `Name` is not just an enum - it **contains variables**!

### Revised Grammar

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }
    terms {
        PZero . Proc ::= "0" ;
        PDrop . Proc ::= "*" (Name) ;
        PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
        POutput . Proc ::= (Name) "!" "(" (Proc) ")" ;
        PPar . Proc ::= (Proc) "|" (Proc) ;

        // Name can be a variable or a quoted process
        NVar . Name ::= Var ;           // ← NEW: Names are variables!
        NQuote . Name ::= "@" (Proc) ;
    }
}
```

### Generated AST (Corrected)

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
    NVar(Var<String>),      // ← Can be Free or Bound!
    NQuote(Box<Proc>),
}
```

---

## Comparison with MeTTaIL Scala

Looking at the Scala code, they use `BindNTerminal`:

```scala
case bnt: BindNTerminal => {
    varToCat(bnt.ident_) = bnt.cat_
    hasBind = true
}
```

This suggests a syntax like:
```bnf
PInput ::= "for" "(" BindNTerminal[x, Name] ")" "{" ... "}" ;
```

But we can simplify for MeTTaIL Rust to just:
```rust
PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
```

---

## Implementation Plan (Revised)

### 1. Update AST

```rust
// macros/src/ast.rs

#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),

    /// Binder: <Category> indicates this position binds a variable
    Binder {
        category: Ident,   // What type it binds (e.g., Name)
    },
}

pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident,
    pub items: Vec<GrammarItem>,

    /// Which items are binders, and what they bind in
    /// For example: vec![(0, vec![1])] means item 0 binds in item 1
    pub bindings: Vec<(usize, Vec<usize>)>,
}
```

### 2. Parse Angle Brackets

```rust
// In parser:
// <Name> → GrammarItem::Binder { category: Name }
// Then infer bindings: if item i is a Binder, it binds in item i+1
```

### 3. Generate Scope-Based AST

```rust
// For: PInput . Proc ::= "for" "(" <Name> ")" "{" Proc "}" ;
// Generate:
pub enum Proc {
    PInput(Scope<Binder<String>, Box<Proc>>),
}
```

### 4. Also Need Variable Category

```rust
// Add a special "Var" category
terms {
    // Variables are automatically added for each binder category
    Name: Var<String>  // implicit
}

// Generates:
pub type Name = Var<String>;  // Or embed in enum
```

---

## Next Steps

1. Update `GrammarItem` to have `Binder { category }` (no var name!)
2. Parse `<Cat>` syntax
3. Infer binding structure (which items bind in which)
4. Generate `Scope<Binder<String>, Body>` types
5. Handle variable categories properly

**Key Takeaway**: Binders describe **structure**, not specific variable names. The actual variable names come at **runtime** when constructing terms.

