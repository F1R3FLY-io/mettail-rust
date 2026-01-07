# HOL Syntax for MeTTaIL

**Status:** Design Phase  
**Date:** January 2026  
**Revision:** 3

---

## 1. Motivation

### 1.1 From BNFC-Style to Judgement Syntax

MeTTaIL currently uses BNFC-inspired syntax for term constructors:

```rust
PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
```

This becomes awkward when dealing with lambda abstractions. Type theory uses a clearer syntax for judgements:

```
Γ (term context) ⊢ term : Type
```

For example, the rho-calculus input constructor:

```
PInput . n:Name, \x.p:[Name->Proc] |- for(x<-n){p} : Proc
```

This syntax makes explicit:
- **Label**: `PInput` — the Rust enum variant name
- **Context**: term parameters (`n:Name`) and abstractions (`\x.p:[Name->Proc]`)
- **Syntax pattern**: `for(x<-n){p}` — the concrete syntax, using identifiers from the context
- **Result type**: `Proc`

### 1.2 The Core Problem

The current `<Name>` binder syntax is **implicit** and **positional**:
- Binding scope is inferred (binder binds in next non-terminal)
- Cannot express function types
- Cannot nest abstractions (`\x.\y.p`)
- Cannot express higher-order functions (functions as arguments)
- Cannot express multi-binders (binding a list of names)

First-class lambda abstractions require:
- Named abstraction parameters with explicit types
- Nested/multiple abstractions
- Higher-order function types (functions as arguments)
- Multi-binders (binding multiple names at once)
- Meta-syntax for describing collection patterns

---

## 2. Design Goals

1. **Judgement-style syntax** for constructor declarations
2. **First-class function types**: `[A -> B]` as valid types
3. **Nested abstractions**: `\x.\y.p:[A -> [B -> C]]`
4. **Higher-order abstractions**: functions that take functions as arguments
5. **Multi-binders**: `\[xs].p:[[Name] -> Proc]` binds a list of names
6. **Meta-syntax**: `#sep`, `#zip`, `#map` for compile-time grammar generation
7. **Bidirectional**: syntax patterns generate both parser and display
8. **Meta-level lambda**: `dup = \n:Name. ...` for reusable term templates
9. **Clean migration**: from current BNFC-style syntax

---

## 3. Type System

### 3.1 Type Grammar

```
Type ::= Ident                    -- base type: Name, Proc
       | "[" Type "->" Type "]"   -- function type: [Name -> Proc]
       | "[[" Type "]]"           -- multi-binder domain: [[Name]]
       | CollType "(" Type ")"    -- collection type: Vec(Name)

CollType ::= "Vec" | "HashBag" | "HashSet"
```

Examples:
```
Name                     -- base type
Proc                     -- base type
[Name -> Proc]           -- function from Name to Proc
[[Name] -> Proc]         -- function from list of Names to Proc (multi-binder)
[Name -> [Name -> Proc]] -- curried function (nested abstraction)
[[Proc -> Proc] -> Proc] -- higher-order: takes a function argument
Vec(Name)                -- vector of names (collection)
HashBag(Proc)            -- multiset of processes
```

### 3.2 Type Representationn

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    /// Base type: Name, Proc
    Base(Ident),
    
    /// Function type: [Domain -> Codomain]
    Arrow {
        domain: Box<TypeExpr>,
        codomain: Box<TypeExpr>,
    },
    
    /// Multi-binder domain: [[A]] means "list of binders of type A"
    MultiBinder(Box<TypeExpr>),
    
    /// Collection type: Vec(T), HashBag(T)
    Collection {
        coll_type: CollType,
        element: Box<TypeExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CollType {
    Vec,
    HashBag,
    HashSet,
}
```

### 3.3 Single Binder vs Multi-Binder

**Single binder** — binds one variable of a given type:
```
\x.p:[Name -> Proc]
```
- `x` is one variable of type `Name`
- `x` is free in body `p`
- Substitution replaces `x` with one `Name` value

**Multi-binder** — binds a list of variables:
```
\[xs].p:[[Name] -> Proc]
```
- `xs` represents variables `x0, x1, ..., xk` each of type `Name`
- All `xi` are free in body `p`
- Length is determined at parse time from syntax
- Runtime type: `Scope<Vec<Binder<String>>, Box<Proc>>`

**Important distinction:**
- `\xs.p:[Vec(Name) -> Proc]` — ONE binder `xs` of type `Vec(Name)`
- `\[xs].p:[[Name] -> Proc]` — LIST of binders, each of type `Name`

These are semantically different. Multi-binder is needed for multi-channel input.

---

## 4. Constructor Syntax

### 4.1 General Form

```
Label . term-context |- syntax-pattern : Type ;
```

Where:
- `Label` — the Rust enum variant name (required)
- `term-context` — comma-separated parameters and abstractions
- `|-` — turnstile separating context from syntax
- `syntax-pattern` — concrete syntax with meta-operations
- `Type` — the result type

### 4.2 Parameter Forms

**Term parameter** — a sub-term of given type:
```
n:Name          -- parameter n of type Name
ps:HashBag(Proc)  -- parameter ps of type HashBag(Proc)
```

**Single abstraction** — binds one variable:
```
\x.p:[Name -> Proc]     -- x binds in p
```

**Named abstraction** — when you need to reference the whole abstraction:
```
f = \x.y:[Proc -> Proc]  -- f names the abstraction; x binds in y
```

**Multi-binder abstraction** — binds multiple variables:
```
\[xs].p:[[Name] -> Proc]  -- xs represents x0, x1, ... binding in p
```

**Nested abstraction** — multiple binding levels:
```
\x.\y.p:[Name -> [Name -> Proc]]  -- x binds in (y binds in p)
```

### 4.3 Examples

```rust
terms {
    // Nullary constructor
    PZero . |- 0 : Proc ;
    
    // Unary constructor
    PDrop . n:Name |- *(n) : Proc ;
    
    // Binary constructor  
    POutput . n:Name, p:Proc |- n!(p) : Proc ;
    
    // Single abstraction
    PInput . n:Name, \x.p:[Name->Proc] |- for(x<-n){p} : Proc ;
    
    // Multi-binder abstraction
    PInputs . ns:Vec(Name), \[xs].p:[[Name]->Proc] 
            |- for( #zip(ns,xs).#map(|n,x| x<-n).#sep(,) ){p} : Proc ;
    
    // Collection
    PPar . ps:HashBag(Proc) |- { ps.#sep("|") } : Proc ;
    
    // Nested abstraction
    PLam2 . \x.\y.p:[Name -> [Name -> Proc]] |- lam(x,y){p} : Proc ;
    
    // Higher-order (named abstraction)
    PMap . f = \x.y:[Proc->Proc], ps:HashBag(Proc) |- map(f){ps} : Proc ;
    
    // Quote
    NQuote . p:Proc |- @(p) : Name ;
}
```

---

## 5. Meta-Syntax

### 5.1 Purpose

Meta-syntax is **compile-time template expansion** that generates:
1. **LALRPOP parser rules** (syntax → AST)
2. **Display implementations** (AST → syntax)

Meta-syntax is NOT runtime. All `#` operations are resolved at macro expansion time.

### 5.2 Core Meta-Functions

| Function | Description | Parser Output | Display Output |
|----------|-------------|---------------|----------------|
| `#sep(coll, sep)` | Join elements with separator | Separated list grammar | Join with separator |
| `#zip(a, b)` | Pair corresponding elements | Paired grammar | N/A (intermediate) |
| `#map(coll, fn)` | Transform each element | Mapped grammar | Mapped format |
| `#opt(x)` | Optional element | Optional grammar | Display if present |

### 5.3 Closures in meta-syntax

Meta-syntax abstractions use Rust closure syntax `|args| expr` (for clear distinction with lambdas):

```rust
// Single argument
#map(xs, |x| x)

// Multiple arguments (from zip)
#zip(ns, xs).#map(|n,x| x<-n)
```

Meta-functions can chain with `.#`:

```rust
#zip(ns, xs).#map(|n,x| x<-n).#sep(",")

// Equivalent to:
#sep(#map(#zip(ns, xs), |n,x| x<-n), ",")
```

### 5.4 Generated Parser (Example)

For `PPar . ps:HashBag(Proc) |- { ps.#sep("|") } : Proc`:

```lalrpop
PPar: Proc = {
    "{" <ps:(<Proc> "|")*> <last:Proc?> "}" => {
        let mut bag = HashBag::new();
        for p in ps { bag.insert(p); }
        if let Some(l) = last { bag.insert(l); }
        Proc::PPar(bag)
    }
};
```

### 5.5 Generated Display (Example)

For the same constructor:

```rust
impl Display for Proc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Proc::PPar(ps) => {
                write!(f, "{{")?;
                let mut first = true;
                for (p, count) in ps.iter() {
                    for _ in 0..count {
                        if !first { write!(f, " | ")?; }
                        first = false;
                        write!(f, "{}", p)?;
                    }
                }
                write!(f, "}}")
            }
            // ...
        }
    }
}
```

### 5.6 Constraint Enforcement

Meta-constraints like "same length" are enforced by grammar structure:

```
PInputs . ns:Vec(Name), \[xs].p:[[Name]->Proc] 
        |- for( #zip(ns,xs).#map(|n,x| x<-n).#sep(",") ){p} : Proc ;
```

The `#zip(ns,xs)` generates grammar that pairs elements. If the user writes `for(x<-n, y){p}`, it fails to parse because `y` doesn't match the `x<-n` pattern.

No explicit `#length(ns) = #length(xs)` needed—it's structural.

---

## 6. Meta-Lambda

### 6.1 Unified Abstraction

All abstractions in MeTTaIL are **meta-lambdas**—the internal hom of a cartesian closed category. This includes:

- Abstraction parameters in constructors: `\x.p:[Name->Proc]`
- Named definitions: `dup = \n:Name. ...`
- Higher-order parameters: `\f:[A->B]. ...`

These are the same abstraction mechanism with different uses:

| Use | Syntax | Runtime Representation |
|-----|--------|------------------------|
| Constructor binding | `PInput . \x.p:[Name->Proc] |- ...` | `Scope<Binder, Box<Proc>>` |
| Definition | `dup = \n:Name. body` | Expanded at use site |
| Unapplied parameter | `f:[A->B]` passed to constructor | `Scope<Binder, Box<B>>` |

### 6.2 Representation

A meta-lambda `\x:A. body` is represented as:

```rust
/// Meta-level abstraction
pub struct MetaLambda {
    /// Binder variable
    pub binder: Ident,
    /// Binder type
    pub binder_type: TypeExpr,
    /// Body expression (may reference binder)
    pub body: MetaExpr,
}

/// Meta-level expression
pub enum MetaExpr {
    /// Variable reference
    Var(Ident),
    /// Object-term literal
    Term(TermExpr),
    /// Lambda abstraction
    Lambda(Box<MetaLambda>),
    /// Application
    App {
        func: Box<MetaExpr>,
        arg: Box<MetaExpr>,
    },
    /// Collection literal
    Collection {
        coll_type: CollType,
        elements: Vec<MetaExpr>,
    },
}
```

### 6.3 Application and Substitution

Application `f(arg)` performs capture-avoiding substitution:

```rust
impl MetaLambda {
    /// Apply this lambda to an argument
    pub fn apply(&self, arg: &MetaExpr, ctx: &TypeContext) -> Result<MetaExpr, TypeError> {
        // Type check: arg must have type self.binder_type
        let arg_type = arg.infer_type(ctx)?;
        if arg_type != self.binder_type {
            return Err(TypeError::Mismatch {
                expected: self.binder_type.clone(),
                found: arg_type,
            });
        }
        
        // Substitute arg for binder in body
        Ok(self.body.substitute(&self.binder, arg))
    }
}

impl MetaExpr {
    /// Capture-avoiding substitution
    pub fn substitute(&self, var: &Ident, replacement: &MetaExpr) -> MetaExpr {
        match self {
            MetaExpr::Var(v) if v == var => replacement.clone(),
            MetaExpr::Var(v) => MetaExpr::Var(v.clone()),
            
            MetaExpr::Lambda(lam) => {
                if &lam.binder == var {
                    // Shadowed - don't substitute in body
                    MetaExpr::Lambda(lam.clone())
                } else {
                    // Moniker handles capture-avoidance automatically via Scope::unbind()
                    // which freshens bound variables. We just substitute in the body.
                    MetaExpr::Lambda(Box::new(MetaLambda {
                        binder: lam.binder.clone(),
                        binder_type: lam.binder_type.clone(),
                        body: lam.body.substitute(var, replacement),
                    }))
                }
            }
            
            MetaExpr::App { func, arg } => MetaExpr::App {
                func: Box::new(func.substitute(var, replacement)),
                arg: Box::new(arg.substitute(var, replacement)),
            },
            
            MetaExpr::Term(t) => MetaExpr::Term(t.substitute_meta(var, replacement)),
            
            MetaExpr::Collection { coll_type, elements } => MetaExpr::Collection {
                coll_type: coll_type.clone(),
                elements: elements.iter().map(|e| e.substitute(var, replacement)).collect(),
            },
        }
    }
    
    /// Collect free meta-variables in this expression
    pub fn free_vars(&self) -> HashSet<Ident> {
        match self {
            MetaExpr::Var(v) => std::iter::once(v.clone()).collect(),
            MetaExpr::Term(t) => t.free_meta_vars(),
            MetaExpr::Lambda(lam) => {
                let mut vars = lam.body.free_vars();
                vars.remove(&lam.binder);
                vars
            }
            MetaExpr::App { func, arg } => {
                let mut vars = func.free_vars();
                vars.extend(arg.free_vars());
                vars
            }
            MetaExpr::Collection { elements, .. } => {
                elements.iter().flat_map(|e| e.free_vars()).collect()
            }
        }
    }
}

impl TermExpr {
    /// Substitute a meta-variable in an object term.
    /// 
    /// Note: For object-level substitution (substituting object variables),
    /// we use moniker's infrastructure. This method is for meta-level
    /// substitution of definition parameters.
    pub fn substitute_meta(&self, var: &Ident, replacement: &MetaExpr) -> TermExpr {
        // Recursively descend into term structure, replacing meta-var refs.
        // Implementation uses pattern matching on term constructors.
        todo!("Implementation traverses term AST, replacing MetaVar(v) with replacement")
    }
    
    /// Collect free meta-variables referenced in this term.
    /// 
    /// For object-level free variables, use moniker's `BoundTerm::visit_vars()`.
    pub fn free_meta_vars(&self) -> HashSet<Ident> {
        todo!("Implementation traverses term AST collecting MetaVar references")
    }
}
```

### 6.4 Normalization to Object Terms

A fully-applied meta-expression normalizes to an object term:

```rust
impl MetaExpr {
    /// Extract lambda if this expression is (or reduces to) a lambda
    fn as_lambda(&self) -> Result<&MetaLambda, NormError> {
        match self {
            MetaExpr::Lambda(lam) => Ok(lam),
            MetaExpr::Var(v) => Err(NormError::FreeVariable(v.clone())),
            MetaExpr::Term(_) => Err(NormError::NotAFunction),
            MetaExpr::App { .. } => Err(NormError::NotNormalized),
            MetaExpr::Collection { .. } => Err(NormError::NotAFunction),
        }
    }

    /// Normalize to object term (beta-reduce all applications)
    pub fn normalize(&self, ctx: &TypeContext) -> Result<TermExpr, NormError> {
        match self {
            MetaExpr::Term(t) => Ok(t.clone()),
            
            MetaExpr::Var(v) => Err(NormError::FreeVariable(v.clone())),
            
            MetaExpr::Lambda(_) => Err(NormError::UnappliedLambda),
            
            MetaExpr::App { func, arg } => {
                // First, reduce func to a lambda (or look it up if it's a var)
                let lam = func.as_lambda()?;
                let result = lam.apply(arg, ctx)?;
                result.normalize(ctx)
            }
            
            MetaExpr::Collection { coll_type, elements } => {
                let norm_elems: Result<Vec<_>, _> = 
                    elements.iter().map(|e| e.normalize(ctx)).collect();
                Ok(TermExpr::Collection {
                    coll_type: coll_type.clone(),
                    elements: norm_elems?,
                })
            }
        }
    }
}
```

### 6.5 Constructor Parameters

In a constructor declaration:

```rust
PInput . n:Name, \x.p:[Name->Proc] |- for(x<-n){p} : Proc ;
```

The `\x.p:[Name->Proc]` is a meta-lambda that:
1. At parse time: binds `x` in the body `p`
2. At runtime: becomes `Scope<Binder<String>, Box<Proc>>`
3. At substitution: uses generated `substitute()` method (from `macros/src/codegen/subst.rs`)

**Generated variant:**
```rust
PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)
```

**Generated parser:**
```lalrpop
"for" "(" <n:Name> "->" <x:Ident> ")" "{" <body:Proc> "}" => {
    // get_or_create_var from runtime/src/binding.rs
    let binder = Binder(get_or_create_var(x));
    // Scope::new automatically closes bound variables
    let scope = Scope::new(binder, Box::new(body));
    Proc::PInput(Box::new(n), scope)
}
```

### 6.6 Definitions

Definitions bind names to meta-expressions:

```rust
definitions {
    dup = \n:Name. for(x<-n){{ *(x) | n!(*(x)) }} ;
}
```

**Implementation:**

```rust
pub struct Definition {
    pub name: Ident,
    pub params: Vec<(Ident, TypeExpr)>,  // Extracted from nested lambdas
    pub body: MetaExpr,
}

/// Definition environment
pub struct DefEnv {
    defs: HashMap<String, Definition>,
}

impl DefEnv {
    /// Expand a definition application
    pub fn expand(&self, name: &Ident, args: &[MetaExpr]) -> Result<MetaExpr, Error> {
        let def = self.defs.get(&name.to_string())
            .ok_or(Error::UndefinedName(name.clone()))?;
        
        if args.len() != def.params.len() {
            return Err(Error::ArityMismatch {
                expected: def.params.len(),
                found: args.len(),
            });
        }
        
        // Substitute all arguments
        let mut result = def.body.clone();
        for ((param_name, _), arg) in def.params.iter().zip(args) {
            result = result.substitute(param_name, arg);
        }
        
        Ok(result)
    }
}
```

### 6.7 Multi-Binder Implementation

For `\[xs].p:[[Name]->Proc]`:

```rust
pub enum BinderSpec {
    Single(Ident),
    Multi(Ident),  // xs represents x0, x1, ...
}

/// Multi-binder lambda
pub struct MultiLambda {
    pub binders: Ident,      // Collective name (xs)
    pub binder_type: TypeExpr,  // Element type (Name)
    pub body: MetaExpr,
}
```

**Application** takes a list and binds each element:

```rust
impl MultiLambda {
    pub fn apply(&self, args: &[MetaExpr]) -> Result<MetaExpr, TypeError> {
        // Generate individual binder names: xs_0, xs_1, ...
        let binder_names: Vec<Ident> = (0..args.len())
            .map(|i| format_ident!("{}_{}", self.binders, i))
            .collect();
        
        // Substitute each arg for its binder
        let mut result = self.body.clone();
        for (binder_name, arg) in binder_names.iter().zip(args) {
            result = result.substitute(binder_name, arg);
        }
        
        Ok(result)
    }
}
```

**Runtime type:**
```rust
Scope<Vec<Binder<String>>, Box<Proc>>
```

### 6.8 Type Checking

**Type Context:**

```rust
/// Type context for meta-expression type checking
#[derive(Clone, Default)]
pub struct TypeContext {
    bindings: HashMap<String, TypeExpr>,
}

impl TypeContext {
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Look up a variable's type
    pub fn lookup(&self, var: &Ident) -> Result<TypeExpr, TypeError> {
        self.bindings.get(&var.to_string())
            .cloned()
            .ok_or_else(|| TypeError::UnboundVariable(var.clone()))
    }
    
    /// Extend context with a new binding
    pub fn extend(&self, var: &Ident, typ: &TypeExpr) -> TypeContext {
        let mut new_bindings = self.bindings.clone();
        new_bindings.insert(var.to_string(), typ.clone());
        TypeContext { bindings: new_bindings }
    }
}
```

**Type Inference:**

```rust
impl MetaExpr {
    pub fn infer_type(&self, ctx: &TypeContext) -> Result<TypeExpr, TypeError> {
        match self {
            MetaExpr::Var(v) => ctx.lookup(v),
            
            MetaExpr::Term(t) => Ok(t.category()),
            
            MetaExpr::Lambda(lam) => {
                let body_ctx = ctx.extend(&lam.binder, &lam.binder_type);
                let body_type = lam.body.infer_type(&body_ctx)?;
                Ok(TypeExpr::Arrow {
                    domain: Box::new(lam.binder_type.clone()),
                    codomain: Box::new(body_type),
                })
            }
            
            MetaExpr::App { func, arg } => {
                let func_type = func.infer_type(ctx)?;
                match func_type {
                    TypeExpr::Arrow { domain, codomain } => {
                        let arg_type = arg.infer_type(ctx)?;
                        if arg_type != *domain {
                            return Err(TypeError::Mismatch {
                                expected: *domain,
                                found: arg_type,
                            });
                        }
                        Ok(*codomain)
                    }
                    _ => Err(TypeError::NotAFunction(func_type)),
                }
            }
            
            MetaExpr::Collection { coll_type, elements } => {
                // All elements must have same type
                let elem_types: Result<Vec<_>, _> = 
                    elements.iter().map(|e| e.infer_type(ctx)).collect();
                let elem_types = elem_types?;
                
                if elem_types.is_empty() {
                    // Empty collection: element type determined by context (annotation required)
                    // For now, defer to later unification or require annotation
                    return Err(TypeError::CannotInferEmptyCollection);
                }
                
                let elem_type = elem_types[0].clone();
                
                for t in &elem_types[1..] {
                    if t != &elem_type {
                        return Err(TypeError::HeterogeneousCollection);
                    }
                }
                
                Ok(TypeExpr::Collection {
                    coll_type: coll_type.clone(),
                    element: Box::new(elem_type),
                })
            }
        }
    }
}

// Note: Empty collections like `{}` are valid syntactically but require type 
// annotation or contextual inference. In constructor parameters where the 
// collection type is declared (e.g., `ps:HashBag(Proc)`), the element type is known.

### 6.9 Worked Examples

#### Example 1: First-Order Abstraction

**Definition:**
```
dup = \n:Name. for(x<-n){{ *(x) | n!(*(x)) }}
```

**Type:** `[Name -> Proc]`

This receives a value on channel `n`, dereferences it (with `*(x)`), and also re-sends the dereferenced process back on `n`.

**Representation:**
```rust
MetaLambda {
    binder: "n",
    binder_type: TypeExpr::Base("Name"),
    body: MetaExpr::Term(
        PInput(n, Scope(x, PPar({PDrop(x), POutput(n, PDrop(x))})))
    )
}
```

Note: In the body, `n` appears as a free meta-variable (of type Name), and `x` is bound by the `for`. The term `*(x)` is `PDrop(x)`, which takes a Name and returns a Proc.

**Application:** `dup(@(0))`

Step 1: Type check
- Argument `@(0)` has type `Name` ✓
- Expected: `Name` ✓

Step 2: Substitute `@(0)` for `n` in body
```
for(x<-n){{ *(x) | n!(*(x)) }}
    ↓ [n := @(0)]
for(x<-@(0)){{ *(x) | @(0)!(*(x)) }}
```

Step 3: Result is an object term (no meta-redexes remain)
```
for(x<-@(0)){{ *(x) | @(0)!(*(x)) }}
```

**Final MetaExpr:**
```rust
MetaExpr::Term(
    PInput(NQuote(PZero), Scope(x, PPar({PDrop(x), POutput(NQuote(PZero), PDrop(x))})))
)
```

---

#### Example 2: Curried Abstraction

**Definition:**
```
fwd = \n:Name. \m:Name. for(x<-n){ m!(*(x)) }
```

**Type:** `[Name -> [Name -> Proc]]`

**Representation:**
```rust
MetaLambda {
    binder: "n",
    binder_type: TypeExpr::Base("Name"),
    body: MetaExpr::Lambda(Box::new(MetaLambda {
        binder: "m",
        binder_type: TypeExpr::Base("Name"),
        body: MetaExpr::Term(
            PInput(@(n), Scope(x, POutput(m, PDrop(x))))
        )
    }))
}
```

**Application:** `fwd(@(a))(@(b))`

**Step 1:** Apply outer lambda to `@(a)`
```
fwd(@(a))
= (\n:Name. \m:Name. for(x<-n){ m!(*(x)) })(@(a))
    ↓ [n := @(a)]
= \m:Name. for(x<-@(a)){ m!(*(x)) }
```

Result type: `[Name -> Proc]` — still a lambda!

**Step 2:** Apply result to `@(b)`
```
(\m:Name. for(x<-@(a)){ m!(*(x)) })(@(b))
    ↓ [m := @(b)]
= for(x<-@(a)){ @(b)!(*(x)) }
```

Result type: `Proc` — object term, fully reduced.

**Final result:**
```
for(x<-@(a)){ @(b)!(*(x)) }
```

---

#### Example 3: Higher-Order Abstraction `[[A->B] -> C]`

**Definition:**
```
invoke = \f:[Name->Proc]. f(@(0))
```

**Type:** `[[Name->Proc] -> Proc]`

This takes a function `f` of type `[Name->Proc]` and applies it to the fixed name `@(0)`.

**Representation:**
```rust
MetaLambda {
    binder: "f",
    binder_type: TypeExpr::Arrow {
        domain: Box::new(TypeExpr::Base("Name")),
        codomain: Box::new(TypeExpr::Base("Proc")),
    },
    body: MetaExpr::App {
        func: Box::new(MetaExpr::Var("f")),
        arg: Box::new(MetaExpr::Term(NQuote(PZero))),
    }
}
```

**Application:** `invoke(\n:Name. *(n))`

**Step 1:** Type check the argument
- Argument: `\n:Name. *(n)`
- Argument type: `[Name -> Proc]` ✓
- Expected: `[Name -> Proc]` ✓

**Step 2:** Substitute `\n:Name. *(n)` for `f` in body `f(@(0))`
```
f(@(0))
    ↓ [f := \n:Name. *(n)]
= (\n:Name. *(n))(@(0))
```

Result is a meta-application — needs further reduction!

**Step 3:** Reduce the inner application
```
(\n:Name. *(n))(@(0))
    ↓ [n := @(0)]
= *(@(0))
```

**Final result:**
```
*(@(0))
```

This is `PDrop(NQuote(PZero))` — a pure object term.

---

#### Example 4: Higher-Order with Lambda Returning Lambda

**Definition:**
```
twice = \f:[Proc->Proc]. \p:Proc. f(f(p))
```

**Type:** `[[Proc->Proc] -> [Proc -> Proc]]`

This takes a transformation `f` and returns a new transformation that applies `f` twice.

**Application:** `twice(\q:Proc. {q|q})(0)`

**Step 1:** Apply to `\q:Proc. {q|q}`
```
twice(\q:Proc. {q|q})
= (\f:[Proc->Proc]. \p:Proc. f(f(p)))(\q:Proc. {q|q})
    ↓ [f := \q:Proc. {q|q}]
= \p:Proc. (\q:Proc. {q|q})((\q:Proc. {q|q})(p))
```

Result type: `[Proc -> Proc]` — still a lambda.

**Step 2:** Apply to `0`
```
(\p:Proc. (\q:Proc. {q|q})((\q:Proc. {q|q})(p)))(0)
    ↓ [p := 0]
= (\q:Proc. {q|q})((\q:Proc. {q|q})(0))
```

**Step 3:** Reduce innermost application
```
(\q:Proc. {q|q})(0)
    ↓ [q := 0]
= {0|0}
```

**Step 4:** Reduce outer application
```
(\q:Proc. {q|q})({0|0})
    ↓ [q := {0|0}]
= {{0|0}|{0|0}}
```

**Step 5:** Normalize (flatten nested PPar)
```
{{0|0}|{0|0}} = {0|0|0|0}
```

**Final result:**
```
{0|0|0|0}
```

## 7. Rewrite Rules

### 7.1 Syntax

Rewrites have an optional proposition context before `|-`:

```
prop-context |- LHS ~> RHS ;
```

The proposition context (only for rewrites) can contain:
- **Freshness**: `x # q` (x is fresh in q)
- **Congruence premise**: `s ~> t` (if s rewrites to t)

### 7.2 Examples

```rust
rewrites {
    // Simple reduction
    *(@(p)) ~> p ;
    
    // Communication with freshness
    x # q |- { for(x<-n){p} | n!(q) } ~> { p(@(q)/x) } ;
    
    // Congruence
    s ~> t |- { s | ...rest } ~> { t | ...rest } ;
}
```

Note: Beta reduction for meta-level lambdas is handled automatically by MeTTaIL, not defined as a theory rewrite.

### 7.3 Substitution Notation

`p(q/x)` means "substitute q for x in p":

```rust
// Generates:
let (binder, body) = abs.unbind();
body.substitute(&binder.0, &replacement)
```

---

## 8. Equations

### 8.1 Syntax

Equations also support freshness conditions:

```
conditions |- LHS == RHS ;
```

### 8.2 Examples

```rust
equations {
    // Quote-drop elimination
    @(*(n)) == n ;
    
    // Scope extrusion with freshness
    x # ...rest |- { new(x, p) | ...rest } == new(x, { p | ...rest }) ;
}
```

---

## 9. Implementation

### 9.1 AST Types

```rust
/// Parameter in the term context
pub enum Param {
    /// Term parameter: n:Name
    Term {
        name: Ident,
        typ: TypeExpr,
    },
    
    /// Abstraction: \x.p:[A->B] or f = \x.p:[A->B]
    Abstraction {
        /// Optional name for the whole abstraction
        name: Option<Ident>,
        /// Binder(s)
        binders: BinderSpec,
        /// Body variable name
        body: Ident,
        /// Full type (must be Arrow)
        abs_type: TypeExpr,
    },
}

/// Binder specification
pub enum BinderSpec {
    /// Single binder: \x
    Single(Ident),
    /// Multi-binder: \[xs]
    Multi(Ident),
    /// Nested: \x.\y (list of single binders)
    Nested(Vec<Ident>),
}

/// Constructor declaration
pub struct Constructor {
    pub label: Ident,
    pub params: Vec<Param>,
    pub syntax: SyntaxExpr,
    pub result: TypeExpr,
}

/// Syntax expression (with pattern operations)
pub enum SyntaxExpr {
    /// Literal token
    Literal(String),
    /// Parameter reference
    Param(Ident),
    /// Pattern operation call
    PatternOp(PatternOp),
    /// Sequence of syntax elements
    Seq(Vec<SyntaxExpr>),
    /// Delimited: { inner }
    Delimited {
        open: String,
        inner: Box<SyntaxExpr>,
        close: String,
    },
}

/// Pattern operations for syntax patterns (distinct from MetaExpr in section 6)
/// These are compile-time operations for generating grammar/display
pub enum PatternOp {
    /// Variable reference
    Var(Ident),
    /// Pattern function: #name(args)
    Call {
        name: Ident,  // sep, zip, map, opt
        args: Vec<PatternOp>,
    },
    /// Method chain: expr.#name(args)
    Method {
        receiver: Box<PatternOp>,
        name: Ident,
        args: Vec<PatternOp>,
    },
    /// Pattern lambda: |params| body (for #map)
    Lambda {
        params: Vec<Ident>,
        body: Box<SyntaxExpr>,
    },
}
```

### 9.2 Runtime Types

We continue using the existing moniker infrastructure from `runtime/src/binding.rs`:

```rust
// Re-exported from moniker (with Hash/Ord wrappers)
pub use mettail_runtime::{Scope, Binder, FreeVar, Var, OrdVar};

// Single binder: Scope<Binder<String>, Box<Proc>>
PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)

// Multi-binder: Scope<Vec<Binder<String>>, Box<Proc>>
PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Box<Proc>>)

// Nested abstraction: nested Scopes
PLam2(Scope<Binder<String>, Scope<Binder<String>, Box<Proc>>>)
```

The existing `Scope` wrapper in `runtime/src/binding.rs` adds `Hash` and `Ord` implementations required by Ascent. Moniker handles:
- **Alpha-equivalence**: via `BoundTerm::term_eq()`
- **Capture-avoiding unbind**: `Scope::unbind()` freshens bound variables
- **Variable identity**: `FreeVar::fresh_named()` creates unique variables
- **Substitution**: generated by `macros/src/codegen/subst.rs`

No new runtime types are needed.

---

## 10. Migration

### 10.1 Syntax Mapping

| Current | New |
|---------|-----|
| `Label . Cat ::= ... ;` | `Label . ctx \|- syntax : Cat ;` |
| `<Name>` | `\x.p:[Name->...]` |
| `HashBag(T) sep "s"` | `ps:HashBag(T)` + `ps.#sep("s")` in pattern |
| `delim "{" "}"` | `{ ... }` in pattern |

### 10.2 Migration Strategy

1. **Phase 1**: Parser accepts both syntaxes; old desugars to new
2. **Phase 2**: Migrate all theories to new syntax
3. **Phase 3**: Remove old syntax support

---


## 11. Implementation Plan

**Guiding Goal**: Define and execute rho calculus with multi-channel input:
```
PInputs . ns:Vec(Name), \[xs].p:[[Name]->Proc] 
        |- for( #zip(ns,xs).#map(|n,x| x<-n).#sep(",") ){p} : Proc ;
```

### Phase 1: Type System (2-3 days)

- [ ] Extend `TypeExpr` with `Arrow { domain, codomain }`
- [ ] Extend `TypeExpr` with `MultiBinder(element_type)`
- [ ] Implement type equality and display

### Phase 2: Constructor Syntax (1 week)

- [ ] Parse new constructor syntax: `Label . ctx |- pattern : Type`
- [ ] Parse abstraction params: `\x.p:[A->B]`
- [ ] Parse multi-binder: `\[xs].p:[[A]->B]`
- [ ] Parse nested abstractions: `\x.\y.p:[A->[B->C]]`
- [ ] Generate enum variants with `Scope` types
- [ ] Generate LALRPOP parser rules

### Phase 3: Pattern Operations (1 week)

- [ ] Parse `#sep(coll, sep)` and method form `coll.#sep(sep)`
- [ ] Parse `#zip(a, b)` and `#map(coll, |x| expr)`
- [ ] Compile pattern ops to LALRPOP grammar
- [ ] Compile pattern ops to Display impl
- [ ] Validate pattern variable usage

### Phase 4: Equations and Rewrites Syntax (3-4 days)

- [ ] Update equation syntax to judgement form
- [ ] Update rewrite syntax to judgement form  
- [ ] Support freshness conditions in new syntax
- [ ] Support congruence premises in new syntax

### Phase 5: Migration (1 week)

- [ ] Migrate RhoCalc to new syntax (including multi-channel input)
- [ ] Migrate Ambient to new syntax
- [ ] Migrate Calculator to new syntax
- [ ] Validate multi-channel input works end-to-end
- [ ] Deprecate old BNFC-style syntax

### Phase 6: Definitions (Optional, 3-4 days)

- [ ] Parse `definitions { name = expr; ... }` block
- [ ] Implement `Definition` struct and `DefEnv`
- [ ] Implement definition expansion (non-recursive)
- [ ] REPL integration for definition lookup

---

## 12. Summary

### 12.1 Unified Meta-Lambda

All abstractions are meta-lambdas (CCC internal hom):

| Use | Syntax | Representation |
|-----|--------|----------------|
| Constructor param | `\x.p:[A->B]` | `Scope<Binder, Box<B>>` at runtime |
| Definition | `name = \x:T. body` | Expanded at use site |
| Higher-order param | `f:[A->B]` | `Scope<Binder, Box<B>>` when passed |

### 12.2 Key Features

| Feature | Syntax |
|---------|--------|
| Constructor abstraction | `\x.p:[A->B]` |
| Named constructor abs | `f = \x.p:[A->B]` |
| Multi-binder | `\[xs].p:[[A]->B]` |
| Nested abstraction | `\x.\y.p:[A->[B->C]]` |
| Function type | `[A->B]` |
| Collection parameter | `ps:HashBag(Proc)` |
| Syntax pattern | `for(x<-n){p}` |
| Meta-syntax | `#sep`, `#zip`, `#map` |
| Meta-definition | `dup = \n:Name. ...` |
| Meta-application | `dup(@(0))` |

### 12.3 Key Principles

1. **Unified abstraction** — all `\x.body` are meta-lambdas (CCC hom)
2. **Meta-syntax is compile-time** — generates grammar + display
3. **Capture-avoiding via moniker** — `Scope::unbind()` freshens bound variables automatically
4. **Constraints are structural** — enforced by grammar, not runtime checks
5. **Type-checked expansion** — application checks argument types

---

**Estimated Effort**: 4-5 weeks (Phases 1-5), +1 week optional (Phase 6)
**Risk Level**: Medium (well-defined scope, leverages existing moniker infrastructure)  
**Impact**: High (enables multi-channel input and expressive language specifications)
