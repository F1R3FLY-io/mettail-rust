# Lambda Environment Design

## Goal

Enable users to store lambda terms in the environment and apply them:

```
> dup = ^n.{n?x.{{ *(x) | n!(*(x)) }}}
✓ dup added to environment
> (subst dup my_name)
my_name?x.{{ *(x) | my_name!(*(x)) }}
```

## Current State

- Environment stores per-category values: `ProcEnv`, `NameEnv`
- Lambdas like `^x.p` are embedded in constructors (e.g., `PInput`)
- `(subst ...)` is rewrite rule syntax, not term syntax
- `Var` variants are auto-generated for each category

## Key Insight

A lambda `^x.P : [A -> B]` is stored as a value of category `B` (its codomain). This avoids creating new categories for every arrow type.

## Design: Auto-Generated Lambda Constructors

### Generation Strategy

Generate lambda constructors for **every pair of categories**, just like we generate substitution methods for every pair. No scanning needed.

For N categories, generate:
- N² single-binder lambda variants (one per `[A -> B]` pair)
- N multi-binder lambda variants (one per `[A* -> B]`)

### Generated Variants

For categories `{Proc, Name}`:

```rust
enum Proc {
    // ... existing variants ...
    
    // Auto-generated lambdas into Proc:
    LamProc(Scope<Binder<String>, Box<Proc>>),  // [Proc -> Proc]
    LamName(Scope<Binder<String>, Box<Proc>>),  // [Name -> Proc]
    
    // Auto-generated multi-lambdas:
    MLamProc(Scope<Vec<Binder<String>>, Box<Proc>>),  // [Proc* -> Proc]
    MLamName(Scope<Vec<Binder<String>>, Box<Proc>>),  // [Name* -> Proc]
}

enum Name {
    // ... existing variants ...
    
    // Auto-generated lambdas into Name:
    LamProc(Scope<Binder<String>, Box<Name>>),  // [Proc -> Name]
    LamName(Scope<Binder<String>, Box<Name>>),  // [Name -> Name]
    
    // Auto-generated multi-lambdas:
    MLamProc(Scope<Vec<Binder<String>>, Box<Name>>),  // [Proc* -> Name]
    MLamName(Scope<Vec<Binder<String>>, Box<Name>>),  // [Name* -> Name]
}
```

**Naming convention**:
- Single: `Lam{Domain}` (e.g., `LamName`, `LamProc`)
- Multi: `MLam{Domain}` (e.g., `MLamName`)

### Type Inference from Usage

**No explicit type annotations needed.** The binder's type is inferred from how it's used in the body:

```
^x.x!(p)     → x used as Name (first arg of POutput) → Proc::LamName
^x.{*(x)}    → x used as Name (arg of PDrop)         → Proc::LamName  
^x.{x | q}   → x used as Proc (element of PPar)      → Proc::LamProc
^n.@(n)      → n used as Proc (arg of NQuote)        → Name::LamProc
```

**Inference algorithm** (at parse time):

1. Parse `^x.{body}` - record `x` as a free variable
2. Parse `body` - track which category each variable occurrence requires
3. Look up where `x` appears in `body`:
   - Collect all positions where `x` is used
   - Each position has a known category (from constructor signatures)
4. Determine `x`'s type:
   - All occurrences must agree → that's the type
   - Conflicting types → **error**: "Variable x used as both Name and Proc"
   - No occurrences → **error**: "Lambda binder x not used in body"
5. Select the appropriate `Lam{Type}` constructor

### Generated Parser Rules

```lalrpop
// Parse lambda, then infer type from body
Proc: Proc = {
    "^" <x:Ident> "." "{" <body:Proc> "}" => {
        let var_name = x.to_string();
        let binder = mettail_runtime::Binder(mettail_runtime::get_or_create_var(&var_name));
        
        // Infer binder type from usage in body
        match infer_var_category(&body, &var_name) {
            Some(Category::Proc) => Proc::LamProc(Scope::new(binder, Box::new(body))),
            Some(Category::Name) => Proc::LamName(Scope::new(binder, Box::new(body))),
            None => panic!("Lambda binder '{}' not used in body", var_name),
        }
    },
};
```

### Generated Display

Pretty-print lambdas with their syntax:

```rust
impl Display for Proc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Proc::LamName(scope) => {
                let (binder, body) = scope.clone().unbind();
                write!(f, "^{}.{{{}}}", binder.0.pretty_name.as_deref().unwrap_or("?"), body)
            }
            Proc::MLamName(scope) => {
                let (binders, body) = scope.clone().unbind();
                let names: Vec<_> = binders.iter()
                    .map(|b| b.0.pretty_name.as_deref().unwrap_or("?"))
                    .collect();
                write!(f, "^[{}].{{{}}}", names.join(","), body)
            }
            // ... other variants
        }
    }
}
```

### Generated Substitution

Lambda variants participate in substitution like other variants:

```rust
// In generate_subst_arm for VariantKind::Binder (already handles this!)
Proc::LamName(scope) => {
    // Capture-avoiding substitution through scope
    Proc::LamName(mettail_runtime::Scope::new(
        scope.unsafe_pattern().clone(),
        Box::new((*scope.unsafe_body()).subst_name(vars, repls))
    ))
}
```

### Application Syntax

Generate `(subst ...)` as valid term syntax for beta reduction:

```lalrpop
// Single-argument application
Proc: Proc = {
    "(" "subst" <lam:Proc> <arg:Name> ")" => {
        match lam {
            Proc::LamName(scope) => {
                let (binder, body) = scope.unbind();
                body.substitute_name(&binder.0, &arg)
            }
            _ => panic!("subst expects a lambda, got {:?}", lam)
        }
    },
};

// Multi-argument application  
Proc: Proc = {
    "(" "subst" <lam:Proc> <args:Name+> ")" => {
        match lam {
            Proc::MLamName(scope) => {
                let (binders, body) = scope.unbind();
                let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
                body.multi_substitute_name(&vars, &args)
            }
            _ => panic!("subst expects a multi-lambda, got {:?}", lam)
        }
    },
};
```

## Implementation Plan

### Step 1: Variant Generation

In `generate_ast_enums`, after generating `Var` variants, generate lambda variants for every category pair:

```rust
// For each category as codomain
for codomain in &theory.exports {
    // Generate Lam{Domain} for each domain category
    for domain in &theory.exports {
        let variant_name = format_ident!("Lam{}", domain.name);
        variants.push(quote! {
            #variant_name(mettail_runtime::Scope<
                mettail_runtime::Binder<String>,
                Box<#codomain_name>
            >)
        });
    }
    
    // Generate MLam{Domain} for multi-binder
    for domain in &theory.exports {
        let variant_name = format_ident!("MLam{}", domain.name);
        variants.push(quote! {
            #variant_name(mettail_runtime::Scope<
                Vec<mettail_runtime::Binder<String>>,
                Box<#codomain_name>
            >)
        });
    }
}
```

**Files**: `macros/src/codegen/ast_gen.rs`

### Step 2: Type Inference Helper

Generate a helper function to infer variable category from usage:

```rust
// Generated for each category
impl Proc {
    /// Find what category a variable is used as in this term
    fn infer_var_category(term: &Proc, var_name: &str) -> Option<Category> {
        // Traverse term, find all uses of var_name
        // Return the category if consistent, None if unused, panic if conflicting
    }
}
```

**Files**: `macros/src/codegen/ast_gen.rs` (new function)

### Step 3: Parser Rule Generation

Generate lambda parsing with type inference:

```lalrpop
Proc: Proc = {
    "^" <x:Ident> "." "{" <body:Proc> "}" => {
        let binder = Binder(get_or_create_var(&x));
        match Proc::infer_var_category(&body, &x) {
            Some(Category::Proc) => Proc::LamProc(Scope::new(binder, Box::new(body))),
            Some(Category::Name) => Proc::LamName(Scope::new(binder, Box::new(body))),
            None => panic!("Binder '{}' not used in body", x),
        }
    },
    // Multi-lambda with inference
    "^" "[" <xs:Comma<Ident>> "]" "." "{" <body:Proc> "}" => {
        // Infer from first binder that's used
        ...
    },
    // Application
    "(" "subst" <lam:Proc> <arg:Name> ")" => apply_lambda(lam, arg),
};
```

**Files**: `macros/src/codegen/parser/lalrpop.rs`

### Step 4: Display Generation

Add match arms for all lambda variants:

```rust
Proc::LamName(scope) => {
    let (binder, body) = scope.clone().unbind();
    write!(f, "^{}.{{{}}}", binder.0.pretty_name.unwrap_or("?"), body)
}
Proc::LamProc(scope) => { /* same pattern */ }
Proc::MLamName(scope) => { /* multi-binder pattern */ }
```

**Files**: `macros/src/codegen/display.rs`

### Step 5: Substitution Integration

Lambda variants use `VariantKind::Binder` - verify they're classified correctly in `classify_variant`.

**Files**: `macros/src/codegen/subst.rs` (verify)

## Example: RhoCalc

For `exports { Proc, Name }`, we generate all category pairs:

**Generated variants for Proc**:
```rust
enum Proc {
    // Existing constructors
    PZero,
    PDrop(Box<Name>),
    POutput(Box<Name>, Box<Proc>),
    PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>),
    PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Box<Proc>>),
    PPar(HashBag<Proc>),
    Var(OrdVar),
    
    // Auto-generated single lambdas (all domain types):
    LamProc(Scope<Binder<String>, Box<Proc>>),  // [Proc -> Proc]
    LamName(Scope<Binder<String>, Box<Proc>>),  // [Name -> Proc]
    
    // Auto-generated multi lambdas:
    MLamProc(Scope<Vec<Binder<String>>, Box<Proc>>),  // [Proc* -> Proc]
    MLamName(Scope<Vec<Binder<String>>, Box<Proc>>),  // [Name* -> Proc]
}

enum Name {
    NQuote(Box<Proc>),
    Var(OrdVar),
    
    // Auto-generated single lambdas:
    LamProc(Scope<Binder<String>, Box<Name>>),  // [Proc -> Name]
    LamName(Scope<Binder<String>, Box<Name>>),  // [Name -> Name]
    
    // Auto-generated multi lambdas:
    MLamProc(Scope<Vec<Binder<String>>, Box<Name>>),
    MLamName(Scope<Vec<Binder<String>>, Box<Name>>),
}
```

**Type inference examples**:
```
^x.x!(0)      → x in POutput position (Name) → Proc::LamName
^x.{*(x)}     → x in PDrop position (Name)   → Proc::LamName
^p.{p | 0}    → p in PPar position (Proc)    → Proc::LamProc
^n.@(n)       → n in NQuote position (Proc)  → Name::LamProc
^x.{x}        → error: x not used with known type (bare var in Par)
^x.{x!(x)}    → error: x used as both Name and Proc
```

## Workflow After Implementation

```
rhocalc> dup = ^n.{n?x.{{ *(x) | n!(*(x)) }}}
✓ dup added to environment

rhocalc> env
Environment:
  dup = ^n.{n?x.{{ *(x) | n!(*(x)) }}}

rhocalc> term: (subst dup @(0))
Parsing... ✓
@(0)?x.{{ *(x) | @(0)!(*(x)) }}

rhocalc> multi = ^[a,b].{a?x.{*(x)} | b!(0)}
✓ multi added to environment

rhocalc> term: (subst multi n m)
Parsing... ✓  
{n?x.{*(x)} | m!(0)}
```

## Summary

| Component | Auto-Generated | Notes |
|-----------|----------------|-------|
| Lambda variants | ✓ | N² variants: `Lam{Domain}` for every category pair |
| Multi-lambda variants | ✓ | N variants: `MLam{Domain}` for every domain category |
| Type inference | ✓ | Infer binder type from usage in body |
| Parser rules | ✓ | Simple `^x.{body}` syntax with inference |
| Display | ✓ | Pretty-print with `^x.{...}` syntax |
| Substitution | ✓ | Handled by existing binder logic |
| Application | ✓ | `(subst lam args)` in term syntax |
| Environment | No changes | Lambdas stored in codomain's env |

## Error Cases

| Case | Error Message |
|------|---------------|
| Binder not used | "Lambda binder 'x' not used in body" |
| Conflicting types | "Variable 'x' used as both Name and Proc" |
| Ambiguous (bare var) | "Cannot infer type of 'x' - appears only as bare variable" |

---

## Higher-Order Lambda Support

### Motivation

For replication to be a genuine metaprogram acting on any input process:

```
rep = ^n.^a.^cont.{{$name(dup, n) | n!(a?y.{{$name(cont,y) | $name(dup, n)}})}}
```

Here `cont` is not a base type - it's a function `[Name -> Proc]` that transforms the received value `y`. We need to:
1. Infer `cont : [Name -> Proc]` from its use in `$name(cont, y)`
2. Infer that `rep : [Name -> [Name -> [[Name->Proc] -> Proc]]]`

### Key Insight: Function Types as Base Types

Our representation already handles this! The type `[Name -> Proc]` is represented as a `Proc` value (specifically, a `Proc::LamName`). So:

- `cont : [Name -> Proc]` means `cont` is a `Proc` that happens to be a `LamName` variant
- `^cont.{...}` where `cont : [Name -> Proc]` generates `Proc::LamProc` (taking a Proc argument)
- The nested lambda structure encodes the full type

**Type correspondence:**

| Type Expression | Rust Representation |
|-----------------|---------------------|
| `Name` | `Name` |
| `Proc` | `Proc` |
| `[Name -> Proc]` | `Proc` (as `Proc::LamName`) |
| `[Proc -> Proc]` | `Proc` (as `Proc::LamProc`) |
| `[[Name->Proc] -> Proc]` | `Proc` (as `Proc::LamProc` containing a lambda-typed arg) |

### Enhanced Type Inference

Current inference returns only base categories. Enhanced inference tracks full function types:

```rust
enum InferredType {
    Base(Category),                              // Name, Proc, Int
    Arrow(Box<InferredType>, Box<InferredType>), // [A -> B]
}
```

#### Inference Rules

**Rule 1: Constructor position** - Standard inference
```
x in POutput(x, p)  →  x : Name
p in PPar(..., p, ...)  →  p : Proc
```

**Rule 2: Application position** - Function type inference
```
f in $domain(f, arg)  →  f : [type(arg) -> result_type_from_context]
```

For `$name(cont, y)` in a Proc context:
- `$name` = `ApplyName` = apply with `Name` domain
- `y : Name` (bound by input binder)
- Result context: inside `PPar` with other `Proc`s
- Therefore: `cont : [Name -> Proc]`

**Rule 3: Nested applications**
```
f in $domain(f, $inner(...))  →  infer inner application first, use result type as argument type
```

#### Inference Algorithm

```rust
/// Infer the full type of a variable from its usage in a term
fn infer_var_type(term: &Proc, var_name: &str, context_type: Category) -> Option<InferredType> {
    match term {
        // Application: f must be a function type
        Proc::ApplyName(f, arg) if is_var(f, var_name) => {
            let arg_type = infer_term_type(arg);  // Type of argument
            Some(InferredType::Arrow(
                Box::new(arg_type),
                Box::new(InferredType::Base(context_type))
            ))
        }
        Proc::ApplyProc(f, arg) if is_var(f, var_name) => {
            let arg_type = infer_term_type(arg);
            Some(InferredType::Arrow(
                Box::new(arg_type),
                Box::new(InferredType::Base(context_type))
            ))
        }
        
        // Regular constructor position: base type
        Proc::POutput(n, _) if is_var(n, var_name) => {
            Some(InferredType::Base(Category::Name))
        }
        
        // Recurse into subterms with appropriate context
        Proc::PPar(bag) => {
            for elem in bag {
                if let Some(t) = infer_var_type(elem, var_name, Category::Proc) {
                    return Some(t);
                }
            }
            None
        }
        
        // ... other cases
    }
}
```

### Example: Typing `rep`

```
rep = ^n.^a.^cont.{{$name(dup, n) | n!(a?y.{{$name(cont,y) | $name(dup, n)}})}}
```

**Step-by-step inference:**

1. **Innermost uses:**
   - `n` in `$name(dup, n)`: `n : Name` (argument to dup's Name domain)
   - `n` in `n!(...)`: `n : Name` (channel)
   - `a` in `a?y.{...}`: `a : Name` (channel)
   - `y` in `$name(cont, y)`: bound by input, so `y : Name`

2. **Function type inference:**
   - `cont` in `$name(cont, y)`: `y : Name`, context is `Proc`
   - Therefore: `cont : [Name -> Proc]`

3. **Lambda construction (inside-out):**
   - `^cont.{...}` where `cont : [Name -> Proc]` (base type `Proc`)
     - → `Proc::LamProc` (taking Proc, returning Proc)
     - Type: `[[Name->Proc] -> Proc]`
   - `^a.{...}` where `a : Name`
     - → `Proc::LamName` (taking Name, returning the above)
     - Type: `[Name -> [[Name->Proc] -> Proc]]`
   - `^n.{...}` where `n : Name`
     - → `Proc::LamName` (taking Name, returning the above)
     - Type: `[Name -> [Name -> [[Name->Proc] -> Proc]]]`

**Result:** `rep : [Name -> [Name -> [[Name->Proc] -> Proc]]]`

### Storage

The full type is encoded structurally:

```rust
// rep = ^n.^a.^cont.{...}
Proc::LamName(Scope::new(n_binder, Box::new(
    Proc::LamName(Scope::new(a_binder, Box::new(
        Proc::LamProc(Scope::new(cont_binder, Box::new(
            // body...
        )))
    )))
)))
```

Each `LamName` or `LamProc` tells us the domain type. The nesting tells us the full curried type.

### Type Annotations (Optional Enhancement)

Allow explicit type annotations for clarity or when inference fails:

```
^cont:[Name->Proc].{...}
```

Parser extension:
```lalrpop
Proc: Proc = {
    // With type annotation
    "^" <x:Ident> ":" <ty:TypeExpr> "." "{" <body:Proc> "}" => {
        validate_type(&body, &x, &ty)?;
        build_lambda(&x, &ty, body)
    },
    
    // Without annotation (infer)
    "^" <x:Ident> "." "{" <body:Proc> "}" => {
        let ty = infer_var_type(&body, &x)?;
        build_lambda(&x, &ty, body)
    },
};

TypeExpr: InferredType = {
    <base:Ident> => InferredType::Base(base.into()),
    "[" <domain:TypeExpr> "->" <codomain:TypeExpr> "]" => {
        InferredType::Arrow(Box::new(domain), Box::new(codomain))
    },
};
```

### Validation

When applying a higher-order function:

```
$name(rep, channel_n)  // rep expects [Name -> ...], channel_n : Name ✓
```

Runtime beta reduction handles this naturally - if `rep` is a `LamName`, applying it with a `Name` works. Type mismatches cause runtime panics (or we add static checking).

### Lambda Selection from Inferred Type

```rust
fn build_lambda(binder: &str, inferred: &InferredType, body: Proc) -> Proc {
    match inferred.base_type() {
        Category::Name => Proc::LamName(make_scope(binder, body)),
        Category::Proc => Proc::LamProc(make_scope(binder, body)),
        // ... other categories
    }
}

impl InferredType {
    /// Get the base representation type (what category stores this type)
    fn base_type(&self) -> Category {
        match self {
            InferredType::Base(cat) => *cat,
            InferredType::Arrow(_, codomain) => codomain.base_type(),
        }
    }
}
```

For `cont : [Name -> Proc]`:
- `base_type()` = `Proc` (the codomain's base type)
- So `^cont.{...}` uses `LamProc` (taking a Proc-typed argument)

### Display Enhancement

Show full types in environment listing:

```
rhocalc> env
Environment:
  dup : [Name -> Proc] = ^n. { n?x. {  { *(x) | n!(*(x)) } } }
  rep : [Name -> [Name -> [[Name->Proc] -> Proc]]] = ^n.^a.^cont. { ... }
```

### Implementation Status (Completed)

1. **`InferredType` enum** - Defined in `macros/src/codegen/ast_gen.rs`
   - `Base(VarCategory)` for simple types
   - `Arrow(InferredType, InferredType)` for function types
   - `MultiArrow(InferredType, InferredType)` for multi-arg functions
   - `base_type()` method returns representation category

2. **`infer_var_type` method** - Generated for each category
   - Detects variable usage in `ApplyX` function position → infers `[Domain -> Codomain]`
   - Recurses into all subterms including auto-generated `LamX`, `ApplyX` variants
   - Returns full type information

3. **Parser generation** - Uses `base_type()` for variant selection
   - Nested match: outer on `Option<InferredType>`, inner on `t.base_type()`
   - Correctly handles higher-order types like `[Name -> Proc]`

4. **Subterm deconstruction** - Added rules for auto-generated variants
   - `ApplyX(lam, arg)` → extracts both `lam` and `arg`
   - `LamX(scope)` → extracts body from scope
   - Enables beta reduction to find redexes in subterms

5. **Rewrite congruence** - Propagates rewrites through structure
   - If `lam` rewrites in `ApplyX(lam, arg)`, the whole `ApplyX` rewrites
   - If `arg` rewrites in `ApplyX(lam, arg)`, the whole `ApplyX` rewrites  
   - If `body` rewrites in `LamX(scope)`, the whole `LamX` rewrites
   - Enables nested beta reductions to appear as top-level choices

### Future Work

- **Type annotations**: Optional `^x:[Type].{body}` syntax
- **Type display in environment**: Show inferred types in `env` command

### Summary

| Aspect | First-Order (Current) | Higher-Order (Enhanced) |
|--------|----------------------|-------------------------|
| Type inference | Base category only | Full function types |
| `^f.{$name(f,x)}` | `f : Proc` | `f : [Name -> Proc]` |
| Storage | `LamProc` | `LamProc` (same - base type is Proc) |
| Display | `^f.{...}` | `^f:[Name->Proc].{...}` (optional) |
| Validation | None | Check application type consistency |

The key insight: **function types are already representable** - `[A->B]` is stored as a `B` value (specifically a `Lam` variant). Enhanced inference just tracks the full type for validation and documentation, without changing the underlying representation.
