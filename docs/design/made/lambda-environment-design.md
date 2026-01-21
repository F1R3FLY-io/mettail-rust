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
