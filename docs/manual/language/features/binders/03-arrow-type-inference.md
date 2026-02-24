# Arrow Type Inference — Full Pipeline Trace

When a binder `^x.{body}` is parsed, the pipeline must decide *which* lambda
variant to construct.  The arrow type `[Domain -> Codomain]` determines this:
the binder's domain category is inferred from how the bound variable is
**used** inside the body.  This document traces the inference mechanism through
every stage, from the generated type system to parse-time variant selection.

## 1. Why Arrow Types Matter for Binders

A binder `^x.{body}` is syntactic sugar for a lambda abstraction.  The `^`
sigil introduces a new binding — but unlike constructor-embedded binders such
as `PNew` (`new(x, p)`), a standalone lambda must know the **domain category**
of the bound variable in order to select the correct AST variant.

```text
^x.{x!(p)}     → x used as Name (channel)   → Proc::LamName(scope)
^x.{x | q}     → x used as Proc (parallel)  → Proc::LamProc(scope)
^n.@(n)        → n used as Proc (NQuote)    → Name::LamProc(scope)
```

The arrow type `[Name -> Proc]` means "binds a `Name`, produces a `Proc`".
The codomain is always the enclosing parse category; the domain is inferred
from the body.

## 2. Auto-Generated Lambda and Application Variants

**File:** `macros/src/gen/types/enums.rs`

For every category (the codomain), the pipeline generates four variant families
for every other category (the domain) — including self-pairings.  For *N*
categories, this produces *4N* variants per codomain category (*4N²* total).

### Generation Loop

```rust
for domain_lang_type in &language.types {
    let domain_name = &domain_lang_type.name;

    // Lam{Domain}: single-binder lambda [Domain -> Codomain]
    // e.g. LamName(Scope<Binder<String>, Box<Proc>>)
    variants.push(quote! {
        #lam_variant(mettail_runtime::Scope<
            mettail_runtime::Binder<String>, Box<#cat_name>>)
    });

    // MLam{Domain}: multi-binder lambda [Domain* -> Codomain]
    // e.g. MLamName(Scope<Vec<Binder<String>>, Box<Proc>>)
    variants.push(quote! {
        #mlam_variant(mettail_runtime::Scope<
            Vec<mettail_runtime::Binder<String>>, Box<#cat_name>>)
    });

    // Apply{Domain}: unevaluated application Apply(lambda, arg)
    // e.g. ApplyName(Box<Proc>, Box<Name>)
    variants.push(quote! {
        #apply_variant(Box<#cat_name>, Box<#domain_name>)
    });

    // MApply{Domain}: multi-argument application MApply(lambda, args)
    // e.g. MApplyName(Box<Proc>, Vec<Name>)
    variants.push(quote! {
        #mapply_variant(Box<#cat_name>, Vec<#domain_name>)
    });
}
```

### Concrete Example: RhoCalc (`{Proc, Name}`)

| Category | Generated Variants                                                    |
|----------|-----------------------------------------------------------------------|
| `Proc`   | `LamProc(Scope<Binder<String>, Box<Proc>>)` — `[Proc -> Proc]`        |
|          | `LamName(Scope<Binder<String>, Box<Proc>>)` — `[Name -> Proc]`        |
|          | `MLamProc(Scope<Vec<Binder<String>>, Box<Proc>>)` — `[Proc* -> Proc]` |
|          | `MLamName(Scope<Vec<Binder<String>>, Box<Proc>>)` — `[Name* -> Proc]` |
|          | `ApplyProc(Box<Proc>, Box<Proc>)`                                     |
|          | `ApplyName(Box<Proc>, Box<Name>)`                                     |
|          | `MApplyProc(Box<Proc>, Vec<Proc>)`                                    |
|          | `MApplyName(Box<Proc>, Vec<Name>)`                                    |
| `Name`   | `LamProc(Scope<Binder<String>, Box<Name>>)` — `[Proc -> Name]`        |
|          | `LamName(Scope<Binder<String>, Box<Name>>)` — `[Name -> Name]`        |
|          | `MLamProc(Scope<Vec<Binder<String>>, Box<Name>>)` — `[Proc* -> Name]` |
|          | `MLamName(Scope<Vec<Binder<String>>, Box<Name>>)` — `[Name* -> Name]` |
|          | `ApplyProc(Box<Name>, Box<Proc>)`                                     |
|          | `ApplyName(Box<Name>, Box<Name>)`                                     |
|          | `MApplyProc(Box<Name>, Vec<Proc>)`                                    |
|          | `MApplyName(Box<Name>, Vec<Name>)`                                    |

**Naming convention:**
- `Lam{Domain}` — domain is the binder's category; codomain is the enum's category
- `Apply{Domain}` — domain is the argument's category; the first `Box` is the
  lambda (same category as the enum)

## 3. The InferredType Enum

**File:** `macros/src/gen/syntax/var_inference.rs`

The pipeline generates three types at compile time that are emitted into the
language module:

```rust
/// Possible base categories for variable classification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarCategory {
    Proc,
    Name,
    // ... one variant per category
}

/// Full type of a variable, including function types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferredType {
    Base(VarCategory),                              // e.g. Name
    Arrow(Box<InferredType>, Box<InferredType>),    // e.g. [Name -> Proc]
    MultiArrow(Box<InferredType>, Box<InferredType>), // e.g. [Name* -> Proc]
}
```

### The `base_type()` Method

`base_type()` extracts the *representation category* — the enum that
physically stores a value of this type.  For function types, this is the
codomain's base type, because `[A -> B]` is stored as a `B` value (a
`Lam{A}` variant inside the `B` enum).

```rust
impl InferredType {
    pub fn base_type(&self) -> VarCategory {
        match self {
            InferredType::Base(cat) => *cat,
            InferredType::Arrow(_, codomain) => codomain.base_type(),
            InferredType::MultiArrow(_, codomain) => codomain.base_type(),
        }
    }
}
```

**Examples:**

| Inferred Type                                                 | `base_type()` | Stored As                                 |
|---------------------------------------------------------------|---------------|-------------------------------------------|
| `Base(Name)`                                                  | `Name`        | `Name::NVar(...)` or other `Name` variant |
| `Base(Proc)`                                                  | `Proc`        | `Proc::PVar(...)` or other `Proc` variant |
| `Arrow(Name, Proc)` — `[Name -> Proc]`                        | `Proc`        | `Proc::LamName(scope)`                    |
| `Arrow(Proc, Name)` — `[Proc -> Name]`                        | `Name`        | `Name::LamProc(scope)`                    |
| `Arrow(Name, Arrow(Name, Proc))` — `[Name -> [Name -> Proc]]` | `Proc`        | Nested `Proc::LamName(...)`               |

## 4. Inference Rules

**File:** `macros/src/gen/syntax/var_inference.rs`

Two methods are generated for each category: `infer_var_category()` (returns
`Option<VarCategory>`) and `infer_var_type()` (returns `Option<InferredType>`).
Both are generated by `generate_var_category_inference()`.

### Rule 1: Constructor Position

When a variable appears as a field of a known constructor, its category is
determined by the constructor's signature.

```text
x in POutput(x, p)    →  x : Name       (POutput's first field is Name)
p in PPar(..., p, ...) →  p : Proc       (PPar's elements are Proc)
n in NQuote(n)         →  n : Proc       (NQuote's field is Proc)
```

Generated match arm (conceptual):

```rust
Proc::POutput(ref f0, ref f1) => {
    // f0 is Name, f1 is Proc — recurse into both
    if let Some(cat) = f0.infer_var_category(var_name) { return Some(cat); }
    if let Some(cat) = f1.infer_var_category(var_name) { return Some(cat); }
    None
}
```

When the recursion reaches a `Var` variant whose name matches, the base
category is returned:

```rust
Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(ref fv))) => {
    if fv.pretty_name.as_deref() == Some(var_name) {
        return Some(VarCategory::Name);
    }
    None
}
```

### Rule 2: Application Position (Function Types)

When a variable appears in the **function position** of an application
`Apply{Domain}(f, arg)`, it is inferred as a function type
`[Domain -> Codomain]` where the codomain is the enclosing category.

```rust
Proc::ApplyName(ref lam, ref arg) => {
    // Check if variable is in function position
    if let Proc::PVar(mettail_runtime::OrdVar(
        mettail_runtime::Var::Free(ref fv))) = **lam
    {
        if fv.pretty_name.as_deref() == Some(var_name) {
            // f in ApplyName(f, x) where context is Proc
            // → f : [Name -> Proc]
            return Some(InferredType::Arrow(
                Box::new(InferredType::Base(VarCategory::Name)),
                Box::new(InferredType::Base(VarCategory::Proc))
            ));
        }
    }
    // Otherwise recurse into both subterms
    if let Some(t) = lam.infer_var_type(var_name) { return Some(t); }
    if let Some(t) = arg.infer_var_type(var_name) { return Some(t); }
    None
}
```

Multi-application follows the same pattern:

```text
f in MApplyName(f, [x, y, z])  →  f : [Name* -> Proc]
                                    (MultiArrow variant)
```

### Rule 3: Recursive Traversal

Inference recurses into all subterms:
- **Constructor fields** — recurse via `field.infer_var_type(var_name)`
- **Collections** — iterate and recurse: `for item in bag.iter() { ... }`
- **Scoped bodies** — `scope.unsafe_body().infer_var_type(var_name)` for
  `Lam{X}` and `MLam{X}` variants
- **Binder scopes** — same `unsafe_body()` access for constructor-embedded
  binders (PNew, PInput, etc.)

The first match wins — the traversal is depth-first, left-to-right.

## 5. Parse-Time Variant Selection

**File:** `prattail/src/recursive.rs` — `write_lambda_handlers()`

When the parser encounters `Token::Caret` (`^`), it enters the lambda handler.
After parsing the binder name(s) and body, it calls `infer_var_type()` on the
body and uses `base_type()` to select the variant.

### Single Lambda: `^x.{body}`

```text
Token stream:      ^     x     .     {    body    }
                   ▲     ▲     ▲     ▲     ▲      ▲
parse_lambda:      │     │     │     │     │      │
  consume ─────────┘     │     │     │     │      │
  expect_ident ──────────┘     │     │     │      │
  expect Dot ──────────────────┘     │     │      │
  expect LBrace ─────────────────────┘     │      │
  parse_{Cat}(0) ──────────────────────────┘      │
  expect RBrace ──────────────────────────────────┘
```

Generated handler (conceptual):

```rust
// After parsing binder_name and body:
let inferred = body.infer_var_type(&binder_name);
let scope = mettail_runtime::Scope::new(
    mettail_runtime::Binder(mettail_runtime::get_or_create_var(binder_name)),
    Box::new(body),
);
Ok(match inferred {
    Some(InferredType::Base(VarCategory::Proc)) => Proc::LamProc(scope),
    Some(InferredType::Base(VarCategory::Name)) => Proc::LamName(scope),
    // ... one arm per category ...
    _ => Proc::LamProc(scope)   // default: same-category lambda
})
```

The `match` arms are generated dynamically — one per category — by
`write_lambda_handlers()`.  Each arm matches only `InferredType::Base(...)`.
For higher-order types like `Arrow(Name, Proc)`, none of the `Base` arms
match, so the wildcard `_` fires and the **default variant** (same-category
lambda, e.g. `LamProc` when parsing `Proc`) is used.  This is correct because
`[A -> B]` is stored as a `B` value — when parsing category `Proc`, the
default `LamProc` means "the binder's representation type is `Proc`", which
is the codomain of any arrow type with codomain `Proc`.

### Multi Lambda: `^[x, y].{body}`

```text
Token stream:   ^  [  x  ,  y  ]  .  {  body  }
```

Inference uses the **first** binder name to determine the domain:

```rust
let inferred = if let Some(name) = binder_names.first() {
    body.infer_var_type(name)
} else {
    None
};
// ... construct scope, match on inferred → MLam{Domain}
```

## 6. Higher-Order Example

**Input:** `^cont.{$name(cont, y)}`

### Step-by-step

1. **Parse** `^cont.{...}` — `cont` is the binder name

2. **Parse body** `$name(cont, y)`:
   - `$name` is the dollar-syntax prefix for domain `Name`
   - Parsed as `Proc::ApplyName(Box::new(cont_var), Box::new(y_name))`

3. **Infer** `body.infer_var_type("cont")`:
   - Match `Proc::ApplyName(ref lam, ref arg)`
   - Check: is `lam` a free variable named `"cont"`? — **Yes**
   - Domain: `VarCategory::Name` (from `ApplyName`)
   - Codomain: `VarCategory::Proc` (the enclosing category)
   - Result: `InferredType::Arrow(Base(Name), Base(Proc))` — `[Name -> Proc]`

4. **Select variant** via match:
   - `inferred` = `Some(Arrow(Base(Name), Base(Proc)))` — `[Name -> Proc]`
   - Match arm `Some(InferredType::Base(VarCategory::Proc))` does **not** match
     (it is `Arrow`, not `Base`)
   - Match arm `Some(InferredType::Base(VarCategory::Name))` does **not** match
   - Wildcard `_` fires → default: `Proc::LamProc(scope)`
   - This is correct: `[Name -> Proc]` has codomain `Proc`, and `LamProc` is
     the same-category default when parsing `Proc`

5. **Construct AST:**
   ```text
   Proc::LamProc(
       Scope::new(
           Binder(get_or_create_var("cont")),
           Box::new(Proc::ApplyName(
               Box::new(Proc::PVar(cont)),
               Box::new(Name::NVar(y))
           ))
       )
   )
   ```

### Nested Higher-Order

For `^n.^a.^cont.{{$name(dup, n) | n!(a?y.{{$name(cont,y) | $name(dup, n)}})}}`:

| Binder | Usage                                               | Inferred Type    | Variant         |
|--------|-----------------------------------------------------|------------------|-----------------|
| `cont` | `$name(cont, y)` → function position of `ApplyName` | `[Name -> Proc]` | `Proc::LamProc` |
| `a`    | `a?y.{...}` → channel in `PInput`                   | `Name`           | `Proc::LamName` |
| `n`    | `n!(...)` → channel in `POutput`                    | `Name`           | `Proc::LamName` |

Constructed (inside-out):

```text
Proc::LamName(^n.                          ← n : Name
  Proc::LamName(^a.                        ← a : Name
    Proc::LamProc(^cont.                   ← cont : [Name -> Proc], base_type() = Proc
      Proc::PPar({...})
    )
  )
)
```

The full curried type is `[Name -> [Name -> [[Name -> Proc] -> Proc]]]`.

## 7. Dollar Syntax Connection

**File:** `prattail/src/recursive.rs` — `write_dollar_handlers()`

Dollar syntax is the concrete notation for explicit function application.  The
dollar prefix specifies the **domain** category; the **codomain** is always the
enclosing parse category.

| Syntax            | Token                  | Parsed As                                    |
|-------------------|------------------------|----------------------------------------------|
| `$name(f, x)`     | `Token::DollarName`    | `{Cat}::ApplyName(Box::new(f), Box::new(x))` |
| `$proc(f, x)`     | `Token::DollarProc`    | `{Cat}::ApplyProc(Box::new(f), Box::new(x))` |
| `$$name(f, x, y)` | `Token::DdollarNameLp` | `{Cat}::MApplyName(Box::new(f), vec![x, y])` |
| `$$proc(f, x, y)` | `Token::DdollarProcLp` | `{Cat}::MApplyProc(Box::new(f), vec![x, y])` |

### Single Apply: `$name(f, x)`

```text
Token stream:          $name  (  f  ,  x  )
                         ▲    ▲  ▲  ▲  ▲  ▲
parse_dollar_name:       │    │  │  │  │  │
  consume DollarName ────┘    │  │  │  │  │
  consume LParen ─────────────┘  │  │  │  │
  parse_{Cat}(0) ────────────────┘  │  │  │  ← f : same category
  consume Comma ────────────────────┘  │  │
  parse_{Dom}(0) ──────────────────────┘  │  ← x : domain category
  consume RParen ─────────────────────────┘
  → Cat::ApplyName(Box::new(f), Box::new(x))
```

### Multi Apply: `$$name(f, x, y, ...)`

```text
Token stream:          $$name(  f  ,  x  ,  y  )
                          ▲     ▲  ▲  ▲  ▲  ▲  ▲
parse_ddollar_name:       │     │  │  │  │  │  │
  consume DdollarNameLp ──┘     │  │  │  │  │  │
  parse_{Cat}(0) ───────────────┘  │  │  │  │  │  ← f : same category
  consume Comma ───────────────────┘  │  │  │  │
  loop:                               │  │  │  │
    iter 1:                           │  │  │  │
      parse_{Dom}(0) ─────────────────┘  │  │  │  ← x : domain category
      peek Comma? → consume, continue ───┘  │  │
    iter 2:                                 │  │
      parse_{Dom}(0) ───────────────────────┘  │  ← y : domain category
      peek Comma? → no (RParen) → break        │
  consume RParen ──────────────────────────────┘
  → Cat::MApplyName(Box::new(f), vec![x, y])
```

> **Tokenization asymmetry — `$` vs `$$`:** In Multi Apply, `$$name(` is a
> **single fused token** (`Token::DdollarNameLp`). The opening parenthesis is
> consumed as part of the token because without it the lexer would see `$` +
> `$name`, creating ambiguity with the single-dollar prefix (see
> `prattail/docs/design/recursive-descent-generator.md`, lines 541-543). In
> Single Apply, `$name` is a standalone token and `(` is parsed separately as
> `Token::LParen`. Because the lexer skips whitespace between tokens, this means
> `$name (x)` with arbitrary whitespace before `(` is accepted, while `$$name
> (f, x, y)` with a space before `(` is a **parse error**. This asymmetry is
> consistent across both parser backends (legacy LALRPOP and PraTTaIL) — fusing
> `$name(` into one token would eliminate the discrepancy but is not strictly
> necessary since `$name` is already unambiguous as a single-dollar prefix.

Dollar syntax creates the `Apply{Domain}` and `MApply{Domain}` nodes that the
type inference engine (Rule 2) examines to determine function types.

## 8. Beta-Reduction via `normalize_term`

**File:** `macros/src/gen/term_ops/normalize.rs` — `generate_beta_reduction_arms()`

When an `Apply{Domain}(lam, arg)` meets a `Lam{Domain}(scope)`, beta-reduction
fires — the scope is unbound and the argument is substituted for the binder.

### Single Beta-Reduction

```text
ApplyName(LamName(scope), arg)
  → scope.unbind() → (binder, body)
  → body.substitute_name(&binder.0, &arg_normalized)
  → result.normalize()
```

Generated (conceptual):

```rust
Proc::ApplyName(lam_box, arg_box) => {
    let lam_normalized = lam_box.as_ref().normalize();
    match &lam_normalized {
        Proc::LamName(scope) => {
            let (binder, body) = scope.clone().unbind();
            let arg_normalized = arg_box.as_ref().normalize();
            (*body).substitute_name(&binder.0, &arg_normalized).normalize()
        }
        _ => {
            // Not a redex — normalize subterms
            Proc::ApplyName(
                Box::new(lam_normalized),
                Box::new(arg_box.as_ref().normalize())
            )
        }
    }
}
```

### Multi Beta-Reduction

```text
MApplyName(MLamName(scope), [a1, a2, ...])
  → scope.unbind() → (binders, body)
  → body.multi_substitute_name(&vars, &args_normalized)
  → result.normalize()
```

### Key Properties

- **Normalize-before-substitute**: both the function and arguments are
  normalized before substitution, enabling nested redexes to reduce
- **Domain matching**: `ApplyName` only beta-reduces with `LamName` (not
  `LamProc`); the domain must agree
- **Non-redex passthrough**: if the function position is not a lambda after
  normalization, the `Apply` node is preserved with normalized subterms

## 9. Pipeline Summary

```text
  DSL: ^x.{body}                    Concrete syntax
       │
       ▼
  Token::Caret → parse_lambda()     prattail/src/recursive.rs
       │
       ├── parse binder name ("x")
       ├── parse body (Proc at bp=0)
       │
       ▼
  body.infer_var_type("x")          var_inference.rs (generated)
       │
       ├── Rule 1: Constructor position → Base(Name/Proc)
       ├── Rule 2: Application position → Arrow(Domain, Codomain)
       ├── Rule 3: Recurse into subterms
       │
       ▼
  InferredType → base_type()        var_inference.rs
       │
       ├── Base(Name) → VarCategory::Name
       ├── Base(Proc) → VarCategory::Proc
       ├── Arrow(_, codomain) → codomain.base_type()
       │
       ▼
  match base_type() {               parse_lambda (generated)
    Name => Cat::LamName(scope),
    Proc => Cat::LamProc(scope),
  }
       │
       ▼
  AST: Cat::Lam{Domain}(           types/enums.rs (generated)
    Scope<Binder<String>,
          Box<Cat>>)
       │
       ▼
  normalize_term():                  normalize.rs (generated)
    Apply{D}(Lam{D}(scope), arg)
    → beta-reduce via substitute_{d}
```

---

**See also:**
- [00-overview.md](00-overview.md) — Binder overview and key types
- [01-single-binders.md](01-single-binders.md) — Single-binder pipeline trace (PNew)
- [02-multi-binders.md](02-multi-binders.md) — Multi-binder pipeline trace (PInputs)
- [Lambda Environment Design](../../../../design/made/lambda-environment-design.md) — Original design doc
