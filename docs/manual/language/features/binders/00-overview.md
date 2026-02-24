# Binders — Overview

Binders are variable-binding constructs that introduce scoped names into terms.
When a binder introduces a variable *x* in a body *p*, every free occurrence of
*x* inside *p* refers to that binding — and two terms that differ only in the
*name* of the bound variable are considered **alpha-equivalent**.

MeTTaIL supports two kinds of binders:

| Kind       | DSL Syntax                | Example Rule | Concrete Syntax  |
|------------|---------------------------|--------------|------------------|
| **Single** | `^x.p:[Name -> Proc]`     | `PNew`       | `new(x, p)`      |
| **Multi**  | `^[xs].p:[Name* -> Proc]` | `PInputs`    | `(n?x, m?y).{p}` |

## Key Types

| Type                      | Crate                                         | Purpose                                                |
|---------------------------|-----------------------------------------------|--------------------------------------------------------|
| `Binder<String>`          | `moniker` (re-exported via `mettail_runtime`) | Wraps a `FreeVar<String>` to mark a binding position   |
| `FreeVar<String>`         | `moniker`                                     | Globally unique variable with a human-readable name    |
| `Scope<P, T>`             | `mettail_runtime::binding`                    | Pairs a pattern *P* (the binder) with a body *T*       |
| `get_or_create_var(name)` | `mettail_runtime::binding`                    | Thread-local cache ensuring same name → same `FreeVar` |

The wrapper `mettail_runtime::Scope` adds `Hash`, `Ord`, and `BoundTerm`
implementations that the upstream `moniker::Scope` lacks — required by Ascent
relations and term enumeration.

## Thread-Local Variable Cache

Parsing a single term must produce the **same** `FreeVar` for repeated
occurrences of the same variable name.  A thread-local `VAR_CACHE`
(`RefCell<HashMap<String, FreeVar<String>>>`) guarantees this:

```text
get_or_create_var("x")
  ├─ cache hit  → return existing FreeVar
  └─ cache miss → FreeVar::fresh_named("x"), insert, return
```

`clear_var_cache()` is called between independent parse sessions so that
variables from different terms do not accidentally share identity.

## Pipeline Diagram

```text
    DSL definition                          Source files
    ──────────────                          ────────────
    ^x.p:[Name -> Proc]                     macros/src/ast/grammar.rs
            │
            ▼
    TermParam::Abstraction                  macros/src/ast/grammar.rs
    { binder: x, body: p,
      ty: Arrow(Base(Name),
                Base(Proc)) }
            │
            ▼
    SyntaxItemSpec::Binder                  prattail/src/lib.rs
    { param_name: "x",
      category: "Name",
      is_multi: false }
            │
            ▼
    classify::classify_rule()               prattail/src/classify.rs
    → has_binder = true
            │
            ▼
    RD handler / trampoline                 prattail/src/recursive.rs
    → expect_ident(tokens, pos)             prattail/src/trampoline.rs
    → Binder(get_or_create_var(x))
    → Scope::new(binder, Box::new(body))
            │
            ▼
    AST: Proc::PNew(                        runtime/src/binding.rs
      Scope<Binder<String>,
            Box<Proc>>)
            │
            ▼
    Ascent: scope kept opaque               macros/src/logic/congruence.rs
    → unsafe_body() for recursive           macros/src/logic/categories.rs
      exploration and rewriting
```

## Reading Guide

| Document                                                 | Content                                                                   |
|----------------------------------------------------------|---------------------------------------------------------------------------|
| [01-single-binders.md](01-single-binders.md)             | Full pipeline trace for `^x.p:[Name -> Proc]` using `PNew`                |
| [02-multi-binders.md](02-multi-binders.md)               | Full pipeline trace for `^[xs].p:[Name* -> Proc]` using `PInputs`         |
| [03-arrow-type-inference.md](03-arrow-type-inference.md) | Arrow type inference: how `^x.{body}` selects `Lam{Domain}` at parse time |

Multi-binders interact with [ZipMapSep](../ZipMapSep/00-overview.md) and
[collections](../collections/00-overview.md) — cross-references are provided
where features intersect.

## Source Files

| File                                              | Role                                                                                     |
|---------------------------------------------------|------------------------------------------------------------------------------------------|
| `macros/src/ast/grammar.rs`                       | `TermParam::Abstraction`, `TermParam::MultiAbstraction`                                  |
| `macros/src/gen/syntax/parser/prattail_bridge.rs` | `classify_param_from_context()`, binder → `SyntaxItemSpec::Binder`                       |
| `macros/src/gen/syntax/var_inference.rs`          | `InferredType` enum, `infer_var_category()`, `infer_var_type()`, `base_type()`           |
| `macros/src/gen/types/enums.rs`                   | Auto-generated `Lam{Domain}`, `MLam{Domain}`, `Apply{Domain}`, `MApply{Domain}` variants |
| `macros/src/gen/term_ops/normalize.rs`            | Beta-reduction: `Apply{D}(Lam{D}(scope), arg)` → substitute                              |
| `prattail/src/lib.rs`                             | `SyntaxItemSpec::Binder` variant, `RuleSpec` flags                                       |
| `prattail/src/classify.rs`                        | `has_binder_recursive()`, flag derivation                                                |
| `prattail/src/recursive.rs`                       | `write_rd_handler()`, `write_lambda_handlers()`, `write_dollar_handlers()`               |
| `prattail/src/trampoline.rs`                      | Frame variants, inline binder handling                                                   |
| `runtime/src/binding.rs`                          | `Scope`, `Binder`, `get_or_create_var()`, `VAR_CACHE`                                    |
