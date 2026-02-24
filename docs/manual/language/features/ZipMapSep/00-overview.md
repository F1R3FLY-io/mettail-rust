# ZipMapSep — Overview

ZipMapSep is a three-stage metasyntax for parsing **pairwise-structured
patterns** — separated lists where each element contains a structured pair of
sub-terms.  The three stages are:

| Stage                    | Syntax                                    | Purpose               |
|--------------------------|-------------------------------------------|-----------------------|
| `*zip(a, b)`             | Pair two parameter lists element-wise     | `a₁↔b₁`, `a₂↔b₂`, ... |
| `*map(\|x, y\| pattern)` | Apply a syntax template to each pair      | `x "?" y` → `n?x`     |
| `*sep(delim)`            | Separate mapped elements with a delimiter | `n?x, m?y`            |

## Motivating Example

RhoCalc's `PInputs` rule uses ZipMapSep to parse channel-variable pairs:

```text
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

Concrete syntax: `(n?x, m?y).{body}` — each pair `n?x` associates a channel
name `n` with a bound variable `x`.

The three stages unpack as:

```text
*zip(ns, xs)                 ← pair channels with bound variables
  .*map(|n, x| n "?" x)     ← each pair formatted as "channel ? variable"
  .*sep(",")                 ← pairs separated by commas
```

## How the Stages Compose

```text
  Parameters:  ns = [n₁, n₂, n₃]     xs = [x₁, x₂, x₃]
                       │                       │
  *zip(ns, xs)         ├──────── zip ──────────┘
                       ▼
                  [(n₁,x₁), (n₂,x₂), (n₃,x₃)]
                       │
  .*map(|n,x| ...)     ▼  apply pattern to each pair
                       │
                  [n₁ "?" x₁,  n₂ "?" x₂,  n₃ "?" x₃]
                       │
  .*sep(",")           ▼  join with separator
                       │
                  n₁ "?" x₁ ","  n₂ "?" x₂ ","  n₃ "?" x₃
```

## Pipeline Diagram

```text
    DSL definition                          Source files
    ──────────────                          ────────────
    *zip(ns,xs).*map(|n,x| n "?" x)        macros/src/ast/grammar.rs
        .*sep(",")
            │
            ▼
    PatternOp::Sep {                        macros/src/ast/grammar.rs
      source: Some(Map {
        source: Zip { left: ns,
                      right: xs },
        params: [n, x],
        body: [Param(n), Lit("?"),
               Param(x)] }),
      separator: "," }
            │
            ▼
    SyntaxItemSpec::ZipMapSep {             prattail/src/lib.rs
      left_name: "ns",
      right_name: "xs",
      left_category: "Name",
      right_category: "Name",
      body_items: [NonTerminal, Terminal,
                   Binder],
      separator: "," }
            │
            ▼
    should_use_standalone_fn() → true       prattail/src/trampoline.rs
    → Standalone parse function
    → Never trampolined
            │
            ▼
    parse_pinputs(tokens, pos):             prattail/src/recursive.rs
      loop { parse n, "?", x; push ns/xs;
             check ","; } ...
            │
            ▼
    AST: Proc::PInputs(                    languages/src/rhocalc.rs
      Vec<Name>,
      Scope<Vec<Binder<String>>,
            Box<Proc>>)
            │
            ▼
    Ascent: decompose ns + body             macros/src/logic/categories.rs
```

## Reading Guide

| Document                                             | Content                                                |
|------------------------------------------------------|--------------------------------------------------------|
| [01-dsl-and-ast.md](01-dsl-and-ast.md)               | DSL syntax, nested `PatternOp` tree, bridge conversion |
| [02-parser-and-runtime.md](02-parser-and-runtime.md) | Standalone parse function, Ascent rules, runtime trace |

## Related Features

ZipMapSep combines with:
- [Multi-binders](../binders/02-multi-binders.md) — `^[xs]` provides the
  right-side bound variables
- [Collections](../collections/00-overview.md) — the left side `ns:Vec(Name)`
  is an ordered collection

## Source Files

| File                                              | Role                                                    |
|---------------------------------------------------|---------------------------------------------------------|
| `macros/src/ast/grammar.rs`                       | `PatternOp::Sep`, `PatternOp::Map`, `PatternOp::Zip`    |
| `macros/src/gen/syntax/parser/prattail_bridge.rs` | `convert_chained_sep()`, parameter mapping              |
| `prattail/src/lib.rs`                             | `SyntaxItemSpec::ZipMapSep` variant                     |
| `prattail/src/classify.rs`                        | `has_binder_recursive()` (recurses into body_items)     |
| `prattail/src/recursive.rs`                       | `RDSyntaxItem::ZipMapSep`, standalone function codegen  |
| `prattail/src/trampoline.rs`                      | `has_zipmapsep()`, `should_use_standalone_fn()` routing |
| `macros/src/logic/categories.rs`                  | `generate_collection_plus_binding_deconstruction()`     |
