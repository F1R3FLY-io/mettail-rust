# Sep / Map / Zip — Composable Pattern Operations

Sep, Map, and Zip are three composable `SyntaxItemSpec` variants that replace
the old monolithic `ZipMapSep`. Each is an independent operation that can be
used standalone or in composition:

| Variant  | Purpose                                                      |
|----------|--------------------------------------------------------------|
| `Sep`    | Repeat a body pattern with a separator between repetitions   |
| `Map`    | Structured body template: multiple items forming one element |
| `Zip`    | Dual-accumulator: left and right collections in lockstep     |

## Motivating Example

RhoCalc's `PInputs` rule uses `Sep(Zip(Map(...)))` to parse channel-variable pairs:

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

## Composed Representation

The DSL `PatternOp::Sep { source: Map { source: Zip { ... } } }` is converted
by the bridge into a composed `SyntaxItemSpec` tree:

```rust
SyntaxItemSpec::Sep {
    body: Box::new(SyntaxItemSpec::Zip {
        left_name: "ns",
        right_name: "xs",
        left_category: "Name",
        right_category: "Name",
        body: Box::new(SyntaxItemSpec::Map {
            body_items: [NonTerminal("Name", "n"), Terminal("?"), Binder("x", "Name")],
        }),
    }),
    separator: ",",
    kind: CollectionKind::Vec,
}
```

## New Composition Capabilities

The decomposition enables compositions that were not previously possible:

| Composition            | Use Case                                       |
|------------------------|-------------------------------------------------|
| `Sep(Zip(Map(...)))`   | Dual-accumulator structured list (PInputs)      |
| `Sep(Map(...))`        | Single-accumulator structured list              |
| `Sep(NonTerminal)`     | Simple separated list                           |
| `Sep(IdentCapture)`    | Separated identifier list                       |
| `Sep(Binder)`          | Separated binder list                           |
| `Map(...)` standalone  | Inline sequence of items                        |
| `Zip(Map(...))` standalone | Dual accumulators without separator          |

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
    SyntaxItemSpec::Sep {                   prattail/src/lib.rs
      body: Zip { ...,
        body: Map { body_items } },
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

Sep/Map/Zip combines with:
- [Multi-binders](../binders/02-multi-binders.md) — `^[xs]` provides the
  right-side bound variables
- [Collections](../collections/00-overview.md) — the left side `ns:Vec(Name)`
  is an ordered collection

## Source Files

| File                                              | Role                                                      |
|---------------------------------------------------|-----------------------------------------------------------|
| `macros/src/ast/grammar.rs`                       | `PatternOp::Sep`, `PatternOp::Map`, `PatternOp::Zip`      |
| `macros/src/gen/syntax/parser/prattail_bridge.rs` | `convert_chained_sep()`, parameter mapping                 |
| `prattail/src/lib.rs`                             | `SyntaxItemSpec::Sep`, `Map`, `Zip` variants               |
| `prattail/src/classify.rs`                        | `has_binder_recursive()` (recurses into Sep/Map/Zip)       |
| `prattail/src/recursive.rs`                       | `RDSyntaxItem::Sep/Map/Zip`, codegen helpers               |
| `prattail/src/trampoline.rs`                      | `has_complex_sep()`, `should_use_standalone_fn()` routing  |
| `macros/src/logic/categories.rs`                  | `generate_collection_plus_binding_deconstruction()`        |
