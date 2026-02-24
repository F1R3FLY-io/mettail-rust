# Macro Expansion: `LanguageDef` → `LanguageSpec`

The `language!` invocation in `languages/src/rhocalc.rs` is processed in two
phases inside the proc-macro.  Phase 1 parses the DSL token stream into a rich
`LanguageDef` AST.  Phase 2 projects the grammar-relevant subset into a
`LanguageSpec` that PraTTaIL uses for code generation.

## Phase 1: DSL → `LanguageDef`

**Entry point:** `macros/src/ast/language.rs` — `impl Parse for LanguageDef`

The `syn` parser walks the token stream section by section:

```
language! { name: RhoCalc, types { ... }, terms { ... }, equations { ... },
            rewrites { ... }, logic { ... } }
```

Each section is guarded by keyword peek (`"types"`, `"terms"`, etc.) and
delegated to a section parser.  The result is:

```rust
pub struct LanguageDef {
    pub name: Ident,                            // RhoCalc
    pub options: HashMap<String, AttributeValue>, // (empty for RhoCalc)
    pub types: Vec<LangType>,                    // [Proc, Name, Int, ...]
    pub terms: Vec<GrammarRule>,                 // [PZero, PDrop, PPar, ...]
    pub equations: Vec<Equation>,                // [QuoteDrop]
    pub rewrites: Vec<RewriteRule>,              // [Comm, Exec, ParCong, ...]
    pub logic: Option<LogicBlock>,               // Some(path, trans rules)
}
```

### Type parsing

```rust
pub struct LangType {
    pub name: Ident,                  // e.g., Int
    pub native_type: Option<Type>,    // e.g., Some(i64)
}
```

The `![i64] as Int` syntax is parsed as: `!` `[` type `]` `as` ident.
Plain category names (`Proc`, `Name`) have `native_type: None`.

### Term parsing

Each term becomes a `GrammarRule` (defined in `macros/src/ast/grammar.rs`):

```rust
pub struct GrammarRule {
    pub label: Ident,                       // Add
    pub category: Ident,                    // Proc
    pub term_context: Option<Vec<TermParam>>,  // [a:Proc, b:Proc]
    pub syntax_pattern: Option<Vec<SyntaxExpr>>,  // [Param(a), Literal("+"), Param(b)]
    pub items: Vec<GrammarItem>,            // (fallback for old-style rules)
    pub rust_code: Option<RustCodeBlock>,   // Some({ match ... })
    pub eval_mode: Option<EvalMode>,        // Some(Fold)
    pub is_right_assoc: bool,               // false
    pub prefix_bp: Option<u8>,              // None
}
```

Term parameters are parsed into `TermParam` variants:

| DSL syntax                | `TermParam` variant                                                            | Example |
|---------------------------|--------------------------------------------------------------------------------|---------|
| `n:Name`                  | `Simple { name: n, ty: Base(Name) }`                                           | PDrop   |
| `^x.p:[Name -> Proc]`     | `Abstraction { binder: x, body: p, ty: Arrow(Name, Proc) }`                    | PNew    |
| `^[xs].p:[Name* -> Proc]` | `MultiAbstraction { binder: xs, body: p, ty: Arrow(MultiBinder(Name), Proc) }` | PInputs |
| `ps:HashBag(Proc)`        | `Simple { name: ps, ty: Collection(HashBag, Base(Proc)) }`                     | PPar    |

Syntax patterns are parsed into `SyntaxExpr` variants:

| DSL syntax                                | `SyntaxExpr` variant                                    |
|-------------------------------------------|---------------------------------------------------------|
| `"+"`                                     | `Literal("+")`                                          |
| `a` (param ref)                           | `Param(a)`                                              |
| `ps.*sep("\|")`                           | `Op(Sep { collection: ps, separator: "\|" })`           |
| `*zip(ns,xs).*map(\|n,x\| ...).*sep(",")` | `Op(Sep { source: Some(Map { source: Zip { ... } }) })` |

### Equation and rewrite parsing

Both use *unified judgement syntax*:

```
Name . type_context | prop_context |- LHS op RHS ;
```

- **Type context**: explicit type bindings (e.g., `P:Proc`) — rarely used since
  patterns imply types
- **Propositional context**: premises after `|`
  - Freshness: `x # T` (variable `x` is fresh in `T`)
  - Congruence: `S ~> T` (rewrites-only: if `S` rewrites to `T`)
  - Relation query: `rel(args)` (e.g., `env_var(x, v)`)
- **LHS/RHS**: parsed as `Pattern` trees (constructor applications, collection
  patterns, lambda patterns, zip/map metasyntax)

The `~>` symbol distinguishes rewrites from equations (`=`).

## Phase 2: `LanguageDef` → `LanguageSpec` (Bridge)

**Entry point:** `macros/src/gen/syntax/parser/prattail_bridge.rs` —
`language_def_to_spec()`

The bridge is a *structural mapping* — it converts the rich `LanguageDef` types
into PraTTaIL's simplified `LanguageSpec` types.  All *semantic classification*
(is_infix, is_cast, etc.) is deferred to PraTTaIL's `classify` module.

### Category mapping

```rust
let categories: Vec<CategorySpec> = language.types.iter().enumerate()
    .map(|(idx, t)| CategorySpec {
        name: t.name.to_string(),               // "Proc"
        native_type: t.native_type.as_ref()      // Some("i64")
            .map(native_type_to_string),
        is_primary: idx == 0,                     // true for Proc
    })
    .collect();
```

The first declared type is always the primary category.

### Rule mapping

Each `GrammarRule` becomes a `RuleSpecInput`:

```rust
pub struct RuleSpecInput {
    pub label: String,             // "Add"
    pub category: String,          // "Proc"
    pub syntax: Vec<SyntaxItemSpec>,  // [NonTerminal("Proc","a"), Terminal("+"),
                                   //  NonTerminal("Proc","b")]
    pub associativity: Associativity, // Left
    pub prefix_precedence: Option<u8>,
    pub has_rust_code: bool,       // true (has ![...] block)
    pub rust_code: Option<TokenStream>,
    pub eval_mode: Option<String>, // Some("Fold")
}
```

### Syntax item mapping

The bridge converts `SyntaxExpr` → `SyntaxItemSpec` via `convert_syntax_pattern()`:

| `SyntaxExpr`                                  | `SyntaxItemSpec`                                                                            | Condition                    |
|-----------------------------------------------|---------------------------------------------------------------------------------------------|------------------------------|
| `Literal("+")`                                | `Terminal("+")`                                                                             | always                       |
| `Param(a)` where `a:Proc`                     | `NonTerminal { category: "Proc", param_name: "a" }`                                         | `Proc` is a known category   |
| `Param(x)` where `^x.p:...`                   | `Binder { param_name: "x", category: "Name", is_multi: false }`                             | binder annotation in context |
| `Param(xs)` where `^[xs].p:...`               | `Binder { param_name: "xs", category: "Name", is_multi: true }`                             | multi-binder annotation      |
| `Op(Sep { collection: ps, separator: "\|" })` | `Collection { param_name: "ps", element_category: "Proc", separator: "\|", kind: HashBag }` | simple `*sep()`              |
| `Op(Sep { source: Map(Zip(...)) })`           | `ZipMapSep { left_name, right_name, body_items, separator }`                                | chained zip+map+sep          |

### Concrete example: tracing `Add`

```
Add . a:Proc, b:Proc |- a "+" b : Proc ![...] fold;
```

1. **`LanguageDef`** parsing produces:
   ```
   GrammarRule {
     label: "Add",
     category: "Proc",
     term_context: [Simple(a, Base(Proc)), Simple(b, Base(Proc))],
     syntax_pattern: [Param(a), Literal("+"), Param(b)],
     rust_code: Some({ match ... }),
     eval_mode: Some(Fold),
   }
   ```

2. **Bridge** converts to:
   ```
   RuleSpecInput {
     label: "Add",
     category: "Proc",
     syntax: [
       NonTerminal { category: "Proc", param_name: "a" },
       Terminal("+"),
       NonTerminal { category: "Proc", param_name: "b" },
     ],
     associativity: Left,
     has_rust_code: true,
     eval_mode: Some("Fold"),
   }
   ```

3. **`LanguageSpec::with_options()`** calls `classify::classify_rule()`:
   ```
   RuleClassification {
     is_infix: true,      // NT + Terminal + NT, first NT matches category
     is_postfix: false,
     is_unary_prefix: false,
     is_cast: false,
     is_cross_category: false,
     is_collection: false,
     has_binder: false,
     ...
   }
   ```

   Result: a `RuleSpec` with all classification flags set, ready for parser
   generation.

### Classification logic

`classify::classify_rule()` in `prattail/src/classify.rs` derives all boolean
flags from structural pattern matching on `SyntaxItemSpec`:

| Classification      | Pattern detected                                                             |
|---------------------|------------------------------------------------------------------------------|
| `is_infix`          | First item is `NonTerminal` of same category, followed by `Terminal`         |
| `is_unary_prefix`   | `Terminal` followed by exactly one same-category `NonTerminal`, no other NTs |
| `is_postfix`        | Same-category `NonTerminal` followed by `Terminal(s)`, no trailing NT        |
| `is_cast`           | Single `NonTerminal` of a *different* category                               |
| `is_cross_category` | Any `NonTerminal` of a different category (not a cast)                       |
| `is_collection`     | Contains a `Collection` or `ZipMapSep` item                                  |
| `has_binder`        | Contains a `Binder { is_multi: false }`                                      |
| `has_multi_binder`  | Contains a `Binder { is_multi: true }`                                       |

This classification is the *single source of truth* — neither the DSL parser nor
the bridge set these flags.

### Options mapping

The bridge also maps DSL options to PraTTaIL configuration:

| DSL option                       | `LanguageSpec` field                 | Default    |
|----------------------------------|--------------------------------------|------------|
| `beam_width: 1.5`                | `beam_width: Explicit(1.5)`          | `Disabled` |
| `beam_width: auto`               | `beam_width: Auto`                   | `Disabled` |
| `dispatch: weighted`             | `dispatch_strategy: Weighted`        | `Static`   |
| `log_semiring_model_path: "..."` | `log_semiring_model_path: Some(...)` | `None`     |

RhoCalc uses no options block, so all defaults apply.

---

**Next:** [03-lexer-generation.md](03-lexer-generation.md) — how `LanguageSpec`
terminals become a direct-coded lexer.
