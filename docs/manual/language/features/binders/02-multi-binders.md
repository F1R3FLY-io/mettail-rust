# Multi-Binders — Full Pipeline Trace

This document traces a multi-binder rule through every stage of the
MeTTaIL/PraTTaIL pipeline, using the RhoCalc `PInputs` constructor.  PInputs
combines multi-binders with [ZipMapSep](../ZipMapSep/00-overview.md) — a
three-stage metasyntax for parsing pairwise-structured patterns.

## 1. DSL Definition

```text
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

| Component                                     | Meaning                                                                     |
|-----------------------------------------------|-----------------------------------------------------------------------------|
| `PInputs`                                     | Constructor label                                                           |
| `ns:Vec(Name)`                                | Ordered list of channel names                                               |
| `^[xs].p`                                     | Multi-binder: `xs` is a *vector* of bound `Name` variables scoping over `p` |
| `[Name* -> Proc]`                             | `xs` binds zero or more `Name`s; `p` is a `Proc`                            |
| `*zip(ns,xs).*map(\|n,x\| n "?" x).*sep(",")` | ZipMapSep — see [ZipMapSep docs](../ZipMapSep/00-overview.md)               |
| `"(" ... ")" "." "{" p "}"`                   | Concrete syntax: `(n?x, m?y).{p}`                                           |
| `: Proc`                                      | Result category                                                             |

The square brackets `[xs]` are the multi-binder sigil: `^[xs]` means "xs binds
a list of variables" whereas `^x` would bind a single variable.  The `Name*`
in the arrow type mirrors the multiplicity.

## 2. LanguageDef AST

**File:** `macros/src/ast/grammar.rs`

### Term Context

The macro parser (`parse_term_param`) processes each parameter:

```text
ns:Vec(Name)
→ TermParam::Simple {
      name: Ident("ns"),
      ty:   TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element:   Box(TypeExpr::Base(Ident("Name"))),
            },
  }

^[xs].p:[Name* -> Proc]
→ TermParam::MultiAbstraction {
      binder: Ident("xs"),
      body:   Ident("p"),
      ty:     TypeExpr::Arrow {
                  domain:   Box(TypeExpr::MultiBinder(
                                Box(TypeExpr::Base(Ident("Name"))))),
                  codomain: Box(TypeExpr::Base(Ident("Proc"))),
              },
  }
```

### Syntax Pattern

The chained pattern operation `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")` is
parsed into nested `PatternOp` nodes:

```text
SyntaxExpr::Op(
    PatternOp::Sep {
        collection: Ident("__chain__"),
        separator:  ",",
        source:     Some(Box(
            PatternOp::Map {
                source: Box(PatternOp::Zip {
                            left:  Ident("ns"),
                            right: Ident("xs"),
                        }),
                params: [Ident("n"), Ident("x")],
                body:   [
                    SyntaxExpr::Param(Ident("n")),
                    SyntaxExpr::Literal("?"),
                    SyntaxExpr::Param(Ident("x")),
                ],
            }
        )),
    }
)
```

The full syntax pattern vector:

```text
[
    Literal("("),
    Op(Sep { ... }),           ← the entire ZipMapSep chain
    Literal(")"),
    Literal("."),
    Literal("{"),
    Param(Ident("p")),
    Literal("}"),
]
```

## 3. Bridge: LanguageDef → LanguageSpec

**File:** `macros/src/gen/syntax/parser/prattail_bridge.rs`

### ZipMapSep Conversion

`convert_pattern_op()` dispatches to `convert_chained_sep()` because the `Sep`
has a non-None `source`.  The chain is unwrapped:

```text
Sep { source: Map { source: Zip { left: "ns", right: "xs" }, params: [n, x], body: [...] } }
```

`convert_chained_sep()` builds a parameter mapping from closure params to zip
params:

```text
n → ns  (left zip param)
x → xs  (right zip param)
```

Body items are resolved through `classify_param_from_context()`:

| Closure Param | Maps To | Context Lookup                                 | Result                             |
|---------------|---------|------------------------------------------------|------------------------------------|
| `n`           | `ns`    | `TermParam::Simple { ty: Vec(Name) }`          | `NonTerminal { category: "Name" }` |
| `"?"`         | —       | Literal                                        | `Terminal("?")`                    |
| `x`           | `xs`    | `TermParam::MultiAbstraction { binder: "xs" }` | `Binder { is_multi: true }`        |

The bridge emits:

```text
SyntaxItemSpec::ZipMapSep {
    left_name:      "ns",
    right_name:     "xs",
    left_category:  "Name",
    right_category: "Name",
    body_items: [
        NonTerminal { category: "Name", param_name: "ns" },
        Terminal("?"),
        Binder { param_name: "xs", category: "Name", is_multi: true },
    ],
    separator: ",",
}
```

### Resolving `p`

`p` matches `TermParam::MultiAbstraction { body: "p" }` — since it is the body
(not the binder), it becomes:

```text
SyntaxItemSpec::NonTerminal { category: "Proc", param_name: "p" }
```

### Complete SyntaxItemSpec List

```text
[
    Terminal("("),
    ZipMapSep { left_name: "ns", right_name: "xs", ... },
    Terminal(")"),
    Terminal("."),
    Terminal("{"),
    NonTerminal { category: "Proc", param_name: "p" },
    Terminal("}"),
]
```

## 4. Classification

**File:** `prattail/src/classify.rs`

`classify_rule()` derives flags from the syntax items:

```text
has_binder_recursive(syntax, check_multi=true)
  → recurses into ZipMapSep::body_items
  → finds Binder { is_multi: true } at body_items[2]
  → returns true

has_binder_recursive(syntax, check_multi=false)
  → no Binder { is_multi: false } found
  → returns false
```

| Flag               | Value   | Reason                                       |
|--------------------|---------|----------------------------------------------|
| `has_multi_binder` | `true`  | `Binder { is_multi: true }` inside ZipMapSep |
| `has_binder`       | `false` | Multi-binder takes precedence                |
| `is_infix`         | `false` | First item is `Terminal("(")`                |
| `is_collection`    | `false` | No `Collection` item at top level            |

## 5. Parser Codegen

**Files:** `prattail/src/recursive.rs`, `prattail/src/trampoline.rs`

### Routing Decision

```text
should_use_standalone_fn(PInputs)?
  has_zipmapsep → true (ZipMapSep item present)
  → true  ✓

  (Also: has_multi_binder → true — either condition suffices)
```

PInputs is **always** routed to a standalone parse function — it is never
trampolined.  The trampoline's prefix phase calls the standalone function
directly and returns the result:

```rust
Token::LParen => {
    // Standalone function — not trampolined
    break 'prefix parse_pinputs(tokens, pos)?;
}
```

### Standalone Function Structure

`write_rd_handler()` generates `parse_pinputs()` (conceptual):

```rust
fn parse_pinputs<'a>(
    tokens: &[Token<'a>],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    // ─── Opening delimiter ───
    expect_token(tokens, pos, Token::LParen)?;

    // ─── ZipMapSep loop ───
    let mut ns: Vec<Name> = Vec::new();
    let mut xs: Vec<String> = Vec::new();

    loop {
        // Guard: stop on closing delimiter or EOF
        if *pos >= tokens.len() { break; }
        match &tokens[*pos] {
            Token::RParen | Token::RBrace | Token::RBracket | Token::Eof => break,
            _ => {}
        }

        // Parse body pattern: n "?" x
        let n = parse_name(tokens, pos, 0)?;     // NonTerminal(Name)
        expect_token(tokens, pos, Token::Question)?;  // Terminal("?")
        let x = expect_ident(tokens, pos)?;       // Binder (captured as String)

        ns.push(n);
        xs.push(x);

        // Check separator
        if peek_token(tokens, pos, Token::Comma) {
            *pos += 1;   // consume ","
        } else {
            break;
        }
    }

    // ─── Remaining syntax ───
    expect_token(tokens, pos, Token::RParen)?;    // ")"
    expect_token(tokens, pos, Token::Dot)?;       // "."
    expect_token(tokens, pos, Token::LBrace)?;    // "{"
    let p = parse_proc(tokens, pos, 0)?;          // body Proc
    expect_token(tokens, pos, Token::RBrace)?;    // "}"

    // ─── Construct AST ───
    let binders: Vec<Binder<String>> = xs.iter()
        .map(|x| mettail_runtime::Binder(
            mettail_runtime::get_or_create_var(x)
        ))
        .collect();

    Ok(Proc::PInputs(
        ns,
        mettail_runtime::Scope::new(binders, Box::new(p)),
    ))
}
```

### Parse State Machine

```text
          ┌──────────────── ZipMapSep loop ──────────┐
          │                                          │
 Token::  │  parse     expect   expect    check      │      expect  expect  expect  parse   expect
 LParen   ▼  Name      "?"     ident     ","         │      ")"     "."     "{"     Proc    "}"
 ─────→───┴───→────────→───────→─────────→───────→───┊───┬──→──────→───────→───────→───────→──────→ Done
 consume     push n    consume  push x    consume?   │   ▲  consume consume consume body   consume
             to ns              to xs     ├── yes: ──┘   │
                                          └── no: break ─┘
```

### Binder Detection in ZipMapSep

The codegen scans `body_items` to determine which of the two collections
contains binders (lines 302-413 of `recursive.rs`):

```text
body_items[0]: NonTerminal  → ns is NonTerminal collection
body_items[2]: Binder       → xs is Binder collection
```

This distinction drives how the collections are stored:
- `ns` → `Vec<Name>` (parsed via `parse_name`)
- `xs` → `Vec<String>` (captured via `expect_ident`, later mapped to `Binder<String>`)

## 6. AST

```text
Proc::PInputs(
    Vec<Name>,                                  ← channel names (ns)
    Scope<Vec<Binder<String>>, Box<Proc>>       ← bound variables + body
)
```

| Field  | Type                                    | Content                       |
|--------|-----------------------------------------|-------------------------------|
| First  | `Vec<Name>`                             | Channel names (`n`, `m`, ...) |
| Second | `Scope<Vec<Binder<String>>, Box<Proc>>` | Multi-binder scope            |

`Scope::new(binders, body)` closes *all* bound variables simultaneously —
each `FreeVar` in `binders` that appears free in `body` is replaced with a
`BoundVar` referencing the appropriate position in the binder vector.

## 7. Ascent Rules

### Category Exploration

**File:** `macros/src/logic/categories.rs`

PInputs is decomposed via `generate_collection_plus_binding_deconstruction()`:

**Extract channel names:**

```text
name(__elem) <--
    proc(t),
    if let Proc::PInputs(ref vec_field, _) = t,
    for __elem in vec_field.iter();
```

Each `Name` element from the channel list is seeded into the `name(...)` relation
for recursive exploration.

**Extract body via MLam wrapping:**

```text
proc(Proc::MLamProc(scope.clone())) <--
    proc(t),
    if let Proc::PInputs(_, ref scope) = t;
```

The scope is wrapped in an auto-generated `MLamProc` variant to make it visible
for congruence and body extraction rules. The `MLam` variant is synthesized
during language compilation — it does not appear in the DSL.

**Body extraction from MLam:**

```text
proc(__body) <--
    proc(t),
    if let Proc::MLamProc(ref scope) = t,
    let __body = scope.inner().unsafe_body.as_ref().clone();
```

### Congruence

**File:** `macros/src/logic/congruence.rs`

If the body of a PInputs term is rewritten:

```text
rw_proc(lhs.clone(), rhs) <--
    proc(lhs),
    if let Proc::PInputs(ref vec_field, ref scope) = lhs,
    let binder = scope.unsafe_pattern().clone(),
    let body = scope.unsafe_body(),
    rw_proc((**body).clone(), body_rewritten),
    let rhs = Proc::PInputs(
        vec_field.clone(),
        mettail_runtime::Scope::from_parts_unsafe(
            binder,
            Box::new(body_rewritten.clone())
        )
    );
```

The channel names `vec_field` are cloned unchanged; only the scope body is
rewritten.

## 8. Runtime Evaluation — Trace

**Input:** `(n?x, m?y).{x | y}`

### Lexing

```text
Input:   (  n  ?  x  ,  m  ?  y  )  .  {  x  |  y  }
Tokens:  LParen  Ident("n")  Question  Ident("x")  Comma
         Ident("m")  Question  Ident("y")  RParen  Dot
         LBrace  Ident("x")  Pipe  Ident("y")  RBrace
```

### Parsing (Standalone Function)

```text
 1. consume LParen

 ─── ZipMapSep iteration 1 ───
 2. parse_name → Name::NVar("n")         ns = [NVar("n")]
 3. consume Question
 4. expect_ident → "x"                   xs = ["x"]
 5. peek Comma → consume

 ─── ZipMapSep iteration 2 ───
 6. parse_name → Name::NVar("m")         ns = [NVar("n"), NVar("m")]
 7. consume Question
 8. expect_ident → "y"                   xs = ["x", "y"]
 9. peek RParen → break loop

10. consume RParen
11. consume Dot
12. consume LBrace
13. parse_proc (body) → Proc::PPar(HashBag { PVar(x): 1, PVar(y): 1 })
14. consume RBrace

15. Construct binders:
      binders = [ Binder(get_or_create_var("x")),
                   Binder(get_or_create_var("y")) ]

16. Result:
      Proc::PInputs(
          [NVar("n"), NVar("m")],
          Scope::new(binders, Box::new(Proc::PPar(bag)))
      )
```

### Ascent Seeding

```text
proc(Proc::PInputs(ns, scope))   ← initial seed
name(Name::NVar("n"))            ← from ns.iter()
name(Name::NVar("m"))            ← from ns.iter()
proc(Proc::MLamProc(scope))      ← wrapped scope
proc(Proc::PPar(bag))            ← from scope.unsafe_body()
proc(Proc::PVar(x))              ← from bag.iter_elements()
proc(Proc::PVar(y))              ← from bag.iter_elements()
```

### Comm Rule Interaction

The communication rule (`Comm`) pattern-matches a `POutput` channel against a
`PInputs` channel.  When the channel names match, the received value is
substituted for the bound variable in the PInputs body:

```text
POutput(n, v) | PInputs([n, ...], Scope([x, ...], body))
→ body[x := v] | PInputs([...], Scope([...], body))
```

This is where multi-binders interact with the runtime: the *i*-th output
channel substitutes for the *i*-th bound variable, enabling pairwise
communication over multiple channels.

---

**See also:**
- [00-overview.md](00-overview.md) — Binder overview and key types
- [01-single-binders.md](01-single-binders.md) — Single-binder pipeline trace (PNew)
- [../ZipMapSep/00-overview.md](../ZipMapSep/00-overview.md) — ZipMapSep feature documentation
- [../collections/01-hashbag.md](../collections/01-hashbag.md) — HashBag pipeline trace (PPar)
