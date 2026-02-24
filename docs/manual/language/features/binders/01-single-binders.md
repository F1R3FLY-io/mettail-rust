# Single Binders — Full Pipeline Trace

This document traces a single-binder rule through every stage of the
MeTTaIL/PraTTaIL pipeline, using the RhoCalc `PNew` constructor as the running
example.

## 1. DSL Definition

```text
PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
```

| Component               | Meaning                             |
|-------------------------|-------------------------------------|
| `PNew`                  | Constructor label                   |
| `^x.p`                  | Binder `x` scopes over body `p`     |
| `[Name -> Proc]`        | `x` binds a `Name`, `p` is a `Proc` |
| `"new" "(" x "," p ")"` | Concrete syntax: `new(x, p)`        |
| `: Proc`                | Result category                     |

The caret `^` is the binder sigil.  The dot `.` separates the bound variable
from the body.  The arrow type `[Name -> Proc]` tells the pipeline that the
binding domain is `Name` and the codomain (body type) is `Proc`.

## 2. LanguageDef AST

**File:** `macros/src/ast/grammar.rs`

The macro parser (`parse_term_param`) recognises `^x.p:[Name -> Proc]` and
builds:

```text
TermParam::Abstraction {
    binder: Ident("x"),
    body:   Ident("p"),
    ty:     TypeExpr::Arrow {
                domain:   Box(TypeExpr::Base(Ident("Name"))),
                codomain: Box(TypeExpr::Base(Ident("Proc"))),
            },
}
```

The syntax pattern `"new" "(" x "," p ")"` produces:

```text
vec![
    SyntaxExpr::Literal("new"),
    SyntaxExpr::Literal("("),
    SyntaxExpr::Param(Ident("x")),   ← binder position
    SyntaxExpr::Literal(","),
    SyntaxExpr::Param(Ident("p")),   ← body position
    SyntaxExpr::Literal(")"),
]
```

At this stage `x` and `p` are unresolved parameter references — the bridge
resolves them against the term context.

## 3. Bridge: LanguageDef → LanguageSpec

**File:** `macros/src/gen/syntax/parser/prattail_bridge.rs`

`convert_syntax_pattern()` walks the pattern and, for each `SyntaxExpr::Param`,
looks up the name in the term context.

### Resolving `x`

`x` matches `TermParam::Abstraction { binder: Ident("x"), .. }`.  Since the
parameter name equals the binder name, the bridge emits:

```text
SyntaxItemSpec::Binder {
    param_name: "x",
    category:   "Name",          ← extracted from Arrow domain
    is_multi:   false,
}
```

This is done via `classify_param_from_context()` (line 221 of `prattail_bridge.rs`):

```rust
TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name_str => {
    SyntaxItemSpec::Binder {
        param_name: name_str.to_string(),
        category: extract_base_category(ty),  // Arrow domain → "Name"
        is_multi: false,
    }
}
```

### Resolving `p`

`p` matches the same `TermParam::Abstraction` but via the `body` field.  Since
it is the body (not the binder), it becomes a `NonTerminal`:

```text
SyntaxItemSpec::NonTerminal {
    category:   "Proc",          ← extracted from Arrow codomain
    param_name: "p",
}
```

### Complete SyntaxItemSpec list

```text
[
    Terminal("new"),
    Terminal("("),
    Binder { param_name: "x", category: "Name", is_multi: false },
    Terminal(","),
    NonTerminal { category: "Proc", param_name: "p" },
    Terminal(")"),
]
```

## 4. Classification

**File:** `prattail/src/classify.rs`

`classify_rule()` inspects the syntax items and derives boolean flags.

```text
has_binder_recursive(syntax, check_multi=false)
  → finds Binder { is_multi: false } at position 2
  → returns true

has_binder_recursive(syntax, check_multi=true)
  → no Binder { is_multi: true }
  → returns false
```

Resulting flags on the `RuleSpec`:

| Flag               | Value   | Reason                                                |
|--------------------|---------|-------------------------------------------------------|
| `has_binder`       | `true`  | Single `Binder { is_multi: false }` present           |
| `has_multi_binder` | `false` | No `Binder { is_multi: true }`                        |
| `is_infix`         | `false` | First item is `Terminal("new")`, not same-category NT |
| `is_collection`    | `false` | No `Collection` item                                  |
| `is_var`           | `false` | Not a bare `IdentCapture`                             |
| `is_cast`          | `false` | More than one item                                    |

## 5. Lexer Impact

The terminals `"new"`, `"("`, `","`, `")"` enter the automata pipeline:

| Terminal | Token Variant          | Priority | Notes                                         |
|----------|------------------------|----------|-----------------------------------------------|
| `new`    | `Token::New` (keyword) | 10       | Beats `Token::Ident` (priority 1)             |
| `(`      | `Token::LParen`        | —        | Structural delimiter (always in terminal set) |
| `,`      | `Token::Comma`         | —        | Structural delimiter                          |
| `)`      | `Token::RParen`        | —        | Structural delimiter                          |

The keyword `new` is compiled into the DFA alongside other keywords.  When the
lexer encounters the character sequence `n`, `e`, `w` followed by a
non-identifier character, it produces `Token::New` rather than
`Token::Ident("new")` due to priority ordering.

## 6. Parser Codegen

**Files:** `prattail/src/recursive.rs`, `prattail/src/trampoline.rs`

### Routing Decision

```text
should_use_standalone_fn(PNew)?
  has_zipmapsep → false
  has_multi_binder → false
  → false  (PNew does NOT use a standalone function)

is_simple_collection(PNew)?
  is_collection → false
  → false
```

PNew is neither a standalone-fn rule nor a simple collection, so it is handled
by the standard RD-handler splitting path.

### Handler Segment Splitting

`split_rd_handler()` walks the syntax items and splits at same-category
`NonTerminal` boundaries:

```text
Items:  Terminal("new")  Terminal("(")  Binder("x")  Terminal(",")  NonTerminal("Proc","p")  Terminal(")")
        ─────────────── inline items ──────────────────────────────  ↑ split point            ─ final ─
```

The `NonTerminal { category: "Proc" }` is a same-category NT (PNew's category
is `Proc`), so the handler splits into two segments:

```text
Segment 0 (frame: RD_PNew_0):
  inline_items: [Terminal("new"), Terminal("("), Binder("x"), Terminal(",")]
  nonterminal:  NonTerminal { category: "Proc", param_name: "p", bp: 0 }
  captures:     [Binder { name: "x" }]

Segment 1 (final):
  inline_items: [Terminal(")")]
  nonterminal:  None
  captures:     [Binder { name: "x" }, NonTerminal { name: "p", category: "Proc" }]
```

### Generated Frame Variant

```text
Frame_Proc::RD_PNew_0 {
    x: String,         ← binder name captured as raw string
    saved_bp: u8,      ← binding power to restore after parsing body
}
```

### Generated Code (Conceptual)

**Prefix phase** (`'drive` loop, on seeing `Token::New`):

```rust
Token::New => {
    *pos += 1;                                    // consume "new"
    expect_token(tokens, pos, Token::LParen)?;    // consume "("
    let x = expect_ident(tokens, pos)?;           // capture binder name
    expect_token(tokens, pos, Token::Comma)?;     // consume ","
    stack.push(Frame_Proc::RD_PNew_0 {
        x,
        saved_bp: cur_bp,
    });
    cur_bp = 0;                                   // body parsed at min BP
    continue 'drive;                              // parse body (Proc)
}
```

**Unwind phase** (popping `RD_PNew_0`):

```rust
Some(Frame_Proc::RD_PNew_0 { x, saved_bp }) => {
    let p = lhs;                                  // body just parsed
    expect_token(tokens, pos, Token::RParen)?;    // consume ")"
    lhs = Proc::PNew(
        mettail_runtime::Scope::new(
            mettail_runtime::Binder(
                mettail_runtime::get_or_create_var(x)
            ),
            Box::new(p),
        )
    );
    cur_bp = saved_bp;
}
```

### Data Flow Diagram

```text
  Token stream:  new    (    x    ,    {x | x}    )
                  ▲     ▲    ▲    ▲       ▲       ▲
  'drive:         │     │    │    │       │       │
    consume ──────┘     │    │    │       │       │
    expect LParen ──────┘    │    │       │       │
    expect_ident ────────────┘    │       │       │
    expect Comma ─────────────────┘       │       │
    push Frame_Proc::RD_PNew_0            │       │
    continue 'drive ──────────────────────┘       │
       (parse Proc at bp=0)                       │
                                                  │
  'unwind:                                        │
    pop RD_PNew_0                                 │
    p = lhs (parsed Proc)                         │
    expect RParen ────────────────────────────────┘
    lhs = Proc::PNew(Scope::new(
              Binder(get_or_create_var("x")),
              Box::new(p)))
```

## 7. AST

The constructed node is:

```text
Proc::PNew(
    Scope<Binder<String>, Box<Proc>>
)
```

Where:
- `Binder<String>` wraps `FreeVar<String>` — a globally unique variable with
  pretty-name `"x"`
- `Box<Proc>` is the body in which `x` is bound
- `Scope::new()` calls `moniker::Scope::new()` internally, which *closes* the
  body — converting free occurrences of `x` in the body to `BoundVar`
  references

## 8. Runtime Binding

**File:** `runtime/src/binding.rs`

### get_or_create_var

```rust
pub fn get_or_create_var(name: impl Into<String>) -> FreeVar<String> {
    let name = name.into();
    VAR_CACHE.with(|cache| {
        cache.borrow_mut()
             .entry(name.clone())
             .or_insert_with(|| FreeVar::fresh_named(name))
             .clone()
    })
}
```

The first call with `"x"` creates `FreeVar { pretty_name: Some("x"), unique_id: 42 }`.
Subsequent calls with `"x"` (within the same parse session) return the same
`FreeVar` — ensuring that occurrences of `x` in the body share identity with
the binder.

### Scope::new

```rust
pub fn new<N>(pattern: P, body: T) -> Scope<P, T>
where
    N: Clone + PartialEq,
    P: BoundPattern<N>,
    T: BoundTerm<N>,
{
    Scope {
        inner: moniker::Scope::new(pattern, body),
    }
}
```

`moniker::Scope::new` performs **closing**: it traverses `body`, finds all
`Var::Free(fv)` where `fv` matches the binder's `FreeVar`, and replaces them
with `Var::Bound(BoundVar { scope: 0, binder: 0 })` — a De Bruijn-indexed
reference to the nearest enclosing binder.

## 9. Ascent Rules

### Category Exploration

**File:** `macros/src/logic/categories.rs`

PNew terms are decomposed for recursive exploration by extracting the body from
the scope:

```text
proc(__body) <--
    proc(t),
    if let Proc::PNew(ref scope) = t,
    let __body = scope.unsafe_body().as_ref().clone();
```

`unsafe_body()` returns `&Box<Proc>` without unbinding — preserving the bound
variable structure for downstream rules.

### Congruence

**File:** `macros/src/logic/congruence.rs`

If the body is rewritten (`p ~> p'`), then the enclosing PNew is also
rewritten:

```text
rw_proc(lhs.clone(), rhs) <--
    proc(lhs),
    if let Proc::PNew(ref scope) = lhs,
    let binder = scope.unsafe_pattern().clone(),
    let body = scope.unsafe_body(),
    rw_proc((**body).clone(), body_rewritten),
    let rhs = Proc::PNew(
        mettail_runtime::Scope::from_parts_unsafe(
            binder,
            Box::new(body_rewritten.clone())
        )
    );
```

Key details:
- `unsafe_pattern()` preserves the binder's identity (no freshening)
- `from_parts_unsafe()` reconstructs the scope without re-closing — safe
  because the body was obtained via `unsafe_body()` (still closed)

## 10. Runtime Evaluation — Trace

**Input:** `new(x, {x | x})`

### Lexing

```text
Input:   n  e  w  (  x  ,  {  x  |  x  }  )
Tokens:  New  LParen  Ident("x")  Comma  LBrace  Ident("x")  Pipe  Ident("x")  RBrace  RParen
```

### Parsing

```text
1. Match Token::New → enter PNew handler
2. Consume LParen
3. expect_ident → "x"
4. Consume Comma
5. Push Frame_Proc::RD_PNew_0 { x: "x", saved_bp: 0 }
6. Parse body (Proc at bp=0):
     Match Token::LBrace → enter PPar handler
     Parse { Ident("x") | Ident("x") } → HashBag { PVar(x), PVar(x) }
     Result: Proc::PPar(HashBag { PVar(x): 2 })
7. Pop RD_PNew_0:
     p = Proc::PPar(HashBag { PVar(x): 2 })
     Consume RParen
     Construct: Proc::PNew(Scope::new(
                    Binder(get_or_create_var("x")),
                    Box::new(p)))
```

After `Scope::new`, the two free occurrences of `x` in the body are closed to
`BoundVar { scope: 0, binder: 0 }` — making the term alpha-equivalent to
`new(y, {y | y})` for any variable name `y`.

### Ascent Seeding

```text
proc(Proc::PNew(scope))     ← initial seed
proc(Proc::PPar(bag))       ← extracted via scope.unsafe_body()
proc(Proc::PVar(x))         ← extracted via bag.iter_elements() (×2, but set)
```

The fixpoint engine propagates these facts until no new rewrites are discovered.

---

**See also:**
- [00-overview.md](00-overview.md) — Binder overview and key types
- [02-multi-binders.md](02-multi-binders.md) — Multi-binder pipeline trace (PInputs)
- [../collections/01-hashbag.md](../collections/01-hashbag.md) — HashBag pipeline (PPar body)
- [../../examples/rhocalc/](../../examples/rhocalc/) — Full RhoCalc pipeline documentation
