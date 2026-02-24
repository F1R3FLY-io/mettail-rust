# ZipMapSep — Parser Codegen and Runtime

This document covers how ZipMapSep is compiled into parser code, how the parsed
result is represented in the AST, how Ascent decomposes it, and a complete
runtime trace.  For the DSL syntax and bridge conversion, see
[01-dsl-and-ast.md](01-dsl-and-ast.md).

## 1. Parser Codegen Routing

**Files:** `prattail/src/trampoline.rs`, `prattail/src/recursive.rs`

### Routing Decision

Three helper functions in `trampoline.rs` determine how PInputs is parsed:

```text
has_zipmapsep(PInputs)?
  → items contains ZipMapSep { ... }
  → true

should_use_standalone_fn(PInputs)?
  → has_zipmapsep(PInputs) = true
  → true  ✓

is_simple_collection(PInputs)?
  → is_collection = false  (ZipMapSep is not a Collection item)
  → false
```

**Routing:** ZipMapSep rules **always** use standalone parse functions.  They
are never trampolined because the dual-accumulator loop with interleaved body
parsing does not fit the single-continuation frame model.

### Trampoline Integration

In the `'drive` prefix phase, when the dispatcher sees `Token::LParen` for
PInputs:

```rust
Token::LParen => {
    break 'prefix parse_pinputs(tokens, pos)?;
}
```

The standalone function is called directly.  It returns a fully-parsed AST node
and control returns to the `'unwind` phase (or back to the caller).

### Thread-Local Pool Safety

The standalone function may call `parse_name()` or `parse_proc()`, which
re-enter the trampoline.  The frame stack uses `Cell<Vec<Frame_Cat>>` with
`take`/`set` semantics (not `RefCell`) to handle this re-entrancy safely — see
[../binders/02-multi-binders.md](../binders/02-multi-binders.md) for details.

## 2. Standalone Function Structure

**File:** `prattail/src/recursive.rs`

`write_rd_handler()` generates `parse_pinputs()`.  The ZipMapSep item (lines
302-413 of `recursive.rs`) produces a dual-accumulator loop.

### Generated Code (Conceptual)

```rust
fn parse_pinputs<'a>(
    tokens: &[Token<'a>],
    pos: &mut usize,
) -> Result<Proc, ParseError> {
    // ═══════════════════════════════════════════════════════
    // Phase 1: Opening delimiter
    // ═══════════════════════════════════════════════════════
    expect_token(tokens, pos, Token::LParen)?;

    // ═══════════════════════════════════════════════════════
    // Phase 2: ZipMapSep loop — dual accumulators
    // ═══════════════════════════════════════════════════════
    let mut ns: Vec<Name> = Vec::new();     // left collection
    let mut xs: Vec<String> = Vec::new();   // right collection (binder names)

    loop {
        // ─── Loop guard ───
        if *pos >= tokens.len() { break; }
        match &tokens[*pos] {
            Token::RParen | Token::RBrace
            | Token::RBracket | Token::Eof => break,
            _ => {}
        }

        // ─── Parse body pattern: n "?" x ───
        // body_items[0]: NonTerminal(Name) → parse_name()
        let n = parse_name(tokens, pos, 0)?;

        // body_items[1]: Terminal("?") → expect
        expect_token(tokens, pos, Token::Question)?;

        // body_items[2]: Binder(Name) → expect_ident()
        let x = expect_ident(tokens, pos)?;

        // ─── Accumulate ───
        ns.push(n);
        xs.push(x);

        // ─── Check separator ───
        if peek_token(tokens, pos, Token::Comma) {
            *pos += 1;   // consume ","
        } else {
            break;
        }
    }

    // ═══════════════════════════════════════════════════════
    // Phase 3: Remaining syntax items
    // ═══════════════════════════════════════════════════════
    expect_token(tokens, pos, Token::RParen)?;     // ")"
    expect_token(tokens, pos, Token::Dot)?;        // "."
    expect_token(tokens, pos, Token::LBrace)?;     // "{"
    let p = parse_proc(tokens, pos, 0)?;           // body Proc
    expect_token(tokens, pos, Token::RBrace)?;     // "}"

    // ═══════════════════════════════════════════════════════
    // Phase 4: Construct AST
    // ═══════════════════════════════════════════════════════
    let binders: Vec<mettail_runtime::Binder<String>> = xs.iter()
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

### Binder Detection in Body Items

The codegen scans `body_items` to determine which of the two accumulators
contains binders:

```text
body_items[0]: NonTerminal { category: "Name" }  → left (ns): NonTerminal
body_items[2]: Binder { is_multi: true }          → right (xs): Binder
```

This distinction drives:
- **Left accumulator**: parsed via `parse_name()` (recursive descent)
- **Right accumulator**: captured via `expect_ident()` (raw string, later wrapped)

If neither body item were a `Binder`, both would use `parse_{category}()`.

### Parse State Machine

```text
               ┌──────────── ZipMapSep loop ────────────┐
               │                                        │
  expect       │  parse     expect   expect    check    │      expect  expect  expect  parse    expect
  LParen       ▼  Name      "?"      ident     ","      │      RParen  "."     LBrace  Proc     RBrace
  ──────→──────┴──────→────→──────→───────→────────→────┊───┬───→──────→──────→──────→───────→───────→ OK
  consume         push n    consume  push x   consume?  │   ▲  consume consume consume body    consume
                  to ns              to xs    ├─ yes: ──┘   │
                                              └─ no: break ─┘
```

### Loop Guard Details

The loop guard checks for structural closing delimiters *before* attempting to
parse the body pattern.  This prevents error cascading when the ZipMapSep
section is empty or when all elements have been consumed:

```rust
match &tokens[*pos] {
    Token::RParen | Token::RBrace | Token::RBracket | Token::Eof => break,
    _ => {}
}
```

Without this guard, an empty `()` would attempt to parse a `Name` after
`LParen`, fail, and produce a confusing error message instead of gracefully
yielding empty collections.

## 3. AST Representation

```text
Proc::PInputs(
    Vec<Name>,                                    ← ns: channel names
    Scope<Vec<Binder<String>>, Box<Proc>>         ← xs + p: binders + body
)
```

| Position     | Type                                    | From                                  | Content                     |
|--------------|-----------------------------------------|---------------------------------------|-----------------------------|
| First field  | `Vec<Name>`                             | Left accumulator (`ns`)               | `[NVar("n"), NVar("m")]`    |
| Second field | `Scope<Vec<Binder<String>>, Box<Proc>>` | Right accumulator (`xs`) + body (`p`) | Binder vector + scoped body |

The `Scope::new(binders, body)` call closes all bound variables simultaneously:
each `FreeVar` in `binders` that appears free in `body` is replaced with a
`BoundVar` referencing its position in the binder vector:

```text
binders = [Binder(FreeVar("x")), Binder(FreeVar("y"))]
body = PPar({ PVar(x), PVar(y) })

After Scope::new:
  body = PPar({ PVar(BoundVar(scope=0, binder=0)),    ← x → position 0
                PVar(BoundVar(scope=0, binder=1)) })   ← y → position 1
```

## 4. Ascent Rules

### Category Exploration

**File:** `macros/src/logic/categories.rs`

`generate_collection_plus_binding_deconstruction()` handles PInputs:

**Extract channel names from Vec:**

```text
name(__elem) <--
    proc(t),
    if let Proc::PInputs(ref vec_field, _) = t,
    for __elem in vec_field.iter();
```

Each `Name` is seeded into the `name(...)` relation for recursive exploration.

**Wrap scope as MLamProc:**

```text
proc(Proc::MLamProc(scope.clone())) <--
    proc(t),
    if let Proc::PInputs(_, ref scope) = t;
```

The scope is wrapped in an auto-generated `MLamProc` variant.  This makes the
body reachable by the standard body-extraction rule:

```text
proc(__body) <--
    proc(t),
    if let Proc::MLamProc(ref scope) = t,
    let __body = scope.inner().unsafe_body.as_ref().clone();
```

### Congruence

**File:** `macros/src/logic/congruence.rs`

If the body of a PInputs is rewritten:

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
            binder, Box::new(body_rewritten.clone())
        )
    );
```

The channel names `vec_field` are cloned unchanged; only the scope body is
rewritten.  `from_parts_unsafe()` reconstructs without re-closing because the
body retains its `BoundVar` structure from `unsafe_body()`.

### Comm Rule Interaction

The communication rule pattern-matches POutput channels against PInputs
channels.  When channel names match:

```text
proc(parent),
if let Proc::PPar(ref bag) = parent,

// Find POutput in the bag
for (elem_out, _) in bag.iter(),
if let Proc::POutput(ref chan, ref val) = elem_out,

// Find PInputs in the bag
for (elem_in, _) in bag.iter(),
if let Proc::PInputs(ref names, ref scope) = elem_in,
if &elem_out != &elem_in,

// Channel match
for (i, n) in names.iter().enumerate(),
if n == chan,

// Substitute value for bound variable
let (binders, body) = scope.clone().unbind(),
let result = substitute(body, &binders[i], val),
...
```

The *i*-th channel from `names` matches against `chan`, and the corresponding
*i*-th binder is substituted with the received value — enabling pairwise
communication over multiple channels.

## 5. Runtime Evaluation — Complete Trace

**Input:** `(n?x, m?y).{x | y}`

### Lexing

```text
 Pos:    0       1         2          3       4     5         6          7       8      9
Token:  LParen  Ident(n)  Question  Ident(x) Comma Ident(m)  Question  Ident(y) RParen Dot

 Pos:   10      11        12    13        14
Token:  LBrace  Ident(x)  Pipe  Ident(y)  RBrace
```

### Parse Execution

```text
 Step │ Action                          │ ns              │ xs          │ pos
 ─────┼─────────────────────────────────┼─────────────────┼─────────────┼────
  1   │ expect LParen                   │ []              │ []          │ 1
      │                                 │                 │             │
      │ ─── ZipMapSep iteration 1 ───   │                 │             │
  2   │ parse_name → NVar("n")          │ [NVar("n")]     │ []          │ 2
  3   │ expect Question                 │                 │             │ 3
  4   │ expect_ident → "x"              │ [NVar("n")]     │ ["x"]       │ 4
  5   │ peek Comma → consume            │                 │             │ 5
      │                                 │                 │             │
      │ ─── ZipMapSep iteration 2 ───   │                 │             │
  6   │ parse_name → NVar("m")          │ [NVar("n"),     │ ["x"]       │ 6
      │                                 │  NVar("m")]     │             │
  7   │ expect Question                 │                 │             │ 7
  8   │ expect_ident → "y"              │ [NVar("n"),     │ ["x","y"]   │ 8
      │                                 │  NVar("m")]     │             │
  9   │ peek RParen → break             │                 │             │ 8
      │                                 │                 │             │
 10   │ expect RParen                   │                 │             │ 9
 11   │ expect Dot                      │                 │             │ 10
 12   │ expect LBrace                   │                 │             │ 11
 13   │ parse_proc → PPar({PVar(x),     │                 │             │ 15
      │              PVar(y)})          │                 │             │
 14   │ expect RBrace                   │                 │             │ 15
      │                                 │                 │             │
      │ ─── Construct AST ───           │                 │             │
 15   │ binders = [Binder(fv_x),        │                 │             │
      │            Binder(fv_y)]        │                 │             │
 16   │ Scope::new(binders,             │                 │             │
      │   Box::new(PPar({PVar(x),       │                 │             │
      │                   PVar(y)})))   │                 │             │
      │                                 │                 │             │
      │ Result: Proc::PInputs(          │                 │             │
      │   [NVar("n"), NVar("m")],       │                 │             │
      │   Scope([Binder(fv_x),          │                 │             │
      │          Binder(fv_y)],         │                 │             │
      │         Box(PPar({...}))))      │                 │             │
```

### Ascent Seeding

```text
proc(Proc::PInputs(ns, scope))  ← initial seed
name(Name::NVar("n"))           ← from ns[0]
name(Name::NVar("m"))           ← from ns[1]
proc(Proc::MLamProc(scope))     ← wrapped scope for body extraction
proc(Proc::PPar(bag))           ← from scope.unsafe_body()
proc(Proc::PVar(x))             ← from bag.iter_elements()
proc(Proc::PVar(y))             ← from bag.iter_elements()
```

### Fixpoint

With only `PInputs` and no matching `POutput`, the fixpoint converges
immediately — no rewrites are triggered.  If a `POutput(n, v)` were present
in a parallel composition with this PInputs, the Comm rule would fire:

```text
Given: { POutput(n, 42) | PInputs([n, m], Scope([x, y], {x | y})) }
Comm:  match n == n at index 0
       unbind scope → body = {x | y}
       substitute x := 42 → {42 | y}
       remove POutput and PInputs from bag, insert result
Result: { 42 | y | PInputs([m], Scope([y], {y})) }
```

(Simplified — the actual Comm rule handles the full mechanics including rest
computation and re-scoping.)

---

**See also:**
- [00-overview.md](00-overview.md) — ZipMapSep overview and pipeline diagram
- [01-dsl-and-ast.md](01-dsl-and-ast.md) — DSL syntax, PatternOp tree, bridge conversion
- [../binders/02-multi-binders.md](../binders/02-multi-binders.md) — Multi-binder context
- [../collections/03-ascent-decomposition.md](../collections/03-ascent-decomposition.md) — Collection decomposition in Ascent
