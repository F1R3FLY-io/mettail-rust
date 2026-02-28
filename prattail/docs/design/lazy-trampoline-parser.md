# Phase 6E: Lazy Trampoline Parser Architecture

**Date:** 2026-02-26

---

## Table of Contents

1. [Comparison: Slice-Based vs Adapter-Based Parsing](#1-comparison-slice-based-vs-adapter-based-parsing)
2. [`set_category()` Call Pattern](#2-set_category-call-pattern)
3. [Cross-Category Dispatch: Before and After](#3-cross-category-dispatch-before-and-after)
4. [Generated Code Structure](#4-generated-code-structure)
5. [Error Propagation (Phase 6H)](#5-error-propagation-phase-6h)
6. [Limitations](#6-limitations)

**Source files:**
- `prattail/src/trampoline.rs` -- `write_trampolined_parser_lazy()` (lines 2370-2776), lazy inline/single-item helpers (lines 2778-2964)
- `prattail/src/automata/codegen.rs` -- `write_lexer_struct()` (lines 792-954), `write_lexer_adapter()` (lines 1004-1064), `write_accept_token_by_kind()` (lines 961-994), `write_expected_category_descriptions()` (lines 766-780)
- `prattail/src/prediction.rs` -- `compute_composed_dispatch()` (lines 1438-1537), `emit_composed_dispatch_table()` (lines 1625-1665)
- `prattail/src/pipeline.rs` -- `generate_with_context_lex()` (lines 450-536), lazy parser emission call (lines 798-808)

**Cross-references:**
- [design/architecture-overview.md](architecture-overview.md) -- Overall pipeline
- [design/disambiguation/01-lexical-disambiguation.md](disambiguation/01-lexical-disambiguation.md) -- Lexer ambiguity resolution
- [design/cross-category-dispatch.md](cross-category-dispatch.md) -- Dispatch wrapper architecture

---

## 1. Comparison: Slice-Based vs Adapter-Based Parsing

PraTTaIL generates two parser entry points for each grammar category. The
**standard** parser operates on a pre-tokenized slice; the **lazy** parser
drives tokenization on demand through a `LexerAdapter`.

### 1.1 Slice-Based Parser (Standard Path)

The standard parser eagerly tokenizes the entire input before parsing begins.

```
fn parse_Cat<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Cat, ParseError>
```

Characteristics:

- **Eager tokenization.** The caller invokes `lex(input)` up front, producing a
  `Vec<(Token, Range)>`. The parser receives the complete slice.
- **Token access.** Current token: `tokens[*pos]`. Advance: `*pos += 1`.
  Peek-ahead: `tokens[*pos + n]`.
- **Cross-category dispatch.** Uses save/restore on `*pos` to attempt parsing
  in one category, then backtrack and try another if the first fails.
- **Stack safety.** Implemented as a trampolined state machine with an explicit
  continuation stack (`Vec<Frame_Cat>`) and thread-local pooling via
  `Cell<Vec<Frame_Cat>>`.

Data flow:

```
  Input string
       │
       ▼
  lex(input) ──── eager, full scan ────▶ Vec<(Token, Range)>
       │                                       │
       │                                       ▼
       │                              parse_Cat(&tokens, &mut 0, 0)
       │                                       │
       │                              tokens[*pos]  *pos += 1
       │                                       │
       ▼                                       ▼
  All tokens                              AST result
  materialized
  in memory
```

### 1.2 Adapter-Based Parser (Lazy Path)

The lazy parser produces tokens on demand, one at a time, through a
`LexerAdapter` that wraps an incremental `Lexer`.

```
fn parse_Cat_lazy<'a>(
    adapter: &mut LexerAdapter<'a>,
    min_bp: u8,
) -> Result<Cat, ParseError>
```

Characteristics:

- **Demand-driven tokenization.** The `LexerAdapter` buffers a small number of
  tokens (capacity 4). Tokens are produced from the underlying `Lexer` only when
  `peek()` or `advance()` exhausts the buffer.
- **Token access.** Peek: `adapter.peek()`. Advance: `adapter.advance()`.
  Peek-ahead: `adapter.peek_ahead(n)`.
- **Context-aware lexing.** Before prefix dispatch, the parser calls
  `adapter.set_category(CATEGORY_ID_CAT)`, which tells the lexer which grammar
  category is active. The lexer uses this to consult the `composed_dispatch()`
  table when it encounters an ambiguous DFA accept state, selecting the correct
  token kind for the current syntactic context.
- **No backtracking.** Cross-category dispatch is resolved at lex time by the
  composed dispatch table. The parser never saves/restores a position.
- **Recursive descent.** The lazy parser is a conventional recursive descent
  parser -- not trampolined. Stack safety for deep nesting relies on the
  standard trampolined path (callers choose which entry point to use).

Data flow:

```
  Input string
       │
       ▼
  Lexer::new(input)
       │
       ▼
  LexerAdapter::new(lexer)
       │
       ├─── set_category(CATEGORY_ID_PROC) ──▶ Lexer knows syntactic context
       │
       ├─── peek()  ─────▶  ensure_buffered(0)
       │                         │
       │                         ▼
       │               next_token_for_category(category_id)
       │                         │
       │                         ├── DFA scan ──▶ accept_state
       │                         │
       │                         ├── composed_dispatch(category_id, accept_state)
       │                         │       │
       │                         │       ├── non-empty: accept_token_by_kind(state, text, kind_id)
       │                         │       └── empty:     accept_token(state, text)
       │                         │
       │                         ▼
       │                  (Token, Range) buffered
       │
       ├─── advance() ──▶ cursor += 1; drain if cursor > 8
       │
       ▼
  parse_Cat_lazy(adapter, 0) ──▶ AST result
```

### 1.3 Side-by-Side Summary

```
┌─────────────────────┬───────────────────────────┬────────────────────────────────┐
│                     │ Slice-Based (Standard)    │ Adapter-Based (Lazy)           │
├─────────────────────┼───────────────────────────┼────────────────────────────────┤
│ Activation          │ Always emitted            │ Always emitted                 │
│ Function name       │ parse_Cat / parse_Cat_own │ parse_Cat_lazy                 │
│ Tokenization        │ Eager (full lex() call)   │ On-demand (peek/advance)       │
│ Token source        │ &[(Token, Range)] slice   │ &mut LexerAdapter<'a>          │
│ Disambiguation      │ Backtracking (save/restore│ Composed dispatch table        │
│                     │ on &mut usize)            │ (precomputed, no backtracking) │
│ Category context    │ None (lexer is unaware)   │ set_category(id) before prefix │
│ Stack safety        │ Trampolined (Frame_Cat)   │ Recursive descent (call stack) │
│ Cross-category      │ Try parse, restore pos    │ Resolved by lexer at token time│
│ Memory              │ O(n) token vec up front   │ O(1) buffer (capacity 4)       │
│ Codegen entry point │ write_trampolined_parser  │ write_trampolined_parser_lazy  │
│                     │ (trampoline.rs:582)       │ (trampoline.rs:2370)           │
└─────────────────────┴───────────────────────────┴────────────────────────────────┘
```

---

## 2. `set_category()` Call Pattern

The `set_category()` method on `LexerAdapter` informs the underlying `Lexer`
which grammar category the parser is currently trying to match. This is the
mechanism through which syntactic context flows back into the lexer.

### 2.1 Protocol

1. **At function entry** (before prefix dispatch):
   ```
   adapter.set_category(CATEGORY_ID_<CAT>);
   ```
   This is emitted at `trampoline.rs:2402`. For example, if category `Proc` has
   index 0 and `Int` has index 1:
   ```
   adapter.set_category(0);   // in parse_Proc_lazy
   adapter.set_category(1);   // in parse_Int_lazy
   ```

2. **At start of infix loop** (after prefix yields `lhs`):
   ```
   adapter.set_category(0);
   ```
   This is emitted at `trampoline.rs:2730`. The category is cleared to 0
   because infix tokens are unambiguous by construction -- they are
   operator-like terminals (`+`, `-`, `*`, `?`, `:`) that do not overlap with
   identifier-like tokens. Setting category to 0 tells the lexer to use the
   standard `next_token()` path (no composed dispatch), which avoids
   unnecessary table lookups during the tight infix loop.

### 2.2 Category ID Constants

Category IDs are emitted as constants by `emit_composed_dispatch_table()`
(`prediction.rs:1640-1642`):

```
const CATEGORY_ID_PROC: u8 = 0;
const CATEGORY_ID_INT: u8 = 1;
const CATEGORY_ID_NAME: u8 = 2;
```

These are derived from the order of categories in the `LanguageSpec`.

### 2.3 How the Lexer Uses Category Context

Inside `LexerAdapter::ensure_buffered()` (`codegen.rs:1025-1029`):

```
let result = if self.category_id > 0 {
    self.lexer.next_token_for_category(self.category_id)
} else {
    self.lexer.next_token()
};
```

When `category_id > 0`, the lexer calls `next_token_for_category()` which, upon
reaching an accept state, consults the composed dispatch table:

```
let dispatch = composed_dispatch(category_id, accept_state);
if dispatch.is_empty() {
    /* unambiguous state -- use default accept_token() */
} else {
    let (kind_id, _rule, _weight) = dispatch[0];  /* best by tropical weight */
    accept_token_by_kind(accept_state, text, kind_id)
}
```

This resolves ambiguous DFA states (e.g., `error` matching both `Token::Error`
keyword and `Token::Ident("error")`) using the FIRST set of the current
category, weighted by rule specificity via the tropical semiring.

### 2.4 Flow Diagram

```
                        parse_Proc_lazy(adapter, 0)
                                  │
                     set_category(CATEGORY_ID_PROC)
                                  │
                         ┌────────┴────────┐
                         │  Prefix Phase   │
                         │                 │
                         │  adapter.peek() │──▶ ensure_buffered(0)
                         │                 │        │
                         │                 │        ▼
                         │                 │   category_id == CATEGORY_ID_PROC
                         │                 │        │
                         │                 │        ▼
                         │                 │   next_token_for_category(CATEGORY_ID_PROC)
                         │                 │        │
                         │                 │        ├─── DFA scan ──▶ ambiguous state?
                         │                 │        │                      │
                         │                 │        │              ┌──────┴──────┐
                         │                 │        │              │ Yes         │ No
                         │                 │        │              ▼             ▼
                         │                 │        │     composed_dispatch   accept_token
                         │                 │        │     (PROC, state)      (state, text)
                         │                 │        │           │
                         │                 │        │           ▼
                         │                 │        │     accept_token_by_kind
                         │                 │        │     (state, text, kind_id)
                         │                 │        │
                         └────────┬────────┘
                                  │
                     set_category(0)        ◀──── infix tokens are unambiguous
                                  │
                         ┌────────┴────────┐
                         │   Infix Loop    │
                         │                 │
                         │  adapter.peek() │──▶ ensure_buffered(0)
                         │                 │        │
                         │                 │        ▼
                         │                 │   category_id == 0
                         │                 │        │
                         │                 │        ▼
                         │                 │   next_token()    (no dispatch table)
                         │                 │
                         └─────────────────┘
```

---

## 3. Cross-Category Dispatch: Before and After

### 3.1 The Problem

In multi-category grammars (e.g., `Proc`, `Int`, `Name`), the same token can
begin rules in different categories. For example, `Token::Ident("x")` could be:
- A `Proc::PVar("x")` (process variable)
- An `Int::IVar("x")` (integer variable)
- A `Name::NVar("x")` (name variable)

When parsing in a context that expects a `Proc`, and the cross-category
dispatch encounters `Token::Ident`, it must determine whether to parse as
`Proc` (own rules), `Int` (via a cast rule), or something else.

### 3.2 BEFORE: Save/Restore Backtracking (Slice-Based)

The standard parser resolves cross-category ambiguity by trial parsing.
It saves `*pos`, attempts a parse, and restores on failure:

```rust
/* Generated code in parse_Proc (slice-based dispatch wrapper) */
Token::Ident(_) => {
    let saved = *pos;

    /* Try Int first (cross-category cast rule: Int -> Proc) */
    if let Ok(int_val) = parse_Int(tokens, pos, 0) {
        /* Check if next token confirms this was the right parse */
        if matches!(tokens.get(*pos).map(|(t,_)| t), Some(Token::Eq)) {
            /* Commit: Int parse consumed the right tokens */
            return Ok(Proc::IntCast(Box::new(int_val)));
        }
    }

    /* Backtrack: restore position and try own category */
    *pos = saved;
    parse_Proc_own(tokens, pos, min_bp)
}
```

This has several downsides:
- **Wasted work.** The trial parse of `Int` may tokenize and build partial AST
  nodes that are discarded on backtrack.
- **Complexity.** Each ambiguous token requires nested `if let Ok` chains with
  save/restore bookkeeping.
- **Ordering sensitivity.** The order of trial parses matters -- the first
  successful parse wins, which may not be the most specific match.

### 3.3 AFTER: Composed Dispatch (Adapter-Based)

The lazy parser eliminates backtracking entirely. When the adapter's `peek()`
encounters an ambiguous DFA accept state, the composed dispatch table resolves
it based on the current category context:

```rust
/* Generated code in parse_Proc_lazy (adapter-based) */
Token::Ident(name) => {
    /* The composed dispatch already resolved this token to
       Token::Ident -- not Token::Error or another ambiguous
       alternative -- because the category context is PROC
       and the dispatch table selected kind_id for Ident.

       No save/restore. No backtracking. */
    let name_str = name.to_string();
    adapter.advance();
    break 'prefix Proc::PVar(name_str);
}
```

The resolution happens inside `ensure_buffered()` before the parser ever sees
the token:

```
composed_dispatch(CATEGORY_ID_PROC, accept_state) -> [(kind_id, rule, weight), ...]
```

The table returns entries sorted by tropical weight (lowest = most specific).
The lexer uses `dispatch[0]` -- the best match -- and produces the
corresponding `Token` variant via `accept_token_by_kind()`.

### 3.4 Comparison Diagram

```
  BEFORE (slice-based):                    AFTER (adapter-based):

  Token::Ident("x")                       Token::Ident("x")
         │                                        │
         ▼                                        ▼
  ┌─────────────────┐                    ┌──────────────────────────┐
  │ save pos        │                    │ Lexer resolves at        │
  │ try parse_Int   │                    │ accept-state time via    │
  │   ├── success?  │                    │ composed_dispatch()      │
  │   │   ├── Y: check lookahead        │                          │
  │   │   │   ├── match: commit         │ Category = PROC          │
  │   │   │   └── no match: restore     │ ──▶ kind_id = Ident     │
  │   │   └── N: restore               │                          │
  │   └── try parse_Proc_own           │ Token already correct     │
  │       └── commit or fail           │ ──▶ no backtracking      │
  └─────────────────┘                    └──────────────────────────┘
        Multiple                                 Single
        parse attempts                           token production
```

---

## 4. Generated Code Structure

The `write_trampolined_parser_lazy()` function (`trampoline.rs:2370-2776`)
generates a complete `parse_Cat_lazy()` function for each grammar category.
The generated code follows a Pratt-style prefix-then-infix structure.

### 4.1 Function Signature

```rust
fn parse_Cat_lazy<'a>(
    adapter: &mut LexerAdapter<'a>,
    min_bp: u8,
) -> Result<Cat, ParseError> {
```

Generated at `trampoline.rs:2392-2399`. Takes the adapter by mutable reference
(shared across all recursive calls in the same parse tree) and the minimum
binding power for Pratt precedence climbing.

### 4.2 Category Context Setup

```rust
    adapter.set_category(CATEGORY_ID_CAT);
    let mut cur_bp = min_bp;
```

Generated at `trampoline.rs:2402-2403`. Sets the lexer's disambiguation
context before any tokens are peeked.

### 4.3 Prefix Dispatch

The prefix phase is a labeled block `'prefix: { ... }` that yields the initial
`lhs` value. It peeks at the current token and dispatches:

```rust
    let mut lhs: Cat = 'prefix: {
        /* EOF check with lex error propagation (see Section 5) */
        if adapter.is_eof() { ... }

        match adapter.peek() {
```

Within the match, arms are generated in the following order:

#### 4.3.1 Terminal-First RD Handlers (trampoline.rs:2434-2537)

Rules that begin with a terminal keyword (e.g., `"error" Int -> Proc`). The
first terminal is consumed, then remaining items are inlined:

```rust
            Token::Error => {
                adapter.advance();
                let p0 = parse_Int_lazy(adapter, 0)?;
                break 'prefix Proc::ErrorHandler(Box::new(p0));
            },
```

RD handler splitting (`split_rd_handler()`) divides multi-nonterminal rules
into segments. Each segment's inline items are emitted via
`write_lazy_inline_items()` (`trampoline.rs:2781-2796`), and nonterminals
become recursive `parse_Cat_lazy()` calls.

Complex rules (those with ZipMapSep or multi-binder items) are skipped --
`should_use_standalone_fn()` returns `true` and the arm is not generated.

#### 4.3.2 Unary Prefix Operators (trampoline.rs:2539-2558)

Rules marked with `is_unary_prefix` (e.g., `-Int -> Int`):

```rust
            Token::Minus => {
                adapter.advance();
                let operand = parse_Int_lazy(adapter, prefix_bp)?;
                break 'prefix Int::Neg(Box::new(operand));
            },
```

The `prefix_bp` is `max_infix_bp + 2`, ensuring prefix operators bind tighter
than any infix operator.

#### 4.3.3 Grouped Expressions (trampoline.rs:2560-2578)

Parenthesized sub-expressions:

```rust
            Token::LParen => {
                adapter.advance();
                let inner = parse_Cat_lazy(adapter, 0)?;
                if !matches!(adapter.peek(), Token::RParen) {
                    return Err(ParseError::UnexpectedToken {
                        expected: "')'",
                        found: format!("{:?}", adapter.peek()),
                        range: *adapter.peek_range(),
                    });
                }
                adapter.advance();
                break 'prefix inner;
            },
```

The binding power resets to 0 inside parentheses, allowing any operator.

#### 4.3.4 Native Literals (trampoline.rs:2580-2635)

Categories with a `native_type` get a literal arm. The token variant depends
on the native type:

| Native type                | Token variant    | AST constructor  |
|----------------------------|------------------|------------------|
| `i32`, `i64`, `u32`, etc.  | `Token::Integer` | `Cat::NumLit`    |
| `f32`, `f64`               | `Token::Float`   | `Cat::FloatLit`  |
| `bool`                     | `Token::Boolean` | `Cat::BoolLit`   |
| `str`, `String`            | `Token::StringLiteral` | `Cat::StringLit` |

Example for `i32`:

```rust
            Token::Integer(n) => {
                let val = *n;
                adapter.advance();
                break 'prefix Int::NumLit(val);
            },
```

#### 4.3.5 Ident Capture with Lookahead (trampoline.rs:2637-2708)

Variable rules (`syntax: [IdentCapture]`) and rules that start with an
identifier followed by a distinguishing terminal. Two sub-cases:

**No lookahead needed** (only a simple variable rule exists):

```rust
            Token::Ident(name) => {
                let name_str = name.to_string();
                adapter.advance();
                break 'prefix Cat::Var(name_str);
            },
```

**Lookahead needed** (multiple ident-first rules, e.g., `x = Proc` and `x`):

```rust
            Token::Ident(name) => {
                let name_str = name.to_string();
                adapter.advance();
                match adapter.peek() {
                    Token::Eq => {
                        adapter.advance();
                        let body = parse_Proc_lazy(adapter, 0)?;
                        break 'prefix Proc::Assign(name_str, Box::new(body));
                    },
                    _ => {
                        break 'prefix Proc::PVar(name_str);
                    }
                }
            },
```

#### 4.3.6 Catch-All Error (trampoline.rs:2712-2722)

```rust
            other => {
                return Err(ParseError::UnexpectedToken {
                    expected: EXPECTED_CAT,
                    found: format!("{:?}", other),
                    range: *adapter.peek_range(),
                });
            }
```

The expected message is computed at codegen time from the category's FIRST set
using `build_expected_message_pub()`.

### 4.4 Infix Loop (trampoline.rs:2727-2772)

After prefix dispatch yields `lhs`, the category context is cleared and the
infix loop runs:

```rust
    adapter.set_category(0);
    loop {
        if adapter.is_eof() { break; }
        let token = adapter.peek();
```

The loop checks, in order:

1. **Postfix operators** (if any exist in the grammar):
   ```rust
        if let Some(l_bp) = postfix_bp_Cat(token) {
            if l_bp < cur_bp { break; }
            adapter.advance();
            lhs = make_postfix_Cat(token, lhs);
            continue;
        }
   ```

2. **Infix operators**:
   ```rust
        if let Some((l_bp, r_bp)) = infix_bp_Cat(token) {
            if l_bp < cur_bp { break; }
            adapter.advance();
            let op_token = token.clone();
            let rhs = parse_Cat_lazy(adapter, r_bp)?;
            lhs = make_infix_Cat(&op_token, lhs, rhs);
            continue;
        }
   ```

3. **Mixfix operators** (if any):
   Generated by `write_lazy_mixfix_handlers()` (`trampoline.rs:2897-2964`).
   Each mixfix operator (e.g., ternary `a ? b : c`) has its trigger token,
   interior operand parses, and separator token checks:
   ```rust
        if matches!(token, Token::Question) {
            let l_bp = mixfix_bp_Cat(token).unwrap_or((0, 0)).0;
            if l_bp >= cur_bp {
                adapter.advance();
                let then_val = parse_Cat_lazy(adapter, 0)?;
                if !matches!(adapter.peek(), Token::Colon) { ... }
                adapter.advance();
                let else_val = parse_Cat_lazy(adapter, 0)?;
                lhs = Cat::Ternary(Box::new(lhs), Box::new(then_val), Box::new(else_val));
                continue;
            }
        }
   ```

4. **Break** -- no infix match found, exit the loop.

The function concludes with:

```rust
    Ok(lhs)
}
```

### 4.5 Helper Functions

The lazy parser reuses the same BP lookup and constructor helpers as the
standard trampolined parser:

- `infix_bp_Cat(token) -> Option<(u8, u8)>` -- left and right binding powers
- `make_infix_Cat(op, lhs, rhs) -> Cat` -- infix AST constructor
- `postfix_bp_Cat(token) -> Option<u8>` -- postfix binding power
- `make_postfix_Cat(op, operand) -> Cat` -- postfix AST constructor
- `mixfix_bp_Cat(token) -> Option<(u8, u8)>` -- mixfix binding power

These are emitted once by `write_trampolined_parser()` (`trampoline.rs:600-612`)
and shared between the standard and lazy paths (see comment at
`trampoline.rs:2383-2385`).

---

## 5. Error Propagation (Phase 6H)

### 5.1 Lex Error Capture

The `LexerAdapter` has a `lex_error: Option<String>` field
(`codegen.rs:1011`). When `ensure_buffered()` calls `next_token()` or
`next_token_for_category()` and the lexer returns an `Err(msg)`, the adapter
stores the error and inserts a synthetic `Token::Eof` into the buffer:

```rust
Err(msg) => {
    self.lex_error = Some(msg);
    let pos = self.lexer.position();
    self.buf.push((Token::Eof, Range { start: pos, end: pos, file_id: None }));
    break;
}
```

This design ensures that the parser always sees a well-formed token stream.
The `Eof` acts as a sentinel that triggers the parser's EOF handling path.

### 5.2 Error Propagation in the Parser

At the start of prefix dispatch (`trampoline.rs:2413-2427`), the lazy parser
checks for EOF and propagates any captured lex error:

```rust
if adapter.is_eof() {
    if let Some(lex_err) = adapter.take_error() {
        return Err(ParseError::LexError {
            message: lex_err,
            position: Position { byte_offset: 0, line: 0, column: 0 },
        });
    }
    return Err(ParseError::UnexpectedEof {
        expected: EXPECTED_CAT,
        range: Range::zero(),
    });
}
```

The `take_error()` method (`codegen.rs:1060-1061`) uses `Option::take()` to
move the error out of the adapter, ensuring it is reported exactly once.

### 5.3 Expected-Message Constants

Per-category expected-message constants are emitted by
`write_expected_category_descriptions()` (`codegen.rs:766-780`):

```rust
const EXPECTED_PROC: &str = "identifier, '(', 'error', or 'new'";
const EXPECTED_INT: &str = "integer literal, identifier, '(', or '-'";
const EXPECTED_NAME: &str = "identifier or '@'";
```

These are built from the category's FIRST set at codegen time via
`build_expected_message_pub()`. The `Lexer::next_token_for_category()` method
uses a companion function `expected_for_category()` (`codegen.rs:864-871`) to
select the appropriate message for lexer-level errors:

```rust
fn expected_for_category(category_id: u8) -> &'static str {
    match category_id {
        0 => EXPECTED_PROC,
        1 => EXPECTED_INT,
        2 => EXPECTED_NAME,
        _ => "token"
    }
}
```

### 5.4 Error Flow Diagram

```
  Lexer encounters invalid character
           │
           ▼
  next_token_for_category() returns Err(msg)
           │
           ▼
  ensure_buffered() stores:
    lex_error = Some(msg)
    buf.push( (Token::Eof, ...) )
           │
           ▼
  adapter.peek() returns &Token::Eof
           │
           ▼
  adapter.is_eof() returns true
           │
           ▼
  adapter.take_error() returns Some(msg)
           │
           ▼
  Err(ParseError::LexError { message: msg, ... })
```

---

## 6. Limitations

### 6.1 Complex RD Rules Unsupported

The lazy parser skips rules that require standalone parse functions:

- **ZipMapSep rules** (e.g., `PInputs` with separator-delimited collection parsing).
  Detected by `has_zipmapsep()` (`trampoline.rs:52-56`).
- **Multi-binder rules** (rules with more than one binder item). Detected by
  `rule.has_multi_binder` in `should_use_standalone_fn()` (`trampoline.rs:65-67`).

These standalone functions currently use the token-slice API
(`&[(Token, Range)]` + `&mut usize`). A future enhancement would create
lazy-adapter versions of these standalone functions.

When a grammar contains such rules, the corresponding match arm is simply
omitted from the lazy parser's prefix dispatch. The comment at
`trampoline.rs:2463-2467` documents this:

```
/* For complex rules, delegate to standalone parse fn.
   These standalone fns use the token-slice API, so for now we skip
   them in the lazy parser. A future enhancement would create lazy
   versions of standalone fns. For now, the lazy parser handles
   simple rules inline. */
```

### 6.2 What the Lazy Parser Does Handle

The following rule types are fully supported in the lazy path:

| Rule Type               | Example                        | Handler Location       |
|--------------------------|-------------------------------|------------------------|
| Terminal-first RD rules  | `"error" Int -> Proc`         | trampoline.rs:2434-2537|
| Unary prefix operators   | `"-" Int -> Int`              | trampoline.rs:2539-2558|
| Grouped expressions      | `"(" Cat ")" -> Cat`          | trampoline.rs:2560-2578|
| Native literals          | `42`, `true`, `3.14`, `"hi"`  | trampoline.rs:2580-2635|
| Ident capture (variable) | `Ident -> Cat`                | trampoline.rs:2637-2708|
| Ident + lookahead        | `Ident "=" Proc -> Proc`      | trampoline.rs:2670-2707|
| Infix operators          | `Cat "+" Cat -> Cat`          | trampoline.rs:2750-2764|
| Postfix operators        | `Cat "!" -> Cat`              | trampoline.rs:2736-2748|
| Mixfix operators         | `Cat "?" Cat ":" Cat -> Cat`  | trampoline.rs:2766-2767|

### 6.3 No Trampolining (Stack Safety)

The lazy parser is a conventional recursive descent parser. Each recursive
`parse_Cat_lazy()` call consumes call stack space. For deeply nested inputs
(e.g., 100K-deep parenthesized expressions), the call stack will overflow.

Stack safety for such inputs is provided by the standard trampolined parser
(`parse_Cat()`), which uses an explicit heap-allocated continuation stack.
Callers should choose the appropriate entry point based on expected input depth:

- **Lazy path:** Best for grammars with context-sensitive lexing needs and
  inputs with moderate nesting depth (< ~10K levels, depending on stack size).
- **Standard path:** Best for deep nesting — the trampolined standard parser
  uses an explicit continuation stack with no call-stack depth limit.

### 6.4 Feature-Gated Emission

The lazy parser is emitted alongside the standard trampolined parser only when
the `context-sensitive-lex` feature is enabled. In the pipeline (`pipeline.rs`):

```rust
#[cfg(feature = "context-sensitive-lex")]
{
    crate::trampoline::write_trampolined_parser_lazy(
        &mut buf, &tramp_config, &bundle.bp_table,
        &cat_handlers, &bundle.rd_rules, cat_idx,
    );
}
```

Without the feature, the lazy parser functions and all associated infrastructure
(Lexer, LexerAdapter, EXPECTED constants) are not emitted, saving ~2,000-4,000
lines of generated code per grammar and eliminating icache pollution.

Both entry points (`Cat::parse()` for the standard path and
`Cat::parse_context_sensitive()` for the lazy path) coexist in the generated
module. The `Lexer` struct, `LexerAdapter`, composed dispatch table, and
`parse_Cat_lazy()` functions are always available.
