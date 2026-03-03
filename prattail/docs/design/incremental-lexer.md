# PraTTaIL: Incremental Lexer and LexerAdapter (Phase 6D)

> **Historical**: This document describes the `context-sensitive-lex` feature which was removed.
> The always-on WFST architecture now resolves all lexer ambiguities at compile time,
> making the runtime context-sensitive lexing infrastructure unnecessary.
> This document is retained for historical reference only.

**Date:** 2026-02-26

---

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [`next_token()` vs `next_token_for_category()`](#2-next_token-vs-next_token_for_category)
3. [`accept_token_by_kind()` Cascade](#3-accept_token_by_kind-cascade)
4. [LexerAdapter: Buffered Parser Interface](#4-lexeradapter-buffered-parser-interface)
5. [Error Handling (Phase 6H)](#5-error-handling-phase-6h)
6. [Zero-Overhead Analysis](#6-zero-overhead-analysis)
7. [Backward-Compatible `lex()` Wrapper](#7-backward-compatible-lex-wrapper)

---

## 1. Architecture Overview

The pipeline always emits a `Lexer<'a>` struct that provides incremental,
token-at-a-time lexing as part of the context-sensitive lexing infrastructure.
This replaces the batch `lex()` model (which eagerly tokenizes the entire input
into a `Vec<(Token<'a>, Range)>`) with a demand-driven model where the parser
requests tokens one at a time, passing its current grammatical context to the
lexer for disambiguation.

### Lexer Struct Fields

```
┌──────────────────────────────────────────────────────────────┐
│                     Lexer<'a>                                │
├──────────────────────────────────────────────────────────────┤
│  input:   &'a str           Source text (borrowed)           │
│  bytes:   &'a [u8]          Byte view of input               │
│  pos:     usize             Current byte offset              │
│  line:    usize             Current line number (0-indexed)  │
│  col:     usize             Current column number (0-indexed)│
│  file_id: Option<u32>       Optional file identifier         │
├──────────────────────────────────────────────────────────────┤
│  new(input, file_id)          Constructor                    │
│  is_eof() -> bool             End-of-input check             │
│  position() -> Position       Current source position        │
│  next_token() -> Result<..>   Unfiltered scan                │
│  next_token_for_category(u8)  Context-aware scan             │
│      -> Result<..>                                           │
└──────────────────────────────────────────────────────────────┘
```

### State Machine: Token Scan Loop

Both `next_token()` and `next_token_for_category()` share the same inner scan
loop. The difference is only in the accept-state resolution at the end.

```
  ┌─────────────────────────┐
  │ Skip whitespace         │◁─── bytes[pos] in {' ', '\t', '\n', '\r'}
  │ (update line/col)       │     pos += 1; loop
  └────────────┬────────────┘
               │ pos >= bytes.len()?
               │ yes ─────────────────────────── return Ok((Token::Eof, eof_range))
               │ no
               ▼
  ┌─────────────────────────┐
  │ Record start position   │     start = pos; start_line = line; start_col = col
  │ state = 0               │     last_accept = None
  │ (check state 0 accept)  │
  └────────────┬────────────┘
               ▼
  ┌─────────────────────────┐
  │ DFA Scan Loop           │◁───┐
  │                         │    │
  │ class = CHAR_CLASS[b]   │    │
  │ next = dfa_next(state,  │    │
  │        class)           │    │
  │                         │    │ next != u32::MAX (DEAD)
  │ next == DEAD? ──────────┼────┘ no: state = next; update line/col; pos += 1
  │              │ yes      │        if accept: last_accept = Some(state,pos,...)
  │              ▼          │
  │ break                   │
  └────────────┬────────────┘
               ▼
  ┌─────────────────────────┐
  │ Accept Resolution       │
  │                         │
  │ last_accept == None?    │── yes ── return Err("unexpected character")
  │              │ no       │
  │              ▼          │
  │ restore pos/line/col    │
  │ text = input[start..end]│
  │                         │
  │ ┌─ next_token():        │     accept_token(state, text)
  │ │                       │
  │ └─ next_token_for_      │     composed_dispatch(cat_id, state)
  │    category():          │     ├─ empty: accept_token(state, text)
  │                         │     └─ non-empty: accept_token_by_kind(state, text, kind_id)
  │                         │                   fallback: accept_token(state, text)
  └─────────────────────────┘
```

### Source Files

- **Lexer struct codegen:** `prattail/src/automata/codegen.rs` -- `write_lexer_struct()`
- **LexerAdapter codegen:** `prattail/src/automata/codegen.rs` -- `write_lexer_adapter()`
- **Pipeline assembly:** `prattail/src/pipeline.rs` -- `generate_parser_code_with_context()`
- **Composed dispatch table:** `prattail/src/prediction.rs` -- `emit_composed_dispatch_table()`
- **Lazy parser codegen:** `prattail/src/trampoline.rs` -- `write_trampolined_parser_lazy()`
- **Integration tests:** `prattail/src/tests/integration_tests.rs` -- context-sensitive lex tests

---

## 2. `next_token()` vs `next_token_for_category()`

### `next_token()`: Unfiltered Lexing

`next_token()` is identical to the inner loop of the batch `lex()` function,
refactored into the `Lexer` struct. It:

1. Skips whitespace (space, tab, newline, carriage return), updating `line`
   and `col`.
2. Runs the DFA scan loop from state 0, tracking the most recent accepting
   state via `last_accept: Option<(u32, usize, usize, usize)>` (DFA state,
   end position, end line, end column).
3. On DFA termination (dead state or end of input), restores position to the
   last accept point.
4. Calls `accept_token(state, text)` to construct the `Token<'a>`.

When the DFA reaches an ambiguous accepting state (a state that could produce
two or more distinct token kinds), `accept_token()` resolves by returning the
first match in declaration order. This is the same maximal-munch, priority-based
resolution used by the batch `lex()` function.

```
accept_token(state, text) -> Option<Token<'a>>
```

### `next_token_for_category(category_id: u8)`: Context-Aware Lexing

`next_token_for_category()` runs the same whitespace-skipping and DFA scan
loop, but uses the parser's grammatical context to resolve ambiguous accept
states. After the DFA terminates:

1. It calls `composed_dispatch(category_id, accept_state)` to look up the
   composed dispatch table.
2. If the table returns an empty slice (no ambiguity for this category at this
   state), it falls through to `accept_token(state, text)` -- identical to
   `next_token()`.
3. If the table returns a non-empty slice, it extracts the highest-priority
   entry `(kind_id, rule_label, weight)` and calls
   `accept_token_by_kind(state, text, kind_id)` to construct the token as
   the specific kind indicated by the parser context.
4. If `accept_token_by_kind()` returns `None` (kind mismatch), falls back to
   `accept_token(state, text)`.

```
composed_dispatch(category_id, dfa_state) -> &'static [(u8, &'static str, f64)]
                                                        │        │          │
                                                  kind_id  rule_label   weight
```

### Delegation When No Ambiguity Exists

When the DFA has no ambiguous accepting states (`LexerAmbiguityInfo.has_ambiguous
== false`), the generated `next_token_for_category()` simply delegates to
`next_token()`, adding only category-aware error messages:

```rust
pub fn next_token_for_category(&mut self, category_id: u8)
    -> Result<(Token<'a>, Range), String>
{
    match self.next_token() {
        Ok(tok_range) => Ok(tok_range),
        Err(msg) => Err(format!("{} (expected {})",
            msg, expected_for_category(category_id))),
    }
}
```

This ensures that `next_token_for_category()` compiles to nearly identical
code as `next_token()` when the grammar has no lexical ambiguity, with only
a thin error-message enhancement wrapper.

---

## 3. `accept_token_by_kind()` Cascade

### Function Signature

```rust
fn accept_token_by_kind<'a>(state: u32, text: &'a str, kind_id: u8) -> Option<Token<'a>>
```

### Purpose

Maps a `(state, kind_id)` pair back to the appropriate `Token` constructor.
The `kind_id` is a compact integer from the `TokenVariantMap`, which assigns
stable IDs to token kinds in declaration order:

| ID | Variant Name  | Constructor                                              |
|----|---------------|----------------------------------------------------------|
| 0  | Eof           | `Token::Eof`                                             |
| 1  | Ident         | `Token::Ident(text)`                                     |
| 2  | Integer       | `Token::Integer(text.parse::<i64>().expect(...))`        |
| 3  | Float         | `Token::Float(text.parse::<f64>().expect(...))`          |
| 4  | Boolean       | `Token::Boolean(text == "true")`                         |
| 5  | StringLit     | `Token::StringLit(&text[1..text.len()-1])`               |
| 6  | Dollar        | `Token::Dollar(&text[1..])`                              |
| 7  | DoubleDollar  | `Token::DoubleDollar(&text[2..text.len()-1])`            |
| N  | `<Fixed>`     | `Token::<VariantName>`                                   |

(Actual IDs depend on the grammar's token kinds; the table above shows the
standard ordering.)

### Generated Code Structure

```rust
fn accept_token_by_kind<'a>(state: u32, text: &'a str, kind_id: u8) -> Option<Token<'a>> {
    match kind_id {
        0 => Some(Token::Eof),
        1 => Some(Token::Ident(text)),
        2 => Some(Token::Integer(text.parse::<i64>().expect("invalid integer literal"))),
        3 => Some(Token::Float(text.parse::<f64>().expect("invalid float literal"))),
        4 => Some(if text == "true" { Token::Boolean(true) }
                  else { Token::Boolean(false) }),
        5 => Some(Token::StringLit(&text[1..text.len()-1])),
        /* ... fixed terminal variants ... */
        _ => accept_token(state, text)    /* fallback: default priority resolution */
    }
}
```

### Cascade Behavior

The resolution cascade for `next_token_for_category()` is:

```
composed_dispatch(category_id, state)
         │
         ├── empty slice ───────────────── accept_token(state, text)
         │
         └── [(kind_id, rule, weight), ...]
                    │
                    ▼
             accept_token_by_kind(state, text, kind_id)
                    │
                    ├── Some(token) ─────── return token
                    │
                    └── None ───────────── accept_token(state, text)  [fallback]
```

This three-tier cascade ensures that:

1. Unambiguous states use the fast `accept_token()` path (no dispatch lookup).
2. Ambiguous states consult the parser context to select the correct kind.
3. If the context-directed kind does not match (defensive), the fallback
   `accept_token()` prevents silent token loss.

### Source File

`prattail/src/automata/codegen.rs` -- `write_accept_token_by_kind()`

---

## 4. LexerAdapter: Buffered Parser Interface

The `LexerAdapter` sits between the `Lexer` and the parser, providing buffered
peek-ahead and category-aware disambiguation. The parser interacts exclusively
with the adapter rather than the lexer directly.

### Struct Fields

```
┌──────────────────────────────────────────────────────────────────┐
│                    LexerAdapter<'a>                               │
├──────────────────────────────────────────────────────────────────┤
│  lexer:       Lexer<'a>                Underlying incremental    │
│                                        lexer                     │
│  buf:         Vec<(Token<'a>, Range)>  Ring-like token buffer    │
│  cursor:      usize                    Read position in buf      │
│  category_id: u8                       Current parse category    │
│  lex_error:   Option<String>           Captured lex error        │
├──────────────────────────────────────────────────────────────────┤
│  new(lexer)                            Constructor (capacity: 4) │
│  set_category(id: u8)                  Set parser context        │
│  peek() -> &Token<'a>                  Current token             │
│  peek_range() -> &Range                Current token's range     │
│  peek_ahead(n) -> Option<&Token<'a>>   Lookahead by n tokens     │
│  advance()                             Consume current token     │
│  is_eof() -> bool                      End-of-input check        │
│  take_error() -> Option<String>        Retrieve captured error   │
└──────────────────────────────────────────────────────────────────┘
```

### `set_category(id)`: Parser Context Injection

Before prefix dispatch, the lazy parser calls `adapter.set_category(CATEGORY_ID_CAT)`
to inform the adapter which grammatical category is currently being parsed.
This category ID is passed through to `Lexer::next_token_for_category()` when
the adapter needs to fill its buffer, enabling the lexer to resolve ambiguous
DFA states using the composed dispatch table.

```rust
/* Inside parse_Int_lazy(): */
adapter.set_category(CATEGORY_ID_INT);
/* ... prefix dispatch on adapter.peek() ... */
```

Category ID constants are generated alongside the composed dispatch table:

```rust
const CATEGORY_ID_PROC: u8 = 0;
const CATEGORY_ID_NAME: u8 = 1;
const CATEGORY_ID_INT:  u8 = 2;
/* ... */
```

### `ensure_buffered(n)`: Lazy Fill from Lexer

The adapter lazily fills its buffer only when a peek or advance operation
requires tokens that have not yet been lexed. The fill logic respects the
current `category_id`:

```rust
fn ensure_buffered(&mut self, n: usize) {
    while self.buf.len() <= self.cursor + n {
        if self.lex_error.is_some() {
            /* Error already captured -- emit synthetic Eof */
            let pos = self.lexer.position();
            self.buf.push((Token::Eof, Range { start: pos, end: pos, file_id: None }));
            break;
        }
        let result = if self.category_id > 0 {
            self.lexer.next_token_for_category(self.category_id)
        } else {
            self.lexer.next_token()
        };
        match result {
            Ok(tok_range) => self.buf.push(tok_range),
            Err(msg) => {
                self.lex_error = Some(msg);
                let pos = self.lexer.position();
                self.buf.push((Token::Eof, Range { start: pos, end: pos, file_id: None }));
                break;
            }
        }
    }
}
```

When `category_id == 0`, the adapter falls back to `next_token()` (unfiltered),
which is the default before the parser has established a category context.

### Buffer Lifecycle

```
           fill                     peek / peek_ahead           advance
     ┌──────────────┐           ┌──────────────────────┐    ┌───────────────┐
     │ ensure_      │           │ buf[cursor + n]      │    │ cursor += 1   │
     │ buffered(n)  │──────────▶│ returns &Token       │    │               │
     │              │           │ or &Range            │    │ cursor > 8?   │
     │ lexer.next_  │           └──────────────────────┘    │ yes: drain    │
     │ token[_for_  │                                       │   buf[..cur]  │
     │ category]()  │                                       │   cursor = 0  │
     └──────────────┘                                       └───────────────┘
```

The drain threshold of 8 prevents unbounded buffer growth. When `cursor`
exceeds 8, consumed tokens are drained from the front of the buffer and
`cursor` is reset to 0. The initial capacity of 4 is sufficient for most
parse operations (typically 1 peek + 1 peek-ahead).

### Buffer Drain Sequence

```
State 0: buf = [t0, t1, t2, t3]  cursor = 0
         peek() = t0

State 1: advance()
         buf = [t0, t1, t2, t3]  cursor = 1
         peek() = t1

   ...   (multiple advances)

State 9: buf = [t0, t1, ..., t9]  cursor = 9
         cursor > 8 triggers drain:
         buf.drain(..9)  =>  buf = [t9]  cursor = 0
         peek() = t9
```

### Source File

`prattail/src/automata/codegen.rs` -- `write_lexer_adapter()`

---

## 5. Error Handling (Phase 6H)

### Lex Error Capture

The `LexerAdapter` captures lexer errors non-destructively. When
`Lexer::next_token()` or `Lexer::next_token_for_category()` returns an `Err`,
the adapter:

1. Stores the error message in `lex_error: Option<String>`.
2. Pushes a synthetic `(Token::Eof, eof_range)` into the buffer so the parser
   sees a clean end-of-input rather than panicking.
3. Subsequent `ensure_buffered()` calls detect `lex_error.is_some()` and
   short-circuit, continuing to emit synthetic Eof tokens.

The parser retrieves the captured error via `take_error()`:

```rust
pub fn take_error(&mut self) -> Option<String> {
    self.lex_error.take()
}
```

### Lazy Parser Error Propagation

The generated `parse_Cat_lazy()` functions check for lex errors at the top of
prefix dispatch, after the initial `is_eof()` check:

```rust
fn parse_Int_lazy<'a>(
    adapter: &mut LexerAdapter<'a>,
    min_bp: u8,
) -> Result<Int, ParseError> {
    adapter.set_category(CATEGORY_ID_INT);
    let mut cur_bp = min_bp;

    let mut lhs: Int = 'prefix: {
        if adapter.is_eof() {
            if let Some(lex_err) = adapter.take_error() {
                return Err(ParseError::LexError {
                    message: lex_err,
                    position: Position { byte_offset: 0, line: 0, column: 0 },
                });
            }
            return Err(ParseError::UnexpectedEof {
                expected: EXPECTED_INT,
                range: Range::zero(),
            });
        }
        match adapter.peek() {
            /* ... prefix dispatch ... */
        }
    };
    /* ... infix loop ... */
}
```

### Enhanced Error Messages

Per-category expected-token description constants are generated from FIRST set
analysis. The pipeline computes the FIRST set for each category and builds a
human-readable message:

```rust
const EXPECTED_PROC: &str = "Proc expression (one of: identifier, '{}', '*', ...)";
const EXPECTED_INT:  &str = "Int expression (one of: integer literal, identifier, '(', ...)";
const EXPECTED_NAME: &str = "Name expression (one of: identifier, '@', ...)";
```

The `expected_for_category()` helper maps category IDs to these constants:

```rust
fn expected_for_category(category_id: u8) -> &'static str {
    match category_id {
        0 => EXPECTED_PROC,
        1 => EXPECTED_NAME,
        2 => EXPECTED_INT,
        _ => "token"
    }
}
```

### Error Format

The `next_token_for_category()` error messages use the `expected_for_category()`
helper to provide context-specific messages:

**Unambiguous grammar (delegation path):**
```
3:5: unexpected character '#' (expected Int expression (one of: integer literal, identifier, ...))
```

**Ambiguous grammar (full context-aware path):**
```
3:5: unexpected character '#'; expected Int expression (one of: integer literal, identifier, ...)
```

### Source Files

- **Expected-token constants:** `prattail/src/automata/codegen.rs` -- `write_expected_category_descriptions()`
- **FIRST set to message:** `prattail/src/pratt.rs` -- `build_expected_message_pub()`
- **Pipeline assembly:** `prattail/src/pipeline.rs` -- `generate_parser_code_with_context()`
- **Lazy parser error flow:** `prattail/src/trampoline.rs` -- `write_trampolined_parser_lazy()`

---

## 6. Overhead Analysis

### Feature-Gated Infrastructure

The context-sensitive lexing runtime infrastructure is gated behind the
`context-sensitive-lex` feature flag. When enabled, the generated code includes:

- `Lexer<'a>` struct with `next_token()` and `next_token_for_category()`
- `LexerAdapter<'a>` with buffered peek-ahead
- `accept_token_by_kind()` function
- `EXPECTED_<CAT>` constants and `expected_for_category()` helper
- `parse_Cat_lazy()` functions for each category
- `CATEGORY_ID_<CAT>` constants
- `composed_dispatch()` runtime function (if ambiguous DFA states exist)

When the feature is **disabled** (default), none of this infrastructure is
emitted. The standard `parse()` path still benefits from composed dispatch
because the resolution happens at codegen time — ambiguous tokens are resolved
into deterministic match arms without save/restore backtracking.

The `Cat::parse_context_sensitive(input)` entry point is only available when
the `context-sensitive-lex` feature is enabled.

This is verified by integration tests:
- `test_emits_context_sensitive_lex_infrastructure_with_feature()` (with feature)
- `test_no_lazy_parsers_without_feature()` (without feature)

### No Ambiguous DFA States

If the grammar's DFA has no ambiguous accepting states
(`LexerAmbiguityInfo.has_ambiguous == false`), then:

- `next_token_for_category()` delegates to `next_token()` -- a single function
  call plus error message formatting on the error path only.
- No `composed_dispatch()` table is emitted (the table would be empty).
- `accept_token_by_kind()` is still emitted (for uniformity) but never called
  in practice.

The hot path through `next_token_for_category()` compiles to:

```rust
pub fn next_token_for_category(&mut self, category_id: u8)
    -> Result<(Token<'a>, Range), String>
{
    match self.next_token() {
        Ok(tok_range) => Ok(tok_range),   /* fast path: forward result */
        Err(msg) => Err(format!("{} (expected {})",
            msg, expected_for_category(category_id))),
    }
}
```

The `Ok` path is a single branch with no additional computation -- the compiler
can inline and eliminate the wrapper entirely.

### When Ambiguous States Exist

For grammars with ambiguous DFA states, the overhead on the hot path is:

1. One `composed_dispatch()` table lookup per token at an ambiguous state
   (static function, `match` on `(category_id, dfa_state)` pair).
2. If the dispatch returns entries: one `accept_token_by_kind()` call
   (`match` on `kind_id`) instead of `accept_token()`.
3. If the dispatch returns an empty slice: zero additional cost (falls through
   to `accept_token()`).

Non-ambiguous tokens (the majority in typical grammars) always take the fast
`accept_token()` path regardless of whether context-sensitive lexing is enabled.

### Summary Table

```
┌─────────────────────────────────┬─────────────────┬────────────────────┐
│ Entry Point                     │ Generated Code  │ Runtime Overhead   │
├─────────────────────────────────┼─────────────────┼────────────────────┤
│ Cat::parse(input)               │ Batch lex() +   │ Zero (standard     │
│ (standard path)                 │ array parser    │ two-phase path)    │
├─────────────────────────────────┼─────────────────┼────────────────────┤
│ Cat::parse_context_sensitive()  │ Lexer + Adapter │ One forwarding     │
│ No ambiguous DFA states         │ Delegation path │ call per token     │
│                                 │ No dispatch tbl │ (inlineable)       │
├─────────────────────────────────┼─────────────────┼────────────────────┤
│ Cat::parse_context_sensitive()  │ Lexer + Adapter │ One table lookup   │
│ Ambiguous DFA states present    │ Full dispatch   │ + kind-directed    │
│                                 │ table + by_kind │ accept per ambig.  │
│                                 │                 │ token              │
└─────────────────────────────────┴─────────────────┴────────────────────┘
```

---

## 7. Backward-Compatible `lex()` Wrapper

The original `lex()` function is always emitted by the lexer codegen pipeline
(`write_direct_coded_lexer()` or `write_compressed_lexer()`). This function is
**not** modified or replaced by the context-sensitive infrastructure.
It continues to work identically to the standard batch lexer:

```rust
pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> {
    lex_with_file_id(input, None)
}
```

The `lex()` function uses `accept_token()` exclusively -- it never calls
`composed_dispatch()` or `accept_token_by_kind()`. For ambiguous DFA states,
it resolves using declaration-order priority (the same behavior as before
context-sensitive lexing was introduced).

This means:

- Existing code that calls `lex()` continues to work unchanged.
- The standard trampolined parser (`parse_Cat()`) continues to use the batch
  `lex()` + index-based token access model.
- Only the lazy parser (`parse_Cat_lazy()`) and the `LexerAdapter` use the
  incremental `Lexer` struct.

### Coexistence of Both Paths

```
┌──────────────────────────────────────────────────────────────────────┐
│                        Generated Module                              │
│                                                                      │
│  ┌─────────────────────┐       ┌──────────────────────────────────┐  │
│  │  Standard Path       │       │  Context-Sensitive Path          │  │
│  │                     │       │                                  │  │
│  │  lex()              │       │  Lexer::new(input, file_id)      │  │
│  │    ▼                │       │    ▼                              │  │
│  │  Vec<(Token, Range)>│       │  LexerAdapter::new(lexer)        │  │
│  │    ▼                │       │    ▼                              │  │
│  │  parse_Cat(         │       │  parse_Cat_lazy(                 │  │
│  │    &tokens, &mut pos│       │    &mut adapter, min_bp)         │  │
│  │    min_bp)          │       │                                  │  │
│  │                     │       │  adapter.set_category(cat_id)    │  │
│  │  tokens[pos]        │       │  adapter.peek() / advance()      │  │
│  │  peek_token(t, pos) │       │  adapter.peek_ahead(n)           │  │
│  │  peek_ahead(t,p,n)  │       │                                  │  │
│  └─────────────────────┘       └──────────────────────────────────┘  │
│                                                                      │
│  Both paths share:                                                   │
│    Token<'a> enum, Range, Position, ParseError,                      │
│    accept_token(), dfa_next(), CHAR_CLASS, is_whitespace()           │
└──────────────────────────────────────────────────────────────────────┘
```

Both paths can coexist in the same generated module when the
`context-sensitive-lex` feature is enabled. The standard batch-lex path is
always emitted. The incremental path is only emitted with the feature flag.
Shared infrastructure (Token enum, DFA tables, accept functions) is emitted
exactly once regardless of feature state.

---

## Appendix: Composed Dispatch Table

The composed dispatch table is the bridge between the parser's grammatical
context and the lexer's ambiguous DFA states. It is computed at compile time
by `compute_composed_dispatch()` in `prediction.rs` and emitted as a static
function.

### Table Structure

```rust
fn composed_dispatch(category_id: u8, dfa_state: u32)
    -> &'static [(u8, &'static str, f64)]
/*                 │        │          │
             kind_id  rule_label   weight (tropical: lower = better)  */
{
    match (category_id, dfa_state) {
        (0, 7) => &[(2, "NumLit", 0.000000), (1, "PVar", 1.000000)],
        (1, 7) => &[(1, "NVar", 0.000000)],
        _ => &[]    /* no ambiguity for this (category, state) pair */
    }
}
```

### Computation

For each ambiguous DFA state `s` (a state with 2+ accepting token kinds):

1. For each category `C`:
   - For each alternative token kind `K` accepted at state `s`:
     - Check if `K`'s variant name is in `FIRST(C)`.
     - If yes, find the best-matching rule in `C` whose first item matches `K`.
     - Compute a weight based on rule specificity (terminal-first rules get
       lower/better weight than NT-first or ident rules).
   - Collect all `(kind_id, rule_label, weight)` entries, sorted by weight.

2. If a category has zero or one entries for a state, no disambiguation is
   needed -- the entry is omitted (the `_ => &[]` default handles it).

This table is only emitted when `ambiguity_info.has_ambiguous` is true.

### Source File

`prattail/src/prediction.rs` -- `compute_composed_dispatch()`,
`emit_composed_dispatch_table()`
