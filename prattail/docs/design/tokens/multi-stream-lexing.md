# Multi-Stream Token Routing

**Date:** 2026-03-11

---

## 1. Why a Single Token Stream Loses Information

A conventional lexer produces one flat token sequence. Whitespace is discarded,
comments vanish, and documentation annotations disappear before the parser sees
them. This is fine for compilation but creates problems for every tool that
needs that metadata:

  - **Formatters** need original whitespace to preserve or normalize indentation.
  - **Doc generators** need doc-comments associated with adjacent declarations.
  - **IDEs** need comment spans for hover, fold regions, and highlighting.
  - **Linters** may inspect comment content (TODO markers, license headers).

The traditional fix is a second lexer pass (doubling work) or including
comments in the parser grammar (polluting every production). PraTTaIL solves
this with **named output streams**: every token is routed to exactly one stream
at lex time. The parser consumes only `main`; auxiliary streams are returned
alongside the parse result as structured metadata.

---

## 2. Syntax

Token definitions carry an optional `-> stream_name` annotation:

```
tokens {
    // Main stream (no annotation needed)
    Plus    = '+'
    Minus   = '-'
    Integer = /[0-9]+/

    // Auxiliary streams
    LineComment  = /\/\/[^\n]*/                      -> comments
    BlockComment = /\/\*[^*]*\*+([^/*][^*]*\*+)*\//  -> comments
    Whitespace   = /[ \t\n\r]+/                      -> whitespace
    DocComment   = /\/\/\/[^\n]*/                     -> docs
}
```

**Rules:**

  - Tokens without `-> stream` go to `main` (stream ID 0).
  - Stream names are arbitrary identifiers, created on first use.
  - Each token has exactly one destination stream.
  - `main` is always present and consumed by the parser.

---

## 3. The `LexResult<T>` Type

When stream annotations are present, the lexer returns `LexResult<T>`:

```rust
pub struct LexResult<T> {
    /// Main token stream (consumed by the parser). Includes Eof.
    pub tokens: Vec<(T, Range)>,
    /// Auxiliary streams, keyed by stream name.
    pub streams: HashMap<String, Vec<(T, Range)>>,
}
```

Each auxiliary stream preserves source order with full positional information
(byte offset, line, column, optional file ID). Tools correlate auxiliary
tokens with main-stream tokens by position:

```rust
let result = lex_with_streams(source)?;
let ast = parse(&result.tokens)?;
if let Some(docs) = result.streams.get("docs") {
    for (token, range) in docs {
        attach_doc_comment(token, range, &ast);
    }
}
```

When no `-> stream` annotations exist, `streams` is empty -- zero allocation.

---

## 4. Stream Routing Architecture

Routing is resolved entirely at compile time. Each DFA accept state is
assigned a stream ID during codegen; at runtime, routing is a single table
lookup per token.

### 4.1 Compile-Time Pipeline

1. Collect unique stream names from `-> stream` annotations (excluding `main`).
2. Assign sequential `u8` IDs: main = 0, first named = 1, second = 2, etc.
3. For each mode's DFA, emit `stream_id_{mode}(state) -> u8` mapping accept
   states to stream IDs.

### 4.2 Generated Tables

```rust
// Stream name table (index 0 is always "main")
static STREAM_NAMES: [&str; 4] = ["main", "comments", "whitespace", "docs"];

// Stream ID constants
const STREAM_COMMENTS:   u8 = 1;
const STREAM_WHITESPACE: u8 = 2;
const STREAM_DOCS:       u8 = 3;

// Per-mode stream routing (default mode shown)
fn stream_id_default(state: u32) -> u8 {
    match state {
        5  => 1,   // LineComment  -> comments
        8  => 1,   // BlockComment -> comments
        3  => 2,   // Whitespace   -> whitespace
        11 => 3,   // DocComment   -> docs
        _  => 0,   // main
    }
}
```

### 4.3 Runtime Routing

After the DFA walk produces an accept state, routing is O(1):

```
                      accept state
                           |
                           v
                 stream_id_{mode}(state)
                           |
                  +--------+--------+
                  |                 |
                  v                 v
            id == 0            id > 0
                  |                 |
                  v                 v
          tokens.push(t,r)  streams[name].push(t,r)
```

The match compiles to a jump table or comparison chain bounded by the number
of distinct token kinds in one mode (typically < 50), making it constant time.

---

## 5. Backward Compatibility

When no `-> stream` annotations exist, PraTTaIL generates the standard
single-stream lexer with no HashMap, no routing logic, and no STREAM_NAMES
table. The generated code is byte-identical to the non-stream path:

```rust
pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { ... }
pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>)
    -> Result<Vec<(Token<'a>, Range)>, String> { ... }
```

When at least one annotation is present, `lex_with_streams` and
`lex_streams_with_file_id` are emitted alongside the standard functions.
The standard functions continue to work but discard auxiliary tokens.

---

## 6. Auto-Triggering Modal Codegen

Stream annotations and mode blocks are orthogonal features but share codegen
infrastructure. When `-> stream` annotations appear without explicit `mode`
blocks, PraTTaIL automatically triggers the modal codegen path with a single
implicit default mode. This is because `stream_id_{mode}` tables are keyed by
mode and the stream-aware lex loop uses the same mode-dispatched structure.

```
tokens {
    Ident = /[a-z]+/
    WS    = /\s+/ -> whitespace   // triggers modal codegen
}
```

is equivalent to:

```
tokens {
    mode default {
        Ident = /[a-z]+/
        WS    = /\s+/ -> whitespace
    }
}
```

The single-mode case is the degenerate instance where the mode dispatch match
has one arm.

---

## 7. Token Routing Flow Diagram

```
                           Input bytes
                               |
                               v
                     +-------------------+
                     | mode = stack.top  |
                     +-------------------+
                               |
                               v
                     +-------------------+
                     | DFA walk (mode)   |
                     | longest match     |
                     +-------------------+
                               |
                        accept state s
                               |
              +-------+--------+--------+-------+
              |       |                 |       |
              v       v                 v       v
        accept_{m}  push/pop      stream_id_{m}
         (token)    transitions    (routing)
              |       |                 |
              |       v                 |
              |  mode_stack update      |
              |                         |
              +-----------+-------------+
                          |
                 +--------+--------+
                 |                 |
                 v                 v
           stream == 0       stream > 0
                 |                 |
                 v                 v
         tokens.push(t,r)  streams[name].push(t,r)
```

---

## 8. Performance

**Time:** O(n) in input length, identical to single-stream lexing. Each byte
is examined once during the DFA walk. Stream routing adds one table lookup per
*token* (not per byte). Since tokens average several bytes, the amortized
overhead is negligible.

**Space:** The `streams` HashMap allocates only when tokens route to auxiliary
streams. Total auxiliary space is O(t) where t is the count of routed tokens.
When no streams are used, the HashMap is empty (zero heap allocation).

**Compile-time:** One additional `stream_id_{mode}` match function per mode,
O(|F|) in accept states -- typically trivial.

**Zero-cost guarantee:** Grammars without `-> stream` produce byte-identical
code to the non-stream path. No runtime branches, no dead code.

---

## 9. Examples

### 9.1 Comment Preservation for Formatting

```
tokens {
    Let   = 'let'
    Eq    = '='
    Semi  = ';'
    Ident = /[a-zA-Z_]\w*/
    Int   = /[0-9]+/
    LineComment  = /\/\/[^\n]*/    -> comments
    BlockComment = /\/\*[^*]*\*+([^/*][^*]*\*+)*\//  -> comments
    Whitespace   = /[ \t\n\r]+/    -> whitespace
}
```

The formatter reads `result.streams["whitespace"]` to decide where to insert
or remove blank lines between declarations.

### 9.2 Doc-Comment Extraction

```
tokens {
    DocComment  = /\/\/\/[^\n]*/  -> docs
    LineComment = /\/\/[^\n]*/    -> comments
}
```

A doc generator iterates `result.streams["docs"]`, associates each comment's
Range with the nearest following AST declaration, and strips the `///` prefix.

### 9.3 Layout-Sensitive Formatting

```
tokens {
    Indent  = /\n[ \t]+/ -> layout
    Newline = /\n/        -> layout
}
```

A layout post-pass reads `result.streams["layout"]` to reconstruct indentation
levels without whitespace-handling grammar rules.

---

## 10. Generated Code Structure

### 10.1 Entry Points

```rust
/// Lex with stream routing.
pub fn lex_with_streams<'a>(input: &'a str)
    -> Result<mettail_prattail::LexResult<Token<'a>>, String>
{
    lex_streams_with_file_id(input, None)
}

/// Lex with stream routing and file ID.
pub fn lex_streams_with_file_id<'a>(input: &'a str, file_id: Option<u32>)
    -> Result<mettail_prattail::LexResult<Token<'a>>, String>
{
    let bytes = input.as_bytes();
    let mut tokens = Vec::with_capacity(input.len() / 2);
    let mut streams: HashMap<String, Vec<(Token, Range)>> = HashMap::new();
    let mut mode_stack: Vec<u8> = vec![0u8];
    // ... standard modal lex loop (see modal-lexing.md) ...
    // Key addition: after resolving token and mode transitions,
    // route by stream_id:
    //   let sid = stream_id_{mode}(accept_state);
    //   if sid == 0 { tokens.push(...); }
    //   else { streams.entry(STREAM_NAMES[sid]).or_default().push(...); }
    Ok(mettail_prattail::LexResult { tokens, streams })
}
```

### 10.2 Stream ID Function

The `stream_id_{mode}` function is the only codegen addition beyond the
standard modal tables. Its presence signals that multi-stream routing is
active. When absent (no `-> stream` annotations), the entire stream routing
path is elided from generated code.
