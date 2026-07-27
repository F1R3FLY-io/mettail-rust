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

## 4.4 A routed token is TRIVIA on every parse path (task #18, 2026-07-25)

Routing decides *where a token goes*; it does not change *how the scanner picks
it*. A routed token competes for the position under the SAME maximal-munch rule
as every other token. When it wins, its span is **consumed** and it is delivered
to its channel instead of to the parse stream — structurally identical to the
inter-token whitespace skip that already sits at the same place in every scanner.

This applies uniformly to every entry point, not just `lex_with_streams`:

| Entry | Routed token |
|---|---|
| `lex` / `lex_with_file_id` | consumed; not appended to `tokens` |
| `lex_dag` / `lex_dag_lazy` (the parse path) | consumed; produces **no DAG edge** |
| `lex_weighted`, `lex_lattice`, `lex_stream` | consumed; produces no token/entry |
| `lex_with_streams` / `lex_streams_with_file_id` | consumed **and retained** in `streams[name]` with its `Range` |

Two rules implement this in `expand_lex_node_impl` and the `*_core_modal`
scanners (`prattail/src/runtime_types.rs`):

1. Accepts occur at strictly increasing end offsets, so the maximal-munch accept
   at a position is unique. If `stream_id` routes it off `DEFAULT`, the scan
   advances past its span and restarts — a DAG node's `byte_start` moves past
   the trivia exactly as it moves past a leading whitespace run.
2. Otherwise, routed accepts at *shorter* lengths are dropped: a routed token can
   never be a parser token, so it must never become a DAG edge.

**Consequence — routing cannot introduce ambiguity.** Trivia only ever REMOVES a
span from the scan; it never contributes an alternative. So the lex DAG over a
source containing trivia is the DAG of that source with the trivia bytes elided,
and the parse forest, the elected term, and the parse COUNT are unchanged. This
is what makes it safe to route `//…` in a grammar that also has a `/` division
terminal: maximal munch — not a new disambiguation — settles the two.

**Compile-time soundness gate.** `crate::lexer::check_channel_soundness` rejects
any DFA state whose co-accepting kinds disagree on their channel, since one span
cannot be both trivia and a parse token. It is the channel analogue of the DUI
check and fails closed rather than silently picking one.

**The channel boundary.** Auxiliary channels are compile-time / tooling-facing
apparatus. Only `main`/`DEFAULT` feeds the parser AND any running program; there
is no path by which a routed token reaches either. Backends read channels through
the ANTLR4-parity accessors on `LexResult` — `tokens_on_channel`,
`hidden_tokens_to_left`, `hidden_tokens_to_right`, `channels` (§3) — which are
generic over the channel name: no registry, no privileged name.

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

The per-mode `stream_id_{mode}` tables themselves ARE emitted for every modal
grammar, so the `m_stream_id` dispatch shim has a uniform signature; with no
annotation each table degenerates to `match state { _ => 0u8 }`, a constant the
optimizer folds away. What remains gated on the presence of an annotation is
everything that exists only to SERVE a channel: the `STREAM_{NAME}` constants,
the `STREAM_NAMES` array, and the `lex_with_streams` /
`lex_streams_with_file_id` retention entries.

When at least one annotation is present, `lex_with_streams` and
`lex_streams_with_file_id` are emitted alongside the standard functions. The
standard functions continue to work; per §4.4 they consume a routed token's span
and deliver nothing for it.

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

`lex_streams_with_file_id` runs its own mode stack, so — like
`compute_mode_map` on the parse path — it verifies the stack has returned to
`[0]` at end of input and reports `unterminated region: …` otherwise. Without
that check a source the parser rejects (an opener whose closer never arrived)
would silently succeed here and hand tooling a truncated token stream.

### 10.2 Stream ID Function

The `stream_id_{mode}` functions map each accept state to its channel index and
are emitted for every modal grammar (§5): with no `-> stream` annotation each
reduces to the constant `0`, which is what lets the `m_stream_id` shim and the
`*_core_modal` trivia rule share one signature across all grammars. A non-trivial
arm is what signals that multi-stream routing is active for a state; the
`STREAM_NAMES` table, the `STREAM_{NAME}` constants, and the `lex_with_streams`
retention entries are emitted only when at least one such arm exists.

---

## 11. Worked Instance — Rholang comments (task #18, 2026-07-25)

Rholang's comments were originally removed by a **pre-parse string strip** in the
`rholang` interpreter binary — a hand-rolled `{Code, Str, Guest}` scanner that
deleted the bytes before the lexer ran. That was lossy: columns shifted, the text
was unrecoverable, and no consumer could observe a comment. It is now expressed
in the mechanism this document describes (`languages/src/rholang.rs`):

```
tokens {
    LineComment  = "//[^\n]*"                   -> COMMENTS ;
    BlockComment = "/\\*([^*]|\\*+[^*/])*\\*+/" -> COMMENTS ;
    …
}
```

Each hand-rolled state of the strip maps onto a mechanism the lexer already had,
which is why none of it survives:

| Strip state | Replaced by |
|---|---|
| `State::Str` — a marker inside `"…"` is string bytes | `StringLit` is one maximal-munch span, so an interior marker is never at a token-start position |
| `State::Guest` — a marker inside `` `…` `` is guest text | the FLT guest modes are RAW and declare their own tokens; the comment tokens exist only in the default mode |
| `//` beats `/` (the `Div` terminal) | maximal munch — the same rule that separates every other token pair |

One deliberate behaviour change: an unterminated `/*` used to be swallowed
silently to EOF. `BlockComment` requires its closing marker, so the maximal munch
at `/` falls back to `Div`, the tail lexes as ordinary tokens, and the program
now fails closed at the parse instead of running with a silently truncated tail.
