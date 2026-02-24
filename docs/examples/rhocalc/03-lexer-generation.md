# Lexer Generation

**Source files:** `prattail/src/automata/` (nfa.rs, subset.rs, minimize.rs,
partition.rs, codegen.rs), `prattail/src/lexer.rs`, `prattail/src/pipeline.rs`

The PraTTaIL lexer pipeline transforms the terminal set extracted from the
grammar into a direct-coded, zero-copy lexer function.  The pipeline is:

```
  Terminals   →   NFA          →   DFA           →   Minimized DFA   →   Rust Code
  -----------------------------------------------------------------------------------
  (strings)       Thompson's       Subset            Hopcroft            direct-coded
                  construction     construction                          match arms
```

## Terminal Extraction

**Entry point:** `lexer::extract_terminals()` in `prattail/src/lexer.rs`

PraTTaIL walks every `SyntaxItemSpec` in every rule and collects:

1. **Literal terminals** — every `Terminal(s)` yields the string `s`
   - RhoCalc examples: `"+"`, `"-"`, `"*"`, `"/"`, `"("`, `")"`, `"{"`, `"}"`,
     `"{}"`, `"!"`, `"?"`, `"."`, `","`, `"|"`, `"@"`, `"=="`, `"!="`, `">"`,
     `"<"`, `">="`, `"<="`, `"not"`, `"and"`, `"or"`, `"new"`, `"error"`,
     `"concat"`, `"len"`, `"int"`, `"float"`, `"bool"`, `"str"`

2. **Structural delimiters** — always included: `(`, `)`, `{`, `}`, `[`, `]`, `,`
   (these may already be covered by literal terminals)

3. **Native literal tokens** — derived from `CategorySpec::native_type`:
   - `i64` → `Token::Integer` (matches `[0-9]+`)
   - `f64` → `Token::Float` (matches `[0-9]+\.[0-9]+`)
   - `bool` → `Token::True`, `Token::False` (matches `true`, `false`)
   - `str` → `Token::StringLit` (matches `"..."`)

4. **Identifier pattern** — always included: `Token::Ident` (matches `[a-zA-Z_][a-zA-Z0-9_]*`)

5. **Dollar tokens** (if binders present) — `Token::Dollar` (`$cat`)
   and `Token::DoubleDollar` (`$$cat(`)

Each terminal is wrapped in a `TerminalPattern { text, kind, is_keyword }`.
Keywords are identifier-like terminals (e.g., `"not"`, `"new"`, `"error"`) that
must take priority over the generic `Ident` pattern.

## NFA Construction (Thompson's Algorithm)

**Source:** `prattail/src/automata/nfa.rs`

For each `TerminalPattern`, Thompson's construction builds an NFA fragment:

```
Example: terminal "+"

   ┌─────┐  '+'  ┌───────────┐
   │start│──────►│ accept    │
   └─────┘       │ kind=Plus │
                 └───────────┘
```

For multi-character terminals like `"new"`:

```
   ┌─────┐  'n'  ┌───┐  'e'  ┌───┐  'w'  ┌──────────┐
   │start│──────►│ 1 │──────►│ 2 │──────►│ accept   │
   └─────┘       └───┘       └───┘       │ kind=New │
                                         └──────────┘
```

For character classes like `Integer` (`[0-9]+`):

```
   ┌─────┐  ε   ┌───┐  [0-9]  ┌──────────┐
   │start│─────►│ 1 │────────►│  accept  │
   └─────┘      └───┘         │ kind=Int │
                  ▲           └────┬─────┘
                  │    [0-9]       │
                  └────────────────┘
```

All fragments are unioned under a single start state via epsilon transitions:

```
   ┌───────────┐  ε   ┌─── fragment for "+" ──► accept(Plus)
   │           ├──────┘
   │ NFA start │  ε   ┌─── fragment for "*" ──► accept(Star)
   │           ├──────┘
   └─────┬─────┘  ε   ┌─── fragment for [0-9]+ ──► accept(Integer)
         └────────────┘
                  ⋮
```

Each accepting state carries a `TropicalWeight` derived from `TokenKind::priority()`.
Keywords and fixed terminals get priority 10; identifiers get priority 1.
During subset construction, when an NFA state set contains multiple accepting
states, the one with the *lowest* tropical weight (highest priority) wins.
This implements maximal-munch with keyword priority.

## Equivalence Class Partition

**Source:** `prattail/src/automata/partition.rs`

Before subset construction, the byte alphabet (0..255) is partitioned into
*equivalence classes* — groups of bytes that behave identically across all NFA
transitions.  For RhoCalc:

| Class | Bytes                | Reason                     |
|-------|----------------------|----------------------------|
| 0     | `+`                  | unique terminal            |
| 1     | `-`                  | unique terminal            |
| 2     | `*`                  | unique terminal            |
| 3     | `/`                  | unique terminal            |
| 4     | `(`                  | delimiter                  |
| 5     | `)`                  | delimiter                  |
| ...   | ...                  | ...                        |
| k     | `a-z` minus keywords | identifier body characters |
| k+1   | `0-9`                | digit characters           |
| k+2   | `_`                  | identifier character       |
| k+3   | all other bytes      | dead transitions           |

This reduces the DFA transition table from 256 columns to ~20-30 columns
(one per equivalence class), dramatically shrinking the minimized DFA.

## Subset Construction (NFA → DFA)

**Source:** `prattail/src/automata/subset.rs`

The powerset construction converts the NFA to a DFA:

1. Start with the epsilon closure of the NFA start state
2. For each equivalence class, compute the set of NFA states reachable from the
   current DFA state via that class
3. Take the epsilon closure of the result
4. If this state set is new, create a new DFA state; otherwise, reuse the
   existing one
5. Repeat until no new DFA states are created

Key optimization: `epsilon_closure_reuse()` maintains a visited bitset and
resets it in O(closure_size) rather than O(num_states).

DFA accepting states inherit the highest-priority token kind from their
constituent NFA accepting states (via tropical weight comparison).

## Hopcroft Minimization (DFA → Minimal DFA)

**Source:** `prattail/src/automata/minimize.rs`

Hopcroft's algorithm reduces the DFA to its minimal equivalent:

1. Initial partition: accepting states (grouped by token kind) vs non-accepting
2. Refine: split partitions where states disagree on which partition a transition
   leads to
3. Repeat until no more splits are possible
4. Each partition becomes a single state in the minimal DFA

For RhoCalc, a typical DFA of ~40-60 states minimizes to ~15-25 states.

After minimization, BFS canonical reordering ensures deterministic state
numbering (start state = 0).

## Code Generation

**Source:** `prattail/src/automata/codegen.rs`

The minimized DFA is emitted as a Rust `next_token()` function.  The generated
code is a direct-coded lexer — each DFA state becomes a labeled block with a
`match` on the current input byte's equivalence class:

```rust
// Generated Token enum (simplified)
#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    Eof,
    Ident(&'a str),
    Integer(&'a str),
    Float(&'a str),
    Boolean(bool),
    StringLit(&'a str),
    Plus,           // "+"
    Minus,          // "-"
    Star,           // "*"
    Slash,          // "/"
    LParen,         // "("
    RParen,         // ")"
    LBrace,         // "{"
    RBrace,         // "}"
    Braces,         // "{}"
    Bang,           // "!"
    Question,       // "?"
    Dot,            // "."
    Comma,          // ","
    Pipe,           // "|"
    At,             // "@"
    EqEq,           // "=="
    BangEq,         // "!="
    // ... (Gt, Lt, GtEq, LtEq, Not, And, Or, New, Error, ...)
}
```

### Zero-Copy Design

`Token<'a>` borrows from the input string — no allocations during lexing.
`Ident(&'a str)`, `Integer(&'a str)`, `Float(&'a str)`, and `StringLit(&'a str)`
all point into the original source slice.

### The `next_token()` Function

The generated `next_token()` function:

1. Skips whitespace
2. Checks for special patterns (string literals, comments)
3. Runs the DFA from the current position, advancing byte by byte
4. On each accepting state, records the token kind and position (longest match)
5. Returns the token and advances the position cursor

For a single-character terminal like `+`:

```rust
'+' => {
    *pos += 1;
    Token::Plus
}
```

For an identifier (which might be a keyword):

```rust
c if c.is_ascii_alphabetic() || c == '_' => {
    let start = *pos;
    while *pos < bytes.len()
        && (bytes[*pos].is_ascii_alphanumeric() || bytes[*pos] == b'_') {
        *pos += 1;
    }
    let word = &input[start..*pos];
    match word {
        "not" => Token::Not,
        "and" => Token::And,
        "or" => Token::Or,
        "new" => Token::New,
        "error" => Token::Error,
        "true" => Token::Boolean(true),
        "false" => Token::Boolean(false),
        // ... more keywords
        _ => Token::Ident(word),
    }
}
```

### Comb Compression (Optional)

When the number of equivalence classes is ≤ 32, the code generator can use
*comb compression* — a compact bitmap representation where a `u32` bitmap and
popcount replace sparse match tables.  This reduces code size for grammars with
many similar-length keywords.

## Lexing a RhoCalc Expression

Tracing `3 + 4` through the generated lexer:

```
Input:   "3 + 4"
          ^

Step 1:  byte '3', class = digit
         DFA enters integer accepting state
         Continue: no more digits
         Emit: Token::Integer("3"), pos = 1

Step 2:  byte ' ', skip whitespace, pos = 2

Step 3:  byte '+', class = plus
         DFA enters Plus accepting state
         Emit: Token::Plus, pos = 3

Step 4:  byte ' ', skip whitespace, pos = 4

Step 5:  byte '4', class = digit
         DFA enters integer accepting state
         Emit: Token::Integer("4"), pos = 5

Step 6:  pos = len, emit Token::Eof
```

Result: `[Integer("3"), Plus, Integer("4"), Eof]`

For the more complex `{ @({}) ! ({}) | *(@({})) }`:

```
Tokens: [LBrace, At, LParen, Braces, RParen, Bang, LParen, Braces, RParen,
         Pipe, Star, LParen, At, LParen, Braces, RParen, RParen, RBrace]
```

Note that `{}` is lexed as a single `Token::Braces` token (not `LBrace` + `RBrace`)
because `"{}"` is a declared terminal in the grammar.

---

**Next:** [04-parser-generation.md](04-parser-generation.md) — how the token
stream is parsed into an AST.
