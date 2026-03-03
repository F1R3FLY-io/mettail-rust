# Lexer Errors

PraTTaIL's DFA-based lexer produces errors when it encounters bytes that don't
match any token pattern. Lexer errors are wrapped in `ParseError::LexError` and
carry the exact source position.

## Error Format

### ASCII Character

```
1:5: unexpected character '@'
```

Triggered when a valid ASCII character (byte 0x00–0x7F) doesn't match any DFA
transition. Common causes:

- Using an operator not defined in the grammar (e.g., `@`, `#`, `~`)
- Mistyped operator (e.g., `&` instead of `&&`)
- Special characters from copy-paste (smart quotes, em-dashes)

### Non-ASCII Byte

```
1:5: unexpected byte 0xE2
```

Triggered when a non-ASCII byte (0x80–0xFF) appears and the grammar only
accepts ASCII tokens. Common causes:

- Unicode characters pasted from external sources (e.g., `×` instead of `*`)
- UTF-8 encoded emoji or special symbols
- Invisible characters (zero-width spaces, BOM)

## Lexer Architecture

PraTTaIL generates a DFA (Deterministic Finite Automaton) lexer for each grammar:

1. **Character equivalence classes** — 256-byte lookup table mapping bytes to classes
2. **DFA transition table** — compressed via comb compression (bitmap + popcount)
3. **IS_ACCEPTING bitmap** — u128 bitmap (≤128 states) or bool array (>128)
4. **Token emission** — `accept_token(state, text)` maps accepting state to Token variant

The lexer loop (in `lex_core()`) performs maximal-munch: it tracks the last
accepting state and backtracks if the DFA enters a dead state (u32::MAX).

## Whitespace Handling

Whitespace characters (`' '`, `'\t'`, `'\n'`, `'\r'`) are skipped automatically
between tokens. They are never part of the DFA transition graph.

## Common Causes and Resolutions

| Symptom | Cause | Resolution |
|---------|-------|------------|
| `unexpected character '@'` | Operator not in grammar | Use a defined operator |
| `unexpected character '#'` | Comment syntax not supported | PraTTaIL grammars have no comments |
| `unexpected byte 0xC2` | Non-ASCII pasted text | Replace with ASCII equivalent |
| `unexpected character '\\'` | Backslash not in terminal set | Add `\\` as a terminal if needed |
| `unexpected character '"'` | No StringLiteral pattern | Add `native_type: String` or custom literal pattern |

## Custom Literal Patterns

The lexer's token patterns are configurable via `LiteralPatterns` in the
EBNF config file (`prattail/src/literal_patterns.ebnf`):

```ebnf
integer  = ["-"] digit { digit } ;
float    = ["-"] digit { digit } "." digit { digit } ;
string   = '"' { char - '"' } '"' ;
boolean  = "true" | "false" ;
```

If a literal pattern doesn't match, the grammar's DFA won't accept that token,
leading to a lexer error at runtime.

## Error Recovery

Lexer errors are **not recoverable** by `parse_recovering()` — since the lexer
runs before the parser, a lex error prevents token stream construction entirely.
The recovery parser returns `(None, vec![ParseError::from(lex_error)])`.

To handle potential lex errors gracefully:

```rust
match Int::parse_structured(input) {
    Ok(ast) => { /* use ast */ }
    Err(ParseError::LexError { message, position }) => {
        eprintln!("Lexer error at {}:{}: {}",
            position.line + 1, position.column + 1, message);
    }
    Err(e) => {
        eprintln!("Parse error: {}", e);
    }
}
```

## Weighted Lexing

When using `parse_structured_weighted()`, the lexer also emits per-token
tropical weights from the composed WFST. Lex errors in weighted mode produce
the same `ParseError::LexError` — weights are only available for successfully
lexed tokens.
