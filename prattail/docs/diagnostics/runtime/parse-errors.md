# Runtime Parse Errors

PraTTaIL parsers produce structured `ParseError` values (defined in
`prattail/src/runtime_types.rs`) with source positions, human-readable
token descriptions, and optional contextual hints.

## ParseError Variants

### UnexpectedToken

```
1:5: expected an Int expression (one of: integer literal, identifier, `+`), found `!`
  = hint: this token cannot start a Int expression
```

**Fields:**
- `expected: Cow<'static, str>` — FIRST-set-based description of what was expected
- `found: String` — friendly description of the token that was found (via `format_token_friendly()`)
- `range: Range` — source position (start/end with line, column, byte offset)
- `hint: Option<Cow<'static, str>>` — optional contextual fix suggestion

**When it triggers:**
- Prefix handler: token at current position doesn't match any prefix rule's dispatch token
- Infix handler: token doesn't match any infix operator
- `expect_token()`: expected a specific terminal but found something else
- `expect_ident()`: expected an identifier but found a keyword or operator

**Resolution:**
- Check that the input matches the grammar's syntax
- The `expected` message lists all valid alternatives
- If a token from another category appears, a cast rule hint may be shown

### UnexpectedEof

```
1:4: unexpected end of input, expected an Int expression (one of: integer literal, identifier)
  = hint: this token cannot start a Int expression
```

**Fields:**
- `expected: Cow<'static, str>` — what was expected
- `range: Range` — position at end of input
- `hint: Option<Cow<'static, str>>` — optional hint

**When it triggers:**
- Parser reaches end of token stream while expecting more input
- Common after an infix operator: `3 +` (missing right operand)
- Inside a delimited group: `(3 +` (missing operand and closing paren)

**Resolution:**
- Complete the expression — add the missing operand or closing delimiter
- The `expected` message indicates what the parser needs next

### LexError

```
1:3: unexpected character '@'
```

**Fields:**
- `message: String` — error description
- `position: Position` — exact source position of the bad character

**When it triggers:**
- DFA lexer encounters a byte that doesn't match any transition from the current state
- ASCII characters show as `unexpected character 'X'`
- Non-ASCII bytes show as `unexpected byte 0xXX`

**Resolution:**
- Remove or replace the invalid character
- Check that the grammar includes the intended operator/delimiter in its terminal set

### TrailingTokens

```
1:7: unexpected integer `5` after parsing
  = hint: the parser finished but input remains; check for missing operators or extra tokens
```

**Fields:**
- `found: String` — friendly description of the leftover token
- `range: Range` — position of the first unconsumed token
- `hint: Option<Cow<'static, str>>` — contextual suggestion

**When it triggers:**
- Parser successfully produces a complete AST but tokens remain in the stream
- The EOF check in `Cat::parse_structured()` detects unconsumed non-EOF tokens
- Common cause: missing operator between terms (`3 4` instead of `3 + 4`)

**Resolution:**
- Add the missing operator between adjacent terms
- Remove extraneous tokens
- If the input contains multiple expressions, parse them separately

### RecoveryApplied

```
1:3: expected `)`, found `]` (recovered: substitute `)` for `]`)
```

**Fields:**
- `original_error: Box<ParseError>` — the underlying error that was recovered from
- `repair_description: String` — human-readable description of the repair action
- `range: Range` — position where recovery was applied

**When it triggers:**
- Only via `Cat::parse_recovering()` — the error recovery path
- Recovery actions include: skip tokens, delete token, swap adjacent tokens,
  substitute one token for another, insert missing token

**Resolution:**
- Apply the suggested fix to the source code
- The `repair_description` explains exactly what the parser did to continue

## Source Context Display

The REPL renders parse errors with rich context using ANSI colors and
Unicode box-drawing characters:

```
error: unexpected integer `5` after parsing
 --> 1:7
  │
1 │ 3 + 4 5
  │       ^
  │
  = hint: the parser finished but input remains; check for missing operators or extra tokens
```

Color scheme:
- `error:` — red bold
- `-->` location arrow — blue bold
- Line numbers and `│` gutter — blue bold
- `^` carets — red bold
- `= hint:` — green

## Programmatic Access

```rust
// String error (convenience)
let result = Int::parse("3 ! 4");
assert!(result.is_err());

// Structured error (programmatic)
let result = Int::parse_structured("3 ! 4");
if let Err(e) = result {
    let range = e.range();           // Source position
    let message = e.to_string();     // Human-readable
    eprintln!("{}", message);
}

// With source context
let result = Int::parse_with_source("3 ! 4");
// Includes source snippet with caret

// Error recovery (multiple errors)
let (ast, errors) = Int::parse_recovering("3 ! 4");
for e in &errors {
    eprintln!("{}", e);
}
```
