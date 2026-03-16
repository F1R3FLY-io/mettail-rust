

### Goal

- Extend the `language! { ... }` DSL with a new optional `literals { ... }` section where the user defines **both** a **regex-like pattern** (what the lexer recognizes as a literal token) and **eval** code (how to convert the matched text to a value). Each subsection is named after the type (e.g. `Int`, `Float`, `Bool`, `Str`) and contains `pattern: <string>` and `eval: ![ ... ]`. The eval expression’s return type must be a standard `Result<T, E>` for an appropriate value type `T`.
- The **lexer** takes these patterns and compiles them (regex subset to NFA/DFA) so it can recognize literal tokens with **any shape the user specifies** — including prefix (e.g. `0x`, `0o`, `0b`) or **suffix** (e.g. `xh` for hex). The Rust eval code must be written to match: if the pattern matches `FFh`, the eval receives `"FFh"` and must strip the suffix and parse accordingly.
- **Section order**: the `types` section must **precede** the `literals` section so that literal subsections (Int, Float, etc.) can be validated against declared type names.
- **No panics; use `Result`**: The Rust code that converts a literal to its internal representation should **not panic**. Instead, it returns `Ok(value)` on success and `Err(error)` on failure. When a DFA state has multiple candidate literal token kinds (e.g. both `Int` and `Float` recognize the same digit prefix), the generated lexer:
  - Tries candidates in **priority order** (highest-priority token kind first).
  - For each candidate, calls its eval and inspects the `Result`.
  - **First** eval that returns `Ok(value)` wins; remaining candidates are skipped.
  - If **all** candidates return `Err(_)`, the span is treated as a lexing error.
- **Partial literals**: If the `literals` section **omits** some types that have native types in `types` (e.g. the user defines only `Int` and `Float` in `literals` but also has `Bool` and `Str` in `types`), then those omitted types use **default** parsing: decimal integers `[0-9]+`, keywords `true`/`false` for Bool, standard float regex for Float, double-quoted string for Str, etc. So custom literals apply only to types that have a subsection in `literals`; all others keep the built-in behavior.

### Constraints from current implementation

- **Lexing is DFA-based** and currently hardcodes numeric tokens:
  - Integer fragment is `[0-9]+` (`build_integer_fragment`) and float is `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?` (`build_float_fragment`) in `[prattail/src/automata/nfa.rs](/home/serhi/Projects/mettail-rust/prattail/src/automata/nfa.rs)`.
- The lexer currently **parses numbers inside the lexer** (e.g., `text.parse::<i64>()`) in `[prattail/src/automata/codegen.rs](/home/serhi/Projects/mettail-rust/prattail/src/automata/codegen.rs)`.
  - This will break as soon as you allow prefixes like `0xFF` or digit separators.

### Proposed `literals { ... }` syntax (example)

Subsection names **match the type names** from `types { ... }` (e.g. `Int`, `Float`, `Bool`, `Str`). Each subsection has **fixed order**: first `pattern:` followed by a string literal (the regex) and `;`, then `eval:` followed by the Rust code in `![ ... ]`. So: `pattern: <string>; eval: ![ <expr> ]`. The eval expression must return a `Result<T, E>` where `T` is compatible with the underlying token type for that literal.

```rust
language! {
  name: Calculator,

  types {
    Proc
    ![i32] as Int
    ![f64] as Float
    ![bool] as Bool
    ![str] as Str
    // ...
  },

  literals {
    Int {
      // Hex (`0xFF`), octal (`0o77`), binary (`0b1010`), or decimal with `_` separators.
      pattern: r"[+-]?(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)";
      eval: ![ {
        // Example using i64 as the token’s storage type; see “Int eval returning i64 vs native i32” below.
        let s = text.replace('_', "");
        let (sign, body) = match s.strip_prefix('-') {
          Some(rest) => (-1_i64, rest),
          None => (1_i64, s.as_str()),
        };
        let (radix, digits) = if let Some(h) = body.strip_prefix("0x") { (16, h) }
          else if let Some(o) = body.strip_prefix("0o") { (8, o) }
          else if let Some(b) = body.strip_prefix("0b") { (2, b) }
          else { (10, body) };
        i64::from_str_radix(digits, radix).map(|n| sign * n)
      } ]
    }

    Float {
      // Require decimal point or exponent so bare integers like "3" are Int, not Float.
      pattern: r"[0-9](_?[0-9])*(\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?|[eE][+-]?[0-9](_?[0-9])*)|\.[0-9](_?[0-9])*([eE][+-]?[0-9](_?[0-9])*)?";
      eval: ![ {
        text.replace('_', "").parse::<f64>()
      } ]
    }

    Bool {
      pattern: r"yes|no";
      eval: ![ {
        match text {
          "yes" => Ok(true),
          "no" => Ok(false),
          _ => Err(()),
        }
      } ]
    }

    Str {
      // Single-quoted strings with backslash escapes (e.g. 'it\\'s fine').
      pattern: r"'([^'\\]|\\.)*'";
      eval: ![ {
        if text.len() < 2 {
          Err(())
        } else {
          let inner = &text[1..text.len()-1];
          let unescaped = inner
            .replace("\\'", "'")
            .replace("\\\\", "\\");
          Ok(unescaped.to_string())
        }
      } ]
    }
  },

  terms { ... }
}
```

(Generated code arranges that `text` is in scope when the eval runs for a matched token.) **Boolean literals** can use custom keywords (e.g. `yes`/`no`). **String literals** can use a different delimiter: e.g. single quotes `'...'` instead of double quotes `"..."`, with a pattern that matches `'...'` (and allows escaped `\'` inside) and eval that strips the quotes and unescapes; invalid or empty → return `String::new()`. To use **suffix** hex (e.g. `FFh`), the pattern would include an alternative like `[0-9A-Fa-f]+h` and the eval would strip the suffix and parse as hex.

### Design notes (why this shape)

- **Patterns drive fast lexing; eval refines candidates**: Each literal type has a `pattern` (regex-like string) that is compiled into the global NFA/DFA. The DFA does a single **O(n)** pass over the input, tracking the longest match and which token kinds can recognize each span. Only for DFA-accepted spans, and only for those candidate token kinds, does the lexer call the corresponding `eval` and inspect its `Result`. This keeps arbitrary user code off the hot path and prevents lexing from devolving into “try every eval at every position”.
- **Patterns also resolve ambiguities**: The DFA plus token priorities encode maximal-munch and precedence rules (e.g. Integer vs Float, keyword vs Ident). Patterns decide *where* tokens can end and *which kinds* are even in play; eval only says “among these candidates, which ones can actually interpret this text?”. Removing patterns would push that disambiguation into ad hoc eval code and make behavior harder to reason about.
- **Same convention**: Rust snippets in `![ ... ]` as in terms. Subsection names = type names. Collection delimiters stay in `types { ... }`.
- **Result-based error signalling**: Eval should not panic; it returns `Ok(value)` on success or `Err(error)` on failure. Failure means “this particular evaluator cannot interpret this text”. The lexer then tries the next candidate literal token kind (if any) for the same span.
- **Eval value type vs native type**: The eval expression’s success value type `T` must be compatible with the token representation the lexer uses for that literal (e.g. `i64` for `Token::Integer`, `f64` for `Token::Float`, `bool` for `Token::Boolean`, `String` for `Token::StringLit`). The **native type** declared in `types { ... }` (e.g. `![i32] as Int`) can differ; the trampoline code is responsible for converting from the token’s storage type to the native type (often via a cast).
- **Pattern string**: Use **raw strings** `r"..."` for the pattern so backslashes (e.g. in regex `\\.`) are written once; non-raw strings require extra escaping.

### Regex subset (literal patterns)

The pattern string is compiled directly to an NFA. The implemented feature set is:

- **Literals** (single chars)
- **Character classes** `[...]` and ranges (e.g. `[0-9]`, `[a-fA-F]`)
- **Alternation** `|`
- **Grouping** with plain `(...)`
- **Quantifiers** `?`, `*`, `+`

PraTTaIL’s regex compiler currently does **not** support extended mode `(?x)` or non-capturing groups `(?:...)`. Patterns in language definitions therefore use plain grouping and avoid `(?x)`/`(?:...)`. Semantics are **ASCII-only** (no Unicode property escapes).

### Literal vs identifier priority

When input could match both a custom literal (e.g. `yes`) and an **identifier**, the lexer resolves ambiguity using token priorities and DFA weights. Literal tokens (Integer, Float, BooleanLit, StringLit) are given higher priority than `Ident` so that, when both can match the same span, the literal token is preferred. Combined with the “first successful eval wins” rule, this ensures that inputs like `yes` are consistently interpreted as `Bool` when a Bool pattern `yes|no` is present.

### Implementation approach (high-level)

1. **Extend macro AST to parse `literals { ... }`**
  - `macros/src/ast/language.rs` holds an optional `literals: Option<LiteralBlock>` on `LanguageDef`. `types` is parsed before `literals` so subsection names can be validated against declared types.
2. **Carry literal configs through the bridge**
  - The bridge from `language!` to PraTTaIL converts the `literals` block into a `LiteralPatterns` plus a `literal_eval: HashMap<String, String>` on `LanguageSpec`, where each entry is the source text of the eval expression for a given type.
3. **Compile user patterns to NFA**
  - In `prattail/src/automata/regex.rs` and `nfa.rs`, the literal patterns are compiled into NFA fragments and used instead of the built-in integer/float/string fragments when custom literals are present.
4. **Token payload and eval hook**
  - The lexer emits `Token::Integer(i64)`, `Token::Float(f64)`, `Token::Boolean(bool)`, `Token::StringLit(Cow<'a, str>)`. For literals with custom eval, the generated lexer code calls the user’s eval expression and interprets the resulting `Result<T, E>` as success/failure.
5. **Parser integration**
  - In `prattail/src/trampoline.rs`, prefix handlers for `NumLit` and similar nodes convert from the token’s storage type to the native type declared in `types { ... }` (e.g. casting `i64` to `i32` for `Int`).
6. **Tests**
  - Integration tests in `prattail/src/tests/integration_tests.rs` exercise custom literal evals and verify backward compatibility when `literal_eval` is empty. Language-level tests (e.g. for Calculator and RhoCalc) can validate that hex/octal/binary, underscore separators, custom Bool keywords, and single-quoted strings behave as expected.

### Backward compatibility

- If `literals {}` is omitted entirely, behavior stays exactly as before (decimal `[0-9]+` integers, current float regex, `true`/`false`, double-quoted strings).
- If `literals {}` is present but **omits** some types, those types still use the **default** literal parsing (decimals for Int, `true`/`false` for Bool, standard float for Float, double-quoted for Str, etc.). Only types listed in `literals` use custom pattern and eval.
- `types`-level collection delimiters stay as they are; no migration needed.

### Eval storage types vs native numeric types

In the Calculator example, the native `Int` type is declared as:

```rust
types {
  Proc
  ![i32] as Int
  // ...
}
```

while the `Int` literal eval is written in terms of `i64`, and the lexer token for integers is `Token::Integer(i64)`. This is intentional:

- The **lexer/eval layer** uses `i64` as the storage type for integer tokens (`Token::Integer(i64)`), because it is large enough for typical use cases and simplifies code generation.
- The **trampoline layer** (see `prattail/src/trampoline.rs`) converts that `i64` token value to the native `Int` type. For an `Int` with native type `i32`, the generated code looks like:

```rust
// prattail/src/trampoline.rs (conceptual snippet)
Token::Integer(v) => {
    let val = *v as i32;
    // build Int::NumLit(val) and advance
}
```

So if `Int.eval` returns `Result<i64, E>`:

- On success, the lexer produces `Token::Integer(i64_value)`.
- When building the AST, the trampoline casts `i64` to `i32` and constructs `Int::NumLit(i32_value)`.
- If the `i64` value is within the range representable by `i32`, this cast is a straightforward narrowing conversion.
- If the `i64` value is **outside** the `i32` range, the `as i32` cast performs a truncating/wrapping conversion according to Rust’s rules (higher bits discarded modulo `2^32`). There is no automatic error; the result is a wrapped `i32`.

If instead you tried to have `Int.eval` return `Result<i32, E>` while the lexer token is still defined as `Token::Integer(i64)`, the generated code in `write_token_constructor` would not type-check: it expects an `Ok(v)` where `v: i64`. This is why the design separates:

- The token’s **storage type** (chosen by PraTTaIL, e.g. `i64`), and
- The language’s **native type** declared in `types { ... }` (e.g. `i32`),

with the trampoline responsible for bridging the two.

The same pattern applies to other numeric types:

- Float literals are stored as `Token::Float(f64)` in the lexer/eval layer, even if a language chose a native `Float` type of `f32`. In that case the trampoline would cast via `as f32` when constructing the `Float` AST node.
- Other integer widths (e.g. `u64` vs `u32`, or `i64` vs `i16`) follow the same rule: the eval returns a `Result<storage_type, E>` (`u64`, `i64`, etc.), the token stores that type, and the trampoline narrows or widens to the native type using Rust’s `as` casts.

Because these conversions use standard Rust `as` semantics:

- **In-range** values convert exactly.
- **Out-of-range** values are truncated/wrapped as defined by Rust (e.g. modulo `2^N` for integer casts), rather than causing runtime errors.

When writing eval code, it is therefore best to:

- Choose a storage type (`i64`, `u64`, `f64`, etc.) that is at least as wide as the range of literals you care about, and
- Be aware that, if the native type is narrower (e.g. `i32`, `f32`), the trampoline will apply a potentially narrowing conversion when building the AST.