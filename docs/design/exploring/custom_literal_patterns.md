<!--
---
name: Custom numeric literal patterns
overview: Add an optional `literals { ... }` block so users define Int/Float literal syntax via a regex-like pattern (what the lexer matches) and Rust parse code (how to convert matched text to a value). Patterns can be prefix or suffix (e.g. 0x or xh); the Rust code must align. Collection delimiters stay in `types { ... }`.
todos:
  - id: ast-literals-block
    content: "Add `literals { Int { pattern: r\\\"...\\\", eval: ![ ... ] } Float { ... } }` (pattern + eval per type) parsing to `LanguageDef` in `macros/src/ast/language.rs`."
    status: pending
  - id: bridge-literal-config
    content: Propagate literal parse code through prattail_bridge into parser/lexer pipeline.
    status: pending
  - id: regex-to-nfa
    content: Compile user-provided literal patterns (regex subset) to NFA fragments; lexer uses these to recognize Int/Float tokens (prefix or suffix); emit token text for parser to pass to user parse code.
    status: pending
  - id: token-and-parse-hook
    content: Lexer emits numeric token as text or value; trampoline/parser uses user eval for custom literals.
    status: pending
  - id: tests
    content: Add tests for Int (prefix/suffix, hex/octal/binary, underscore), Float (underscore, exponent), Bool (yes/no), Str (single-quoted, escaping); and backward compatibility when literals {} is absent.
    status: pending
---
-->

### Goal

- Extend the `language! { ... }` DSL with a new optional `literals { ... }` section where the user defines **both** a **regex-like pattern** (what the lexer recognizes as a literal token) and **eval** code (how to convert the matched text to a value). Each subsection is named after the type (e.g. `Int`, `Float`, `Bool`, `Str`) and contains `pattern: <string>` and `eval: ![ ... ]`. The **eval expression's return type** must match the native type declared in `types` for that category.
- The **lexer** takes these patterns and compiles them (regex subset to NFA) so it can recognize literal tokens with **any shape the user specifies** — including prefix (e.g. `0x`, `0o`, `0b`) or **suffix** (e.g. `xh` for hex). The Rust code must be written to match: if the pattern matches `FFh`, the parse code receives `"FFh"` and must strip the suffix and parse accordingly.
- **Section order**: the `types` section must **precede** the `literals` section so that literal subsections (Int, Float, etc.) can be validated against declared type names.
- **No panics**: The Rust code that converts a literal to its internal representation must **not panic**. On invalid or unparseable input it must return a sentinel value: **Int** → all-bits-set (e.g. `-1` for i64); **Float** → **NaN** (e.g. `f64::NAN`); **Bool** → `false`; **Str** → `String::new()` (empty string).
- **Partial literals**: If the `literals` section **omits** some types that have native types in `types` (e.g. the user defines only `Int` and `Float` in `literals` but also has `Bool` and `Str` in `types`), then those omitted types use **default** parsing: decimal integers `[0-9]+`, keywords `true`/`false` for Bool, standard float regex for Float, double-quoted string for Str, etc. So custom literals apply only to types that have a subsection in `literals`; all others keep the built-in behavior.

### Constraints from current implementation

- **Lexing is DFA-based** and currently hardcodes numeric tokens:
  - Integer fragment is `[0-9]+` (`build_integer_fragment`) and float is `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?` (`build_float_fragment`) in `[prattail/src/automata/nfa.rs](/home/serhi/Projects/mettail-rust/prattail/src/automata/nfa.rs)`.
- The lexer currently **parses numbers inside the lexer** (e.g., `text.parse::<i64>()`) in `[prattail/src/automata/codegen.rs](/home/serhi/Projects/mettail-rust/prattail/src/automata/codegen.rs)`.
  - This will break as soon as you allow prefixes like `0xFF` or digit separators.

### Proposed `literals { ... }` syntax (example)

Subsection names **match the type names** from `types { ... }` (e.g. `Int`, `Float`, `Bool`, `Str`). Each subsection has **fixed order**: first `**pattern:`** followed by a string literal (the regex) and `**;`**, then `**eval:`** followed by the Rust code in `**![ ... ]**`. So: `pattern: <string>; eval: ![ <expr> ]`.

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
      pattern: r"(?x) [+-]?(?: 0b[01](?:_?[01])* | 0o[0-7](?:_?[0-7])* | 0x[0-9A-Fa-f](?:_?[0-9A-Fa-f])* | [0-9](?:_?[0-9])* )";
      eval: ![ {
        let s = text.replace('_', "");
        let (sign, body) = match s.strip_prefix('-') {
          Some(rest) => (-1_i64, rest),
          None => (1_i64, s.as_str()),
        };
        let (radix, digits) = if let Some(h) = body.strip_prefix("0x") { (16, h) }
          else if let Some(o) = body.strip_prefix("0o") { (8, o) }
          else if let Some(b) = body.strip_prefix("0b") { (2, b) }
          else { (10, body) };
        i64::from_str_radix(digits, radix).map(|n| sign * n).unwrap_or(-1_i64)
      } ]
    }

    Float {
      pattern: r"[0-9](?:_?[0-9])*(?:\.[0-9](?:_?[0-9])*)?([eE][+-]?[0-9](?:_?[0-9])*)?";
      eval: ![ { text.replace('_', "").parse::<f64>().unwrap_or(f64::NAN) } ]
    }

    Bool {
      pattern: r"yes|no";
      eval: ![ { text == "yes" } ]
    }

    Str {
      pattern: r"'([^'\\]|\\.)*'";
      eval: ![ {
        if text.len() < 2 { String::new() }
        else { text[1..text.len()-1].replace("\\'", "'").replace("\\\\", "\\").to_string() }
      } ]
    }
  },

  terms { ... }
}
```

(Generated code arranges that `text` is in scope when the eval runs for a matched token.) **Boolean literals** can use custom keywords (e.g. `yes`/`no`). **String literals** can use a different delimiter: e.g. single quotes `'...'` instead of double quotes `"..."`, with a pattern that matches `'...'` (and allows escaped `\'` inside) and eval that strips the quotes and unescapes; invalid or empty → return `String::new()`. To use **suffix** hex (e.g. `FFh`), the pattern would include an alternative like `[0-9A-Fa-f]+h` and the eval would strip the suffix and parse as hex.

### Design notes (why this shape)

- **Lexer uses user patterns**: Each literal type has a `pattern` (regex-like string) compiled to an NFA so the lexer recognizes that token shape (prefix or suffix). The **eval** (`![ ... ]`) code must align: it receives whatever the pattern matched.
- **Same convention**: Rust snippets in `![ ... ]` as in terms. Subsection names = type names. Collection delimiters stay in `types { ... }`.
- **Sentinel on error**: Eval must not panic; return Int → all-bits-set (e.g. `-1`), Float → NaN, Bool → `false`, Str → `String::new()` on invalid input.
- **Eval return type**: The eval expression's type must match the **native type** declared in `types` for that category (e.g. `i32`/`i64` for Int, `f64` for Float, `bool` for Bool, `String` or `str` for Str). Codegen uses this to generate the correct token/constructor.
- **Pattern string**: Use **raw strings** `r"..."` for the pattern so backslashes (e.g. in regex `\\.`) are written once; non-raw strings require extra escaping.

### Regex subset (literal patterns)

The pattern string is compiled to an NFA. The **required** feature set is: **literals** (single chars), **character classes** `[...]` and ranges (e.g. `[0-9]`, `[a-fA-F]`), **alternation** `|`, **grouping** `(?: ... )` (non-capturing), **quantifiers** `?`, `*`, `+`. Optional: **extended mode** `(?x)` (ignore whitespace/comments in the pattern). Semantics are **ASCII-only** (no Unicode property escapes). Document this set so the regex→NFA step has a clear spec; implement only what is needed for the examples (prefix/suffix numeric, yes/no, single-quoted string).

### Literal vs identifier priority

When input could match both a custom literal (e.g. `yes`) and an **identifier**, the lexer must apply a defined rule. Use **literal tokens before identifier**: try literal patterns (for Int, Float, Bool, Str, etc.) in the same NFA/DFA as other tokens; if a literal pattern matches, emit that token rather than `Ident`. (Alternatively, longest match wins if both literal and ident are tried; the implementation should document the chosen rule so that e.g. `yes` is always Bool when Bool has pattern `yes|no`.)

### Implementation approach (high-level)

1. **Extend macro AST to parse `literals { ... }`**
  - Update macros/src/ast/language.rs to add an optional `literals: Option<LiteralBlock>` to `LanguageDef`. Enforce that `**types` is parsed before `literals**` (so literal subsection names can be validated against declared types).
  - Parse subsections by **type name** (e.g. `Int { pattern: r\"...\", eval: ![ ... ] }`, `Float { ... }`). Each subsection has `pattern: <LitStr>` and `eval: ![ <expr> ]` (same rust_code parsing as in terms). Only types in `types {}` with matching name and numeric native type are valid.
2. **Carry literal parse code through the bridge**
  - In prattail_bridge, pass literal specs (pattern string + parse expression) into the parser/lexer pipeline.
3. **Compile user patterns to NFA**
  - Implement a regex subset compiler (or use a crate): user pattern string -> NFA fragment. Support alternation, groups, character classes, quantifiers so that both prefix (0x...) and suffix (...h) forms can be expressed. In nfa.rs, when custom literals are present, use these NFA fragments instead of the hardcoded integer/float fragments. Lexer emits the matched text as the token payload; parser calls user parse code.
4. **Token payload and parse hook**
  - Lexer either emits numeric tokens as text and the parser/trampoline calls the user parse code to get the value, or the generated code wraps the user expression in a helper and the lexer calls it. Emitting text and parsing in the parser layer keeps the lexer simple and gives good error spans.
5. **Parser integration**
  - In trampoline.rs, when building the NumLit prefix handler for Int/Float, use the language literal **eval** (the `eval: ![ ... ]` expression) so that Int::NumLit(...) and Float::FloatLit(...) are produced from the matched text via the user code.
6. **Tests**
  - **Int**: prefix/suffix (e.g. 0xff, 0o77, 0b1010, 1_000_000, FFh if supported). **Float**: decimal, underscore, exponent. **Bool**: custom keywords (e.g. yes/no). **Str**: custom delimiter (e.g. single-quoted with escaping). **Backward compatibility**: when `literals {}` is omitted, default behavior unchanged (decimal int, standard float, true/false, double-quoted string).

### Backward compatibility

- If `literals {}` is omitted entirely, behavior stays exactly as today (decimal `[0-9]+` integers, current float regex, `true`/`false`, double-quoted strings).
- If `literals {}` is present but **omits** some types, those types still use the **default** literal parsing (decimals for Int, `true`/`false` for Bool, standard float for Float, double-quoted for Str, etc.). Only types listed in `literals` use custom pattern and eval.
- `types`-level collection delimiters stay as they are; no migration needed.

