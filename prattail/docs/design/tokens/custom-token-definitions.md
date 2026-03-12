# Custom Token Definitions

**Date:** 2026-03-11
**Version:** 1.0

## Table of Contents

- [Overview](#overview)
- [Grammar](#grammar)
- [Regex Patterns](#regex-patterns)
- [Category Mapping](#category-mapping)
- [Constructor Code](#constructor-code)
- [Priority Disambiguation](#priority-disambiguation)
- [Override Semantics](#override-semantics)
- [NFA Pipeline](#nfa-pipeline)
- [Generated Code Structure](#generated-code-structure)
- [Examples](#examples)
- [References](#references)

---

## Overview

A custom token definition declares a new token kind or overrides a built-in
one. Intuitively, think of each definition as answering three questions:

1. **What does this token look like?** -- A regex pattern.
2. **What does it mean to the parser?** -- A category mapping and payload.
3. **How should the lexer behave after matching it?** -- Mode transitions
   and stream routing.

The answers are compiled at macro expansion time into NFA fragments, DFA
states, and `Token<'a>` enum variants. No regex engine runs at parse time;
the patterns are baked into a deterministic finite automaton.

---

## Grammar

The full syntax for a single token definition:

```
token_def  ::=  Name "=" pattern_spec
                [":" Category]
                ["!" "[" rust_code "]"]
                modifier*
                ";"

pattern_spec  ::=  "/" regex "/"
                |  string_literal

modifier  ::=  "push" "(" mode_name ")"
            |  "pop"
            |  "priority" "(" integer ")"
            |  "->" stream_name
```

Production rules in detail:

| Non-terminal     | Expansion | Notes |
|------------------|-----------|-------|
| `Name`           | Rust identifier | PascalCase by convention |
| `pattern_spec`   | `/regex/` or `"regex"` or `r"regex"` | String literal form needed if pattern contains `"` |
| `Category`       | Rust identifier | Must match a `types { ... }` declaration |
| `rust_code`      | Rust expression | `text: &str` is in scope |
| `mode_name`      | Rust identifier | Must match a `mode name { ... }` block or `default` |
| `stream_name`    | Rust identifier | Creates or routes to a named auxiliary stream |
| `integer`        | `0`..`255` | Disambiguation priority (u8) |

Modifiers may appear in any order after the optional `![code]` block and
before the terminating `;`. Each modifier may appear at most once.

---

## Regex Patterns

### Delimiters

Patterns are delimited by `/` ... `/` (slash form) or by string literals.
The slash form is convenient for simple patterns; the string form is
required when the pattern itself contains unescaped `"` characters:

```
HexLiteral = /0x[0-9a-fA-F]+/ ;          // slash form
RawString  = r"r#\"[^\"]*\"#" ;           // string literal form
```

### Supported PCRE Subset

The regex compiler (`automata/regex.rs`) implements a single-pass,
trampolined Thompson NFA construction with no intermediate AST:

| Feature              | Syntax                             | Notes                    |
|----------------------|------------------------------------|--------------------------|
| Literal character    | `a`, `1`, `_`                      | ASCII byte-level         |
| Escaped metachar     | `\.` `\\` `\[` `\(` `\|` etc.     | Metachar as literal      |
| Escape sequences     | `\n` `\r` `\t`                     | Common whitespace        |
| Shorthand classes    | `\d` `\w` `\s` `\D` `\W` `\S`     | POSIX-like (ASCII)       |
| Unicode escape       | `\u{03B1}` `\u03B1` `\U000003B1`  | Codepoint by hex         |
| Unicode property     | `\p{XID_Start}` `\P{White_Space}`  | Unicode categories       |
| Character class      | `[abc]` `[a-z]` `[0-9A-F]`        | Byte or codepoint ranges |
| Negated class        | `[^abc]` `[^\p{Letter}]`           | Complement over domain   |
| Dot / Groups         | `.` `(...)`                        | Non-capturing groups     |
| Alternation          | `a\|b`                             | Union                    |
| Quantifiers          | `*` `+` `?` `{n}` `{n,m}` `{,n}`  | Greedy, count-bounded    |

**Not supported:** Backreferences, lookahead/lookbehind, lazy quantifiers,
named groups, anchors (`^` `$` outside character classes).

### Unicode Support

Multi-byte codepoints are decomposed into byte-level NFA transition chains
at compile time via `regex_syntax::utf8::Utf8Sequences` -- for example,
U+03B1 (UTF-8 `CE B1`) becomes the chain `──[CE]──▸──[B1]──▸ accept`.
The downstream pipeline operates on `[u8; 256]` tables with zero UTF-8
decoding at lex time. Unicode property classes (`\p{XID_Start}`) are
resolved at compile time to codepoint ranges, then decomposed to byte
chains, enabling Unicode-aware identifiers at no runtime cost.

---

## Category Mapping

The optional `: Category` annotation links a token kind to a grammar
category declared in `types { ... }`. This determines two things:

1. **Payload type.** The category's native type (from `![T] as Category`)
   becomes the payload type of the generated `Token` enum variant.

2. **Parse-time conversion.** When the parser encounters this token kind
   where a nonterminal of the target category is expected, it constructs
   the payload using the `![code]` block.

```rust
types {
    ![i64] as Int;         // native type i64
    ![f64] as Real;        // native type f64
}

tokens {
    HexLiteral = /0x[0-9a-fA-F]+/ : Int
        ![i64::from_str_radix(&text[2..], 16).unwrap_or(0)];
}
```

Here, `HexLiteral` maps to category `Int`, so the generated enum variant
is `HexLiteral(i64)`. The `![...]` block provides the conversion from the
matched `text: &str` to `i64`.

If no `: Category` is given, the token has no payload -- its enum variant
is a unit variant (e.g., `Semicolon`). This is the common case for
delimiters, operators, and whitespace tokens.

### Payload Type Resolution

The bridge layer resolves the payload type by looking up the category's
native type in `types { ... }`. If the category has native type *T*, the
enum variant carries *T*; otherwise it is a unit variant. For `str`-typed
payloads, the generated variant uses `&'a str` to avoid allocation.

---

## Constructor Code

The `![code]` block provides a Rust expression that converts the matched
text into the payload value. Inside the block, one binding is available:

- **`text: &str`** -- The matched source text (the exact slice from the
  input that the DFA accepted).

The expression must evaluate to the payload type determined by the category
mapping. The `![code]` block is syntactically delimited by `![ ... ]`,
reusing the same delimiter convention as `types { ![i32] as Int; }`.

```rust
HexLiteral = /0x[0-9a-fA-F]+/ : Int ![i64::from_str_radix(&text[2..], 16).unwrap_or(0)];
StringLit  = /"([^"\\]|\\.)*"/ : Txt ![&text[1..text.len()-1]];
TrueLit    = /true/  : Bool ![true];
FalseLit   = /false/ : Bool ![false];
```

---

## Priority Disambiguation

When two or more token patterns match the same input at the same position
and with the same length, **priority** breaks the tie. The lexer always
prefers the longest match first (maximal munch); priority only applies
among equal-length matches.

```
priority(N)     where  N : u8   (0 ≤ N ≤ 255)
```

### Default Priorities

| Token kind                 | Default priority |
|----------------------------|:----------------:|
| Custom pattern (regex)     | 2                |
| Fixed terminal (keyword)   | 10               |

The keyword default of 10 ensures that `true` is lexed as the keyword
`KwTrue` rather than as an identifier `Ident("true")`, since both patterns
match "true" with length 4 but the keyword has higher priority.

### How Priority Maps to Tropical Weights

Internally, priority is encoded as a `TropicalWeight` on the NFA accept
state. The tropical semiring `(R ∪ {+∞}, min, +, +∞, 0)` assigns lower
numerical weight to higher-priority tokens:

```
weight = TropicalWeight::from_priority(p)
```

where `from_priority` maps `u8` priority *p* to weight *w* via an
order-inverting function (higher priority produces lower weight, which the
tropical `min` operation prefers). During DFA construction and
minimization, the weight propagates through the pipeline so that the
codegen emits the correct token kind when multiple patterns accept at the
same position.

Maximal munch handles most cases (e.g., `0x1F` matches 4 chars via hex vs.
1 char via integer), but priority resolves ties among equal-length matches.

---

## Override Semantics

Four token names are "built-in" and correspond to the patterns in
`literal_patterns.ebnf`:

| Built-in name | Default pattern                          | `TokenKind` variant |
|---------------|------------------------------------------|---------------------|
| `Integer`     | `[0-9]+`                                 | `TokenKind::Integer` |
| `Float`       | `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`      | `TokenKind::Float`   |
| `StringLit`   | `"([^"\\]\|\\.)*"`                       | `TokenKind::StringLit` |
| `Ident`       | `[a-zA-Z_][a-zA-Z0-9_]*`                | `TokenKind::Ident`   |

When a token definition uses one of these names, the bridge layer sets
`is_builtin_override = true` and patches the corresponding `LiteralPatterns`
field before NFA construction. Override tokens reuse the existing `Token`
enum variants (`Integer(i64)`, `Float(f64)`, etc.) -- no new variants are
generated. Non-override tokens always produce new `Token` enum variants
(`TokenKind::Custom(name)`).

---

## NFA Pipeline

Custom token patterns flow through the same automata pipeline as built-in
patterns. The full compilation chain:

```
                          Thompson          ε-closure         Subset
  /regex/  ──────────▸  NFA Fragment  ──────────▸  NFA  ──────────▸  DFA
                                                     ▲
                                                     │
  built-in patterns ──── NFA fragments ──────────────┘
  keyword trie ──────── NFA trie ────────────────────┘

      Hopcroft                Alphabet            Codegen
  DFA  ──────────▸  Min DFA  ──────────▸  (DFA + Partition)  ──────────▸  Rust source
```

### Step-by-step Detail

**1. Thompson construction.** Each regex is compiled into an NFA fragment
(start, accept pair) via single-pass trampolined construction in
`build_nfa_with_custom()`.

**2. Global NFA assembly.** All fragments are joined via epsilon
transitions from a single global start state *q*_0:

```
             ┌─ε─▸ keyword/operator trie ─▸ (accept states)
             │
    q₀ ──────┼─ε─▸ ident fragment ─▸ (accept: Ident)
             ├─ε─▸ integer fragment ─▸ (accept: Integer)
             ├─ε─▸ float fragment ─▸ (accept: Float)
             ├─ε─▸ string fragment ─▸ (accept: StringLit)
             └─ε─▸ HexLiteral fragment ─▸ (accept: Custom("HexLiteral"))
```

Each accept state carries a `TropicalWeight` encoding its priority.

**3. Subset construction.** The powerset construction converts the NFA
to a DFA. Among conflicting accept states, the lowest tropical weight
(highest priority) wins.

**4. Hopcroft minimization.** Partition-refinement produces the smallest
equivalent DFA (Hopcroft, 1971).

**5. Alphabet partitioning.** Byte values with identical behavior across
all states are grouped into equivalence classes (typically 15--40).

**6. Codegen.** Three strategies: direct-coded (DFA ≤ 30 states),
table-driven (> 30), or hybrid AL02 (hot states direct, cold table).

---

## Generated Code Structure

The codegen emits a `Token<'a>` enum and supporting functions:

### Token Enum

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    Eof,
    Ident(&'a str),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    StringLit(&'a str),
    // Fixed terminals (from grammar):
    Plus,           // "+"
    LParen,         // "("
    KwLet,          // "let"
    // Custom tokens (from tokens { ... }):
    HexLiteral(i64),
    DocComment,
    // ...
}
```

Custom tokens with a `: Category` annotation and a `payload_type` produce
tuple variants; those without produce unit variants. The variant name
matches the token definition name exactly.

A `format_token_friendly()` function is also generated alongside the enum,
producing human-readable descriptions for error messages (e.g.,
`Token::HexLiteral(n)` renders as `"hex literal \`255\`"`).

When a custom token has a `![code]` block, the codegen inlines the
expression at the lex site: `let text = &input[start..end];
Token::HexLiteral(i64::from_str_radix(&text[2..], 16).unwrap_or(0))`.

---

## Examples

### Hex, Binary, and Octal Literals

```rust
types { ![i64] as Int; }

tokens {
    HexLiteral = /0x[0-9a-fA-F]+/ : Int
        ![i64::from_str_radix(&text[2..], 16).unwrap_or(0)]
        priority(3);

    BinLiteral = /0b[01]+/ : Int
        ![i64::from_str_radix(&text[2..], 2).unwrap_or(0)]
        priority(3);

    OctLiteral = /0o[0-7]+/ : Int
        ![i64::from_str_radix(&text[2..], 8).unwrap_or(0)]
        priority(3);
}
```

All three map to `Int` (payload type `i64`). The `priority(3)` ensures
they are preferred over the default `Integer` pattern when prefixes overlap.

### Unicode Identifiers

```rust
tokens {
    Ident = /\p{XID_Start}\p{XID_Continue}*/ ;
}
```

This overrides the default `[a-zA-Z_][a-zA-Z0-9_]*` pattern with the
Unicode-standard identifier syntax. The `\p{XID_Start}` and
`\p{XID_Continue}` property classes are resolved at compile time to byte
chains via `regex_syntax::utf8::Utf8Sequences`. Variables like `nombre`,
`imie`, and `alpha` are recognized without any runtime cost.

### String Interpolation via Mode Stack

```rust
tokens {
    StringStart = /"/ push(string_body);
    mode string_body {
        InterpOpen  = /\$\{/ push(default);
        StringEnd   = /"/ pop;
        StringChars = /([^"$\\]|\\.)+/;
    }
}
```

Each mode has its own DFA. The `push`/`pop` modifiers form a pushdown
automaton restricted to a finite set of stack symbols (the mode names).

### Comment Routing

```rust
tokens {
    LineComment  = /\/\/[^\n]*/  -> comments;
    BlockComment = /\/\*([^*]|\*[^\/])*\*\//  -> comments;
}
```

Comments are placed in `LexResult::streams["comments"]` with byte-offset
ranges, preserving them for IDE tooling without polluting the parse stream.

---

## References

- **Thompson, K.** (1968). "Regular expression search algorithm."
  *CACM*, 11(6), 419--422. Foundational NFA construction algorithm.

- **Hopcroft, J.** (1971). "An *n* log *n* algorithm for minimizing
  states in a finite automaton." *Theory of Machines and Computations*,
  189--196. The partition-refinement DFA minimization used in the pipeline.

- **Aho, Lam, Sethi & Ullman** (2006). *Compilers: Principles,
  Techniques, and Tools* (2nd ed.). Ch. 3: lexical analysis, DFA
  construction, maximal munch.

- **Kempe, A.** (2004). "Multi-tape transducers and weighted automata."
  *CIAA*. Framework for the `multi-tape` feature's multi-stream lexing.

- **Droste & Kuich** (2009). "Semirings and Formal Power Series."
  *Handbook of Weighted Automata*, Ch. 1. Tropical semiring foundations.
