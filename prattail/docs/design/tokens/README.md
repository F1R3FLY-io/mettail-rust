# PraTTaIL `tokens { ... }` Block

**Date:** 2026-03-11
**Version:** 1.0

## Table of Contents

- [Motivation](#motivation)
- [Syntax Summary](#syntax-summary)
- [Relationship to literal_patterns.ebnf](#relationship-to-literal_patternsebnf)
- [Quick-Start Guide](#quick-start-guide)
- [Feature Gates](#feature-gates)
- [Cross-References](#cross-references)

---

## Motivation

Every language definition needs a lexer, and every lexer needs to know what
tokens look like. PraTTaIL ships with four built-in token kinds -- `Integer`,
`Float`, `StringLit`, and `Ident` -- whose regex patterns are defined in
`literal_patterns.ebnf`. These defaults work well for simple expression
languages, but real-world languages inevitably outgrow them:

**Problem 1: Hardcoded patterns are too narrow.** The default integer pattern
is `[0-9]+`. A language that needs hex literals (`0x1F`), binary literals
(`0b1010`), or numeric separators (`1_000_000`) cannot express these through
`literal_patterns.ebnf` alone without editing that file globally for all
languages in the workspace.

**Problem 2: New token kinds have no declaration site.** When a language
introduces token kinds that do not exist in the built-in set -- such as
`HashTag`, `AtSign`, `DocComment`, or `RegexLiteral` -- there is no place
in the `language!` macro to declare them, assign regex patterns, or wire them
into the NFA pipeline.

**Problem 3: Context-sensitive lexing requires modal DFAs.** Languages with
string interpolation, heredocs, nested comments, or embedded DSLs need the
lexer to switch between distinct sets of token rules depending on context.
A flat, single-DFA lexer cannot handle `"hello ${name} world"` correctly
because the rules inside `${ ... }` are different from the rules inside the
string body.

**Problem 4: Multi-stream output is needed for tooling.** IDEs, formatters,
and documentation generators need access to comments and whitespace that the
parser discards. Routing these tokens to auxiliary streams at lex time avoids
a costly second pass over the source text.

**Problem 5: Structural invariants need a declaration site.** Languages with
structural constraints on their token streams (e.g., "braces never nest more
than *k* deep") benefit from compile-time verification via mu-calculus
formulas on the parse tree. These constraints need a place to live alongside
the token definitions they reference.

The `tokens { ... }` block addresses all five problems in a single,
composable declaration site inside the `language!` macro.

---

## Syntax Summary

The `tokens` block sits between `types { ... }` and `terms { ... }` in the
`language!` macro. It contains four kinds of items, all optional, in any
order:

```
language! {
    name: MyLang,

    types { ... }

    tokens {
        // ── 1. Token definitions (default mode) ────────────────
        Integer = /[0-9](_?[0-9])*/ : Int ![code];     // override built-in
        HexLiteral = /0x[0-9a-fA-F]+/ : Int ![code];   // new token kind
        DocComment = /\/\/\/[^\n]*/ -> comments;         // stream routing

        // ── 2. Named lexer modes ───────────────────────────────
        mode string_body {
            Interpolation = /\$\{/ push(default);        // push mode
            StringEnd     = /"/ pop;                     // pop mode
            StringChars   = /[^"$\\]+/;                  // plain text
            EscapeSeq     = /\\./;                       // escapes
        }

        // ── 3. Cross-stream sync constraints ───────────────────
        sync {
            align(main, comments) on /\n/;
            track(whitespace, main);
        }

        // ── 4. Tree structural invariants ──────────────────────
        tree_invariants {
            no_nested_new: forall children of PNew { not PNew };
        }
    }

    terms { ... }
}
```

### 1. Token Definitions

Each token definition has the form:

```
Name = /regex/ [: Category] [![code]] [push(mode)] [pop]
       [-> stream] [priority(N)] ;
```

| Component       | Required | Description |
|-----------------|----------|-------------|
| `Name`          | yes      | Identifier for the token kind. If it matches a built-in name (`Integer`, `Float`, `StringLit`, `Ident`), the regex **overrides** the default pattern. |
| `/regex/`       | yes      | PCRE-subset pattern compiled to a Thompson NFA fragment. May also be written as `"regex"` or `r"regex"` for patterns containing `/`. |
| `: Category`    | no       | Maps the token to a grammar category. The category's native type determines the payload type. |
| `![code]`       | no       | Rust expression to construct the payload from `text: &str`. The binding `text` is in scope. |
| `push(mode)`    | no       | After matching, push `mode` onto the mode stack (activates that mode's DFA). |
| `pop`           | no       | After matching, pop the current mode from the stack (returns to the previous mode). |
| `-> stream`     | no       | Route matched tokens to a named auxiliary stream instead of `main`. |
| `priority(N)`   | no       | Disambiguation priority (0--255). Default: 2 for patterns, 10 for keywords. Higher values win on equal-length matches. |

### 2. Mode Blocks

```
mode mode_name {
    TokenA = /pattern_a/ ;
    TokenB = /pattern_b/ pop;
}
```

Each mode gets its own NFA -> DFA -> minimized DFA pipeline and its own
codegen. At runtime, the lexer maintains a mode stack. The active mode's DFA
processes input bytes; `push(mode)` and `pop` modifiers on token definitions
transition between modes.

### 3. Sync Constraints

```
sync {
    align(stream_a, stream_b) on /boundary_pattern/ ;
    track(auxiliary, primary) ;
}
```

- **`align(a, b) on /pat/`** -- Whenever the boundary pattern `/pat/`
  matches in one stream, synchronize token positions between `a` and `b`.
  Typical use: aligning comments with code at newline boundaries.

- **`track(aux, primary)`** -- The auxiliary stream tracks byte offsets
  relative to the primary stream. Used for whitespace preservation: the
  formatter reads whitespace tokens from the `whitespace` stream using
  offsets anchored in the `main` stream.

### 4. Tree Invariants

```
tree_invariants {
    invariant_name: constraint_expression ;
}
```

Constraint expressions use a tree DSL that supports both keyword and
Unicode operator forms:

| Keyword form                         | Unicode form             | Meaning |
|--------------------------------------|--------------------------|---------|
| `forall children of S { body }`      | `∀ ↓ S { body }`         | For every child of symbol *S*, *body* holds |
| `exists child`                       | `∃ child`                | The node has at least one child |
| `not expr`                           | `¬ expr`                 | Negation |
| `expr and expr`                      | `expr ∧ expr`            | Conjunction |
| `expr or expr`                       | `expr ∨ expr`            | Disjunction |
| `match { A \| B \| C }`             | `∈ { A \| B \| C }`     | Node label is one of the listed symbols |

Tree invariants are compiled to mu-calculus formulas and verified by the
parity alternating tree automaton (PATA) infrastructure at compile time.

---

## Relationship to `literal_patterns.ebnf`

The file `prattail/src/literal_patterns.ebnf` is the single source of truth
for the four built-in token patterns:

```ebnf
<integer> = /[0-9]+/                             ;
<float>   = /[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/   ;
<string>  = /"([^"\\]|\\.)*"/                    ;
<ident>   = /[a-zA-Z_][a-zA-Z0-9_]*/             ;
```

These patterns are embedded into the binary at compile time via
`include_str!` and parsed into a `LiteralPatterns` struct. The `tokens`
block interacts with them as follows:

```
┌─────────────────────────────┐     ┌────────────────────────────────┐
│   literal_patterns.ebnf     │     │     tokens { ... } block       │
│                             │     │                                │
│  <integer> = /[0-9]+/       │     │  Integer = /[0-9](_?[0-9])*/   │
│  <float>   = /..../         │     │  HexLiteral = /0x[0-9a-fA-F]+/ │
│  <string>  = /..../         │     │                                │
│  <ident>   = /..../         │     │                                │
└──────────┬──────────────────┘     └───────────┬────────────────────┘
           │                                    │
           ▼                                    ▼
   LiteralPatterns {                  CustomTokenSpec[] {
     integer: "[0-9]+",                 { name: "Integer",
     float: "...",                        pattern: "[0-9](_?[0-9])*",
     string: "...",                       is_builtin_override: true },
     ident: "...",                      { name: "HexLiteral",
   }                                      pattern: "0x[0-9a-fA-F]+",
           │                               is_builtin_override: false },
           │  override                  }
           ▼                                    │
   LiteralPatterns {                            │
     integer: "[0-9](_?[0-9])*", ◀──────────────┘ (override applied)
     float: "...",                              │
     string: "...",                             │
     ident: "...",                              │
   }                                            │
           │                                    │
           └────────────┬───────────────────────┘
                        ▼
                NFA (global start)
                 ├─ε─▸ keyword/operator trie
                 ├─ε─▸ ident fragment
                 ├─ε─▸ integer fragment  (overridden)
                 ├─ε─▸ float fragment
                 ├─ε─▸ string fragment
                 └─ε─▸ HexLiteral fragment  (new)
```

**Override rule:** If a token definition's name matches one of the four
built-in names (`Integer`, `Float`, `StringLit`, `Ident`), its regex
replaces the corresponding field in `LiteralPatterns` before NFA
construction. The override is purely lexical -- no new `Token` enum
variant is generated; the existing variant is reused.

**Non-override rule:** Any name that does not match a built-in adds a
new `TokenKind::Custom(name)` variant to the NFA and a corresponding
variant to the generated `Token<'a>` enum.

---

## Quick-Start Guide

### Hex Literals

```rust
language! {
    name: HexCalc,

    types { ![i64] as Int; }

    tokens {
        HexLiteral = /0x[0-9a-fA-F]+/ : Int
            ![i64::from_str_radix(&text[2..], 16).unwrap_or(0)]
            priority(3);
    }

    terms {
        HexLit . |- HexLiteral : Int;
        NumLit . |- Integer : Int;
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
    }
}
```

The `HexLiteral` token matches `0x` followed by hex digits, maps to
category `Int` (whose native type is `i64`), and uses the `![...]` block
to parse the text into an `i64`. The `priority(3)` ensures that `0x1F`
is lexed as a single `HexLiteral` rather than an `Integer` (`0`) followed
by an `Ident` (`x1F`).

### String Interpolation

```rust
tokens {
    StringStart = /"/ push(string_body);

    mode string_body {
        InterpStart = /\$\{/ push(default);
        InterpEnd   = /\}/ pop;
        StringEnd   = /"/ pop;
        StringChars = /[^"$\\]+/;
        EscapeSeq   = /\\./;
    }
}
```

When the lexer sees `"` in the default mode, it emits `StringStart` and
pushes `string_body`. Inside that mode, `${` pushes back to `default`
for the interpolated expression; `}` pops back to `string_body`; the
closing `"` pops back to `default`.

### Comment Preservation

```rust
tokens {
    LineComment = /\/\/[^\n]*/ -> comments;
    BlockComment = /\/\*([^*]|\*[^\/])*\*\// -> comments;
}
```

Comments are routed to the `comments` auxiliary stream. The parser never
sees them, but IDE tooling can retrieve them from `LexResult::streams`
keyed by `"comments"`.

---

## Feature Gates

The core `tokens` block (token definitions, overrides, `priority`, `push`,
`pop`) requires no feature gates -- it is always available.

| Sub-feature             | Cargo feature            | Description |
|-------------------------|--------------------------|-------------|
| Stream routing (`->`)   | *(always on)*            | Multi-stream output via `LexResult::streams` |
| `sync { ... }`          | *(always on)*            | Cross-stream synchronization constraints |
| `tree_invariants`       | `parity-tree-automata`   | Mu-calculus PATA verification of tree constraints |
| Multi-tape dispatch     | `multi-tape`             | Synchronized k-tape computation for multi-channel lexing |
| Probabilistic weights   | `probabilistic`          | Corpus-trained weights for disambiguation |
| Grammar generation      | `grammar-gen`            | Proptest-based expression generators for token testing |

---

## Cross-References

| Topic | Document |
|-------|----------|
| Token definition syntax (detailed) | [custom-token-definitions.md](custom-token-definitions.md) |
| Regex compiler internals | [../automata-pipeline.md](../automata-pipeline.md) |
| Automata codegen optimizations | [../automata-codegen-optimizations.md](../automata-codegen-optimizations.md) |
| WFST prediction dispatch | [../wfst/](../wfst/) |
| Parity tree automata | [../parity-tree-automata.md](../parity-tree-automata.md) |
| Multi-tape automata | [../multi-tape-automata.md](../multi-tape-automata.md) |
| Semiring catalog | [../semiring-catalog.md](../semiring-catalog.md) |
| Lint diagnostics | [../lint-layer.md](../lint-layer.md) |
| Overall design rationale | [../README.md](../README.md) |

### Source Files

| File | Role |
|------|------|
| `macros/src/ast/language.rs` | Parsing of `tokens { ... }` block into AST (`TokenDef`, `ModeDef`, `SyncConstraint`, `TreeInvariant`) |
| `macros/src/ast/fragment.rs` | Fragment merging of token definitions via `language_fragment!` |
| `prattail/src/lib.rs` | `CustomTokenSpec`, `LexerModeSpec`, `SyncSpec`, `TreeInvariantSpec`, `LexResult` |
| `prattail/src/automata/nfa.rs` | `build_nfa_with_custom()` -- NFA construction from custom tokens |
| `prattail/src/automata/regex.rs` | PCRE-subset regex compiler (Thompson NFA, trampolined) |
| `prattail/src/automata/codegen.rs` | `write_token_enum()`, `write_token_display()` -- `Token<'a>` enum generation |
| `prattail/src/lexer.rs` | Lexer pipeline orchestration (NFA -> DFA -> minimize -> codegen) |
| `prattail/src/literal_patterns.ebnf` | Default built-in patterns (canonical source of truth) |
