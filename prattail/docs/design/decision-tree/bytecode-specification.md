# PraTTaIL Decision Tree Bytecode Specification

| Metadata | Value                                                                                           |
|----------|-------------------------------------------------------------------------------------------------|
| Date     | 2026-03-06                                                                                      |
| Updated  | 2026-03-06                                                                                      |
| Source   | `prattail/src/decision_tree.rs`, `prattail/src/token_id.rs`, `prattail/src/automata/codegen.rs` |

---

## Table of Contents

- [§1 Encoding Overview](#1-encoding-overview)
- [§2 Byte Ranges](#2-byte-ranges)
- [§3 Terminal Encoding](#3-terminal-encoding)
- [§4 Pattern Element Types](#4-pattern-element-types)
- [§5 Nonterminal Boundary Protocol](#5-nonterminal-boundary-protocol)
- [§6 Encoding Examples](#6-encoding-examples)
- [§7 Encoding Constraints](#7-encoding-constraints)

---

## §1 Encoding Overview

Every rule in a PraTTaIL grammar consists of a sequence of **pattern items**: terminals
(keywords, punctuation, operators), nonterminal references (recursive sub-parses), capture
markers (identifier or binder positions), and optional groups. The decision tree dispatch
mechanism encodes each item in a rule's pattern as a single byte so that the entire prefix
can be inserted into a PathMap trie for compact, O(k) prefix-based rule resolution where
k is the length of the byte path.

The encoding is defined by a partitioning of the byte space [0x00, 0xC1] into five
non-overlapping regions, each assigned to a distinct element kind:

```
  Byte Space Layout
  ┌──────────────────────────────────────────────────────────────────┐
  │ 0x00                                                      0xFF   │
  │ ├──────────────┬────┬────┬──────────────────────┬────┬────┤      │
  │ │  Terminals   │ ID │ BD │    NonTerminals      │ O₀ │ O₁ │      │
  │ │ 0x00 ─ 0x7F  │0x80│0x81│  0x82 ─ 0xBF         │0xC0│0xC1│      │
  │ └──────────────┴────┴────┴──────────────────────┴────┴────┘      │
  └──────────────────────────────────────────────────────────────────┘
  ID = IDENT_CAPTURE    BD = BINDER_CAPTURE    O₀/O₁ = Optional markers
```

Each pattern item maps to exactly one byte. The resulting byte sequence is inserted into a
`PathMap<DecisionAction>` trie (one per syntactic category). At parse time, the parser
walks the trie byte-by-byte using the current token's ID as the lookup key, arriving at a
leaf that names the unique matching rule or an ambiguity set requiring further
disambiguation.

---

## §2 Byte Ranges

The full byte encoding scheme partitions the [0x00, 0xC1] range as follows:

| Range           | Hex              | Width | Purpose                                      |
|-----------------|------------------|-------|----------------------------------------------|
| Terminal IDs    | `0x00` .. `0x7F` | 128   | Token IDs assigned by `TokenIdMap`           |
| IDENT_CAPTURE   | `0x80`           | 1     | Consumes exactly one `Ident` token           |
| BINDER_CAPTURE  | `0x81`           | 1     | Consumes exactly one `Ident` token (binding) |
| NonTerminal IDs | `0x82` .. `0xBF` | 62    | Category index + `NT_BASE` (0x82)            |
| OPTIONAL_START  | `0xC0`           | 1     | Marks the beginning of an optional group     |
| OPTIONAL_END    | `0xC1`           | 1     | Marks the end of an optional group           |

The invariant maintained by the encoder is:

```
∀ b ∈ encoded_bytes:
    b ≤ 0x7F  ⟹  b is a terminal token ID
    b = 0x80  ⟹  IDENT_CAPTURE
    b = 0x81  ⟹  BINDER_CAPTURE
    0x82 ≤ b ≤ 0xBF  ⟹  NonTerminal with category_index = b − 0x82
    b = 0xC0  ⟹  OPTIONAL_START
    b = 0xC1  ⟹  OPTIONAL_END
```

Bytes above `0xC1` are currently unassigned and reserved for future use.

---

## §3 Terminal Encoding

Terminal tokens are assigned compact `u16` identifiers by `TokenIdMap`
(`prattail/src/token_id.rs`). The map is built once per grammar during pipeline
construction, assigning IDs in sorted order for determinism:

```
TokenIdMap::from_names(names)
  1. Collect and sort all token variant names alphabetically
  2. Assign sequential u16 IDs: 0, 1, 2, ...
  3. Store bidirectional mapping: name → id, id → name
```

For the decision tree encoding, only the first 128 IDs (0x00 through 0x7F) are usable
because the byte ranges above 0x7F are reserved for captures, nonterminals, and optional
markers. The constant `MAX_TERMINAL_ID: u8 = 0x7F` enforces this ceiling.

### Variant Name Conversion

Raw terminal strings from the grammar specification are converted to Rust-style variant
names by `terminal_to_variant_name()` (`prattail/src/automata/codegen.rs`). This function
handles three classes of terminals:

**Symbolic operators** (exhaustive match table):

| Raw  | Variant       | Raw    | Variant      |
|------|---------------|--------|--------------|
| `+`  | `Plus`        | `(`    | `LParen`     |
| `-`  | `Minus`       | `)`    | `RParen`     |
| `*`  | `Star`        | `{`    | `LBrace`     |
| `/`  | `Slash`       | `}`    | `RBrace`     |
| `%`  | `Percent`     | `[`    | `LBracket`   |
| `!`  | `Bang`        | `]`    | `RBracket`   |
| `?`  | `Question`    | `==`   | `EqEq`       |
| `@`  | `At`          | `!=`   | `BangEq`     |
| `.`  | `Dot`         | `<=`   | `LtEq`       |
| `,`  | `Comma`       | `>=`   | `GtEq`       |
| `\|` | `Pipe`        | `&&`   | `AmpAmp`     |
| `:`  | `Colon`       | `\|\|` | `PipePipe`   |
| `;`  | `Semi`        | `++`   | `PlusPlus`   |
| `^`  | `Caret`       | `--`   | `MinusMinus` |
| `~`  | `Tilde`       | `**`   | `StarStar`   |
| `#`  | `Hash`        | `->`   | `Arrow`      |
| `&`  | `Amp`         | `=>`   | `FatArrow`   |
| `=`  | `Eq`          | `<-`   | `LArrow`     |
| `<`  | `Lt`          | `::`   | `ColonColon` |
| `>`  | `Gt`          | `..`   | `DotDot`     |
| `{}` | `EmptyBraces` | `<<`   | `LtLt`       |
|      |               | `>>`   | `GtGt`       |
|      |               | `>>>`  | `GtGtGt`     |

**Keywords** (alphanumeric strings): prefixed with `Kw` and capitalized.
For example, `"if"` becomes `"KwIf"`, `"match"` becomes `"KwMatch"`.

**Dollar-prefixed terminals**: `"$proc"` becomes `"DollarProc"`,
`"$$name("` becomes `"DdollarNameLp"`.

### Source Constants

All encoding constants are defined at the top of `prattail/src/decision_tree.rs`:

```rust
const IDENT_CAPTURE:  u8 = 0x80;
const BINDER_CAPTURE: u8 = 0x81;
const NT_BASE:        u8 = 0x82;
const OPTIONAL_START: u8 = 0xC0;
const OPTIONAL_END:   u8 = 0xC1;
const MAX_TERMINAL_ID: u8 = 0x7F;
```

---

## §4 Pattern Element Types

Before byte encoding, each item in a rule's pattern is represented as a variant of the
`PatternElement` enum (`prattail/src/decision_tree.rs`):

```rust
pub enum PatternElement {
    Terminal      { variant: String, id: u8 },
    IdentCapture  { param_name: String },
    BinderCapture { param_name: String },
    NonTerminal   { category: String, category_id: u8 },
    OptionalStart,
    OptionalEnd,
}
```

Each variant maps to a specific byte in the encoding:

| Variant         | Encoded Byte            | Notes                                        |
|-----------------|-------------------------|----------------------------------------------|
| `Terminal`      | `id` field (0x00-0x7F)  | Looked up from `TokenIdMap`                  |
| `IdentCapture`  | `0x80`                  | Fixed; `param_name` used only during codegen |
| `BinderCapture` | `0x81`                  | Fixed; `param_name` used only during codegen |
| `NonTerminal`   | `0x82 + category_index` | Triggers a **segment split** (see §5)        |
| `OptionalStart` | `0xC0`                  | Opens an optional group bracket              |
| `OptionalEnd`   | `0xC1`                  | Closes an optional group bracket             |

The encoding function `encode_terminal_prefix()` walks the pattern left-to-right, pushing
one byte per element, until it encounters a `NonTerminal` — at which point it returns
early with the accumulated bytes and a boundary descriptor. If no `NonTerminal` is
encountered, the entire pattern is encoded as a single contiguous byte sequence.

---

## §5 Nonterminal Boundary Protocol

The trie cannot directly encode nonterminal positions because a nonterminal represents a
recursive sub-parse whose result is not known until runtime. Instead, the trie is **split
at nonterminal boundaries** into linked segments. The protocol works as follows:

### Step 1: Encode the Terminal Prefix

`encode_terminal_prefix()` walks the pattern elements sequentially. For each element that
is not a `NonTerminal`, it appends the corresponding byte to the output vector. Upon
encountering the first `NonTerminal`, it stops and returns:

```
encode_terminal_prefix(pattern) → (bytes: Vec<u8>, boundary: Option<NTBoundaryInfo>)
```

where `NTBoundaryInfo` captures the state at the split point:

```rust
pub struct NTBoundaryInfo {
    pub category: String,              // nonterminal's category name
    pub category_id: u8,               // 0x82 + category_index
    pub remaining_pattern: Vec<PatternElement>,  // items after the NT
    pub position: usize,               // index of the NT in the pattern
}
```

### Step 2: Insert the Prefix Segment

The terminal prefix bytes are inserted into segment 0 (the root segment) of the
category's `CategoryDecisionTree`. Each category maintains a `Vec<PathMap<DecisionAction>>`
where segment 0 is the root and segments 1..n are continuation segments created at NT
boundaries.

### Step 3: Create the Continuation Segment

`insert_nt_continuation()` handles the post-boundary pattern:

1. Allocate a new segment (PathMap) in the category's segment vector.
2. Call `encode_terminal_prefix()` on `boundary.remaining_pattern` to encode the
   continuation (the items after the nonterminal).
3. Insert the continuation bytes into the new segment with a `Commit` action.
4. Increment `stats.nonterminal_boundaries` for diagnostic reporting.

### Segment Linking Diagram

```
  Rule: FloatCast → float ( Int )
  Pattern: [Terminal("KwFloat"), Terminal("LParen"), NonTerminal("Int"), Terminal("RParen")]

  ┌─ Segment 0 (root) ──────────────────────────────────┐
  │                                                     │
  │  Path: [id_float, id_lparen]                        │
  │  Action: NonterminalBoundary { category: "Int",     │
  │          resume_segment: 1 }                        │
  │                                                     │
  └─────────────────────────────────────────────────────┘
            │
            │ after parsing Int sub-expression
            ▼
  ┌─ Segment 1 (continuation) ──────────────────────────┐
  │                                                     │
  │  Path: [id_rparen]                                  │
  │  Action: Commit { rule: "FloatCast" }               │
  │                                                     │
  └─────────────────────────────────────────────────────┘
```

### FIRST Set Expansion at Boundaries

At each nonterminal boundary, the resolver (`resolve_nonterminal_boundaries()`) expands
the nonterminal's FIRST set. If the FIRST tokens are disjoint from other options at the
same trie node, the boundary is deterministic: the parser can peek the next token and
decide which nonterminal to enter. If they overlap, the node is marked `Ambiguous` with
the minimal candidate set for NFA try-all dispatch.

---

## §6 Encoding Examples

The following examples illustrate the byte encoding for representative rule patterns.
Terminal IDs are written symbolically as `id_X` where `X` is the variant name; their
actual numeric values depend on the grammar's `TokenIdMap` assignment order.

### Example 1: Pure Terminal Rule

**Rule:** `IfThenElse: if Expr then Expr else Expr`

Because this rule has nonterminals, only the prefix up to the first NT is encoded in
segment 0. But consider a simplified terminal-only rule for illustration:

**Rule (simplified):** `IfThenElse_kw: if then else`

**Pattern elements:**

```
[Terminal("KwIf"), Terminal("KwThen"), Terminal("KwElse")]
```

**Encoding:**

```
encode_terminal_prefix(pattern) = ([id_if, id_then, id_else], None)

  Byte sequence: ┌──────┬────────┬────────┐
                 │id_if │id_then │id_else │
                 │ 0x__ │  0x__  │  0x__  │
                 └──────┴────────┴────────┘

  Trie path: id_if → id_then → id_else → Commit("IfThenElse_kw")
```

No nonterminal boundary, so the entire pattern lives in a single segment.

### Example 2: Rule with Nonterminal Boundary

**Rule:** `FloatCast: float ( Int )`

**Pattern elements:**

```
[Terminal("KwFloat"), Terminal("LParen"), NonTerminal("Int", 0x82), Terminal("RParen")]
```

**Encoding — Step 1 (prefix):**

```
encode_terminal_prefix(pattern)
  = ([id_float, id_lparen], Some(NTBoundaryInfo { category: "Int", position: 2, ... }))

  Segment 0 path: ┌──────────┬───────────┐
                  │ id_float │ id_lparen │
                  │   0x__   │   0x__    │
                  └──────────┴───────────┘
```

**Encoding — Step 2 (continuation):**

```
insert_nt_continuation(remaining = [Terminal("RParen")])
  → encode_terminal_prefix([Terminal("RParen")]) = ([id_rparen], None)

  Segment 1 path: ┌───────────┐
                  │ id_rparen │
                  │   0x__    │
                  └───────────┘
  Action: Commit("FloatCast")
```

### Example 3: Rule with IdentCapture

**Rule:** `Var: @ x` (where `x` is an identifier capture)

**Pattern elements:**

```
[Terminal("At"), IdentCapture { param_name: "x" }]
```

**Encoding:**

```
encode_terminal_prefix(pattern) = ([id_at, 0x80], None)

  Byte sequence: ┌───────┬──────┐
                 │ id_at │ 0x80 │
                 │ 0x__  │ IDENT│
                 └───────┴──────┘

  Trie path: id_at → 0x80 → Commit("Var")
```

The `0x80` byte acts as a wildcard that matches any `Ident` token at parse time. The
`param_name` ("x") is not encoded in the byte path — it is used only during code
generation to name the captured variable in the emitted Rust code.

### Example 4: Rule with BinderCapture

**Rule:** `Bind: for x in Expr` (where `x` is a binder capture)

**Pattern elements (prefix only):**

```
[Terminal("KwFor"), BinderCapture { param_name: "x" }, Terminal("KwIn"), NonTerminal("Expr", ...)]
```

**Encoding:**

```
encode_terminal_prefix(pattern)
  = ([id_for, 0x81, id_in], Some(NTBoundaryInfo { category: "Expr", ... }))

  Segment 0 path: ┌────────┬──────┬───────┐
                  │ id_for │ 0x81 │ id_in │
                  │  0x__  │BINDER│ 0x__  │
                  └────────┴──────┴───────┘
```

The `0x81` byte marks a binding position. Like `IDENT_CAPTURE`, it matches any `Ident`
token, but the code generator wraps the captured name in a `Binder(FreeVar(...))` during
AST construction.

### Example 5: Rule with Optional Group

**Rule:** `Opt: if [then]` (where `[then]` is optional)

**Pattern elements:**

```
[Terminal("KwIf"), OptionalStart, Terminal("KwThen"), OptionalEnd]
```

**Encoding:**

```
encode_terminal_prefix(pattern) = ([id_if, 0xC0, id_then, 0xC1], None)

  Byte sequence: ┌───────┬──────┬─────────┬──────┐
                 │ id_if │ 0xC0 │ id_then │ 0xC1 │
                 │ 0x__  │ OPT₀ │  0x__   │ OPT₁ │
                 └───────┴──────┴─────────┴──────┘

  Trie path: id_if → 0xC0 → id_then → 0xC1 → Commit("Opt")
```

The `OPTIONAL_START` (0xC0) and `OPTIONAL_END` (0xC1) markers bracket the optional group
in the byte path. During trie traversal at parse time, encountering `0xC0` signals that
the enclosed tokens may or may not be present; the dispatch logic forks to handle both the
present and absent cases.

---

## §7 Encoding Constraints

The byte-range partitioning imposes the following hard limits on grammar complexity:

### Maximum 128 Terminal Token IDs

The terminal range `0x00` .. `0x7F` provides 128 slots. Since `TokenIdMap` assigns IDs
sequentially from 0, any grammar with more than 128 distinct terminal token variants
cannot be fully represented in the decision tree encoding. In practice this ceiling is
rarely approached:

| Grammar Class       | Typical Terminal Count |
|---------------------|------------------------|
| Arithmetic (calc)   | 10 - 15                |
| Expression language | 20 - 40                |
| Full PL (Rholang)   | 60 - 80                |
| Maximum supported   | 128                    |

If a terminal's ID exceeds `MAX_TERMINAL_ID` (0x7F), the encoder skips that terminal and
falls back to non-decision-tree dispatch for rules containing it.

### Maximum 62 Nonterminal Categories

The nonterminal range `0x82` .. `0xBF` provides 62 category slots
(category_index ∈ {0, 1, ..., 61}). This is generous for practical grammars:

```
max_categories = 0xBF − 0x82 + 1 = 62
```

Typical grammar sizes:

| Grammar Class       | Typical Category Count |
|---------------------|------------------------|
| Arithmetic (calc)   | 1 - 3                  |
| Expression language | 3 - 8                  |
| Full PL (Rholang)   | 10 - 20                |
| Maximum supported   | 62                     |

### Optional Groups are Flattened

Optional groups `[...]` are encoded as flat byte sequences with bracket markers rather
than as nested sub-tries. The byte sequence for `[A B]` is `[0xC0, id_A, id_B, 0xC1]` —
the optional group structure is preserved solely by the start/end marker bytes. This
means:

- No additional trie depth is introduced by optionals beyond the markers themselves.
- Nested optionals (`[A [B]]`) produce `[0xC0, id_A, 0xC0, id_B, 0xC1, 0xC1]` —
  properly nested bracket pairs.
- The dispatch logic at parse time must track optional group depth to handle the
  present/absent forking correctly.

### Capture Markers are Fixed Bytes, Not Parameterized

Both `IDENT_CAPTURE` (0x80) and `BINDER_CAPTURE` (0x81) are single fixed bytes. They do
not encode which parameter name they capture or which variable index they correspond to.
This information is carried out-of-band in the `PatternElement` enum's `param_name` field
and used exclusively during code generation.

Consequence: if a rule has two ident captures (e.g., `Pair: @ x @ y`), both encode as
`0x80` in the byte path: `[id_at, 0x80, id_at, 0x80]`. The trie can still distinguish
this rule from one with a single capture because the path lengths differ, but it cannot
distinguish two rules that differ only in their capture parameter names — such rules would
be structurally identical and would (correctly) be flagged as ambiguous.

### Summary of Limits

| Resource               | Maximum | Byte Range   |
|------------------------|---------|--------------|
| Terminal token IDs     | 128     | 0x00 .. 0x7F |
| Nonterminal categories | 62      | 0x82 .. 0xBF |
| Capture marker types   | 2       | 0x80, 0x81   |
| Optional markers       | 2       | 0xC0, 0xC1   |
| Reserved (future)      | 62      | 0xC2 .. 0xFF |
