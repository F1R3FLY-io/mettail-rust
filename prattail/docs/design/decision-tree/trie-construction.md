# PraTTaIL Decision Tree — Trie Construction

| Metadata | Value                                                                               |
|----------|-------------------------------------------------------------------------------------|
| Date     | 2026-03-06                                                                          |
| Updated  | 2026-03-06                                                                          |
| Source   | `prattail/src/decision_tree.rs` (L349-707), `prattail/src/pipeline.rs` (L1650-1713) |

---

## Table of Contents

- [§1 Overview](#1-overview)
- [§2 Rule Classification](#2-rule-classification)
- [§3 Insertion Algorithm — RD Rules](#3-insertion-algorithm--rd-rules)
- [§4 Segment Splitting at NT Boundaries](#4-segment-splitting-at-nt-boundaries)
- [§5 Insertion Algorithm — Cross-Category Rules](#5-insertion-algorithm--cross-category-rules)
- [§6 Insertion Algorithm — Cast Rules](#6-insertion-algorithm--cast-rules)
- [§7 PathMap pjoin Merge for Ambiguous Prefixes](#7-pathmap-pjoin-merge-for-ambiguous-prefixes)
- [§8 Worked Example](#8-worked-example)
- [§9 PathMap API Usage](#9-pathmap-api-usage)
- [§10 Correctness Invariants](#10-correctness-invariants)

---

## §1 Overview

Trie construction is **Phase 1** of the decision tree pipeline.  The
`DecisionTreeBuilder` (defined at `decision_tree.rs:349`) constructs one
`PathMap<DecisionAction>` trie per syntactic category from the grammar's rules.
The trie is built after FIRST sets and dead rules have been computed in the
pipeline (`pipeline.rs:1650-1713`).

The construction processes three rule classes in strict sequence:

```
  ┌─────────────────────────────────────────────────────┐
  │              DecisionTreeBuilder::build_all()       │
  │                                                     │
  │  Step 1: insert_rd_rules()          (L504-558)      │
  │            │                                        │
  │            ▼                                        │
  │  Step 2: insert_cross_category_rules()  (L592-630)  │
  │            │                                        │
  │            ▼                                        │
  │  Step 3: insert_cast_rules()        (L633-668)      │
  │            │                                        │
  │            ▼                                        │
  │  Step 4: compute_statistics()       (L817-864)      │
  └─────────────────────────────────────────────────────┘
```

Each step adds byte-encoded paths to the per-category PathMap.  When two rules
map to the same path, PathMap's `Lattice::pjoin` merges them into an
`Ambiguous` action.

---

## §2 Rule Classification

The builder classifies each rule before deciding whether and how to insert it
into the trie.

### §2.1 RD Rules (Recursive-Descent)

Terminal-first rules whose first item is a `Terminal` keyword or punctuation
token.  These are the primary candidates for trie dispatch.

**Skip conditions** (L505-521):

| Condition                                     | Reason                                             |
|-----------------------------------------------|----------------------------------------------------|
| `dead_rules.contains(label)`                  | Dead rules are excluded from the trie              |
| `rule.is_collection`                          | Collections use standalone functions               |
| `rule.prefix_bp.is_some()`                    | Unary prefix rules are handled by Pratt            |
| First item is `NonTerminal` or `IdentCapture` | Not terminal-first; cannot dispatch on first token |
| Empty pattern after conversion                | Unconvertible items (e.g., `SepList`, `Map`)       |

### §2.2 Cross-Category Rules

Infix rules whose left operand is a nonterminal from a different category.
For a rule `result_cat: <source_cat> OP ...`, the dispatch token is not the
operator `OP` directly but rather the FIRST set of `source_cat`.

### §2.3 Cast Rules

Implicit coercions from a source category to a target category.  Dispatch
is on tokens unique to the source's FIRST set that are not in the target's
FIRST set (i.e., `FIRST(source) \ FIRST(target)`).

---

## §3 Insertion Algorithm — RD Rules

The RD rule insertion (`insert_rd_rules`, L504-558) proceeds in four stages
for each qualifying rule:

### §3.1 Pattern Conversion

`pattern_from_rd_rule()` (L401-457) converts an `RDRuleInfo`'s syntax items to
a `Vec<PatternElement>`:

```
  RDSyntaxItem::Terminal("if")       →  PatternElement::Terminal { variant: "KwIf", id: 0x0C }
  RDSyntaxItem::IdentCapture { "x" } →  PatternElement::IdentCapture { param_name: "x" }
  RDSyntaxItem::Binder { "x", .. }   →  PatternElement::BinderCapture { param_name: "x" }
  RDSyntaxItem::NonTerminal { "Int" } →  PatternElement::NonTerminal { category: "Int", category_id: 0 }
  RDSyntaxItem::Optional { inner }    →  [OptionalStart, ...inner..., OptionalEnd]
```

Complex constructs (`Collection`, `Sep`, `Map`, `Zip`, `SepList`,
`BinderCollection`) cause a `break` — items after them are not encoded because
these constructs require standalone handler functions.

### §3.2 Terminal Prefix Encoding

`encode_terminal_prefix()` (L461-486) walks the pattern left-to-right, pushing
one byte per element.  Upon encountering a `NonTerminal`, it stops and returns
the accumulated bytes plus an `NTBoundaryInfo` descriptor:

```
  encode_terminal_prefix(pattern) → (bytes: Vec<u8>, boundary: Option<NTBoundaryInfo>)
```

The encoding follows the byte-space partitioning defined in the
[bytecode specification](bytecode-specification.md):

```
  0x00..0x7F   Terminal token IDs
  0x80         IDENT_CAPTURE
  0x81         BINDER_CAPTURE
  0x82..0xBF   NonTerminal category IDs (triggers segment split)
  0xC0         OPTIONAL_START
  0xC1         OPTIONAL_END
```

### §3.3 Root Segment Insertion

The encoded prefix bytes are inserted into segment 0 (root segment) of the
category's `CategoryDecisionTree`.  If an existing action is already stored at
the same path, `pjoin` merges them:

```rust
if let Some(existing) = tree.segments[0].get(&prefix_bytes) {
    let merged = existing.pjoin(&action);     // Lattice merge
    tree.segments[0].insert(&prefix_bytes, merged);
} else {
    tree.segments[0].insert(&prefix_bytes, action);
}
```

### §3.4 Continuation Segment (if NT boundary present)

If `encode_terminal_prefix` returned a boundary, `insert_nt_continuation()`
(L561-589) is called to handle the remaining pattern after the nonterminal.
See [§4](#4-segment-splitting-at-nt-boundaries).

---

## §4 Segment Splitting at NT Boundaries

The trie cannot inline all possible expansions of a nonterminal — doing so
would cause exponential blowup.  Instead, the trie is **split at nonterminal
boundaries** into linked segments.

### §4.1 Protocol

```
  Rule pattern: [T₁, T₂, NT₃, T₄, T₅]
                  │   │    ▲    │   │
                  │   │  split  │   │
                  └───┘  point  └───┘
                segment 0     segment k
```

1. `encode_terminal_prefix` encodes `[T₁, T₂]` and returns an
   `NTBoundaryInfo` recording `NT₃`'s category, position, and the remaining
   items `[T₄, T₅]`.

2. The prefix `[T₁, T₂]` is inserted into segment 0 with a `Commit` action.

3. `insert_nt_continuation()` allocates a new segment k, encodes `[T₄, T₅]`
   as the continuation's prefix, and inserts that into segment k with a
   `Commit` action pointing to the original rule.

4. `stats.nonterminal_boundaries` is incremented.

### §4.2 NTBoundaryInfo Structure

```rust
pub struct NTBoundaryInfo {
    pub category: String,              // nonterminal's category name
    pub category_id: u8,               // 0x82 + category_index
    pub remaining_pattern: Vec<PatternElement>,  // items after the NT
    pub position: usize,               // index of the NT in original pattern
}
```

### §4.3 Multiple Boundaries

If the remaining pattern after one nonterminal contains another nonterminal,
`encode_terminal_prefix` on the continuation will itself stop at the second
boundary.  The current implementation encodes only the continuation's terminal
prefix (L573: `Self::encode_terminal_prefix(&boundary.remaining_pattern)`),
which naturally handles nested boundaries by producing shorter continuation
segments.

### §4.4 Segment Linking Diagram

Consider a rule `ForLoop: for x in Expr do Stmt end`:

```
  Pattern: [Terminal("for"), BinderCapture("x"), Terminal("in"),
            NonTerminal("Expr"), Terminal("do"), NonTerminal("Stmt"), Terminal("end")]

  ┌─ Segment 0 (root) ───────────────────────────────────────────┐
  │  Path: [id_for, 0x81, id_in]                                 │
  │  Action: Commit("ForLoop")                                   │
  │  Boundary: NT("Expr") at position 3                          │
  │            resume_segment = 1                                │
  └──────────────────────────────────────────────────────────────┘
               │
               ▼ after parsing Expr sub-expression
  ┌─ Segment 1 (continuation) ───────────────────────────────────┐
  │  Path: [id_do]                                               │
  │  Boundary: NT("Stmt") at position 0 (relative)               │
  │            resume_segment = 2                                │
  └──────────────────────────────────────────────────────────────┘
               │
               ▼ after parsing Stmt sub-expression
  ┌─ Segment 2 (continuation) ───────────────────────────────────┐
  │  Path: [id_end]                                              │
  │  Action: Commit("ForLoop")                                   │
  └──────────────────────────────────────────────────────────────┘
```

---

## §5 Insertion Algorithm — Cross-Category Rules

`insert_cross_category_rules()` (L592-630) handles infix rules that cross
category boundaries.

### §5.1 Path Structure

For a cross-category rule `R: <S> OP ...` where `S` is the source category,
`OP` is the operator token, and `R` goes into the result category:

```
  Path = [FIRST(S)_token, OP_id]
```

The builder iterates over every token in `FIRST(S)` and inserts a two-byte
path `[tok_id, op_id]` into R's trie.

### §5.2 Algorithm

```
for rule in cross_rules:
    if rule.label in dead_rules: continue
    op_id ← encode_terminal(terminal_to_variant_name(rule.operator))
    for token in FIRST(rule.source_category).tokens:
        tok_id ← encode_terminal(terminal_to_variant_name(token))
        path ← [tok_id, op_id]
        action ← Commit { rule_label: rule.label, category: rule.result_category }
        insert_or_merge(result_category.segments[0], path, action)
```

### §5.3 Example

Given `Comparison: <Expr> == <Expr>` and `FIRST(Expr) = { Integer, Ident, LParen }`:

```
  Trie insertions into Comparison's root segment:
    [id_Integer, id_EqEq] → Commit("CmpEq")
    [id_Ident,   id_EqEq] → Commit("CmpEq")
    [id_LParen,  id_EqEq] → Commit("CmpEq")
```

Each FIRST token of the source category fans out to a separate path.

---

## §6 Insertion Algorithm — Cast Rules

`insert_cast_rules()` (L633-668) handles implicit coercions.

### §6.1 Unique Token Computation

For a cast from source S to target T, the relevant dispatch tokens are those
in `FIRST(S)` that are **not** in `FIRST(T)`:

```
  unique_tokens = FIRST(S) \ FIRST(T)
```

This difference is computed via `FirstSet::difference()` (L642).

### §6.2 Path Structure

Each unique token produces a single-byte path:

```
  Path = [tok_id]
```

### §6.3 Algorithm

```
for rule in cast_rules:
    if rule.label in dead_rules: continue
    source_first ← first_sets[rule.source_category]
    target_first ← first_sets[rule.target_category]
    unique ← source_first.difference(target_first)
    for token in unique.tokens:
        tok_id ← encode_terminal(terminal_to_variant_name(token))
        path ← [tok_id]
        action ← Commit { rule_label: rule.label, category: rule.target_category }
        insert_or_merge(target_category.segments[0], path, action)
```

### §6.4 Example

Given `CastIntToFloat` with `FIRST(Int) = { Integer, Ident, LParen }` and
`FIRST(Float) = { KwFloat, Ident, LParen }`:

```
  unique = FIRST(Int) \ FIRST(Float) = { Integer }

  Trie insertion into Float's root segment:
    [id_Integer] → Commit("CastIntToFloat")
```

Only `Integer` is unique to Int — `Ident` and `LParen` appear in both FIRST
sets and would cause ambiguity if inserted.

---

## §7 PathMap pjoin Merge for Ambiguous Prefixes

When two rules map to the same byte path, the PathMap's `Lattice::pjoin`
implementation on `DecisionAction` (L139-176) merges them.

### §7.1 Merge Rules

```
  pjoin(Commit(A), Commit(B))       = Ambiguous { candidates: [A, B] }
  pjoin(Ambiguous(cs), Commit(B))   = Ambiguous { candidates: cs ++ [B] }
  pjoin(Commit(A), Ambiguous(cs))   = Ambiguous { candidates: [A] ++ cs }
  pjoin(Ambiguous(cs₁), Ambiguous(cs₂)) = Ambiguous { candidates: cs₁ ++ cs₂ }
  pjoin(NonterminalBoundary, _)     = Identity(1)   // boundary wins
  pjoin(_, NonterminalBoundary)     = Identity(2)   // boundary wins
```

### §7.2 Semantic Interpretation

| Merge Result                     | Meaning                                                                       |
|----------------------------------|-------------------------------------------------------------------------------|
| `Commit` (no merge needed)       | Unique path — deterministic dispatch                                          |
| `Ambiguous` (after merge)        | Path conflict — NFA try-all required at this prefix                           |
| `NonterminalBoundary` (identity) | NT boundary is preserved; alternatives become candidates in the NT resolution |

### §7.3 Example: Ambiguous Prefix

Rules `FloatId: float ( <Ident> )` and `IntToFloat: float ( <Int> )` both
encode prefix `[id_float, id_lparen]`.  When `IntToFloat`'s prefix is
inserted, the existing `Commit("FloatId")` is merged:

```
  Before: segments[0].get([id_float, id_lparen]) = Commit("FloatId")
  Insert: Commit("IntToFloat") at [id_float, id_lparen]
  After:  segments[0].get([id_float, id_lparen]) = Ambiguous {
            candidates: [
              { rule_label: "FloatId",   weight: 0.0, remaining: 0 },
              { rule_label: "IntToFloat", weight: 0.0, remaining: 0 },
            ]
          }
```

Note: `FloatId` also has a deeper path `[id_float, id_lparen, 0x80]` from its
`IDENT_CAPTURE` byte.  The ambiguity at depth 2 indicates that the parser
cannot decide between the two rules without looking past the `(` token.

---

## §8 Worked Example

This section builds a complete trie from a grammar with three categories and
five rules.

### §8.1 Grammar Definition

```
Category: Stmt
  IfThenElse:  if <Expr> then <Stmt> else <Stmt>
  LetIn:       let x = <Expr> in <Stmt>

Category: Expr
  FloatCast:   float ( <Int> )
```

Token ID assignments (alphabetical sort):

| Variant   | Raw     | Byte ID |
|-----------|---------|---------|
| `Eq`      | `=`     | 0x00    |
| `KwElse`  | `else`  | 0x01    |
| `KwFloat` | `float` | 0x02    |
| `KwIf`    | `if`    | 0x03    |
| `KwIn`    | `in`    | 0x04    |
| `KwLet`   | `let`   | 0x05    |
| `KwThen`  | `then`  | 0x06    |
| `LParen`  | `(`     | 0x07    |
| `RParen`  | `)`     | 0x08    |

Category ID assignments: `Stmt = 0`, `Expr = 1`, `Int = 2`.

### §8.2 Pattern Encoding

**Rule: IfThenElse**

```
  Items: [Terminal("if"), NonTerminal("Expr"), Terminal("then"),
          NonTerminal("Stmt"), Terminal("else"), NonTerminal("Stmt")]

  encode_terminal_prefix →
    bytes:    [0x03]          (only "KwIf" before the first NT)
    boundary: NTBoundaryInfo {
                category: "Expr",
                category_id: 1,
                remaining: [Terminal("then"), NT("Stmt"), Terminal("else"), NT("Stmt")],
                position: 1
              }
```

**Rule: LetIn**

```
  Items: [Terminal("let"), IdentCapture("x"), Terminal("="),
          NonTerminal("Expr"), Terminal("in"), NonTerminal("Stmt")]

  encode_terminal_prefix →
    bytes:    [0x05, 0x80, 0x00]   ("KwLet", IDENT_CAPTURE, "Eq")
    boundary: NTBoundaryInfo {
                category: "Expr",
                category_id: 1,
                remaining: [Terminal("in"), NT("Stmt")],
                position: 3
              }
```

**Rule: FloatCast**

```
  Items: [Terminal("float"), Terminal("("), NonTerminal("Int"), Terminal(")")]

  encode_terminal_prefix →
    bytes:    [0x02, 0x07]    ("KwFloat", "LParen")
    boundary: NTBoundaryInfo {
                category: "Int",
                category_id: 2,
                remaining: [Terminal(")")],
                position: 2
              }
```

### §8.3 Trie Construction — Stmt Category

```
insert_rd_rules:

  IfThenElse:
    Root segment insert: path [0x03] → Commit("IfThenElse", weight=0.0)
    Continuation segment 1: encode [Terminal("then"), NT("Stmt"), ...]
      → bytes [0x06], boundary at NT("Stmt")
      → Segment 1 insert: path [0x06] → Commit("IfThenElse")
      → Continuation segment 2: encode [Terminal("else"), NT("Stmt")]
        → bytes [0x01], boundary at NT("Stmt")
        → Segment 2 insert: path [0x01] → Commit("IfThenElse")

  LetIn:
    Root segment insert: path [0x05, 0x80, 0x00] → Commit("LetIn", weight=0.0)
    Continuation segment 3: encode [Terminal("in"), NT("Stmt")]
      → bytes [0x04], boundary at NT("Stmt")
      → Segment 3 insert: path [0x04] → Commit("LetIn")
```

Resulting Stmt trie:

```
  Segment 0 (root):
  ╔═══════════════════════════════╗
  ║ [0x03]              → Commit  ║──── IfThenElse
  ║ [0x05, 0x80, 0x00]  → Commit  ║──── LetIn
  ╚═══════════════════════════════╝

  Segment 1 (IfThenElse after Expr):
  ╔═══════════════════════════════╗
  ║ [0x06]              → Commit  ║──── IfThenElse
  ╚═══════════════════════════════╝

  Segment 2 (IfThenElse after Stmt₁):
  ╔═══════════════════════════════╗
  ║ [0x01]              → Commit  ║──── IfThenElse
  ╚═══════════════════════════════╝

  Segment 3 (LetIn after Expr):
  ╔═══════════════════════════════╗
  ║ [0x04]              → Commit  ║──── LetIn
  ╚═══════════════════════════════╝
```

### §8.4 Trie Construction — Expr Category

```
insert_rd_rules:

  FloatCast:
    Root segment insert: path [0x02, 0x07] → Commit("FloatCast", weight=0.0)
    Continuation segment 1: encode [Terminal(")")]
      → bytes [0x08], no boundary
      → Segment 1 insert: path [0x08] → Commit("FloatCast")
```

Resulting Expr trie:

```
  Segment 0 (root):
  ╔═══════════════════════════════╗
  ║ [0x02, 0x07]        → Commit  ║──── FloatCast
  ╚═══════════════════════════════╝

  Segment 1 (FloatCast after Int):
  ╔═══════════════════════════════╗
  ║ [0x08]              → Commit  ║──── FloatCast
  ╚═══════════════════════════════╝
```

### §8.5 Trie Diagram (Stmt, Root Segment)

```
                            ROOT
                           ╱    ╲
                      0x03         0x05
                     (if)          (let)
                       │             │
                    COMMIT          0x80
                  IfThenElse     (IDENT_CAPTURE)
                                     │
                                    0x00
                                    (=)
                                     │
                                  COMMIT
                                   LetIn
```

### §8.6 Dispatch Query

`dispatch_strategy("KwIf", token_ids)` on the Stmt trie:

1. Look up `KwIf` → byte `0x03`.
2. Collect all paths starting with `0x03` → one entry: `[0x03] → Commit("IfThenElse")`.
3. Single entry, action is `Commit` → return `Singleton { rule_label: "IfThenElse" }`.

`dispatch_strategy("KwLet", token_ids)` on the Stmt trie:

1. Look up `KwLet` → byte `0x05`.
2. Collect all paths starting with `0x05` → one entry: `[0x05, 0x80, 0x00] → Commit("LetIn")`.
3. Single entry, action is `Commit` → return `Singleton { rule_label: "LetIn" }`.

Both dispatches are deterministic — no backtracking needed.

---

## §9 PathMap API Usage

The builder uses three PathMap operations:

### §9.1 `insert(path, value)`

Inserts a value at the given byte path.  If the path already contains a value,
the builder explicitly checks with `get()` first and uses `pjoin` to merge.

```rust
// From insert_rd_rules (L542-551):
if let Some(existing) = tree.segments[0].get(&prefix_bytes) {
    let merged = match existing.pjoin(&action) {
        AlgebraicResult::Element(merged) => merged,
        AlgebraicResult::Identity(_) => existing.clone(),
        AlgebraicResult::None => action,
    };
    tree.segments[0].insert(&prefix_bytes, merged);
} else {
    tree.segments[0].insert(&prefix_bytes, action);
}
```

### §9.2 `get(path) -> Option<&V>`

Retrieves the value at an exact path.  Used during insertion to detect
conflicts and during querying (`dispatch_strategy`, `query_dispatch_token`).

### §9.3 `iter() -> impl Iterator<Item = (Vec<u8>, &V)>`

Iterates all (path, value) pairs in the trie.  Used pervasively:
- `dispatch_strategy()` filters paths by first byte
- `dispatch_tokens()` collects unique first bytes
- `compute_statistics()` counts nodes by action type
- All analysis layers iterate to find ambiguities and dead rules

### §9.4 `is_empty() -> bool`

Checks whether the trie has any entries.  Used as a guard in emission and
analysis functions to short-circuit empty trees.

---

## §10 Correctness Invariants

The following invariants are maintained throughout trie construction:

### §10.1 Dead Rule Exclusion

Dead rules (from WFST dead-rule detection) are excluded at insertion time:

```
∀ rule ∈ dead_rules: ¬∃ path ∈ trie s.t. action(path).rule_label = rule.label
```

### §10.2 Segment Monotonicity

Segments are only appended, never modified or reordered:

```
∀ i, j: i < j ⟹ segment[i] was created before segment[j]
```

Segment 0 is always the root.  Segments 1..n are continuation segments in
creation order.

### §10.3 Encoding Bijectivity (within a segment)

Within a single segment, the byte encoding of a rule's terminal prefix is
unique up to the first nonterminal boundary.  Two rules that produce the same
byte path are detected and merged via `pjoin`.

### §10.4 pjoin Commutativity

The merge operation is commutative: `pjoin(A, B) = pjoin(B, A)` (both produce
an `Ambiguous` with the same candidate set, modulo ordering).  Insertion order
of rules does not affect the final trie structure — only the candidate ordering
within `Ambiguous` nodes may differ.

### §10.5 Terminal ID Ceiling

No terminal with ID > `MAX_TERMINAL_ID` (0x7F) is inserted into the trie.
If a terminal exceeds this ceiling (grammar has > 128 distinct terminals),
it is silently skipped and the rule falls back to non-decision-tree dispatch.

```
∀ byte ∈ path ∈ trie: byte ≤ 0x7F ∨ byte ∈ {0x80, 0x81, 0xC0, 0xC1}
```

(NonTerminal bytes `0x82..0xBF` do not appear in paths because the trie
splits at NT boundaries rather than encoding them inline.)
