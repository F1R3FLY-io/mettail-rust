# Phase 6: Parser-Driven Lexing

> **Historical**: This document describes the `context-sensitive-lex` feature which was removed.
> The always-on WFST architecture now resolves all lexer ambiguities at compile time,
> making the runtime context-sensitive lexing infrastructure unnecessary.
> This document is retained for historical reference only.

**Date:** 2026-02-26

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
   - 1.1 [Keyword/Identifier Overlap](#11-keywordidentifier-overlap)
   - 1.2 [Cross-Category Token Ambiguity](#12-cross-category-token-ambiguity)
   - 1.3 [Why the Existing Layers Are Insufficient](#13-why-the-existing-layers-are-insufficient)
2. [Three-Layer Resolution Strategy](#2-three-layer-resolution-strategy)
   - 2.1 [Layer 1: Lexer Filter (FIRST-Set Bitset)](#21-layer-1-lexer-filter-first-set-bitset)
   - 2.2 [Layer 2: Parser Lookahead (2nd-Token Disambiguation)](#22-layer-2-parser-lookahead-2nd-token-disambiguation)
   - 2.3 [Layer 3: WFST Composition (Composed Dispatch Tables)](#23-layer-3-wfst-composition-composed-dispatch-tables)
   - 2.4 [How the Three Layers Interact](#24-how-the-three-layers-interact)
3. [Architecture Diagram](#3-architecture-diagram)
   - 3.1 [Codegen-Time Data Flow](#31-codegen-time-data-flow)
   - 3.2 [Runtime Data Flow](#32-runtime-data-flow)
   - 3.3 [Component Inventory](#33-component-inventory)
4. [How Composed Dispatch Eliminates Backtracking](#4-how-composed-dispatch-eliminates-backtracking)
   - 4.1 [Old Approach: Save/Restore Backtracking](#41-old-approach-saverestore-backtracking)
   - 4.2 [New Approach: Table-Driven O(1) Dispatch](#42-new-approach-table-driven-o1-dispatch)
   - 4.3 [Composed Dispatch Table Structure](#43-composed-dispatch-table-structure)
   - 4.4 [Worked Example: "error" as Keyword vs Identifier](#44-worked-example-error-as-keyword-vs-identifier)
   - 4.5 [Worked Example: Multi-Category Ident Dispatch](#45-worked-example-multi-category-ident-dispatch)
5. [Comparison with Alternatives](#5-comparison-with-alternatives)
   - 5.1 [Traditional Two-Phase (Lex-Then-Parse)](#51-traditional-two-phase-lex-then-parse)
   - 5.2 [Scannerless Parsing (PEG, Earley, GLL/GLR)](#52-scannerless-parsing-peg-earley-gllglr)
   - 5.3 [Flex/Bison Start Conditions](#53-flexbison-start-conditions)
   - 5.4 [PraTTaIL Phase 6](#54-prattail-phase-6)
   - 5.5 [Comparison Table](#55-comparison-table)
6. [Connection to Speech Recognition Pipeline](#6-connection-to-speech-recognition-pipeline)
   - 6.1 [The Speech Recognition WFST Cascade](#61-the-speech-recognition-wfst-cascade)
   - 6.2 [The PraTTaIL WFST Cascade](#62-the-prattail-wfst-cascade)
   - 6.3 [Formal Correspondence](#63-formal-correspondence)
   - 6.4 [What the Analogy Buys Us](#64-what-the-analogy-buys-us)
7. [Detailed Design: Codegen-Time Construction](#7-detailed-design-codegen-time-construction)
   - 7.1 [Multi-Accept DFA States](#71-multi-accept-dfa-states)
   - 7.2 [FIRST-Set Bitset Per Category](#72-first-set-bitset-per-category)
   - 7.3 [Composed Dispatch Table Construction](#73-composed-dispatch-table-construction)
   - 7.4 [Static Embedding in Generated Code](#74-static-embedding-in-generated-code)
8. [Detailed Design: Runtime Infrastructure](#8-detailed-design-runtime-infrastructure)
   - 8.1 [Lexer Struct](#81-lexer-struct)
   - 8.2 [LexerAdapter (Buffered Peek-Ahead)](#82-lexeradapter-buffered-peek-ahead)
   - 8.3 [Lazy Parser Entry Points](#83-lazy-parser-entry-points)
   - 8.4 [Category ID Constants](#84-category-id-constants)
9. [Correctness Argument](#9-correctness-argument)
   - 9.1 [Soundness: Every Accepted Parse Is Valid](#91-soundness-every-accepted-parse-is-valid)
   - 9.2 [Completeness: No Valid Parse Is Rejected](#92-completeness-no-valid-parse-is-rejected)
   - 9.3 [Determinism: At Most One Token Per Position Per Category](#93-determinism-at-most-one-token-per-position-per-category)
10. [Activation and Configuration](#10-activation-and-configuration)
    - 10.1 [DSL Options Block](#101-dsl-options-block)
    - 10.2 [Zero Overhead When Disabled](#102-zero-overhead-when-disabled)
    - 10.3 [Interaction with WFST Features](#103-interaction-with-wfst-features)

---

## 1. Problem Statement

PraTTaIL's existing six-layer disambiguation model (lexical, prediction,
precedence, cross-category, error recovery, semantic) resolves most parsing
ambiguities efficiently. However, one fundamental architectural limitation
remains: **the lexer operates without knowledge of which grammar category the
parser is currently trying to parse**. This creates two classes of ambiguity
that the current architecture handles with unnecessary backtracking.

### 1.1 Keyword/Identifier Overlap

Consider a grammar with an `error` keyword used in a comparison rule:

```
types:
  Proc
  Int (i32)
  Bool (bool)

rules:
  Compare . e1:Int, e2:Int |- e1 "error" e2 : Bool    (* cross-category *)
  PVar    : Proc                                        (* variable *)
  IVar    : Int                                         (* variable *)
  ...
```

The string `error` is simultaneously:
- A keyword `Token::KwError` when the parser is in a context expecting `Bool`
  (the `Compare` rule uses `"error"` as an infix operator)
- A valid identifier `Token::Ident("error")` when the parser is in a context
  expecting `Proc` (the `PVar` rule accepts any identifier)

The existing lexer (Layer 1) resolves this using token priority: `Fixed("error")`
has priority 10, `Ident` has priority 1, so `error` always lexes as the keyword.
This is correct when the parser needs the keyword, but **incorrect** when the
parser needs an identifier named `error`. The priority system is context-free --
it cannot distinguish these cases.

```
Input:  error handler       (* intended as identifier "error" then identifier "handler" *)
Lexer:  KwError  Ident("handler")    (* WRONG -- "error" became a keyword *)
```

### 1.2 Cross-Category Token Ambiguity

Even without keyword overlap, `Token::Ident` can start rules in multiple
categories:

```
FIRST(Int)  = {Integer, Ident, Minus}
FIRST(Bool) = {Boolean, Ident, Bang, Integer, Pipe, ...}
FIRST(Proc) = {Ident, EmptyBraces, Star, LBrace, Caret, ...}
```

When the parser sees `Ident("x")`, it cannot immediately determine which
category to parse. The current cross-category dispatch (Layer 4) handles this
by **backtracking**: save the lexer position, try parsing as one category, peek
for the expected operator, and if it fails, restore and try the next category.

For a grammar with `k` cross-category rules sharing an ambiguous token, the
parser performs up to `k` save/restore cycles per ambiguous token. While bounded,
this backtracking is avoidable if the lexer were told which category to prefer.

### 1.3 Why the Existing Layers Are Insufficient

The root cause is a **phase-ordering problem**: Layer 1 (lexical) makes
irrevocable tokenization decisions before Layer 2 (prediction) computes which
category is being parsed. By the time the parser knows it needs a `Proc`
expression (not a `Bool` expression), the lexer has already committed to
`KwError` instead of `Ident("error")`.

The existing layers attempt to compensate:
- **Layer 1 priority**: Cannot distinguish contexts; always picks the
  higher-priority token
- **Layer 2 dispatch tables**: Operate on already-tokenized input; cannot
  re-tokenize
- **Layer 4 backtracking**: Correct but performs redundant work; the parser
  re-lexes and re-parses the same input region

Parser-driven lexing solves this by **feeding parser context back to the lexer**
at tokenization time, so the lexer produces the contextually correct token on
the first attempt.

---

## 2. Three-Layer Resolution Strategy

Phase 6 introduces a three-layer disambiguation strategy that operates between
the existing lexer (Layer 1) and parser dispatch (Layer 2). Each successive
layer handles a narrower class of ambiguity.

### 2.1 Layer 1: Lexer Filter (FIRST-Set Bitset)

**Mechanism**: For each grammar category `C`, precompute a bitset `EXPECTED_C`
containing the token-kind IDs that appear in `FIRST(C)`. When the parser calls
`next_token_for_category(category_id)`, the lexer uses this bitset to filter
which DFA accept states are valid.

**What it resolves**: Tokens that are in one category's FIRST set but not
another's. For example, if `KwError` is in `FIRST(Bool)` but not in
`FIRST(Proc)`, then when parsing `Proc`, the lexer skips `KwError` and returns
`Ident("error")` instead.

**Complexity**: O(1) per token -- a single bitwise AND between the DFA accept
state's token-kind bitset and the category's FIRST-set bitset.

```
DFA accept state S:  { KwError (kind 5), Ident (kind 1) }
Parsing category Proc:  EXPECTED_PROC = { Ident, EmptyBraces, Star, ... }

Filter:  { KwError, Ident } AND EXPECTED_PROC = { Ident }
Result:  Token::Ident("error")    (* contextually correct *)
```

### 2.2 Layer 2: Parser Lookahead (2nd-Token Disambiguation)

**Mechanism**: When the FIRST-set filter leaves multiple valid token kinds (e.g.,
both `Ident` and a keyword are in `FIRST(C)`), the parser peeks at the second
token to disambiguate, using the same lookahead machinery already in Layer 2's
`DispatchAction::Lookahead`.

**What it resolves**: Cases where the same token kind appears in multiple rules
within a single category, distinguished by the following token. For example,
`Ident` followed by `!` triggers `POutput`, while `Ident` followed by anything
else triggers `PVar`.

**Complexity**: O(1) -- one additional token peek.

### 2.3 Layer 3: WFST Composition (Composed Dispatch Tables)

**Mechanism**: For DFA accept states that remain ambiguous after FIRST-set
filtering (multiple token kinds map to the same DFA state and are all in the
current category's FIRST set), a **composed dispatch table** provides the unique
best `(token_kind, rule_label, weight)` triple.

The composed table is the result of WFST composition between the lexer's
multi-accept DFA and the prediction WFST:

```
Composed Table:  TABLE[category_id][dfa_state] -> &[(kind_id, rule_label, weight)]
```

Each entry is pre-sorted by weight (tropical: lower = better). The parser takes
the first entry, which is the best-weighted disambiguation.

**What it resolves**: Residual ambiguity that FIRST-set filtering and lookahead
cannot resolve. This includes cases where a DFA state simultaneously accepts
a keyword and an identifier, both of which are in the current category's
FIRST set, but one is the contextually preferred interpretation.

**Complexity**: O(1) -- array index into a static table, take the first element.

### 2.4 How the Three Layers Interact

The three layers form a cascade, each handling what the previous layer could not:

```
  Token Position
       │
       ▼
  ┌─────────────────────────────────────────────────────────┐
  │  FIRST-Set Bitset Filter                                │
  │                                                         │
  │  DFA accept: {KwError, Ident}                           │
  │  Category:   Proc                                       │
  │  EXPECTED:   {Ident, EmptyBraces, ...}  (no KwError)    │
  │                                                         │
  │  Filter result: exactly one kind?                       │
  │    YES ──────────────────────────────────────────► DONE │
  │    NO ──► still ambiguous                               │
  └──────────────────────────┬──────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────┐
  │  Parser Lookahead (2nd token)                           │
  │                                                         │
  │  Peek next token:                                       │
  │    Unique match? ──────────────────────────────► DONE   │
  │    Still ambiguous? ──► fall through                    │
  └──────────────────────────┬──────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────┐
  │  Composed Dispatch Table                                │
  │                                                         │
  │  TABLE[Proc][dfa_state=7] = [(Ident, "PVar", 0.0)]      │
  │                                                         │
  │  Take first entry ────────────────────────────► DONE    │
  └─────────────────────────────────────────────────────────┘
```

The key property is **monotonic narrowing**: each layer can only eliminate
candidates, never add them. Layer 1 (FIRST-set filter) eliminates token kinds
not in the category. Layer 2 (lookahead) eliminates rules that do not match the
second token. Layer 3 (composed dispatch) selects the best remaining candidate.
The process always terminates with exactly one token kind and one rule.

---

## 3. Architecture Diagram

### 3.1 Codegen-Time Data Flow

The codegen-time pipeline constructs all static tables that the runtime uses for
O(1) dispatch. This work happens inside the `language!` proc-macro expansion.

```
                        LanguageSpec
                            │
              ┌─────────────┴─────────────┐
              │                           │
              ▼                           ▼
    ┌────────────────────┐       ┌─────────────────────────────┐
    │  Lexer Pipeline    │       │  Parser Pipeline            │
    │                    │       │                             │
    │  Terminals ──► NFA │       │  Rules ──► FIRST sets       │
    │  NFA ──► DFA       │       │  FIRST ──► DispatchTable    │
    │  DFA ──► Minimize  │       │  FIRST ──► Overlaps         │
    │  DFA ──► EquivCls  │       │                             │
    │                    │       │  ┌───────────────────────┐  │
    │  Multi-accept      │       │  │  PredictionWfst       │  │
    │  DFA states ──►    │       │  │  (per category,       │  │
    │  AmbiguityInfo     │       │  │   token ──► actions   │  │
    │                    │       │  │   with weights)       │  │
    └────────┬───────────┘       │  └──────────┬────────────┘  │
             │                   └─────────────┊───────────────┘
             │                                 │
             └───────────────┬─────────────────┘
                             │
                             ▼
              ┌───────────────────────────────┐
              │  WFST Composition             │
              │                               │
              │  For each ambiguous DFA state │
              │  S with accept set A(S):      │
              │                               │
              │  For each category C:         │
              │    EXPECTED_C ∩ A(S) ──►      │
              │    score by PredictionWfst    │
              │    ──► sort by weight         │
              │    ──► ComposedEntry          │
              │                               │
              │  Result: BTreeMap<            │
              │    (category, dfa_state),     │
              │    Vec<ComposedEntry>         │
              │  >                            │
              └──────────────┬────────────────┘
                             │
                             ▼
              ┌──────────────────────────────┐
              │  Static Embedding            │
              │                              │
              │  CATEGORY_ID_PROC: u8 = 0    │
              │  CATEGORY_ID_INT:  u8 = 1    │
              │  CATEGORY_ID_BOOL: u8 = 2    │
              │                              │
              │  EXPECTED_PROC: &str = "..." │
              │  EXPECTED_INT:  &str = "..." │
              │  EXPECTED_BOOL: &str = "..." │
              │                              │
              │  fn composed_dispatch(       │
              │    cat_id: u8,               │
              │    dfa_state: u32            │
              │  ) -> &[(u8, &str, f64)]     │
              │                              │
              │  Lexer<'a> struct            │
              │  LexerAdapter<'a> struct     │
              │  parse_Cat_lazy() fns        │
              └──────────────────────────────┘
```

### 3.2 Runtime Data Flow

At parse time, the generated code uses the precomputed tables for O(1) dispatch.

```
                     Input: "error == 3"
                            │
                            ▼
  ┌──────────────────────────────────────────────────────────────────────┐
  │  Parser: parse_Bool_lazy()                                           │
  │                                                                      │
  │  adapter.set_category(CATEGORY_ID_BOOL)                              │
  │                                                                      │
  └───────────────────────────────┬──────────────────────────────────────┘
                                  │
  ┌───────────────────────────────▼──────────────────────────────────────┐
  │  LexerAdapter.peek()                                                 │
  │                                                                      │
  │  ┌─────────────────────────────────────────────────────────────────┐ │
  │  │  Lexer.next_token_for_category(CATEGORY_ID_BOOL)                │ │
  │  │                                                                 │ │
  │  │  1. Run DFA on "error"                                          │ │
  │  │     DFA reaches state S with accept = {KwError, Ident}          │ │
  │  │                                                                 │ │
  │  │  2. composed_dispatch(CATEGORY_ID_BOOL, S)                      │ │
  │  │     Returns: [(KwError, "Compare", 0.0)]                        │ │
  │  │     (* KwError is in FIRST(Bool) for the Compare rule *)        │ │
  │  │                                                                 │ │
  │  │  3. accept_token_by_kind(S, "error", kind_id=KwError)           │ │
  │  │     Returns: Token::KwError                                     │ │
  │  └─────────────────────────────────────────────────────────────────┘ │
  │                                                                      │
  │  Result: Token::KwError with range [0..5]                            │
  └───────────────────────────────┬──────────────────────────────────────┘
                                  │
  ┌───────────────────────────────▼──────────────────────────────────────┐
  │  Parser dispatch: KwError ──► Compare rule                           │
  │  parse_Int(), expect KwError, parse_Int() ──► Bool::Compare(...)     │
  └──────────────────────────────────────────────────────────────────────┘
```

Contrast with the same input parsed as `Proc`:

```
  Parser: parse_Proc_lazy()
  adapter.set_category(CATEGORY_ID_PROC)

  Lexer.next_token_for_category(CATEGORY_ID_PROC):
    DFA state S: accept = {KwError, Ident}
    composed_dispatch(CATEGORY_ID_PROC, S):
      Returns: [(Ident, "PVar", 0.0)]
      (* KwError is NOT in FIRST(Proc); Ident IS *)
    accept_token_by_kind(S, "error", kind_id=Ident):
      Returns: Token::Ident("error")

  Parser dispatch: Ident ──► PVar rule
  Result: Proc::PVar("error")
```

The **same five characters** produce different tokens depending on parser
context. No backtracking, no save/restore. O(1) per token.

### 3.3 Component Inventory

| Component                                | Location              | Phase   | Description                             |
|------------------------------------------|-----------------------|---------|-----------------------------------------|
| `AmbiguityInfo`                          | `automata/codegen.rs` | Codegen | DFA states with multiple accept tokens  |
| `TokenVariantMap`                        | `automata/codegen.rs` | Codegen | Maps token names to numeric kind IDs    |
| `compute_composed_dispatch()`            | `prediction.rs`       | Codegen | FIRST-set x DFA-state composition       |
| `emit_composed_dispatch_table()`         | `prediction.rs`       | Codegen | Emits `composed_dispatch()` function    |
| `write_lexer_struct()`                   | `automata/codegen.rs` | Codegen | Emits `Lexer<'a>` struct                |
| `write_lexer_adapter()`                  | `automata/codegen.rs` | Codegen | Emits `LexerAdapter<'a>` struct         |
| `write_accept_token_by_kind()`           | `automata/codegen.rs` | Codegen | Emits `accept_token_by_kind()` function |
| `write_expected_category_descriptions()` | `automata/codegen.rs` | Codegen | Emits `EXPECTED_<CAT>` constants        |
| `write_trampolined_parser_lazy()`        | `trampoline.rs`       | Codegen | Emits `parse_Cat_lazy()` functions      |
| `Lexer<'a>`                              | Generated             | Runtime | Incremental lexer with category context |
| `LexerAdapter<'a>`                       | Generated             | Runtime | Buffered peek-ahead wrapper             |
| `composed_dispatch()`                    | Generated             | Runtime | Static dispatch table lookup            |
| `accept_token_by_kind()`                 | Generated             | Runtime | Token construction by kind ID           |
| `parse_Cat_lazy()`                       | Generated             | Runtime | Category parser using adapter           |
| `parse_context_sensitive()`              | Generated             | Runtime | Top-level entry point                   |

---

## 4. How Composed Dispatch Eliminates Backtracking

### 4.1 Old Approach: Save/Restore Backtracking

Without parser-driven lexing, cross-category dispatch uses the save/restore
pattern from Layer 4 (see `dispatch.rs`, `write_category_dispatch()`):

```rust
/* Inside parse_Bool dispatcher */
Token::Ident(_) => {
    /* Ident is in BOTH FIRST(Int) and FIRST(Bool) -- ambiguous */
    let saved = *pos;

    /* Try cross-category: parse as Int, then look for "==" */
    if let Ok(left) = parse_Int(tokens, pos, 0) {
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::EqEq)) {
            *pos += 1;  /* consume "==" */
            let right = parse_Int(tokens, pos, 0)?;
            return Ok(Bool::Eq(Box::new(left), Box::new(right)));
        }
    }

    /* Cross-category failed -- restore and try own category */
    *pos = saved;
    parse_Bool_own(tokens, pos, min_bp)
}
```

**Cost**: For `k` cross-category rules, up to `k` full sub-expression parses
are attempted and discarded before the correct path is found. Each discarded
parse re-lexes tokens that were already processed.

### 4.2 New Approach: Table-Driven O(1) Dispatch

With parser-driven lexing, the `composed_dispatch()` table tells the parser
which interpretation to use before parsing begins:

```rust
/* Inside parse_Bool_lazy() */
let (token, range) = adapter.peek();  /* context-aware: category = Bool */
match token {
    Token::KwError => {
        /* composed_dispatch already selected KwError for Bool context */
        /* Deterministic: proceed with Compare rule */
        let left = parse_Int_lazy(adapter, 0)?;
        adapter.expect(Token::KwError)?;
        let right = parse_Int_lazy(adapter, 0)?;
        Ok(Bool::Compare(Box::new(left), Box::new(right)))
    }
    Token::Ident(_) => {
        /* Ident was returned because this context expects Bool variables */
        parse_Bool_own_lazy(adapter, min_bp)
    }
    /* ... */
}
```

**Cost**: O(1) per token. The `composed_dispatch()` lookup is a constant-time
array index. No sub-expression parsing is performed speculatively.

### 4.3 Composed Dispatch Table Structure

The composed dispatch table is a function mapping `(category_id, dfa_state)` to
a sorted list of `(kind_id, rule_label, weight)` triples:

```rust
fn composed_dispatch(category_id: u8, dfa_state: u32) -> &'static [(u8, &'static str, f64)] {
    match (category_id, dfa_state) {
        (CATEGORY_ID_BOOL, 7) => &[
            (5, "Compare", 0.0),   /* KwError, weight 0.0 (best) */
        ],
        (CATEGORY_ID_PROC, 7) => &[
            (1, "PVar", 0.0),      /* Ident, weight 0.0 (best) */
        ],
        (CATEGORY_ID_INT, 7) => &[
            (1, "IVar", 0.25),     /* Ident, weight 0.25 */
        ],
        _ => &[],  /* no disambiguation needed */
    }
}
```

**Key properties**:

1. **Deterministic**: Each `(category, state)` pair maps to exactly one sorted
   list. The first entry is always the best.

2. **Sparse**: Only ambiguous DFA states appear in the table. Unambiguous states
   (single accept token) return `&[]`, and the standard `accept_token()` path is
   used.

3. **Precomputed**: All composition work happens at compile time. Runtime cost is
   a match on two integers.

### 4.4 Worked Example: "error" as Keyword vs Identifier

Grammar:
```
Compare . e1:Int, e2:Int |- e1 "error" e2 : Bool
PVar    : Proc    (* variable, accepts any Ident *)
IVar    : Int     (* variable, accepts any Ident *)
```

DFA state after reading `e-r-r-o-r` (followed by whitespace):
```
State S_error:
  Accept set: { Fixed("error") = KwError (priority 10),
                Ident (priority 1) }
```

FIRST sets:
```
FIRST(Bool) = { Boolean, Ident, Bang, KwError, Integer, ... }
FIRST(Proc) = { Ident, EmptyBraces, Star, ... }     (* no KwError *)
FIRST(Int)  = { Integer, Ident, Minus, ... }         (* no KwError *)
```

Composed dispatch table construction:
```
For state S_error, accept = {KwError, Ident}:

  Category Bool:
    KwError in FIRST(Bool)? YES  ──► include: (KwError, "Compare", 0.0)
    Ident in FIRST(Bool)?   YES  ──► include: (Ident, "BVar", 2.0)
    Sorted: [(KwError, "Compare", 0.0), (Ident, "BVar", 2.0)]

  Category Proc:
    KwError in FIRST(Proc)? NO   ──► exclude
    Ident in FIRST(Proc)?   YES  ──► include: (Ident, "PVar", 0.0)
    Sorted: [(Ident, "PVar", 0.0)]

  Category Int:
    KwError in FIRST(Int)?  NO   ──► exclude
    Ident in FIRST(Int)?    YES  ──► include: (Ident, "IVar", 0.25)
    Sorted: [(Ident, "IVar", 0.25)]
```

Runtime behavior:
```
Input: "error == 3"

  Parsing Bool:  composed_dispatch(Bool, S_error) = [(KwError, ...)]
                 ──► Token::KwError ──► Compare rule ──► Bool::Compare(...)

  Parsing Proc:  composed_dispatch(Proc, S_error) = [(Ident, ...)]
                 ──► Token::Ident("error") ──► PVar rule ──► Proc::PVar("error")

  Parsing Int:   composed_dispatch(Int, S_error) = [(Ident, ...)]
                 ──► Token::Ident("error") ──► IVar rule ──► Int::IVar("error")
```

### 4.5 Worked Example: Multi-Category Ident Dispatch

Consider parsing `x == y` where `x` and `y` are identifiers:

**Without** parser-driven lexing (existing Layer 4):
```
1. parse_Bool(pos=0):
   Token = Ident("x"). Ident is ambiguous (in FIRST(Int) and FIRST(Bool)).
2. Save pos=0.
3. Try parse_Int(pos=0): IVar("x"). Peek: EqEq. Match!
4. Consume EqEq. parse_Int(pos=2): IVar("y").
5. Construct Bool::Eq(IVar("x"), IVar("y")).

Cost: 1 save + 1 speculative Int parse + 1 peek = O(n) for the Int sub-parse.
```

**With** parser-driven lexing:
```
1. parse_Bool_lazy(adapter):
   adapter.set_category(CATEGORY_ID_BOOL).
   adapter.peek() invokes next_token_for_category(CATEGORY_ID_BOOL).
   DFA state for "x": Ident (unambiguous, single accept).
   composed_dispatch returns &[] (no disambiguation needed).
   Token = Ident("x").
2. Dispatch table: Ident is ambiguous in Bool → Lookahead.
   Peek second token: EqEq. Match Compare rule.
3. parse_Int_lazy(adapter, 0): adapter.set_category(CATEGORY_ID_INT). IVar("x").
4. Expect KwEqEq. parse_Int_lazy(adapter, 0): IVar("y").
5. Construct Bool::Eq(IVar("x"), IVar("y")).

Cost: 0 saves, 0 speculative parses, 1 peek = O(1) for dispatch.
```

For single-accept DFA states (like the state for identifiers), the two approaches
have similar cost. The savings come from multi-accept states (keyword/identifier
overlap) and from eliminating backtracking in cross-category dispatch for those
states.

---

## 5. Comparison with Alternatives

### 5.1 Traditional Two-Phase (Lex-Then-Parse)

The standard approach in tools like Flex/Bison, LALRPOP, and most hand-written
parsers: the lexer runs to completion first, producing a flat token array, then
the parser consumes it.

**Strengths**:
- Simple architecture; clean separation of concerns
- Lexer can be optimized independently (DFA, SIMD, etc.)
- Token array enables random-access lookahead

**Weaknesses**:
- Context information is lost at the lexer-parser boundary
- Keywords must be reserved globally (cannot be used as identifiers in any
  context)
- All cross-category ambiguity must be resolved by the parser via backtracking

**Where PraTTaIL was before Phase 6**: Two-phase with bounded backtracking.
The lexer produces a flat `Vec<(Token<'a>, Span)>`, and the parser indexes into
it. Cross-category ambiguity is handled by Layer 4's save/restore pattern.

### 5.2 Scannerless Parsing (PEG, Earley, GLL/GLR)

Scannerless parsers interleave character-level and grammar-level decisions.
There is no separate lexer; the grammar itself specifies character patterns.

**Strengths**:
- No lexer-parser phase boundary; context is always available
- Keywords are naturally context-sensitive (only recognized where the grammar
  expects them)
- Compositional grammars (no global keyword reservation)

**Weaknesses**:
- **PEG**: Ordered choice hides ambiguity; greedy matching can cause surprising
  behavior; O(n) space for packrat memoization
- **Earley**: O(n^3) worst-case time; practical implementations are O(n^2) for
  ambiguous grammars
- **GLL/GLR**: Can produce parse forests (exponential in size for highly
  ambiguous grammars); SPPF traversal is complex
- All approaches: no DFA-based lexer optimization; character-by-character
  matching is slower than batch DFA lexing

### 5.3 Flex/Bison Start Conditions

Flex (and re2c) support **start conditions**: named lexer states that enable or
disable pattern rules. The parser can switch the lexer's start condition to
change which tokens are recognized.

```lex
%x STRING_MODE
%%
<INITIAL>"error"   return KW_ERROR;
<INITIAL>[a-z]+    return IDENT;
<STRING_MODE>[^"]*  return STRING_CONTENT;
```

**Strengths**:
- Context sensitivity without abandoning DFA-based lexing
- Established technique with decades of tooling support

**Weaknesses**:
- Start conditions are manually defined and switched; no automatic derivation
  from the grammar
- The number of conditions can explode for multi-category grammars (one per
  category combination)
- No weighted disambiguation; when multiple tokens match in a start condition,
  the first rule wins (order-dependent)
- Cannot express "prefer keyword in category A, prefer identifier in category B"
  without separate start conditions for each

### 5.4 PraTTaIL Phase 6

PraTTaIL's parser-driven lexing takes a different approach: the DFA remains
a single, universal automaton that recognizes all tokens simultaneously, but
the **accept decision** is conditioned on parser context.

**Strengths**:
- **Single DFA**: No start conditions, no state explosion. The same DFA handles
  all categories. Only the accept filter changes.
- **Automatic derivation**: FIRST sets and composed dispatch tables are computed
  automatically from the grammar. No manual specification.
- **Weighted disambiguation**: When multiple tokens match in the same category,
  WFST weights (from rule specificity, declaration order, or training data)
  break ties. This is principled, not order-dependent.
- **O(1) dispatch**: The composed dispatch table provides constant-time lookup.
  No backtracking, no speculative parsing.
- **Composed dispatch always on, CSL feature-gated**: The composed dispatch
  table is always computed at codegen time and used by the standard `parse()`
  path for deterministic dispatch (no backtracking). The runtime CSL
  infrastructure (Lexer, LexerAdapter, lazy parsers) is feature-gated behind
  `context-sensitive-lex` and only emitted when enabled.

**Weaknesses**:
- Additional compile-time complexity (composed dispatch table construction)
- When `context-sensitive-lex` is enabled: slightly larger generated code
  (Lexer struct, LexerAdapter, dispatch tables, lazy parser functions)
- The `wfst` feature is needed for full weighted disambiguation; without it,
  FIRST-set filtering with priority-based weighting is used as a fallback

### 5.5 Comparison Table

```
┌─────────────────────────┬───────────┬─────────────┬───────────────┬─────────────────┐
│                         │ Two-Phase │ Scannerless │ Start         │ PraTTaIL        │
│                         │ (Lex/Parse│ (PEG/       │ Conditions    │ Phase 6         │
│                         │  )        │  Earley/GLL)│ (Flex/re2c)   │                 │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Context at lex time     │ None      │ Full        │ Manual states │ Automatic       │
│                         │           │ (no lexer)  │               │ (FIRST sets)    │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ DFA-based lexing        │ Yes       │ No          │ Yes           │ Yes (single     │
│                         │           │             │ (per state)   │  universal DFA) │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Keyword context         │ Global    │ Local       │ Per start     │ Per category    │
│ sensitivity             │ reserved  │ (grammar    │ condition     │ (automatic)     │
│                         │           │  rules)     │ (manual)      │                 │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Disambiguation          │ Priority  │ Ordered     │ First rule    │ WFST weights    │
│ method                  │ (fixed)   │ choice/     │ wins          │ (trainable)     │
│                         │           │ parse forest│               │                 │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Backtracking            │ Bounded   │ None (PEG:  │ None          │ None            │
│                         │ save/     │ memoized)   │               │ (table-driven)  │
│                         │ restore   │ or forests  │               │                 │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Parse-time complexity   │ O(n) +    │ PEG: O(n)   │ O(n)          │ O(n)            │
│ (per token)             │ O(k)      │ Earley:     │               │                 │
│                         │ backtrack │ O(n^2)-O(n^3│               │                 │
│                         │           │ )           │               │                 │
├─────────────────────────┼───────────┼─────────────┼───────────────┼─────────────────┤
│ Always-on infrastructure│ N/A       │ N/A         │ N/A           │ Yes (default)   │
│ with dual entry points  │           │             │               │                 │
└─────────────────────────┴───────────┴─────────────┴───────────────┴─────────────────┘
```

---

## 6. Connection to Speech Recognition Pipeline

The mathematical framework underlying PraTTaIL's parser-driven lexing is the
same one used in speech recognition: **weighted finite-state transducer (WFST)
composition**. This is not a superficial analogy -- the operations are
algebraically identical, applied to different input domains.

### 6.1 The Speech Recognition WFST Cascade

In the Mohri-Pereira-Riley framework (1996, 2002), speech recognition decodes
acoustic signals into word sequences by composing three transducers:

```
  Acoustic Signal
       │
       ▼
  ┌───────────────────┐
  │  H: Acoustic      │   HMM states ──► phone labels
  │     Model         │   Weight: P(observation | phone state)
  └────────┬──────────┘
           │
           ▼
  ┌───────────────────┐
  │  C: Pronunciation │   Phone sequences ──► word labels
  │     Model         │   Weight: P(pronunciation | word)
  └────────┬──────────┘
           │
           ▼
  ┌───────────────────┐
  │  G: Language      │   Word sequences ──► sentences
  │     Model         │   Weight: P(word sequence) from n-gram LM
  └────────┬──────────┘
           │
           ▼
  Decoded Word Sequence
```

The decoding network is the **composition** `H ∘ C ∘ G`: a single WFST that maps
acoustic observations directly to word sequences. Composition precomputes all
intermediate decisions, so at runtime the decoder makes a single Viterbi pass
through the composed transducer.

### 6.2 The PraTTaIL WFST Cascade

PraTTaIL's parser-driven lexing composes two transducers:

```
  Character Sequence
       │
       ▼
  ┌───────────────────┐
  │  L: Lexer WFST    │   Characters ──► token kinds
  │                   │   Weight: TokenKind::priority()
  │                   │   States: DFA states (after minimization)
  │                   │   Accept: multi-accept (keyword + ident, etc.)
  └────────┬──────────┘
           │
           ▼
  ┌───────────────────┐
  │  P: Prediction    │   Token kinds ──► parse rules
  │     WFST          │   Weight: rule specificity / training weight
  │                   │   States: per-category dispatch states
  │                   │   Accept: dispatch actions
  └────────┬──────────┘
           │
           ▼
  Parse Rule Selection
  (token kind + rule label + weight)
```

The **composed dispatch table** is the precomputed `L ∘ P`: a single table that
maps `(category, dfa_state)` directly to `(token_kind, rule, weight)`. Like
speech recognition's `H ∘ C ∘ G`, this eliminates intermediate decisions at
runtime.

### 6.3 Formal Correspondence

The correspondence between the two domains is precise:

```
┌───────────────────────┬───────────────────────────┬───────────────────────────┐
│ Concept               │ Speech Recognition        │ PraTTaIL                  │
├───────────────────────┼───────────────────────────┼───────────────────────────┤
│ Input signal          │ Acoustic feature vectors  │ Character sequence        │
│ First transducer      │ H (Acoustic model)        │ L (Lexer DFA)             │
│ Intermediate labels   │ Phone labels              │ Token kinds               │
│ Second transducer     │ C (Pronunciation model)   │ P (Prediction WFST)       │
│ Output labels         │ Word labels               │ Parse rule labels         │
│ Third transducer      │ G (Language model)        │ (not needed -- grammar    │
│                       │                           │  is finite)               │
│ Composition           │ H ∘ C ∘ G                 │ L ∘ P                     │
│ Runtime operation     │ Viterbi best path         │ Table lookup [cat][state] │
│ Semiring              │ Tropical (min, +, inf, 0) │ Tropical (min, +, inf, 0) │
│ Weight interpretation │ -log P(observation|phone) │ -log P(rule|token,cat)    │
│ Training              │ EM (Baum-Welch)           │ SGD on parse examples     │
│ Pruning               │ Beam search               │ BeamWidthConfig           │
└───────────────────────┴───────────────────────────┴───────────────────────────┘
```

### 6.4 What the Analogy Buys Us

Using the WFST framework for parser-driven lexing provides several concrete
benefits beyond the conceptual elegance:

1. **Composition algorithm**: The `compute_composed_dispatch()` function is a
   direct implementation of WFST pointwise composition (restricted to ambiguous
   states only, since unambiguous states have trivial composition). The
   algorithm's correctness follows from the standard WFST composition theorem
   (Mohri, 2009): the composed transducer accepts exactly the intersection of
   the component transducers' path sets, with weights combined via the semiring's
   multiplication.

2. **Weight training**: The `wfst-log` feature enables log-semiring SGD training
   (see `training.rs`), which learns rule weights from parse examples. This is
   the exact analogue of acoustic model training in speech recognition. The
   trained weights flow into the composed dispatch table, improving disambiguation
   for real-world input distributions.

3. **Beam pruning**: The `BeamWidthConfig` option (when combined with the `wfst`
   feature) prunes low-weight alternatives during composition, limiting the
   table size. This is identical to beam search pruning in speech recognition
   decoders.

4. **Forward-backward analysis**: The `forward_backward.rs` module (gated under
   `wfst-log`) computes expected rule usage across all paths through the
   prediction WFST, exactly as the forward-backward algorithm computes expected
   state occupancy in HMMs. This enables gradient-based weight training.

5. **Theoretical guarantees**: The WFST framework provides a formal proof that
   composition preserves the best-path property under the tropical semiring:
   the best `(token, rule)` pair in the composed table is the globally optimal
   pair, not merely a locally greedy choice.

---

## 7. Detailed Design: Codegen-Time Construction

### 7.1 Multi-Accept DFA States

After NFA-to-DFA conversion and Hopcroft minimization, some DFA states accept
multiple token kinds simultaneously. This occurs when the DFA merges states from
different NFA paths that converge on the same character sequence.

The `LexerAmbiguityInfo` struct (in `automata/codegen.rs`) records which states
are multi-accept:

```rust
pub struct LexerAmbiguityInfo {
    pub has_ambiguous: bool,
    pub ambiguous_states: Vec<(StateId, Vec<(TokenKind, TropicalWeight)>)>,
}
```

Each ambiguous state carries its set of possible `(TokenKind, weight)` pairs,
where the weight is derived from `TokenKind::priority()` converted to the
tropical semiring:

```
  Ident      → priority 1  → tropical weight 9.0  (10 - 1)
  KwError    → priority 10 → tropical weight 0.0  (10 - 10)
```

The tropical weight reversal ensures that higher-priority tokens have lower
(better) tropical weights.

### 7.2 FIRST-Set Bitset Per Category

For each category, a FIRST-set bitset is computed by `compute_first_sets()`
(in `prediction.rs`), augmented with native literal tokens (Integer for `i32`,
Boolean for `bool`, etc.), and then stored as a set of token variant names.

During composed dispatch construction, this set is used as a filter: only token
kinds that appear in the current category's FIRST set are considered valid
interpretations of an ambiguous DFA state.

### 7.3 Composed Dispatch Table Construction

The `compute_composed_dispatch()` function (in `prediction.rs`) performs the
WFST composition. For each `(ambiguous_state, category)` pair:

```
COMPUTE_COMPOSED_DISPATCH(ambiguous_states, categories, first_sets, variant_map, rule_infos):
  table = BTreeMap::new()

  for each (state, accept_set) in ambiguous_states:
    for each category C in categories:
      first_C = first_sets[C]
      entries = []

      for each (kind, weight) in accept_set:
        kind_name = variant_map.id_to_name[kind]
        if kind_name in first_C.tokens:
          /* This token kind is valid for category C */
          rule = find_best_rule(kind_name, C, rule_infos)
          specificity = compute_rule_specificity(rule)
          combined_weight = weight + specificity   /* tropical multiplication = addition */
          entries.push(ComposedEntry { kind_name, rule, combined_weight })

      if entries is not empty:
        entries.sort_by(|a, b| a.weight.partial_cmp(&b.weight))
        table[(C, state)] = entries

  return table
```

**Rule specificity** is computed from the rule's syntax pattern:
- Rules with more terminal tokens in their syntax have higher specificity
  (lower weight), because they are less likely to match by accident
- Variable rules have the lowest specificity (highest weight)
- The formula counts the fraction of syntax items that are terminals:
  `specificity = (terminal_count / total_items) * (terminal_count / total_items)`

### 7.4 Static Embedding in Generated Code

The composed dispatch table is emitted as a Rust function with static array
literals:

```rust
const CATEGORY_ID_PROC: u8 = 0;
const CATEGORY_ID_INT:  u8 = 1;
const CATEGORY_ID_BOOL: u8 = 2;

fn composed_dispatch(category_id: u8, dfa_state: u32) -> &'static [(u8, &'static str, f64)] {
    match (category_id, dfa_state) {
        (0, 7) => &[(1, "PVar", 0.0)],          /* Proc, state 7: Ident */
        (2, 7) => &[(5, "Compare", 0.0),         /* Bool, state 7: KwError (best) */
                     (1, "BVar", 2.0)],           /*                Ident (fallback) */
        _ => &[],
    }
}
```

Properties of the emitted code:
- **No heap allocation**: All entries are `&'static` array references
- **Deterministic ordering**: BTreeMap iteration ensures reproducible output
- **Sparse**: Only `(category, state)` pairs with actual entries appear
- **Fallback**: `_ => &[]` handles all unambiguous cases (zero-cost path)

---

## 8. Detailed Design: Runtime Infrastructure

### 8.1 Lexer Struct

The `Lexer<'a>` struct provides incremental (token-at-a-time) lexing, as opposed
to the batch `lex()` function that eagerly tokenizes the entire input:

```rust
pub struct Lexer<'a> {
    input: &'a str,
    bytes: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
    file_id: Option<u32>,
}
```

Two methods:
- `next_token()`: Unfiltered DFA lexing, identical to the inner loop of `lex()`.
  Uses `accept_token(state, text)` for unambiguous states.
- `next_token_for_category(category_id)`: Context-aware lexing. Runs the same
  DFA but consults `composed_dispatch(category_id, accept_state)` for ambiguous
  states. If the dispatch returns a non-empty list, uses
  `accept_token_by_kind(state, text, kind_id)` to construct the token with the
  preferred kind.

The DFA execution loop is identical in both methods -- only the accept decision
differs. This means the character-level performance (DFA transitions, maximal
munch, equivalence classes) is unchanged.

### 8.2 LexerAdapter (Buffered Peek-Ahead)

The `LexerAdapter<'a>` wraps a `Lexer<'a>` with a small token buffer for
peek-ahead and category-aware disambiguation:

```rust
pub struct LexerAdapter<'a> {
    lexer: Lexer<'a>,
    buf: Vec<(Token<'a>, Range)>,   /* preallocated capacity: 4 */
    cursor: usize,
    category_id: u8,
    lex_error: Option<String>,
}
```

The adapter provides:
- `set_category(id)`: Sets the category context for subsequent lex calls.
  Called by `parse_Cat_lazy()` before lexing begins.
- `peek()` / `peek_range()`: Returns the current token without consuming it.
  Lazily fills the buffer via `ensure_buffered()`.
- `peek_ahead(n)`: Returns the token `n` positions ahead.
- `advance()`: Moves the cursor past the current token.
- `expect(token)`: Asserts the current token matches, then advances.
- `take_error()`: Extracts any stored lex error for propagation.

The buffer uses `ensure_buffered()` to lazily lex tokens on demand:
- If `category_id > 0`, uses `next_token_for_category(category_id)` for
  context-aware lexing
- If `category_id == 0`, uses `next_token()` for unfiltered lexing
- Lex errors are captured and stored; subsequent peeks return `Token::Eof`

### 8.3 Lazy Parser Entry Points

For each category `C`, a `parse_C_lazy()` function is generated that uses the
`LexerAdapter` instead of the pre-lexed token array:

```rust
fn parse_Bool_lazy<'a>(
    adapter: &mut LexerAdapter<'a>,
    min_bp: u8,
) -> Result<Bool, ParseError> {
    /* Set category context for context-sensitive lexing */
    adapter.set_category(CATEGORY_ID_BOOL);

    /* ... trampolined parser using adapter.peek(), adapter.advance(), etc. ... */
}
```

The lazy parser mirrors the structure of the standard trampolined parser
(`parse_Cat()`) but replaces `tokens[*pos]` lookups with `adapter.peek()` calls
and `*pos += 1` with `adapter.advance()`.

### 8.4 Category ID Constants

Each category receives a unique `u8` identifier, emitted as a constant:

```rust
const CATEGORY_ID_PROC: u8 = 0;
const CATEGORY_ID_INT:  u8 = 1;
const CATEGORY_ID_BOOL: u8 = 2;
```

These constants index into the composed dispatch table and the
`expected_for_category()` helper. The assignment order follows the category
declaration order in the grammar.

---

## 9. Correctness Argument

### 9.1 Soundness: Every Accepted Parse Is Valid

**Claim**: If `parse_Cat_lazy()` returns `Ok(ast)`, then `ast` is a valid parse
tree according to the grammar.

**Argument**: The lazy parser uses the same dispatch tables, binding power
comparisons, and rule application logic as the standard parser. The only
difference is the token source: `LexerAdapter` instead of `tokens[pos]`. The
adapter returns tokens from the same DFA, with the same maximal munch semantics.
The composed dispatch table only filters the accept decision -- it cannot
introduce tokens that the DFA did not match. Therefore, the token stream seen by
the lazy parser is a subset of what the standard lexer would produce, and every
token in it is a valid DFA match.

Since the parser logic is identical and the token stream is a valid subset, any
parse tree produced by the lazy parser is also producible by the standard parser
(possibly after different cross-category backtracking choices). Soundness of the
standard parser implies soundness of the lazy parser.

### 9.2 Completeness: No Valid Parse Is Rejected

**Claim**: If the standard parser returns `Ok(ast)` for input `s` in category
`C`, then `parse_C_lazy()` also returns `Ok(ast')` where `ast'` is structurally
equivalent.

**Argument**: The composed dispatch table includes every token kind that is in
`FIRST(C)`. If a token kind `k` is needed to start a valid parse in category
`C`, then `k` is in `FIRST(C)`, and the composed dispatch table includes `k`
for every DFA state that accepts it. Therefore, the context-aware lexer will
return `k` whenever the standard lexer would (and the standard parser would use
it for category `C`).

The one subtlety is priority resolution: the standard lexer always picks the
highest-priority token, regardless of context. If the highest-priority token is
NOT in `FIRST(C)` but a lower-priority token IS, the standard lexer returns the
wrong token for category `C`, causing the standard parser to fall through to
backtracking. The context-aware lexer returns the correct (lower-priority) token
directly, avoiding the backtracking. Both paths ultimately parse the same input,
producing structurally equivalent ASTs.

### 9.3 Determinism: At Most One Token Per Position Per Category

**Claim**: For a given input position and category, `next_token_for_category()`
returns exactly one token.

**Argument**: The DFA is deterministic (each input character maps to exactly one
next state). Maximal munch produces exactly one accept state. The composed
dispatch table maps `(category, state)` to a sorted list; the first entry is
selected. Since the DFA state, the category, and the selection rule (first entry)
are all deterministic, the result is deterministic.

---

## 10. Activation and Configuration

### 10.1 Composed Dispatch (Always On)

The composed dispatch table is **always** computed at code generation time for
every grammar, regardless of feature flags. This table resolves ambiguous
`(category, token)` pairs into deterministic match arms, eliminating save/restore
backtracking from the standard `parse()` path.

The standard batch `parse()` path benefits from composed dispatch with zero
runtime overhead — the resolution happens entirely at codegen time. The generated
`match` arms are deterministic: no `let saved = *pos` / `*pos = saved`.

### 10.2 Context-Sensitive Lex Infrastructure (Feature-Gated)

The runtime infrastructure for parser-driven lexing is **feature-gated** behind
`context-sensitive-lex`:

```toml
[features]
context-sensitive-lex = ["mettail-macros/context-sensitive-lex"]
```

When the `context-sensitive-lex` feature is enabled, the generated code includes:
- `Lexer<'a>` struct with `next_token()` and `next_token_for_category()`
- `LexerAdapter<'a>` with buffered peek-ahead
- `composed_dispatch()` runtime function (if ambiguous DFA states exist)
- `accept_token_by_kind()` function
- `CATEGORY_ID_*` constants
- `EXPECTED_*` description constants
- `parse_Cat_lazy()` functions for each category
- `Cat::parse_context_sensitive(input)` entry point methods

When the feature is **disabled** (default), none of this infrastructure is
emitted — saving ~2,000-4,000 lines per grammar and eliminating icache pollution.

### 10.3 Dual Entry Points

| Entry Point                           | Lexing Strategy                     | Feature Required        | Use Case                                       |
|---------------------------------------|-------------------------------------|-------------------------|------------------------------------------------|
| `Cat::parse(input)`                   | Batch lex (all tokens up front)     | None (always available) | Standard parsing, maximum throughput           |
| `Cat::parse_context_sensitive(input)` | Parser-driven (one token at a time) | `context-sensitive-lex` | Ambiguous grammars, context-dependent keywords |

The standard `parse()` path uses the composed dispatch resolutions at codegen
time, so ambiguous tokens are handled deterministically without backtracking.
The `parse_context_sensitive()` path uses the `Lexer` struct and `LexerAdapter`
for incremental, context-aware tokenization with runtime dispatch.

### 10.4 Interaction with WFST Features

The composed dispatch table uses different weight sources depending on the
`wfst-log` feature gate. WFST-weighted dispatch is always active.

| Configuration         | Weight Source                       | Disambiguation Quality             |
|-----------------------|-------------------------------------|------------------------------------|
| Default (no features) | Priority + rule specificity         | Good (always-on WFST)              |
| `wfst-log`            | Trained weights from `TrainedModel` | Best (learned from parse examples) |

The `compute_composed_dispatch()` function always produces WFST-weighted dispatch
tables using FIRST-set filtering, priority-based weights, and rule specificity
scoring. The `wfst-log` feature enables loading trained weights from a
`TrainedModel` binary file, which adjusts the composed dispatch weights based on
corpus statistics.

Both configurations produce correct results. The feature flag controls
disambiguation **quality** (which interpretation is preferred when multiple are
valid), not correctness.

---

## 11. End-to-End Runtime Flow

This section traces a complete parse through the context-sensitive lexing path,
from the user's `Cat::parse_context_sensitive(input)` call to the final AST
node, illustrating how the parser, lexer, and disambiguation layers interact.

### 11.1 Invocation and Initialization

```
User code                           Generated code
─────────                           ──────────────
Cat::parse_context_sensitive(input)
    │
    ├─→ Lexer::new(input, None)           /* DFA state = 0, offset = 0 */
    ├─→ LexerAdapter::new(lexer)          /* buffer = [], category = 0 */
    └─→ parse_Cat_lazy(&mut adapter, 0)   /* min_bp = 0 */
```

The `LexerAdapter` wraps the `Lexer` in a peek-ahead buffer (capacity 4). It
maintains the current grammatical category so the lexer can disambiguate
context-sensitive tokens.

### 11.2 Token Request Cycle

Each time the lazy parser needs a token (via `adapter.peek()` or
`adapter.advance()`), the following chain executes:

```
parse_Cat_lazy                     LexerAdapter                  Lexer
──────────────                     ────────────                  ─────
  adapter.set_category(cat_id)  ─→ self.category = cat_id
  adapter.peek()                ─→ if buffer empty:
                                      fill_buffer()
                                   ─→ lexer.next_token_for_category(cat_id)
                                                                ─→ run DFA from current offset
                                                                   ┌───────────────────────────┐
                                                                   │ DFA state ∈ ambiguous?    │
                                                                   │ ┌─ No:  accept_token()    │
                                                                   │ └─ Yes: composed_dispatch │
                                                                   │         (cat_id, state)   │
                                                                   │         → accept_by_kind  │
                                                                   └───────────────────────────┘
                                   ← (Token, Range)
                                   store in buffer[0]
                                ← &Token
```

### 11.3 Disambiguation at Ambiguous DFA States

When the DFA reaches an ambiguous accepting state (multiple token kinds
valid), the composed dispatch table resolves the ambiguity in O(1):

```
                  composed_dispatch(category_id, dfa_state)
                           │
                           ▼
              ┌───────────────────────────┐
              │ Static match table:       │
              │ (cat, state) → &[Entry]   │
              │                           │
              │ Entry {                   │
              │   token_kind_id: u8,      │
              │   rule_id: u16,           │
              │   weight: W               │    W = TropicalWeight (default)
              │ }                         │        or LogWeight (wfst-log)
              └───────────────────────────┘
                           │
                           ▼
              Select entry with best weight
              (tropical: min; log: max exp)
                           │
                           ▼
              accept_token_by_kind(kind_id)
              → Token variant determined
                by parser context
```

### 11.4 Complete Parse Trace Example

Consider parsing `"int(3.14)"` in a grammar with both `Int` and `Float`
categories, where `int` is the keyword for cast-to-integer:

```
Step   Parser State              Adapter Action           Lexer / DFA
────   ────────────              ──────────────           ───────────
 1     parse_Int_lazy(0)         set_category(INT_ID)
 2       peek()                  fill → next_token_for_category(INT_ID)
                                                          DFA: "int" → state 42 (ambig: KwInt|Ident)
                                                          composed_dispatch(INT_ID, 42) → KwInt
                                                          accept_by_kind(KwInt) → Token::KwInt
 3       match Token::KwInt      advance()                buffer consumed
 4       peek()                  fill → next_token_for_category(INT_ID)
                                                          DFA: "(" → state 5 (unambig)
                                                          accept_token() → Token::LParen
 5       match Token::LParen     advance()
 6     parse_Float_lazy(0)       set_category(FLOAT_ID)
 7       peek()                  fill → next_token_for_category(FLOAT_ID)
                                                          DFA: "3.14" → state 18 (unambig)
                                                          accept_token() → Token::Float(3.14)
 8       match Token::Float      advance()                val = 3.14
 9       ← Float::NumLit(3.14)
10     back in parse_Int_lazy    peek()
                                                          DFA: ")" → unambig → Token::RParen
11       match Token::RParen     advance()
12     ← Int::FloatToInt(Float::NumLit(3.14))
```

Key observations:
- Step 2: The lexer disambiguates `"int"` as `KwInt` (not `Ident`) because
  the parser is in the `Int` category, and the composed dispatch table maps
  `(INT_ID, state 42)` → `KwInt`.
- Step 6: When the parser enters `parse_Float_lazy`, it sets the category to
  `FLOAT_ID` before requesting tokens, ensuring correct disambiguation in
  the float sub-expression.
- Steps 4, 7, 10: Unambiguous tokens (`(`, `3.14`, `)`) take the fast
  `accept_token()` path with no dispatch table lookup.

### 11.5 Relationship Between Entry Points

```
                        ┌──────────────────────────────────┐
                        │          language! { ... }       │
                        └────────────┬─────────────────────┘
                                     │ macro expansion
                          ┌──────────┴──────────┐
                          ▼                     ▼
                 Cat::parse(input)    Cat::parse_context_sensitive(input)
                          │                     │
                          ▼                     ▼
                   lex(input)            Lexer::new(input)
                      → Vec<(Token,Range)>    + LexerAdapter
                          │                     │
                          ▼                     ▼
                  parse_Cat(tokens,pos)  parse_Cat_lazy(adapter,0)
                  ┌───────────────┐     ┌───────────────┐
                  │ Trampolined   │     │ Recursive     │
                  │ (Frame stack) │     │ descent       │
                  │ Array-indexed │     │ Adapter-based │
                  │ Backtracking  │     │ No backtrack  │
                  └───────┬───────┘     └───────┬───────┘
                          │                     │
                          └──────────┬──────────┘
                                     ▼
                                  Cat (AST)
```

Both paths produce identical AST results. The standard path is optimal for
grammars without lexer ambiguity. The context-sensitive path eliminates
backtracking at the cost of call-stack-based recursion depth.
