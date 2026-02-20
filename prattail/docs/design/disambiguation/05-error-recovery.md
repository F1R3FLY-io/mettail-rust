# Layer 5: Error Recovery

Error recovery is the fifth layer in PraTTaIL's six-layer model. It
activates **only when Layers 1-4 fail to produce a valid parse** and determines
where the parser should resume after a syntax error, preventing error cascades
that would obscure the original problem.

**Source files:**
- `prattail/src/prediction.rs` -- `generate_sync_predicate()` (lines 1019-1094),
  `compute_follow_sets()` (lines 260-340)

**Cross-references:**
- [theory/prediction-and-lookahead.md](../../theory/prediction-and-lookahead.md) §3
- [design/prediction-engine.md](../prediction-engine.md) §8

---

## 1. The Error Recovery Problem

When a parser encounters invalid syntax, it must decide where to resume parsing.
The wrong choice causes **error cascades** -- a single missing token generates
dozens of spurious errors as the parser attempts to parse subsequent tokens in
the wrong context.

```
Input: 3 + + 5 * 2

The second "+" is a syntax error (expected operand, got operator).
Where should the parser resume?

  Option A: Skip to "5"    → 1 error  (correct: "3 + 5 * 2" makes sense)
  Option B: Skip to "*"    → 2 errors (wrong: "* 2" is also invalid)
  Option C: Skip to end    → 1 error  (wasteful: loses all subsequent parsing)
```

The challenge: choose resume points that are **syntactically meaningful** -- where
the parser can re-enter a known state and continue producing useful results.

---

## 2. FOLLOW Sets as Recovery Guides

A **FOLLOW set** for a category is the set of tokens that can legally appear
**immediately after** an expression of that category. These tokens are natural
recovery points because they mark boundaries between expressions.

### 2.1 FOLLOW Set Computation

PraTTaIL computes FOLLOW sets via fixed-point iteration (`prediction.rs`,
`compute_follow_sets_from_inputs()`, lines 264-306):

```
1. Initialize: FOLLOW(start_category) = {Eof}
               FOLLOW(other) = {} for all other categories

2. Repeat until no changes:
   For each rule in category A with syntax [item_0, ..., item_n]:
     For each NonTerminal(B) at position i:
       a. Compute FIRST(items_{i+1}...item_n) (suffix after B)
       b. FOLLOW(B) += FIRST(suffix) \ {epsilon}
       c. If suffix is nullable: FOLLOW(B) += FOLLOW(A)
```

### 2.2 Intuition

If the grammar has a rule `Stmt → "if" Bool "then" Proc "else" Proc`, then:
- FOLLOW(Bool) includes `"then"` (what comes after the condition)
- FOLLOW(Proc) includes `"else"` (what comes after the then-branch)
- FOLLOW(Proc) also includes FOLLOW(Stmt) (what comes after the whole if-stmt)

These tokens mark points where the parser expects to transition between
categories -- ideal places to resynchronize.

### 2.3 Worked Example

```
Grammar:
  Stmt → Expr ";"
  Expr → Int "==" Int
  Int  → Int "+" Int | Int "*" Int | Ident | Integer

FOLLOW sets:
  FOLLOW(Int)  = {"+", "*", "==", ";", Eof}
  FOLLOW(Expr) = {";", Eof}
  FOLLOW(Stmt) = {Eof}
```

---

## 3. Structural Delimiters as Sync Points

In addition to FOLLOW tokens, PraTTaIL includes **structural delimiters** as
sync points -- but **only if they appear in the grammar's terminal set**.

### 3.1 The Structural Delimiters

```
Potential sync delimiters: ) } ] ; ,
```

These delimiters are good recovery points because they mark the end of grouping
constructs, statement boundaries, and list element boundaries.

### 3.2 Grammar-Conditional Inclusion

Not every grammar uses every delimiter. A grammar without semicolons should not
synchronize on `;` (it would never appear in valid input). PraTTaIL checks the
grammar's terminal set before including each delimiter:

```
For each potential sync delimiter d:
  if d exists in grammar terminal set:
    include d in sync predicate
  else:
    omit d
```

This prevents false sync points that would cause the parser to resume at tokens
that have no syntactic meaning in the current grammar.

### 3.3 Why Not Hardcode?

Different grammars use different delimiters:

| Grammar | Uses `;`? | Uses `]`? | Uses `}`? |
|---------|-----------|-----------|-----------|
| Calculator | No | No | No |
| RhoCalc | Yes | No | Yes |
| Lambda calculus | No | No | No |
| Full Rholang | Yes | Yes | Yes |

Hardcoding all delimiters would cause false positives in simple grammars.

---

## 4. Separate Recovery Functions

PraTTaIL generates **two versions** of each parse function: a normal version and
a recovery version. This ensures **zero overhead** on the happy path.

### 4.1 The Two Functions

```
parse_Cat(tokens, pos, min_bp)
  │
  ├── Normal path: called during regular parsing
  │   No sync checks, no error node generation
  │   Returns Result<Cat, ParseError>
  │
  └── Errors propagate up to caller

parse_Cat_recovering(tokens, pos, min_bp)
  │
  ├── Error recovery path: called when error recovery is active
  │   On parse failure: call sync_to() to skip to sync point
  │   Insert error node in AST
  │   Returns Cat (always succeeds, possibly with error nodes)
  │
  └── Errors are absorbed, not propagated
```

### 4.2 Why Not a Single Function with a Flag?

A single function with `if recovering { ... }` checks on every parse step would
add branch overhead to every successful parse. Since errors are rare (vast
majority of parsing is the happy path), the separate function design pays for
recovery logic only when recovery is actually needed.

### 4.3 Performance Guarantee

```
Normal parsing:  ZERO overhead from error recovery
                 (recovery functions not compiled into normal path)

Error recovery:  Localized overhead
                 (only the recovering function has sync checks)
```

---

## 5. Panic-Mode Recovery

When a parse error occurs in the recovery function, PraTTaIL uses **panic-mode
recovery**: skip tokens until a sync predicate matches, then resume parsing.

### 5.1 The `sync_to()` Function

```
sync_to(tokens, pos):
  While not at Eof:
    If is_sync_Cat(peek_token(tokens, *pos)):
      return   // Found sync point, resume here
    *pos += 1  // Skip this token
```

### 5.2 Token Stream Visualization

```
Input: 3 + @ 5 * 2 ; next_stmt

       3  +  @  5  *  2  ;  next_stmt
       ──────  ─  ──────  ─  ─────────
       parsed  ↑  skipped ↑  resumed
               │          │
              error     sync
              here      point
                        (";")
```

The `@` is invalid. Panic-mode recovery skips `@`, `5`, `*`, `2` until it
reaches `;` (a structural delimiter in the grammar). Parsing resumes at
`next_stmt`.

### 5.3 Error Node Insertion

The skipped region is recorded as an **error node** in the AST:

```
AST:
  Stmt(
    ErrorExpr(skipped: "@5*2"),
    ";"
  )
  Stmt(
    parse_Expr("next_stmt"),
    ...
  )
```

This preserves the AST structure for subsequent processing (e.g., error
reporting, partial evaluation) while clearly marking the error region.

---

## 6. Sync Predicate Composition

The sync predicate for a category combines three sources (`prediction.rs`,
`generate_sync_predicate()`, lines 1033-1079):

```
is_sync_Cat(token) =
     token == Eof                                    // Always sync at end
  || token in structural_delimiters_in_grammar       // If grammar uses them
  || token in FOLLOW(Cat)                            // What can follow Cat
```

### 6.1 Generated Code Example

For category `Int` in a calculator grammar with `;`:

```rust
fn is_sync_Int<'a>(token: &Token<'a>) -> bool {
    matches!(token,
        Token::Eof
        | Token::Semicolon           // structural delimiter (in grammar)
        | Token::RParen              // structural delimiter (in grammar)
        | Token::Plus                // FOLLOW(Int): from Int "+" Int rules
        | Token::Star                // FOLLOW(Int): from Int "*" Int rules
        | Token::EqEq                // FOLLOW(Int): from Int "==" Int → Bool
    )
}
```

### 6.2 Token-to-Pattern Conversion

The sync predicate generator converts token names to match patterns
(`prediction.rs`, lines 1082-1094):

| Token | Match Pattern |
|-------|---------------|
| Simple terminal (`Plus`) | `Token::Plus` |
| Data-carrying (`Ident`) | `Token::Ident(_)` |
| Data-carrying (`Integer`) | `Token::Integer(_)` |
| Data-carrying (`Boolean`) | `Token::Boolean(_)` |
| Data-carrying (`StringLit`) | `Token::StringLit(_)` |
| Data-carrying (`Dollar`) | `Token::Dollar(_)` |
| Data-carrying (`DoubleDollar`) | `Token::DoubleDollar(_)` |

The wildcard `_` on data-carrying tokens ensures the predicate matches regardless
of the token's payload.

---

## 7. Interaction with Other Layers

### 7.1 Layer 2 → Layer 5

FOLLOW sets (computed by Layer 2's prediction engine) are the primary input to
sync predicate generation. The quality of error recovery depends directly on the
accuracy of FOLLOW set computation.

### 7.2 Layers 1-4 → Layer 5

Error recovery activates **only after Layers 1-4 exhaust their options**:

```
  ┌──────────────────────────────────────────────────────────┐
  │  Layer 1: Lexer produces valid token                     │
  │  Layer 2: Dispatch table selects rule                    │
  │  Layer 3: Pratt loop parses expression                   │
  │  Layer 4: Cross-category dispatch resolves category      │
  │                                                          │
  │  If ALL succeed: normal parse result (no recovery)       │
  │  If ANY fails:   error → Layer 5 recovery activates      │
  └──────────────────────────────────────────────────────────┘
```

### 7.3 Recovery Scope

Error recovery operates per-category. If a `Bool` parse fails, the `Bool`
recovery function skips to a `Bool`-appropriate sync point. An outer `Stmt`
recovery function operates with `Stmt`-appropriate sync points. This nesting
ensures each recovery level uses contextually appropriate sync predicates.

---

## 8. Summary

```
  Parse Error → FOLLOW(Cat) + Structural Delimiters → Sync Point → Resume
                (from Layer 2)   (grammar-filtered)    (skip to)    (continue)
```

| Mechanism | Ambiguity Resolved | Implementation |
|-----------|-------------------|----------------|
| FOLLOW sets | Where can parsing legally resume? | `compute_follow_sets()` |
| Structural delimiters | Grammar-aware sync points | Grammar terminal set check |
| Separate functions | Zero overhead on happy path | `parse_Cat` vs `parse_Cat_recovering` |
| Panic-mode skip | Skip to next sync point | `sync_to()` function |
| Sync predicates | Combined sync check | `is_sync_Cat()` function |

**Layer 5 output:** An AST that may contain error nodes in regions where parsing
failed, but where subsequent valid portions of the input are correctly parsed.
The error nodes preserve source location information for error reporting.
