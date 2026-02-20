# Layer 4: Cross-Category Resolution

Cross-category resolution is the fourth layer in PraTTaIL's six-layer model. It
resolves ambiguity that arises when a grammar has **multiple type categories** and
a token could legitimately begin an expression in more than one category.

**Source files:**
- `prattail/src/dispatch.rs` -- Cross-category dispatch generation (lines 60-200)
- `prattail/src/prediction.rs` -- `analyze_cross_category_overlaps()` (lines 714-769)

**Cross-references:**
- [theory/prediction-and-lookahead.md](../../theory/prediction-and-lookahead.md) §5
- [design/cross-category-dispatch.md](../cross-category-dispatch.md) §1-7

---

## 1. The Cross-Category Ambiguity Problem

In a multi-type grammar like a calculator with `Int`, `Bool`, and `Str` categories,
a single token may be claimed by multiple categories:

```
Category Int:   IVar(Ident), NumLit(Integer), IAdd(Int, "+", Int), ...
Category Bool:  BVar(Ident), BTrue("true"),   BAnd(Bool, "&&", Bool), ...
Category Str:   SVar(Ident), StrLit(String),  SCat(Str, "++", Str), ...
```

The token `Ident("x")` appears in FIRST(Int), FIRST(Bool), and FIRST(Str). When
the parser expects a `Bool` (e.g., after `if`), and sees `Ident("x")`, should it:

1. Parse `x` as a `Bool` variable?
2. Parse `x` as an `Int` variable, then look for `==` to produce a `Bool`?
3. Parse `x` as a `Str` variable, then look for `matches` to produce a `Bool`?

All three are valid depending on what follows `x`. This is the cross-category
ambiguity problem.

---

## 2. Three-Way Token Partition

PraTTaIL resolves cross-category ambiguity by partitioning tokens into three sets
based on FIRST set membership (`prediction.rs`, `analyze_cross_category_overlaps()`,
lines 714-769).

### 2.1 The Partition

For a cross-category rule where category B has a rule that parses category A then
an operator (e.g., `Eq(Int, "==", Int) → Bool`):

```
  ┌─────────────────────────────────────────────────────────┐
  │                    All Tokens                           │
  │                                                         │
  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │
  │  │ Unique to A  │  │  Ambiguous   │  │ Unique to B  │  │
  │  │              │  │ (A ∩ B)      │  │              │  │
  │  │  Integer     │  │  Ident       │  │  Boolean     │  │
  │  │  Minus       │  │              │  │  Bang        │  │
  │  │              │  │              │  │              │  │
  │  └──────────────┘  └──────────────┘  └──────────────┘  │
  │                                                         │
  │  Deterministic     Save/Restore      Deterministic      │
  │  → parse as A      → try A, then B   → parse as B      │
  └─────────────────────────────────────────────────────────┘
```

### 2.2 The CrossCategoryOverlap Structure

```rust
struct CrossCategoryOverlap {
    category_a: String,           // Source category (e.g., "Int")
    category_b: String,           // Target category (e.g., "Bool")
    ambiguous_tokens: FirstSet,   // Tokens in both FIRST sets
    unique_to_a: FirstSet,        // Tokens only in FIRST(A)
    unique_to_b: FirstSet,        // Tokens only in FIRST(B)
}
```

### 2.3 Worked Example: Calculator

```
FIRST(Int)  = {Integer, Ident, Minus}
FIRST(Bool) = {Boolean, Ident, Bang}

Partition for cross-category rules Int → Bool:
  Unique to Int:   {Integer, Minus}     → deterministic: parse as Int
  Ambiguous:       {Ident}              → save/restore: try Int, fallback Bool
  Unique to Bool:  {Boolean, Bang}      → deterministic: parse as Bool
```

---

## 3. Deterministic Dispatch for Unique Tokens

When a token is unique to the source category, the parser knows immediately
which category to try -- no backtracking needed.

### 3.1 Generated Code Pattern

```rust
// Inside parse_Bool dispatcher (dispatch.rs, lines 85-109)
match peek_token(tokens, *pos) {
    Some(Token::Integer(_)) => {
        // Integer is UNIQUE to Int -- deterministic dispatch
        let left = parse_Int(tokens, pos, 0)?;
        expect_token(tokens, pos, Token::EqEq)?;
        let right = parse_Int(tokens, pos, 0)?;
        Ok(Bool::Eq(Box::new(left), Box::new(right)))
    }
    // ...
}
```

### 3.2 Worked Example: `"42 == 7"`

```
Parsing Bool, see Token::Integer(42).

  Integer is in FIRST(Int) but NOT in FIRST(Bool).
  → Unique to Int → deterministic dispatch.

  1. parse_Int(min_bp=0) → consumes "42", returns NumLit(42)
  2. Expect "==" → consume EqEq
  3. parse_Int(min_bp=0) → consumes "7", returns NumLit(7)
  4. Construct Bool::Eq(NumLit(42), NumLit(7))

No backtracking needed. O(1) dispatch decision.
```

---

## 4. Backtracking Dispatch for Ambiguous Tokens

When a token appears in both source and target FIRST sets, the parser must
**save** its position, try one interpretation, and **restore** on failure.

### 4.1 The Save/Restore Pattern

```rust
// Inside parse_Bool dispatcher (dispatch.rs, lines 113-141)
Token::Ident(_) => {
    // Ident is in BOTH FIRST(Int) and FIRST(Bool) -- ambiguous
    let saved = *pos;

    // Try cross-category: parse as Int, then look for "=="
    if let Ok(left) = parse_Int(tokens, pos, 0) {
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::EqEq)) {
            // Cross-category succeeded!
            *pos += 1;  // consume "=="
            let right = parse_Int(tokens, pos, 0)?;
            return Ok(Bool::Eq(Box::new(left), Box::new(right)));
        }
    }

    // Cross-category failed -- restore and try own category
    *pos = saved;
    parse_Bool_own(tokens, pos, min_bp)
}
```

### 4.2 Worked Example: `"x == y"` (cross-category succeeds)

```
Parsing Bool, see Token::Ident("x").

  Ident is AMBIGUOUS (in both FIRST(Int) and FIRST(Bool)).
  → Save position. Try cross-category.

  1. saved = pos (pointing at "x")
  2. parse_Int(min_bp=0) → consumes "x", returns IVar("x")  ✓
  3. Peek next: Token::EqEq                                  ✓
     → Cross-category matched!
  4. Consume "==", parse_Int(min_bp=0) → consumes "y", returns IVar("y")
  5. Construct Bool::Eq(IVar("x"), IVar("y"))

No restore needed. Cross-category path succeeded.
```

### 4.3 Worked Example: `"b && true"` (cross-category fails, own-category succeeds)

```
Parsing Bool, see Token::Ident("b").

  Ident is AMBIGUOUS.
  → Save position. Try cross-category.

  1. saved = pos (pointing at "b")
  2. parse_Int(min_bp=0) → consumes "b", returns IVar("b")  ✓
  3. Peek next: Token::AmpAmp                                ✗
     → "&&" is NOT "==" — cross-category does NOT match
  4. Restore: *pos = saved (back to "b")
  5. parse_Bool_own(tokens, pos, min_bp)
     → Parses "b" as BVar("b")
     → Infix loop picks up "&&" as BAnd
     → Parses "true" as BTrue
     → Returns BAnd(BVar("b"), BTrue)

Backtracking recovered correctly.
```

### 4.4 The Operator Peek

After parsing the source category expression, the dispatcher peeks at the next
token to check for the cross-category operator (e.g., `==`). This **one-token
peek** is the key disambiguation step:

```
  ┌────────────────────────────────────────────────────────┐
  │  Parse source category expression                      │
  │  Peek next token:                                      │
  │    Expected operator ("==") → cross-category succeeds  │
  │    Anything else            → restore, try own category │
  └────────────────────────────────────────────────────────┘
```

---

## 5. Cast Rules as Disambiguation

Cast rules embed one type category into another (e.g., every `Int` expression
is also a valid `Expr` expression). They require special handling for
disambiguation.

### 5.1 Why Casts Must Be in the PREFIX Handler

Cast rules are placed in the Pratt **prefix** handler, not as dispatch wrappers.
This is a critical correctness requirement:

```
WRONG (dispatch wrapper):
  parse_Expr(tokens, pos, min_bp) {
      let inner = parse_Int(tokens, pos, min_bp);
      return Expr::FromInt(inner);
      // ← PROBLEM: Pratt infix loop never runs on Expr!
  }

RIGHT (prefix handler):
  // In parse_Expr's nud/prefix section:
  Token::Integer(_) => {
      let inner = parse_Int(tokens, pos, 0);
      lhs = Expr::FromInt(inner);
      // ← Pratt infix loop continues for Expr operators
  }
```

If a cast rule were a dispatch wrapper, the Pratt infix loop for the target
category would never execute. An expression like `int_expr + other_expr` would
fail because `+` (an `Expr` infix operator) would never be checked.

### 5.2 Cast Token Selection

Cast rules use **unique tokens** from the source category's FIRST set to trigger
deterministic dispatch:

```
Source FIRST(Int) = {Integer, Ident, Minus}
Target FIRST(Expr) = {Ident, LeftParen, ...}

Unique to Int: {Integer, Minus}
  → Seeing Integer → deterministically cast from Int
  → Seeing Minus   → deterministically cast from Int

Ambiguous: {Ident}
  → Seeing Ident → may need backtracking (try Int cast, fallback to Expr)
```

---

## 6. The `parse_Cat_own` vs `parse_Cat` Split

When a category has cross-category rules, PraTTaIL generates **two** parse
functions:

```
  ┌─────────────────────────────────────────────────────┐
  │                                                     │
  │  parse_Bool(tokens, pos, min_bp)                    │
  │  ├── Dispatch wrapper                               │
  │  ├── Handles cross-category dispatch                │
  │  │     (unique tokens, save/restore for ambiguous)  │
  │  └── Falls through to parse_Bool_own on failure     │
  │                                                     │
  │  parse_Bool_own(tokens, pos, min_bp)                │
  │  ├── Category's own Pratt parser                    │
  │  ├── Prefix handlers for Bool-native rules          │
  │  └── Infix loop for Bool operators (&&, ||, ...)    │
  │                                                     │
  └─────────────────────────────────────────────────────┘
```

### 6.1 Call Graph

```
  parse_Bool ──┬── [Integer] ──→ parse_Int ──→ expect "==" ──→ Bool::Eq
               │
               ├── [Ident]  ──→ save pos
               │                 ├── parse_Int → peek "==" → Bool::Eq
               │                 └── restore → parse_Bool_own
               │
               ├── [Boolean] ──→ parse_Bool_own
               │
               └── [Bang]    ──→ parse_Bool_own
```

### 6.2 When No Dispatch Is Needed

If a category has **no cross-category rules**, only `parse_Cat` is generated
(no `_own` split). The dispatch wrapper adds overhead only when cross-category
rules actually exist.

---

## 7. Backtracking Bounds

Cross-category backtracking is **bounded** and does not lead to exponential
blowup:

### 7.1 What Gets Backtracked

1. **One sub-expression** parse in the source category
2. **One token peek** for the cross-category operator

### 7.2 Bound Analysis

For each ambiguous token:
- The parser tries at most **one** cross-category parse path
- If the operator peek fails, it immediately restores and tries own-category
- There is no recursive backtracking -- the save/restore is flat

For a category with `k` cross-category rules:
- At most `k` save/restore attempts per ambiguous token
- Each attempt parses one sub-expression + one peek = bounded work
- Total: O(k) overhead per ambiguous token, where k is typically 1-2

### 7.3 Why This Is Efficient

```
  Deterministic tokens: O(1) — no backtracking
  Ambiguous tokens:     O(k) — bounded save/restore
  Total per parse call: O(1) amortized (most tokens are deterministic)
```

In practice, grammars have 1-2 cross-category rules per category, and the
ambiguous token set is typically just `{Ident}`. The overhead is negligible.

---

## 8. Multiple Cross-Category Sources

A target category can have cross-category rules from **multiple** source
categories:

```
Category Bool:
  Eq(Int, "==", Int)      // From Int
  StrEq(Str, "===", Str)  // From Str
  BVar(Ident)             // Own category
```

The dispatch wrapper handles each source in sequence:

```
  parse_Bool ──┬── [Integer] ──→ parse_Int  (unique to Int)
               │
               ├── [StringLit] → parse_Str  (unique to Str)
               │
               ├── [Ident] ───→ save
               │                 ├── try parse_Int → peek "==" → Eq
               │                 ├── try parse_Str → peek "===" → StrEq
               │                 └── restore → parse_Bool_own
               │
               └── [Boolean] ──→ parse_Bool_own
```

Each source is tried in declaration order. The first successful match wins.

---

## 9. Interaction with Other Layers

### 9.1 Layer 2 → Layer 4

Parse prediction (Layer 2) computes the FIRST sets and identifies cross-category
overlaps. Layer 4 uses this analysis to generate the dispatch wrapper. The
partition (unique/ambiguous/unique) is computed once at compile time.

### 9.2 Layer 4 → Layer 3

The cross-category dispatch wrapper calls the Pratt parser (Layer 3) for the
source category. After the source expression is parsed, the operator peek
occurs, and then the Pratt parser for the source category runs again (for the
right operand). Layer 3's precedence disambiguation operates independently
within each category.

### 9.3 Layer 4 → Layer 5

If both cross-category and own-category parsing fail, control passes to Layer 5
(error recovery). The sync predicate uses FOLLOW sets that account for
cross-category operators.

### 9.4 Layer 4 → Layer 6

Layer 4 and Layer 6 both resolve cross-category ambiguity, but at different
levels:

- **Layer 4 (syntactic):** Operates *within* a single parse invocation. When
  parsing `Bool` and encountering `Ident("x")`, Layer 4 tries parsing as `Int`
  and peeks for `==`. This is a single-parse-path decision — exactly one
  category wins per token.

- **Layer 6 (semantic):** Operates *across* multiple parse invocations. When
  the top-level NFA-style parser runs `Float::parse("a + b")` and
  `Int::parse("a + b")` and both succeed, Layer 6 resolves via groundness
  checking and substitution. This handles multi-parse-path ambiguity that
  Layer 4 cannot see (because Layer 4 operates inside each category's parser,
  not across them).

Layer 4's backtracking dispatch is a necessary prerequisite for Layer 6: it
ensures that each individual category parser produces a correct, unambiguous
AST. Layer 6 then decides which of those correct ASTs is the intended
interpretation.

See [07-semantic-disambiguation.md](07-semantic-disambiguation.md) §8 for the
full interaction model.

---

## 10. Summary

```
  Token ──→ FIRST Set Partition ──→ Unique?  ──→ Deterministic Dispatch
                                     │
                                     └── Ambiguous? ──→ Save/Restore
                                                         ├── Try source cat
                                                         │   + operator peek
                                                         └── Fallback: own cat
```

| Mechanism | Ambiguity Resolved | Implementation |
|-----------|-------------------|----------------|
| Three-way partition | Which category owns a token | `analyze_cross_category_overlaps()` |
| Deterministic dispatch | Unique tokens: no backtracking | Direct parse call in wrapper |
| Save/restore | Ambiguous tokens: bounded backtrack | `saved = *pos` / `*pos = saved` |
| Operator peek | Cross-category operator present? | One-token peek after source parse |
| Cast in prefix | Type embedding + infix continuation | Pratt prefix handler (not wrapper) |
| `_own` split | Separate own-category from dispatch | `parse_Cat` + `parse_Cat_own` |

**Layer 4 output → Layer 5 input:** A fully typed AST node, or a parse failure
that Layer 5 will attempt to recover from. When multiple categories each produce
a valid AST (Layer 4 succeeded in each), Layer 6 resolves the remaining ambiguity
via groundness checking and substitution (see
[07-semantic-disambiguation.md](07-semantic-disambiguation.md)).
