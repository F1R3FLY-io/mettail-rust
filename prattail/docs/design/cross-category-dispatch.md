# PraTTaIL: Cross-Category Dispatch

**Date:** 2026-02-14

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Cast Rules (Type Embedding)](#2-cast-rules-type-embedding)
3. [Comparison Rules (Cross-Type Operators)](#3-comparison-rules-cross-type-operators)
4. [FIRST Set Overlap Driving Backtracking Decisions](#4-first-set-overlap-driving-backtracking-decisions)
5. [parse_X_own vs parse_X_cross Split](#5-parse_x_own-vs-parse_x_cross-split)
6. [Dispatch Generation Algorithm](#6-dispatch-generation-algorithm)
7. [Worked Example: Calculator Bool Parsing](#7-worked-example-calculator-bool-parsing)

---

## 1. Problem Statement

Cross-category dispatch arises when a grammar category's parse function
must handle expressions that involve other categories. Two patterns create
this situation:

### Pattern 1: Cross-Category Operators

An operator whose operands are in one category and whose result is in
another category:

```
Eq    . a:Int,  b:Int  |- a "==" b : Bool    -- Int operands, Bool result
EqStr . a:Str,  b:Str  |- a "==" b : Bool    -- Str operands, Bool result
Lt    . a:Int,  b:Int  |- a "<"  b : Bool    -- Int operands, Bool result
```

When `parse_Bool` is called, it may need to parse an `Int` expression first,
check for `==`, then parse another `Int` expression, and wrap the result as
`Bool::Eq(left, right)`.

### Pattern 2: Type Embedding (Casts)

A rule that wraps one category's value inside another category:

```
CastInt . k:Int |- k : Proc    -- Embed Int into Proc
```

When `parse_Proc` sees an integer literal, it must parse it as `Int` and
wrap it as `Proc::CastInt(Box::new(int_value))`.

### The Challenge

The parser for category B must decide, **before consuming any tokens**,
whether the current expression belongs to category A (triggering a
cross-category path) or to category B itself. The decision depends on
which token is at the current position:

```
parse_Bool sees:
  "true"    → definitely a Bool expression (BoolLit)
  "42"      → definitely NOT a Bool; must be Int (for Eq rule)
  "x"       → ambiguous! Could be Bool variable OR Int variable (for Eq)
```

---

## 2. Cast Rules (Type Embedding)

### Structure

A cast rule embeds values from a source category into a target category:

```rust
CastRule {
    label: "CastInt",
    source_category: "Int",
    target_category: "Proc",
}
```

### Dispatch Logic

For tokens **unique to the source category** (not in the target's FIRST set),
the parser deterministically routes to the source parser:

```
parse_Proc sees Token::Integer(42):
  Integer is in FIRST(Int) but not in FIRST(Proc) natively
  → Deterministic cast path:
     let val = parse_Int(tokens, pos, 0)?;
     Ok(Proc::CastInt(Box::new(val)))
```

For tokens **in both FIRST sets** (ambiguous), the parser must decide
between casting and parsing natively. This is handled by the same
save/restore mechanism used for cross-category operators (Section 4).

### Multiple Cast Sources

A category can have multiple cast rules:

```
CastInt  . k:Int  |- k : Proc    -- embed Int
CastBool . b:Bool |- b : Proc    -- embed Bool
```

The dispatch handles each source independently. Tokens unique to `Int`
trigger `CastInt`; tokens unique to `Bool` trigger `CastBool`; tokens
shared between `Int`, `Bool`, and `Proc` require backtracking.

> **Terminology mapping:** The three-way partition in prose maps to
> `CrossCategoryOverlap` field names as follows: "tokens unique to the source"
> = `unique_to_a`, "tokens unique to the target" = `unique_to_b`, "tokens
> shared (ambiguous)" = `ambiguous_tokens`.

---

## 3. Comparison Rules (Cross-Type Operators)

### Structure

A cross-category rule takes operands from a source category and produces
a result in a different target category:

```rust
CrossCategoryRule {
    label: "Eq",
    source_category: "Int",
    result_category: "Bool",
    operator: "==",
    needs_backtrack: false,  // determined by overlap analysis
}
```

### Operator-Mediated Dispatch

Cross-category rules are mediated by an operator token. The parser:

1. Parses a source-category expression (the left operand).
2. Checks for the expected operator token.
3. If found, parses another source-category expression (right operand).
4. Constructs the cross-category result.

```
parse_Bool for Eq rule (Int "==" Int → Bool):

  left  = parse_Int(tokens, pos, 0)?;
  expect_token(tokens, pos, Token::EqEq, "==")?;
  right = parse_Int(tokens, pos, 0)?;
  Ok(Bool::Eq(Box::new(left), Box::new(right)))
```

### Multiple Operators, Same Target

When multiple cross-category rules target the same category but use
different operators, each gets its own dispatch arm:

```
Bool rules:
  Eq    . a:Int, b:Int |- a "==" b : Bool
  Lt    . a:Int, b:Int |- a "<"  b : Bool
  EqStr . a:Str, b:Str |- a "==" b : Bool
```

The dispatch for ambiguous tokens must try each possibility:

```
Token::Ident(_) => {
    let saved = *pos;
    // Try Int "==" Int path
    if let Ok(left) = parse_Int(tokens, pos, 0) {
        match peek_token(tokens, *pos) {
            Some(Token::EqEq) => {
                *pos += 1;
                let right = parse_Int(tokens, pos, 0)?;
                return Ok(Bool::Eq(left, right));
            }
            Some(Token::Lt) => {
                *pos += 1;
                let right = parse_Int(tokens, pos, 0)?;
                return Ok(Bool::Lt(left, right));
            }
            _ => {}  // Not a cross-category match
        }
    }
    *pos = saved;
    // Try Str "==" Str path
    if let Ok(left) = parse_Str(tokens, pos, 0) {
        if peek_token(tokens, *pos) == Some(&Token::EqEq) {
            *pos += 1;
            let right = parse_Str(tokens, pos, 0)?;
            return Ok(Bool::EqStr(left, right));
        }
    }
    *pos = saved;
    // Fall through to own-category
    parse_Bool_own(tokens, pos)
}
```

---

## 4. FIRST Set Overlap Driving Backtracking Decisions

### The Three-Way Partition

For each pair of categories (source, target), the overlap analysis
produces three disjoint token sets:

```
┌─────────────────────┬──────────────────────────────────────────────┐
│ Set                 │ Dispatch behavior                            │
├─────────────────────┼──────────────────────────────────────────────┤
│ unique_to_source    │ Deterministic: cross-category path.          │
│                     │ No backtracking needed.                      │
├─────────────────────┼──────────────────────────────────────────────┤
│ unique_to_target    │ Deterministic: own-category path.            │
│                     │ No backtracking needed.                      │
├─────────────────────┼──────────────────────────────────────────────┤
│ ambiguous_tokens    │ Non-deterministic: save position, try        │
│ (intersection)      │ cross-category first, backtrack if operator  │
│                     │ not found, then try own-category.            │
└─────────────────────┴──────────────────────────────────────────────┘
```

### Deterministic vs Save/Restore

The key insight is that **most tokens are NOT ambiguous**. For a typical
grammar:

```
FIRST(Int)  = {Ident, Integer, Pipe, LParen}
FIRST(Bool) = {Ident, KwTrue, KwFalse, KwNot}

unique_to_Int:  {Integer, Pipe}         → 2 tokens, deterministic
unique_to_Bool: {KwTrue, KwFalse, KwNot} → 3 tokens, deterministic
ambiguous:      {Ident, LParen}          → 2 tokens, save/restore
```

Only 2 out of 7 distinct tokens require backtracking. The generated code
has deterministic fast paths for the majority of tokens.

### Backtracking Bound

The save/restore backtracking is **bounded**: the parser attempts to parse
one source-category expression (which is O(n) in the worst case but
typically O(1) for simple expressions like a single variable), then peeks
at one token. If the peek fails, it restores the position and tries the
next alternative.

The total number of backtrack attempts per parse call is bounded by the
number of cross-category rules targeting this category, which is a static
constant determined at compile time (typically 1-3 rules).

---

## 5. parse_X_own vs parse_X_cross Split

### Architecture

When a category has cross-category or cast rules, the generated code uses
a two-function structure:

```
parse_Bool(tokens, pos, min_bp)           -- dispatch wrapper
    │
    ├── Token analysis (FIRST set overlap)
    │   │
    │   ├── unique_to_source  → cross-category path
    │   ├── unique_to_target  → parse_Bool_own()
    │   ├── ambiguous         → save/restore, then parse_Bool_own()
    │   └── default           → parse_Bool_own()
    │
    ▼

parse_Bool_own(tokens, pos)               -- original Pratt parser
    │
    ├── parse_Bool_prefix(tokens, pos)
    │       │
    │       ├── KwTrue/KwFalse → BoolLit
    │       ├── KwNot          → Not
    │       ├── Ident          → BVar
    │       └── LParen         → grouping
    │
    └── Pratt infix loop (&&, ==, ...)
```

### Function Renaming

The original `parse_Bool` (generated by the Pratt generator) is conceptually
renamed to `parse_Bool_own`. A new `parse_Bool` wrapper is generated by the
dispatch module that handles cross-category routing before delegating to
`parse_Bool_own`.

In the generated code, the renaming is achieved by having the dispatch
module's `generate_category_dispatch` emit a function with the name
`parse_Bool` that calls `parse_Bool_own`:

```rust
fn parse_Bool(tokens: &[(Token, Span)], pos: &mut usize, min_bp: u8)
    -> Result<Bool, String>
{
    if *pos >= tokens.len() {
        return Err("unexpected end of input, expected Bool expression".into());
    }
    match &tokens[*pos].0 {
        // ... dispatch arms ...
        _ => parse_Bool_own(tokens, pos)
    }
}
```

### When No Dispatch Is Needed

If a category has no cross-category or cast rules, the dispatch module
produces no code for that category. The Pratt-generated `parse_Cat` is the
only function, and it is not wrapped.

```
Categories needing dispatch:
  - Bool (has Eq, EqStr cross-category rules)
  - Proc (has CastInt cast rule)

Categories NOT needing dispatch:
  - Int  (all rules are same-category)
  - Str  (all rules are same-category)
  - Name (all rules are same-category)
```

---

## 6. Dispatch Generation Algorithm

The `generate_category_dispatch` function follows this algorithm:

```
INPUT:
  category:             "Bool"
  cross_category_rules: [Eq(Int=="Int→Bool), EqStr(Str=="Str→Bool)]
  cast_rules:           []
  overlaps:             {(Int,Bool): overlap1, (Str,Bool): overlap2}
  first_sets:           {Int: {...}, Bool: {...}, Str: {...}}

ALGORITHM:
  dispatch_arms = []

  // Step 1: Process cross-category rules
  For each cross_rule in cross_category_rules:
    source_first = first_sets[cross_rule.source_category]
    target_first = first_sets[category]

    // Step 1a: Tokens unique to source → deterministic cross path
    unique_tokens = source_first MINUS target_first
    For each token in unique_tokens:
      Generate arm:
        Token::TOKEN => {
          let left = parse_SOURCE(tokens, pos, 0)?;
          expect_token(tokens, pos, OPERATOR)?;
          let right = parse_SOURCE(tokens, pos, 0)?;
          Ok(CATEGORY::LABEL(Box::new(left), Box::new(right)))
        }

    // Step 1b: Ambiguous tokens → save/restore
    overlap = overlaps[(source, category)]
    For each token in overlap.ambiguous_tokens:
      Generate arm:
        Token::TOKEN => {
          let saved = *pos;
          if let Ok(left) = parse_SOURCE(tokens, pos, 0) {
            if peek matches OPERATOR {
              consume operator;
              let right = parse_SOURCE(tokens, pos, 0)?;
              return Ok(CATEGORY::LABEL(Box::new(left), Box::new(right)));
            }
          }
          *pos = saved;
          parse_CATEGORY_own(tokens, pos)
        }

  // Step 2: Process cast rules
  For each cast_rule in cast_rules:
    source_first = first_sets[cast_rule.source_category]
    target_first = first_sets[category]

    unique_tokens = source_first MINUS target_first
    For each token in unique_tokens:
      Generate arm:
        Token::TOKEN => {
          let val = parse_SOURCE(tokens, pos, 0)?;
          Ok(CATEGORY::LABEL(Box::new(val)))
        }

  // Step 3: Add fallback
  dispatch_arms.push(
    _ => parse_CATEGORY_own(tokens, pos)
  )

  // Step 4: Generate wrapper function
  Generate fn parse_CATEGORY(tokens, pos, min_bp) {
    match &tokens[*pos].0 {
      #dispatch_arms
    }
  }
```

---

## 7. Worked Example: Calculator Bool Parsing

### Grammar

```
types: Int (i32), Bool (bool), Str (str)

Bool rules:
  Eq      . a:Int,  b:Int  |- a "==" b : Bool   (cross: Int → Bool)
  EqBool  . a:Bool, b:Bool |- a "==" b : Bool   (same-cat infix)
  EqStr   . a:Str,  b:Str  |- a "==" b : Bool   (cross: Str → Bool)
  Comp    . a:Bool, b:Bool |- a "&&" b : Bool   (same-cat infix)
  Not     . a:Bool         |- "not" a  : Bool   (prefix)
  BoolLit : Bool   (literal: true/false)
  BVar    : Bool   (variable)
```

### FIRST Sets

```
FIRST(Int)  = {Ident, Integer, Pipe, LParen}
FIRST(Bool) = {Ident, Integer, Pipe, LParen, KwTrue, KwFalse, KwNot,
               StringLit}
  (Bool includes Int and Str tokens due to cross-category rules)
FIRST(Str)  = {Ident, StringLit, LParen}
```

### Overlap Analysis

```
Overlap(Int, Bool):
  unique_to_Int:  {}              -- everything in Int is also in Bool
  unique_to_Bool: {KwTrue, KwFalse, KwNot, StringLit}
  ambiguous:      {Ident, Integer, Pipe, LParen}

Overlap(Str, Bool):
  unique_to_Str:  {}              -- everything in Str is also in Bool
  unique_to_Bool: {Integer, Pipe, KwTrue, KwFalse, KwNot}
  ambiguous:      {Ident, StringLit, LParen}
```

### Generated Dispatch Wrapper

```rust
/// Top-level parse entry with cross-category dispatch for Bool.
fn parse_Bool(
    tokens: &[(Token, Span)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Bool, String> {
    if *pos >= tokens.len() {
        return Err("unexpected end of input, expected Bool expression".into());
    }
    match &tokens[*pos].0 {
        // ---- Tokens unique to Bool (not in any source category's unique set) ----
        // These go directly to own-category parsing.
        // KwTrue, KwFalse, KwNot are unique to Bool (not in Int or Str).
        // (But they are in Bool's FIRST set, so they hit the default arm.)

        // ---- Cross-category: Eq (Int "==" Int -> Bool) ----
        // unique_to_Int = {} (empty! all Int tokens are also in Bool)
        // So NO deterministic arms for Int.

        // ---- Cross-category: EqStr (Str "==" Str -> Bool) ----
        // unique_to_Str = {} (empty! all Str tokens are also in Bool)
        // So NO deterministic arms for Str.

        // ---- Ambiguous tokens ----
        // Overlap(Int, Bool).ambiguous = {Ident, Integer, Pipe, LParen}
        // These require save/restore.

        Token::Integer(_) => {
            // Ambiguous: could be Int (for Eq) or... actually Integer
            // is not natively a Bool token, but it enters Bool's FIRST
            // set via the cross-category inclusion.
            let saved = *pos;
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_token(tokens, *pos).map_or(false,
                    |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos)
        }

        Token::Ident(_) => {
            let saved = *pos;
            // Try Int "==" Int path
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_token(tokens, *pos).map_or(false,
                    |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            // Try Str "==" Str path
            if let Ok(left) = parse_Str(tokens, pos, 0) {
                if peek_token(tokens, *pos).map_or(false,
                    |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Str(tokens, pos, 0)?;
                    return Ok(Bool::EqStr(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos)
        }

        Token::StringLit(_) => {
            let saved = *pos;
            // Try Str "==" Str path
            if let Ok(left) = parse_Str(tokens, pos, 0) {
                if peek_token(tokens, *pos).map_or(false,
                    |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Str(tokens, pos, 0)?;
                    return Ok(Bool::EqStr(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos)
        }

        Token::Pipe => {
            let saved = *pos;
            // Try Int "==" Int path (|s| is an Int expression via Len)
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_token(tokens, *pos).map_or(false,
                    |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos)
        }

        // Everything else -> own-category
        _ => parse_Bool_own(tokens, pos)
    }
}
```

### Parsing Traces

**Trace 1: `3 == 4`** (cross-category, deterministic)

```
Tokens: [Integer(3), EqEq, Integer(4), Eof]

parse_Bool(pos=0):
  match Integer(3):
    saved = 0
    parse_Int(pos=0): Integer(3) → NumLit(3), pos=1
      Pratt loop: EqEq is not Int infix → break
    peek(pos=1) = EqEq → match!
    pos=2
    parse_Int(pos=2): Integer(4) → NumLit(4), pos=3
    return Bool::Eq(Box(NumLit(3)), Box(NumLit(4)))
```

**Trace 2: `true && false`** (own-category)

```
Tokens: [Boolean(true), AmpAmp, Boolean(false), Eof]

parse_Bool(pos=0):
  match Boolean(true):
    default arm → parse_Bool_own(pos=0)
      parse_Bool_prefix: Boolean(true) → BoolLit(true), pos=1
      Pratt loop: AmpAmp, infix_bp = Some((2,3))
        2 >= 0 → continue
        consume AmpAmp, pos=2
        parse_Bool(pos=2, min_bp=3):
          match Boolean(false):
            default → parse_Bool_own:
              BoolLit(false), pos=3
              Pratt loop: Eof → break
        rhs = BoolLit(false)
        make_infix(AmpAmp, BoolLit(true), BoolLit(false))
          = Comp(BoolLit(true), BoolLit(false))
      Pratt loop: Eof → break
    return Comp(BoolLit(true), BoolLit(false))
```

**Trace 3: `x == y`** (ambiguous, backtrack to Bool)

```
Tokens: [Ident("x"), EqEq, Ident("y"), Eof]

parse_Bool(pos=0):
  match Ident("x"):
    saved = 0
    Try Int path:
      parse_Int(pos=0): IVar("x"), pos=1
      peek(pos=1) = EqEq → match!
      pos=2
      parse_Int(pos=2): IVar("y"), pos=3
      return Bool::Eq(Box(IVar("x")), Box(IVar("y")))
    (Success on first try, no backtracking needed)
```

**Trace 4: `b && (x == y)`** (own-category with nested cross-category)

```
Tokens: [Ident("b"), AmpAmp, LParen, Ident("x"), EqEq, Ident("y"),
         RParen, Eof]

parse_Bool(pos=0):
  match Ident("b"):
    saved = 0
    Try Int path:
      parse_Int(pos=0): IVar("b"), pos=1
      peek(pos=1) = AmpAmp (not EqEq) → no match
    pos = 0 (backtrack)
    Try Str path:
      parse_Str(pos=0): SVar("b"), pos=1
      peek(pos=1) = AmpAmp (not EqEq) → no match
    pos = 0 (backtrack)
    parse_Bool_own(pos=0):
      parse_Bool_prefix: Ident("b") → BVar("b"), pos=1
      Pratt loop: AmpAmp, infix_bp = Some((2,3))
        2 >= 0 → continue
        consume AmpAmp, pos=2
        parse_Bool(pos=2, min_bp=3):
          match LParen:
            (same ambiguous logic, but eventually reaches own-category)
            parse_Bool_own(pos=2):
              LParen → consume, pos=3
              parse_Bool(pos=3, min_bp=0):
                match Ident("x"):
                  Try Int path:
                    parse_Int: IVar("x"), pos=4
                    peek = EqEq → match!
                    consume EqEq, pos=5
                    parse_Int: IVar("y"), pos=6
                    return Bool::Eq(IVar("x"), IVar("y"))
              expect RParen, pos=7
              return Eq(IVar("x"), IVar("y"))
            Pratt loop: Eof → break (min_bp=3)
          return Eq(IVar("x"), IVar("y"))
        make_infix(AmpAmp, BVar("b"), Eq(IVar("x"), IVar("y")))
          = Comp(BVar("b"), Eq(IVar("x"), IVar("y")))
      Pratt loop: Eof → break
    return Comp(BVar("b"), Eq(IVar("x"), IVar("y")))
```

This trace demonstrates the full interplay: the initial `Ident("b")` triggers
backtracking (Int and Str paths fail because `&&` is not `==`), then the
own-category path succeeds via the Pratt loop. The nested `(x == y)` inside
parentheses correctly dispatches to the cross-category `Eq` rule because
`parse_Bool` is called recursively, and `Ident("x")` followed by `==` matches
the cross-category pattern on the first try.
