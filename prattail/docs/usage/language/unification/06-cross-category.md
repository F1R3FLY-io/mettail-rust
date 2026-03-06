# Cross-Category Dispatch as Implicit Unification

## Intuition

"Cross-category rules stitch categories together --- they're implicit composition
at the rule level." When a rule takes operands from one category and produces a
result in another (e.g., `Eq . a:Int, b:Int |- a "==" b : Bool`), PraTTaIL
automatically generates dispatch logic that unifies the two categories at parse
time.

## Why Important

- **Multi-sort languages**: integer arithmetic + boolean comparisons
- **Type systems**: expressions that cross type boundaries
- **Comparison operators**: operands of type A producing results of type B

## How It Works

A cross-category rule has operands in a source category and results in a target
category:

```rust
Eq . a:Int, b:Int |- a "==" b : Bool;   // Int operands -> Bool result
Len . s:Str |- "|" s "|" : Int;         // Str operand -> Int result
```

The parser for the TARGET category (Bool, Int) must handle tokens that normally
belong to the SOURCE category (Int, Str).

## FIRST Set Overlap Analysis

PraTTaIL analyzes FIRST set overlap to determine dispatch strategy:

```
FIRST(Int)  = {Integer, Ident, LParen}
FIRST(Bool) = {KwTrue, KwFalse, Ident, LParen}

For "Eq . a:Int, b:Int |- a '==' b : Bool":
  +---------------------------------------------+
  |                FIRST(Bool)                  |
  |  +---------+  +---------------+             |
  |  | unique  |  |  ambiguous    |  unique     |
  |  | to Int  |  |  (both sets)  |  to Bool    |
  |  |         |  |               |             |
  |  | Integer |  | Ident, LParen |  KwTrue     |
  |  |         |  |               |  KwFalse    |
  |  +---------+  +---------------+             |
  +---------------------------------------------+
```

**Deterministic tokens** (unique to one category): dispatch directly without
backtracking.

**Ambiguous tokens** (in both FIRST sets): require save/restore backtracking.

## Composed Dispatch via WFST

For ambiguous tokens, composed dispatch uses WFST tropical shortest-path:

1. Build prediction WFST for each category with weighted actions
2. For tokens that appear in multiple categories' FIRST sets, compose weights
3. Order dispatch arms by weight (lowest = most likely = tried first)
4. Generated code uses weight-ordered match arms with save/restore for ambiguous
   cases

## Dispatch Code Generation

```rust
// Generated parse_Bool wrapper:
fn parse_Bool(tokens: &[(Token, Range)], pos: &mut usize, min_bp: u8)
    -> Result<Bool, ParseError>
{
    match &tokens.get(*pos).map(|(t, _)| t) {
        // Deterministic: Integer is unique to Int
        Some(Token::Integer(_)) => {
            let left = parse_Int(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::EqEq), "==")?;
            let right = parse_Int(tokens, pos, 0)?;
            Ok(Bool::Eq(Box::new(left), Box::new(right)))
        }
        // Ambiguous: Ident in both Int and Bool
        Some(Token::Ident(_)) => {
            let saved = *pos;
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_is(tokens, *pos, Token::EqEq) {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos, min_bp)
        }
        // Unique to Bool: dispatch directly
        Some(Token::KwTrue) | Some(Token::KwFalse) => {
            parse_Bool_own(tokens, pos, min_bp)
        }
        _ => parse_Bool_own(tokens, pos, min_bp)
    }
}
```

## Hot/Cold Splitting

Dispatch arms are split by weight:

- **Hot path** (low weight): most likely token, tried first
- **Cold path** (high weight): unlikely tokens, tried last
- Weight gap > 2.0 tropical units triggers cold splitting

## Diagrams

**Information flow from FIRST sets to codegen:**

```
  FIRST(Int) -----------+     +------------ FIRST(Bool)
                        |     |
                        v     v
                analyze_cross_category_overlaps()
                        |
                        v
                CrossCategoryOverlap {
                  ambiguous: {Ident, LParen},
                  unique_to_int: {Integer},
                  unique_to_bool: {KwTrue, KwFalse}
                }
                        |
                        +---- build_prediction_wfsts()
                        |            |
                        |            v
                        |     compute_composed_dispatch()
                        |            |
                        |            v
                        |     resolve_dispatch_winners()
                        |            |
                        v            v
                write_category_dispatch()
                        |
                        v
                Generated dispatch code
                (weight-ordered match arms)
```

## Integration

Cross-category dispatch is a sub-phase within parser codegen (Phase 3 of the
pipeline). It runs after FIRST/FOLLOW computation and WFST prediction, and
produces match arms that are emitted as part of the parser code string.

## Source Reference

| Component                           | File                         |
|-------------------------------------|------------------------------|
| `analyze_cross_category_overlaps()` | `prattail/src/prediction.rs` |
| `write_category_dispatch()`         | `prattail/src/dispatch.rs`   |
| `build_prediction_wfsts()`          | `prattail/src/pipeline.rs`   |
| `compute_composed_dispatch()`       | `prattail/src/pipeline.rs`   |
| `resolve_dispatch_winners()`        | `prattail/src/pipeline.rs`   |
