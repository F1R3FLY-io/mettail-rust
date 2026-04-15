# Infix Cross-Category Dispatch Bug

## Finding

`Bool::parse("b >= true")` fails even though `GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool` is defined.

The parser's LED (infix) dispatch commits to `GtEqInt` (first `>=` rule by weight) and doesn't try `GtEqBool` when the right operand fails to parse as Int.

## Root cause

Cross-category infix operators (`>=`, `==`, `<`, `>`, `<=`, `!=`) exist in multiple categories:
- `GtEqInt . a:Int, b:Int |- a ">=" b : Bool`
- `GtEqFloat . a:Float, b:Float |- a ">=" b : Bool`
- `GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool`
- `GtEqStr . a:Str, b:Str |- a ">=" b : Bool`

When parsing `b >= true`:
1. `b` is parsed as a variable (ambiguous category)
2. `>=` is seen as an infix operator
3. Parser commits to `GtEqInt` (first by weight)
4. Tries to parse `true` as Int — fails
5. Does NOT try `GtEqBool` which would succeed

## Affected expressions

All cross-category comparisons where the operand types disambiguate:
- `b >= true` (Bool operand requires GtEqBool)
- `b == str("hello")` (Str operand requires EqStr)
- `(z <= "wn") != (true < a)` (mixed types)

## Status

Needs proper explore + plan investigation of the LED dispatch mechanism.
