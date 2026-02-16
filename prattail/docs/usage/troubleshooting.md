# PraTTaIL Troubleshooting Guide

**Common issues, diagnostic strategies, and performance tips.**

---

## Table of Contents

1. [Lambda Binder Type Inference Failures](#1-lambda-binder-type-inference-failures)
2. [Cross-Category Ambiguity Warnings](#2-cross-category-ambiguity-warnings)
3. [Parse Error Messages](#3-parse-error-messages)
4. [Lexer Errors](#4-lexer-errors)
5. [Precedence and Associativity Issues](#5-precedence-and-associativity-issues)
6. [Collection Parsing Issues](#6-collection-parsing-issues)
7. [Build and Compilation Issues](#7-build-and-compilation-issues)
8. [Performance Tips](#8-performance-tips)

---

## 1. Lambda Binder Type Inference Failures

### Symptom

```
Lambda binder 'x' not used in body
```

or

```
thread 'main' panicked at 'Lambda binder 'x' not used in body'
```

### Cause

When parsing `^x.{body}`, PraTTaIL calls `body.infer_var_type("x")` to determine
which lambda variant to construct (e.g., `LamInt` vs `LamBool`). If `x` does not
appear in the body, inference fails.

### Solutions

1. **Ensure the binder variable is used in the body:**
   ```
   ^x.{x + 1}      OK: x appears in body
   ^x.{42}          FAILS: x not used
   ```

2. **For unused binders, use a discard convention.** This is a known limitation:
   PraTTaIL requires type inference from usage, so unused binders cannot have their
   type inferred.

3. **For multi-binders, all variables must be used:**
   ```
   ^[x,y].{x + y}   OK: both used
   ^[x,y].{x + 1}   FAILS: y not used
   ```

### Diagnostic

Enable verbose output to see what `infer_var_type` returns:

```rust
let _inferred = body.infer_var_type(&binder_name);
eprintln!("Inferred type for '{}': {:?}", binder_name, _inferred);
```

---

## 2. Cross-Category Ambiguity Warnings

### Symptom

The parser sometimes backtracks unnecessarily or gives unexpected parse results
when expressions could belong to multiple categories.

### Cause

When two categories share tokens in their FIRST sets, the parser must use
save/restore backtracking to determine the correct parse path. The most common
case is `Ident`, which appears in the FIRST set of every category that has
variables.

### Example

```
Bool::parse("x == y")
```

1. Parser sees `Ident("x")` -- ambiguous between `Int` and `Bool`
2. Saves position, tries `parse_Int` -> succeeds with `IVar(x)`
3. Checks for `==` operator -> found, confirms cross-category path
4. Parses right side as `Int`
5. Returns `Bool::Eq(IVar(x), IVar(y))`

But if the input were just `x`:
1. Parser sees `Ident("x")` -- ambiguous
2. Saves position, tries `parse_Int` -> succeeds with `IVar(x)`
3. Checks for `==` -> NOT found
4. Backtracks, tries `parse_Bool_own` -> returns `BVar(x)`

### Solutions

1. **Minimize FIRST set overlap.** Use unique prefix terminals for rules where
   possible (e.g., `"not"` uniquely identifies Bool context).

2. **Order cross-category rules by specificity.** Put more specific rules
   (with unique starting tokens) before less specific ones.

3. **Verify with the FIRST set analysis.** Use the `LexerStats` output to
   check equivalence class counts, or add debug prints to
   `analyze_cross_category_overlaps()`:

   ```rust
   let overlaps = analyze_cross_category_overlaps(&categories, &first_sets);
   for ((a, b), overlap) in &overlaps {
       eprintln!(
           "Overlap {}/{}: ambiguous={:?}, unique_a={:?}, unique_b={:?}",
           a, b,
           overlap.ambiguous_tokens.tokens,
           overlap.unique_to_a.tokens,
           overlap.unique_to_b.tokens,
       );
   }
   ```

---

## 3. Parse Error Messages

### `unexpected character 'X' at position N`

**Source:** Lexer (`lex()` function).

The DFA reached a dead state on character `X`. This means the character is not
part of any terminal pattern or built-in token.

**Common causes:**
- Unicode characters in input (the lexer handles ASCII only)
- Special characters not declared as terminals in any rule
- Missing terminal in grammar (e.g., using `<` without declaring it)

**Fix:** Add the missing terminal to a grammar rule, or check for non-ASCII input.

### `expected 'TOKEN' at position N, found TOKEN2`

**Source:** Parser (`expect_token()` helper).

A structural rule expected a specific terminal but found something else.

**Common causes:**
- Missing delimiter (e.g., forgetting closing `)` or `}`)
- Wrong operator in expression
- Typo in keyword

**Fix:** Check the input syntax against the grammar rule's syntax pattern.

### `expected CATEGORY expression at position N, found TOKEN`

**Source:** Parser (`parse_<Cat>_prefix()` function).

The prefix handler could not match the current token to any rule in this category.

**Common causes:**
- Expression starts with a token not in the category's FIRST set
- Non-primary category used without type prefix (e.g., bare `x` for Bool variable)
- Missing rule for a construct you are trying to parse

**Fix:** Check that the token is a valid start for this category. For non-primary
categories, use the type prefix syntax (e.g., `bool:x`).

### `unexpected token TOKEN at position N after parsing`

**Source:** Parse entry point (`Cat::parse()`).

The parser successfully parsed an expression but there are leftover tokens.

**Common causes:**
- Two expressions without an operator between them (e.g., `3 4`)
- Missing infix operator
- Extra closing delimiters

**Fix:** Ensure the input is a single complete expression.

### `unexpected end of input, expected TOKEN`

**Source:** Parser (`expect_token()` or prefix handler).

The input ended before the parser finished matching a rule.

**Common causes:**
- Incomplete expression (e.g., `3 +` without right operand)
- Missing closing delimiter (e.g., `(3 + 4` without `)`)

---

## 4. Lexer Errors

### Keywords Not Recognized

**Symptom:** A keyword like `error` is lexed as `Ident("error")` instead of
`Token::KwError`.

**Cause:** The DFA's maximal munch produced an identifier instead of a keyword.
This happens if the keyword is followed by an alphanumeric character (e.g.,
`errors` is correctly an identifier, not the keyword `error`).

**Diagnostic:** Check that the keyword is followed by a non-identifier character
(space, operator, delimiter, or end of input).

### Integer vs. Float Ambiguity

**Symptom:** `3.14` is lexed as `Integer(3)`, `Dot`, `Integer(14)` instead of
`Float(3.14)`.

**Cause:** Float lexing is only enabled when the grammar has a native `f32` or
`f64` type. If no float type is declared, the `.` is treated as a separate token.

**Fix:** Declare a float native type: `![f64] as Float`.

### String Literal Issues

**Symptom:** Unterminated string literal causes `unexpected character` error.

**Cause:** The string literal NFA pattern matches `"[^"]*"`. If the closing quote
is missing, the DFA runs past the end of the string content into the dead state.

**Fix:** Ensure all string literals are properly quoted.

---

## 5. Precedence and Associativity Issues

### Wrong Precedence

**Symptom:** `2 + 3 * 4` parses as `(2 + 3) * 4` instead of `2 + (3 * 4)`.

**Cause:** In the `terms` block, operators declared earlier get lower precedence.
If `Mul` is declared before `Add`, multiplication will have lower precedence.

**Fix:** Declare operators in precedence order (lowest first):

```rust
terms {
    Add . a:Int, b:Int |- a "+" b : Int;   // Lowest precedence
    Mul . a:Int, b:Int |- a "*" b : Int;   // Higher precedence
}
```

### Wrong Associativity

**Symptom:** `2 ^ 3 ^ 4` parses as `(2 ^ 3) ^ 4` instead of `2 ^ (3 ^ 4)`.

**Cause:** All operators default to left-associativity. For right-associativity,
the `associativity` field on `RuleSpec` must be set to `Associativity::Right`.

**Fix:** Set associativity in the rule specification (this is done at the
`RuleSpec` level, which is set during macro expansion).

---

## 6. Collection Parsing Issues

### Empty Collection Not Parsed

**Symptom:** `{ }` fails to parse as an empty `HashBag`.

**Cause:** The collection parser loop attempts to parse at least one element.
If the first element parse fails, the loop exits with an empty collection, but
only if the error is caught (the `match` in the generated code uses
`Err(_) => break`).

**Fix:** This should work by default. If it fails, verify that the closing
delimiter token is not being consumed as part of the element parse.

### Separator Confusion

**Symptom:** `{ P1 | P2 | }` (trailing separator) fails.

**Cause:** After consuming the last separator, the parser tries to parse another
element, fails, and breaks. But now the position is past the separator, and the
closing delimiter check may fail.

**Fix:** Do not use trailing separators. The grammar expects
`element (sep element)*` without trailing separators.

---

## 7. Build and Compilation Issues

### `proc-macro2` Version Conflicts

**Symptom:** Compilation errors about incompatible `TokenStream` types.

**Fix:** Ensure all crates in the workspace use the same `proc-macro2` version.
Check `Cargo.lock` for duplicate versions.

### Macro Expansion Errors

**Symptom:** Cryptic errors during macro expansion.

**Diagnostic:** Use `cargo expand` to see the generated code:

```bash
cargo expand -p mettail-languages 2>/dev/null > expanded.rs
```

Check the expanded code for syntax errors or type mismatches.

### Large DFA Warning

**Symptom:** Compilation is slow or the generated code is very large.

**Cause:** A grammar with many terminals (>30 DFA states) triggers the table-driven
lexer, which generates a flat transition table. For very large grammars, this table
can be significant.

**Diagnostic:** Check `LexerStats`:
```rust
let (_code, stats) = generate_lexer(&input);
eprintln!("States: NFA={}, DFA={}, min={}, classes={}",
    stats.num_nfa_states, stats.num_dfa_states,
    stats.num_minimized_states, stats.num_equiv_classes);
```

---

## 8. Performance Tips

### Lexer Performance

The generated lexer is already highly optimized:
- Equivalence classes compress the transition table by ~15-20x
- Hopcroft's minimization reduces DFA states
- Direct-coded lexer (for small DFAs) avoids table indirection

For further optimization:
- Preallocate the token vector: `Vec::with_capacity(input.len() / 4)` (rough estimate)
- Use `&[u8]` instead of `&str` for input if you do not need UTF-8 validation

### Parser Performance

The Pratt parser runs in O(n) time. Key factors:
- **Token array is contiguous** -- good cache locality for sequential access
- **No backtracking** for same-category expressions
- **Bounded backtracking** for cross-category (save/restore, O(1) per decision point)

For faster parsing:
- Minimize the number of cross-category rules with ambiguous FIRST sets
  (each ambiguous token adds one save/restore attempt)
- Use unique prefix terminals where possible to avoid lookahead

### Diagnostic Benchmarking

To benchmark the parser:

```rust
use std::time::Instant;

let input = "1 + 2 * 3 + 4 * 5 + 6";
let start = Instant::now();
for _ in 0..10_000 {
    let _ = Int::parse(input);
}
let elapsed = start.elapsed();
println!("{:.2} us/parse", elapsed.as_micros() as f64 / 10_000.0);
```

Expected: sub-microsecond for simple expressions, low single-digit microseconds
for complex expressions.
