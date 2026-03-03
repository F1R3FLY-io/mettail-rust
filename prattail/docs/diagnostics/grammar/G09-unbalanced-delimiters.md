# G09: unbalanced-delimiters

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects rules where the count of opening delimiter characters does not match the
count of closing delimiter characters across all terminal strings in the rule's
syntax. The lint checks three delimiter pairs:

| Open | Close |
|------|-------|
| `(` | `)` |
| `{` | `}` |
| `[` | `]` |

Counting is performed at the character level within each terminal string, not at the
terminal-string level. This means compound terminals like `"in("` contribute 1 to
the open-parenthesis count, and self-balanced terminals like `"()"` contribute 1 to
both the open and close counts. The lint sums character counts across all terminals
in the rule (including separators from `Collection`, `BinderCollection`, and
`ZipMapSep` items, and recursively into `Optional` and `ZipMapSep` body items).

An unbalanced delimiter in a grammar rule almost always indicates a typo or omission.
Because PraTTaIL's structural delimiters `(){}[],` are always included in the
terminal set, a missing closing bracket will cause parse failures that are difficult
to diagnose from the generated parser alone.

## Trigger Conditions

The lint fires when **all** of the following conditions hold for a given rule:

1. The rule's syntax items are collected into a flat list of terminal strings via
   `collect_terminals_flat()`, which:
   - Extracts `Terminal(t)` strings directly.
   - Extracts `separator` strings from `Collection`, `BinderCollection`, and
     `ZipMapSep` items.
   - Recurses into `ZipMapSep.body_items` and `Optional.inner`.
2. For at least one delimiter pair `(open_char, close_char)`:
   - The sum of `open_char` occurrences across all terminal strings differs from
     the sum of `close_char` occurrences.

The lint fires once per unbalanced pair per rule. A single rule can produce multiple
diagnostics if, for example, both parentheses and braces are unbalanced.

## Example

### Grammar

```
language! {
    name: Lambda,
    types {
        ![i32] as Proc
        ![i32] as Int
    },
    terms {
        // Correct: balanced parentheses
        App    . f:Proc, x:Proc |- f "(" x ")" : Proc ![f] step;

        // Bug: missing closing parenthesis
        LetIn  . x:Int, body:Proc |- "let" x "=" "(" body : Proc ![body] step;

        // Correct: compound terminal "in(" contributes 1 open-paren,
        // and the closing ")" contributes 1 close-paren
        PIn    . ch:Int, body:Proc |- "in(" ch ")" body : Proc ![body] step;

        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        IntToProc . a:Int |- a : Proc ![a] step;
    }
}
```

The `LetIn` rule has one `"("` terminal but no matching `")"`. The `PIn` rule is
correctly balanced because `"in("` contains one `(` character and the separate `")"`
terminal contains one `)` character.

### Output

```
warning[G09]: rule `LetIn` in category `Proc` has unbalanced delimiters: 1 `(` vs 0 `)`
  --> <macro>:12:9
  = in category `Proc`, rule `LetIn`
  = hint: add the missing `)` delimiter
```

## Resolution

To resolve this warning, examine the rule's terminal sequence and add the missing
delimiter:

1. **Identify the missing delimiter.** The diagnostic message shows the exact counts
   for each character of the unbalanced pair. In the example above, there is 1 `(`
   but 0 `)`.

2. **Add the missing terminal.** Insert the closing delimiter at the appropriate
   position in the rule's syntax:

   ```
   // Fixed: closing parenthesis added
   LetIn . x:Int, body:Proc |- "let" x "=" "(" body ")" : Proc ![body] step;
   ```

3. **Verify compound terminals.** If your grammar uses compound terminals that
   contain bracket characters (e.g., `"in("`, `"begin{"`, `"@["`), ensure that the
   corresponding closing bracket appears elsewhere in the same rule. The lint's
   character-level counting handles these correctly:

   ```
   // "in(" has 1 open-paren, ")" has 1 close-paren => balanced
   PIn . ch:Int, body:Proc |- "in(" ch ")" body : Proc ![body] step;
   ```

4. **Intentional imbalance.** In rare cases, a rule may intentionally have an
   unbalanced delimiter (e.g., a rule that parses only the opening part of a
   bracketed expression, with the closing bracket handled by a different rule or
   recovery mechanism). If this is intentional, acknowledge the warning. Consider
   restructuring the grammar so that each rule is self-contained with respect to
   delimiters.

## Hint Explanation

> add the missing `{delimiter}` delimiter

The hint identifies which specific delimiter character is missing based on the count
imbalance:

- If `open_count > close_count`, the missing delimiter is the **close** character
  (e.g., `)`, `}`, `]`).
- If `close_count > open_count`, the missing delimiter is the **open** character
  (e.g., `(`, `{`, `[`).

The hint names the exact character to add. The grammar author must determine the
correct position within the rule's syntax sequence where the delimiter should appear,
as the lint cannot infer positional intent from the grammar structure alone.

## Related Lints

- [R05](../recovery/R05-missing-bracket-sync.md) -- detects opening brackets that appear in a category's terminal set but whose matching closing bracket is absent from the sync set used for error recovery; this is a related but distinct issue at the category level rather than the rule level
