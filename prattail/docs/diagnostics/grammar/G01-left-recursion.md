# G01: left-recursion

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects left-recursive rules where the first syntax item is a NonTerminal of the same category as the rule's target category. Left recursion is problematic for recursive-descent and Pratt parsers because it causes infinite recursion: the parser calls itself on the same input position without consuming any tokens. PraTTaIL handles certain left-recursive patterns natively (infix, postfix, mixfix) through Pratt binding-power dispatch, but raw left recursion outside those patterns produces non-terminating parsers.

## Trigger Conditions

A warning is emitted when **all** of the following conditions hold:

1. The first `SyntaxItemSpec` of a rule is `NonTerminal { category }` where `category` matches the rule's own target category.
2. The rule does **not** match any of these Pratt-recognized patterns:
   - **Infix pattern:** exactly 2 NonTerminals of the same category + at least 1 Terminal, total length >= 3, and the last item is a same-category NonTerminal (e.g., `a "+" b`).
   - **Postfix pattern:** exactly 1 NonTerminal + exactly 1 Terminal, total length == 2 (e.g., `a "!"`).
   - **Mixfix pattern:** at least 3 NonTerminals + at least 2 Terminals (e.g., `c "?" t ":" e`).

Rules matching those patterns are handled by the Pratt parser's binding power mechanism and are excluded from this lint.

## Example

### Grammar

```
language! {
    name: BadCalc,
    types {
        ![i32] as Int
    },
    terms {
        // Left-recursive: first item is Int NonTerminal, target is Int,
        // but the pattern is not infix (3 NTs, only 1 T -- not enough
        // terminals for mixfix, too many NTs for infix)
        BadList . head:Int, sep:Int, tail:Int |- head "," sep tail : Int;

        // These do NOT trigger G01 (Pratt-handled patterns):
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;      // infix
        Fact . a:Int |- a "!" : Int ![{ (1..=a).product() }];    // postfix
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int;      // mixfix
    },
}
```

### Output

```
warning[G01]: left-recursive rule `BadList` in category `Int` (first item is NonTerminal of same category)
  = in category `Int`, rule `BadList`
  = hint: convert to infix/postfix pattern for Pratt handling, or restructure to avoid same-category leading NonTerminal
```

## Resolution

There are three strategies to resolve a G01 warning:

1. **Convert to an infix pattern.** If the rule expresses a binary operation, restructure it so exactly two same-category NonTerminals are separated by at least one Terminal. For example, change `head "," sep tail` to a proper infix rule `a "," b` where `a` and `b` are both the same category.

2. **Convert to a postfix pattern.** If the rule appends a token after a single expression, restructure it to the form `expr <terminal>` with exactly one NonTerminal and one Terminal.

3. **Eliminate the self-reference.** If neither infix nor postfix apply, introduce a new category for the leading position or use a Collection syntax item to express repetition:
   ```
   // Instead of: BadList . head:Int, tail:Int |- head "," tail : Int;
   // Use a Collection:
   IntList . items:[Int, ","] |- items : IntList;
   ```

## Hint Explanation

The hint "convert to infix/postfix pattern for Pratt handling, or restructure to avoid same-category leading NonTerminal" describes the two fundamental resolution paths. PraTTaIL's Pratt parser handles left recursion natively for infix (`a op b`), postfix (`a op`), and mixfix (`a op1 b op2 c`) patterns by using binding power to break the recursion: the left operand is parsed at a higher binding power, consuming the recursive call. Any other pattern where the first syntax item is a same-category NonTerminal will recurse infinitely because there is no binding-power mechanism to advance the parser position. The fix is either to reshape the rule into a recognized Pratt pattern or to break the self-reference by using a different category or a Collection.

## Related Lints

- [G03](./G03-ambiguous-prefix.md) -- multiple prefix rules sharing the same first terminal can co-occur with left-recursive rules that were restructured into prefix form
- [G10](./G10-ambiguous-associativity.md) -- after converting a left-recursive rule to infix form, mixed associativity at the same precedence level may trigger this lint
