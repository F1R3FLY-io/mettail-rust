# R07: transposition-candidate

**Severity:** Note
**Category:** Recovery

## Description

Identifies pairs of non-structural operator terminals in the grammar whose Levenshtein (character edit) distance is exactly 1. These pairs are prime candidates for the `SwapTokens` repair action during error recovery: when a programmer mistypes one operator as the other (e.g., `+=` instead of `-=`, or `&&` instead of `&`), the recovery system can detect and correct the typo with a single-character substitution at the `swap_cost` rate rather than a more expensive delete-then-insert sequence.

The lint collects all unique terminal tokens from the grammar, excluding structural delimiters (`(`, `)`, `{`, `}`, `[`, `]`, `,`, `;`) which are not operators and are handled separately by bracket-aware recovery. It then performs an all-pairs comparison using a specialized `char_edit_distance_is_one` function that checks for exactly one of:

- **Same-length substitution:** the two strings have the same character count and differ in exactly one position (e.g., `+` vs `-`, `==` vs `!=`, `<=` vs `>=`).
- **Length-differ-by-1 insertion/deletion:** the two strings differ in length by exactly 1 character, and the shorter string can be obtained by deleting one character from the longer string (e.g., `&` vs `&&`, `=` vs `==`, `|` vs `||`).

The lint emits a single summary note listing the total count and up to 8 sample pairs. If there are more than 8 pairs, the remaining count is shown as "(N more)". This avoids O(n^2) diagnostic output for grammars with many similar operators.

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The grammar contains at least 2 unique non-structural operator terminals.
2. At least one pair of those terminals has a character edit distance of exactly 1.

The lint does **not** fire if:
- All operator terminals are structurally distinct (edit distance >= 2 for all pairs).
- The grammar contains only structural delimiters and no operator terminals.

## Example

### Grammar

```
language! {
    name: RichOps,
    types {
        ![i32] as Expr,
        ![bool] as Bool
    },
    terms {
        // Expr rules
        Lit    . n:Expr |- n                     : Expr ![n];
        Neg    . a:Expr |- "-" a                 : Expr ![- a];
        Add    . a:Expr, b:Expr |- a "+" b       : Expr ![a + b];
        Sub    . a:Expr, b:Expr |- a "-" b       : Expr ![a - b];
        Mul    . a:Expr, b:Expr |- a "*" b       : Expr ![a * b];
        Div    . a:Expr, b:Expr |- a "/" b       : Expr ![a / b];
        Mod    . a:Expr, b:Expr |- a "%" b       : Expr ![a % b];
        AddEq  . a:Expr, b:Expr |- a "+=" b     : Expr ![a + b];
        SubEq  . a:Expr, b:Expr |- a "-=" b     : Expr ![a - b];
        MulEq  . a:Expr, b:Expr |- a "*=" b     : Expr ![a * b];
        DivEq  . a:Expr, b:Expr |- a "/=" b     : Expr ![a / b];
        Assign . a:Expr, b:Expr |- a "=" b       : Expr ![b];
        Group  . a:Expr |- "(" a ")"             : Expr ![a];

        // Bool rules
        Eq     . a:Expr, b:Expr |- a "==" b     : Bool ![a == b];
        Neq    . a:Expr, b:Expr |- a "!=" b     : Bool ![a != b];
        Lt     . a:Expr, b:Expr |- a "<" b       : Bool ![a < b];
        Gt     . a:Expr, b:Expr |- a ">" b       : Bool ![a > b];
        Le     . a:Expr, b:Expr |- a "<=" b     : Bool ![a <= b];
        Ge     . a:Expr, b:Expr |- a ">=" b     : Bool ![a >= b];
        And    . a:Bool, b:Bool |- a "&&" b      : Bool ![a && b];
        Or     . a:Bool, b:Bool |- a "||" b      : Bool ![a || b];
        Not    . a:Bool |- "!" a                 : Bool ![! a];
    },
}
```

The non-structural operator terminals are: `-`, `+`, `*`, `/`, `%`, `+=`, `-=`, `*=`, `/=`, `=`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `&&`, `||`, `!`. The pairs with edit distance = 1 include:

| Pair | Distance Type |
|------|---------------|
| `+` <-> `-` | substitution (same length, 1 char differs) |
| `<` <-> `>` | substitution |
| `=` <-> `==` | insertion/deletion (length differs by 1) |
| `!` <-> `!=` | insertion/deletion |
| `+=` <-> `-=` | substitution |
| `*=` <-> `/=` | substitution |
| `<=` <-> `>=` | substitution |
| `<=` <-> `!=` | substitution |
| `&&` <-> `||` | substitution (both chars differ -- **not** distance 1) |

Note: `&&` <-> `||` has edit distance 2 (two character substitutions), so it is **not** included. The actual pairs found depend on the full pair-wise analysis; the example above is illustrative.

### Output

```
note[R07]: 8 operator pair(s) differ by 1 character (SwapTokens repair candidates): `+`<->`-`, `<`<->>`>`, `=`<->`==`, `!`<->`!=`, `+=`<->`-=`, `*=`<->`/=`, `<=`<->`>=`, `<=`<->`!=`
  = hint: the error recovery system can detect and fix common typos between these operators via SwapTokens
```

## Resolution

This lint is informational (Note severity) and does not require action. It exists to inform the grammar author about which operator pairs the recovery system can automatically correct via the `SwapTokens` repair action. However, the information can be used in several ways:

1. **Verify swap_cost is reasonable.** The `SwapTokens` repair action uses `swap_cost` from `RecoveryConfig` (default: 1.25). If many operator pairs are candidates, a well-tuned swap cost ensures that transposition repairs are preferred over the more expensive substitute or insert actions. See [R06](./R06-inverted-recovery-costs.md) for cost hierarchy validation.

2. **Consider operator disambiguation.** If two operators with edit distance 1 have very different semantics (e.g., `=` assignment vs `==` equality), the grammar author may want to add additional context-sensitive recovery hints or adjust error messages to help users distinguish between them.

3. **Review operator naming.** If the number of close-distance pairs is very high (e.g., 20+ pairs), the grammar may benefit from more distinctive operator syntax to reduce the likelihood of typos, though this is a language design decision rather than a PraTTaIL configuration issue.

4. **No action needed.** For most grammars, this note simply confirms that the recovery system is aware of common typo patterns and will handle them automatically.

## Hint Explanation

The hint "the error recovery system can detect and fix common typos between these operators via SwapTokens" explains the practical consequence of the analysis. The `SwapTokens` repair action is one of five repair strategies available to the Viterbi recovery search. When the parser encounters an unexpected token and the actual token differs from an expected token by exactly 1 character edit, the `SwapTokens` action can replace the actual token with the expected one at `swap_cost` (default: 1.25), which is cheaper than the general `substitute_cost` (1.5) or a delete-then-insert sequence (1.0 + 2.0 = 3.0). The pairs identified by this lint are precisely those for which the SwapTokens action can fire, so the note serves as a preview of the recovery system's typo-correction capabilities for the given grammar.

## Related Lints

- [R06](./R06-inverted-recovery-costs.md) -- validates that the cost hierarchy is correct, which directly affects whether SwapTokens repairs are preferred over more expensive alternatives; an inverted hierarchy could cause the recovery system to ignore swap opportunities in favor of less optimal repairs
