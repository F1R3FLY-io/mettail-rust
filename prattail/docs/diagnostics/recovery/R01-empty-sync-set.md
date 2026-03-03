# R01: empty-sync-set

**Severity:** Warning
**Category:** Recovery

## Description

Detects categories whose recovery WFST has an empty `sync_tokens()` set. Sync tokens are the set of terminals that the error recovery system uses as resynchronization points when a parse error occurs: the recovery algorithm scans ahead in the token stream looking for one of these tokens, then resumes normal parsing from that point. When the sync set is empty, there are no valid resynchronization targets, so the recovery system has no choice but to skip every remaining token until it reaches the end of the input (EOF). This effectively disables incremental error recovery for the category, meaning a single syntax error anywhere in the category causes all subsequent tokens to be discarded and only one error is reported -- any additional errors downstream are lost.

The sync set is populated from two sources: (1) the category's FOLLOW set, which contains tokens that can legally appear after a complete parse of the category, and (2) structural delimiters (`(`, `)`, `{`, `}`, `[`, `]`, `,`, `;`) that are globally recognized as recovery landmarks. A category triggers this lint when neither source contributes any tokens to the sync set, which typically indicates that the category is either unreferenced (no other rule consumes it, so the FOLLOW set is empty) or that it is a leaf category with no structural delimiters in its grammar.

## Trigger Conditions

A warning is emitted when **all** of the following conditions hold:

1. A `RecoveryWfst` exists for the category (i.e., the category has at least one rule and was processed by the recovery pipeline).
2. The `sync_tokens()` method on that `RecoveryWfst` returns an empty set (zero tokens).

## Example

### Grammar

```
language! {
    name: Minimal,
    types {
        ![i32] as Num
    },
    terms {
        // `Num` is a leaf category: no other category references it via
        // a NonTerminal, so its FOLLOW set is empty. The grammar also
        // uses no structural delimiters, so no delimiters leak into the
        // sync set either.
        Lit   . n:Num |- n               : Num ![n];
        Neg   . a:Num |- "-" a           : Num ![- a];
        Add   . a:Num, b:Num |- a "+" b  : Num ![a + b];
    },
}
```

### Output

```
warning[R01]: category `Num` has no sync tokens -- recovery always skips to EOF
  = in category `Num`
  = hint: add structural delimiters or ensure the category has FOLLOW set tokens
```

## Resolution

There are two complementary strategies to resolve an R01 warning:

1. **Add structural delimiters to the grammar.** Introduce bracketed syntax or statement terminators that use standard structural delimiters (`(`, `)`, `;`, etc.). For example, adding a parenthesized grouping rule (`"(" Num ")"`) ensures that `)` appears in the FOLLOW set of `Num` and is available as a sync token.

   ```
   Group . a:Num |- "(" a ")" : Num ![a];
   ```

2. **Ensure the category is referenced by other rules.** If the category is consumed as a NonTerminal in another category's rule, the FOLLOW set is populated by the tokens that can appear after that NonTerminal position. For example, if an `Expr` category has a rule `Stmt . e:Num |- e ";" : Stmt`, then `";"` enters the FOLLOW set of `Num`.

3. **Combine both strategies.** Real grammars almost always have both structural delimiters and cross-category references. Adding even one semicolon-terminated statement rule and one parenthesized grouping rule typically populates the sync set with 2-4 tokens, which is sufficient for effective recovery.

## Hint Explanation

The hint "add structural delimiters or ensure the category has FOLLOW set tokens" identifies the two sources that populate the sync set. Structural delimiters (`(){}[],;`) are globally recognized by PraTTaIL's recovery system as safe resynchronization points because they serve as unambiguous boundaries in nearly all programming languages. FOLLOW set tokens are computed by the prediction pipeline: they are the set of terminals that can legally follow a complete derivation of the category. By adding tokens from either source, the recovery system gains at least one resynchronization target, which allows it to skip only the erroneous tokens (rather than everything through EOF) and attempt to parse further tokens after the sync point, potentially catching additional errors in a single pass.

## Related Lints

- [G05](../grammar/G05-empty-category.md) -- an empty category (zero rules) will also have an empty sync set, but the root cause is different: G05 fires when no rules exist at all, while R01 fires when rules exist but produce no FOLLOW/delimiter tokens
- [R02](./R02-sparse-recovery.md) -- a category with exactly 1 sync token is marginally better than 0, but still offers limited recovery; R02 is the "next step up" from R01
