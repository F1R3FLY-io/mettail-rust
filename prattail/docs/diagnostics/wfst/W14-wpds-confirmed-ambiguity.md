# W14: wpds-confirmed-ambiguity

**Severity:** Warning (confirmed) / Note (false positive)
**Category:** WFST-Specific

## Description

Distinguishes genuine pushdown-level ambiguity from WFST false-positives for categories with NFA spillover. When a category has NFA spillover (multiple RD rules share a dispatch token), the ambiguity may be:

- **WFST false positive** (Note severity): The category is WPDS-unreachable, so the NFA ambiguity can never manifest in practice.
- **Confirmed ambiguity** (Warning severity): The category is WPDS-reachable AND has multiple calling contexts with fan-in > 0, confirming that different stack configurations can reach the ambiguous dispatch point.

## Trigger Conditions

A W14 diagnostic fires when:

1. A category appears in `nfa_spillover_categories` (has NFA-ambiguous prefix groups).
2. WPDS analysis is available.
3. If the category is NOT in `reachable_categories`: emit Note (false positive).
4. If the category IS reachable AND has `fan_in > 0` AND `calling_context_count > 1`: emit Warning (confirmed).

## Example

### Grammar (false positive path)

```
language! {
    name: FalsePositiveExample;
    primary: Expr;
    category Expr { Num = INTEGER; Add = Expr "+" Expr; }
    category Phantom {
        PhantomA = "phantom" Phantom;
        PhantomB = "phantom" "(" Phantom ")";
        // Both start with "phantom" -> NFA spillover
        // But no category calls Phantom
    }
}
```

### Output (false positive)

```
note[W14]: NFA spillover for `Phantom` may be a WFST false-positive
           (category is WPDS-unreachable)
  = hint: WPDS stack-aware analysis suggests this category is unreachable;
          the NFA ambiguity may not manifest in practice
```

### Grammar (confirmed ambiguity)

```
language! {
    name: ConfirmedExample;
    primary: Expr;
    category Expr {
        Num = INTEGER;
        UseType = "(" Type ")";
        UseDecl = "let" Decl;
    }
    category Type {
        IntType = "int";
        ArrType = "int" "[" "]";
        // NFA spillover on "int"
    }
    category Decl { LetDecl = Type Expr; }
}
```

### Output (confirmed)

```
warning[W14]: NFA spillover for `Type` is confirmed at pushdown level
              (2 calling contexts, fan-in=2)
  = hint: the ambiguity is genuine: multiple stack configurations can reach
          this category's dispatch point
```

## Resolution

- **False positive (Note):** No action needed. The WFST-level ambiguity cannot manifest because the category is never called. Consider removing the unreferenced category.
- **Confirmed (Warning):** The ambiguity is real. Consider adding distinguishing tokens to the ambiguous rules, or accept the NFA save/restore overhead.

## Hint Explanation

The WPDS poststar analysis determines whether stack configurations leading to the ambiguous category actually arise during parsing. If they don't, the NFA spillover machinery will never execute -- the ambiguity is a phantom.

## Related Lints

- [W02](W02-nfa-ambiguous-prefix.md) -- NFA-ambiguous prefix detection (structural). W14 confirms or denies at pushdown level.
- [W10](W10-multi-token-lookahead-required.md) -- Multi-token lookahead for NFA disambiguation.
- [W13](W13-wpds-unreachable.md) -- Stack-aware dead-rule detection. W14 Note severity aligns with W13 unreachability.
