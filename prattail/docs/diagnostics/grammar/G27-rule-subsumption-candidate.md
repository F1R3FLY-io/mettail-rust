# G27: rule-subsumption-candidate

**Severity:** Warning
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Warns that a rule (equation or rewrite) may be subsumed by a more general
rule -- both LHS patterns match the same terms, but the general rule's
pattern is strictly more permissive. Unlike [G26](G26-equation-subsumed.md),
this lint fires for cases where automatic elimination is **not** safe:
rewrite rules (which have directional semantics) and mixed equation/rewrite
pairs (where subsumption does not guarantee semantic equivalence).

The subsumption analysis comes from the pattern trie's `detect_subsumption()`
pass. A subsumption pair (general, specific) satisfies:

    ∀ term t: specific.LHS matches t ⟹ general.LHS matches t

When the specific rule is a rewrite or the general rule is a rewrite, the
elimination cannot be automated because:

- Rewrite directionality: `l => r` and `l => r'` may have different RHS
  expressions even with the same LHS pattern.
- Semantic differences: the specific rule may have a different reduction
  strategy (e.g., `fold` vs `step`) or produce a different result.

```
  General rule:  Add(X, Zero()) => X       (rewrite, any X)
  Specific rule: Add(Zero(), Zero()) => Z  (rewrite, specific case)

  The general rule's LHS subsumes the specific rule's LHS,
  but their RHS expressions may differ → manual review needed.
```

G27 diagnostics are eligible for **grouping**: when multiple specific rules
are subsumed by the same general rule, the diagnostic grouper consolidates
them into a single message listing all candidates.

## Trigger Conditions

All of the following must hold:

- The grammar defines equations or rewrites.
- The pattern trie `detect_subsumption()` analysis identifies a pair where
  the specific rule's LHS is subsumed by the general rule's LHS.
- The pair is NOT an equation-equation pair where both are in the
  `subsumed_equations` set (those are reported as G26 instead).

One diagnostic is emitted per subsumption pair.

## Example

### Grammar

```rust
language! {
    name: Simplify,
    types { ![Expr] as Expr },
    terms {
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Mul  . a:Expr, b:Expr |- a "*" b : Expr;
        Zero . |- "0" : Expr;
        One  . |- "1" : Expr;
    },
    rewrites {
        // General: addition with zero simplifies to the other operand
        AddZeroR . a:Expr |- Add(a, Zero()) => a;
        // Specific: multiplication by one (different operation, but
        // if the pattern trie sees shared prefix structure, it may
        // flag subsumption)
        MulOneR  . a:Expr |- Mul(a, One()) => a;
    },
}
```

### Output (grouped)

```
warning[G27] (Simplify): rule `MulOneR` may be subsumed by more general rule `AddZeroR` (both LHS patterns match the same terms, but `AddZeroR` is more general)
  = hint: review whether rule `MulOneR` can be removed or merged with `AddZeroR`
```

### Output (grouped, multiple candidates)

```
warning[G27] (Simplify): 3 rules may be subsumed by more general rule `AmbCong`
    candidates: AmbNew, OutRule, FooRule
  = hint: review whether rule can be removed or merged
```

## Resolution

1. **Remove the specific rule.** If the general rule already handles all
   cases correctly, the specific rule is redundant:

   ```
   // Keep only the general rule
   AddZeroR . a:Expr |- Add(a, Zero()) => a;
   // Remove MulOneR if AddZeroR covers its cases
   ```

2. **Merge the rules.** If both rules serve similar purposes, combine them
   into a single more general rule with appropriate case handling.

3. **Differentiate the LHS patterns.** If the rules serve genuinely
   different purposes, add structural distinctions so the specific rule
   is no longer subsumed:

   ```
   AddZeroR . a:Expr |- Add(a, Zero()) => a;
   MulOneR  . a:Expr |- Mul(a, One()) => a;  // different constructor
   ```

4. **Accept the subsumption.** If the specific rule handles a special case
   with different RHS semantics (e.g., a more efficient computation path),
   the subsumption warning is informational. The specific rule will still
   execute when its more constrained pattern matches.

## Hint Explanation

> review whether rule `SpecificName` can be removed or merged with
> `GeneralName`

The hint identifies the two rules involved and recommends a manual review.
Unlike G26 (where elimination is automatic and safe), G27 requires human
judgment because the RHS expressions or reduction strategies may differ.
The author should compare the two rules' right-hand sides and determine
whether the specific rule adds value beyond what the general rule provides.

## Related Lints

- [G26](G26-equation-subsumed.md) -- fires when an equation IS
  auto-eliminated by subsumption (the automatic counterpart to G27)
- [G28](G28-alpha-equivalent-groups.md) -- reports groups of rules with
  alpha-equivalent LHS patterns (same structure, different names)
- [G24](G24-alpha-equivalent-rules.md) -- pipeline-phase detection of
  alpha-equivalent rules within a category
- [G31](G31-subsumed-equations-eliminated.md) -- summary count of equations
  eliminated from codegen
