# X02: composition-priority-shadowing

**Severity:** Warning
**Category:** Composition
**Feature Gate:** (none -- always active when composition lints run)

## Description

Detects when a rule from grammar A is shadowed by a rule from grammar B for
the same token in a shared category. Shadowing occurs when both grammars
provide prediction WFST entries for the same token in the same category, but
grammar B's best weight is strictly lower (better) than grammar A's best
weight. In the tropical semiring used by WFST dispatch, lower weights have
higher priority, so B's rule will always be selected over A's.

For each shared category C, the lint queries both prediction WFSTs for every
token in the union of A's and B's FIRST sets:

    For token t ∈ FIRST_A(C) ∪ FIRST_B(C):
        weight_A = best prediction weight for t in WFST_A
        weight_B = best prediction weight for t in WFST_B

        If weight_A > weight_B:  → A's rule is shadowed by B's rule

```
  Token "+"
  ┌───────────────────────────────────┐
  │ Grammar A: AddA  (weight 0.800)  │  ← shadowed (worse weight)
  │ Grammar B: AddB  (weight 0.300)  │  ← wins dispatch
  └───────────────────────────────────┘
  Merged: AddB always selected for "+" → AddA is unreachable
```

This is distinct from X01 (new tokens) and X03 (dead rules) because the
shadowed rule is not dead in its source grammar -- it is only outcompeted
after composition. The rule may still be reachable via different tokens, so
it is not necessarily fully dead.

## Trigger Conditions

All of the following must hold:

- Two grammars A and B are composed via the composition lint framework.
- A `CompositionLintContext` is provided with prediction WFSTs from both
  source grammars.
- At least one shared category C exists with prediction WFSTs in both A
  and B.
- For some token t in that category, both A and B have predictions, and A's
  best weight is strictly greater (worse) than B's best weight.

One diagnostic is emitted per (category, token, shadowed rule) triple.

## Example

### Grammar

```rust
// Grammar A: defines "+" with weight 0.800
language! {
    name: ArithA,
    types { ![i32] as Expr },
    terms {
        AddA . a:Expr, b:Expr |- a "+" b : Expr;
    },
}

// Grammar B: defines "+" with weight 0.300 (higher priority)
language! {
    name: ArithB,
    types { ![i32] as Expr },
    terms {
        AddB . a:Expr, b:Expr |- a "+" b : Expr;
    },
}
```

### Output

```
warning[X02] (MergedArith): rule `AddA` from grammar A is shadowed by `AddB` from grammar B for token `+` in category `Expr` (weight 0.800 vs 0.300)
  = hint: rename rules or reorder declarations to avoid unintended priority override (WFST auto-assigns weights by declaration order)
```

## Resolution

1. **Reorder declarations.** Since WFST weights are assigned by declaration
   order, placing the intended higher-priority rule first ensures it receives
   a lower weight:

   ```
   // In merged grammar, declare AddA before AddB
   AddA . a:Expr, b:Expr |- a "+" b : Expr;
   AddB . a:Expr, b:Expr |- a "+" b : Expr;
   ```

2. **Rename rules to differentiate syntax.** If both rules should be
   reachable, change their terminal tokens so they no longer compete:

   ```
   AddA    . a:Expr, b:Expr |- a "+"  b : Expr;
   ConcatB . a:Expr, b:Expr |- a "++" b : Expr;
   ```

3. **Remove the shadowed rule.** If the shadowing is intentional (grammar B
   is meant to override grammar A's rule), remove the shadowed rule from the
   composition to make the intent explicit.

4. **Accept the shadowing.** If grammar B is an extension that intentionally
   overrides A's rules, the warning is informational. The WFST dispatch will
   always select B's rule.

## Hint Explanation

> rename rules or reorder declarations to avoid unintended priority override
> (WFST auto-assigns weights by declaration order)

The hint explains two mechanisms: (1) renaming rules so they no longer
compete for the same token removes the shadowing entirely, and (2) reordering
declarations changes the auto-assigned WFST weights. In PraTTaIL, rules
declared earlier receive lower tropical weights (higher priority). When two
rules from different grammars share a token, the one with the lower weight
wins dispatch. Reordering or explicit weight assignment can restore the
intended priority.

## Related Lints

- [X01](X01-composition-ambiguity-introduction.md) -- detects new tokens
  introduced by composition (ambiguity growth, not priority conflict)
- [X03](X03-composition-dead-rule-creation.md) -- detects rules that become
  fully dead after composition, which may be a consequence of shadowing
- [G06](../grammar/G06-shadowed-operator.md) -- single-grammar operator
  shadowing (the non-composition counterpart)
