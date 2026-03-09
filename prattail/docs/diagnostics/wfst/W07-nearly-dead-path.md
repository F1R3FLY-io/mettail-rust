# W07: nearly-dead-path

**Severity:** Note
**Category:** WFST-Specific
**Feature Gate:** none (always active)

## Description

Detects rules whose categories are technically **reachable** but have **very
few derivation paths** relative to the total across all categories.  While
[W01](W01-dead-rule.md) flags rules that are completely unreachable (dead),
W07 flags rules on the boundary -- they can be reached, but through so few
paths that they may be effectively dead in practice.

The detection uses `ProductWeight<BooleanWeight, CountingWeight>` analysis
over the inter-category dispatch graph:

```
  Category "Phantom":
  ┌─────────────────────────────────────────────────┐
  │  Forward-backward analysis:                      │
  │    BooleanWeight: reachable (true)              │
  │    CountingWeight: 1 path (out of 200 total)    │
  │                                                  │
  │    1 / 200 = 0.5%  <  1% threshold              │
  │    -> NearlyDeadPath flagged                     │
  └─────────────────────────────────────────────────┘
```

The `BooleanWeight` component confirms reachability (the category is not
outright dead).  The `CountingWeight` component counts the number of distinct
derivation paths through the category.  If the path count is less than **1%**
of the maximum count across all categories, the rule is flagged as
"nearly dead."

W07 uses Note severity rather than Warning because the rule is technically
functional.  It serves as a diagnostic hint that the category may be
under-connected in the grammar's inter-category graph.

## Trigger Conditions

All of the following must hold:

- The rule's category passes the `BooleanWeight` forward-backward reachability
  check (it is not already flagged by W01 Tiers 1-4).
- The rule's category has a `CountingWeight` derivation count that is less
  than **1%** of the maximum derivation count across all categories.
- The rule is not already flagged by any W01 tier (deduplication).

One diagnostic is emitted per rule in the nearly-dead category.

## Example

### Grammar

```rust
language! {
    name: SkewedLang,
    primary: Proc,
    // Proc has 10 rules, Name has 5, Atom has 1 (barely connected)
    terms {
        POutput  . |- "stdout" "!" "(" Str ")" : Proc;
        PEval    . |- "eval" "(" Int ")"       : Proc;
        // ... 8 more Proc rules ...

        NVar     . |- <ident>                  : Name;
        // ... 4 more Name rules ...

        // Atom: only one cast from Name, very few paths reach it
        AtomLit  . |- <int>                    : Atom;
    },
}
```

### Output

```
note[W07] (SkewedLang): rule `AtomLit` in category `Atom` is on a nearly-dead inter-category path (1/200 derivation paths)
  = hint: this category has very few derivation paths; consider simplifying or removing rules
```

When grouped:

```
note[W07] (SkewedLang): 3 rules on nearly-dead paths
  Bool: BoolLit, BoolAnd
  Str: StrConcat
```

## Resolution

1. **Add inter-category connections.**  If the category should be more
   reachable, add cast rules or cross-category references from well-connected
   categories.  This increases the derivation path count and silences W07.

2. **Remove the category.**  If the category is vestigial or under-utilized,
   removing it simplifies the grammar.  Rules in a nearly-dead category
   are unlikely to see real input.

3. **Simplify the grammar.**  If the category has a legitimate purpose but
   is over-shadowed by other categories, consider merging it with a more
   connected category to improve reachability.

4. **Ignore the note.**  If the low connectivity is intentional (e.g., the
   category handles rare edge cases or is a placeholder for future
   expansion), no action is needed.

## Hint Explanation

The hint **"this category has very few derivation paths; consider simplifying
or removing rules"** communicates that the category is structurally
under-connected:

- **Very few derivation paths** means that the forward-backward product
  weight is much lower than the grammar's average.  In practice, the parser
  will almost never dispatch to rules in this category.

- **Simplifying or removing** are the two natural responses: either improve
  connectivity (add paths) or accept the category's marginal role and
  potentially remove it.

## Related Lints

- [W01](W01-dead-rule.md) -- The stronger version: W01 flags truly
  unreachable rules (zero paths).  W07 flags rules with non-zero but very
  few paths.
- [G08](../grammar/G08-missing-cast-to-root.md) -- Detects categories with
  no directed cast path to the primary, which may contribute to low
  derivation counts.
- [W13](W13-wpds-unreachable.md) -- WPDS stack-aware analysis may reveal
  that a nearly-dead category is actually unreachable when the full call
  stack is considered.
