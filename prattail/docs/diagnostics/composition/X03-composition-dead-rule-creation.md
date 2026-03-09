# X03: composition-dead-rule-creation

**Severity:** Warning
**Category:** Composition
**Feature Gate:** (none -- always active when composition lints run)

## Description

Detects rules that were live (reachable) in their source grammar but became
dead (unreachable) after composition. This lint computes the set-theoretic
difference between dead rules in the merged grammar and dead rules in either
source grammar:

    newly_dead = dead_rules_merged \ (dead_rules_A ∪ dead_rules_B)

A rule in `newly_dead` was reachable in its source grammar (it could be
dispatched to during parsing) but is no longer reachable in the composed
grammar. This typically happens when the composition introduces a
higher-priority rule for the same token prefix, causing the original rule
to be shadowed into unreachability.

```
  Grammar A (live)        Merged (dead)
  ┌──────────────┐       ┌──────────────┐
  │ Rule "Foo"   │       │ Rule "Foo"   │
  │ token: "x"   │  ──→  │ token: "x"   │
  │ live ✓       │       │ dead ✗       │
  └──────────────┘       └──────────────┘
                          Grammar B added a higher-priority
                          rule for token "x"
```

The diagnostic identifies which source grammar (A or B) the newly dead rule
originated from, helping the author trace the conflict.

## Trigger Conditions

All of the following must hold:

- Two grammars A and B are composed via the composition lint framework.
- A `CompositionLintContext` is provided with dead-rule sets from both source
  grammars and the merged grammar.
- At least one rule label appears in `dead_rules_merged` but not in
  `dead_rules_A` or `dead_rules_B`.

One diagnostic is emitted per newly dead rule.

## Example

### Grammar

```rust
// Grammar A: rule "Foo" is live (reachable)
language! {
    name: GrammarA,
    types { ![i32] as Expr },
    terms {
        Foo . a:Expr |- "x" a : Expr;
    },
}

// Grammar B: also defines a rule for token "x" with higher priority
language! {
    name: GrammarB,
    types { ![i32] as Expr },
    terms {
        Bar . a:Expr |- "x" a : Expr;
    },
}

// After composition, "Foo" from grammar A is shadowed by "Bar" from grammar B
// and becomes dead in the merged grammar.
```

### Output

```
warning[X03] (MergedGrammar): rule `Foo` was live in grammar A but became dead after composition (category `Expr`)
  = hint: the composed grammar may have a higher-priority rule that shadows this one -- verify intent or adjust weights
```

## Resolution

1. **Remove the dead rule.** If the composition intentionally replaces the
   rule, remove it from the source grammar to eliminate the warning:

   ```
   // Remove "Foo" from Grammar A since Grammar B's "Bar" supersedes it
   ```

2. **Adjust weights.** If the rule should remain live, modify declaration
   order or explicit weights so the rule is not outcompeted:

   ```
   // Declare "Foo" before "Bar" to give it higher priority
   Foo . a:Expr |- "x" a : Expr;
   Bar . a:Expr |- "x" a : Expr;
   ```

3. **Differentiate syntax.** Change the terminal prefix of one rule to
   avoid the collision:

   ```
   Foo . a:Expr |- "x"  a : Expr;
   Bar . a:Expr |- "xx" a : Expr;
   ```

4. **Accept the dead rule.** If the composition is an intentional override
   mechanism (e.g., an extension grammar replacing base grammar rules),
   the warning is informational.

## Hint Explanation

> the composed grammar may have a higher-priority rule that shadows this
> one -- verify intent or adjust weights

The hint identifies the most common cause: another rule in the composed
grammar has a lower (better) WFST weight for the same token prefix, causing
the original rule to become unreachable. The author should verify whether
this shadowing is intentional. If not, adjusting declaration order (which
controls auto-assigned weights) or adding distinguishing syntax will restore
reachability.

## Related Lints

- [X02](X02-composition-priority-shadowing.md) -- detects priority shadowing
  (the mechanism that often causes X03); X02 fires even when the shadowed
  rule is not fully dead, while X03 fires when it becomes completely
  unreachable
- [X01](X01-composition-ambiguity-introduction.md) -- detects new tokens
  introduced by composition that may contribute to the priority conflict
- [W01](../wfst/W01-unreachable-dead-rule.md) -- single-grammar dead-rule
  detection (the non-composition counterpart)
