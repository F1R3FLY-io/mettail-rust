# D13: parsed-but-unrewritten

**Severity:** Note
**Category:** decision-tree
**Feature Gate:** None (always enabled)

## Description

Detects constructor rules that are reachable in the decision tree's dispatch
trie (they can be parsed) but never appear in any Ascent equation or rewrite
rule's semantic dependency group. These "orphan" rules produce parse nodes that
the semantic evaluation layer never consumes or transforms.

This diagnostic correlates two independent analysis layers:

1. **Decision tree reachability**: the PathMap trie records which constructor
   rules have at least one dispatch path from a leading token to a successful
   parse.
2. **Semantic dependency groups**: the equation/rewrite/logic dependency
   analysis partitions rules into connected components by which constructors
   they reference. A rule not in any group is semantically disconnected.

When a constructor is trie-reachable but semantically disconnected, it means
the parser will successfully recognize the construct, but the Ascent fixpoint
engine will never process the resulting term. This is often (but not always) a
sign of a missing equation or rewrite rule.

```
  Trie-reachable rules vs. semantic dependency groups:

  Trie dispatch:    {Num, Add, Sub, Mul, Lit, Neg}
  Semantic groups:  {Num, Add, Sub, Mul, Neg}
                                          ───
  Orphan: Lit is parsed but never consumed by any equation
  ⟹ D13 fires for rule `Lit`
```

One diagnostic is emitted per orphan rule per category.

## Trigger Conditions

All of the following must hold:

- At least one semantic dependency group is available in the lint context
  (equations, rewrites, or logic blocks define dependency relationships).
- At least one decision tree is available in the lint context.
- A constructor rule label appears in the decision tree's `reachable_rules()`
  set but does not appear in any semantic dependency group.

One diagnostic is emitted per orphan rule.

## Example

### Grammar

```rust
language! {
    name: CalcLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . n:Expr |- n           : Expr;
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Lit  . |- "true"             : Expr;   // parsed but no equation references it
    },
    equations {
        Num(n) = n;
        Add(a, b) = a + b;
        // Note: no equation for Lit
    },
}
```

### Output

```
note[D13] (CalcLang): rule `Lit` is reachable in trie dispatch but appears in zero Ascent equations
  = in category `Expr`, rule `Lit`
  = hint: this constructor is parsed but never semantically consumed; verify it's needed or add an Ascent equation referencing it
```

## Resolution

1. **Add the missing equation or rewrite.** If the orphan rule is supposed
   to participate in semantic evaluation, add an equation (`Lit(x) = ...`) or
   rewrite (`Lit(x) -> ...`) that references the constructor. This connects
   it to the semantic dependency graph.

2. **Remove the unused rule.** If the constructor is genuinely dead code,
   remove it from the grammar. This also eliminates its dispatch path from
   the decision tree, potentially reducing lookahead depth.

3. **Accept the orphan.** Some constructors exist solely for pattern matching
   in user-defined `logic {}` blocks that bypass the standard dependency
   analysis. If the constructor is consumed by custom Ascent rules, this
   diagnostic is a false positive and can be safely ignored.

## Hint Explanation

The hint **"this constructor is parsed but never semantically consumed; verify
it's needed or add an Ascent equation referencing it"** highlights the
disconnect between the parse layer and the semantic layer. The parser
successfully builds AST nodes for this constructor, but no Ascent rule ever
inspects or transforms them. The two actions are:

- **Verify it's needed**: check whether the constructor should participate in
  evaluation. If it is consumed by custom `logic {}` rules, no change is needed.
- **Add an Ascent equation referencing it**: connect the constructor to the
  semantic layer by defining how it should be evaluated or transformed.

## Related Lints

- [D10](D10-dead-rule-weight.md) -- Lookahead waste. Orphan rules may
  contribute unnecessary depth to the decision tree without providing semantic
  value.
- [D03](D03-trie-unreachable-rule.md) -- Trie-unreachable rule. The inverse
  of D13: a rule exists in the grammar but has no dispatch path in the trie.
- [W01](../wfst/W01-dead-rule.md) -- WFST dead rule. A different unreachability
  analysis based on WFST weight analysis rather than trie dispatch.
