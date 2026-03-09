# G25: cancellation-pair-detected

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports that an equation in the grammar has been identified as a
**cancellation pair** and has been suppressed from the equality relation
(`eqrel`). A cancellation pair is an equation of the form:

    Outer(Inner(X)) = X

where composing two constructors and then applying the equation collapses the
nested structure back to the original value. This is a special case of an
inverse relationship: `Outer` and `Inner` are mutual inverses with respect
to nesting.

```
  Outer(Inner(X)) = X

  ┌───────────────────┐
  │ Inner(X)          │
  │   ┌─────────────┐ │
  │   │ Outer(...)  │ │  →  X
  │   └─────────────┘ │
  └───────────────────┘
  Cancellation: nesting undone
```

Cancellation pairs are problematic in the equality relation because they
create infinite equivalence classes: if `Outer(Inner(X)) = X`, then
`Outer(Inner(Outer(Inner(X)))) = X`, and so on to arbitrary depth. The Ascent
fixpoint computation would diverge. Instead, cancellation pairs are handled
by the `normalize()` function, which collapses them during term construction
rather than during equational reasoning.

This lint is **informational** (Note severity). It confirms that the pair was
detected and suppressed, so the author knows that the equation is being
handled efficiently via normalization rather than through the equality
relation.

## Trigger Conditions

All of the following must hold:

- The grammar defines equations (in the `equations` block or via implicit
  equation generation from constructor patterns).
- At least one equation matches the pattern `Outer(Inner(X)) = X`, where
  `Outer` and `Inner` are distinct constructors and `X` is a single
  variable.
- The cancellation pair detection pass in `equations.rs` successfully
  identifies the pair.

One diagnostic is emitted per detected cancellation pair.

## Example

### Grammar

```rust
language! {
    name: Exec,
    types {
        ![Process] as Proc
        ![Name] as Chan
    },
    terms {
        Quote   . p:Proc |- "@" p : Chan;
        Deref   . c:Chan |- "*" c : Proc;
    },
    equations {
        // Cancellation pair: Quote(Deref(c)) = c
        UnQuote . c:Chan |- Quote(Deref(c)) = c;
    },
}
```

### Output

```
note[G25] (Exec): equation `UnQuote` is a cancellation pair and has been suppressed
  = hint: Quote(Deref(X)) = X is handled by normalize() instead of eq_chan
```

## Resolution

No action is required. This is an informational diagnostic confirming correct
behavior. The cancellation pair is handled efficiently by `normalize()`.

If the suppression is undesired (rare), the equation can be restructured to
avoid the `Outer(Inner(X)) = X` pattern:

1. **Split into two directed rewrites.** Replace the equation with explicit
   rewrite rules that control the direction of simplification:

   ```
   rewrites {
       UnQuote . c:Chan |- Quote(Deref(c)) => c;
   }
   ```

2. **Accept the suppression.** The `normalize()` approach is strictly more
   efficient than equational reasoning for cancellation pairs, as it
   operates in O(1) per term construction rather than requiring fixpoint
   iteration.

## Hint Explanation

> Outer(Inner(X)) = X is handled by normalize() instead of eq_rel

The hint explains the mechanism: instead of adding the equation to the
Ascent-generated equality relation (which would cause infinite equivalence
class expansion), the compiler routes the cancellation through the
`normalize()` function. This function is called during term construction and
collapses `Outer(Inner(X))` to `X` immediately, preventing the nesting from
accumulating. The result is the same semantically but avoids divergence in
the fixpoint computation.

## Related Lints

- [W09](../wfst/W09-cancellation-pair-missing-rewrite.md) -- fires when a
  cancellation pair is suppressed but no corresponding directional rewrite
  exists, meaning the pair can only be collapsed during `normalize()` calls
  and not during Ascent's fixpoint iteration
- [G26](G26-equation-subsumed.md) -- equation eliminated by subsumption
  analysis (a different equation elimination mechanism)
- [G31](G31-subsumed-equations-eliminated.md) -- summary count of equations
  eliminated from codegen
