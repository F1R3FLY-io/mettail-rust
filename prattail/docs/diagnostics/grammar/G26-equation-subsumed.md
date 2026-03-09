# G26: equation-subsumed

**Severity:** Note
**Category:** Grammar Structure (macro phase)
**Feature Gate:** (none -- always active)

## Description

Reports that an equation has been eliminated from Ascent codegen because it
is **subsumed** by a more general equation. Subsumption means that every
term matched by the specific equation's LHS pattern is also matched by the
general equation's LHS pattern. Since the general equation already handles
all those cases, the specific equation is redundant and can be safely
removed without changing the grammar's semantics.

The subsumption analysis is performed by the pattern trie infrastructure
(Sprint 6 of the codegen optimization catalog). The `PatternIndex` builds a
trie of all equation and rewrite LHS patterns, then `detect_subsumption()`
identifies pairs where one pattern is strictly more general than another.
Only equation-equation pairs are eligible for elimination (rewrite
subsumption is reported as [G27](G27-rule-subsumption-candidate.md) instead,
since rewrite directionality requires manual review).

```
  General equation:  F(X, Y) = G(X, Y)     matches any F(a, b)
  Specific equation: F(A, B) = G(A, B)     matches any F(a, b)

  Since F(X, Y) ⊇ F(A, B) (same structure, just variable renaming),
  the specific equation is subsumed → G26 fires, equation eliminated.
```

For true subsumption (not just alpha-equivalence), the general pattern must
have strictly fewer constraints:

```
  General:  F(X, Y) = G(X, Y)    matches F(1, 2), F(a, b), ...
  Specific: F(X, X) = G(X, X)    matches F(1, 1), F(a, a), ...

  F(X, Y) ⊇ F(X, X) → specific is subsumed
```

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one equation.
- The pattern trie `detect_subsumption()` analysis identifies a pair where:
  - The general rule is an equation.
  - The specific rule is an equation.
  - The specific equation's index is in the `subsumed_equations` set.

One diagnostic is emitted per subsumed equation.

## Example

### Grammar

```rust
language! {
    name: Simplify,
    types { ![Expr] as Expr },
    terms {
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Zero . |- "0" : Expr;
    },
    equations {
        // General: any addition with zero on the right
        AddZeroR . a:Expr |- Add(a, Zero()) = a;
        // Specific: zero plus zero (subsumed by AddZeroR)
        ZeroZero . |- Add(Zero(), Zero()) = Zero();
    },
}
```

### Output

```
note[G26] (Simplify): equation `ZeroZero` eliminated -- subsumed by more general equation `AddZeroR`
  = hint: the more general equation `AddZeroR` covers all cases
```

## Resolution

No action is required. This is an informational diagnostic confirming that
redundant equations have been optimized away. The eliminated equation was
already covered by the more general one.

If the elimination is undesired:

1. **Differentiate the patterns.** Add a structural distinction to the
   specific equation's LHS so it is no longer subsumed:

   ```
   // Add a distinguishing constructor
   ZeroZero . |- Add(Zero(), Zero()) = Zero();  // now differs structurally
   ```

2. **Convert to a rewrite.** Rewrites are not auto-eliminated by subsumption
   (they receive [G27](G27-rule-subsumption-candidate.md) warnings instead):

   ```
   rewrites {
       ZeroZero . |- Add(Zero(), Zero()) => Zero();
   }
   ```

## Hint Explanation

> the more general equation `GeneralName` covers all cases

The hint identifies the general equation that subsumes the eliminated one.
Because equation semantics are symmetric (bidirectional), if the general
equation matches all terms that the specific equation matches, the specific
equation adds no new equivalences to the equality relation. Removing it
reduces the Ascent codegen size and fixpoint iteration count without
changing the grammar's observable behavior.

## Related Lints

- [G27](G27-rule-subsumption-candidate.md) -- fires for subsumption pairs
  that are NOT auto-eliminated (rewrites, or mixed equation/rewrite pairs)
  and require manual review
- [G31](G31-subsumed-equations-eliminated.md) -- summary lint reporting the
  total count of equations eliminated by subsumption
- [G25](G25-cancellation-pair-detected.md) -- a different equation
  elimination mechanism (cancellation pair suppression)
