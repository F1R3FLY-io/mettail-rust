# SYM03: subsumed-guard

**Severity:** Note
**Module:** M1 Symbolic Automata
**Feature gate:** `symbolic-automata`

## What It Detects

- Guard A is subsumed by guard B, meaning every input accepted by A is also accepted by B: `L(A) subseteq L(B)`.
- The subsumed guard is redundant -- it can never fire exclusively. Any input that would trigger A also triggers B, so the subsumed guard adds no distinguishing power.

## Example

### Triggering Code

```
language! {
    name: Filter;
    primary: Proc;

    category Proc {
        HandleSmall = "for" "(" "@x" ":" "x > 0 /\ x < 50"  "<-" ch ")" "{" SmallProc "}";
        HandleAny   = "for" "(" "@x" ":" "x > 0 /\ x < 100" "<-" ch ")" "{" AnyProc   "}";
        Zero = "0";
    }
}
```

The guard `x > 0 /\ x < 50` is subsumed by `x > 0 /\ x < 100`.

### Diagnostic Output

```
note[SYM03] (Filter): guard 'x > 0 /\ x < 50' is subsumed by 'x > 0 /\ x < 100' (redundant)
  = hint: the subsumed guard can be removed without affecting behavior
```

### Fix

```
// Option 1: Remove the subsumed guard and handle all values in one branch.
HandleAny = "for" "(" "@x" ":" "x > 0 /\ x < 100" "<-" ch ")" "{" AnyProc "}";

// Option 2: Make guards disjoint with explicit ranges.
HandleSmall = "for" "(" "@x" ":" "x > 0 /\ x < 50"   "<-" ch ")" "{" SmallProc "}";
HandleLarge = "for" "(" "@x" ":" "x >= 50 /\ x < 100" "<-" ch ")" "{" LargeProc "}";
```

## Rationale

- Subsumption is checked via `complement(B) intersection A` emptiness. If `L(A) intersection L(complement(B)) = emptyset`, then every word in `L(A)` is also in `L(B)`, confirming subsumption.
- Subsumed guards waste dispatch effort: the runtime evaluates both guards and must resolve the overlap. If dispatch is priority-ordered, the subsumed guard is effectively dead code.
- This is a strict refinement of SYM02 (overlap): subsumption implies overlap, but not vice versa. When subsumption is detected, the diagnostic is more actionable than a generic overlap warning.

## Related Lints

- [SYM01](SYM01.md) -- Unsatisfiable guard: the extreme case where a guard accepts nothing at all
- [SYM02](SYM02.md) -- Overlapping guards: the general case; subsumption is a special form of overlap
- [SYM04](SYM04.md) -- Non-minimal guards: subsumed guards are a primary source of non-minimality in the SFA
- [MS02](../multiset/MS02.md) -- Redundant feature check: the multiset-level analogue of tautological guards
