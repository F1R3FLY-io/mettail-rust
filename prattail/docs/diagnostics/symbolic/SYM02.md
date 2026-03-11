# SYM02: overlapping-guards

**Severity:** Warning
**Module:** M1 Symbolic Automata
**Feature gate:** `symbolic-automata`

## What It Detects

- Two guards on the same channel have overlapping (non-disjoint) domains: there exist inputs that satisfy both guards simultaneously.
- When multiple guards overlap, the runtime must either pick one arbitrarily (nondeterministic choice) or execute both branches (ambiguous dispatch). Either outcome may violate the programmer's intent.

## Example

### Triggering Code

```
language! {
    name: Router;
    primary: Proc;

    category Proc {
        HandleLow  = "for" "(" "@x" ":" "x < 100" "<-" ch ")" "{" LowProc  "}";
        HandleHigh = "for" "(" "@x" ":" "x > 50"  "<-" ch ")" "{" HighProc "}";
        Zero = "0";
    }
}
```

Here, values in the range `(50, 100)` satisfy both `x < 100` and `x > 50`.

### Diagnostic Output

```
warning[SYM02] (Router): guards 'x < 100' and 'x > 50' overlap (non-disjoint)
  = hint: add disambiguation predicates or merge the guards
```

### Fix

```
// Make the guards disjoint:
HandleLow  = "for" "(" "@x" ":" "x <= 50" "<-" ch ")" "{" LowProc  "}";
HandleHigh = "for" "(" "@x" ":" "x > 50"  "<-" ch ")" "{" HighProc "}";
```

## Rationale

- Guard overlap is detected via `BooleanAlgebra::is_satisfiable(and(g1, g2))`. If the conjunction is satisfiable, the `witness()` function can produce a concrete domain element in the overlap, which serves as a counterexample.
- In process algebra, overlapping guards on the same channel create a race condition: the outcome depends on which receive fires first. For deterministic semantics, guards must partition the input domain.
- The SFA intersection algorithm runs in O(|Q_1| x |Q_2| x |delta_1| x |delta_2|) with a SAT query per transition pair, making the check tractable for typical guard sizes.

## Related Lints

- [SYM01](SYM01.md) -- Unsatisfiable guard: the degenerate case where one guard accepts nothing
- [SYM03](SYM03.md) -- Subsumed guard: a special case of overlap where one guard is entirely contained in the other
- [SYM04](SYM04.md) -- Non-minimal guards: overlapping guards often indicate the SFA has mergeable states
- [PR01](../probabilistic/PR01.md) -- Low selectivity rule: probabilistic analysis may reveal that the overlap region is rarely exercised
