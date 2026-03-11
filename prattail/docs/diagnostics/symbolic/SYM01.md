# SYM01: unsatisfiable-guard

**Severity:** Warning
**Module:** M1 Symbolic Automata
**Feature gate:** `symbolic-automata`

## What It Detects

- A receive guard predicate evaluates to BOT (the false predicate) under the Boolean algebra, meaning no element of the domain can ever satisfy it.
- This results in a dead receive: the guarded branch can never be taken at runtime, wasting compile-time resources and potentially hiding a logic error in the predicate specification.

## Example

### Triggering Code

```
language! {
    name: Protocol;
    primary: Proc;

    category Proc {
        Recv = "for" "(" Guard "<-" Chan ")" "{" Proc "}";
        Send = Chan "!" "(" Expr ")";
        Zero = "0";
    }

    // Guard that requires x > 10 AND x < 5 simultaneously
    guard recv_filter: x > 10 /\ x < 5;
}
```

### Diagnostic Output

```
warning[SYM01] (Protocol): guard 'recv_filter' is unsatisfiable (dead receive)
  = hint: remove the unreachable guard or relax its predicate
```

### Fix

```
// Relax the predicate so it accepts a non-empty domain:
guard recv_filter: x > 5 /\ x < 10;
```

## Rationale

- An unsatisfiable guard is analogous to dead code: it increases compilation cost and automaton state count without any runtime benefit.
- Mathematically, `is_satisfiable(phi)` returns false when there exists no element `d` in the domain `D` such that `evaluate(phi, d) = true`. The SFA emptiness check (`BFS reachability + SAT per transition`) confirms that no accepting run exists through the guard's symbolic transitions.
- In predicated type systems, unsatisfiable guards silently discard all incoming messages on the guarded channel, which can cause deadlocks or starvation in concurrent processes.

## Related Lints

- [SYM02](SYM02.md) -- Overlapping guards: fires when two guards accept overlapping domains (the opposite problem -- too much acceptance rather than none)
- [SYM03](SYM03.md) -- Subsumed guard: fires when one guard is a superset of another, which may indicate the subsumed guard is partially unsatisfiable
- [PT01](../parity-tree/PT01.md) -- PATA emptiness violation: the tree-level analogue of unsatisfiable guards
- [MSO01](../mso/MSO01.md) -- Unrestricted universal set: formula-level decidability issues that can produce unsatisfiable guards
