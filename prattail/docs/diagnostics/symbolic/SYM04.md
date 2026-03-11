# SYM04: non-minimal-guards

**Severity:** Note
**Module:** M1 Symbolic Automata
**Feature gate:** `symbolic-automata`

## What It Detects

- The Symbolic Finite Automaton (SFA) constructed from the grammar's guard predicates has more than 10 states and contains subsumed guards, indicating that the SFA is non-minimal.
- A non-minimal SFA has mergeable states that accept equivalent predicate sets. Minimization would reduce the state count, improving both analysis time and runtime dispatch performance.

## Example

### Triggering Code

```
language! {
    name: Classifier;
    primary: Proc;

    category Proc {
        ClassA = "for" "(" "@x" ":" "x in [0,10)"   "<-" ch ")" "{" A "}";
        ClassB = "for" "(" "@x" ":" "x in [5,15)"   "<-" ch ")" "{" B "}";
        ClassC = "for" "(" "@x" ":" "x in [10,20)"  "<-" ch ")" "{" C "}";
        ClassD = "for" "(" "@x" ":" "x in [0,20)"   "<-" ch ")" "{" D "}";  // subsumes A, B, C
        // ... more guards producing > 10 SFA states
    }
}
```

### Diagnostic Output

```
note[SYM04] (Classifier): SFA has 14 states with 3 subsumed guards; minimization would reduce state count
  = hint: run SFA minimization to merge equivalent guard states
```

### Fix

```
// Remove redundant guards that are subsumed by broader ones,
// or reorganize guards into disjoint partitions:
ClassLow  = "for" "(" "@x" ":" "x in [0,10)"  "<-" ch ")" "{" Low  "}";
ClassMid  = "for" "(" "@x" ":" "x in [10,15)" "<-" ch ")" "{" Mid  "}";
ClassHigh = "for" "(" "@x" ":" "x in [15,20)" "<-" ch ")" "{" High "}";
```

## Rationale

- The lint fires when `result.num_states > 10 && !result.subsumed_guards.is_empty()`. The threshold of 10 avoids noise on small grammars where the overhead of non-minimality is negligible.
- SFA minimization uses symbolic Hopcroft partition refinement in O(n^2 x |minterms|), which can significantly reduce state count for predicate-heavy grammars.
- Each SFA state corresponds to a distinct predicate equivalence class. Merging equivalent states reduces the number of runtime guard evaluations during dispatch.
- Non-minimal SFAs also slow down compile-time analyses that operate over the SFA (intersection, complement, equivalence checking).

## Related Lints

- [SYM01](SYM01.md) -- Unsatisfiable guard: minimization may reveal guards that are equivalent to BOT
- [SYM02](SYM02.md) -- Overlapping guards: often the root cause of non-minimality
- [SYM03](SYM03.md) -- Subsumed guard: the presence of subsumed guards is a prerequisite for this lint to fire
- [PR03](../probabilistic/PR03.md) -- High entropy category: non-minimal guard structures inflate the entropy calculation
