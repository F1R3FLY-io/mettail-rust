# MSO03: equivalent-formulas

**Severity:** Note
**Module:** M10 Weighted MSO Logic
**Feature gate:** `weighted-mso`

## What It Detects

- An MSO formula is internally inconsistent: it is marked as a sentence (no free variables) but its `free_vars` set is non-empty.
- This indicates a construction error in the formula builder: a variable was not properly bound by a quantifier, yet the formula was classified as closed. The inconsistency may cause incorrect results in equivalence checking and automaton compilation.

## Example

### Triggering Code

```
language! {
    name: FormCheck;
    primary: Prop;

    category Prop {
        And  = Prop "/\\" Prop;
        Or   = Prop "\\/" Prop;
        Atom = <ident>;
    }

    // Formula marked as sentence but contains unbound variable 'y':
    predicate check:
        exists x. P_a(x) /\ P_b(y);
    // 'y' is free, but the formula is somehow classified as a sentence
}
```

### Diagnostic Output

```
note[MSO03] (FormCheck): MSO formula is marked as sentence but has free variables -- internal inconsistency
  = hint: check formula construction for variable binding errors
```

### Fix

```
// Bind all free variables with quantifiers to make it a true sentence:
predicate check:
    exists x. exists y. P_a(x) /\ P_b(y);

// Or use close_existentially() to automatically bind free variables:
// close_existentially(phi) produces exists x1 ... exists xn . phi
```

## Rationale

- A sentence is a formula with no free variables: `Free(phi) = emptyset`. The `is_sentence()` check verifies `free_variables(phi).is_empty()`. When `result.is_sentence` is true but `result.free_vars` is non-empty, the formula's metadata contradicts its structure.
- The equivalence checking operation `check_equivalence(phi, psi)` is decidable for locally finite semirings only when both formulas are sentences (Corollary 6.5). Passing a non-sentence disguised as a sentence could produce incorrect equivalence results.
- The `to_weighted_automaton()` compilation (constructive Theorem 5.5) requires knowing which variables are free vs. bound. Free variables must be tracked as part of the automaton's alphabet extension (extended word positions). An inconsistency here leads to incorrect automaton construction.
- This diagnostic is rare in practice -- it typically indicates a bug in the formula construction pipeline rather than a user error. The `free_variables()` function should be called to verify classification before downstream use.

## Related Lints

- [MSO01](MSO01.md) -- Unrestricted universal set: related formula classification issues
- [MSO02](MSO02.md) -- Non-recognizable step: another formula-level decidability concern
- [K02](../analysis/kat/K02-kat-equivalence.md) -- KAT equivalence: related semantic equivalence checking at the KAT level
- [SYM03](../symbolic/SYM03.md) -- Subsumed guard: guard-level semantic redundancy detection
