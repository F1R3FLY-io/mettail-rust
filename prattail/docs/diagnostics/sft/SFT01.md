# SFT01: empty-sft-domain

**Severity:** Warning
**Module:** Symbolic Finite Transducers
**Feature gate:** `sft`

## What It Detects

An SFT has an empty domain -- the domain SFA extracted from the SFT accepts no
inputs, meaning the transduction can never fire. This is analogous to a dead
rule: the SFT consumes compile-time resources constructing transition tables and
output functions for a transformation that is unreachable at runtime.

Detection works by extracting the domain SFA from the SFT (projecting away the
output component of each transition) and checking the resulting automaton for
emptiness via BFS reachability from the initial state to any accepting state. If
no accepting state is reachable, the SFT's domain is empty and it is flagged as
dead.

## Example

### Triggering Code

```
language! {
    name: Normalizer;
    primary: Proc;

    category Proc {
        Send  = Chan "!" "(" Expr ")";
        Recv  = "for" "(" Pattern "<-" Chan ")" "{" Proc "}";
        Par   = Proc "|" Proc;
        Zero  = "0";
    }

    category Expr {
        Num = /[0-9]+/;
        Var = /[a-z][a-zA-Z0-9_]*/;
    }

    // Transducer guard requires x > 100 AND x < 50 simultaneously --
    // no integer can satisfy both constraints, so the domain SFA is empty.
    sft flatten_guard {
        input:  Recv where guard(x > 100 /\ x < 50);
        output: Zero;
    }
}
```

The SFT `flatten_guard` has input guard `x > 100 /\ x < 50`, which is
unsatisfiable. The domain SFA constructed from the input specification
accepts no strings, so the transduction can never fire.

### Diagnostic Output

```
warning[SFT01] (Normalizer): SFT 'flatten_guard' has empty domain (dead transduction)
  = hint: remove the unreachable SFT or relax its input guard
```

### Fix

```
// Option 1: Relax the guard so the domain is non-empty.
sft flatten_guard {
    input:  Recv where guard(x > 50 /\ x < 100);
    output: Zero;
}

// Option 2: Remove the dead SFT entirely.
```

## Rationale

- A dead SFT wastes compile-time resources: the pipeline constructs transition
  tables, output functions, and domain/range SFAs for a transduction that can
  never contribute to runtime behavior. Removing it reduces compilation cost
  and generated code size.
- An empty domain often hides a logic error in the input specification. The
  grammar author likely intended the SFT to match some input class but
  accidentally wrote contradictory constraints or an impossible structural
  pattern.
- Generated code paths for dead SFTs are unreachable, which inflates binary
  size and complicates coverage analysis. Eliminating them produces cleaner
  codegen output and more accurate coverage metrics.

## Related Lints

- [SFT02](SFT02.md) -- Constant SFT output: the SFT fires but always produces the same result
- [SFT03](SFT03.md) -- Nondeterministic SFT: the SFT can produce multiple outputs for a single input
- [SFT04](SFT04.md) -- Equivalent SFT pair: two SFTs compute the same function and one is redundant
- [SYM01](../symbolic/SYM01.md) -- Unsatisfiable guard: the SFA-level analogue for general predicates
- [W01](../wfst/W01-dead-rule.md) -- Dead rule: the WFST-level analogue for unreachable parse rules
