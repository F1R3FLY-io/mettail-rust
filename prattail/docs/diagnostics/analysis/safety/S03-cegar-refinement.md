# S03: cegar-refinement

**Severity:** Note
**Category:** analysis/safety
**Feature Gate:** always-on

## Description

Reports the outcome of the CEGAR (CounterExample-Guided Abstraction Refinement)
loop applied to the grammar's WPDS model. CEGAR is an iterative verification
technique that starts with a coarse abstraction of the parser's state space and
progressively refines it until either a genuine counterexample is confirmed or
the abstraction is precise enough to prove the property.

The core insight behind CEGAR is that direct model checking of the full WPDS
state space may be expensive or impractical for large grammars. Instead, the
analysis begins with a deliberately over-approximate model and checks whether
any apparent safety violation is *real* (a true counterexample) or *spurious*
(an artifact of the abstraction). If spurious, the abstraction is refined to
exclude the spurious path, and the check is repeated.

### Abstraction ladder

PraTTaIL's CEGAR implementation uses a semiring abstraction ladder, where each
level provides a more precise weight domain:

```
  Abstraction Ladder (coarse --> precise)
  ════════════════════════════════════════

  Level 0: BooleanWeight
  ┌─────────────────────────────────────────────────────┐
  │  Domain: {true, false}                              │
  │  Question: "Is a bad state reachable at all?"       │
  │  Precision: lowest -- ignores path costs entirely   │
  │  Cost: O(|Delta| * |Q|^2)                           │
  └───────────────────────────┬─────────────────────────┘
                              │ spurious?
                              │ refine
                              v
  Level 1: CountingWeight
  ┌─────────────────────────────────────────────────────┐
  │  Domain: N union {+infinity}                        │
  │  Question: "How many distinct paths reach bad?"     │
  │  Precision: medium -- counts paths, ignores costs   │
  │  Cost: O(|Delta| * |Q|^2 * max_count)               │
  └───────────────────────────┬─────────────────────────┘
                              │ spurious?
                              │ refine
                              v
  Level 2: TropicalWeight
  ┌─────────────────────────────────────────────────────┐
  │  Domain: R+ union {+infinity}                       │
  │  Question: "What is the minimum cost to reach bad?" │
  │  Precision: highest -- tracks exact path costs      │
  │  Cost: O(|Delta| * |Q|^2 * log|Q|)                  │
  └─────────────────────────────────────────────────────┘

  Legend:
    |Delta|  = number of WPDS transition rules
    |Q|      = number of P-automaton states
    spurious = counterexample does not correspond to a concrete path
    refine   = move to a more precise semiring domain
```

At each level, the CEGAR loop:

1. Runs prestar with the current semiring.
2. If the initial configuration has zero weight, the property is verified --
   stop and report "safe".
3. If non-zero, extract a candidate counterexample (witness trace).
4. Simulate the witness trace on the concrete WPDS model.
5. If the trace is feasible, the property is violated -- stop and report
   "unsafe".
6. If the trace is spurious (infeasible on the concrete model), refine the
   abstraction by moving to the next level and repeat from step 1.

The diagnostic reports the number of refinement steps taken and the final
verdict.

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The pipeline's CEGAR module (`cegar.rs`) has been executed, producing a
   `CegarLog`.
2. The log contains at least one `RefinementStep`.

The lint is silent when:
- No `CegarLog` is available (CEGAR was not run).

The message includes:
- The number of refinement steps (levels traversed in the abstraction ladder).
- The final verdict from the last step's `verdict` field (e.g., `"safe"`,
  `"unsafe"`, or `"unknown"`).

## Example

### Grammar

```
language! {
    name: ProcessLang;
    primary: Proc;

    category Proc {
        Send  = "send" "!" "(" Expr ")";
        Recv  = "recv" "?" "(" Name ")";
        Par   = Proc "|" Proc;
        Seq   = Proc ";" Proc;
        Zero  = "0";
    }

    category Expr {
        native_type: Integer;
        IntLit = <int>;
        Add    = Expr "+" Expr;
    }

    category Name {
        Ident = <ident>;
    }
}
```

Suppose the CEGAR loop runs two refinement steps:
- Level 0 (BooleanWeight): reports a candidate counterexample.
- Level 1 (CountingWeight): confirms the counterexample is spurious.
- Level 2 (TropicalWeight): proves safety.

### Output

```
note[S03] (ProcessLang): CEGAR loop: 3 refinement step(s), final verdict: safe
```

Or, if the counterexample is confirmed at Level 1:

```
note[S03] (ProcessLang): CEGAR loop: 2 refinement step(s), final verdict: unsafe
```

## Resolution

S03 is informational. No action is required unless the final verdict is
`"unsafe"`, in which case:

1. Inspect the CEGAR log for the refinement steps that led to the verdict.
   Each step records the semiring used, the verdict at that level, and whether
   the counterexample was spurious.

2. If the verdict is `"unsafe"`, a genuine safety violation exists. See
   [S01](S01-safety-violation.md) for resolution strategies.

3. If the verdict is `"safe"` after multiple refinement steps, the grammar's
   safety was not obvious at the coarsest abstraction level but was confirmed
   at a finer level. This is expected for grammars with complex cross-category
   call structures.

4. If the verdict is `"unknown"`, the CEGAR loop exhausted its abstraction
   ladder without reaching a conclusive verdict. This may indicate that the
   grammar's state space requires a richer semiring domain than the ladder
   provides.

## Hint Explanation

S03 does not include a hint, as it is purely informational. The refinement
step count and final verdict provide sufficient context for interpreting the
analysis outcome.

## Related Lints

- [S01](S01-safety-violation.md) -- Fires when prestar (with or without CEGAR) finds a reachable bad state
- [S02](S02-safety-verified.md) -- Fires when prestar proves no bad states are reachable
- [S06](S06-algebraic-summary.md) -- Tarjan path expression summary; the SCC structure influences CEGAR refinement depth
