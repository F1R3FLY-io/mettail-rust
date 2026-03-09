# I01: transducer-cascade

**Severity:** Info
**Category:** infrastructure
**Feature Gate:** None (always enabled; cascade gated by WFST state count > 4)

## Description

Reports the summary of the E1 optimization transducer cascade that runs over
the grammar's prediction WFSTs during pipeline construction. The cascade
applies a sequence of optimization passes (dead-state elimination, weight
normalization, epsilon removal, state minimization) to each per-category WFST,
converging when no pass produces further changes.

The transducer cascade is the primary mechanism for reducing WFST complexity
before the WFSTs are consumed by downstream analyses (lint layer, decision tree
construction, dispatch code generation). Each pass is a finite-state transducer
that rewrites the WFST in place, and the cascade iterates all passes to a
fixed point.

```
  Transducer cascade pipeline:

  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
  │ Dead-state   │ -> │ Weight       │ -> │ Epsilon      │
  │ elimination  │    │ normalization│    │ removal      │
  └──────────────┘    └──────────────┘    └──────────────┘
         │                                       │
         │         ┌──────────────┐              │
         └─────────│ State        │<─────────────┘
                   │ minimization │
                   └──────────────┘
                         │
                    converged?
                    ├── no  -> repeat from dead-state elimination
                    └── yes -> emit I01 summary
```

The I01 diagnostic is purely informational -- it reports the number of changes
made and the number of categories affected. No user action is required.

## Trigger Conditions

All of the following must hold:

- The grammar has at least one prediction WFST (non-trivial grammar).
- The total WFST state count across all categories exceeds 4 (below this
  threshold, the cascade is skipped and I02 is emitted instead).
- The cascade produces at least one change across all passes.

One diagnostic is emitted per grammar (summarizing all categories).

## Example

### Grammar

```rust
language! {
    name: Ambient,
    types {
        Proc,
        Name,
        Expr
    },
    terms {
        // ... rules for three categories ...
    },
}
```

### Output

```
info[I01] (Ambient): transducer cascade: 8 change(s) across 3 categories (12 total iterations)
```

## Resolution

No action required. I01 is an informational diagnostic reporting pipeline
progress. The transducer cascade runs automatically and its results are
consumed by downstream analysis passes.

If the cascade reports an unexpectedly high number of changes or iterations,
this may indicate:

1. **Redundant WFST structure.** The grammar's prediction WFSTs have
   significant dead states or epsilon transitions, suggesting that the
   initial WFST construction could be improved.

2. **Non-converging optimization.** An unusually high iteration count may
   indicate that the passes are oscillating (one pass's changes trigger
   another pass's changes in a cycle). This is rare and should be reported
   as a bug.

## Hint Explanation

I01 does not emit a hint. The diagnostic message itself is the complete
summary of the cascade's work.

## Related Lints

- [I02](I02-cascade-skipped.md) -- Cascade skipped. Emitted when the total
  WFST state count is too small to justify the cascade overhead.
- [I04](I04-beam-feature-required.md) -- Beam feature required. The beam
  width configuration may affect which cascade passes are invoked.
- [W01](../wfst/W01-dead-rule.md) -- Dead rule. Dead-state elimination in
  the cascade may remove states that correspond to dead rules, contributing
  to W01 diagnostics.
