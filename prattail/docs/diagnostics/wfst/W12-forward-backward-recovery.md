# W12: forward-backward-recovery

**Severity:** Note
**Category:** WFST-Specific / Weight Training
**Feature Gate:** `wfst-log`

## Description

Detects categories with **high dispatch entropy**, indicating that the WFST
weight distribution across dispatch actions is nearly uniform.  High entropy
means the weights provide little discriminating power: the parser has no
strong preference among candidate rules, leading to suboptimal disambiguation.

The lint computes the **Shannon entropy** of the dispatch weight distribution:

```
  H = - sum_i  p_i * log2(p_i)

  where p_i = exp(-w_i) / sum_j exp(-w_j)
  and w_i is the tropical weight of action i
```

```
  Category "Proc" with 10 dispatch actions:
  ┌─────────────────────────────────────────────────────────┐
  │  Entropy: 3.21 bits (maximum for 10 actions = 3.32)     │
  │  Ratio: 3.21 / 3.32 = 96.7% of maximum                 │
  │                                                          │
  │  Near-uniform distribution:                              │
  │    Rule 1: weight 2.0  (prob 0.098)                     │
  │    Rule 2: weight 2.1  (prob 0.095)                     │
  │    Rule 3: weight 2.0  (prob 0.098)                     │
  │    ...                                                   │
  │    Rule 10: weight 2.2 (prob 0.092)                     │
  │                                                          │
  │  All probabilities approximately equal -> high entropy   │
  │  Weights provide little disambiguation value             │
  └─────────────────────────────────────────────────────────┘
```

When entropy exceeds **2.0 bits**, the weight distribution is too flat to
provide meaningful priority ordering.  **Weight training** from parse
examples (via `SpilloverTrainer` or `train_from_corrections()`) can learn
better weights that reflect actual usage patterns, reducing entropy and
improving disambiguation quality.

The lint's ID W12 and its grouped name "dispatch-entropy" reflect its dual
role: it detects the entropy condition and recommends training as the
resolution.

When multiple W12 diagnostics are emitted, the grouper consolidates them:

```
note[W12] (RhoCalc): 2 categories have high dispatch entropy: Proc(3.21 bits), Name(2.85 bits)
```

## Trigger Conditions

All of the following must hold:

- The `wfst-log` feature is enabled at compile time (W12 is gated behind
  `wfst-log` because entropy computation requires `LogWeight`).
- A category's prediction WFST has a computed entropy exceeding **2.0 bits**.

One diagnostic is emitted per high-entropy category.

## Example

### Grammar

```rust
// Feature: wfst-log enabled
language! {
    name: RhoCalc,
    types { ![String] as Proc, ![String] as Name },
    terms {
        PNew     . |- "new" Name "in" Proc  : Proc;
        PSend    . |- Name "!" "(" Proc ")" : Proc;
        PRecv    . |- Name "?" "(" Proc ")" : Proc;
        PPar     . |- Proc "|" Proc         : Proc;
        PNil     . |- "Nil"                 : Proc;
        // ... 5 more rules with similar weights
    },
}
```

### Output

```
note[W12] (RhoCalc): category `Proc` has high dispatch entropy (3.21 bits, 2.22 nats) across 10 actions — WFST weight training would likely improve disambiguation quality
  = hint: use `SpilloverTrainer` or `train_from_corrections()` to learn better weights from parse examples
```

## Resolution

1. **Train weights from examples.**  Use `SpilloverTrainer` with a corpus of
   representative input programs to learn weights that reflect actual dispatch
   frequencies.  Training adjusts weights so that commonly-used rules receive
   lower (better) weights, reducing entropy.

2. **Use `train_from_corrections()`.**  If a corpus is not available, provide
   individual correction examples where the parser chose the wrong rule.
   Each correction adjusts the relevant weights incrementally.

3. **Restructure for distinct prefixes.**  If rules share dispatch tokens
   because their leading terminals overlap, restructuring to give each rule a
   unique prefix eliminates the entropy problem at the source.

4. **Accept the note.**  If the grammar is inherently ambiguous at the
   single-token level and the NFA try-all fallback handles all cases
   correctly, high entropy is not a correctness issue.  It is a performance
   and disambiguation-quality signal.

## Hint Explanation

The hint **"use `SpilloverTrainer` or `train_from_corrections()` to learn
better weights from parse examples"** identifies the two training mechanisms:

- **`SpilloverTrainer`** takes a corpus of input texts, parses them, and
  records which rules are actually dispatched.  It then adjusts WFST weights
  to minimize entropy, making frequently-used rules cheaper (lower weight).

- **`train_from_corrections()`** is an incremental approach: when the parser
  makes a wrong dispatch choice, the correction is recorded and the relevant
  weights are adjusted.  This is useful when a full corpus is not available.

Both approaches use gradient-based weight adjustment over the `LogWeight`
semiring, which is why the `wfst-log` feature gate is required.

## Related Lints

- [W05](W05-composed-dispatch-ambiguity.md) -- Ambiguity resolution via
  tropical shortest path; high entropy means the weights used for this
  resolution may not reflect true priorities.
- [W10](W10-multi-token-lookahead.md) -- Multi-token lookahead can resolve
  ambiguity structurally even when weights are uninformative.
- [W06](W06-weight-inversion.md) -- Weight inversions can coexist with high
  entropy; training typically fixes both.
- [W14](W14-wpds-confirmed-ambiguity.md) -- WPDS-confirmed ambiguities
  represent deeper structural issues that training alone may not resolve.
