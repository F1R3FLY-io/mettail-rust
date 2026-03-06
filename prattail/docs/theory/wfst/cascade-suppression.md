# Cascade Suppression Theory

**Date:** 2026-03-01

Formalizes error cascade prevention in PraTTaIL's WFST recovery subsystem
using an absorbing-state model. A single syntactic error (e.g. a missing
closing bracket) can cause the parser to report errors at every subsequent
token position. The cascade window mechanism suppresses these phantom errors
by temporarily entering an absorbing state after each genuine error.

---

## Table of Contents

1. [The Cascade Problem](#1-the-cascade-problem)
2. [Cascade Window as Temporal Guard](#2-cascade-window-as-temporal-guard)
3. [Absorbing-State Model](#3-absorbing-state-model)
4. [Properties](#4-properties)
5. [Parameter Selection](#5-parameter-selection)
6. [Source Reference](#6-source-reference)
7. [References](#7-references)

---

## 1. The Cascade Problem

### 1.1 Phenomenon

When a parser encounters a syntax error (e.g. a missing `)`, an extra
operator, or a misplaced keyword), it applies a recovery strategy and
continues parsing. But if the recovery places the parser in a state that
is only slightly correct, subsequent tokens are likely to trigger further
errors — even though the programmer made only a single mistake. Each
secondary error is a *phantom error*: it is a symptom of the original
mistake, not an independent problem.

### 1.2 Example

Consider the input `(1 + 2 * 3` parsed by a calculator grammar that
expects balanced parentheses:

```
Tokens:  LParen  Integer(1)  Plus  Integer(2)  Star  Integer(3)  Eof
         pos=0   pos=1       pos=2 pos=3       pos=4 pos=5       pos=6
```

The programmer forgot the closing `)`. Without cascade suppression:

1. **Error at pos=6 (Eof):** Expected `)`, found Eof. Recovery inserts a
   phantom `)` and continues.
2. If the recovery does not perfectly restore state, the parser may
   re-enter at an unexpected position and report another error at the
   very next token.
3. In pathological cases, a single missing delimiter can produce *N*
   errors for an *N*-token input.

The user sees a wall of errors when only one fix is needed. This degrades
the developer experience and obscures the root cause.

### 1.3 Classical Solution: Panic Mode

Traditional panic-mode recovery skips tokens until a "strong" sync point
(typically a statement terminator like `;` or a closing delimiter). This
suppresses errors within the skip window, but:

- Errors *before* the skip (between the error and the next sync point)
  may still cascade.
- If the skip window is short, phantom errors after the sync point can
  still occur.
- The suppression is implicit and unreliable — it depends on the
  distribution of sync points in the input.

PraTTaIL replaces this implicit suppression with an explicit *cascade
window* mechanism.

---

## 2. Cascade Window as Temporal Guard

### 2.1 Definition

The **cascade window** is a non-negative integer *k* (default: 3) that
defines a temporal guard around each reported error. After an error at
token position *p*, any error at position *p'* with *p' ≤ p + k* is
suppressed: the parser advances by one token without invoking recovery
and without reporting a diagnostic.

### 2.2 Invariant

Let *E* = position of the most recent genuine error (initially ∞).

```
Error at position p:
  if p ≤ E + k:
    suppress (do not report, do not recover, advance by 1)
  else:
    report error, invoke recovery, set E = p
```

### 2.3 Suppressed Positions

When an error is suppressed:

- The parser position advances by 1 (`*pos += 1`).
- No recovery strategy is evaluated.
- No `ParseError` is pushed to the error vector.
- The `LAST_ERROR_POS` thread-local is *not* updated (the window
  continues to be measured from the original error).

This ensures that a burst of phantom errors is silently absorbed, while
genuinely independent errors (separated by more than *k* tokens) are all
reported.

---

## 3. Absorbing-State Model

The cascade suppression mechanism can be formalized as a two-state finite
process over token positions.

### 3.1 Parser as Finite-State Process

At each token position, the parser is in one of two states:

- **Normal**: standard parsing and recovery behavior.
- **Absorbing(n)**: error suppression is active with *n* tokens remaining
  in the window.

### 3.2 State Set

```
Q = { Normal, Absorbing(n) }   where  n ∈ {0, 1, ..., k}
```

### 3.3 Transitions

```
─────────────────────────────────────────────────────────────────────
  Current State          Event             Next State       Action
─────────────────────────────────────────────────────────────────────
  Normal                 parse succeeds    Normal           ── (none)
  Normal                 parse error       Absorbing(k)     report, recover
  Absorbing(n), n > 0   parse succeeds    Absorbing(n−1)   ── (none)
  Absorbing(n), n > 0   parse error       Absorbing(n−1)   suppress, pos += 1
  Absorbing(0)           parse succeeds    Normal           ── (none)
  Absorbing(0)           parse error       Absorbing(k)     report, recover
─────────────────────────────────────────────────────────────────────
```

On a successful parse, the countdown decrements (or transitions to Normal
if already at 0). On an error, the behavior depends on the countdown:

- **n > 0**: the error is within the cascade window — suppress it.
- **n = 0**: the window has expired — this is a new genuine error.

### 3.4 State Diagram

```
                  parse ok
            ┌────────────────┐
            │                │
            ▼                │
     ┌──────────┐     ┌─────┴──────────┐
     │  Normal  │     │  Absorbing(n)  │
     └────┬─────┘     └────┬───────────┘
          │                │
   error  │                │  error, n > 0
          │                │  (suppress, advance)
          ▼                ▼
     ┌────────────────────────┐
     │  report + recover      │
     │  set Absorbing(k)      │
     └────────────────────────┘
          │
          │  n = 0, error
          │  (window expired → new error)
          └──────────────────┘
```

### 3.5 Implementation

PraTTaIL implements the absorbing-state model via a per-category
thread-local `Cell<usize>`:

```rust
thread_local! {
    static LAST_ERROR_POS_Cat: Cell<usize> = Cell::new(usize::MAX);
}
```

The transition logic in `parse_Cat_recovering`:

```rust
let last_err = LAST_ERROR_POS_Cat.with(|c| c.get());
if last_err != usize::MAX && *pos <= last_err + CASCADE_WINDOW {
    // Absorbing state: suppress, advance by 1
    if *pos < tokens.len() { *pos += 1; }
    return None;
}
// Normal state or window expired: report and recover
LAST_ERROR_POS_Cat.with(|c| c.set(*pos));
```

The initial value `usize::MAX` acts as a sentinel for "no previous error"
(i.e. the Normal state). The condition `*pos ≤ last_err + k` implements
the Absorbing(n > 0) check. Resetting to `usize::MAX` on `min_bp == 0`
ensures the window is cleared at each top-level parse invocation.

---

## 4. Properties

### 4.1 Error Count Bound

**Theorem.** For an input of *n* tokens with cascade window *k*, the
number of reported errors is at most ⌈n/(k + 1)⌉.

**Proof.** Each reported error at position *p* suppresses all errors in
[*p* + 1, *p* + *k*]. The next reportable position is at earliest
*p* + *k* + 1. Therefore, reported error positions form a sequence with
minimum spacing *k* + 1. At most ⌈n/(k + 1)⌉ such positions fit in a
range of *n* tokens.  ∎

### 4.2 No False Suppression

**Theorem.** If two syntax errors are separated by more than *k* tokens,
both are reported.

**Proof.** Let the first error be at position *p₁* and the second at
*p₂* with *p₂ > p₁ + k*. After reporting *p₁*, the absorbing state
suppresses positions in [*p₁* + 1, *p₁* + *k*]. Since *p₂ > p₁ + k*,
position *p₂* is outside the suppression window. The check
`*pos ≤ last_err + k` evaluates to false, so the error at *p₂* is
reported.  ∎

### 4.3 Monotonicity

**Theorem.** Increasing *k* monotonically reduces (or preserves) the
number of reported errors.

**Proof.** Let *E(k)* = set of reported error positions with window *k*,
and *E(k + 1)* = set with window *k + 1*. For any error position *p* ∈
*E(k + 1)*, the preceding reported error *p'* satisfies *p > p' + k + 1*,
which implies *p > p' + k*, so *p* ∈ *E(k)*. Therefore *E(k + 1) ⊆ E(k)*,
giving |*E(k + 1)*| ≤ |*E(k)*|.  ∎

### 4.4 Thread-Local Tracking

Each category maintains its own `LAST_ERROR_POS_Cat` thread-local. This
ensures that:

- Cross-category parses do not interfere (an error in `Bool` does not
  suppress errors in `Int`).
- Multi-threaded parsers are safe (each thread has its own Cell).
- The initial sentinel value `usize::MAX` prevents false suppression on
  the first error (no position satisfies `pos ≤ usize::MAX + k` due to
  overflow wrapping).

---

## 5. Parameter Selection

### 5.1 Default: k = 3

The default cascade window is 3 tokens. Empirically, most phantom errors
caused by a single missing or extra token occur within 1-2 tokens of the
original error. A window of 3 provides a safety margin while keeping the
error reporting responsive.

### 5.2 Configuration

The cascade window is configurable via `RecoveryConfig.cascade_window`:

```rust
RecoveryConfig {
    cascade_window: 3,  // default
    ..Default::default()
}
```

See [RecoveryConfig](../../design/wfst/recovery-config.md) for the full
parameter reference.

### 5.3 Trade-Off Curve

```
  Errors reported
  │
  │ ●                              k = 0 (no suppression)
  │
  │   ●                            k = 1
  │
  │     ●                          k = 2
  │       ●───────────●            k = 3 (default) ← diminishing returns
  │                     ●          k = 5
  │                       ●────●   k = 10+
  │
  └──────────────────────────────── k (cascade window)
```

For most grammars, the curve flattens around *k* = 3. Increasing *k*
beyond 3 suppresses genuinely independent errors more often than it
suppresses phantoms. The default balances precision (report independent
errors) with noise reduction (suppress phantoms).

**Bracket-heavy grammars** (e.g. Lisp, Rholang) may benefit from *k* = 4
or 5, since a single mismatched bracket can produce a longer trail of
phantoms.

**Expression-dense grammars** (e.g. calculator, APL) may benefit from
*k* = 2, since operators appear at high density and errors are typically
independent.

---

## 6. Source Reference

| Symbol                 | Location                             |
|------------------------|--------------------------------------|
| `RecoveryConfig`       | `prattail/src/recovery.rs:109`       |
| `cascade_window` field | `prattail/src/recovery.rs:165`       |
| `LAST_ERROR_POS_Cat`   | `prattail/src/pipeline.rs:2101`      |
| Cascade check logic    | `prattail/src/pipeline.rs:2117–2123` |
| Reset on `min_bp == 0` | `prattail/src/pipeline.rs:2112`      |

---

## 7. References

- [RecoveryConfig](../../design/wfst/recovery-config.md) — full
  parameter specification
- [Extended Recovery Strategies](../../design/wfst/extended-recovery-strategies.md)
  — strategy evaluation order
- [Recovery State Propagation](../../architecture/wfst/recovery-state-propagation.md)
  — thread-local state infrastructure
- [Error Recovery (base)](../../design/wfst/error-recovery.md) — 4
  original repair actions, 3-tier cost model

---

*Cross-reference:* The cascade window interacts with the beam width in
`viterbi_multi_step()`: a wider beam may find repairs beyond the cascade
window, leading to genuinely better fixes that bypass suppression. See
[Multi-Step Viterbi Recovery](multi-step-viterbi-recovery.md) §4.3 for
beam pruning mechanics.
