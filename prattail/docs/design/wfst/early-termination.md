# Early Termination on Deterministic Hit (F2)

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem](#1-problem)
2. [Mechanism](#2-mechanism)
3. [Why `needs_nfa_spillover` Disables F2](#3-why-needs_nfa_spillover-disables-f2)
4. [Correctness Proof](#4-correctness-proof)
5. [Generated Code](#5-generated-code)
6. [Weight Scale Reference](#6-weight-scale-reference)
7. [Source References](#7-source-references)

---

## 1. Problem

When multiple grammar rules share the same dispatch token, the NFA
try-all loop evaluates every inlineable alternative, saves each
successful parse result into `nfa_results`, and then selects the best
one by WFST weight order.  This is correct but wasteful in a common
case: the first alternative (after weight ordering) has tropical weight
0.0 -- meaning it is deterministic and unambiguous -- and it succeeds.

Because weight 0.0 is the multiplicative identity of the tropical
semiring, no other alternative can produce a lower weight.  Trying the
remaining alternatives is pure overhead: they cannot displace the
already-successful first result.

Consider a category `Proc` where `Token::LParen` dispatches both a
`Grouping` rule (weight 0.0, delimiter-driven) and a `Cast` rule
(weight 0.5, needs backtracking).  In the unoptimised loop the parser:

1. Saves position, tries `Grouping` -- succeeds, pushes into `nfa_results`.
2. Restores position, tries `Cast` -- may succeed or fail.
3. Picks `nfa_results[0]` as the best (it is already weight-ordered).

Step 2 cannot change the outcome.  F2 eliminates it.

---

## 2. Mechanism

F2 is a **compile-time** decision.  During trampoline codegen, the
NFA merged-prefix emitter inspects the weight-ordered alternative list
and decides whether to emit an early-exit guard around the remaining
alternatives.  Three conditions must all hold:

| # | Condition | Rationale |
|---|-----------|-----------|
| 1 | First alternative has weight exactly 0.0 | Only weight-0.0 is provably optimal (see Section 4) |
| 2 | More than one alternative exists | A single alternative has nothing to skip |
| 3 | `needs_nfa_spillover == false` | Spillover requires all alternatives (see Section 3) |

When all three hold, the code generator wraps every alternative after
the first in an `if nfa_results.is_empty() { ... }` guard.  At
runtime, if the first alternative pushed a result into `nfa_results`,
the guard evaluates to `false` and the remaining alternatives are
skipped entirely.

The decision logic in the code generator:

```rust
let first_is_deterministic = ordered_inlineable.len() > 1
    && !config.needs_nfa_spillover
    && ordered_inlineable
        .first()
        .map_or(false, |(_, w)| *w == 0.0);
```

This variable is computed once and drives two code-emission points:

1. **Guard open** -- after the first alternative's match arm, before the
   second alternative:

   ```rust
   if idx == 0 && first_is_deterministic {
       buf.push_str("if nfa_results.is_empty() {");
   }
   ```

2. **Guard close** -- after the loop over all alternatives:

   ```rust
   if first_is_deterministic {
       buf.push_str("} /* F2: deterministic hit ... */");
   }
   ```

The following diagram shows the control flow at runtime:

```
┌─────────────────────────────────────────────────────┐
│ Token::LParen =>                                    │
│   let nfa_saved = *pos;                             │
│   let mut nfa_results = Vec::new();                 │
│   let mut nfa_positions = Vec::new();               │
│   let mut nfa_weights = Vec::new();                 │
│                                                     │
│   // Alt 0: Grouping (w=0.0)                        │
│   *pos = nfa_saved;                                 │
│   match try_grouping(tokens, pos) {                 │
│       Ok(v) => { nfa_results.push(v); ... }         │
│       Err(e) => { ... }                             │
│   }                                                 │
│                                                     │
│   if nfa_results.is_empty() {  ◄── F2 guard         │
│       // Alt 1: Cast (w=0.5)                        │
│       *pos = nfa_saved;                             │
│       match try_cast(tokens, pos) {                 │
│           Ok(v) => { nfa_results.push(v); ... }     │
│           Err(e) => { ... }                         │
│       }                                             │
│       // Alt 2..N likewise                          │
│   } /* F2 */                                        │
│                                                     │
│   match nfa_results.len() {                         │
│       0 => { return Err(...); }                     │
│       _ => { *pos = nfa_positions[0]; ... }         │
│   }                                                 │
└─────────────────────────────────────────────────────┘
```

---

## 3. Why `needs_nfa_spillover` Disables F2

NFA spillover is the mechanism by which the NFA try-all loop feeds
alternative parse results into `NFA_PREFIX_SPILL_<CAT>` for later
forced-prefix replay by `from_alternatives`.  This is needed when the
grammar has semantic ambiguity that cannot be resolved syntactically --
the parser must collect *all* successful alternatives so that
downstream semantic analysis (e.g., type checking, variable binding,
groundness analysis) can select the correct one.

F2 would prevent this collection.  A concrete example:

```
rule Float::FloatId { Ident }    // weight 0.0, Direct
rule Float::IntToFloat { Int }   // weight 0.5, Cast
```

Suppose `Token::Ident` dispatches both `FloatId` and a cross-category
cast that converts `Proc::PVar` to `Float` through `float(x)`.
The `FloatId` rule succeeds with weight 0.0 -- it matches any
identifier as a float variable.  But the parse tree it produces may
contain a free variable `x` that is not ground.  The cast alternative,
though heavier, may produce a ground result via the cross-category
interpretation.  `from_alternatives` needs both alternatives to compare
groundness and select the semantically correct one.

If F2 skipped the cast alternative, `from_alternatives` would only
see the `FloatId` result and blindly accept the non-ground parse,
producing a semantic error downstream.

The invariant:

> When `needs_nfa_spillover == true`, the NFA loop must try all
> alternatives regardless of the first alternative's weight.

This is enforced by the conjunction in the `first_is_deterministic`
condition: `!config.needs_nfa_spillover` is a required predicate.

---

## 4. Correctness Proof

**Theorem.**  When the first alternative (in WFST weight order) has
tropical weight 0.0, succeeds, and `needs_nfa_spillover` is false,
skipping all remaining alternatives preserves parse correctness.

**Definitions.**

Let (R^+ ∪ {+∞}, ⊕, ⊗, +∞, 0.0) be the tropical semiring, where:

- ⊕ = min  (selects best alternative)
- ⊗ = +    (accumulates path costs)
- zero = +∞  (additive identity; unreachable)
- one = 0.0  (multiplicative identity; zero cost)

Let w(aᵢ) denote the tropical weight assigned to alternative aᵢ by
`compute_action_weight()`.

**Lemma 1 (Non-negativity).**  For all alternatives aᵢ,
w(aᵢ) ≥ 0.0.

*Proof.*  By inspection of `compute_action_weight()`:

| DispatchAction      | Weight   |
|---------------------|----------|
| Direct              | 0.0      |
| Grouping            | 0.0      |
| CrossCategory (det) | 0.0      |
| CrossCategory (bt)  | 0.5      |
| Cast                | 0.5      |
| Lookahead           | 1.0 + n  |
| Variable            | 2.0      |

Every assigned weight is in R^+ (non-negative reals).  ∎

**Lemma 2 (Weight ordering).**  The alternative list is sorted by
weight: w(a₀) ≤ w(a₁) ≤ ... ≤ w(aₙ₋₁).

*Proof.*  `nfa_alternative_order()` sorts the indexed list by
`TropicalWeight::cmp`, which delegates to `f64::total_cmp`.
Since all weights are non-negative finite reals (Lemma 1),
`total_cmp` provides a total order consistent with ≤.  ∎

**Lemma 3 (Optimality of weight 0.0).**  If w(a₀) = 0.0 and
a₀ succeeds, then a₀ is the optimal parse result under ⊕ = min.

*Proof.*

1. By Lemma 1, w(aᵢ) ≥ 0.0 for all i.
2. By Lemma 2, w(a₀) ≤ w(aᵢ) for all i ≥ 1.
3. Since w(a₀) = 0.0 = one (the multiplicative identity), and
   w(aᵢ) ≥ 0.0 for all i, we have:
   ⊕{w(aᵢ) | aᵢ succeeds} = min{w(aᵢ) | aᵢ succeeds} = w(a₀) = 0.0.
4. Therefore a₀ is an optimal alternative.  ∎

**Lemma 4 (Spillover independence).**  When `needs_nfa_spillover` is
false, the result selection depends only on `nfa_results[0]`.

*Proof.*  When spillover is disabled, the result-selection arm is:

```rust
_ => {
    *pos = nfa_positions[0];
    RUNNING_WEIGHT_CAT.with(|cell| cell.set(cell.get() + nfa_weights[0]));
    break 'prefix nfa_results.into_iter().next()
        .expect("nfa_results non-empty");
}
```

Only `nfa_results[0]`, `nfa_positions[0]`, and `nfa_weights[0]` are
read.  Elements at indices ≥ 1 are discarded.  No spillover buffer is
populated.  ∎

**Proof of Theorem.**

1. By the F2 preconditions: w(a₀) = 0.0, a₀ succeeds (since the
   guard `nfa_results.is_empty()` evaluates to false), and
   `needs_nfa_spillover` is false.
2. By Lemma 3, a₀ is the optimal alternative.
3. By Lemma 4, only `nfa_results[0]` is consumed by result selection.
4. F2 prevents alternatives a₁ ... aₙ₋₁ from executing, so
   `nfa_results` contains exactly one element: a₀'s result.
5. `nfa_results[0]` is the same value that would be selected by the
   unoptimised loop (where all alternatives are tried but only
   index 0 is consumed).
6. Therefore F2 preserves parse correctness.  ∎

---

## 5. Generated Code

### 5.1. Before F2 (all alternatives unconditionally tried)

```rust
Token::LParen => {
    let nfa_saved = *pos;
    let mut nfa_results: Vec<Proc> = Vec::new();
    let mut nfa_positions: Vec<usize> = Vec::new();
    let mut nfa_weights: Vec<f64> = Vec::new();
    let mut nfa_first_err: Option<ParseError> = None;

    // Alt 0: PGroup (w=0.0, Direct/Grouping)
    *pos = nfa_saved;
    match (|| -> Result<Proc, ParseError> {
        let _t0 = expect_token!(tokens, pos, Token::LParen, "(");
        let inner = parse_proc_own(tokens, pos, 0)?;
        let _t1 = expect_token!(tokens, pos, Token::RParen, ")");
        Ok(Proc::PGroup(Box::new(inner)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // Alt 1: IntToProc (w=0.5, Cast)
    *pos = nfa_saved;
    match (|| -> Result<Proc, ParseError> {
        let inner = parse_int_own(tokens, pos, 0)?;
        Ok(Proc::IntToProc(Box::new(inner)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.5);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // Alt 2: LookaheadTuple (w=1.0, Lookahead)
    *pos = nfa_saved;
    match (|| -> Result<Proc, ParseError> {
        // ... lookahead-disambiguated parse ...
        Ok(Proc::PTuple(Box::new(a), Box::new(b)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(1.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    match nfa_results.len() {
        0 => { return Err(nfa_first_err.unwrap_or_else(|| /* ... */)); },
        _ => {
            *pos = nfa_positions[0];
            RUNNING_WEIGHT_PROC.with(|cell| cell.set(cell.get() + nfa_weights[0]));
            break 'prefix nfa_results.into_iter().next()
                .expect("nfa_results non-empty");
        },
    }
},
```

### 5.2. After F2 (remaining alternatives guarded)

```rust
Token::LParen => {
    let nfa_saved = *pos;
    let mut nfa_results: Vec<Proc> = Vec::new();
    let mut nfa_positions: Vec<usize> = Vec::new();
    let mut nfa_weights: Vec<f64> = Vec::new();
    let mut nfa_first_err: Option<ParseError> = None;

    // Alt 0: PGroup (w=0.0, Direct/Grouping)
    *pos = nfa_saved;
    match (|| -> Result<Proc, ParseError> {
        let _t0 = expect_token!(tokens, pos, Token::LParen, "(");
        let inner = parse_proc_own(tokens, pos, 0)?;
        let _t1 = expect_token!(tokens, pos, Token::RParen, ")");
        Ok(Proc::PGroup(Box::new(inner)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    if nfa_results.is_empty() {  // ◄── F2 guard: first alt failed
        // Alt 1: IntToProc (w=0.5, Cast)
        *pos = nfa_saved;
        match (|| -> Result<Proc, ParseError> {
            let inner = parse_int_own(tokens, pos, 0)?;
            Ok(Proc::IntToProc(Box::new(inner)))
        })() {
            Ok(v) => {
                nfa_results.push(v);
                nfa_positions.push(*pos);
                nfa_weights.push(0.5);
            },
            Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
        }

        // Alt 2: LookaheadTuple (w=1.0, Lookahead)
        *pos = nfa_saved;
        match (|| -> Result<Proc, ParseError> {
            // ... lookahead-disambiguated parse ...
            Ok(Proc::PTuple(Box::new(a), Box::new(b)))
        })() {
            Ok(v) => {
                nfa_results.push(v);
                nfa_positions.push(*pos);
                nfa_weights.push(1.0);
            },
            Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
        }
    } /* F2: deterministic hit (w=0.0) -- remaining alternatives skipped
         if first succeeded */

    match nfa_results.len() {
        0 => { return Err(nfa_first_err.unwrap_or_else(|| /* ... */)); },
        _ => {
            *pos = nfa_positions[0];
            RUNNING_WEIGHT_PROC.with(|cell| cell.set(cell.get() + nfa_weights[0]));
            break 'prefix nfa_results.into_iter().next()
                .expect("nfa_results non-empty");
        },
    }
},
```

### 5.3. Diff summary

The only structural change is the insertion of one `if` guard and one
closing brace.  No logic inside any alternative is modified.  The
`match nfa_results.len()` block is unchanged -- when the first
alternative succeeds, `nfa_results.len()` is 1, and the `_ =>` arm
runs identically in both versions.

---

## 6. Weight Scale Reference

The following table lists the weight assigned to each `DispatchAction`
variant by `compute_action_weight()`.  F2 applies when alternatives
with weight 0.0 are mixed with alternatives carrying higher weights.

| DispatchAction                  | Weight | Description                           | F2 Eligible |
|---------------------------------|--------|---------------------------------------|-------------|
| `Direct`                        | 0.0    | Unambiguous, single-rule dispatch     | Yes         |
| `Grouping`                      | 0.0    | Delimiter-driven (parens, braces)     | Yes         |
| `CrossCategory` (deterministic) | 0.0    | Cross-cat, no backtrack needed        | Yes         |
| `CrossCategory` (backtracking)  | 0.5    | Cross-cat, tries source first         | No          |
| `Cast`                          | 0.5    | Type coercion between categories      | No          |
| `Lookahead`                     | 1.0+n  | Needs extra tokens to disambiguate    | No          |
| `Variable`                      | 2.0    | Last-resort variable capture          | No          |

"F2 Eligible" means this action type can appear as the first
alternative and trigger the F2 guard.  Actions with weight > 0.0
cannot trigger F2 (the condition requires exactly 0.0) but benefit
from it when they appear after a weight-0.0 first alternative -- they
are the ones being skipped.

### Worked example: rhocalc `Proc` category

In the rhocalc grammar, the `Proc` category dispatches `Token::LParen`
to three rules:

| Alternative | Rule        | Action     | Weight |
|-------------|-------------|------------|--------|
| a₀          | PGroup      | Grouping   | 0.0    |
| a₁          | IntToProc   | Cast       | 0.5    |
| a₂          | FloatToProc | Cast       | 0.5    |

Since `Proc` does not need NFA spillover and w(a₀) = 0.0, F2 applies.
When `PGroup` succeeds (the common case -- most `(` tokens begin
grouped expressions), `IntToProc` and `FloatToProc` are not attempted,
saving two position-save/restore cycles and two closure invocations.

---

## 7. Source References

| File | Location | Description |
|------|----------|-------------|
| `trampoline.rs` | lines 244-257 | `first_is_deterministic` computation |
| `trampoline.rs` | lines 259-305 | NFA try-all loop with F2 guard emission |
| `wfst.rs` | lines 559-581 | `compute_action_weight()` weight table |
| `wfst.rs` | lines 198-218 | `nfa_alternative_order()` weight sorting |
| `semiring.rs` | lines 57-100 | `TropicalWeight` definition and semiring axioms |
