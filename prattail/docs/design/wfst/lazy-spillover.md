# F3: Lazy Spillover (Demand-Driven Replay)

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Mechanism](#2-mechanism)
3. [Refactored parse_preserving_vars Flow](#3-refactored-parse_preserving_vars-flow)
4. [Correctness Argument](#4-correctness-argument)
5. [Interaction with substitute_env](#5-interaction-with-substitute_env)
6. [Worked Examples](#6-worked-examples)
7. [Performance Impact](#7-performance-impact)
8. [Source References](#8-source-references)

---

## 1. Problem Statement

When multiple grammar rules within the same category share a dispatch token,
PraTTaIL's NFA disambiguation (Layer 2.5) resolves the ambiguity by trying
all N alternatives in the NFA try-all loop.  The primary result (lowest WFST
weight) is returned from the prefix match, while the remaining N-1
alternatives are **spilled** into a thread-local buffer
(`NFA_PREFIX_SPILL_CAT`) for **forced-prefix replay**.  During replay, each
spilled alternative is injected into a fresh `Cat::parse(input)` call via
the `NFA_FORCED_PREFIX_CAT` thread-local, so that `substitute_env` and
`from_alternatives` can resolve the ambiguity semantically.

The problem: every spilled alternative triggers a **full parser invocation**
-- prefix dispatch, the entire infix loop, environment substitution -- even
when the primary result is already a concrete, ground term.  Ground terms
are semantically unambiguous: they contain no free variables, so no
alternative interpretation can produce a "better" result.  The replay work
is wasted.

### Scale of the waste

Consider a grammar with K categories, each having M ambiguous dispatch
tokens with an average of A alternatives per token.  Without F3, every
successful parse of an ambiguous token triggers (A-1) replay invocations,
each running the full parser.  For a typical expression like `float(3)` in
the Calculator grammar:

| Component           | Count | Cost per replay          |
|---------------------|-------|--------------------------|
| Spilled alternatives | 3     | (FloatId, IntToFloat, BoolToFloat, StrToFloat minus primary) |
| Lex pass per replay | 1     | Full re-lex of input     |
| Prefix dispatch     | 1     | Token match + rule body  |
| Infix loop          | 1     | BP comparison + possible continuation |
| Total per parse     | 3     | 3 full parser invocations |

When the primary result is `3.0` (a ground float literal), all three
replays produce results that `from_alternatives` would discard in favor
of the primary.  The replay work is pure overhead.

---

## 2. Mechanism

F3 inserts a **demand check** between the primary parse success and the
spillover replay loop.  After the primary parse succeeds, F3 inspects the
result via `is_accepting()` -- a method that delegates to `is_ground()`,
which recursively checks whether the term contains any free variables.

### Decision logic

```
if primary is accepting (ground/concrete):
    discard all N-1 spilled alternatives   -- no replay needed
else (primary contains free variables):
    replay all N-1 spilled alternatives    -- semantic disambiguation required
```

The check is performed in the generated `parse_preserving_vars` method,
immediately after the primary parse succeeds and the spillover buffer is
drained from the thread-local:

```rust
let spilled: Vec<(Cat, usize, f64)> = NFA_PREFIX_SPILL_CAT.with(|cell| cell.take());
let primary_is_accepting = successes.last()
    .map_or(false, |s| s.is_accepting());
if !primary_is_accepting {
    for (alt_prefix, alt_pos, alt_weight) in spilled {
        NFA_FORCED_PREFIX_CAT.with(|cell| cell.set(Some((alt_prefix, alt_pos, alt_weight))));
        if let Ok(alt_term) = Cat::parse(input) {
            successes.push(Inner::CatVariant(alt_term));
            success_weights.push(alt_weight);
        }
        NFA_PREFIX_SPILL_CAT.with(|cell| { cell.take(); });
    }
}
/* else: F3 skipped replay -- primary is ground, N-1 alternatives discarded */
```

### is_accepting delegation chain

The `is_accepting()` method on the inner enum delegates to `is_ground()`:

```
Inner::CatVariant(inner) => inner.is_ground()
Inner::Ambiguous(_)      => false
```

`is_ground()` is a generated per-category method that recursively traverses
the term:

| Variant kind   | `is_ground()` result |
|----------------|----------------------|
| Var            | `false` (always)     |
| Literal        | `true` (always)      |
| Nullary        | `true` (always)      |
| Regular        | `f0.is_ground() && f1.is_ground() && ...` |
| Collection     | `coll.iter().all(\|x\| x.is_ground())` |
| Binder         | pre-scope fields ground `&&` scope body ground |
| Ambiguous      | `false` (always)     |

---

## 3. Refactored parse_preserving_vars Flow

The following diagram shows the complete flow of `parse_preserving_vars`
for a single category parse attempt, with F3's decision point highlighted:

```
┌─────────────────────────────────────────────────────────────────────┐
│ parse_preserving_vars(input)                                        │
│                                                                     │
│   for each category Cat in parse_order:                             │
│                                                                     │
│     ┌─────────────────────────────────────────────────────────┐     │
│     │ Cat::parse(input)                                       │     │
│     └──────────────┬──────────────────────────────────────────┘     │
│                    │                                                │
│              ┌─────┴──────┐                                         │
│              │  Result?   │                                         │
│              └──┬──────┬──┘                                         │
│            Ok   │      │ Err                                        │
│     ┌───────────▼┐  ┌──▼───────────────────────────────┐            │
│     │ Push to    │  │ Clear spillover, record first_err │            │
│     │ successes  │  └──────────────────────────────────┘            │
│     └──────┬─────┘                                                  │
│            │                                                        │
│     ┌──────▼──────────────────────────────────┐                     │
│     │ Drain spillover buffer:                 │                     │
│     │ spilled = NFA_PREFIX_SPILL_CAT.take()   │                     │
│     └──────┬──────────────────────────────────┘                     │
│            │                                                        │
│     ┌──────▼──────────────────────────────────┐                     │
│     │ F3 DECISION POINT                       │                     │
│     │ primary_is_accepting =                  │                     │
│     │   successes.last().is_accepting()       │                     │
│     └──────┬──────────────────────────────────┘                     │
│            │                                                        │
│       ┌────┴────────────┐                                           │
│       │ is_accepting()? │                                           │
│       └──┬───────────┬──┘                                           │
│    true  │           │ false                                        │
│   ┌──────▼────────┐  ┌──────▼──────────────────────────────────┐    │
│   │ SKIP REPLAY   │  │ FULL REPLAY                             │    │
│   │               │  │                                         │    │
│   │ Discard all   │  │ for each (alt, pos, weight) in spilled: │    │
│   │ N-1 spilled   │  │   NFA_FORCED_PREFIX_CAT.set(alt)        │    │
│   │ alternatives. │  │   Cat::parse(input)                     │    │
│   │               │  │   push Ok result to successes            │    │
│   │ Zero replays. │  │   clear nested spillover                 │    │
│   └───────────────┘  └─────────────────────────────────────────┘    │
│                                                                     │
│   match successes.len():                                            │
│     0 => Err(first_err)                                             │
│     1 => Ok(Term(successes[0]))                                     │
│     _ => Ok(Term(from_alternatives(successes)))                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 4. Correctness Argument

### Theorem: Skipping replay when the primary is ground preserves semantics.

**Claim:** If the primary parse result `p` satisfies `p.is_accepting()`,
then `from_alternatives([p] ++ replay_results)` would return `p`
regardless of the replay results.  Therefore, skipping replay does not
change the final output.

**Definitions.**

- A term `t` is **ground** iff `t.is_ground() == true` -- it contains no
  free variables at any depth.
- A term `t` is **accepting** iff `is_accepting(t) == true`, which
  delegates to `is_ground()`.
- `from_alternatives(alts)` resolves a vector of parse alternatives into
  a single term via the following priority:
  1. If `|alts| == 1`: return the sole alternative.
  2. Count the accepting alternatives.
  3. If exactly 1 is accepting: return it.
  4. If N > 1 are accepting: return the one with lowest WFST weight.
  5. If 0 are accepting: return `Ambiguous(alts)`.

**Lemma 1 (Ground terms are accepting).**

By construction, `is_accepting()` delegates to `is_ground()`.  If `p` is
ground, then `p.is_accepting() == true`.  This is a direct consequence
of the delegation chain:

```
is_accepting(Inner::CatVariant(inner)) = inner.is_ground()
```

**Lemma 2 (Primary is always present in alternatives).**

The primary result `p` is always pushed to `successes` before the replay
loop.  Replay results are appended after `p`.  Therefore `p` is always
at index 0 in the alternatives passed to `from_alternatives`.

**Lemma 3 (Primary weight is minimal).**

The NFA try-all loop sorts alternatives by WFST weight (via
`nfa_alternative_order()`).  The primary result has weight `w_0`, and
all spilled alternatives have weight `w_i >= w_0` (for `i >= 1`).
After replay, replay results accumulate additional weight via
`RUNNING_WEIGHT_CAT`, so their final weight is `w_i + delta_i` where
`delta_i >= 0`.

**Proof.**

Assume `p.is_accepting() == true`.  We show that
`from_alternatives([p] ++ R) == p` for any replay results `R`.

**Case 1: `R` is empty (all replays failed).**
`from_alternatives([p])` returns `p` directly (single-element case).

**Case 2: `R` is non-empty, no replay result is accepting.**
The accepting count is 1 (only `p`).  By rule (3) of `from_alternatives`,
the sole accepting alternative is returned.  That is `p`.

**Case 3: `R` is non-empty, some replay results are also accepting.**
The accepting count is N > 1.  By rule (4) of `from_alternatives`, the
accepting alternative with the lowest WFST weight is selected.  By
Lemma 3, `p` has weight `w_0 <= w_i + delta_i` for all replay results.
Therefore `p` is selected (or in the degenerate case of equal weights,
`p` is at index 0 and `min_by` preserves first-encountered on ties).

In all three cases, `from_alternatives` returns `p`.  Skipping the
replay loop therefore produces the same result as performing it.  **QED**

### Edge cases

| Case | Behavior |
|------|----------|
| Primary is `Ambiguous(...)` | `is_accepting()` returns false; replay proceeds (correct) |
| Primary is a Var term | `is_ground()` returns false; replay proceeds (correct) |
| Primary is a nested term with a deep Var | `is_ground()` recursively finds it; replay proceeds (correct) |
| No spillover occurred (empty spill buffer) | The `for` loop body executes 0 times; F3 adds only the `is_accepting()` check |
| Binder with ground body | `is_ground()` traverses into scope; returns true; replay skipped (correct) |

---

## 5. Interaction with substitute_env

The `substitute_env` method on the inner enum replaces free variables in
a term with their bound values from the environment.  F3 interacts with
substitution as follows:

### Timeline

```
         parse time                    eval time
        ───────────────────────────  ───────────────────
        Cat::parse(input)            substitute_env(env)
              │                            │
              ├─ primary result            ├─ variables resolved
              ├─ F3 check: is_accepting?   ├─ may become ground
              ├─ replay or skip            ├─ from_alternatives
              └─ successes collected       └─ final term
```

### Why F3 is correct despite deferred substitution

Variables in the parse result trigger replay because the primary is NOT
accepting at parse time.  After substitution, those variables may become
ground -- but substitution happens **after** parsing, in a separate phase.
At parse time, the presence of free variables correctly signals that
alternative interpretations may resolve differently under substitution.

Consider `float(x)` where `x` is bound in the environment:

1. **Parse time:** `Cat::parse("float(x)")` produces `FloatId(FreeVar("x"))`.
   `is_ground()` returns `false` because `FreeVar` is a Var variant.
   F3 triggers full replay.

2. **Replay:** Spilled alternatives (e.g., `IntToFloat`, `BoolToFloat`)
   are replayed.  Each produces its own interpretation of `x`.

3. **Eval time:** `substitute_env` resolves `x` in each alternative.
   `from_alternatives` selects the best accepting result.

If F3 had incorrectly skipped replay at step 1 (it does not -- the primary
is not ground), only `FloatId(FreeVar("x"))` would be available for
substitution.  The cross-category alternatives would be lost, potentially
producing a semantically incorrect result.

### When substitution cannot affect F3's decision

If the primary is ground at parse time, substitution is a no-op on it
(there are no free variables to replace).  The term is already fully
resolved.  F3 correctly skips replay because:

- The primary cannot change under substitution.
- No alternative can produce a "more ground" result than one that is
  already fully ground.
- `from_alternatives` would select the primary anyway (Section 4).

---

## 6. Worked Examples

### Example 1: `float(3)` -- ground primary, replay skipped

Input: `"float(3)"` in the Calculator grammar.

**NFA try-all phase:**

| Alternative   | Rule        | Weight | Result          | Accepting? |
|---------------|-------------|--------|-----------------|------------|
| a_0 (primary) | FloatId     | 0.0    | `Float::NumLit(3.0)` | Yes   |
| a_1 (spilled) | IntToFloat  | 0.3    | `Int::NumLit(3)`     | --    |
| a_2 (spilled) | BoolToFloat | 0.8    | (parse fails)        | --    |
| a_3 (spilled) | StrToFloat  | 1.5    | (parse fails)        | --    |

**F3 decision:**

```
primary = Inner::Float(Float::NumLit(3.0))
primary.is_accepting() = Float::NumLit(3.0).is_ground() = true   // Literal => true
```

Result: **skip all 3 replays**.  The primary `Float::NumLit(3.0)` is
returned directly.

**Savings:** 3 replay invocations eliminated (3 lex passes, 3 prefix
dispatches, 3 infix loops).

### Example 2: `float(x)` with `x` bound -- non-ground primary, replay triggered

Input: `"float(x)"` in the Calculator grammar, with environment
`{x -> 42}`.

**NFA try-all phase:**

| Alternative   | Rule        | Weight | Result               | Accepting? |
|---------------|-------------|--------|----------------------|------------|
| a_0 (primary) | FloatId     | 0.0    | `Float::FVar("x")`  | No         |
| a_1 (spilled) | IntToFloat  | 0.3    | `Int::IVar("x")`    | --         |
| a_2 (spilled) | BoolToFloat | 0.8    | (parse fails)        | --         |
| a_3 (spilled) | StrToFloat  | 1.5    | (parse fails)        | --         |

**F3 decision:**

```
primary = Inner::Float(Float::FVar(FreeVar("x")))
primary.is_accepting() = Float::FVar(_).is_ground() = false      // Var => false
```

Result: **full replay** of all spilled alternatives.

**Replay results:**

| Replay | Forced prefix | Result                    | Weight |
|--------|---------------|---------------------------|--------|
| a_1    | IntToFloat    | `Inner::Float(IntToFloat(Int::IVar("x")))` | 0.3 |
| a_2    | BoolToFloat   | Err (parse fails)         | --     |
| a_3    | StrToFloat    | Err (parse fails)         | --     |

**Post-substitution:** `substitute_env({x -> 42})` resolves `FVar("x")`
to `42`.  `from_alternatives` selects the accepting result with the
lowest weight.

### Example 3: `3 + 4` -- ground compound term, replay skipped

Input: `"3 + 4"` in the Calculator grammar.

**NFA try-all phase:** Prefix dispatch on `Token::Integer` for the `Int`
category.  The primary result is `Int::Add(Int::NumLit(3), Int::NumLit(4))`.

**F3 decision:**

```
primary = Inner::Int(Int::Add(Box(Int::NumLit(3)), Box(Int::NumLit(4))))
primary.is_accepting()
  = Int::Add(a, b).is_ground()
  = a.is_ground() && b.is_ground()
  = Int::NumLit(3).is_ground() && Int::NumLit(4).is_ground()
  = true && true
  = true
```

Result: **skip replay**.  The deep recursive `is_ground()` check correctly
identifies the compound term as ground despite having nested structure.

### Example 4: `3 + x` -- non-ground compound term, replay triggered

Input: `"3 + x"` in the Calculator grammar.

**F3 decision:**

```
primary = Inner::Int(Int::Add(Box(Int::NumLit(3)), Box(Int::IVar("x"))))
primary.is_accepting()
  = Int::Add(a, b).is_ground()
  = a.is_ground() && b.is_ground()
  = Int::NumLit(3).is_ground() && Int::IVar("x").is_ground()
  = true && false
  = false
```

Result: **full replay**.  The presence of `IVar("x")` at any depth causes
`is_ground()` to return false, correctly triggering replay for semantic
disambiguation.

---

## 7. Performance Impact

### Overhead of F3

The only added operation on the critical path is a single `is_accepting()`
call after the primary parse succeeds.  This call delegates to `is_ground()`,
whose cost depends on the term structure:

| Term structure        | `is_ground()` cost | Notes |
|-----------------------|-------------------|-------|
| Literal (`NumLit`)    | O(1) | Single pattern match |
| Nullary constructor   | O(1) | Single pattern match |
| Var (`FVar`, `IVar`)  | O(1) | Single pattern match, returns false immediately |
| Regular (N fields)    | O(N) | Short-circuit on first non-ground field |
| Collection (M elems)  | O(M) | Short-circuit via `.all()` |
| Nested depth D        | O(D) | Recursive traversal |

For the common case of ground literals (the majority of real-world
expressions), the cost is O(1) -- a single pattern match arm.

### Savings

When the primary is ground, F3 eliminates all (A-1) replay invocations
per ambiguous dispatch.  Each replay involves:

1. Thread-local set (`NFA_FORCED_PREFIX_CAT.set(...)`) -- O(1)
2. Full `Cat::parse(input)` invocation -- O(|input| * grammar_complexity)
3. Thread-local clear (`NFA_PREFIX_SPILL_CAT.take()`) -- O(1)

The dominant cost is (2), the full parser re-invocation.  For a grammar
with A alternatives, F3 saves (A-1) full parser calls.

### Expected benefit by grammar profile

| Grammar profile                    | Primary ground? | F3 benefit |
|------------------------------------|-----------------|------------|
| Arithmetic on literals (e.g., `3 + 4 * 2`) | Yes | Eliminates all replay |
| Programs with bound variables (e.g., `let x = 3 in x + 1`) | Mixed | Replay only for variable subexpressions |
| Purely symbolic (e.g., `f(x, y)`)  | No | No benefit (replay still needed) |

For the Calculator grammar's benchmark suite, the majority of expressions
are ground (literal arithmetic).  F3 eliminates replay for all of these,
reducing the per-parse cost to a single primary invocation plus one O(1)
`is_accepting()` check.

### Interaction with F1 and F2

F3 is **complementary** to both F1 (Spillover Pruning) and F2 (Early
Termination).  The three optimizations target different phases:

| Optimization | Phase | When it helps |
|-------------|-------|---------------|
| F2 (Early Termination) | NFA try-all loop | First alt is deterministic (w=0.0), no spillover |
| F1 (Spillover Pruning) | Spill loop (before replay) | High-weight alternatives pruned by beam |
| F3 (Lazy Spillover) | Replay loop (after primary) | Primary is ground, all replay skipped |

When F1 has already pruned some alternatives and F3 determines the primary
is ground, the remaining (post-F1) alternatives are also skipped.  The
optimizations compose: F1 reduces the spill buffer size, and F3 may then
skip the reduced buffer entirely.

---

## 8. Source References

| File | Location | Description |
|------|----------|-------------|
| `macros/src/gen/runtime/language.rs` | lines 1136-1156 | F3 lazy spillover in `parse_preserving_vars` codegen |
| `macros/src/gen/runtime/language.rs` | lines 270-278 | `is_accepting()` method on inner enum |
| `macros/src/gen/runtime/language.rs` | lines 284-326 | `from_alternatives()` disambiguation logic |
| `macros/src/gen/runtime/language.rs` | lines 205-207 | `is_accepting` delegation to `is_ground()` |
| `macros/src/gen/term_ops/ground.rs` | lines 31-59 | `is_ground()` generation for all categories |
| `macros/src/gen/term_ops/ground.rs` | lines 62-85 | Per-variant `is_ground` arm generation |
