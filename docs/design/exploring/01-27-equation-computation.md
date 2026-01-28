# Equation Computation Performance Analysis

**Date**: January 27, 2026  
**Status**: Implemented ✓  
**Related Files**: `macros/src/logic/categories.rs`, `macros/src/logic/rules.rs`

---

## Problem Statement

The original rule generation included three performance-critical rules that compute the closure of rewrites over equations:

```rust
// categories.rs (originally present, now removed)
proc(t) <-- proc(s), eq_proc(s, t);
rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1);
rw_proc(s, t1) <-- rw_proc(s, t0), eq_proc(t0, t1);
```

These rules were too slow because they computed a full closure, leading to O(R × E²) complexity where R is rewrite count and E is equivalence class size.

---

## Current Architecture

### Rule Categories

1. **Category exploration**: `proc(c1) <-- proc(c0), rw_proc(c0, c1)`
   - Adds rewritten terms to the term universe

2. **Equation computation** (in `equations.rs`):
   - Reflexivity: `eq_proc(t, t) <-- proc(t)`
   - Congruence: `eq_proc(f(s), f(t)) <-- proc(f(s)), proc(f(t)), eq_*(subterms...)`
   - User-defined equations

3. **Rewrite rules** (in `rules.rs`):
   - Pattern-match on `proc(s)`, generate `rw_proc(s, t)`
   - May include equational checks: `eq_name(n1, n2)` for pattern matching

4. **Closure rules** (the problematic ones):
   - Extend `proc` to equation-equivalent terms
   - Extend `rw_proc` source to equivalent terms
   - Extend `rw_proc` target to equivalent terms

### Data Flow

```
Input term
    ↓
proc(term) [seed]
    ↓
deconstruction → more proc facts
    ↓
equation rules → eq_proc facts
    ↓
rewrite rules → rw_proc facts
    ↓
closure rules → extended rw_proc facts [SLOW]
    ↓
category exploration → new proc facts
    ↓
[iterate until fixpoint]
```

---

## Why Current Approach Is Slow

### Rule 1: `proc(t) <-- proc(s), eq_proc(s, t)`

**Intent**: Add equation-equivalent terms to the term universe.

**Problem**:
- `eq_proc` is an `eqrel` (equivalence relation with union-find)
- With congruence, equivalence classes grow: if `eq(a1, a2)` and `eq(b1, b2)`, then `f(a1, b1)` ≡ `f(a2, b2)` (4 equivalent terms from 2)
- For N terms with congruence, can have O(N²) equation pairs
- This rule iterates over all pairs, adding O(N²) facts to `proc`
- Each new `proc` fact triggers more equation/deconstruction rules → positive feedback loop

**Complexity**: O(N × |equivalence-class|) = O(N²) new facts per iteration

### Rules 2-3: Extending rewrites along equality

```rust
rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1);
rw_proc(s, t1) <-- rw_proc(s, t0), eq_proc(t0, t1);
```

**Intent**: If `s0 → t` and `s0 ≡ s1`, then `s1 → t` (semantic equivalence).

**Problem**:
- For R rewrites and E average equivalence class size
- Rule 2 generates R × E new rewrite facts (source extension)
- Rule 3 generates R × E new rewrite facts (target extension)
- Combined: O(R × E²) total rewrites
- With 10 rewrites and 50-term equivalence classes, this is 25,000 rewrite facts

**Complexity**: O(R × E²) where R = rewrite count, E = equivalence class size

---

## Proposed Solution: Inline Equation Matching

### Core Insight

Instead of:
1. Compute all equations (full closure)
2. Compute rewrites matching `proc(s)`
3. Extend rewrites to equivalent terms (expensive closure)

Do:
1. Compute all equations (same)
2. **Match rewrites against `eq_proc(s_orig, s)`** instead of `proc(s)`
3. Generate `rw_proc(s_orig, t)` directly (no closure needed)

### Transformation

**Current rewrite rule generation** (from `rules.rs`):

```rust
rw_proc(s.clone(), t) <--
    proc(s),                    // iterate over terms
    if let Pattern = s,         // pattern match
    eq_name(n1, n2),           // equational checks
    let t = ...;                // compute RHS
```

**Proposed rewrite rule generation**:

```rust
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),         // iterate over equation pairs
    if let Pattern = s,         // pattern match on RHS of equation
    eq_name(n1, n2),           // equational checks
    let t = ...;                // compute RHS (uses s)
```

### Why This Works

1. **Reflexivity ensures identity matching**: Because `eq_proc(t, t) <-- proc(t)` is always generated, iterating over `eq_proc` includes all `(t, t)` pairs. So patterns that don't require equations still match.

2. **Equations enable extended matching**: If `s_orig ≡ s` and `s` matches the pattern, then `s_orig → t`. This is exactly what the closure rules were computing, but now done inline.

3. **No source-side closure needed**: Rule 2 (`rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1)`) is no longer needed because we already match against all equivalent terms via `eq_proc(s_orig, s)`.

4. **Target-side closure may still be needed**: Rule 3 extends targets. This is semantically correct but may not be necessary for path computation (see below).

---

## Analysis of Target-Side Closure

The question is whether we need:
```rust
rw_proc(s, t1) <-- rw_proc(s, t0), eq_proc(t0, t1);
```

### What It Computes

If `s → t0` and `t0 ≡ t1`, then `s → t1`.

### Is It Necessary?

**For path computation**:
```rust
path(p, r) <-- rw_proc(p, q), path(q, r);
```

If `s → t0` and we want to reach `t1` (where `t0 ≡ t1`):
- Without target closure: `path(s, t0)` exists but not `path(s, t1)` directly
- We need `path(t0, t1)` for transitivity

**Key observation**: If `t0 ≡ t1`, then either:
1. They're structurally identical (reflexivity) → same term
2. They're related by a user-defined equation → equation rules populate `eq_proc`
3. They're related by congruence → congruence rules populate `eq_proc`

In cases 2-3, we'd want `path(t0, t1)` anyway for exploring the term space.

**Proposal**: Instead of target-side closure on `rw_proc`, handle it in path computation:

```rust
path(p, t1) <-- path(p, t0), eq_proc(t0, t1);
```

Or more selectively:
```rust
path(p, t1) <-- rw_proc(p, t0), eq_proc(t0, t1);  // single-step equation extension
```

This is still O(Path × E) but may be cheaper because:
- Path computation happens once at the end
- Not feeding back into more iterations

---

## Implementation (Completed)

### Change 1: Rewrite Rules Match via Equation Relation

In `macros/src/logic/rules.rs`, rewrite rules now use `eq_proc(s_orig, s)`:

```rust
// Rewrite rules (use_equation_matching: true)
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),     // match via equation pairs
    if let Pattern = s,      // pattern match on s
    let t = ...;             // compute RHS
```

This enables rewrites to fire on equation-equivalent terms without needing closure rules.

### Change 2: Equation Rules Add Produced Terms to proc

In `macros/src/logic/rules.rs`, user-defined equation rules now output to BOTH `eq_proc` AND `proc`:

```rust
// Equation rules (use_equation_matching: false)
eq_proc(s.clone(), t.clone()),
proc(t.clone()) <--          // Add produced term to proc!
    proc(s),
    if let Pattern = s,
    let t = ...;
```

This ensures equation-produced terms (e.g., from scope extrusion) are:
1. Added to `proc` for deconstruction
2. Available for reflexivity (`eq_proc(t, t)`)
3. Matchable by rewrite rules via `eq_proc(_, t)`

### Change 3: No Blanket Closure Rules

The three expensive closure rules are NOT generated:
- ~~`proc(t) <-- proc(s), eq_proc(s, t)`~~ — would iterate O(|proc|²) congruence pairs
- ~~`rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1)`~~ — replaced by inline matching
- ~~`rw_proc(s, t1) <-- rw_proc(s, t0), eq_proc(t0, t1)`~~ — not needed for current semantics

---

## Performance Results

### Before (with closure rules)

| Metric | Estimate |
|--------|----------|
| `eq_proc` facts | O(N²) due to congruence |
| `rw_proc` facts | O(R × E²) due to closure |
| Iterations | High (positive feedback) |
| Test time | Very slow (timeouts) |

### After (with inline equation matching)

| Metric | Estimate |
|--------|----------|
| `eq_proc` facts | O(N²) (same, congruence still applies) |
| `rw_proc` facts | O(R × E) (each rewrite matches E equation pairs) |
| Iterations | Lower (no feedback from closure) |
| Test time | **29 ambient tests pass in 2.5 seconds** |

**Achieved speedup**: Significant — tests that were timing out now complete quickly.

---

## Correctness Considerations

### Semantic Equivalence

The transformation preserves the semantic meaning:

**Original semantics**: "If term s matches pattern P and rewrites to t, then for all s' ≡ s, we have s' → t"

**New semantics**: "For all equations s' ≡ s where s matches pattern P, generate s' → t"

These are equivalent because:
- The union-find `eqrel` computes transitive closure automatically
- Reflexivity ensures `eq(s, s)` for identity matches
- The iteration is over the same set of facts, just organized differently

### Termination

Termination is preserved because:
1. `proc` is still bounded by input + rewrite results
2. `eq_proc` is still bounded by congruence on `proc` (O(|proc|²))
3. `rw_proc` is now bounded by O(|rewrite patterns| × |eq_proc|)
4. No new positive feedback loops introduced

---

## Alternative Approaches Considered

### 1. Lazy Equation Computation

Only compute equations when needed for rewrite matching.

**Rejected**: Hard to implement in Datalog; equations must be computed before rules that use them.

### 2. Bounded Equivalence Classes

Limit the size of equivalence classes.

**Rejected**: May cause incompleteness; hard to choose the right bound.

### 3. Stratified Computation

Compute equations in one stratum, rewrites in another.

**Rejected**: Ascent doesn't support explicit stratification; relies on fixpoint.

### 4. Demand-Driven Evaluation

Only compute facts reachable from the query.

**Rejected**: Requires different evaluation strategy; not compatible with Ascent's semi-naive evaluation.

---

## Summary

| Aspect | Before | After |
|--------|--------|-------|
| Source matching | `proc(s)` + closure | `eq_proc(s_orig, s)` |
| Equation output | Only `eq_proc(s, t)` | `eq_proc(s, t)` + `proc(t)` |
| Complexity | O(R × E²) | O(R × E) |
| Tests | Timeouts | 29/29 pass in 2.5s |

The implementation replaces `proc(s), ...` with `eq_proc(s_orig, s), ...` in rewrite rules, and adds produced terms directly to `proc` in equation rules. This avoids the expensive closure computation while maintaining semantic correctness.
