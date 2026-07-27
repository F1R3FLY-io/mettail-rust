# Rholang Performance Analysis

**Date**: November 9, 2025
**Execution Time**: 18.5 seconds
**Status**: 🔴 TOO SLOW

---

## Current Performance

**Test case**: 7 parallel processes with 3 communication pairs
**Time**: 18.5 seconds
**Result**: 9 paths to normal forms (correct)

---

## Performance Bottlenecks (Ranked by Impact)

### 1. 🔥 Collection Deconstruction on Every Iteration (MAJOR)

**Line 227-228**:
```rust
proc(elem.clone()) <-- proc(t), if let Proc::PPar(bag) = t,
    for elem in bag.iter().map(|(e, _count)| e);
```

**Problem**:
- **Every** `proc(t)` fact triggers a full iteration over the bag
- If there are N `proc` facts with M-element bags, this generates N×M new `proc` facts
- These new facts trigger MORE iterations (recursive explosion)

**Example**:
- Start: 1 fact `proc({a, b, c})`
- After deconstruction: 4 facts: `proc({a,b,c})`, `proc(a)`, `proc(b)`, `proc(c)`
- Next iteration: Each of these 4 facts checked for more deconstruction
- If any result is a collection, exponential growth continues

**Impact**:
- With 7 top-level processes in the test case
- Each rewrite creates new terms
- Each new term is deconstructed → more facts
- Easily 100s-1000s of `proc` facts

**Cost**: O(N×M) where N = proc facts, M = avg bag size

---

### 2. 🔥 Equational Closure Computation (MAJOR)

**Lines 235-256**: Reflexivity, symmetry, transitivity, congruence rules

**Problem**:
- `eq_proc` is an `eqrel` (union-find equivalence relation)
- Every new `proc` fact triggers reflexivity: `eq_proc(t, t)`
- Congruence rules (lines 238-247) trigger on EVERY combination of equivalent subterms
- With N proc facts, congruence generates O(N²) checks

**Example**:
- If `eq_proc(P1, P2)` and `eq_proc(Q1, Q2)`
- Then check `POutput(P1, Q1)` ≡ `POutput(P2, Q2)`
- For M output constructors with 2 arguments, this is O(M × N²)

**Impact**:
- With 100+ proc facts, this is 10,000+ congruence checks
- Most are redundant (already equivalent)
- But Ascent checks them all

**Cost**: O(N²) for N proc facts

---

### 3. 🔥 Rewrite Path Transitivity (MAJOR)

**Lines 259-264**: Equational matching for rewrites

```rust
rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1);
rw_proc(s, t1) <-- rw_proc(s, t0), eq_proc(t0, t1);
```

**Problem**:
- For every rewrite `rw_proc(s, t)` and every equivalence `eq_proc(s, s')`, generate `rw_proc(s', t)`
- This creates exponential rewrite facts when combined with congruence

**Example**:
- If `s` is equivalent to 10 terms (via congruence)
- And `t` is equivalent to 10 terms
- Then 1 rewrite becomes 100 rewrite facts

**Impact**:
- With complex terms, many equivalences
- Rewrite relation explodes

**Cost**: O(R × E) where R = rewrite facts, E = equivalence classes

---

### 4. 🟡 Indexed Projection Extraction (MEDIUM)

**Lines 269-278**: Extract inputs and outputs for matching

```rust
pinput_proj_r0_p0(parent, chan, x, p, elem) <--
    proc(parent),
    if let Proc::PPar(ref bag_field) = parent,
    for (elem, _count) in bag_field.iter(),
    if let Proc::PInput(ref f0, ref f1) = elem, ...
```

**Problem**:
- For EVERY `proc(parent)` fact
- Check if it's a `PPar`
- Iterate over ALL elements
- Check each element's constructor

**Impact**:
- With N proc facts, M avg bag size
- K elements are PInput
- This is O(N × M × pattern_check_cost)

**Cost**: O(N × M) iterations, most don't match

---

### 5. 🟡 Path Computation (MEDIUM)

**Lines 88-91 in rholang.rs**:
```rust
path(redex, redex) <-- for _ in [()];
path(redex, q) <-- redex_eq(q);
path(p, q) <-- rw_proc(p, q);
path(p, r) <-- rw_proc(p, q), path(q, r);  // Transitivity
```

**Problem**:
- Path transitivity: if `p → q` and `q → r`, then `p → r`
- With K rewrites, this can generate O(K²) paths
- Most paths are redundant for final result

**Impact**:
- Moderate - paths are computed but not the primary bottleneck
- With deep rewrite chains, can slow down

**Cost**: O(K²) for K rewrite facts

---

## Quantitative Analysis

Let's estimate the costs for the test case:

### Initial State
- 7 top-level processes in collection
- After deconstruction: ~15-20 `proc` facts

### After First Rewrite
- 1 rewrite generates new term
- New term deconstructed → 5 more proc facts
- Total: ~25 proc facts

### Congruence Explosion
- 25 proc facts × reflexivity = 25 eq_proc facts
- Congruence on `POutput(name, proc)`: 25² = 625 checks
- Congruence on nested PPar: more checks
- **Total eq_proc facts: 100-500**

### Rewrite Explosion
- Each rewrite `rw(s, t)` combined with eq_proc creates more rw facts
- 10 base rewrites × 50 equivalences = **500 rw_proc facts**

### Deconstruction Loop
- Every new proc fact triggers deconstruction
- Creates more proc facts
- Which trigger more congruence checks
- **Positive feedback loop**

### Total Iterations
- Ascent runs until fixpoint
- With positive feedback: **10-20 iterations**
- Each iteration: 1000s of clause evaluations
- **Total: 100,000+ clause evaluations**

---

## Performance Breakdown (Estimated)

| Component | Time (est) | Percentage |
|-----------|------------|------------|
| Collection deconstruction | 8s | 43% |
| Equational closure | 6s | 32% |
| Rewrite transitivity | 3s | 16% |
| Path computation | 1s | 5% |
| Other | 0.5s | 3% |

---

## Root Cause

The fundamental issue is **positive feedback loops**:

1. New term → deconstruct → more proc facts
2. More proc facts → more congruence checks → more eq_proc facts
3. More eq_proc facts → more rewrite variants → more rw_proc facts
4. More rw_proc facts → more new terms → back to step 1

Each iteration amplifies the problem.

---

## Solutions (Ranked by Impact)

### 🥇 Option 1: Lazy Deconstruction (Highest Impact)

**Stop deconstructing everything eagerly.**

**Current**:
```rust
proc(elem) <-- proc(t), if let Proc::PPar(bag) = t, for elem in bag.iter();
```

**Proposed**:
```rust
// Only deconstruct when needed for pattern matching
// Remove the eager deconstruction rule entirely
```

**How it works**:
- Indexed projection already iterates over bags when needed
- Don't add elements as separate `proc` facts
- Only track top-level terms

**Impact**:
- Eliminates the N×M explosion
- Reduces proc facts by 80-90%
- **Expected speedup: 5-10x**

**Changes needed**:
- Remove line 227-228 from generated code
- Ensure indexed projection still works (it should - it iterates directly)
- Test that pattern matching still finds matches

---

### 🥈 Option 2: Limit Congruence Rules (High Impact)

**Don't generate congruence for ALL constructors.**

**Current**:
- Congruence for `PDrop`, `POutput`, `NQuote`
- O(N²) cost for each

**Proposed**:
```rust
// Only essential congruence:
eq_proc(PDrop(n1), PDrop(n2)) <-- eq_name(n1, n2);
// Skip POutput congruence - not needed for correctness
// Rewrite engine already handles this via pattern matching
```

**Impact**:
- Reduces eq_proc facts by 50-80%
- **Expected speedup: 2-3x**

**Trade-off**:
- Less complete equivalence relation
- But rewrites still work (they use pattern matching, not equations)

---

### 🥉 Option 3: Incremental Computation (Medium Impact)

**Only process new facts, not all facts.**

This requires Ascent's `ascent!` macro (not `ascent_run!`) with explicit iteration control.

**Impact**:
- Reduces redundant computation
- **Expected speedup: 1.5-2x**

**Complexity**: High - requires restructuring the code

---

### Option 4: Parallel Execution (Medium Impact)

Use `ascent_run_par!` for parallel evaluation.

**Status**: Currently broken (see docs/ASCENT-PARALLEL-ISSUE.md)

**Expected speedup**: 2-4x on multi-core

**Prerequisites**: Fix the type mismatch issue first

---

### Option 5: Limit Path Depth (Low Impact)

Add depth limit to path computation:

```rust
relation path_depth(Proc, Proc, usize);
path_depth(p, p, 0) <-- proc(p);
path_depth(p, r, d+1) <-- path_depth(p, q, d), rw_proc(q, r), if d < 10;
```

**Impact**: Small - paths aren't the main bottleneck

---

## Recommended Immediate Fix

**Implement Option 1 (Lazy Deconstruction)**:

1. **Remove** the eager deconstruction rule (line 227-228)
2. **Test** that indexed projection still works
3. **Measure** the speedup

**Expected result**: 2-3 seconds instead of 18.5 seconds

**Why this works**:
- Indexed projection already iterates over collections when matching
- We don't need to eagerly add all elements as separate facts
- This eliminates the main source of fact explosion

---

## Long-term Optimizations (Q1 2026)

1. **Selective Congruence**: Only generate congruence rules when needed
2. **Demand-driven Evaluation**: Only compute what's needed for the query
3. **Memoization**: Cache intermediate results
4. **Parallel Execution**: Once the type issue is fixed
5. **Specialized Data Structures**: Custom data structures for specific patterns

---

## Testing the Fix

After removing eager deconstruction:

```bash
cargo run --bin rholang
```

**Check**:
- Time < 5 seconds (target: 2-3 seconds)
- Same 9 paths found (correctness)
- No missing rewrites

**Measure**:
- Count of `proc` facts (should be < 50, not 100+)
- Count of `eq_proc` facts (should be < 100)
- Count of `rw_proc` facts (should be < 50)

---

## Summary

**Main bottleneck**: Eager collection deconstruction causing fact explosion
**Root cause**: Positive feedback loop (more facts → more checks → more facts)
**Quick fix**: Remove eager deconstruction, rely on indexed projection
**Expected speedup**: 5-10x (18.5s → 2-3s)
**Implementation**: Simple - remove one line from ascent_gen.rs

