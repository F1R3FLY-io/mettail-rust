# Ascent Parallel Execution Issue

**Date**: November 9, 2025
**Updated**: 2026-03-21
**Status**: Resolved — `ascent-parallel` feature retained as no-op; `generate_ascent_struct()` always uses serial `ascent!`

> **Resolution (2026-03-21):** The `dual_indexed` BYODS provider (used by all
> generated languages) only implements serial Ascent traits. Rather than implementing
> parallel-safe types (high effort, no proven need), `generate_ascent_struct()` was
> changed to always emit `ascent!`. The `ascent-parallel` feature flag is kept for
> forward compatibility. `compile_error!` guard arms in the provider macros prevent
> accidental re-enablement. See `dual_indexed_parallel_limitation.md` for details.

**Original Status**: 🔴 INCOMPATIBLE - Requires Code Generation Changes

---

## Problem

When switching from `ascent_run!` to `ascent_run_par!` in `examples/rhocalc.rs`, we get type errors:

```
mismatched types
expected reference `&&(Name, Name)`
   found reference `&(Name, Name)`

mismatched types
expected reference `&&(Proc, Proc)`
   found reference `&(Proc, Proc)`
```

---

## Root Cause

### Discovery from Ascent Source

In `/ascent-byods-rels/src/eqrel_binary.rs`:

```rust
// Line 60-68
macro_rules! eqrel_binary_rel_ind_common {
   (($col1: ty, $col2: ty), $indices: expr, ser, ()) => {
      $crate::eqrel_ind::EqRelIndCommon<$col1>    // Serial
   };

   // par:
   (($col1: ty, $col2: ty), $indices: expr, par, ()) => {
      $crate::ceqrel_ind::CEqRelIndCommon<$col1>  // Parallel  ⚠️ Different type!
   };
}
```

**Serial mode** uses `eqrel_ind::EqRelIndCommon`
**Parallel mode** uses `ceqrel_ind::CEqRelIndCommon` (concurrent eqrel)

### Iterator Type Difference

In `/ascent-byods-rels/src/ceqrel_ind.rs` line 205-215:

```rust
impl<'a, T: Clone + Hash + Eq + Sync> CRelIndexRead<'a> for EqRelInd0<'a, T> {
   type Key = (T,);
   type Value = (&'a T,);  // ⚠️ Single reference

   type IteratorType = rayon::iter::Map<SetOfAddedParIter<'a, T>, fn(&T) -> (&T,)>;

   fn c_index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
      let set = self.0.c_set_of_added(&key.0)?;
      let res: Self::IteratorType = set.map(|x| (x,));  // ⚠️ Returns &T, not &&T
      Some(res)
   }
}
```

Compare to serial `eqrel_ind.rs`:

```rust
impl<'a, T: Clone + Hash + Eq> RelIndexRead<'a> for EqRelInd0<'a, T> {
   type Value = (&'a T,);  // Single reference

   fn index_get(&'a self, key: &Self::Key) -> Option<Self::IteratorType> {
      // ... returns iterator over (&T,)
   }
}
```

**Wait, both are single references!** So the issue must be elsewhere...

### The Real Issue: Generated Code Expectations

Our generated code in `ascent_gen.rs` and `rewrite_gen.rs` likely uses patterns expecting double references because of how Ascent's `iter()` works vs `par_iter()`.

Let me check what patterns we generate...

---

## Investigation Needed

### Questions to Answer

1. **What pattern does our code generate for eqrel joins?**
   - Check `ascent_gen.rs` where we generate `eq_name(n1, n2)` clauses
   - Check `rewrite_gen.rs` where we generate indexed projection joins

2. **Does the pattern differ based on relation type?**
   - Regular relations: `proc(t)`
   - Eqrel relations: `eq_name(n1, n2)`

3. **Are we dereferencing correctly?**
   - Look for `.iter()` vs `.par_iter()` assumptions
   - Check if we're adding extra `&` in patterns

---

## Hypothesis

Our generated code might have patterns like:

```rust
// Serial (working):
eq_name(n1, n2) <-- ...
// Ascent expands to something that gives us &(Name, Name)

// Parallel (broken):
eq_name(n1, n2) <-- ...
// Ascent expands expecting &&(Name, Name) from c_index_get
```

The parallel iterator from Rayon may wrap values differently than the serial iterator.

---

## Potential Solutions

### Option 1: Adjust Generated Patterns (Preferred)

Detect when generating code for `eqrel` relations and adjust the pattern:

```rust
// In ascent_gen.rs or rewrite_gen.rs
if relation.is_eqrel && is_parallel {
    // Generate pattern with double reference
    quote! { eq_#cat_lower(&#n1, &#n2) }
} else {
    // Normal pattern
    quote! { eq_#cat_lower(#n1, #n2) }
}
```

### Option 2: Add Dereferencing in Generated Code

Wrap the generated patterns to handle both cases:

```rust
// Generate explicit dereferences
eq_name(n1, n2),
let n1 = (*n1).clone(),
let n2 = (*n2).clone()
```

### Option 3: Use Intermediate Variables

Always bind through intermediate variables:

```rust
// Instead of:
pinput_proj(parent, chan, ...) <--
    ...
    eq_name(chan, chan);

// Generate:
pinput_proj(parent, chan, ...) <--
    ...
    eq_name(chan_eq1, chan_eq2),
    if chan == chan_eq1,
    if chan == chan_eq2;
```

### Option 4: Document Limitation (Short-term)

For now, document that parallel execution requires manual adjustments and stick with serial `ascent_run!`.

---

## Action Plan

### Immediate (Today)
1. **Document the issue** (this file) ✅
2. **Confirm the issue** by checking generated code
3. **Choose simplest solution** (likely Option 4 for now)

### Short-term (Next Week)
1. **Investigate exact pattern mismatch** in generated code
2. **Test Option 2** (explicit dereferencing) as it's least invasive
3. **Update code generators** if solution works

### Medium-term (Q1 2026)
1. **Full parallel support** with automatic code generation
2. **Benchmark parallel vs serial** to quantify speedup
3. **Update documentation** with parallel examples

---

## Workaround for Now

**Keep using `ascent_run!` (serial mode)**:

```rust
// In examples/rhocalc.rs and examples/ambient.rs
let mut prog = ascent_run! {
    // NOT ascent_run_par!
    ...
};
```

**Benefits of serial mode:**
- Works correctly with current code generation
- Still fast enough for current test cases
- No code changes needed

**When to revisit parallel:**
- When benchmarking shows serial is too slow
- After implementing deep projection (Phase 7)
- When we have large-scale test cases

---

## Related Files

- `/ascent-byods-rels-0.8.0/src/eqrel_binary.rs` - Macro that switches types
- `/ascent-byods-rels-0.8.0/src/ceqrel_ind.rs` - Parallel eqrel implementation
- `/ascent-byods-rels-0.8.0/src/eqrel_ind.rs` - Serial eqrel implementation
- `mettail-macros/src/ascent_gen.rs` - Our equation generation
- `mettail-macros/src/rewrite_gen.rs` - Our rewrite generation

---

## Summary

**Issue**: `ascent_run_par!` uses `CEqRelIndCommon` (concurrent) instead of `EqRelIndCommon` (serial), which has different iterator types expecting different reference levels.

**Impact**: Cannot use parallel execution without modifying code generation.

**Workaround**: Continue using `ascent_run!` (serial mode).

**Fix**: Need to investigate exact pattern mismatch and adjust code generation to handle both modes.

**Priority**: Low - serial mode is fast enough for current use cases. Revisit in Q1 2026 during performance optimization phase.

