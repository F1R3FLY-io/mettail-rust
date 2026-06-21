# Generic Term Sorting Design

**Status:** Design Document
**Date:** November 4, 2025
**Goal:** Define a simple, correct, and generic method for sorting terms in MeTTaIL theories

---

## Overview

MeTTaIL generates algebraic data types from theory definitions. For applications like exhaustive testing, canonical forms, and deterministic execution, we need a total ordering on terms. This document designs a generic sorting mechanism that respects the structure of terms.

### Key Insight

A signature consists of:
1. **Operations** (constructors) - finite, enumerable, can be sorted by definition order or name
2. **Variables** (strings) - sortable lexicographically

Both admit simple, canonical orderings, which can be lifted to sort entire terms.

---

## Current State

### What We Have

From the code generation in `macros/src/codegen.rs`, MeTTaIL currently generates:

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash, mettail_runtime::BoundTerm)]
pub enum Proc {
    PZero,
    PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>),
    POutput(Box<Name>, Box<Proc>),
    PPar(Box<Proc>, Box<Proc>),
    PDrop(Box<Name>),
}
```

**What's Missing:** `Ord` and `PartialOrd` implementations.

### Dependencies

- `moniker::Var<String>` - used for variables
- `moniker::Binder<String>` - used in scopes
- `moniker::Scope<P, T>` - wrapped in `mettail_runtime::Scope`
- Standard library: `Box<T>`, `String`

**Issue:** The `moniker` crate does not implement `Ord` for `Var`, `Binder`, or its `Scope`. Our wrapper `mettail_runtime::Scope` implements `Hash` but not `Ord`.

---

## Design: Structural Ordering

### Principle

Terms should be ordered **structurally** using a **lexicographic ordering** that respects:
1. Constructor precedence (based on definition order or variant order)
2. Recursive subterm ordering
3. Variable names (lexicographically)

### Strategy

**Three-Level Approach:**

#### Level 1: Constructor Ordering

For each category (enum), variants are ordered by their **discriminant** (definition order):

```rust
// Discriminant ordering (built into Rust enums):
PZero < PInput < POutput < PPar < PDrop
```

This is automatic if we derive `Ord` on enums with all fields implementing `Ord`.

#### Level 2: Field Ordering

For variants with fields, compare fields **left-to-right** (lexicographic tuple ordering):

```rust
PPar(a1, b1) < PPar(a2, b2)  iff  (a1, b1) < (a2, b2)
```

This is also automatic via Rust's derived `Ord`.

#### Level 3: Variable and Scope Ordering

**Variables:**
- `moniker::Var<String>` represents variables
- Variables have internal identities (unique IDs) but also names
- **Decision:** Order variables by their **pretty-printed names** (lexicographic)

**Binders:**
- `moniker::Binder<String>` wraps variables in binding positions
- **Decision:** Order binders by their underlying variable names

**Scopes:**
- `Scope<Binder<String>, Box<T>>` represents binder + body
- **Decision:** Compare scopes **up to alpha-equivalence** by:
  1. Unbind both scopes (freshen variables)
  2. Compare binder names lexicographically
  3. Compare bodies recursively
  4. **Caveat:** This is **not** alpha-equivalence-respecting! We want **canonical** ordering, not equivalence-class representatives.

---

## Implementation Plan

### Phase 1: Add Ord to Scope (Just Like Hash!)

**File:** `runtime/src/lib.rs` (in `scope_wrapper` module)

We already added `Hash` to `Scope`. Let's add `Ord` the same way:

```rust
impl<P, T> PartialOrd for Scope<P, T>
where
    P: Clone + BoundPattern<String>,
    T: Clone + BoundTerm<String>,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<P, T> Ord for Scope<P, T>
where
    P: Clone + BoundPattern<String>,
    T: Clone + BoundTerm<String>,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        // Clone scopes to unbind without consuming
        let (p1, t1) = self.clone().unbind();
        let (p2, t2) = other.clone().unbind();

        // Compare by pretty-printed representation
        // (since Binder doesn't implement Ord directly)
        let p1_str = format!("{:?}", p1);
        let p2_str = format!("{:?}", p2);

        match p1_str.cmp(&p2_str) {
            Ordering::Equal => {
                // Compare bodies by their Debug representation
                let t1_str = format!("{:?}", t1);
                let t2_str = format!("{:?}", t2);
                t1_str.cmp(&t2_str)
            }
            other => other,
        }
    }
}
```

**Note:** Since `Binder<String>` doesn't implement `Ord`, we compare via `Debug` representation. This gives us a consistent, canonical ordering based on the pretty-printed form.

### Phase 2: Handle Var in Generated Code

**Problem:** `moniker::Var<String>` doesn't implement `Ord`

**Current Generation:**
```rust
pub enum Name {
    NQuote(Box<Proc>),
    NVar(Var<String>),  // <-- Var doesn't implement Ord!
}
```

**Solution A (Simplest): Wrapper Type**

Create a transparent wrapper in `runtime`:

```rust
// In runtime/src/lib.rs
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OrdVar(pub Var<String>);

impl PartialOrd for OrdVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by Debug representation (gives us the name)
        format!("{:?}", self.0).cmp(&format!("{:?}", other.0))
    }
}

// Forward BoundTerm implementation
impl BoundTerm<String> for OrdVar {
    fn term_eq(&self, other: &Self) -> bool {
        self.0.term_eq(&other.0)
    }
    // ... forward other methods ...
}
```

Then change code generation to use `OrdVar` instead of `Var`:

```rust
// Generated:
NVar(mettail_runtime::OrdVar)  // Now it's Ord!
```

**Update codegen.rs:**
```rust
// In generate_variant():
if cat.to_string() == "Var" {
    // Use OrdVar wrapper for Ord support
    fields.push(quote! { mettail_runtime::OrdVar });
} else {
    fields.push(quote! { Box<#cat> });
}
```

### Phase 3: Simply Derive Ord!

**File:** `macros/src/codegen.rs`

Change the derive clause:

```rust
// Current:
#[derive(Debug, Clone, PartialEq, Eq, Hash, mettail_runtime::BoundTerm)]

// New:
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, mettail_runtime::BoundTerm)]
```

That's it! No manual implementation generation needed.

**Requirements (All Satisfied):**
- ✓ `Box<T>` implements `Ord` if `T: Ord` (stdlib)
- ✓ `mettail_runtime::Scope` implements `Ord` (Phase 1)
- ✓ `mettail_runtime::OrdVar` implements `Ord` (Phase 2)

The Rust compiler generates the `Ord` implementation automatically using:
1. Constructor discriminant order (definition order)
2. Lexicographic field comparison (left-to-right)

---

## Summary: Why This is Simple

Just like we added `Hash` to `Scope` with a newtype wrapper, we can add `Ord`:

1. ✅ **Scope** - Add `Ord` implementation (follows existing `Hash` pattern)
2. ✅ **OrdVar** - Create wrapper type (follows existing `Scope` wrapper pattern)
3. ✅ **Codegen** - Change `Var` to `OrdVar`, add `Ord` to derive list
4. ✅ **No manual generation** - Rust derives everything automatically!

The only code generation change needed is:
- Replace `mettail_runtime::Var<String>` with `mettail_runtime::OrdVar` in variants
- Add `Ord, PartialOrd` to the derive list

Everything else is just implementing `Ord` for our two wrapper types (`Scope` and `OrdVar`) in the runtime library.

---

## Semantic Considerations

### Not Alpha-Equivalence Respecting

The proposed ordering is **NOT** alpha-equivalence respecting:
- `for(a<-x){a!(0)}` vs `for(b<-x){b!(0)}` will compare differently
- These are alpha-equivalent but not equal under `Ord`

**Rationale:**
- We want a **total order** for **canonical forms**, not equivalence classes
- Alpha-equivalence is already handled by `PartialEq` (via `BoundTerm::term_eq`)
- Sorting is for **enumeration**, not **equality testing**

### Use Cases

**Where Ord is needed:**
1. **Term enumeration** - generating all terms up to size N
2. **Set/Map keys** - using terms in `BTreeSet`, `BTreeMap`
3. **Deterministic iteration** - consistent ordering for testing
4. **Canonical representatives** - choosing one term from equivalence class

**Where Ord is NOT appropriate:**
1. **Semantic equality** - use `PartialEq` (already alpha-equivalence aware)
2. **Rewriting** - use pattern matching and `PartialEq`

---

## Testing Strategy

### Unit Tests

**File:** `macros/tests/ord_generation.rs`

Test cases:
1. Simple terms without binders: `PZero < PDrop(a)`
2. Nested terms: `PPar(PZero, PZero) < PPar(PZero, PDrop(a))`
3. Variables: `NVar(x) < NVar(y)` if `"x" < "y"`
4. Scopes: `for(a<-x){...}` vs `for(b<-x){...}`

### Integration Tests

**File:** `examples/test_term_generation.rs`

1. Generate all terms up to depth 3
2. Sort them
3. Verify ordering is consistent and total
4. Verify no panics or infinite loops

---

## Future Extensions

### Optimizations

1. **Memoization:** Cache unbinding results for large terms
2. **Interning:** Use interned strings for variable names
3. **Custom discriminants:** Allow user to specify constructor ordering

### Advanced Orderings

1. **Size-based:** Sort by term size, then structurally
2. **Weighted:** Assign weights to constructors
3. **Type-directed:** Sort based on inferred types

### Integration with E-graphs

When integrating with e-graph libraries (Phase 4), we may want:
- Canonical representatives from equivalence classes
- Ordering that respects equations (e.g., commutativity)

This requires more sophisticated analysis (rewrite normal forms).

---

## Implementation Checklist

- [ ] **Runtime (Scope):** Add `Ord` impl to `mettail_runtime::Scope` (50 lines, like `Hash`)
- [ ] **Runtime (OrdVar):** Create `OrdVar` wrapper with `Ord` + `BoundTerm` (50 lines)
- [ ] **Codegen:** Change `Var` → `OrdVar` in `generate_variant()` (5 lines)
- [ ] **Codegen:** Add `Ord, PartialOrd` to derive list (1 line)
- [ ] **Tests:** Unit tests for ordering invariants (50 lines)
- [ ] **Tests:** Integration test with term enumeration (100 lines)
- [ ] **Docs:** Update README with sorting example

**Total Effort:** ~250 lines of new code, mostly tests

**No New Modules Required:** All changes in existing files!

---

## Open Questions

1. **Performance:** How expensive is unbinding for `Ord` comparison?
   - **Answer:** Measure with benchmarks; optimize if needed

2. **Consistency:** Should `Ord` be consistent with `Hash`?
   - **Answer:** Not required by Rust, but nice to have
   - Current `Hash` on `Scope` hashes internal fields, not names
   - May need to revise `Hash` implementation

3. **User Control:** Should users specify constructor ordering?
   - **Answer:** Not in Phase 1; use definition order
   - Future: allow `#[sort_priority(N)]` annotations

4. **Moniker Upstream:** Should we contribute `Ord` to `moniker`?
   - **Answer:** Maybe, but our ordering is **intentionally** not alpha-aware
   - Their design philosophy may differ

---

## References

- **Moniker Crate:** https://github.com/brendanzab/moniker
- **Rust Ord Trait:** https://doc.rust-lang.org/std/cmp/trait.Ord.html
- **Rust Derive Macros:** https://doc.rust-lang.org/reference/procedural-macros.html#derive-macros
- **MeTTaIL Docs:**
  - `docs/design/DATA-STRUCTURES-DESIGN.md`
  - `docs/phase-1/PHASE-1-COMPLETE.md`
  - `docs/ROADMAP.md`

---

**Next Steps:** Implement Phase 1 (Scope Ord) and validate with simple tests.

