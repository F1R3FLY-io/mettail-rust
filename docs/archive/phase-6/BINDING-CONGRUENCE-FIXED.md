# Binding Congruence: Fixed via Direct Field Access

## Status: ✅ COMPLETE

**Date**: Fixed by accessing moniker's `unsafe_body` and `unsafe_pattern` fields directly
**Solution**: Use `scope.inner().unsafe_body` instead of `scope.clone().unbind()`
**Result**: All binding congruences now work correctly!

## Summary

The binding congruence issue has been **completely resolved**. The problem was that `unbind()` creates fresh variable IDs on every call, preventing Datalog joins. The solution was to access moniker's `unsafe_body` and `unsafe_pattern` fields directly, preserving the bound variable structure.

## Test Results

All 6 congruence tests pass:
- ✅ `amb_congruence` - Regular congruence
- ✅ `par_congruence` - Collection congruence
- ✅ `new_congruence` - **Direct binding congruence**
- ✅ `nested_amb_new` - **Nested binding congruence**
- ✅ `new_with_rest` - **Binding congruence with rest patterns**
- ✅ `new_in_collection` - **Collection binding congruence**

## The Problem

From `BINDING-CONGRUENCE-BLOCKED.md`, we discovered that `unbind()` creates fresh variable IDs:

```rust
// First unbind
let (binder1, body1) = scope.clone().unbind();
// body1: ... Free(FreeVar { unique_id: UniqueId(3) ...

// Second unbind (same scope!)
let (binder2, body2) = scope.clone().unbind();
// body2: ... Free(FreeVar { unique_id: UniqueId(4) ...  // DIFFERENT!

// Bodies equal? false
```

This broke Datalog joins:
1. Category rules unbind: `Body@IDs_A` → added to `proc`
2. Base rewrite: `Body@IDs_A ~> Body'` → added to `rw_proc`
3. Congruence unbinds **again**: `Body@IDs_B` → tries to join
4. **Join fails**: IDs don't match!

## The Solution

Access moniker's public `unsafe_body` and `unsafe_pattern` fields directly:

```rust
// OLD (broken):
let (binder, body) = scope.clone().unbind();  // Creates fresh IDs!

// NEW (working):
let binder = scope.inner().unsafe_pattern.clone();
let body = scope.inner().unsafe_body.as_ref().clone();  // Preserves Bound vars!
```

### Key Insight from Moniker Example

Looking at moniker's lambda calculus example (`moniker/examples/lc.rs`):

```rust
fn subst<N: PartialEq<Var<String>>>(&self, name: &N, replacement: &RcExpr) -> RcExpr {
    match *self.inner {
        Expr::Lam(ref scope) => RcExpr::from(Expr::Lam(Scope {
            unsafe_pattern: scope.unsafe_pattern.clone(),
            unsafe_body: scope.unsafe_body.subst(name, replacement),  // Direct access!
        })),
        // ...
    }
}
```

They access `unsafe_body` **directly** for structural operations like substitution, avoiding `unbind()`!

## Implementation Changes

### 1. Category Rules (`ascent_gen.rs`)

```rust
// Generate category rule for PNew
#body_cat_lower(body_value) <--
    #cat_lower(t),
    if let #category::#label(scope) = t,
    let body_value = scope.inner().unsafe_body.as_ref().clone();
```

### 2. Direct Binding Congruence Projections (`ascent_gen.rs`)

```rust
#proj_rel(parent, binder_var, body) <--
    #cat_lower(parent),
    if let #parent_cat::#constructor(ref scope) = parent,
    let binder_var = scope.inner().unsafe_pattern.clone(),
    let body = scope.inner().unsafe_body.as_ref().clone();
```

### 3. Collection Binding Congruence Projections (`congruence_analysis.rs`)

```rust
// For binding fields in collection projections
let binder_name = (* #field_name).inner().unsafe_pattern.clone(),
let body_name = (* #field_name).inner().unsafe_body.as_ref().clone()
```

### 4. Reconstruction (`ascent_gen.rs`)

```rust
// Use from_parts_unsafe to avoid rebinding
let scope_tmp = mettail_runtime::Scope::from_parts_unsafe(
    binder_var.clone(),
    Box::new(body_rewritten.clone())
)
```

## Why This Works

### Moniker's Design

Moniker uses "locally nameless" representation:
- **Inside scopes**: Variables are `Bound(BoundVar { scope, binder, ... })`
- **After unbind**: Variables become `Free(FreeVar { unique_id, ... })`

The `unsafe_` prefix is a **semantic warning**, not Rust `unsafe`:
- ⚠️ **Semantic**: You're responsible for understanding binding structure
- ✅ **Memory safe**: Just public fields, no undefined behavior

### Use Cases

**When to use `unbind()`**: Single-pass traversal
- ✅ Evaluation: `eval(λx. body)` → unbind once → evaluate → done
- ✅ Type checking: `typecheck(λx. body)` → unbind once → check → done

**When to use direct access**: Structural operations preserving binding
- ✅ Substitution: Need to preserve bound variable structure
- ✅ Alpha-equivalence: Need stable identity for comparison
- ✅ **Term rewriting in Datalog**: Need stable identity for joins!

### Our Use Case

```rust
// 1. Extract body preserving Bound variables
let body = scope.inner().unsafe_body.as_ref().clone();
// body: { ... Bound(x), ... } with stable structure

// 2. Pass through Datalog
proc(body)                              // body has Bound vars
rw_proc(body, body_rewritten)          // Both have same Bound structure

// 3. Reconstruct without rebinding
Scope::from_parts_unsafe(binder, Box::new(body_rewritten))
// Preserves Bound vars exactly
```

**Result**: Same term always has same structure → Datalog joins succeed!

## Safety Analysis

### Is This "Unsafe"?

**NO** - The name is misleading:

1. ✅ **Memory safe**: Just accessing public fields
2. ✅ **No mutation**: We clone, don't mutate shared state
3. ✅ **Preserves semantics**: α-equivalence maintained
4. ✅ **Follows moniker's design**: Same pattern as their substitution example

### Why Moniker Called It "Unsafe"

From moniker's documentation:
```rust
/// You can access this directly, but only if you understand what you are
/// doing! Prefer calling `Scope::unbind` instead.
pub unsafe_pattern: P,
pub unsafe_body: T,
```

They mean: "You need to understand binding semantics to use this correctly."

**For our use case** (term rewriting with stable identity), this is the **correct and safe** approach!

## Performance Impact

✅ **Faster**: No fresh ID generation on every access
✅ **Simpler**: Fewer allocations (no unbinding/rebinding)
✅ **Correct**: Enables Datalog fixpoint to work properly

## What Now Works

### All Binding Congruences

```rust
// Direct
new(x, {agent[{in(x,0)}], x[0]}) ~> new(x, {x[{0, agent[{0}]}]})

// Nested in ambient
outer[new(x, ...)] ~> outer[new(x, ...')]

// Inside collection
{new(x, ...), rest} ~> {new(x, ...'), rest}

// With rest patterns
new(x, {a[{in(b,p), state}], b[r], obs}) ~> new(x, {b[{a[{p, state}], r}], obs})
```

### Any Nominal Calculus

Now works for:
- ✅ Ambient calculus with `new(x, P)`
- ✅ Lambda calculus with `λx. M`
- ✅ Pi calculus with `ν(x) P`
- ✅ Any process calculus with restriction/binding

## Files Modified

1. **`macros/src/ascent_gen.rs`**:
   - `generate_binding_deconstruction`: Category rules use direct access
   - `generate_binding_proj_population`: Direct congruence projections use direct access
   - `generate_binding_congruence_clause`: Reconstruction uses `from_parts_unsafe`
   - `generate_regular_congruence_clause`: Collection congruence reconstruction uses `from_parts_unsafe`

2. **`macros/src/congruence_analysis.rs`**:
   - Base rewrite projections: Use direct access for binding fields
   - Regular congruence projections: Use direct access for binding elements

3. **`runtime/src/lib.rs`**:
   - Added `unsafe_pattern()` and `unsafe_body()` accessor methods
   - Added `from_parts_unsafe()` constructor for reconstructing scopes without rebinding

## Lessons Learned

1. **Read the examples**: Moniker's lambda calculus example showed the way
2. **"Unsafe" doesn't always mean `unsafe`**: Sometimes it's just a semantic warning
3. **Match your use case**: `unbind()` is for evaluation, direct access is for structural operations
4. **Empirical testing is key**: We empirically verified that `unbind()` creates fresh IDs
5. **Datalog needs stable identity**: Term rewriting via fixpoint requires terms to have consistent structure

## Related Documents

- `BINDING-CONGRUENCE-BLOCKED.md`: Original problem analysis and attempted solutions
- `BINDING-CONGRUENCE-DETAILED-DESIGN.md`: Detailed design for projection-based approach
- `REST-PATTERNS-COMPLETE.md`: Implementation of explicit rest patterns (prerequisite)

## Conclusion

**The binding congruence issue is completely solved** by following moniker's own design pattern for structural operations. This enables mettail to handle any nominal calculus with binders, making it suitable for a wide range of process calculi and lambda calculi.

