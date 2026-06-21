# Binder Shadowing Fix - Implementation Summary

## Problem

The initial implementation of term generation (both exhaustive and random) had a critical flaw: all binders used the same variable name `"x"`, causing **variable shadowing** in nested scopes.

### What Was Wrong

```rust
// OLD (incorrect):
for(a->x){for(b->x){*x}}
         └─────┘    └─ Which x? Only the innermost!
```

**Issues:**
- Inner binders shadowed outer binders
- Generated terms could only reference the innermost binder
- Bodies of nested binders couldn't use variables from outer scopes
- Poor test coverage of variable binding behavior

## Solution

Use **unique binder names** at each binding depth: `x0`, `x1`, `x2`, ...

### Correct Behavior

```rust
// NEW (correct):
for(a->x0){for(b->x1){*x0|*x1}}
      └──┘     └──┘    └─┘ └─┘
      Depth 0  Depth 1  Can reference both!
```

**Benefits:**
- No shadowing - each binder has unique identity
- Bodies can reference ANY binder in scope
- Much better test coverage for variable binding
- Semantically cleaner

## Implementation

### 1. Random Generation (`random_generation.rs`)

Added `binding_depth` parameter threaded through all recursive calls:

```rust
fn generate_random_at_depth_internal<R: Rng>(
    vars: &[String],
    depth: usize,
    rng: &mut R,
    binding_depth: usize,  // NEW: track nesting level
) -> Self {
    // ...
}
```

**For binder constructors:**
```rust
let binder_name = format!("x{}", binding_depth);
let mut extended_vars = vars.to_vec();
extended_vars.push(binder_name.clone());

let body = Category::generate_random_at_depth_internal(
    &extended_vars,
    depth - 1,
    rng,
    binding_depth + 1  // Increment for nested scope
);

let binder = Binder(get_or_create_var(&binder_name));
let scope = Scope::new(binder, Box::new(body));
```

### 2. Exhaustive Generation (`termgen_gen.rs`)

Extended `GenerationContext` to track initial variable pool size:

```rust
struct GenerationContext {
    vars: Vec<String>,
    initial_var_count: usize,  // NEW: track initial pool size
    max_depth: usize,
    // ... category fields
}
```

**Calculate binding depth:**
```rust
let current_binding_depth = self.vars.len() - self.initial_var_count;
let binder_name = format!("x{}", current_binding_depth);
```

This works because:
- Initial vars = `["a", "b"]` → length 2
- After entering first binder: `["a", "b", "x0"]` → length 3 → depth = 3-2 = 1 → use "x1" (next)
- After entering second binder: `["a", "b", "x0", "x1"]` → length 4 → depth = 4-2 = 2 → use "x2"

**Note:** We use the *next* binder index (equal to current depth) for the name.

### 3. Changes Applied

**Files modified:**
- `macros/src/random_generation.rs`: All binder generation functions
- `macros/src/termgen_gen.rs`: Context struct and all binder generation functions
- `examples/rhocalc.rs`: Updated demo to show unique binder names

## Verification

### Test Output

```
Exhaustive at depth 1 (showing x0):
    for(a->x0){0}
    for(b->x0){0}

Random at depth 10 (showing x0, x1, x2, ...):
  [0] Binders: x0(1) x1(2) x2(2)
      for(@(*a)->x0){*@(for(@(for(b->x1){0})->x1){a!(0)|for(@(@(0)!(0|0))->x2){*x2}})}|a!(0)

  [1] Binders: x0(3) x1(6) x2(2)
      @(a!(0))!(for(@(for(@(a!(0|0|0))->x0){for(@(a!(0))->x1){...}})
```

**Observations:**
- Depth 1 uses `x0` ✓
- Nested binders use `x0`, `x1`, `x2`, ... ✓
- Multiple occurrences of each binder variable show they're being referenced ✓
- No shadowing - all levels accessible ✓

## Impact

### Correctness
- **Before**: Shadowing made nested binders semantically incorrect
- **After**: Full variable binding semantics preserved

### Test Coverage
- **Before**: Only tested innermost binder usage
- **After**: Tests full scope interaction, multiple nesting levels

### Performance
- **No change**: Same algorithmic complexity
- Only adds one integer parameter and `format!` calls

### API
- **No breaking changes**: Public API unchanged
- Internal implementation detail

## Related Documents

- `docs/design/TERM-GENERATION-DESIGN.md` - Original design
- `docs/design/TERM-GENERATION-COMPLETE.md` - Initial implementation
- `docs/design/SORTING-DESIGN.md` - Term ordering foundation

## Future Considerations

1. **Alpha-equivalence**: The `x0`, `x1`, `x2` names are for generation only. The `moniker` crate handles actual binding semantics, so terms like:
   ```rust
   for(a->x0){*x0}  and  for(a->x1){*x1}
   ```
   Are alpha-equivalent (same binding structure).

2. **Pretty-printing**: We could implement a custom display that normalizes binder names back to `x`, `y`, `z` for readability while preserving uniqueness internally.

3. **Parser integration**: The parser should accept any binder name (`x0`, `x1`, etc.) for consistency with generated terms.

## Conclusion

The binder shadowing fix ensures that MeTTaIL's term generation correctly handles variable binding at all nesting levels. By using unique names (`x0`, `x1`, ...) instead of shadowing a single name (`x`), we achieve:

1. ✅ Correct semantics
2. ✅ No shadowing
3. ✅ Full scope accessibility
4. ✅ Better test coverage
5. ✅ No performance cost

This is a foundational fix that ensures the correctness of all downstream uses of generated terms, including testing, rewriting, and analysis.

