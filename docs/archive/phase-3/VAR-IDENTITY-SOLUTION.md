# Variable Identity Solution for Parsing

## Problem

When parsing terms with `moniker`, every call to `FreeVar::fresh_named("x")` creates a **new unique ID**, even for the same variable name. This causes issues with:

1. **Pattern matching in rewrite rules**: Variables that should be equal (same name) are not equal (different IDs)
2. **Freshness checks**: The `x # Q` condition can't properly check if a variable appears free in a term

### Why Moniker Uses Unique IDs

Moniker uses unique IDs (not names) for variable equality to ensure correct α-equivalence and prevent accidental variable capture. This is the right design for implementing correct name binding.

## Solution: Variable Cache with `get_or_create_var`

We implemented **Option 4** from the analysis: a cached variable constructor that ensures consistent identity within a parsing session.

### Implementation

Added to `runtime/src/lib.rs`:

```rust
/// Get or create a free variable with the given name.
///
/// Within a parsing session, all variables with the same name will share
/// the same unique ID.
pub fn get_or_create_var(name: impl Into<String>) -> FreeVar<String> {
    let name = name.into();
    let mut cache = VAR_CACHE.lock().unwrap();

    cache.entry(name.clone())
        .or_insert_with(|| FreeVar::fresh_named(name))
        .clone()
}

/// Clear the variable cache.
///
/// Call this between independent parsing sessions.
pub fn clear_var_cache() {
    VAR_CACHE.lock().unwrap().clear()
}
```

### Usage Pattern

```rust
fn main() {
    let rdx_str = "for(a<-x){*x|*x}|a!(0)";

    // Clear variable cache before parsing to ensure fresh IDs for this term
    mettail_runtime::clear_var_cache();

    let parser = rhocalc::ProcParser::new();
    let redex = parser.parse(rdx_str).unwrap();

    // Now all occurrences of "x" in the parsed term have the same ID
    // ...
}
```

### How It Works

1. **Within a parse**: First time parsing `"x"` creates a new `FreeVar`. Subsequent parses of `"x"` reuse the same `FreeVar` instance (same unique ID).

2. **Between parses**: Call `clear_var_cache()` so that variables from different terms don't incorrectly share IDs.

3. **Binder integration**: The existing binder code searches the body's free variables for a matching name and reuses its ID - this continues to work correctly.

### Generated Grammar

The LALRPOP generator now produces:

```lalrpop
// Variables use get_or_create_var instead of fresh_named
pub Name: Name = {
    <v:Ident> => Name::NVar(Var::Free(mettail_runtime::get_or_create_var(v)))
};

// Binders also use it as fallback
"for" "(" <f0:Name> "<-" <x_1:Ident> ")" "{" <body_2:Proc> "}" => {
    use mettail_runtime::BoundTerm;
    let free_vars = body_2.free_vars();
    let binder = if let Some(fv) = free_vars.iter().find(|fv| fv.pretty_name.as_deref() == Some(&x_1)) {
        Binder((*fv).clone())
    } else {
        Binder(mettail_runtime::get_or_create_var(x_1))  // Uses cache
    };
    let scope = Scope::new(binder, Box::new(body_2));
    Proc::PInput(Box::new(f0), scope)
}
```

## Benefits

✅ **Correct variable equality**: Same name → same ID within a parse session
✅ **Pattern matching works**: Rewrite rules can match on variable identity
✅ **Freshness checks work**: Can properly check if a variable appears free
✅ **Simple API**: Just call `clear_var_cache()` before each independent parse
✅ **No post-processing**: Variables have correct IDs immediately after parsing
✅ **Backward compatible**: Doesn't break existing moniker functionality

## Best Practices

### ✅ DO

- **Call `clear_var_cache()` before parsing each independent term**
- Use it for interactive REPLs, test cases, or multiple file parsing
- Call it in test cleanup to ensure isolation

### ⚠️ DON'T

- Don't parse multiple independent terms without clearing the cache
- Don't rely on variable IDs being stable across program runs
- Don't use variable IDs for serialization

## Example: Rho Calculus Rewrite

With this solution, the rho calculus rewrite rule now works correctly:

```rust
rewrites {
    if x # Q then (PPar (PInput chan x P) (POutput chan Q))
        => (subst P x (NQuote Q));
}
```

When parsing `"for(a<-x){*x|*x}|a!(0)"`:
- Both occurrences of `x` inside the body get the **same unique ID**
- The binder `a` can properly bind those occurrences
- The freshness check `a # (0)` correctly determines that `a` doesn't appear free in `0`
- The rewrite fires and produces the correct result: `*@(0)|*@(0)`

## Testing

Run the variable identity test:

```bash
cargo run --bin test_var_identity
```

All tests should pass, confirming:
- Same name gets same ID within session
- Different names get different IDs
- Cache tracking works
- Clearing cache creates new IDs
- New session reuses IDs correctly

## Alternative Approaches Considered

We evaluated 4 options:

1. **Variable Environment** during parsing - Not feasible with LALRPOP's limited state support
2. **Post-Processing Pass** - Extra work, delays error detection
3. **Two-Phase Grammar** - Too complex for the benefit
4. **Variable Cache** (implemented) - Simple, fast, correct ✅

The cache approach provides the best balance of simplicity and correctness.

