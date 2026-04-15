# LED Infix Cross-Category Backtracking Fix

## Problem

Cross-category infix operators (`>=`, `==`, `<`, `>`, `<=`, `!=`) fail when the RHS operand type doesn't match the first-tried source category. Example: `Bool::parse("b >= true")` fails even though `GtEqBool . a:Bool, b:Bool |- a ">=" b : Bool` is defined.

The parser commits to `GtEqInt` (first source by weight), tries `parse_Int("true")`, fails, and exits immediately without trying `GtEqBool`.

## Three Bugs

### Bug 1 (Primary): `dispatch.rs` ambiguous arm — `?` commits on RHS failure

**Location**: `prattail/src/dispatch.rs`, lines 432–463.

**Root cause**: The RHS parse uses `?` which propagates errors immediately, never reaching the `*pos = saved` restore at line 466 or trying the next source category.

**Fix**: Replace `?` with `match` that falls through on `Err`:

Single-operator case (lines 435–445):
```rust
// Before:
"let right = parse_{}(tokens, pos, 0)?; \
 return Ok({}::{}(Box::new(left), Box::new(right)));"

// After:
"match parse_{}(tokens, pos, 0) {{ \
    Ok(right) => return Ok({}::{}(Box::new(left), Box::new(right))), \
    Err(_) => {{ }} \
}}"
```

Multi-operator case (lines 449–461): same `?` → `match` replacement.

### Bug 2 (Secondary): `trampoline.rs` LED delegation — pos corruption on failure

**Location**: `prattail/src/trampoline.rs`, lines 4987–5051.

**Root cause**: Delegation advances `pos` (consuming operator token), then `return None` on RHS failure exits with pos corrupted. The mutable reference propagates the corruption to the caller.

**Fix**: Save pos before consuming, restore on failure:

```rust
// Before:
"*pos += 1; \
 match parse_{src}(tokens, pos, r_bp) {{ \
     Ok(rhs) => return Some(...), \
     Err(_) => return None, \
 }}"

// After:
"let saved_led = *pos; \
 *pos += 1; \
 match parse_{src}(tokens, pos, r_bp) {{ \
     Ok(rhs) => return Some(...), \
     Err(_) => {{ *pos = saved_led; return None; }} \
 }}"
```

Three sites: mixfix (lines 4987–5000), same-cat infix (lines 5008–5017), cross-cat ops (lines 5031–5051). For cross-cat ops, fall through instead of `return None` to allow trying subsequent match arms.

### Bug 3 (Tertiary): `dispatch.rs` deterministic arm — same `?` pattern

**Location**: `prattail/src/dispatch.rs`, lines 268 (single-op) and 346 (multi-op).

**Root cause**: Same commit pattern as Bug 1 but for deterministic tokens.

**Fix**: Same `?` → `match` replacement. Exception: G1 committed path (`fallback_dead=true`) should keep `?` — when fallback is provably dead, committing is correct.

## Testing

Add regression tests:
1. `Bool::parse("b >= true")` → succeeds as `GtEqBool(BVar("b"), BoolLit(true))`
2. `Bool::parse("b == true")` → succeeds as `EqBool(BVar("b"), BoolLit(true))`
3. `Int::parse("int(b >= true)")` → succeeds via NFA try-all + fixed LED dispatch
4. LED delegation pos-corruption regression: parse fails cleanly without advancing pos

## Files to Modify

| File | Change |
|------|--------|
| `prattail/src/dispatch.rs` | Bug 1 + 3: `?` → `match` fallthrough at lines 435, 449, 268, 346 |
| `prattail/src/trampoline.rs` | Bug 2: pos save/restore at lines 4987, 5008, 5031 |
| `languages/tests/calculator.rs` | Regression tests for `b >= true`, `b == true` |

## Verification

```
Bool::parse("b >= true")     → OK
Bool::parse("b == true")     → OK
Int::parse("int(b >= true)") → OK
simulate_calculator --cases 200 → 0 parse errors
All 3000+ existing tests pass
```
