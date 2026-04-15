Now I have all the information needed. Let me compose the complete architectural plan.

---

## Design: Cross-Category Infix Pratt Loop Interaction Fix

### 1. Problem Statement (Precise)

When a category `C` (e.g., Bool) is the target of cross-category infix operators (e.g., `NeFloat . a:Float, b:Float |- a "!=" b : Bool`), the dispatch wrapper `parse_C` resolves these operators at the prefix level. The dispatch wrapper parses `left OP right` entirely, then returns `Ok(C::NeFloat(left, right))` directly. This `return Ok(...)` exits the dispatch function, and any subsequent operators in the token stream (e.g., `> y`) are never consumed.

The result: `int(y != 0.5 > y)` fails because after `NeFloat(y, 0.5)` is resolved, the `> y` part remains unconsumed and `int(...)` expects `)`.

### 2. Root Cause

File: `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/dispatch.rs`, lines 449-462 (ambiguous arms) and lines 240-284 (deterministic arms).

The generated dispatch code does:
```rust
Ok(right) => return Ok(Bool::NeFloat(Box::new(left), Box::new(right))),
```

This `return Ok(...)` bypasses the Pratt infix loop. The cross-category result is treated as a complete expression, not as a prefix that should enter the infix loop for further operator consumption.

### 3. Solution: Forced-Prefix Injection into the Own Parser's Infix Loop

**Key insight**: The existing NFA forced-prefix mechanism (`NFA_FORCED_PREFIX_CAT` thread-local) provides exactly the infrastructure needed. It allows injecting a pre-parsed value as the `lhs` of the Pratt loop, skipping the prefix phase entirely.

**The fix**: Instead of `return Ok(cross_result)`, set the forced prefix and call `parse_Cat_own`:

```rust
// BEFORE (bug):
Ok(right) => return Ok(Bool::NeFloat(Box::new(left), Box::new(right))),

// AFTER (fix):
Ok(right) => {
    let cross_result = Bool::NeFloat(Box::new(left), Box::new(right));
    NFA_FORCED_PREFIX_BOOL.with(|c| c.set(Some((cross_result, *pos, 0.0))));
    return parse_Bool_own(tokens, pos, min_bp);
},
```

Inside `parse_Bool_own_impl`, the forced-prefix check (trampoline.rs line 3592-3596) fires:
```rust
if let Some((forced_val, forced_pos, _forced_weight)) = forced {
    *pos = forced_pos;
    break 'prefix forced_val;
}
```

This sets `lhs = cross_result` and enters the Pratt infix loop, which then sees `>` and handles it as `GtBool`.

### 4. Detailed Implementation Steps

#### Step 4.1: Modify `dispatch.rs` — Ambiguous Arms

File: `prattail/src/dispatch.rs`, function `write_category_dispatch`

In the ambiguous arms section (lines 449-462 for single-operator, lines 468-483 for multi-operator), replace every `return Ok(Category::Label(...))` with:

```rust
let __cross_result = Category::Label(Box::new(left), Box::new(right));
NFA_FORCED_PREFIX_{CAT_UPPER}.with(|c| c.set(Some((__cross_result, *pos, 0.0))));
return parse_{category}_own(tokens, pos, min_bp);
```

The `*pos` at the point of injection is already correct (it points past the cross-category expression's RHS).

The weight `0.0` indicates a deterministic forced-prefix injection (no ambiguity penalty).

#### Step 4.2: Modify `dispatch.rs` — Deterministic Arms

File: `prattail/src/dispatch.rs`, function `write_category_dispatch`

In the deterministic arms section (lines 240-284 for single-rule, lines 286-330 for multi-rule), apply the same transformation. Both the G1-committed path (no save/restore) and the defense-in-depth path need the forced-prefix injection.

For the G1-committed path (lines 243-256), replace:
```rust
return Ok(Category::Label(Box::new(left), Box::new(right)));
```
with:
```rust
let __cross_result = Category::Label(Box::new(left), Box::new(right));
NFA_FORCED_PREFIX_{CAT_UPPER}.with(|c| c.set(Some((__cross_result, *pos, 0.0))));
return parse_{category}_own(tokens, pos, min_bp);
```

For the defense-in-depth path (lines 257-283), apply the same to the `Ok(right) =>` arm.

#### Step 4.3: Ensure NFA Forced Prefix Thread-Locals Are Available

File: `prattail/src/trampoline.rs`

The NFA forced prefix thread-locals are already generated for ALL categories (line 3274-3278: "Emitted for ALL categories so parse_preserving_vars can unconditionally drain"). So no new thread-locals need to be added.

However, verify that the dispatch wrapper function has access to the thread-local. Since the dispatch wrapper (`parse_Cat`) and the own parser (`parse_Cat_own`) are generated in the same module, the thread-local `NFA_FORCED_PREFIX_{CAT_UPPER}` is in scope. This should already work.

#### Step 4.4: Verify Non-Interference with Existing Forced Prefix Usage

The forced prefix is currently used ONLY by `parse_preserving_vars` for NFA spillover replay. The Cell-based `take()` semantics guarantee mutual exclusion:
- The dispatch wrapper sets the forced prefix via `c.set(Some(...))`
- The very next call `parse_Cat_own` will `take()` it at the top of the prefix phase
- No intermediate code can race with this (single-threaded, Cell-based)

There is no reentrancy concern because the dispatch wrapper calls `parse_Cat_own` directly (no recursion through `parse_Cat` again).

#### Step 4.5: Handle the Recovery Variant

File: `prattail/src/dispatch.rs`

If the dispatch also generates a recovery variant (`parse_Cat_recovering`), the same transformation must be applied. Check if recovery dispatches use the same cross-category arms.

#### Step 4.6: Add/Update Tests

File: `languages/tests/calculator.rs`

Convert the existing `debug_chained_comparisons` and `debug_int_chained_comparison` from println-based debug tests to proper assertions:

```rust
#[test]
fn test_cross_category_infix_continuation() {
    // Single cross-cat: should work (already works)
    assert!(Int::parse("int(y != 0.5)").is_ok());
    
    // Chained: cross-cat followed by same-cat operator (the bug)
    assert!(Int::parse("int(y != 0.5 > y)").is_ok());
    assert!(Int::parse("int(x != 0.5 > y)").is_ok());
    
    // Double chained
    assert!(Int::parse("int(y != 0.5 > y != 0.5)").is_ok());
    
    // Cross-cat with different source categories
    assert!(Int::parse("int(x != 0.5 and y != 0.5)").is_ok());
    
    // Verify same-cat still works (regression)
    assert!(Int::parse("int(x != true > y)").is_ok());
    
    // Verify the Pratt loop respects binding powers
    let r = Bool::parse("y != 0.5 > y");
    assert!(r.is_ok());
    // Should parse as (y != 0.5) > y since != and > have specific BPs
}
```

### 5. Affected Files

| File | Change | Scope |
|------|--------|-------|
| `prattail/src/dispatch.rs` | Replace `return Ok(cross_result)` with forced-prefix injection + `parse_Cat_own` | ~20 lines changed across 4 code sites |
| `languages/tests/calculator.rs` | Add proper assertion tests for chained cross-category expressions | ~30 lines added |
| `docs/design/exploring/chained_cross_category_comparison_bug.md` | Update status to resolved | Documentation |

### 6. What Does NOT Change

- `prattail/src/trampoline.rs`: No changes. The forced prefix infrastructure already exists.
- `prattail/src/pratt.rs`: No changes. The non-trampoline path generates `parse_Cat_own` with the same structure.
- `prattail/src/binding_power.rs`: No changes. BP tables remain the same.
- `prattail/src/pipeline.rs`: No changes. The pipeline configuration is unaffected.
- `prattail/src/classify.rs`: No changes. Rule classification is unaffected.

### 7. Correctness Argument

**Claim**: After the fix, `int(y != 0.5 > y)` parses correctly.

**Proof trace**:
1. `parse_Int` NFA try-all tries `BoolToInt`, calls `parse_Bool("y != 0.5 > y")`
2. `parse_Bool` dispatch sees `Ident`, enters ambiguous arm for Float source
3. `parse_Float(tokens, pos, 0)` parses `y` as `FVar(y)`, pos at `!=`
4. Peek: `!=` matches. Consumes `!=`. `parse_Float(tokens, pos, 0)` parses `0.5`, pos at `>`
5. **NEW**: Instead of `return Ok(Bool::NeFloat(FVar(y), Float(0.5)))`, sets forced prefix to `NeFloat(FVar(y), Float(0.5))` with pos pointing at `>`, calls `parse_Bool_own(tokens, pos, min_bp=0)`
6. `parse_Bool_own_impl` prefix phase: takes forced prefix, `lhs = NeFloat(FVar(y), Float(0.5))`, `*pos` at `>`
7. Enters Pratt infix loop. Token: `>`. `infix_bp_Bool(>)` returns `Some((l_bp, r_bp))` for `GtBool`. Pushes InfixRHS frame, `continue 'drive`
8. Prefix phase: parses `y` as `BVar(y)`. Infix loop: next token is `)`, not an operator, break
9. Unwind: `lhs = GtBool(NeFloat(FVar(y), Float(0.5)), BVar(y))`. Stack empty, return `Ok(lhs)`
10. Back in dispatch: return value propagates. `parse_Bool` returns `Ok(GtBool(NeFloat(FVar(y), Float(0.5)), BVar(y)))`
11. `BoolToInt` wraps: `BoolToInt(GtBool(NeFloat(FVar(y), Float(0.5)), BVar(y)))`. Pos at `)`. Expects `)`. SUCCESS.

**Binding power correctness**: The forced prefix enters the infix loop with `cur_bp = min_bp`. The cross-category result is treated as a single atomic value at the Bool level. Subsequent Bool operators bind at their declared binding powers, which is correct. `NeBool` and `GtBool` have specific left/right BPs that determine associativity and precedence, and these are preserved.

**No regression for same-category paths**: When `parse_Bool_own` is called normally (without forced prefix), the `take()` returns `None` and the prefix phase proceeds as before. The forced prefix mechanism has zero overhead on the happy path (Cell pointer swap).

### 8. Edge Cases

**Multiple cross-category operators in sequence**: `y != 0.5 > z != 0.5`
- After the first cross-cat resolves NeFloat(y, 0.5) and enters Bool's infix loop, `>` binds as GtBool. The RHS of GtBool is `z != 0.5`. But when parsing the RHS, `parse_Bool` is called again (via the infix loop's `continue 'drive` which calls `parse_Bool` for the RHS). This second call to `parse_Bool` will again dispatch cross-category for `z != 0.5`. It will set forced prefix to NeFloat(z, 0.5) and call `parse_Bool_own`. The infix loop at this level has no more operators, so it returns. The outer infix loop gets the result and builds GtBool. This works correctly.

**Nested cross-category**: `int((x != 0.5) > y)`
- Parentheses are handled by the Pratt prefix handler (grouping). Inside parens, `x != 0.5` is parsed as a standalone Bool expression via `parse_Bool`, which uses the forced-prefix injection to produce NeFloat(x, 0.5). Parens close. Then `> y` is consumed by Bool's infix loop. This works correctly.

**min_bp propagation**: When `parse_Bool` is called with min_bp > 0 (e.g., as an RHS of a higher-precedence operator), the forced prefix injection passes `min_bp` through to `parse_Bool_own`. The Pratt loop's `cur_bp = min_bp` correctly filters out operators with left_bp < min_bp.

### 9. Alternative Approaches Considered and Rejected

**Option B (Change how RHS is parsed)**: Replace `parse_Cat(RHS)` with a dispatch wrapper that tries all categories. This would mean the infix loop of Bool would parse the RHS via the dispatch wrapper, which tries Float first. Problem: this changes the infix loop semantics for ALL operators, not just cross-category ones. It would break same-category operators (NeBool should parse RHS as Bool, not via dispatch). Rejected.

**Option C (Peek at RHS first token before selecting operator)**: Before committing to NeBool in the infix loop, peek at the RHS first token. If it's a Float literal, select NeFloat instead. Problem: requires lookahead analysis at every infix step, and the FIRST sets overlap heavily (Ident is in all categories). Would require full NFA try-all at every infix step. Performance-destructive. Rejected.

**Option D (New type-directed parser automaton)**: Build a register automaton that tracks the type context across the parse. Problem: massive infrastructure investment for what is essentially a codegen routing issue. The forced-prefix injection solves the problem with ~20 lines of changes. Rejected for this specific bug.

**Architecture 2 (Move cross-category dispatch into prefix handler)**: Move the cross-category infix logic into `parse_Bool_own`'s prefix handler. Problem: prefix handlers are inside the trampolined match arms, which use `break 'prefix` control flow. Cross-category dispatch needs save/restore backtracking. Mixing these two control flow patterns inside the prefix phase is complex and error-prone. The dispatch wrapper's match-based structure is better suited for cross-category backtracking. Rejected.

### Critical Files for Implementation
- `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/dispatch.rs` - Core fix: replace `return Ok(cross_result)` with forced-prefix injection in both deterministic and ambiguous arms
- `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/trampoline.rs` - Reference only: understand forced-prefix mechanism (lines 3588-3598) and verify thread-local availability
- `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/languages/tests/calculator.rs` - Add regression tests for chained cross-category infix expressions
- `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/pipeline.rs` - Reference only: verify dispatch category determination and weight map propagation
- `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/languages/src/calculator.rs` - Reference only: grammar definition with cross-category operators (NeFloat, GtFloat, etc.)
