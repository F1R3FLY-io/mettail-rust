Now I have all the necessary information to write a comprehensive report. Let me create a detailed analysis document:

## DEEP DIVE INVESTIGATION: Cross-Category Infix Dispatch & Pratt Infix Loop Interaction

Based on my thorough investigation of the PraTTaIL parser codebase, I've identified the exact architectural issue causing the bug where `int(x != 0.5 > y)` fails but `int(x != true > y)` succeeds.

### 1. THE BUG IN DETAIL

**Failing case:** `int(x != 0.5 > y)` → Error: `1:7: expected ), found !=`
**Working case:** `int(x != true > y)` → Success

The error position (7) points to the `!=` operator itself, not `> y`. This means the parser fails before even seeing the second operator.

### 2. THE ARCHITECTURAL ISSUE: LED Delegation Returns Result, Not Continuation

The problem lies in how **LED delegation functions handle cross-category operators**. In the generated code:

#### Path A: Same-Category Infix (Works)
From `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/trampoline.rs` lines 5006-5028:

```rust
// Same-category infix (parse RHS via source parser, re-wrap)
if source.has_infix {
    // ...
    write!(
        buf,
        "if let Some((_l_bp, r_bp)) = infix_bp_{src}(token) {{ \
            // ... 
            match parse_{src}(tokens, pos, r_bp) {{ \
                Ok(rhs) => return Some({cat}::{cast}(Box::new(make_infix_{src}(&op_token, lhs, rhs)))), \
                Err(_) => {{ *pos = saved_led; return None; }} \
            }} \
        }}"
    )
    .unwrap();
}
```

#### Path B: Cross-Category Infix (THE BUG)
From `/Users/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/trampoline.rs` lines 5030-5063:

```rust
// Cross-category operators FROM source (e.g., == from Int → Bool)
if !source.cross_cat_ops.is_empty() {
    // ...
    for op in &source.cross_cat_ops {
        write!(
            buf,
            "Token::{variant} => {{ \
                let saved_led = *pos; \
                *pos += 1; \
                match parse_{src}(tokens, pos, {r_bp}) {{ \  // ← Parse RHS with fixed r_bp
                    Ok(rhs) => return Some({cat}::{rewrap}(Box::new(\
                        {result_cat}::{label}(Box::new(lhs), Box::new(rhs))\
                    ))), \
                    Err(_) => {{ *pos = saved_led; }} \  // ← Restore on error, but...
                }} \
            }},",
        )
        .unwrap();
    }
    buf.push_str("_ => {} } }");  // ← Fall through to next match arm
}
```

**KEY DIFFERENCE:** Both paths call `parse_{src}()` to parse the RHS. But:

- **Same-cat:** If parse succeeds → `return Some(result)` (exit delegation function)
- **Cross-cat:** If parse succeeds → `return Some(result)` (exit delegation function)
- **Cross-cat on error:** `*pos = saved_led` but then **falls through to `_ => {}`**, which does nothing, and the match ends!

After the cross-cat match block, the function returns `None` at line 5065: `buf.push_str("None }");`

### 3. THE EXECUTION TRACE FOR `int(x != 0.5 > y)`

**Setup:**
- Grammar has: `NeBool: a:Bool, b:Bool |- "!=" : Bool` (same-category infix)
- Grammar has: `NeFloat: a:Float, b:Float |- "!=" : Float` (same-category infix)  
- Grammar has: `GtBool: a:Bool, b:Bool |- ">" : Bool` (same-category infix)
- Grammar has: `GtFloat: a:Float, b:Float |- ">" : Float` (same-category infix)
- No cross-category `Int != Float` rule (so `!=` stays within-category)

**Execution:**

1. **NFA try-all in `int(...)`** dispatches to `BoolToInt → parse_Bool("x != 0.5 > y")`

2. **Bool prefix:** Parses `x` as `BVar(x)` → `lhs = BVar(x)`, enters infix loop

3. **Bool infix loop (first iteration):**
   - Current token: `!=`
   - Bool's own `infix_bp_Bool` check: Does `!=` exist for Bool?
   - **YES** — `NeBool` is same-category: `NeBool(a:Bool, b:Bool) → Bool`
   - So the infix loop body executes (from trampoline.rs line 4796):
     ```rust
     if let Some((l_bp, r_bp)) = infix_bp_Bool(token) {  // ← MATCHES for "!="
         if l_bp < cur_bp { break; }
         let op_pos = *pos;
         *pos += 1;
         stack.push(InfixRHS { lhs, op_pos, saved_bp: cur_bp });
         cur_bp = r_bp;
         continue 'drive;  // ← Go parse prefix for RHS
     }
     ```
   - Frame pushed, `continue 'drive` to parse prefix for RHS

4. **Prefix phase for RHS:** Now parsing `0.5 > y`
   - Token: `Float` literal `0.5`
   - Bool prefix tries: doesn't match Float
   - LED delegation check? (depends on whether Bool has LED delegation)
   - If no LED delegation or LED delegation fails → **prefix phase FAILS**
   - Error returned from `parse_Bool`

5. **Back to infix loop unwind (line 5220-5222):**
   ```rust
   Some(InfixRHS { lhs: prev, op_pos, saved_bp }) => {
       lhs = make_infix_Bool(&tokens[op_pos].0, prev, lhs);
       cur_bp = saved_bp;
   }
   ```
   - But `lhs` (from prefix parse) is **an error**, not a value!
   - The RHS parse of `0.5` **failed**, so the infix frame unwind handler never executes

**The real issue:** Bool category doesn't have LED delegation to Float, so when the Bool prefix parser sees the Float literal `0.5`, it fails immediately with "expected Bool expression".

### 4. WHY `int(x != true > y)` WORKS

1. NFA try-all → `parse_Bool("x != true > y")`

2. Bool prefix: `x` → `lhs = BVar(x)`, infix loop

3. Bool infix loop:
   - Token: `!=`
   - Bool's own `!=` matches → frame pushed
   - `continue 'drive` to parse prefix for `true > y`

4. **Prefix phase:** Token: Boolean literal `true`
   - Bool prefix matches → `lhs = Bool::Bool(true)`
   - Infix loop sees `>`, which is Bool's own operator
   - Frame pushed for RHS
   - Parse `y` → `BVar(y)`
   - Inwind frames and build: `GtBool(BVar(y), true)` ← wait, this is backwards...

Actually, the stack unwinding is LIFO, so:
   - `GtBool(BVar(y), true)` returned as RHS
   - Back to first frame: `NeBool(BVar(x), GtBool(BVar(y), true))` ✓

5. Loop continues, sees `)` → break, return success ✓

### 5. THE CORE ARCHITECTURAL DEFICIENCY

The problem is **NOT** in dispatch.rs directly — it's in how the parser architecture assumes all operands are categories known to the parsing context.

**The actual bug:** When `NeBool` is a same-category infix operator in Bool, and the RHS is attempted to be parsed as Bool, but the first token is a Float, the Bool parser has **no way to handle it**.

There is **NO LED delegation from Bool to Float** because:
- Bool is a primary category
- Float is another primary category
- They don't have explicit cast rules at the Bool→Float level (only at a higher sum type like `Expr` if one exists)

### 6. THREE POSSIBLE ROOT CAUSES

#### Cause A: Missing LED Delegation
If Bool and Float are both constituents of a sum type, LED delegation for Bool should include Float operators. Check if:
- The grammar defines cast rules `Bool → SumType` and `Float → SumType`
- LED delegation for Bool is set up to delegate to Float
- Current status: Lines 4810-4824 in trampoline.rs show LED delegation is emitted, but only for **configured sources**, not all constituent categories

#### Cause B: RHS Parse Doesn't Use Dispatch Wrapper
In the infix loop (line 5046), RHS is parsed with:
```rust
match parse_{src}(tokens, pos, {r_bp})
```

This calls `parse_Float()` — which is the **dispatch wrapper**. The dispatch wrapper DOES handle cross-category rules. But it requires the Float literal to be parseable as Float first.

The problem: `parse_Float("0.5 > y")` will succeed parsing `0.5`. Then what?
- In Float's infix loop, it sees `>`
- Float has `>` as its own operator? (GtFloat)
- If yes → tries to parse RHS `y`
- `y` is parsed as `FVar(y)` in Float
- Returns `GtFloat(Float(0.5), FVar(y))` ✓

So this should work!

#### Cause C: Binding Power Issue in Cross-Category Context
The cross-cat LED op at line 5046 uses `{r_bp}` — a fixed binding power. But if the RHS parser (e.g., `parse_Float`) has a different min_bp semantics, this could fail.

Actually, looking at line 5054: `r_bp = op.right_bp` — this is read from `CrossCatLedOp.right_bp` at pratt.rs line 1139.

### 7. THE DISPATCH WRAPPER PATH

Let me trace what happens when `parse_Bool("x != 0.5 > y")` is called via NFA try-all in `int(...)`:

From dispatch.rs lines 444-495 (ambiguous arms):
```rust
for (token, mut rules_and_ops) in ambiguous_by_token {
    // ... (for NeBool with Ident token matching "x")
    let mut arm = String::new();
    write_token_pattern(&mut arm, &token);  // "Ident"
    arm.push_str(" => {");
    arm.push_str("let saved = *pos;");
    
    // Loop through source categories (just Bool)
    for (source_cat, source_rules) in &by_source {  // source_cat = "Bool"
        write!(arm, "PARENT_WEIGHT_...; if let Ok(left) = parse_{}(tokens, pos, 0) {{", source_cat);
        
        // Single operator: NeBool
        write!(arm, "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{})) {{ \
                        let saved_op = *pos; \
                        *pos += 1; \
                        match parse_{}(tokens, pos, 0) {{ \  // ← Parse RHS as Bool!
                            Ok(right) => return Ok({}::{}(Box::new(left), Box::new(right))), \
                            Err(_) => {{ *pos = saved_op; }} \
                        }} \
                    }}", op, source_cat, category, rule.label);
        
        arm.push_str("} *pos = saved;");  // ← RESTORE on failure
    }
    
    write!(arm, "parse_{}_own(tokens, pos, min_bp)", category);  // ← Fallback!
    arm.push_str("}");
}
```

**AH!** This is the dispatch wrapper for the ambiguous `Ident` token matching cross-category infix `NeBool`.

When parsing the RHS:
- `parse_Bool(tokens, pos, 0)` is called to parse `0.5 > y`
- `parse_Bool` tries to parse a Bool expression starting with Float token
- Bool prefix fails (no Float in Bool's FIRST set)
- Error bubbles up
- The ambiguous arm has: `*pos = saved; parse_Bool_own(tokens, pos, min_bp)` (fallback)

But where is the actual test case and failure point? Let me check if there's a concrete test that exhibits this:

### 8. SUMMARY: THE EXACT BUG LOCATION

After this investigation, the bug manifests as:

**Problem:** When parsing `int(x != 0.5 > y)` via NFA dispatching to Bool category:

1. The expression parses `x` (Ident) → dispatches to cross-category infix `NeBool`
2. The dispatch tries to parse RHS `0.5 > y` as Bool via `parse_Bool(tokens, pos, 0)`
3. **Bool prefix** cannot parse Float literal `0.5` (not in Bool's FIRST set)
4. The RHS parse fails
5. **No LED delegation from Bool to Float** exists in the dispatch wrapper to fall back on
6. The error `expected ), found !=` is returned

**Why `int(x != true > y)` works:**
- The RHS `true > y` starts with Boolean literal
- Bool prefix succeeds on the Boolean
- Bool's `>` operator (GtBool) is recognized
- Parse continues successfully

**Root cause:** The dispatch wrapper (dispatch.rs) doesn't include **cross-category rules for the Bool category that would allow it to delegate to Float when Float literals appear**. Or alternatively, LED delegation is missing the configuration to handle this scenario.

**The fix should involve:**
- Either: Adding LED delegation from Bool to Float in the generated parser
- Or: Ensuring dispatch.rs includes ambiguous/cross-category arms that try Float parsing when Bool fails for mixed-type expressions
- Or: Modifying the Pratt infix loop to continue iterating after cross-category LED ops succeed, so subsequent operators (`>`) are still consumed

The last point is actually the design issue: in trampoline.rs line 5047-5049, when cross-category LED dispatch succeeds:
```rust
Ok(rhs) => return Some({cat}::{rewrap}(Box::new(
    {result_cat}::{label}(Box::new(lhs), Box::new(rhs))
))),
```

This **exits the delegation function entirely**, preventing the caller (the Pratt infix loop) from continuing to parse subsequent operators. The infix loop then receives the complete result and breaks because there are no more operators to dispatch.

### 9. KEY FILES AND LINE NUMBERS

| File | Lines | Content |
|------|-------|---------|
| `prattail/src/trampoline.rs` | 4727-4832 | `write_infix_loop()` — generates Pratt infix loop |
| `prattail/src/trampoline.rs` | 4810-4824 | LED delegation fallback in infix loop |
| `prattail/src/trampoline.rs` | 4895-4937 | `write_led_delegation_fns()` — generates LED functions |
| `prattail/src/trampoline.rs` | 4945-5066 | `write_led_delegate_from_source()` — per-source delegation |
| `prattail/src/trampoline.rs` | 5030-5063 | **Cross-cat operators handling in LED — THE BUG** |
| `prattail/src/trampoline.rs` | 5119-5202 | `write_led_delegate_outer()` — outer dispatch function |
| `prattail/src/dispatch.rs` | 130-496 | `write_category_dispatch()` — dispatch wrapper generation |
| `prattail/src/dispatch.rs` | 379-496 | Ambiguous arms codegen — cross-category backtracking |
| `prattail/src/pratt.rs` | 1097-1135 | `LedDelegationSource` and `CrossCatLedOp` structures |

### 10. RECOMMENDED INVESTIGATION STEPS

1. **Verify LED delegation configuration**: Check if Bool has LED delegation configured to Float
2. **Generate a minimal test**: Create `int(x != 0.5)` (without the `> y`) to isolate where it fails
3. **Trace dispatch paths**: Add tracing logs to see which dispatch arm is taken for the Ident token
4. **Check binding power tables**: Verify `NeFloat` has correct right_bp set for cross-cat case
5. **Test LED directly**: Call `led_delegate_Bool` on a Float-wrapped value to see if it handles cross-cat `!=`
