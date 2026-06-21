# Equation Implementation Plan (REVISED)

**Date**: November 19, 2025 (Updated after review)
**Status**: 🚨 CRITICAL - Equations Not Implemented
**Priority**: HIGH - Semantic Correctness Issue

---

## Problem Statement

### Current Status
**NONE of the 6 ambient calculus equations are being generated.** Even after flipping `P == {P, 0}` to `{P, 0} == P`, it still fails because `PZero` is a **nullary constructor**, not a simple variable.

### Root Cause (Confirmed)

**File**: `macros/src/ascent_gen.rs`, lines 1477-1512

```rust
for (elem_idx, elem) in elements.iter().enumerate() {
    match elem {
        Expr::Var(var) if !is_constructor(var, theory) => {
            // ✅ Simple variable - works
        }
        _ => {
            // ❌ EVERYTHING ELSE - returns None
            // This blocks:
            // - Nullary constructors (PZero)
            // - Non-nullary constructors (PNew, PIn, POut, etc.)
            // - Nested Apply patterns
            // - CollectionPatterns (nested collections)
            return None;
        }
    }
}
```

**The Key Insight**: Rewrite rules use `generate_ascent_pattern()` which **recursively** handles all expression types. Equations use custom logic that only handles simple variables.

**Example Failure**:
```rust
// Equation 0: {P, PZero} == P
elements = [Var(P), Var(PZero)]
// elem 0: P passes (not a constructor)
// elem 1: PZero FAILS (is_constructor returns true!)
```

---

## Design Decisions

### Key Insight: Reuse Rewrite Rule Logic! ✅

**Equations are like rewrites** - they match patterns and construct new terms. The rewrite rule machinery (`generate_ascent_pattern` in `rewrite_gen.rs`) already handles:
- ✅ All expression types (Var, Apply, CollectionPattern, Subst)
- ✅ Nullary constructors (PZero)
- ✅ Non-nullary constructors (PNew, PIn, etc.)
- ✅ Binders (with `unsafe_pattern`/`unsafe_body`)
- ✅ Nested patterns
- ✅ Rest patterns (`...rest`)
- ✅ Duplicate variable handling (equational matching)

**We should adapt `generate_ascent_pattern` for equations, not reinvent the wheel!**

---

### Approach: Adapter Pattern

**Create an equation-specific adapter** that calls the proven rewrite rule pattern matching logic.

**Why Not Use Directly?**
1. **Signature differences**: Equations don't need `duplicate_vars` or `equational_checks` (simpler)
2. **Binding format**: Equations use `HashMap<String, Ident>`, rewrites use `HashMap<String, TokenStream>`
3. **Output format**: Equations need `Vec<TokenStream>` for nested patterns, rewrites add to mutable `clauses`

**The Plan**:
```rust
fn generate_equation_pattern_via_rewrite_logic(
    expr: &Expr,
    term_name: &str,
    bindings: &mut HashMap<String, Ident>,
    theory: &TheoryDef,
    nested_patterns: &mut Vec<TokenStream>,
) -> Option<TokenStream> {
    // 1. Create adapter data structures
    let mut rewrite_bindings: HashMap<String, TokenStream> = HashMap::new();
    let mut variable_categories: HashMap<String, Ident> = HashMap::new();
    let mut clauses: Vec<TokenStream> = Vec::new();
    let duplicate_vars: HashSet<String> = HashSet::new(); // Empty for equations
    let mut equational_checks: Vec<TokenStream> = Vec::new();

    // 2. Call the rewrite logic
    let term_ident = format_ident!("{}", term_name);
    let expected_category = extract_category_from_expr(expr, theory)?;
    generate_ascent_pattern(
        expr, &term_ident, &expected_category, theory,
        &mut rewrite_bindings, &mut variable_categories, &mut clauses,
        &duplicate_vars, &mut equational_checks
    );

    // 3. Convert bindings back to equation format
    for (var_name, token) in rewrite_bindings {
        // Extract Ident from TokenStream (it's just `term.clone()`)
        let var_ident = format_ident!("{}", to_snake_case(&var_name));
        bindings.insert(var_name, var_ident);
    }

    // 4. Return combined pattern
    Some(quote! {
        #(#clauses)*
    })
}
```

---

### Rest Patterns: Free Implementation!

Since we're reusing `generate_ascent_pattern`, **rest patterns work automatically!**

The rewrite logic already handles:
```rust
// Extract specific elements
for (elem_idx, elem_expr) in elements.iter().enumerate() {
    // Recursively handle each element
}

// Handle rest
if let Some(rest_var) = rest {
    clauses.push(quote! {
        let #rest_var = {
            let mut bag = #bag_var.clone();
            #(bag.remove(&#elem_vars);)*
            bag
        },
    });
}
```

**Decision**: Implement rest support from the start (it's free with reuse!)

---

## Implementation Plan

### Phase 1: Adapter Implementation (Week 1, Days 1-3)

#### Task 1.1: Make `generate_ascent_pattern` Public (Day 1, 2 hours)

**File**: `macros/src/rewrite_gen.rs`
**Line**: 183

**Current**:
```rust
pub fn generate_ascent_pattern(...)  // Already public!
```

✅ Already done! This function is public for use in congruence projection generation.

#### Task 1.2: Create Equation Pattern Adapter (Day 1-2, 1 day)

**File**: `macros/src/ascent_gen.rs`
**Location**: New function before `generate_equation_clause`

**Implementation**:
```rust
use crate::rewrite_gen::generate_ascent_pattern;

/// Adapter function: Use rewrite rule pattern matching for equations
/// Converts between equation-style bindings and rewrite-style bindings
fn generate_equation_pattern_via_rewrite_logic(
    expr: &Expr,
    term_name: &str,
    bindings: &mut HashMap<String, Ident>,
    theory: &TheoryDef,
) -> Option<Vec<TokenStream>> {
    // Setup for rewrite pattern matching
    let mut rewrite_bindings: HashMap<String, TokenStream> = HashMap::new();
    let mut variable_categories: HashMap<String, Ident> = HashMap::new();
    let mut clauses: Vec<TokenStream> = Vec::new();
    let duplicate_vars: HashSet<String> = HashSet::new(); // No duplicates in equations
    let mut equational_checks: Vec<TokenStream> = Vec::new();

    // Call rewrite pattern logic
    let term_ident = format_ident!("{}", term_name);
    let expected_category = extract_category_from_expr(expr, theory)?;

    generate_ascent_pattern(
        expr,
        &term_ident,
        &expected_category,
        theory,
        &mut rewrite_bindings,
        &mut variable_categories,
        &mut clauses,
        &duplicate_vars,
        &mut equational_checks,
    );

    // Convert bindings to equation format
    // Rewrite bindings are TokenStream like `term.clone()`
    // Equation bindings are Ident that will be bound in the clauses
    for (var_name, _token) in rewrite_bindings {
        let var_snake = to_snake_case(&var_name);
        let var_ident = format_ident!("{}", var_snake);
        bindings.insert(var_name, var_ident);
    }

    Some(clauses)
}
```

**Helper Needed**:
```rust
/// Convert to snake_case (might already exist)
fn to_snake_case(s: &str) -> String {
    // existing implementation at line ~1290
}
```

#### Task 1.3: Replace Equation Pattern Generation (Day 2-3, 1 day)

**File**: `macros/src/ascent_gen.rs`
**Location**: `generate_equation_clause` function, line ~1175

**Current**:
```rust
let lhs_pattern = generate_equation_pattern(&normalized_left, "p0", &mut bindings, theory, &mut nested_patterns)?;
```

**New**:
```rust
// Use rewrite rule logic for pattern matching!
let lhs_clauses = generate_equation_pattern_via_rewrite_logic(
    &normalized_left,
    "p0",
    &mut bindings,
    theory,
)?;
```

**Update Return**:
```rust
Some(quote! {
    #eq_rel(p0, p1) <--
        #cat_lower(p0),
        #(#lhs_clauses)*  // Use the clauses directly
        #freshness_checks
        let p1 = #rhs_construction;
})
```

**Remove**:
- Old `generate_equation_pattern` function (lines 1321-1521)
- `nested_patterns` parameter (no longer needed)

---

### Phase 2: RHS Construction (Week 1, Days 4-5)

#### Task 2.1: Verify RHS Works with New Bindings

**File**: `macros/src/ascent_gen.rs`
**Location**: `generate_equation_rhs` and `generate_collection_equation_rhs`

**Check**:
1. Variable lookups in `bindings` still work
2. Binder reconstruction with `Scope::from_parts_unsafe` still works
3. Collection construction still works

**Expected**: Should work without changes! The bindings format is the same (HashMap<String, Ident>).

#### Task 2.2: Test RHS with Binders

**Test Equation**:
```rust
{P, (PNew x C)} == (PNew x {P, C})
```

**Verify**:
- LHS binds: `P`, `x` (binder), `C`
- RHS constructs: `PNew(Scope::from_parts_unsafe(x, Box::new(PPar{P, C}))))`

---

### Phase 3: Freshness Conditions (Week 2, Days 1-2)

#### Task 3.1: Verify Freshness Generation

**File**: `macros/src/ascent_gen.rs`
**Location**: `generate_equation_freshness`, line ~1207

**Check**:
```rust
if x # N then (PNew x {P, (PIn N P)}) == {P, (PIn N (PNew x P))}
```

**Verify**:
- Freshness condition parsed: `x # N`
- Variables bound correctly: `x` (binder), `N` (name)
- Check generated: `if !contains_free(&n, &x),`

**Implementation**:
```rust
fn generate_equation_freshness(
    conditions: &[FreshnessCondition],
    bindings: &HashMap<String, Ident>
) -> TokenStream {
    let mut checks = Vec::new();

    for condition in conditions {
        let var_ident = bindings.get(&condition.variable)
            .expect(&format!("Freshness variable {} not bound", condition.variable));
        let term_ident = bindings.get(&condition.term)
            .expect(&format!("Freshness term {} not bound", condition.term));

        checks.push(quote! {
            if !mettail_runtime::contains_free(&#term_ident, &#var_ident),
        });
    }

    quote! { #(#checks)* }
}
```

**Note**: May need to add `contains_free` to `mettail_runtime` or generate inline check.

---

### Phase 4: Testing & Validation (Week 2, Days 3-5)

#### Task 4.1: Add Equation-Specific Tests

**File**: New `examples/equation_tests.rs`

**Test Structure**:
```rust
use mettail_examples::ambient::*;

#[test]
fn test_zero_identity() {
    let parser = AmbientParser::new();

    // Parse both sides
    let p = parser.parse_proc("a[0]").unwrap();
    let p_with_zero_left = parser.parse_proc("{a[0], 0}").unwrap();
    let p_with_zero_right = parser.parse_proc("{0, a[0]}").unwrap();

    // Run Ascent
    let mut prog = amb_source();
    prog.proc.insert((p.clone(),));
    prog.proc.insert((p_with_zero_left.clone(),));
    prog.proc.insert((p_with_zero_right.clone(),));
    prog.run();

    // Check equivalence
    assert!(
        prog.eq_proc.contains(&(p.clone(), p_with_zero_left.clone()))
        || prog.eq_proc.contains(&(p_with_zero_left.clone(), p.clone())),
        "Zero identity: {{P, 0}} should equal P"
    );

    assert!(
        prog.eq_proc.contains(&(p.clone(), p_with_zero_right.clone()))
        || prog.eq_proc.contains(&(p_with_zero_right.clone(), p.clone())),
        "Zero identity: {{0, P}} should equal P (order independence)"
    );
}

#[test]
fn test_new_extrusion_collection() {
    let parser = AmbientParser::new();

    // Test: {a[0], new(x, b[x])} == new(x, {a[0], b[x]})
    let lhs = parser.parse_proc("{a[0], new(x, b[x])}").unwrap();
    let rhs = parser.parse_proc("new(x, {a[0], b[x]})").unwrap();

    let mut prog = amb_source();
    prog.proc.insert((lhs.clone(),));
    prog.proc.insert((rhs.clone(),));
    prog.run();

    assert!(
        prog.eq_proc.contains(&(lhs.clone(), rhs.clone()))
        || prog.eq_proc.contains(&(rhs.clone(), lhs.clone())),
        "New extrusion should work when x not free in a[0]"
    );
}

#[test]
fn test_new_extrusion_in() {
    // Test: new(x, {P, in(N, P)}) == {P, in(N, new(x, P))} when x not free in N
    // ... similar structure
}

// More tests for each equation...
```

#### Task 4.2: Verify Generated Code

**Manual Check**:
```bash
cd /Users/cbwells/Documents/GitHub/mettail-rust
cargo build --bin ambient 2>&1 | grep -A 30 "GENERATING EQUATION"
```

**Expected Output**:
```
=== GENERATING EQUATION CLAUSES ===
Total equations to process: 6

Equation 0: (PPar {P, PZero}) == P
  ✅ Generated successfully

Equation 1: (PPar {P, (PNew x C)}) == (PNew x (PPar {P, C}))
  ✅ Generated successfully

... (all 6 should pass)
```

**Check Generated Ascent Code** (example for Equation 0):
```rust
eq_proc(p0, p1) <--
    proc(p0),
    if let Proc::PPar(ref bag) = p0,
    if bag.len() >= 2,
    for (elem_0, _count_0) in bag.iter(),
    let p = elem_0.clone(),
    for (elem_1, _count_1) in bag.iter(),
    if &elem_1 != &elem_0,
    if let Proc::PZero = elem_1,  // Nullary constructor match!
    let p1 = p.clone();
```

#### Task 4.3: Comprehensive Test Suite

**Coverage**:
- ✅ Zero identity (both orders)
- ✅ All 5 scope extrusion equations
- ✅ Freshness condition enforcement
- ✅ Freshness condition violations (should not fire)
- ✅ Order independence in collections
- ✅ Transitivity via eqrel

**Run**:
```bash
cargo test --bin equation_tests
```

---

## Success Criteria

### Phase 1 Complete
- ✅ All 6 ambient equations generate without errors
- ✅ Build succeeds
- ✅ Generated Ascent code is syntactically correct
- ✅ Pattern matching handles all expression types

### Phase 2 Complete
- ✅ RHS construction works for all equation types
- ✅ Binders reconstructed correctly
- ✅ Collections built correctly

### Phase 3 Complete
- ✅ Freshness conditions generate correct checks
- ✅ Equations with conditions only fire when met
- ✅ Equations blocked when freshness violated

### Phase 4 Complete
- ✅ 10+ equation-specific tests pass
- ✅ Verify `{P, 0}` ≡ `P` via equivalence relation
- ✅ Verify scope extrusion works correctly
- ✅ No false equivalences (soundness)
- ✅ Order independence verified

---

## Risk Assessment

### Low Risk ✅
- **Reusing proven code**: `generate_ascent_pattern` already works for rewrites
- **Adapter pattern**: Clean separation, minimal changes
- **Rest patterns**: Free with reuse

### Medium Risk
- **Binding format conversion**: Need to ensure adapter works correctly
- **Freshness conditions**: May need runtime support

### Minimal Changes
- **No changes to rewrite logic**: Zero risk to existing functionality
- **Only changes to equation generation**: Isolated impact

---

## Timeline (Revised)

- **Week 1**:
  - Days 1-3: Adapter implementation
  - Days 4-5: RHS verification
- **Week 2**:
  - Days 1-2: Freshness conditions
  - Days 3-5: Comprehensive testing

**Total**: 2 weeks, but **simpler than original plan!**

---

## Why This Approach is Better

1. **Reuse Proven Code**: `generate_ascent_pattern` handles 100% of cases already
2. **No Duplication**: Don't reinvent pattern matching
3. **Rest Patterns Free**: Already implemented
4. **Lower Risk**: Minimal new code
5. **Easier to Maintain**: One source of truth for pattern matching
6. **Future-Proof**: Any improvements to rewrite patterns benefit equations

---

## Implementation Notes

### Key Files
- `macros/src/rewrite_gen.rs` - Source of truth for pattern matching (already public!)
- `macros/src/ascent_gen.rs` - Add adapter, update equation generation

### Testing Strategy
- Unit tests for adapter
- Integration tests for all 6 equations
- Property tests for order independence

---

**Priority**: Start Phase 1 immediately - this is now a **simpler, lower-risk** fix than originally planned!
