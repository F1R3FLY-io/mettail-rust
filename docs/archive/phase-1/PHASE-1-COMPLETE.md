# Phase 1 Complete: Cross-Category Substitution ✅

## Achievement

Successfully implemented **cross-category substitution** for the Rho Calculus, completing Phase 1 of the MeTTaIL project.

## What Was the Problem?

The initial implementation had two fundamental issues:

###  1. Field Ordering
**Problem:** The `PInput` constructor generated fields in the wrong order.

```rust
// Grammar:
PInput . Proc ::= "for" "(" Name <Name> ")" "{" Proc "}" ;
//                          ^^^^  ^^^^^^         ^^^^
//                        chan(0)  bind(1)     body(2)

// Was generating:
PInput(Scope<Binder<String>, Box<Proc>>, Box<Name>)  // ❌ Wrong order

// Now generates:
PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>)   // ✅ Correct order
```

**Fix:** Modified `generate_binder_variant` in `codegen.rs` to preserve grammar order when generating fields.

### 2. Cross-Category Substitution
**Problem:** The generated `substitute` method was category-homogeneous, but Rho Calculus needs heterogeneous substitution.

```rust
// Was generating:
impl Proc {
    fn substitute(&self, var: &FreeVar<String>, replacement: &Proc) -> Proc
    // ❌ Can only substitute Proc for Proc
}

// Needed:
impl Proc {
    fn substitute_name(&self, var: &FreeVar<String>, replacement: &Name) -> Proc
    // ✅ Can substitute Name for Name variables bound in Proc
}
```

**Fix:** Refactored `substitution.rs` to generate multiple substitution methods:
- `substitute(var, replacement)` - same-category substitution
- `substitute_X(var, replacement)` - cross-category substitution for each category X that appears
- Self-referential aliases for uniform recursion

## Solution Architecture

### Code Generation Changes

1. **Field Ordering (`codegen.rs`)**
   - Generate fields in grammar order
   - Track binder and body positions correctly
   - Preserve non-binder fields before and after scope

2. **Category Discovery (`substitution.rs`)**
   - `find_substitutable_categories`: Find all categories that appear (not just binders)
   - Generate methods for each category

3. **Method Generation**
   - `generate_substitute_method`: Main same-category method
   - `generate_cross_category_substitute_method`: Cross-category methods
   - `generate_self_substitute_method`: Self-referential alias

4. **Smart Recursion**
   - Scope arms: Check if binder category matches replacement category
   - Regular arms: Recurse into fields that match replacement category
   - Uses correct method name (`substitute` vs `substitute_X`)

### Key Insight

For cross-category substitution to work, we need:
1. `Proc.substitute_name(var, replacement: &Name)` - for `Proc` terms with `Name` variables
2. `Name.substitute_name(var, replacement: &Name)` - alias for `Name.substitute` (uniform API)
3. Correct determination of which method to call based on field/body categories

## Test Results

### Working Example: Rho Calculus Communication

```rust
// Input: for(x y){*y} | x!(0)
// Expected: *@0 (after substituting @0 for y in *y)

let input = Proc::PInput(
    Box::new(x_name),
    Scope::new(Binder(y), Box::new(Proc::PDrop(Box::new(Name::NVar(Var::Free(y))))))
);

// Extract body and perform cross-category substitution ✅
let result = input_body.substitute_name(&y, &Name::NQuote(Box::new(Proc::PZero)));

// Result: PDrop(NQuote(PZero)) == *@0  ✅
assert_eq!(result, Proc::PDrop(Box::new(Name::NQuote(Box::new(Proc::PZero)))));
```

### Test Output
```
=== Testing Rho Calculus Communication ===

Example 1: for(x y){*y} | x!(0) => *@0
  Before: PPar(PInput(...), POutput(...))
  Binder: Binder(FreeVar { unique_id: UniqueId(2), pretty_name: Some("y") })
  Body before subst: PDrop(NVar(Free(FreeVar { unique_id: UniqueId(2), pretty_name: Some("y") })))
  After:  PDrop(NQuote(PZero))
  ✓ Communication: for(x y){*y} | x!(0) => *@0
```

## Phase 1 Status: COMPLETE ✅

All Phase 1 goals achieved:
- [x] Type-Checking
- [x] Equations of Theory Terms
- [x] Parser Generation (basic)
- [x] Binders & Variables (with `moniker`)
- [x] Substitution (with cross-category support) **← Final goal**
- [x] Rewrite Rules (parsing and validation)
- [x] Substitution in Rewrites (`subst` syntax)
- [x] **Rho Calculus with working communication rule** **← Phase 1 TARGET**

## Next Steps (Phase 2)

With a solid foundation, Phase 2 can focus on:
1. **Full Parser Generation** - Complete LALRPOP-based parsers
2. **Runtime Execution** - Interpreter or JIT compilation
3. **Rewrite Engine** - Apply rewrite rules automatically
4. **Theory Composition** - Parameterization and modules
5. **Advanced Type Features** - Dependent types, refinement types

## Files Modified

### Core Implementation
- `macros/src/codegen.rs` - Fixed field ordering
- `macros/src/substitution.rs` - Cross-category substitution generation

### Tests & Documentation
- `theories/rhocalc.rs` - Updated with working cross-category substitution test
- `docs/PHASE-1-PLAN.md` - Marked complete
- `docs/PHASE-1-COMPLETE.md` - This document

## Conclusion

Phase 1 is **complete**. We have successfully implemented a working system for:
- Defining theories with binders
- Type-checking terms and equations
- Generating capture-avoiding substitution
- **Cross-category substitution for languages like Rho Calculus** ✅

The system correctly handles the fundamental operation needed for process calculi: substituting names into processes across category boundaries, with proper handling of binders and capture avoidance via `moniker`.
