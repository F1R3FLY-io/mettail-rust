# Congruence Rules Design

**Status:** Design Phase
**Date:** October 29, 2025
**Phase:** 3 - Rewrite Engine Enhancement

---

## Overview

Congruence rules enable rewriting **within subterms** of constructors. The principle:

> If `S => T` (by some rewrite rule), then `op(..., S, ...) => op(..., T, ...)`

This allows rewrite rules to apply **recursively** throughout a term structure, not just at the top level.

---

## Motivation

### Current State: Direct Pattern Matching Only

We can currently rewrite:
```
for(a<-x){*x} | a!(0)  =>  *@(0)
```

But we **cannot** rewrite nested terms like:
```
b!(0) | (for(a<-x){*x} | a!(0))  =>  b!(0) | *@(0)
         ^^^^^^^^^^^^^^^^^^^^
         communication happens here
```

Without congruence rules, the communication pattern is **hidden** inside the parallel composition and won't match.

### Solution: Congruence Rules

Add explicit congruence rules to the theory:
```rust
rewrites {
    // Direct communication rule
    if x # Q then (PPar (PInput chan x P) (POutput chan Q))
        => (subst P x (NQuote Q));

    // Congruence: rewrite right side of parallel composition
    if S => T then (PPar P S) => (PPar P T);
}
```

Now the system can:
1. Try direct rewrite rules on the whole term
2. Try congruence rules that recursively rewrite subterms
3. Keep applying until normal form

---

## Syntax

### Congruence Rule Declaration

```rust
if S => T then (Constructor P ... S ...) => (Constructor P ... T ...)
   ^^^^^^^     ^^^^^^^^^^^^^^^^^^^^^^^^     ^^^^^^^^^^^^^^^^^^^^^^^^
   premise     LHS pattern                  RHS pattern
   (rewrite)   (S appears in one position)  (S replaced by T)
```

**Key properties:**
- **Premise:** `S => T` means "S can be rewritten to T by some rule"
- **LHS pattern:** Contains variable `S` in exactly one field position
- **RHS pattern:** Same constructor, but `S` replaced by `T`

### Multiple Variables

```rust
// Valid: Single rewrite premise
if S => T then (PPar P S) => (PPar P T)

// Also valid: Multiple non-rewrite premises
if x # Q, S => T then (PInput chan x S) => (PInput chan x T)

// Future work: Multiple rewrite premises (not in initial implementation)
if S1 => T1, S2 => T2 then ...
```

---

## Implementation Plan

### Phase 1: Extend AST (`macros/src/ast.rs`)

**Current structure:**
```rust
pub struct RewriteRule {
    pub conditions: Vec<FreshnessCondition>,
    pub left: Expr,
    pub right: Expr,
}

pub struct FreshnessCondition {
    pub var: Ident,
    pub term: Ident,
}
```

**New structure:**
```rust
pub enum Premise {
    Freshness(FreshnessCondition),  // x # Q
    Rewrite {                       // S => T
        source_var: Ident,          // S
        target_var: Ident,          // T
    },
}

pub struct FreshnessCondition {
    pub var: Ident,
    pub term: Ident,
}

pub struct RewriteRule {
    pub premises: Vec<Premise>,     // Renamed from 'conditions'
    pub left: Expr,
    pub right: Expr,
}
```

**Tasks:**
- [ ] Define `Premise` enum
- [ ] Add `Rewrite` variant with `source_var` and `target_var`
- [ ] Rename `conditions` to `premises` in `RewriteRule`
- [ ] Update all code that references `conditions`

---

### Phase 2: Parse Congruence Syntax (`macros/src/lib.rs` or parser module)

**Current parsing:** (simplified)
```rust
// Parses: if x # Q then LHS => RHS
if input.peek(Token![if]) {
    // Parse conditions
    while not_then {
        let var = parse_ident();
        parse_token!(#);
        let term = parse_ident();
        conditions.push(FreshnessCondition { var, term });
    }
}
```

**New parsing:**
```rust
// Parses: if x # Q, S => T then LHS => RHS
if input.peek(Token![if]) {
    loop {
        let first_var = parse_ident();

        if peek_token!(#) {
            // Freshness condition: x # Q
            parse_token!(#);
            let term = parse_ident();
            premises.push(Premise::Freshness(FreshnessCondition { var: first_var, term }));
        } else if peek_token!(=>) {
            // Rewrite premise: S => T
            parse_token!(=>);
            let target = parse_ident();
            premises.push(Premise::Rewrite {
                source_var: first_var,
                target_var: target,
            });
        } else {
            error!("Expected # or => after variable in premise");
        }

        if !peek_token!(,) { break; }
        parse_token!(,);
    }

    parse_token!(then);
}
```

**Tasks:**
- [ ] Locate rewrite rule parsing code
- [ ] Add conditional parsing for `#` vs `=>`
- [ ] Update to create `Premise` enum variants
- [ ] Test parsing both freshness and rewrite premises

---

### Phase 3: Classify Rule Type (`macros/src/rewrite_gen.rs`)

**Discriminate between regular and congruence rules:**

```rust
fn generate_rule_matcher(
    idx: usize,
    rule: &RewriteRule,
    theory: &TheoryDef
) -> TokenStream {
    // Check if this is a congruence rule
    let has_rewrite_premise = rule.premises.iter()
        .any(|p| matches!(p, Premise::Rewrite { .. }));

    if has_rewrite_premise {
        generate_congruence_matcher(idx, rule, theory)
    } else {
        generate_direct_matcher(idx, rule, theory)  // Existing code path
    }
}
```

**Tasks:**
- [ ] Add `generate_congruence_matcher` function
- [ ] Refactor existing code into `generate_direct_matcher`
- [ ] Route based on premise types

---

### Phase 4: Generate Congruence Matchers

**Goal:** For `if S => T then (PPar P S) => (PPar P T)`, generate:

```rust
pub fn try_rewrite_rule_1(term: &Proc) -> Option<Proc> {
    // Match the constructor pattern
    if let Proc::PPar(field_0, field_1) = term {
        // field_1 corresponds to variable S in the pattern
        // Try applying ALL rewrite rules to field_1

        if let Some(rewritten) = try_rewrite_rule_0(&**field_1) {
            return Some(Proc::PPar(
                field_0.clone(),
                Box::new(rewritten)
            ));
        }

        // Try next rule
        if let Some(rewritten) = try_rewrite_rule_1(&**field_1) {
            return Some(Proc::PPar(
                field_0.clone(),
                Box::new(rewritten)
            ));
        }

        // Try remaining rules...
        // (Generated for all rules in theory)
    }
    None
}
```

**Algorithm:**

1. **Extract rewrite premise:** `Premise::Rewrite { source_var: S, target_var: T }`

2. **Find S's position in LHS:**
   - Parse LHS: `(PPar P S)`
   - Identify which argument is `S` (must be `Expr::Var(S)`)
   - Map to AST field index (e.g., `field_1`)

3. **Generate pattern match:**
   ```rust
   if let Category::Constructor(field_0, field_1, ...) = term {
       // ...
   }
   ```

4. **Generate rewrite attempts:**
   For each rule `i` in `0..theory.rewrites.len()`:
   ```rust
   if let Some(rewritten) = try_rewrite_rule_i(&**field_N) {
       return Some(Category::Constructor(
           field_0.clone(),
           ...,
           Box::new(rewritten),  // Replace field_N
           ...
       ));
   }
   ```

5. **Return None if no rewrites succeed**

**Tasks:**
- [ ] Implement `find_rewrite_var_position(lhs: &Expr, var: &Ident) -> usize`
- [ ] Generate constructor pattern match
- [ ] Generate loop over all rewrite rules
- [ ] Generate reconstruction with rewritten field
- [ ] Handle `Box<T>` wrapping/unwrapping correctly

---

### Phase 5: Handle Edge Cases

#### 5.1 Self-Application

**Issue:** Rule can call itself recursively

**Example:**
```
Rule 1: if S => T then (PPar P S) => (PPar P T)

Term: PPar(a, PPar(b, c))
```

**Execution:**
1. Try rule 1 on whole term
2. Match `PPar(a, PPar(b, c))`
3. Try rule 1 on `field_1 = PPar(b, c)`  ← Self-application
4. Match `PPar(b, c)`
5. Try rule 0 (communication) on `field_1 = c`

**Solution:** Include the current rule index when generating rewrite attempts. This is actually **desired behavior** for nested rewrites.

```rust
// Always try all rules, including self
for i in 0..total_rule_count {
    if let Some(rewritten) = try_rewrite_rule_i(&**field_N) { ... }
}
```

#### 5.2 Multiple Fields

**Constraint:** Each congruence rule applies to **one specific field only**

**Example:**
```rust
// Valid: Rewrites second field only
if S => T then (PPar P S) => (PPar P T)

// Also valid: Different rule for first field
if S => T then (PPar S Q) => (PPar T Q)

// Invalid: Ambiguous which field to rewrite
if S => T then (PPar S S) => (PPar T T)
```

**Validation:** During typechecking, ensure:
- LHS contains exactly one occurrence of `source_var`
- RHS contains exactly one occurrence of `target_var`
- Both occur in same position

**Tasks:**
- [ ] Add validation in typechecker
- [ ] Report error if variable appears multiple times
- [ ] Report error if variable positions don't match

#### 5.3 Freshness + Rewrite Premises

**Example:**
```rust
if x # P, S => T then (PInput chan x S) => (PInput chan x T)
```

**Generated code:**
```rust
pub fn try_rewrite_rule_N(term: &Proc) -> Option<Proc> {
    if let Proc::PInput(field_0, scope_field) = term {
        let (binder, body) = scope_field.clone().unbind();

        // Try rewriting body (which corresponds to S)
        if let Some(rewritten) = try_rewrite_rule_0(&*body) {
            // Check freshness condition BEFORE returning
            if !is_fresh(&binder, &rewritten) {
                return None;  // Freshness violated after rewrite
            }

            // Re-bind with rewritten body
            let new_scope = Scope::new(binder.clone(), Box::new(rewritten));
            return Some(Proc::PInput(
                field_0.clone(),
                new_scope
            ));
        }

        // Try more rules...
    }
    None
}
```

**Tasks:**
- [ ] Extract freshness premises separately
- [ ] Generate freshness checks AFTER rewrite succeeds
- [ ] Apply to rewritten term, not original

---

### Phase 6: Integration & Testing

#### 6.1 Update Main Rewrite Engine

**Current pattern:**
```rust
pub fn reduce(term: Proc) -> Proc {
    let mut current = term;
    loop {
        if let Some(rewritten) = try_rewrite_rule_0(&current) {
            current = rewritten;
        } else {
            break;
        }
    }
    current
}
```

**With congruence:**
```rust
pub fn reduce(term: Proc) -> Proc {
    let mut current = term;
    let mut step = 0;
    loop {
        let mut changed = false;

        // Try all rules (direct + congruence)
        for i in 0..RULE_COUNT {
            if let Some(rewritten) = try_rewrite_rule(i, &current) {
                current = rewritten;
                changed = true;
                step += 1;
                break;  // Apply one rule at a time
            }
        }

        if !changed {
            break;  // Normal form reached
        }
    }
    current
}
```

**Tasks:**
- [ ] Generate rule dispatcher
- [ ] Add step counting
- [ ] Add max step limit (prevent infinite loops)
- [ ] Add trace/debug output

#### 6.2 Test Cases

**Test 1: Nested Communication**
```rust
// Input: b!(0) | (for(a<-x){*x} | a!(0))
// Expected: b!(0) | *@(0)

let term = Proc::PPar(
    Box::new(Proc::POutput(...)),
    Box::new(Proc::PPar(
        Box::new(Proc::PInput(...)),
        Box::new(Proc::POutput(...))
    ))
);

let result = reduce(term);
// Should reduce inner communication first via congruence
```

**Test 2: Deep Nesting**
```rust
// Input: c!(1) | (b!(2) | (for(a<-x){*x} | a!(0)))
// Expected: c!(1) | (b!(2) | *@(0))
```

**Test 3: Multiple Reductions**
```rust
// Input: (for(a<-x){*x} | a!(1)) | (for(b<-y){*y} | b!(2))
// Expected: *@(1) | *@(2)
```

**Test 4: No Infinite Loop**
```rust
// Input: a!(0)  (no matching input)
// Expected: a!(0)  (unchanged)
```

**Tasks:**
- [ ] Write test cases in `examples/rhocalc.rs`
- [ ] Verify congruence rules fire correctly
- [ ] Verify termination
- [ ] Add debug output to trace rewrites

---

## Design Decisions

### Decision 1: Which Rules to Try?

**Question:** When applying a congruence rule, which other rules should be attempted?

**Options:**
1. Only rules defined before this rule (prevents cycles)
2. All rules except this one (prevents direct recursion)
3. All rules including this one (allows nested patterns)

**Decision:** **All rules including this one** (Option 3)

**Rationale:**
- Handles nested patterns: `PPar(P, PPar(Q, S))`
- Congruence rule can recursively apply to subterms
- Termination guaranteed by term size decreasing (base rewrites are confluent)
- Matches standard rewriting semantics

### Decision 2: Field Position Specification

**Question:** How to specify which field to rewrite?

**Options:**
1. Infer from variable position in pattern
2. Explicit annotation: `if S => T at 2 then ...`
3. Generate congruence for all fields automatically

**Decision:** **Infer from pattern** (Option 1)

**Rationale:**
- More concise syntax
- Pattern makes it clear: `(PPar P S)` ← S is in second position
- Consistent with freshness conditions
- Can validate during typechecking

### Decision 3: Return Strategy

**Question:** When multiple rules can rewrite a field, which one to apply?

**Options:**
1. First successful rewrite (stop immediately)
2. Try all, return longest reduction
3. Non-deterministic (explore all paths)

**Decision:** **First successful** (Option 1)

**Rationale:**
- Simpler implementation
- Predictable behavior
- Matches eager evaluation strategy
- Can be changed later if needed

### Decision 4: Binder Handling

**Question:** Can congruence rules rewrite inside binders?

**Example:**
```rust
if S => T then (PInput chan x S) => (PInput chan x T)
                               ^                     ^
                               inside scope
```

**Decision:** **Defer to Phase 2** - Start with non-binder fields only

**Rationale:**
- Binders require careful freshness management
- Need to check `x # T` after rewriting
- Need to re-bind after rewriting body
- Adds complexity; validate basic approach first

---

## Implementation Phases

### Phase 1: MVP (This PR)
- [ ] Extend AST with `Premise` enum
- [ ] Parse rewrite premises (`S => T`)
- [ ] Generate congruence matchers for simple fields
- [ ] Test with `PPar` congruence rule
- [ ] Validate nested communication example works

**Success Criteria:**
```rust
// Input
b!(0) | (for(a<-x){*x} | a!(0))

// Output
b!(0) | *@(0)
```

### Phase 2: Binder Support (Next PR)
- [ ] Handle congruence inside binders
- [ ] Generate freshness checks after rewrite
- [ ] Re-binding logic
- [ ] Test with `PInput` body rewrites

### Phase 3: Optimization (Future)
- [ ] Cache rewrite attempts
- [ ] Parallel rule application
- [ ] Strategy selection (innermost, outermost, etc.)

---

## Open Questions

1. **Congruence generation:** Should we auto-generate congruence rules for all constructors? Or require explicit declaration?
   - **For now:** Explicit only (more predictable)
   - **Future:** Could add `@derive(Congruence)` attribute

2. **Rule ordering:** Does order of congruence rules matter?
   - **Current:** Try in declaration order
   - **Analysis needed:** Impact on performance/semantics

3. **Termination:** How to prevent infinite rewrite loops?
   - **Current:** Assume confluence + decreasing term size
   - **Future:** Add max step limit, cycle detection

4. **Multiple rewrite premises:** Support `if S1 => T1, S2 => T2 then ...`?
   - **Current:** No (not needed for MVP)
   - **Future:** Could enable rewriting multiple fields at once

---

## Related Work

- **K Framework:** Auto-generates congruence rules for all contexts
- **Maude:** Explicit congruence rules via `crl` (conditional rewrite logic)
- **Stratego:** Strategy combinators for controlling rewrite order
- **PLT Redex:** Reduction contexts specify where rewrites can occur

---

## Next Steps

1. Review this design document
2. Get approval on syntax and semantics
3. Start implementation with Phase 1 (AST extension)
4. Iterate on each phase with tests

---

**Last Updated:** October 29, 2025
**Status:** Ready for implementation

