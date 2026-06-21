# Phase 1: Critical Analysis for Proper Foundation

**Date:** 2025-10-25
**Status:** Analysis for completeness

---

## Current State Assessment

### ✅ What We Have
1. **Type-checking** - Basic context-aware type inference
2. **Equations** - Parsing and basic type validation
3. **Freshness conditions** - Parsed but not validated
4. **AST** - Extended to support equations and expressions
5. **Validation** - Constructor and category checking

### ⏳ What's Planned (from PHASE-1-PLAN.md)
1. Parser Generation
2. Binders support
3. Theory Composition (deferred to 1.5)

---

## Critical Foundation Gaps

### 🔴 CRITICAL: Missing Core Features

#### 1. **Freshness Condition Validation** (HIGH PRIORITY)
**Current:** We parse `if x # Q then ...` but don't validate it
**Problem:** Can't properly check scope/binding without this
**Impact:** Can't define theories like `NewReplCalc` correctly

**What's needed:**
```rust
// In typechecker.rs or validator.rs
fn validate_freshness_condition(
    cond: &FreshnessCondition,
    left: &Expr,
    right: &Expr
) -> Result<(), ValidationError> {
    // Check that:
    // 1. Variable `x` appears in the equation
    // 2. Term `Q` is valid (e.g., `Q` in `x # Q`)
    // 3. Freshness makes semantic sense
}
```

**Example:**
```rust
equations {
    if x # Q then (NQuote (PNew x Q)) == Q
}
// We need to verify:
// - x is a bound variable
// - Q has correct category
// - x doesn't appear free in Q
```

**Estimated:** 1-2 days

---

#### 2. **Variable Scoping and Bound Variables** (HIGH PRIORITY)
**Current:** We track variable types but not scopes
**Problem:** Can't handle binders or freshness properly
**Impact:** Can't distinguish free vs bound variables

**What's needed:**
```rust
pub struct Scope {
    bound_vars: HashMap<String, Category>,
    free_vars: HashMap<String, Category>,
}

impl TypeChecker {
    pub fn check_with_scope(
        &self,
        expr: &Expr,
        scope: &Scope
    ) -> Result<Category, TypeError> {
        // Handle bound vs free variables
    }
}
```

**Estimated:** 2-3 days

---

#### 3. **Runtime AST Types** (HIGH PRIORITY)
**Current:** `runtime` is empty
**Problem:** Generated code has nowhere to go
**Impact:** Can't actually instantiate or manipulate terms

**What's needed:**
```rust
// runtime/src/lib.rs
pub trait Term: Clone + Debug {
    fn category(&self) -> &str;
}

pub trait Equation<T: Term> {
    fn check(&self, left: &T, right: &T) -> bool;
}

// Maybe also:
pub trait Parser<T: Term> {
    fn parse(&self, input: &str) -> Result<T, ParseError>;
}
```

**Estimated:** 2-3 days

---

#### 4. **Better Error Messages with Spans** (MEDIUM-HIGH PRIORITY)
**Current:** Errors are just strings
**Problem:** Hard to debug macro usage
**Impact:** Poor developer experience

**What's needed:**
```rust
use syn::spanned::Spanned;

pub enum ValidationError {
    UnknownCategory {
        name: String,
        span: proc_macro2::Span,
    },
    TypeMismatch {
        expected: String,
        found: String,
        span: proc_macro2::Span,
    },
    // etc.
}

impl ValidationError {
    pub fn to_compile_error(&self) -> proc_macro2::TokenStream {
        let span = self.span();
        let msg = self.message();
        quote_spanned!(span => compile_error!(#msg))
    }
}
```

**Estimated:** 1-2 days

---

### 🟡 IMPORTANT: Quality Improvements

#### 5. **Category Validation in Grammar Rules** (MEDIUM PRIORITY)
**Current:** We check exports, but not all category references
**Problem:** Could reference undefined categories in grammar
**Impact:** Runtime errors instead of compile-time errors

**What's needed:**
```rust
fn validate_grammar_rule(rule: &GrammarRule, theory: &TheoryDef) -> Result<(), String> {
    // Check that rule.category is exported
    // Check that all NonTerminal categories are exported
}
```

**Example catch:**
```rust
terms {
    Foo . Bar ::= (Baz) ;  // Error: Bar and Baz not exported
}
```

**Estimated:** 0.5 days

---

#### 6. **Comprehensive Testing Infrastructure** (MEDIUM PRIORITY)
**Current:** A few examples, basic tests
**Problem:** Not systematic enough
**Impact:** Bugs slip through

**What's needed:**
1. **Unit tests** for each module
2. **Integration tests** for complete theories
3. **Negative tests** (should fail compilation)
4. **Property-based tests** (using `proptest`)

**Structure:**
```
macros/tests/
├── compile_fail/          # Tests that should fail
│   ├── unknown_category.rs
│   ├── type_mismatch.rs
│   └── ...
├── compile_pass/          # Tests that should succeed
│   ├── simple_monoid.rs
│   ├── quote_drop.rs
│   └── ...
└── integration/
    ├── parser_roundtrip.rs
    └── ...
```

**Estimated:** 2-3 days (ongoing)

---

#### 7. **Documentation and Examples** (MEDIUM PRIORITY)
**Current:** Minimal documentation
**Problem:** Hard to understand for users/contributors
**Impact:** Adoption and maintenance

**What's needed:**
1. **API docs** - Doc comments on all public items
2. **User guide** - How to define theories
3. **Examples** - More diverse examples
4. **Theory cookbook** - Common patterns

**Estimated:** 2-3 days (ongoing)

---

### 🟢 NICE-TO-HAVE: Future Enhancements

#### 8. **Pattern Matching in Equations** (LOW PRIORITY)
**Current:** Only constructor application
**Future:** Need patterns like `(Plus A B)` matching any Plus term

**Defer to:** Phase 2

---

#### 9. **Rewrite Rule Execution** (LOW PRIORITY)
**Current:** Only equation checking
**Future:** Need to actually apply rewrites

**Defer to:** Phase 2

---

#### 10. **Performance Optimization** (LOW PRIORITY)
**Current:** Basic implementation
**Future:** Optimize type-checking, parsing

**Defer to:** Phase 3

---

## Revised Phase 1 Scope

### Core Foundation (Weeks 1-2)

**Week 1: Type System + Validation**
- [x] Day 1-2: Basic type-checking ✅
- [x] Day 3-4: Equations + context tracking ✅
- [ ] Day 5-6: **Freshness validation** ⭐
- [ ] Day 7: **Scoping infrastructure** ⭐

**Week 2: Runtime + Error Handling**
- [ ] Day 1-2: **Runtime AST types** ⭐
- [ ] Day 3-4: **Error messages with spans** ⭐
- [ ] Day 5: **Category validation** ⭐
- [ ] Day 6-7: Testing infrastructure

### Parser Generation (Week 3)

**Week 3: Parser Combinators**
- [ ] Day 1-2: Parser trait generation
- [ ] Day 3-4: Terminal/non-terminal handling
- [ ] Day 5: Recursive parsing
- [ ] Day 6-7: Error handling + tests

### Binders (Week 4)

**Week 4: Binders + Integration**
- [ ] Day 1-2: Binder syntax parsing
- [ ] Day 3-4: Scope tracking + bound variables
- [ ] Day 5: Integration with freshness
- [ ] Day 6-7: Testing + documentation

---

## Priority Ordering

### Must-Have for Phase 1 ⭐
1. **Freshness condition validation** (enables NewReplCalc)
2. **Variable scoping** (foundation for binders)
3. **Runtime AST types** (enables code generation)
4. **Parser generation** (makes theories usable)
5. **Binders** (needed for Rholang)

### Should-Have for Quality 🔶
6. **Error messages with spans** (developer experience)
7. **Category validation** (catch more bugs)
8. **Testing infrastructure** (confidence)
9. **Documentation** (usability)

### Nice-to-Have for Future 🟢
10. Pattern matching (Phase 2)
11. Rewrite execution (Phase 2)
12. Performance (Phase 3)

---

## Specific Action Items

### Immediate (This Week)

1. **Freshness Validation**
   - File: `macros/src/validator.rs`
   - Add: `validate_freshness_conditions()`
   - Test: `NewReplCalc` example

2. **Scoping Infrastructure**
   - File: `macros/src/typechecker.rs`
   - Add: `Scope` struct and `check_with_scope()`
   - Test: Bound vs free variables

3. **Runtime Foundation**
   - File: `runtime/src/lib.rs`
   - Add: `Term`, `Equation`, `Parser` traits
   - Test: Simple monoid runtime

### Next (Week 2)

4. **Error Spans**
   - Files: All validators
   - Add: `Span` tracking to errors
   - Test: Error message quality

5. **Category Validation**
   - File: `macros/src/validator.rs`
   - Add: Complete category checking
   - Test: Invalid category references

### Then (Weeks 3-4)

6. **Parser Generation**
7. **Binders**
8. **Testing + Docs**

---

## Questions for Consideration

### 1. Freshness Semantics
**Question:** What exactly does `x # Q` mean?
- Option A: `x` does not appear free in `Q`
- Option B: `x` is fresh (generated, unique) relative to `Q`
- **Proposal:** Start with Option A (simpler), add Option B if needed

### 2. Runtime Execution
**Question:** Should Phase 1 include term rewriting?
- **Current plan:** No, just AST types and parsing
- **Rationale:** Rewriting is complex, defer to Phase 2
- **User input needed:** Is this reasonable?

### 3. Parser Library
**Question:** Which parser library for combinator generation?
- Option A: `nom` (popular, well-tested)
- Option B: Hand-rolled (more control)
- **Proposal:** `nom` for reliability

### 4. Testing Strategy
**Question:** How thorough should testing be?
- **Proposal:**
  - Each validator function has unit tests
  - Each example has integration test
  - Add `trybuild` for compile-fail tests

---

## Success Criteria (Updated)

Phase 1 is complete when:

- [ ] **Freshness conditions** are validated at compile-time
- [ ] **Scoping** distinguishes bound vs free variables
- [ ] **Runtime types** exist and are used by codegen
- [ ] **Parsers** can be generated from grammar rules
- [ ] **Binders** work with proper scoping
- [ ] **Error messages** show spans and are helpful
- [ ] **All categories** are validated in grammar rules
- [ ] **Test suite** covers all validators
- [ ] **Examples** demonstrate all features:
  - `simple_monoid` - Basic theory
  - `quote_drop` - Equations without freshness
  - `new_repl` - Equations with freshness
  - `par_monoid` - Theory composition (if time permits)
- [ ] **Documentation** explains how to use the system

---

## Risk Assessment

### High Risk
- **Freshness semantics** - Might be subtle, need careful thought
- **Parser generation** - Complex, might take longer than expected
- **Binders** - Scope handling is tricky

### Medium Risk
- **Runtime design** - Need to get traits right for extensibility
- **Testing** - Need to prevent regressions

### Low Risk
- **Error spans** - Straightforward with `syn`
- **Category validation** - Simple extension of existing code

---

## Recommendation

**Proposed Phase 1 Duration:** 4 weeks (was 3)

**Justification:**
- Added critical features (freshness, scoping, runtime)
- More thorough testing
- Better error handling
- Proper foundation for Phase 2

**Alternative:** Keep 3 weeks, but defer testing/docs to Phase 1.5

---

**Decision needed:** Does this analysis capture everything for a proper foundation?

