# Macro Flow Analysis

This document analyzes the core tasks of the `theory!` macro, identifies the minimal necessary structure for each, and contrasts the current implementation.

## Overview: What the Macro Does

The `theory!` macro takes a theory definition (categories, constructors, equations, rewrites) and generates:

1. **AST Types** - Rust enums for each category
2. **Parser** - LALRPOP grammar to parse terms
3. **Display** - Pretty-printing for terms
4. **Substitution** - Capture-avoiding substitution methods
5. **Equality Rules** - Ascent Datalog for equational reasoning
6. **Rewrite Rules** - Ascent Datalog for term rewriting
7. **Auxiliary** - Blockly blocks, term generation, etc.

## Core Data Flow

```
TheoryDef (parsed input)
    │
    ├─► AST Generation (codegen/ast_gen.rs)
    │   └─► Rust enums, Display, Substitution
    │
    ├─► Parser Generation (codegen/parser/)
    │   └─► LALRPOP grammar file
    │
    └─► Ascent Generation (ascent/)
        ├─► Relations (relations.rs)
        ├─► Category rules (categories.rs)
        ├─► Equation rules (equations.rs)
        └─► Rewrite rules (rewrites/, congruence/)
```

---

## Task 1: AST Generation

### Goal
Generate Rust enums for each category with proper derives and field types.

### Minimal Structure
```
Input:  TheoryDef { exports, terms }
Output: TokenStream of enum definitions

Core logic:
1. Group grammar rules by category
2. For each export, generate enum with variants from rules
3. Each variant's fields come from grammar items (NonTerminal → Box<Cat>, Collection → HashBag<Cat>, etc.)
```

### Current Implementation

**File:** `codegen/ast_gen.rs` (1659 lines)

**Issues:**
- `generate_ast()` calls 10 different generators (flatten, normalize, subst, display, termgen, eval, rewrite, env...)
- Most of these could be separate modules or even separate files
- Many functions share logic for "iterating over category rules" - no abstraction

**Redundant patterns:**
```rust
// Pattern repeated ~15 times across files:
let rules: Vec<&GrammarRule> = theory.terms.iter()
    .filter(|r| r.category == *category)
    .collect();
```

**Proposed simplification:**
- Extract `theory.rules_for_category(cat)` helper
- Split `ast_gen.rs` into: `enums.rs`, `eval.rs`, `env.rs`
- Keep `generate_ast()` as pure orchestrator

---

## Task 2: Substitution Generation

### Goal
Generate `substitute(&self, var, replacement) -> Self` methods for each category.

### Minimal Structure
```
For each category:
  For each variant:
    Match fields, recursively substitute, handle binders
```

### Current Implementation

**File:** `codegen/subst.rs` (1637 lines!)

**Issues:**
- Handles 5 different substitution cases:
  1. Same-category substitution
  2. Cross-category substitution
  3. Multi-binder substitution
  4. Native type handling
  5. Collection field substitution

- **Massive code duplication** between regular and multi-binder cases
- Complex control flow with 10+ helper functions
- ~500 lines just for multi-binder support

**Proposed simplification:**
- The BoundTerm derive macro handles most substitution
- Only need custom logic for multi-binders and cross-category
- Could reduce to ~300 lines with proper abstraction

---

## Task 3: Parser Generation

### Goal
Generate LALRPOP grammar from theory definition.

### Minimal Structure
```
For each category:
  Generate production rules from grammar items
  Handle precedence/associativity
  Generate terminals for literals
```

### Current Implementation

**File:** `codegen/parser/lalrpop.rs` (779 lines)

**Reasonable:** This is one of the cleaner modules. Grammar generation is inherently complex.

**Minor issues:**
- Some duplication in handling different grammar item types
- Could use a trait for "generate LALRPOP pattern"

---

## Task 4: Ascent Relation Generation

### Goal
Declare Ascent relations: `cat(Cat)`, `eq_cat(Cat, Cat)`, `rw_cat(Cat, Cat)`.

### Minimal Structure
```
For each category:
  relation cat(Cat);
  relation eq_cat(Cat, Cat);  // with eqrel annotation
  relation rw_cat(Cat, Cat);
```

### Current Implementation

**File:** `ascent/relations.rs` (160 lines)

**Reasonable:** Clean and focused.

**Minor issues:**
- `extract_category_from_rewrite` duplicated in multiple files
- Collection projection relations could be simpler

---

## Task 5: Equation Rule Generation

### Goal
Generate Ascent rules for:
1. Reflexivity: `eq_cat(t, t) <-- cat(t)`
2. Congruence: args equal → terms equal
3. User equations: `eq_cat(lhs, rhs) <-- cat(lhs), ...conditions...`

### Minimal Structure
```
1. Reflexivity: trivial one-liner per category
2. Congruence: for each n-ary constructor, generate rule
3. User equations: parse LHS/RHS patterns, generate matching clauses
```

### Current Implementation

**File:** `ascent/equations.rs` (554 lines)

**Issues:**
- `generate_equation_clause()` is 200+ lines with deeply nested logic
- **Pattern matching logic duplicated** with rewrites module
- Variable occurrence tracking duplicated
- Category extraction duplicated

**Functions that should be shared:**
- `collect_variable_occurrences()` - used in equations AND rewrites
- `generate_ascent_pattern()` - used in equations AND rewrites AND congruence
- `extract_category_from_pattern()` - used everywhere

---

## Task 6: Rewrite Rule Generation

### Goal
Generate Ascent rules for:
1. Base rewrites: `rw_cat(lhs, rhs) <-- cat(lhs), ...conditions...`
2. Congruence: if arg rewrites, constructor result rewrites

### Minimal Structure
```
1. Base rewrites: same as equations, but for rw_cat relation
2. Congruence: for each constructor field position, generate rule
```

### Current Implementation

**Files:**
- `ascent/rewrites/mod.rs` (43 lines) - just re-exports
- `ascent/rewrites/clauses.rs` (447 lines)
- `ascent/rewrites/patterns.rs` (872 lines!)
- `ascent/rewrites/rhs.rs` (385 lines)
- `ascent/congruence/mod.rs` (160 lines)
- `ascent/congruence/analysis.rs` (806 lines!)
- `ascent/congruence/binding.rs` (~200 lines)
- `ascent/congruence/collection.rs` (420 lines)
- `ascent/congruence/regular.rs` (260 lines)
- `ascent/congruence/projections.rs` (~200 lines)

**Total: ~3,800 lines for rewrite generation!**

**Major Issues:**

1. **Duplicated pattern matching:** `patterns.rs` has `generate_ascent_pattern()` and `generate_ascent_lhs_pattern()` which are nearly identical to code in equations.rs

2. **Proliferation of "info" types:**
   ```rust
   CollectionCongruenceInfo
   RegularCongruencePattern
   ElementPatternInfo
   CaptureInfo
   // ... and more
   ```
   These carry data between functions but obscure the actual computation.

3. **Over-abstracted congruence handling:**
   - 5 files for congruence rules
   - Projection-based approach adds complexity for marginal benefit
   - Could be 1 file with ~200 lines

4. **Category extraction chaos:**
   ```rust
   extract_category()           // in analysis.rs
   extract_category_from_pattern()  // in analysis.rs
   extract_category_from_rewrite()  // in relations.rs
   infer_category_from_pattern()    // in patterns.rs
   // All do essentially the same thing!
   ```

---

## Identified Redundancies

### 1. Pattern → Ascent Clause Generation

**Used by:** equations, rewrites, congruence

**Current:** 3 different implementations with slight variations

**Minimal:**
```rust
fn pattern_to_ascent_clauses(
    pattern: &Pattern,
    term_var: &Ident,
    category: &Ident,
    theory: &TheoryDef,
) -> (Vec<TokenStream>, HashMap<String, Ident>)
```

### 2. Variable Occurrence Collection

**Used by:** equations, rewrites, validation

**Current:** Multiple functions:
- `collect_variable_occurrences()`
- `collect_vars_from_pattern()`
- `collect_pattern_vars()`
- `find_duplicate_vars()`

**Minimal:**
```rust
fn collect_vars(pattern: &Pattern) -> HashMap<String, usize>  // var → count
```

### 3. Category Extraction

**Used by:** everywhere

**Current:** 5+ different functions

**Minimal:**
```rust
impl Pattern {
    fn category(&self, theory: &TheoryDef) -> Option<Ident>
}
```

### 4. Constructor Lookup

**Used by:** everywhere

**Current:** `theory.terms.iter().find(|r| r.label == constructor)` repeated 50+ times

**Minimal:**
```rust
impl TheoryDef {
    fn constructor(&self, name: &Ident) -> Option<&GrammarRule>
    fn constructors_for_category(&self, cat: &Ident) -> Vec<&GrammarRule>
}
```

---

## Proposed Restructure

### Phase 1: Add Helper Methods to TheoryDef
```rust
impl TheoryDef {
    fn constructor(&self, name: &Ident) -> Option<&GrammarRule>;
    fn constructors_for(&self, category: &Ident) -> Vec<&GrammarRule>;
    fn category_of(&self, constructor: &Ident) -> Option<Ident>;
    fn is_collection_constructor(&self, name: &Ident) -> bool;
    fn collection_element_type(&self, name: &Ident) -> Option<Ident>;
}
```

### Phase 2: Unify Pattern Operations in pattern.rs
```rust
impl Pattern {
    fn category(&self, theory: &TheoryDef) -> Option<Ident>;
    fn constructor_name(&self) -> Option<&Ident>;
    fn collect_vars(&self) -> HashMap<String, usize>;
    fn to_ascent_clauses(&self, ...) -> AscentClauses;
}
```

### Phase 3: Simplify Ascent Generation
```
ascent/
  mod.rs           - orchestration
  relations.rs     - relation declarations (keep as-is)
  rules.rs         - unified equation/rewrite generation
  congruence.rs    - all congruence in one file
```

### Phase 4: Simplify Codegen
```
codegen/
  mod.rs
  enums.rs         - just enum generation
  subst.rs         - simplified substitution
  display.rs       - keep as-is
  parser/          - keep as-is
```

---

## Summary Table

| Module | Current Lines | Minimal Estimate | Redundancy Type |
|--------|--------------|------------------|-----------------|
| ast_gen.rs | 1659 | 400 | Over-bundling |
| subst.rs | 1637 | 400 | Duplication |
| equations.rs | 554 | 150 | Shared w/ rewrites |
| rewrites/ | 1747 | 400 | Shared w/ equations |
| congruence/ | 2046 | 300 | Over-abstraction |
| patterns.rs | 872 | (merge) | Duplication |
| **Total** | **8515** | **~1650** | **80% reduction** |

---

## Detailed Implementation Plan

### Phase 0: Remove Term::CollectionConstruct

**Goal:** Make `Term` a pure object-language type without metasyntax.

The new `Pattern` type replaces the need for `Term::CollectionConstruct`:

| Old (Term) | New (Pattern) |
|------------|---------------|
| `Term::CollectionConstruct { constructor, elements, merge_with }` | `Pattern::Collection { constructor, elements, rest }` |

**Key insight:** Collection syntax like `{P, Q, ...rest}` is *rule specification*, not object-language. The runtime representation uses `HashBag<T>` directly, constructed by generated code.

**Changes:**
1. Remove `Term::CollectionConstruct` variant from `term.rs`
2. Update parsing to produce `Pattern::Collection` instead
3. RHS code generation constructs `HashBag` directly from `Pattern::Collection`

---

### Phase 1: TheoryDef Helper Methods

**Goal:** Eliminate the repeated `theory.terms.iter().find(...)` pattern.

**Location:** `macros/src/ast/theory.rs`

```rust
impl TheoryDef {
    /// Get a grammar rule by constructor name
    pub fn get_constructor(&self, name: &Ident) -> Option<&GrammarRule> {
        self.terms.iter().find(|r| &r.label == name)
    }

    /// Get all constructors for a category
    pub fn constructors_for(&self, category: &Ident) -> Vec<&GrammarRule> {
        self.terms.iter()
            .filter(|r| &r.category == category)
            .collect()
    }

    /// Get the category that a constructor produces
    pub fn category_of_constructor(&self, constructor: &Ident) -> Option<&Ident> {
        self.get_constructor(constructor).map(|r| &r.category)
    }

    /// Check if a constructor has a collection field
    pub fn is_collection_constructor(&self, name: &Ident) -> bool {
        self.get_constructor(name)
            .map(|r| r.items.iter().any(|i| matches!(i, GrammarItem::Collection { .. })))
            .unwrap_or(false)
    }

    /// Get the element type of a collection constructor
    pub fn collection_element_type(&self, name: &Ident) -> Option<&Ident> {
        self.get_constructor(name).and_then(|r| {
            r.items.iter().find_map(|i| {
                if let GrammarItem::Collection { element_type, .. } = i {
                    Some(element_type)
                } else {
                    None
                }
            })
        })
    }

    /// Check if a constructor has binders
    pub fn has_binders(&self, name: &Ident) -> bool {
        self.get_constructor(name)
            .map(|r| !r.bindings.is_empty())
            .unwrap_or(false)
    }

    /// Get the export definition for a category
    pub fn get_export(&self, category: &Ident) -> Option<&Export> {
        self.exports.iter().find(|e| &e.name == category)
    }

    /// Check if a category has a native type
    pub fn has_native_type(&self, category: &Ident) -> bool {
        self.get_export(category)
            .map(|e| e.native_type.is_some())
            .unwrap_or(false)
    }
}
```

**Soundness:** These are pure accessor methods with no behavior changes. They return references or `Option`, preserving ownership semantics.

**Migration:** 
1. Add the methods
2. Search-replace common patterns:
   - `theory.terms.iter().find(|r| r.label == *name)` → `theory.get_constructor(name)`
   - `theory.terms.iter().filter(|r| r.category == *cat).collect()` → `theory.constructors_for(cat)`

---

### Phase 2: Pattern Type Completion

**Goal:** Complete the `Pattern` and `PatternTerm` types with all needed operations.

**Location:** `macros/src/ast/pattern.rs`

#### 2.1 Category Inference

```rust
impl Pattern {
    /// Infer the category this pattern produces (if determinable)
    /// 
    /// Returns `Some(category)` if the pattern unambiguously produces that category.
    /// Returns `None` for variables (unknown without context) or errors.
    pub fn category(&self, theory: &TheoryDef) -> Option<&Ident> {
        match self {
            Pattern::Term(pt) => pt.category(theory),
            Pattern::Collection { constructor, .. } => {
                constructor.as_ref().and_then(|c| theory.category_of_constructor(c))
            }
            Pattern::Map { collection, .. } => collection.category(theory),
            Pattern::Zip { collections } => {
                // Zip produces a collection of tuples - category depends on usage
                collections.first().and_then(|c| c.category(theory))
            }
        }
    }
    
    /// Get the constructor name if this pattern is a constructor application
    pub fn constructor_name(&self) -> Option<&Ident> {
        match self {
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => Some(constructor),
            Pattern::Collection { constructor, .. } => constructor.as_ref(),
            _ => None,
        }
    }
}

impl PatternTerm {
    /// Infer the category this pattern term produces
    pub fn category(&self, theory: &TheoryDef) -> Option<&Ident> {
        match self {
            PatternTerm::Var(_) => None, // Variables need context
            PatternTerm::Apply { constructor, .. } => theory.category_of_constructor(constructor),
            PatternTerm::Lambda { body, .. } => body.category(theory),
            PatternTerm::MultiLambda { body, .. } => body.category(theory),
            PatternTerm::Subst { term, .. } => term.category(theory),
            PatternTerm::MultiSubst { scope, .. } => scope.category(theory),
        }
    }
}
```

**Soundness:** Category inference follows the grammar rules. Lambda/Subst return the body's category because binding doesn't change the type.

#### 2.2 Variable Collection with Counts

```rust
impl Pattern {
    /// Collect all variable occurrences with their counts
    /// Useful for detecting duplicate variables that need equational checks
    pub fn var_occurrences(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        self.collect_var_occurrences(&mut counts);
        counts
    }
    
    fn collect_var_occurrences(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Pattern::Term(pt) => pt.collect_var_occurrences(counts),
            Pattern::Collection { elements, rest, .. } => {
                for elem in elements {
                    elem.collect_var_occurrences(counts);
                }
                if let Some(r) = rest {
                    *counts.entry(r.to_string()).or_insert(0) += 1;
                }
            }
            Pattern::Map { collection, params, body } => {
                collection.collect_var_occurrences(counts);
                // params are binders, not occurrences
                // body occurrences that match params are bound
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                let param_names: HashSet<_> = params.iter().map(|p| p.to_string()).collect();
                for (var, count) in body_counts {
                    if !param_names.contains(&var) {
                        *counts.entry(var).or_insert(0) += count;
                    }
                }
            }
            Pattern::Zip { collections } => {
                for coll in collections {
                    coll.collect_var_occurrences(counts);
                }
            }
        }
    }
    
    /// Get variables that appear more than once (need equational matching)
    pub fn duplicate_vars(&self) -> HashSet<String> {
        self.var_occurrences()
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .map(|(var, _)| var)
            .collect()
    }
}
```

**Soundness:** This correctly handles binding by excluding bound variables from the count in `Map`. The `free_vars` method (already implemented) handles scoping; this gives raw occurrences for duplicate detection.

#### 2.3 Pattern to Ascent Clauses (Core Abstraction)

This is the most important unification. Currently duplicated across equations.rs, patterns.rs, and congruence code.

```rust
/// Result of converting a pattern to Ascent clauses
pub struct AscentClauses {
    /// The clauses to add to the rule body (if let ..., for loops, etc.)
    pub clauses: Vec<TokenStream>,
    /// Variable bindings: var_name -> expression to access it
    pub bindings: HashMap<String, TokenStream>,
    /// Category assignments for variables
    pub variable_categories: HashMap<String, Ident>,
    /// Equational checks needed for duplicate variables
    pub equational_checks: Vec<TokenStream>,
}

impl Pattern {
    /// Convert this pattern to Ascent matching clauses
    /// 
    /// # Arguments
    /// * `term_var` - The Ascent variable being matched (e.g., `s`)
    /// * `category` - The expected category of `term_var`
    /// * `theory` - Theory definition for lookups
    /// * `duplicate_vars` - Variables that appear multiple times (need eq_ checks)
    /// 
    /// # Example Output
    /// For pattern `(PNew x P)` with `term_var = s`:
    /// ```text
    /// clauses: [
    ///     if let Proc::PNew(x_binder, p_scope) = s
    /// ]
    /// bindings: { "x" -> x_binder.clone(), "P" -> p_body.clone() }
    /// ```
    pub fn to_ascent_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
    ) -> AscentClauses {
        let mut result = AscentClauses {
            clauses: Vec::new(),
            bindings: HashMap::new(),
            variable_categories: HashMap::new(),
            equational_checks: Vec::new(),
        };
        
        self.generate_clauses(
            term_var,
            category,
            theory,
            duplicate_vars,
            &mut result,
            &mut HashSet::new(), // first_occurrence tracker
        );
        
        result
    }
    
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
    ) {
        match self {
            Pattern::Term(pt) => {
                pt.generate_clauses(term_var, category, theory, duplicate_vars, result, first_occurrences)
            }
            Pattern::Collection { constructor, elements, rest } => {
                // Generate collection matching
                self.generate_collection_clauses(
                    term_var, category, constructor.as_ref(), elements, rest.as_ref(),
                    theory, duplicate_vars, result, first_occurrences
                )
            }
            Pattern::Map { .. } | Pattern::Zip { .. } => {
                // These are handled specially for LHS (rarely used) and RHS
                unimplemented!("Map/Zip in LHS patterns not yet supported")
            }
        }
    }
    
    fn generate_collection_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        constructor: Option<&Ident>,
        elements: &[Pattern],
        rest: Option<&Ident>,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
    ) {
        let cons = constructor.expect("Collection pattern must have constructor");
        let elem_cat = theory.collection_element_type(cons)
            .expect("Collection constructor must have element type");
        
        // Match the constructor
        let bag_var = format_ident!("{}_bag", term_var);
        result.clauses.push(quote! {
            if let #category::#cons(#bag_var) = #term_var
        });
        
        // Generate element matching
        let mut elem_vars = Vec::new();
        for (i, elem) in elements.iter().enumerate() {
            let elem_var = format_ident!("{}_elem_{}", term_var, i);
            let count_var = format_ident!("_count_{}_{}", term_var, i);
            elem_vars.push(elem_var.clone());
            
            result.clauses.push(quote! {
                for (#elem_var, #count_var) in #bag_var.iter()
            });
            
            // Distinctness checks
            for prev in &elem_vars[..i] {
                result.clauses.push(quote! {
                    if &#elem_var != &#prev
                });
            }
            
            // Recursively process element pattern
            elem.generate_clauses(
                &elem_var, elem_cat, theory, duplicate_vars, result, first_occurrences
            );
        }
        
        // Bind rest variable
        if let Some(rest_var) = rest {
            let rest_ident = format_ident!("{}_rest", term_var);
            if !elem_vars.is_empty() {
                result.clauses.push(quote! {
                    let #rest_ident = {
                        let mut bag = #bag_var.clone();
                        #(bag.remove(&#elem_vars);)*
                        bag
                    }
                });
            } else {
                result.clauses.push(quote! {
                    let #rest_ident = #bag_var.clone()
                });
            }
            result.bindings.insert(rest_var.to_string(), quote! { #rest_ident.clone() });
        }
    }
}
```

**Soundness:** 
- This unifies the logic from `generate_ascent_pattern` and `generate_ascent_lhs_pattern`
- Collection handling properly generates distinctness checks
- First-occurrence tracking ensures duplicate variables get equational checks

#### 2.4 PatternTerm Clause Generation

```rust
impl PatternTerm {
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
    ) {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();
                
                if duplicate_vars.contains(&var_name) {
                    // Duplicate variable - need equational check
                    if first_occurrences.insert(var_name.clone()) {
                        // First occurrence: bind it
                        result.bindings.insert(var_name.clone(), quote! { #term_var.clone() });
                        result.variable_categories.insert(var_name, category.clone());
                    } else {
                        // Subsequent occurrence: emit eq check
                        let existing = result.bindings.get(&var_name).unwrap().clone();
                        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
                        result.equational_checks.push(quote! {
                            #eq_rel(#existing, #term_var.clone())
                        });
                    }
                } else {
                    // Single-occurrence variable: just bind
                    result.bindings.insert(var_name.clone(), quote! { #term_var.clone() });
                    result.variable_categories.insert(var_name, category.clone());
                }
            }
            
            PatternTerm::Apply { constructor, args } => {
                let rule = theory.get_constructor(constructor)
                    .expect("Unknown constructor in pattern");
                
                // Generate field variables
                let field_vars: Vec<Ident> = (0..args.len())
                    .map(|i| format_ident!("{}_f{}", term_var, i))
                    .collect();
                
                // Generate destructuring pattern
                result.clauses.push(quote! {
                    if let #category::#constructor(#(#field_vars),*) = #term_var
                });
                
                // Recursively process each argument
                for (i, (arg, field_var)) in args.iter().zip(&field_vars).enumerate() {
                    let field_cat = get_field_category(rule, i, theory);
                    
                    // Handle Box<T> - need to dereference
                    let deref_var = if needs_box(rule, i, theory) {
                        let deref = format_ident!("{}_deref", field_var);
                        result.clauses.push(quote! {
                            let #deref = &**#field_var
                        });
                        deref
                    } else {
                        field_var.clone()
                    };
                    
                    arg.generate_clauses(
                        &deref_var, &field_cat, theory, duplicate_vars, result, first_occurrences
                    );
                }
            }
            
            PatternTerm::Lambda { binder, body } => {
                // Match scope, unbind to get binder and body
                let scope_var = format_ident!("{}_scope", term_var);
                let binder_var = format_ident!("{}_binder", term_var);
                let body_var = format_ident!("{}_body", term_var);
                
                result.clauses.push(quote! {
                    let (#binder_var, #body_var) = #term_var.clone().unbind()
                });
                
                // Bind the binder variable
                result.bindings.insert(binder.to_string(), quote! { #binder_var.clone() });
                
                // Recursively process body
                // Note: body's category should be inferred from context
                let body_cat = body.category(theory).unwrap_or(category);
                body.generate_clauses(
                    &body_var, body_cat, theory, duplicate_vars, result, first_occurrences
                );
            }
            
            PatternTerm::Subst { term, var, replacement } => {
                // Substitution in LHS is unusual but could mean:
                // Match a term that's the result of substitution
                // For now, treat as constructing and matching
                unimplemented!("Subst in LHS patterns")
            }
            
            // Similar for MultiLambda, MultiSubst
            _ => unimplemented!("Complex pattern in LHS")
        }
    }
}

/// Get the category of field i in a constructor
fn get_field_category(rule: &GrammarRule, i: usize, theory: &TheoryDef) -> Ident {
    let mut field_idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(cat) => {
                if field_idx == i {
                    return cat.clone();
                }
                field_idx += 1;
            }
            GrammarItem::Collection { element_type, .. } => {
                if field_idx == i {
                    // Collection field - return element type for iteration
                    return element_type.clone();
                }
                field_idx += 1;
            }
            GrammarItem::Binder { category } => {
                if field_idx == i {
                    return category.clone();
                }
                field_idx += 1;
            }
            _ => {} // Skip terminals
        }
    }
    panic!("Field index {} out of bounds for {}", i, rule.label);
}

/// Check if field i needs Box wrapping (recursive types)
fn needs_box(rule: &GrammarRule, i: usize, theory: &TheoryDef) -> bool {
    let mut field_idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(cat) => {
                if field_idx == i {
                    // Box if same category as constructor's result (recursive)
                    return cat == &rule.category;
                }
                field_idx += 1;
            }
            _ => {
                if matches!(item, GrammarItem::Collection { .. } | GrammarItem::Binder { .. }) {
                    field_idx += 1;
                }
            }
        }
    }
    false
}
```

**Soundness:**
- Variables: first occurrence binds, subsequent occurrences emit eq checks
- Apply: destructs constructor, recursively matches arguments
- Lambda: unbinds scope to get binder and body, recursively matches body
- Box handling: correctly dereferences recursive fields
- Field category lookup: follows grammar structure

---

### Phase 3: Unified Ascent Rule Generation

**Goal:** Replace separate equation/rewrite generators with one unified module.

**Key Insight:** Equations and rewrites differ only in:
1. The relation they write to (`eq_cat` vs `rw_cat`)
2. Whether they're bidirectional (equations) or directional (rewrites)

```rust
/// Unified rule generator for both equations and rewrites
pub fn generate_rule_clause(
    left: &Pattern,
    right: &Pattern,
    conditions: &[Condition],
    relation_name: &Ident,  // eq_proc or rw_proc
    theory: &TheoryDef,
) -> TokenStream {
    // 1. Determine category from LHS
    let category = left.category(theory)
        .expect("Cannot determine category from LHS");
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    
    // 2. Find duplicate variables for equational matching
    let mut all_vars = left.var_occurrences();
    for (var, count) in right.var_occurrences() {
        *all_vars.entry(var).or_insert(0) += count;
    }
    let duplicate_vars: HashSet<_> = all_vars.into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(var, _)| var)
        .collect();
    
    // 3. Generate LHS matching clauses
    let lhs_var = format_ident!("s");
    let lhs_clauses = left.to_ascent_clauses(&lhs_var, category, theory, &duplicate_vars);
    
    // 4. Generate RHS construction
    let rhs_var = format_ident!("t");
    let rhs_expr = right.to_ascent_rhs(&lhs_clauses.bindings, theory);
    
    // 5. Generate condition checks
    let condition_clauses = generate_condition_clauses(conditions, &lhs_clauses.bindings);
    
    // 6. Assemble the rule
    let clauses = &lhs_clauses.clauses;
    let eq_checks = &lhs_clauses.equational_checks;
    
    quote! {
        #relation_name(#lhs_var.clone(), #rhs_var) <--
            #cat_lower(#lhs_var),
            #(#clauses,)*
            #(#eq_checks,)*
            #(#condition_clauses,)*
            let #rhs_var = #rhs_expr;
    }
}
```

**Soundness:** 
- Category inference from LHS ensures type safety
- Duplicate variable detection handles equational matching
- Conditions are processed uniformly

#### RHS Construction

The RHS needs its own method on `Pattern`:

```rust
impl Pattern {
    /// Generate RHS construction expression
    /// 
    /// # Arguments
    /// * `bindings` - Variables bound by LHS → their Ascent expressions
    /// * `theory` - Theory definition for constructor lookups
    /// 
    /// # Example
    /// For RHS `(PNew x (PPar {P, Q}))` with bindings `{"x" -> x_binder, "P" -> p, "Q" -> q}`:
    /// ```text
    /// Proc::PNew(x_binder.clone(), Box::new(Proc::PPar({
    ///     let mut bag = HashBag::new();
    ///     bag.insert(p.clone());
    ///     bag.insert(q.clone());
    ///     bag
    /// })))
    /// ```
    pub fn to_ascent_rhs(
        &self,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        match self {
            Pattern::Term(pt) => pt.to_ascent_rhs(bindings, theory),
            Pattern::Collection { constructor, elements, rest } => {
                self.generate_collection_rhs(constructor.as_ref(), elements, rest.as_ref(), bindings, theory)
            }
            Pattern::Map { collection, params, body } => {
                self.generate_map_rhs(collection, params, body, bindings, theory)
            }
            Pattern::Zip { collections } => {
                self.generate_zip_rhs(collections, bindings, theory)
            }
        }
    }
    
    fn generate_collection_rhs(
        &self,
        constructor: Option<&Ident>,
        elements: &[Pattern],
        rest: Option<&Ident>,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        let elem_exprs: Vec<_> = elements.iter()
            .map(|e| e.to_ascent_rhs(bindings, theory))
            .collect();
        
        let coll_type = quote! { mettail_runtime::HashBag };
        
        if let Some(rest_var) = rest {
            let rest_binding = bindings.get(&rest_var.to_string())
                .expect("rest variable not bound");
            quote! {
                {
                    let mut bag = (#rest_binding).clone();
                    #(bag.insert(#elem_exprs);)*
                    bag
                }
            }
        } else {
            quote! {
                {
                    let mut bag = #coll_type::new();
                    #(bag.insert(#elem_exprs);)*
                    bag
                }
            }
        }
    }
    
    fn generate_map_rhs(
        &self,
        collection: &Pattern,
        params: &[Ident],
        body: &Pattern,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        // Generate: collection.iter().map(|params| body).collect()
        let coll_expr = collection.to_ascent_rhs(bindings, theory);
        
        // For each element, evaluate body with params bound
        // This requires knowing the element type
        let param = &params[0]; // Assume single param for now
        
        quote! {
            {
                let mut result = mettail_runtime::HashBag::new();
                for (#param, _count) in (#coll_expr).iter() {
                    let mapped = /* body with #param bound */;
                    result.insert(mapped);
                }
                result
            }
        }
    }
}

impl PatternTerm {
    pub fn to_ascent_rhs(
        &self,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();
                bindings.get(&var_name)
                    .map(|b| quote! { (#b).clone() })
                    .unwrap_or_else(|| quote! { #v.clone() })
            }
            PatternTerm::Apply { constructor, args } => {
                let category = theory.category_of_constructor(constructor)
                    .expect("Unknown constructor");
                let arg_exprs: Vec<_> = args.iter()
                    .map(|a| a.to_ascent_rhs(bindings, theory))
                    .collect();
                
                // Check which args need Box
                let rule = theory.get_constructor(constructor).unwrap();
                let boxed_args = wrap_args_if_needed(&arg_exprs, rule, theory);
                
                quote! { #category::#constructor(#(#boxed_args),*) }
            }
            PatternTerm::Lambda { binder, body } => {
                // Construct a Scope
                let body_expr = body.to_ascent_rhs(bindings, theory);
                quote! {
                    mettail_runtime::Scope::new(
                        mettail_runtime::Binder(#binder.to_string()),
                        #body_expr
                    )
                }
            }
            PatternTerm::Subst { term, var, replacement } => {
                let term_expr = term.to_ascent_rhs(bindings, theory);
                let repl_expr = replacement.to_ascent_rhs(bindings, theory);
                quote! { (#term_expr).substitute(&#var, &#repl_expr) }
            }
            // ... other cases
        }
    }
}
```

**Soundness:**
- Variable references look up in bindings map (established by LHS)
- Constructor applications recursively construct arguments
- Collections build a HashBag and insert elements
- Map/Zip iterate and transform (future work for full implementation)

---

### Phase 4: Simplified Congruence

**Goal:** Replace 5 congruence files with one.

**Key Insight:** Congruence rules follow a simple pattern:
- For each field position in a constructor that can rewrite:
  - If field `i` rewrites from `s` to `t`, the whole term rewrites

```rust
/// Generate all congruence rules for a theory
pub fn generate_congruence_rules(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    
    for rule in &theory.terms {
        let category = &rule.category;
        let constructor = &rule.label;
        let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
        
        // Skip if has native type
        if theory.has_native_type(category) {
            continue;
        }
        
        // Get rewritable field positions
        let field_positions = get_rewritable_fields(rule, theory);
        
        for (field_idx, field_cat) in field_positions {
            if theory.is_collection_constructor(constructor) {
                rules.push(generate_collection_congruence(
                    category, constructor, &rw_rel, &field_cat, theory
                ));
            } else if theory.has_binders(constructor) {
                rules.push(generate_binding_congruence(
                    category, constructor, field_idx, &rw_rel, rule, theory
                ));
            } else {
                rules.push(generate_simple_congruence(
                    category, constructor, field_idx, &rw_rel, rule
                ));
            }
        }
    }
    
    rules
}

fn generate_simple_congruence(
    category: &Ident,
    constructor: &Ident,
    field_idx: usize,
    rw_rel: &Ident,
    rule: &GrammarRule,
) -> TokenStream {
    // Generate: if arg_i rewrites, whole term rewrites
    let cat_lower = format_ident!("{}", category.to_string().to_lowercase());
    let field_cat_lower = /* get from rule.items[field_idx] */;
    let rw_field_rel = format_ident!("rw_{}", field_cat_lower);
    
    let n = count_nonterminal_fields(rule);
    let vars: Vec<Ident> = (0..n).map(|i| format_ident!("x{}", i)).collect();
    let mut vars_t = vars.clone();
    vars_t[field_idx] = format_ident!("t");
    
    let s_var = &vars[field_idx];
    
    quote! {
        #rw_rel(lhs, rhs) <--
            #cat_lower(lhs),
            if let #category::#constructor(#(#vars),*) = lhs,
            #rw_field_rel(#s_var.clone(), t),
            let rhs = #category::#constructor(#(#vars_t.clone()),*);
    }
}
```

**Soundness:**
- Simple congruence is structurally correct: matches constructor, finds rewrite in field, reconstructs
- Collection congruence needs special handling for bag iteration
- Binding congruence must respect scoping (field rewrites under binder)

---

### Phase 5: Module Restructure

**Proposed final structure:**

```
macros/src/
├── ast/
│   ├── mod.rs
│   ├── grammar.rs       # GrammarRule, GrammarItem
│   ├── pattern.rs       # Pattern, PatternTerm (expanded with methods)
│   ├── term.rs          # Term (runtime, no metasyntax)
│   ├── theory.rs        # TheoryDef (with helper methods)
│   └── types.rs
│
├── ascent/
│   ├── mod.rs           # generate_ascent_source orchestrator
│   ├── relations.rs     # Relation declarations (keep as-is)
│   ├── rules.rs         # Unified equation/rewrite generation (NEW)
│   └── congruence.rs    # All congruence in one file (NEW)
│
├── codegen/
│   ├── mod.rs
│   ├── enums.rs         # Just enum generation (split from ast_gen)
│   ├── subst.rs         # Simplified substitution
│   ├── display.rs
│   ├── parser/
│   └── ...
│
└── validation/
    ├── mod.rs
    ├── validator.rs
    └── typechecker.rs
```

---

## Correctness Invariants

### Invariant 1: Category Consistency
Every pattern in an equation/rewrite LHS must have a determinable category, and it must match the RHS category.

**Enforcement:** `validate_theory` calls `TypeChecker::check_equation` and `TypeChecker::check_rewrite`.

### Invariant 2: Variable Scoping
Variables bound by patterns (e.g., in binders, collection rest) are visible in the RHS.

**Enforcement:** `Pattern::free_vars()` and `Pattern::var_occurrences()` respect scoping. The `to_ascent_clauses` method builds a bindings map that tracks where each variable is bound.

### Invariant 3: Collection Element Type Matching
In a `Collection` pattern, elements must match the collection's element type.

**Enforcement:** `validate_pattern` checks that collection constructors exist and have collection fields. The `to_ascent_clauses` method looks up element types from the grammar.

### Invariant 4: Duplicate Variable Equational Matching
If a variable appears multiple times, the generated code must check equality (via eq_cat relations) rather than assuming syntactic identity.

**Enforcement:** `Pattern::duplicate_vars()` identifies these. The clause generator emits `eq_cat(x1, x2)` checks when the same variable is bound twice.

---

## Migration Strategy

### Step 1: Non-breaking additions (1-2 hours)
- Add `TheoryDef` helper methods
- Add remaining `Pattern` methods (category, var_occurrences)
- No existing code changes

### Step 2: Internal refactoring (2-4 hours)
- Replace inline lookups with helper methods (mechanical search-replace)
- Verify tests still pass

### Step 3: Unify pattern generation (4-8 hours)
- Implement `Pattern::to_ascent_clauses` 
- Update `equations.rs` to use it
- Update `rewrites/clauses.rs` to use it
- Remove duplicated code from `rewrites/patterns.rs`

### Step 4: Simplify congruence (4-8 hours)
- Create unified `congruence.rs`
- Migrate collection, binding, regular congruence
- Remove old congruence/ directory

### Step 5: Cleanup (2-4 hours)
- Remove dead code
- Update documentation
- Final test pass

**Total estimated time:** 13-26 hours

---

## Map/Zip in Patterns: Multi-Communication Support

**Goal:** Support patterns like multi-communication in pi-calculus, where multiple channels synchronize simultaneously.

### Example: Multi-Comm Pattern

```
// Match: collection where all elements are PInput on same channel
xs.#map(|x| (PInput chan_x scope_x))

// RHS: substitute all bodies with all messages
#zip(scope_xs, msg_xs).#map(|(scope, msg)| subst(scope, x, msg))
```

### LHS Semantics for Map

When `#map` appears on LHS:
1. **Bound collection:** Iterate collection, match body pattern against each element
2. **Unbound collection:** Search for all matching elements, bind to collection

```rust
impl Pattern {
    fn generate_map_lhs_clauses(
        &self,
        collection: &Pattern,
        params: &[Ident],
        body: &Pattern,
        term_var: &Ident,
        theory: &TheoryDef,
        result: &mut AscentClauses,
    ) {
        // If collection is already bound, iterate and match
        // If collection is unbound, this is a "findall" pattern
        
        let coll_name = match collection {
            Pattern::Term(PatternTerm::Var(v)) => v.to_string(),
            _ => panic!("Map collection must be a variable"),
        };
        
        if result.bindings.contains_key(&coll_name) {
            // Bound: iterate and match each element
            let coll_binding = result.bindings.get(&coll_name).unwrap();
            let elem_var = format_ident!("{}_elem", term_var);
            let param = &params[0];
            
            result.clauses.push(quote! {
                for (#elem_var, _) in (#coll_binding).iter()
            });
            
            // Match body pattern with param bound to elem_var
            let mut body_bindings = result.bindings.clone();
            body_bindings.insert(param.to_string(), quote! { #elem_var.clone() });
            
            // Generate body matching with updated bindings
            // Collected variables become Vec<T>
        } else {
            // Unbound: "findall" - search for all matching elements
            // This requires aggregation in Ascent (lattice or collect)
            todo!("Unbound map collection - requires Ascent aggregation")
        }
    }
}
```

### LHS Semantics for Zip

When `#zip` appears on LHS:
1. **Both bound:** Parallel iteration, match pairs
2. **One bound, one unbound:** For each in bound, search for matching unbound
3. **Both unbound:** Search/join (most expensive)

```rust
fn generate_zip_lhs_clauses(
    collections: &[Pattern],
    term_var: &Ident,
    theory: &TheoryDef,
    result: &mut AscentClauses,
) {
    // Determine which collections are bound
    let bound_status: Vec<bool> = collections.iter()
        .filter_map(|c| {
            if let Pattern::Term(PatternTerm::Var(v)) = c {
                Some(result.bindings.contains_key(&v.to_string()))
            } else {
                None
            }
        })
        .collect();
    
    match (bound_status.get(0), bound_status.get(1)) {
        (Some(true), Some(true)) => {
            // Both bound: parallel iteration
            // zip(xs, ys).iter() gives (x, y) pairs
        }
        (Some(true), Some(false)) | (Some(false), Some(true)) => {
            // One bound: search/join
            // For each x in xs, find matching y in ys
        }
        _ => {
            // Neither bound or error
            todo!("Complex zip pattern")
        }
    }
}
```

### RHS Semantics for Map

Transform each element:
```rust
fn generate_map_rhs(
    collection: &Pattern,
    params: &[Ident],
    body: &Pattern,
    bindings: &HashMap<String, TokenStream>,
    theory: &TheoryDef,
) -> TokenStream {
    let coll_expr = collection.to_ascent_rhs(bindings, theory);
    let param = &params[0];
    let body_expr = body.to_ascent_rhs(bindings, theory);
    
    quote! {
        {
            let mut result = mettail_runtime::HashBag::new();
            for (#param, _count) in (#coll_expr).iter() {
                result.insert(#body_expr);
            }
            result
        }
    }
}
```

### RHS Semantics for Zip

Pair-wise combination:
```rust
fn generate_zip_rhs(
    collections: &[Pattern],
    bindings: &HashMap<String, TokenStream>,
    theory: &TheoryDef,
) -> TokenStream {
    // For two collections, generate paired iteration
    let coll_exprs: Vec<_> = collections.iter()
        .map(|c| c.to_ascent_rhs(bindings, theory))
        .collect();
    
    // Zip requires equal-length collections (or truncate to shorter)
    quote! {
        {
            let xs = #(#coll_exprs[0]);
            let ys = #(#coll_exprs[1]);
            xs.iter().zip(ys.iter()).map(|(x, y)| (x.clone(), y.clone())).collect()
        }
    }
}
```

### Implementation Priority

1. **Phase 1:** RHS Map (transform collections) - straightforward iteration
2. **Phase 2:** RHS Zip (pair collections) - straightforward zip
3. **Phase 3:** LHS Map with bound collection - iterate and match
4. **Phase 4:** LHS Zip with one bound - search/join
5. **Phase 5:** LHS with unbound collections - requires Ascent aggregation

---

## Testing Strategy

### Unit Tests for Pattern Methods

```rust
#[test]
fn test_pattern_category() {
    let theory = /* setup */;
    let pattern = Pattern::Term(PatternTerm::Apply {
        constructor: format_ident!("PNew"),
        args: vec![/* ... */],
    });
    assert_eq!(pattern.category(&theory), Some(&format_ident!("Proc")));
}

#[test]
fn test_duplicate_vars() {
    let pattern = /* (PInput X P) | (POutput X Q) */;
    let dups = pattern.duplicate_vars();
    assert!(dups.contains("X"));
    assert!(!dups.contains("P"));
}

#[test]
fn test_to_ascent_clauses() {
    let theory = /* setup */;
    let pattern = Pattern::Term(PatternTerm::Apply {
        constructor: format_ident!("PInput"),
        args: vec![
            Pattern::Term(PatternTerm::Var(format_ident!("x"))),
            Pattern::Term(PatternTerm::Var(format_ident!("p"))),
        ],
    });
    let clauses = pattern.to_ascent_clauses(
        &format_ident!("s"),
        &format_ident!("Proc"),
        &theory,
        &HashSet::new(),
    );
    
    // Verify clauses contain if-let destructuring
    assert!(clauses.clauses[0].to_string().contains("if let"));
    // Verify bindings for x and p
    assert!(clauses.bindings.contains_key("x"));
    assert!(clauses.bindings.contains_key("p"));
}
```

### Integration Tests

Test that generated Ascent code compiles and runs correctly:

```rust
#[test]
fn test_equation_codegen() {
    // Generate code for: (PNew x (PNew y P)) == (PNew y (PNew x P)) if x # P, y # P
    let code = generate_equation_clause(&eq, &theory);
    
    // Compile and run in test harness
    let result = eval_ascent(code);
    
    // Verify the equation holds
    assert!(result.eq_proc.contains(&(term1, term2)));
}
```

### Regression Tests

Keep existing theory tests (rhocalc, ambient, etc.) to ensure migration doesn't break functionality.

---

**Total estimated time:** 13-26 hours

---

## Completion Status (January 2026)

### Completed Phases ✓

All core refactoring phases have been completed:

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 0: Remove Term::CollectionConstruct | ✓ Complete | Pattern::Collection now handles collection metasyntax |
| Phase 1: TheoryDef Helper Methods | ✓ Complete | `get_constructor`, `constructors_for`, etc. |
| Phase 2: Pattern Type Completion | ✓ Complete | `category()`, `var_occurrences()`, `to_ascent_clauses()`, `to_ascent_rhs()` |
| Phase 3: Unified Ascent Rule Generation | ✓ Complete | `generate_rule_clause` in `ascent/rules.rs` |
| Phase 4: Simplified Congruence | ✓ Complete | Single `congruence/unified.rs` replaces 5 files |
| Phase 5: Module Restructure | ✓ Complete | Cleaner module layout achieved |
| Phase 6: Cleanup | ✓ Complete | Legacy code removed, all theories working |

### Deleted Files (Legacy Code Removed)

```
macros/src/ascent/congruence/analysis.rs     (806 lines)
macros/src/ascent/congruence/binding.rs      (~200 lines)
macros/src/ascent/congruence/collection.rs   (420 lines)
macros/src/ascent/congruence/regular.rs      (260 lines)
macros/src/ascent/congruence/projections.rs  (~200 lines)
macros/src/ascent/rewrites/patterns.rs       (841 lines)
macros/src/ascent/rewrites/rhs.rs            (383 lines)
```

**Total removed:** ~3,100 lines of legacy code

### Current Module Structure

```
macros/src/
├── ast/
│   ├── mod.rs
│   ├── grammar.rs       # GrammarRule, GrammarItem
│   ├── pattern.rs       # Pattern, PatternTerm (with AscentClauses)
│   ├── term.rs          # Term (pure object language)
│   └── theory.rs        # TheoryDef (with helper methods)
│
├── ascent/
│   ├── mod.rs           # Orchestration
│   ├── relations.rs     # Relation declarations
│   ├── rules.rs         # Unified equation/rewrite generation (NEW)
│   └── congruence/
│       ├── mod.rs
│       └── unified.rs   # All congruence in one file (NEW)
│
├── codegen/
│   ├── mod.rs           # With auto-generation helpers
│   ├── ast_gen.rs       # Enum generation + IVar/NumLit auto-gen
│   ├── subst.rs         # Substitution
│   ├── display.rs       # Display impl
│   └── parser/          # LALRPOP generation
│
└── validation/
    └── validator.rs     # Pattern validation
```

### Key Technical Achievements

1. **Unified Pattern Type**: `Pattern` and `PatternTerm` handle both LHS matching and RHS construction
2. **AscentClauses Abstraction**: Single `to_ascent_clauses()` method replaces duplicated pattern-to-Datalog logic
3. **Stable Binder Identity**: Using `unsafe_pattern()`/`unsafe_body()` and `from_parts_unsafe()` instead of `unbind()`/`Scope::new()` prevents infinite loops in equations with binders
4. **Native Type Support**: Auto-generation of `IVar`/`NumLit` variants for categories with native types
5. **Explicit Congruence**: Rewrite congruence rules are now explicit in theory definitions (e.g., `if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})`)

### Working Theories

| Theory | Status | Features Tested |
|--------|--------|-----------------|
| calculator | ✓ Working | Native types, env queries, auto-generated IVar/NumLit |
| rhocalc | ✓ Working | Collections, binders, communication, congruence |
| ambient | ✓ Working | Nested binders, scope extrusion equations, freshness conditions |

---

## Next Steps: Collection Metasyntax

The core Pattern refactoring is complete. The remaining work is implementing advanced collection operations for multi-communication:

1. **`#map` in RHS**: Transform each element of a collection (partially implemented)
2. **`#zip` in patterns**: Pair-wise iteration over multiple collections
3. **Multi-binder support**: `^[x0,x1,...].body` syntax for binding multiple variables
4. **Multi-substitution**: `multisubst` for simultaneous substitution

See `docs/design/exploring/pattern-type.md` and `docs/design/exploring/collection-metasyntax.md` for detailed designs.
