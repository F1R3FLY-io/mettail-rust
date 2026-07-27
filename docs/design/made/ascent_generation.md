# Ascent Datalog Generation Design

**Status:** Design Phase
**Date:** November 4, 2025
**Phase:** 3 - Automated Datalog Generation

---

## Overview

Mettail is a framework for defining languages with variable-binding operations, equations, and rewrites. Currently, the `theory!` macro generates:
- ✅ AST enums (Rust types)
- ✅ LALRPOP parsers
- ✅ Substitution methods (capture-avoiding)
- ✅ Rewrite functions (`try_rewrite_rule_N`)
- ✅ Display implementations

However, the **core logic** for exploring rewrite spaces via Ascent (Rust Datalog) is currently **hand-written**. This document designs the automatic generation of Ascent code for:
- `eq` relations (equality/equations)
- `rw` relations (rewrites + congruences)
- `cat` relations (e.g., `proc`, `name`) for term exploration

**Key Design Principle:** Congruence rules are **explicitly declared** in `rewrites {}` (not auto-generated), making generation straightforward.

---

## Current State: Hand-Written Ascent Code

### Example: Ambient Calculus

```rust
ascent_source! {
    theory_source:

    // Relations
    relation proc(Proc);           // Terms explored
    relation eq(Proc, Proc);       // Equality relation
    relation rw(Proc, Proc);       // Rewrite relation
    relation path(Proc, Vec<Proc>);
    relation path_terminal(Proc, Vec<Proc>);

    // Category expansion: explore subterms
    proc(p1) <-- proc(p0), rw(p0,p1);
    proc(p1) <-- proc(p0), eq(p0,p1);
    proc(*p.clone()), proc(*q.clone()) <--
        proc(p0), if let Proc::PPar(p,q) = p0;
    proc(*p.clone()) <--
        proc(p0),
        if let Proc::PNew(scope) = p0,
        let (x,p) = scope.clone().unbind();

    // Equation clauses
    // Commutativity: P|Q == Q|P
    eq(p0,p1) <--
        proc(p0),
        if let Proc::PPar(p,q) = p0,
        let p1 = Proc::PPar(q.clone(),p.clone());

    // Associativity: P|(Q|R) == (P|Q)|R
    eq(p0,p1) <--
        proc(p0),
        if let Proc::PPar(t,r) = p0,
        if let Proc::PPar(p,q) = &**t,
        let p1 = Proc::PPar(p.clone(),Box::new(Proc::PPar(q.clone(),r.clone())));

    // Reflexivity, symmetry, transitivity
    eq(p,p) <-- proc(p);
    eq(q,p) <-- eq(p,q);
    eq(p,r) <-- eq(p,q), eq(q,r);

    // Rewrite clauses
    rw(s, t.clone()) <--
        proc(s),
        if let Some(t) = try_rewrite_rule_0(&s);
    rw(s, t.clone()) <--
        proc(s),
        if let Some(t) = try_rewrite_rule_1(&s);
    rw(s, t.clone()) <--
        proc(s),
        if let Some(t) = try_rewrite_rule_2(&s);

    // Congruence: rewrite inside PPar
    rw(s,t) <--
        proc(s),
        if let Proc::PPar(s0,p) = s,
        rw(**s0,t0),
        let t = Proc::PPar(Box::new(t0.clone()),p.clone());

    // Congruence: rewrite inside PNew
    rw(s,t) <--
        proc(s),
        if let Proc::PNew(scope) = s,
        let (x, p) = scope.clone().unbind(),
        rw(*p,t0),
        let new_scope = mettail_runtime::Scope::new(x.clone(), Box::new(t0.clone())),
        let t = Proc::PNew(new_scope);

    // Extension: rewrite along equality
    rw(s1,t) <-- rw(s0,t), eq(s0,s1);
}
```

---

## Goal: Automatic Generation

From a `theory!` definition, automatically generate the above Ascent code structure.

### Input (Theory Definition)

```rust
theory! {
    name: Ambient,
    exports {
        Proc
        Name
    },
    terms {
        PZero . Proc ::= "0" ;
        PPar . Proc ::= Proc "|" Proc ;
        PNew . Proc ::= "new(" <Name> "," Proc ")";
        PAmb . Proc ::= Name "[" Proc "]";
        // ...
        NVar . Name ::= Var ;
    },
    equations {
        (PPar P Q) == (PPar Q P) ;
        (PPar P (PPar Q R)) == (PPar (PPar P Q) R) ;
        (PPar P PZero) == P ;
        // ...
    },
    rewrites {
        (PPar (PAmb N (PPar (PIn M P) Q)) (PAmb M R))
            => (PAmb M (PPar (PAmb N (PPar P Q)) R));
        // ...
    }
}
```

### Output (Generated Ascent Source)

```rust
ascent_source! {
    ambient_source:  // Named source: ${theory_name}_source

    // Category exploration relations (unadorned)
    relation proc(Proc);
    relation name(Name);

    // Equality relations (per-category, typed)
    relation eq_proc(Proc, Proc);
    relation eq_name(Name, Name);

    // Rewrite relations (per-category, typed)
    relation rw_proc(Proc, Proc);
    relation rw_name(Name, Name);

    // Category exploration rules (generated)
    // Equation rules (generated)
    // Rewrite rules (generated)
}
```

**Note:** Category relations are unadorned (`proc`, `name`), but equality and rewrite relations are per-category and typed (`eq_proc`, `eq_name`, `rw_proc`, `rw_name`). Often only `rw_proc` will have clauses, not `rw_name`, as rewrites typically apply to the main process category.

---

## Design: Three Core Components

### 1. Category Relations (`cat`)

**Purpose:** Explore the term space by decomposing terms into subterms.

**Pattern:**
- Each exported category gets a relation: `proc`, `name`, etc.
- Terms expand via rewrites: `cat(t1) <-- cat(t0), rw(t0, t1)`
- Terms expand via equality: `cat(t1) <-- cat(t0), eq(t0, t1)`
- Terms expand via deconstruction: For each constructor, extract subterms

**Generation Strategy:**

For each exported category `C`:
1. Create relation: `relation cat(C);` where `cat` is the lowercase category name (e.g., `proc` for `Proc`)
2. Add expansion rules:
   - `cat(c1) <-- cat(c0), rw_cat(c0, c1);`
   - `cat(c1) <-- cat(c0), eq_cat(c0, c1);`
3. For each constructor of `C`:
   - Generate deconstruction clause

**Note:** Category exploration relations are unadorned (`proc`, `name`), but they reference the per-category typed rewrite/equality relations (`rw_proc`, `eq_proc`).

#### Example: Deconstruction Clauses

**For non-binding constructor (PPar):**
```rust
proc(*p.clone()), proc(*q.clone()) <--
    proc(p0),
    if let Proc::PPar(p,q) = p0;
```

**For binding constructor (PNew):**
```rust
proc(*p.clone()) <--
    proc(p0),
    if let Proc::PNew(scope) = p0,
    let (x,p) = scope.clone().unbind();
```

**Generation Algorithm:**

```rust
fn generate_category_deconstruction(
    category: &Ident,
    rules: &[GrammarRule]
) -> Vec<TokenStream> {
    let mut clauses = Vec::new();
    let cat_lower = category.to_string().to_lowercase();
    let cat_rel = format_ident!("{}", cat_lower);

    for rule in rules {
        if rule.bindings.is_empty() {
            // Non-binding constructor
            let constructor = &rule.label;
            let fields: Vec<_> = (0..field_count(rule))
                .map(|i| format_ident!("field_{}", i))
                .collect();

            let subterm_facts: Vec<_> = fields.iter().map(|f| {
                quote! { #cat_rel((*#f).clone()) }
            }).collect();

            clauses.push(quote! {
                #(#subterm_facts),* <--
                    #cat_rel(t),
                    if let #category::#constructor(#(#fields),*) = t;
            });
        } else {
            // Binding constructor
            // Generate unbinding + subterm extraction
            // ...
        }
    }
    clauses
}
```

---

### 2. Equality Relations (`eq`)

**Purpose:** Define equivalence classes based on equations.

**Pattern:**
- Reflexivity: `eq(t, t) <-- cat(t);`
- Symmetry: `eq(t2, t1) <-- eq(t1, t2);`
- Transitivity: `eq(t1, t3) <-- eq(t1, t2), eq(t2, t3);`
- One clause per equation declaration

**Generation Strategy:**

For each exported category `C` (e.g., `Proc`):
1. Create relation: `relation eq_cat(C, C);` (e.g., `eq_proc(Proc, Proc)`)
2. Add reflexivity, symmetry, transitivity
3. For each equation in `theory.equations` of type `C`:
   - Generate pattern-matching clause

#### Example: Equation Clauses

**Input equation:**
```rust
(PPar P Q) == (PPar Q P)
```

**Generated clause:**
```rust
eq_proc(p0, p1) <--
    proc(p0),
    if let Proc::PPar(p, q) = p0,
    let p1 = Proc::PPar(q.clone(), p.clone());
```

**Input equation (with nesting):**
```rust
(PPar P (PPar Q R)) == (PPar (PPar P Q) R)
```

**Generated clause:**
```rust
eq_proc(p0, p1) <--
    proc(p0),
    if let Proc::PPar(p, qr) = p0,
    if let Proc::PPar(q, r) = &**qr,
    let p1 = Proc::PPar(
        Box::new(Proc::PPar(p.clone(), q.clone())),
        r.clone()
    );
```

**Generation Algorithm:**

```rust
fn generate_equation_clause(
    category: &Ident,
    equation: &Equation,
    theory: &TheoryDef
) -> TokenStream {
    let cat_lower = category.to_string().to_lowercase();
    let eq_rel = format_ident!("eq_{}", cat_lower);
    let cat_rel = format_ident!("{}", cat_lower);

    // Parse LHS pattern
    let lhs_pattern = generate_pattern_match(&equation.left, "t0");

    // Generate RHS construction
    let rhs_expr = generate_construction(&equation.right);

    quote! {
        #eq_rel(t0, t1) <--
            #cat_rel(t0),
            #lhs_pattern,
            let t1 = #rhs_expr;
    }
}
```

**Key Challenge:** Handling nested patterns on LHS.
- Must generate cascading `if let` patterns
- Track variable bindings through nesting levels
- Similar to rewrite_gen.rs logic

---

### 3. Rewrite Relations (`rw`)

**Purpose:** Define rewrite steps via direct rules and congruences.

**Pattern:**
- One clause per **base** rewrite rule (via `try_rewrite_rule_N`)
- One clause per **congruence** rewrite rule (explicitly declared with `if S => T then`)
- Extension along equality: `rw(s1, t) <-- rw(s0, t), eq(s0, s1);`

**Generation Strategy:**

For each exported category `C` (e.g., `Proc`):
1. Create relation: `relation rw_cat(C, C);` (e.g., `rw_proc(Proc, Proc)`)
2. For each **base** rewrite rule of category `C` (no `if S => T` premise):
   - Add clause: `rw_cat(s, t) <-- cat(s), if let Some(t) = try_rewrite_rule_i(&s);`
3. For each **congruence** rewrite rule of category `C` (with `if S => T then` premise):
   - Parse pattern to identify constructor and field being rewritten
   - Generate recursive rewrite clause
4. Add extension rule: `rw_cat(s1, t) <-- rw_cat(s0, t), eq_cat(s0, s1);`

**Key Insight:** Congruences are **explicitly declared** in the theory, not auto-generated. This simplifies generation significantly!

**Note:** Rewrite relations are per-category and typed. Often only `rw_proc` will have clauses, not `rw_name`, as rewrites typically apply to the main process category.

#### Example: Rewrite Clauses

**Base rewrite (using generated function):**
```rust
rw_proc(s, t.clone()) <--
    proc(s),
    if let Some(t) = try_rewrite_rule_0(&s);
```

**Congruence from declared rule:** `if S => T then (PPar P S) => (PPar P T)`
```rust
rw_proc(s, t) <--
    proc(s),
    if let Proc::PPar(p, s0) = s,
    rw_proc(**s0, t0),
    let t = Proc::PPar(p.clone(), Box::new(t0.clone()));
```

**Congruence from declared rule:** `if S => T then (PNew x S) => (PNew x T)`
```rust
rw_proc(s, t) <--
    proc(s),
    if let Proc::PNew(scope) = s,
    let (x, p) = scope.clone().unbind(),
    rw_proc(*p, t0),
    let new_scope = mettail_runtime::Scope::new(x.clone(), Box::new(t0.clone())),
    let t = Proc::PNew(new_scope);
```

**Extension along equality:**
```rust
rw_proc(s1, t) <-- rw_proc(s0, t), eq_proc(s0, s1);
```

**Generation Algorithm:**

```rust
fn generate_rewrite_clauses(
    category: &Ident,  // e.g., "Proc"
    base_rewrites: &[RewriteRule],  // Rules without "if S => T" premise
    congruence_rewrites: &[RewriteRule],  // Rules with "if S => T" premise
) -> Vec<TokenStream> {
    let mut clauses = Vec::new();
    let cat_rel = format_ident!("{}", category.to_string().to_lowercase());
    let rw_rel = format_ident!("rw_{}", category.to_string().to_lowercase());
    let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());

    // Base rewrites (one per declared rewrite rule of this category)
    for (i, rule) in base_rewrites.iter().enumerate() {
        let fn_name = format_ident!("try_rewrite_rule_{}", i);
        clauses.push(quote! {
            #rw_rel(s, t.clone()) <--
                #cat_rel(s),
                if let Some(t) = #fn_name(&s);
        });
    }

    // Congruences (from explicitly declared congruence rules)
    for rule in congruence_rewrites {
        clauses.push(generate_congruence_clause(category, rule));
    }

    // Extension along equality
    clauses.push(quote! {
        #rw_rel(s1, t) <-- #rw_rel(s0, t), #eq_rel(s0, s1);
    });

    clauses
}

fn generate_congruence_clause(
    category: &Ident,
    rule: &RewriteRule  // Has "if S => T then (Constructor ... S ...) => (Constructor ... T ...)"
) -> TokenStream {
    // Parse LHS to find constructor and which field contains S
    // Generate Ascent clause that:
    // 1. Matches the constructor
    // 2. Recursively applies rw to that field
    // 3. Reconstructs with rewritten field
    // ... (similar to current rewrite_gen.rs logic)
}
```

---

## Revised Implementation Plan (4 Weeks)

The design is significantly simpler than originally planned because:
1. **Congruences are explicitly declared** (not auto-generated) - just parse and generate
2. **Relation naming is straightforward** - category relations unadorned, eq/rw relations per-category
3. **Pattern matching logic heavily reuses** `rewrite_gen.rs` infrastructure
4. **No complex multi-category rewrite coupling** - each category has its own typed relations

### Key Implementation Notes

**Rewrite Rule Numbering:**
- `try_rewrite_rule_N` functions are numbered globally (already generated by `rewrite_gen.rs`)
- Each theory has rules 0, 1, 2, ... in declaration order
- Ascent generation needs to determine which category each rule belongs to (from LHS type)
- Base rewrites reference the corresponding `try_rewrite_rule_N` function

**Category Determination:**
- Extract category from rewrite rule LHS (first constructor determines type)
- Group rules by category when generating `rw_cat` relations
- Congruence rules are identified by `if S => T then` premise (already parsed in AST)

### Phase 1: Core Infrastructure (Week 1)

**Goal:** Set up generation framework and basic structure.

**Tasks:**
- [ ] Create `macros/src/ascent_gen.rs`
- [ ] Define `generate_ascent_source(theory: &TheoryDef) -> TokenStream`
- [ ] Integrate into `lib.rs` (call from `theory!` macro)
- [ ] Generate relation declarations:
  - Category relations: `proc(Proc)`, `name(Name)`
  - Equality relations: `eq_proc(Proc, Proc)`, `eq_name(Name, Name)`
  - Rewrite relations: `rw_proc(Proc, Proc)`, `rw_name(Name, Name)`
- [ ] Test that generated `ascent_source!` block compiles

**Deliverable:**
```rust
pub fn theory(input: TokenStream) -> TokenStream {
    // ... existing code ...
    let ast_code = generate_ast(&theory_def);
    let rewrite_code = generate_rewrite_engine(&theory_def);
    let ascent_code = generate_ascent_source(&theory_def);  // NEW

    quote! {
        #ast_code
        #rewrite_code

        #ascent_code  // Generates full ascent_source! { ... } block
    }
}
```

---

### Phase 2: Category Relations (Week 2)

**Goal:** Generate term exploration (deconstruction) clauses.

**Tasks:**
- [ ] Implement `generate_category_relations()`
- [ ] For each category, generate `relation cat(Cat);`
- [ ] Generate expansion via `rw` and `eq`
- [ ] Generate deconstruction for non-binding constructors
- [ ] Test with simple theory (e.g., arithmetic)

**Test Case:**
```rust
theory! {
    name: Arith,
    exports { Expr },
    terms {
        Zero . Expr ::= "0";
        Succ . Expr ::= "S" "(" Expr ")";
        Plus . Expr ::= Expr "+" Expr;
    },
    equations {},
    rewrites {}
}
```

Expected generation:
```rust
relation expr(Expr);

// Deconstruction
expr(*e.clone()) <--
    expr(e0),
    if let Expr::Succ(e) = e0;
expr(*e1.clone()), expr(*e2.clone()) <--
    expr(e0),
    if let Expr::Plus(e1, e2) = e0;
```

---

### Phase 3: Equation Relations (Week 3)

**Goal:** Generate equality clauses from equations.

**Tasks:**
- [ ] Implement `generate_equation_relations()`
- [ ] Generate reflexivity, symmetry, transitivity
- [ ] Parse equation LHS patterns (reuse logic from `rewrite_gen.rs`)
- [ ] Generate equation clauses
- [ ] Handle nested patterns in LHS
- [ ] Test with commutative/associative theories

**Test Case:**
```rust
equations {
    (Plus X Y) == (Plus Y X);
    (Plus X (Plus Y Z)) == (Plus (Plus X Y) Z);
}
```

Expected generation:
```rust
relation eq_expr(Expr, Expr);

eq_expr(e, e) <-- expr(e);
eq_expr(e2, e1) <-- eq_expr(e1, e2);
eq_expr(e1, e3) <-- eq_expr(e1, e2), eq_expr(e2, e3);

eq_expr(e0, e1) <--
    expr(e0),
    if let Expr::Plus(x, y) = e0,
    let e1 = Expr::Plus(y.clone(), x.clone());

eq_expr(e0, e1) <--
    expr(e0),
    if let Expr::Plus(x, yz) = e0,
    if let Expr::Plus(y, z) = &**yz,
    let e1 = Expr::Plus(
        Box::new(Expr::Plus(x.clone(), y.clone())),
        z.clone()
    );
```

---

### Phase 4: Base Rewrite Relations (Week 4)

**Goal:** Generate base rewrite clauses (no congruences yet).

**Tasks:**
- [ ] Implement `generate_rewrite_relations()`
- [ ] Separate base rewrites from congruence rewrites (check for `if S => T` premise)
- [ ] Determine category for each rewrite rule (from LHS constructor)
- [ ] Group rules by category
- [ ] Generate base rewrite clauses (using `try_rewrite_rule_N`)
- [ ] Generate extension along equality
- [ ] Test with simple rewrite rules

**Test Case:**
```rust
rewrites {
    (Plus Zero X) => X;
}
```

Expected generation:
```rust
relation rw_expr(Expr, Expr);

rw_expr(s, t.clone()) <--
    expr(s),
    if let Some(t) = try_rewrite_rule_0(&s);

rw_expr(s1, t) <-- rw_expr(s0, t), eq_expr(s0, s1);
```

**Note:** Much simpler than original design - no auto-generated congruences!

**Important:** Need to track which `try_rewrite_rule_N` corresponds to which category.

---

### Phase 5: Congruence Rewrite Relations (Week 5)

**Goal:** Generate congruence clauses from explicitly declared congruence rules.

**Tasks:**
- [ ] Parse congruence rules (those with `if S => T then` premise)
- [ ] Identify constructor and field being rewritten from LHS pattern
- [ ] Generate recursive rewrite clause for non-binding constructors
- [ ] Generate recursive rewrite clause for binding constructors (unbind + rebind)
- [ ] Test with declared congruence rules

**Test Case:**
```rust
rewrites {
    (Plus Zero X) => X;
    if S => T then (Plus S Y) => (Plus T Y);  // Congruence for first field
    if S => T then (Lam x S) => (Lam x T);    // Congruence inside binder
}
```

Expected generation:
```rust
// Base rewrite
rw_expr(s, t.clone()) <--
    expr(s),
    if let Some(t) = try_rewrite_rule_0(&s);

// Congruence for Plus (first field)
rw_expr(s, t) <--
    expr(s),
    if let Expr::Plus(s0, y) = s,
    rw_expr(**s0, t0),
    let t = Expr::Plus(Box::new(t0.clone()), y.clone());

// Congruence for Lam (inside binder)
rw_expr(s, t) <--
    expr(s),
    if let Expr::Lam(scope) = s,
    let (x, body) = scope.clone().unbind(),
    rw_expr(*body, t0),
    let new_scope = mettail_runtime::Scope::new(x.clone(), Box::new(t0.clone())),
    let t = Expr::Lam(new_scope);
```

---

### Phase 4: Integration & Testing (Week 4)

**Goal:** Test with full theories (Ambient, Rholang).

**Tasks:**
- [ ] Enable congruence rules in theory definitions (uncomment in examples)
- [ ] Generate Ascent source for Ambient Calculus
- [ ] Generate Ascent source for Rho Calculus
- [ ] Compare generated code to hand-written versions
- [ ] Verify correctness (same rewrite paths)
- [ ] Update examples to use generated code exclusively
- [ ] Documentation and examples

**Success Criteria:**
- Generated Ascent code compiles
- Produces same rewrite paths as hand-written code
- Examples (ambient.rs, rholang.rs) work with 100% generated code
- No hand-written Ascent code needed

---

## Technical Challenges

### Challenge 1: Pattern Matching in Equations

**Problem:** Equation LHS can have nested patterns:
```rust
(PPar P (PPar Q R)) == (PPar (PPar P Q) R)
```

**Solution:** Reuse pattern matching logic from `rewrite_gen.rs`:
- `extract_variables_recursive()` to find all variables
- `generate_nested_patterns()` to create cascading `if let` statements
- Similar handling of bindings and field access

### Challenge 2: Congruence Parsing and Generation

**Problem:** Parse congruence rules and determine which field to rewrite.

**Solution:**
- Congruence rules have form: `if S => T then (Constructor ... S ...) => (Constructor ... T ...)`
- Parse LHS to find which argument position contains variable `S`
- Generate Ascent clause that matches constructor, recursively rewrites that field, and reconstructs

**Example:**

Input: `if S => T then (Plus S Y) => (Plus T Y)`

Generated:
```rust
rw_expr(s, t) <--
    expr(s),
    if let Expr::Plus(s0, y) = s,  // Match constructor
    rw_expr(**s0, t0),              // Recursively rewrite first field (S's position)
    let t = Expr::Plus(Box::new(t0.clone()), y.clone());  // Reconstruct
```

**Key insight:** The congruence rule explicitly specifies which field via variable position in the pattern!

### Challenge 3: Cross-Category Relations

**Problem:** Terms of one category can contain terms of another.

Example:
- `Proc` has `Name` fields
- Need both `rw_proc` and `rw_name` relations
- Congruence in `Proc` should trigger exploration of `Name` subterms

**Solution:**
- Generate relations for all exported categories (both category and per-category eq/rw)
- In deconstruction, extract subterms of different categories:
  ```rust
  proc(*p.clone()), name(*n.clone()) <--
      proc(p0),
      if let Proc::PAmb(n, p) = p0;
  ```
- Each category has its own typed rewrite relation (`rw_proc`, `rw_name`)
- Congruences don't cross categories - `rw_proc` recursively calls `rw_proc`, not `rw_name`
- Often only `rw_proc` will have rewrite rules (not `rw_name`), which is fine

### Challenge 4: Freshness Conditions in Equations

**Problem:** Equations can have freshness conditions:
```rust
if x # C then (PPar P (PNew x C)) == (PNew x (PPar P C))
```

**Solution:**
- Generate freshness checks in equation clauses (similar to rewrite_gen.rs)
- Use `is_fresh()` helper function
- Filter out equations where freshness fails

**Generated:**
```rust
eq_proc(p0, p1) <--
    proc(p0),
    if let Proc::PPar(p, pnew) = p0,
    if let Proc::PNew(scope) = &**pnew,
    let (x, c) = scope.clone().unbind(),
    if is_fresh(&x, &**p),  // Freshness check
    let inner = Proc::PPar(p.clone(), c.clone()),
    let new_scope = mettail_runtime::Scope::new(x.clone(), Box::new(inner)),
    let p1 = Proc::PNew(new_scope);
```

---

## Code Organization

### New File: `macros/src/ascent_gen.rs`

```rust
use crate::ast::{TheoryDef, GrammarRule, Equation, RewriteRule, Expr};
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

pub fn generate_ascent_source(theory: &TheoryDef) -> TokenStream {
    let theory_name = theory.name.to_string().to_lowercase();
    let source_name = format_ident!("{}_source", theory_name);

    let relations = generate_relations(theory);
    let category_rules = generate_category_rules(theory);
    let equation_rules = generate_equation_rules(theory);
    let rewrite_rules = generate_rewrite_rules(theory);

    quote! {
        ascent_source! {
            #source_name:

            #relations

            #category_rules

            #equation_rules

            #rewrite_rules
        }
    }
}

fn generate_relations(theory: &TheoryDef) -> TokenStream {
    let mut relations = Vec::new();

    // Category exploration relations
    for export in &theory.exports {
        let cat = &export.name;
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());
        relations.push(quote! { relation #cat_lower(#cat); });
    }

    // Equality relations (per-category)
    for export in &theory.exports {
        let cat = &export.name;
        let eq_rel = format_ident!("eq_{}", cat.to_string().to_lowercase());
        relations.push(quote! { relation #eq_rel(#cat, #cat); });
    }

    // Rewrite relations (per-category)
    for export in &theory.exports {
        let cat = &export.name;
        let rw_rel = format_ident!("rw_{}", cat.to_string().to_lowercase());
        relations.push(quote! { relation #rw_rel(#cat, #cat); });
    }

    quote! { #(#relations)* }
}

fn generate_relations(theory: &TheoryDef) -> TokenStream { ... }
fn generate_category_rules(theory: &TheoryDef) -> TokenStream { ... }
fn generate_equation_rules(theory: &TheoryDef) -> TokenStream { ... }
fn generate_rewrite_rules(theory: &TheoryDef) -> TokenStream { ... }
```

### Integration in `lib.rs`

```rust
mod ascent_gen;  // NEW
use ascent_gen::generate_ascent_source;  // NEW

#[proc_macro]
#[proc_macro_error]
pub fn theory(input: TokenStream) -> TokenStream {
    let theory_def = parse_macro_input!(input as TheoryDef);

    if let Err(e) = validate_theory(&theory_def) {
        let span = e.span();
        let msg = e.message();
        abort!(span, "{}", msg);
    }

    let ast_code = generate_ast(&theory_def);
    let rewrite_code = generate_rewrite_engine(&theory_def);
    let ascent_code = generate_ascent_source(&theory_def);  // NEW

    let grammar = generate_lalrpop_grammar(&theory_def);
    if let Err(e) = write_grammar_file(&theory_def.name.to_string(), &grammar) {
        eprintln!("Warning: Failed to write LALRPOP grammar: {}", e);
    }

    let combined = quote! {
        #ast_code
        #rewrite_code
        #ascent_code  // NEW
    };

    TokenStream::from(combined)
}
```

---

## Open Questions

### Q1: Should Ascent code be generated as `ascent_source!` or `ascent!`?

**Options:**
1. Generate `ascent_source!` block (named source for `include_source!`)
2. Generate `ascent!` block (inline program)
3. Generate Rust function returning string (for dynamic assembly)

**Recommendation:** Option 1 (named source)
- Allows users to compose with custom Ascent code
- Matches current usage pattern in examples
- More flexible for experimentation

### Q2: Should congruences be generated for ALL constructors or only those explicitly marked?

**Answer:** ✅ **RESOLVED** - Congruences are **explicitly declared** in `rewrites {}` using `if S => T then` syntax.
- Users write: `if S => T then (PPar P S) => (PPar P T)`
- Generator creates corresponding Ascent clause
- No auto-generation needed
- This is simpler and gives users full control

### Q3: How to handle equations vs rewrites?

**Answer:** ✅ **RESOLVED** - Keep separate
- Equations define equivalence classes (`eq` relation)
- Rewrites define directed reductions (`rw` relation)
- Rewrites extend along equality: `rw(s1,t) <-- rw(s0,t), eq(s0,s1)`
- Bidirectional rewrites would introduce redundant paths
- Allows different optimization strategies for `eq` vs `rw`

### Q4: Should we generate path-tracking relations?

**Answer:** ✅ **RESOLVED** - Not initially
- Current examples include `path` and `path_terminal` relations for debugging
- These are derived relations, not core semantics
- Can be added later as needed
- Users can manually add them to the generated source if needed

---

## Success Metrics

### Phase 1 Success (Week 1):
- [ ] Generated Ascent code compiles
- [ ] Relations declared for all categories
- [ ] `ascent_source!` block properly named

### Phase 2 Success (Week 2):
- [ ] Category deconstruction works
- [ ] Subterms properly explored
- [ ] Binding constructors unbind correctly

### Phase 3 Success (Week 3):
- [ ] Equations generate correct equality clauses
- [ ] Reflexivity/symmetry/transitivity work
- [ ] Nested patterns handled

### Phase 4 Success (Week 4):
- [ ] Base rewrites work
- [ ] Congruence rewrites work (from declared rules)
- [ ] Extension along equality works
- [ ] Ambient Calculus example works with generated code
- [ ] Rho Calculus example works with generated code
- [ ] Performance comparable to hand-written code

### Final Success Criteria:
- [ ] Zero hand-written Ascent code needed
- [ ] Examples (ambient.rs, rholang.rs) use 100% generated code
- [ ] Docs/examples updated
- [ ] All tests pass
- [ ] Generated code is readable and well-commented

---

## Future Enhancements

### 1. E-graph Integration (Phase 5)
- Use `egg` or `egglog` for equality saturation
- Replace `eq` relation with e-graph
- Much faster for large equational theories

### 2. Strategy Selection
- Generate different rewrite strategies (innermost, outermost, etc.)
- Allow user to choose via annotation
- Example: `@strategy(innermost)`

### 3. Optimization
- Detect when congruences are unnecessary (e.g., never match)
- Inline small equations
- Partial evaluation of rewrite patterns

### 4. Profiling/Debugging
- Generate trace output
- Count rewrite applications
- Identify bottlenecks

### 5. Parallel Exploration
- Generate parallel Ascent code
- Use multiple threads for large rewrite spaces

---

## Related Work

- **K Framework:** Auto-generates congruence rules, uses term rewriting
- **Maude:** Explicit congruence rules, conditional rewrite logic
- **Ascent:** Rust Datalog, designed for fixed-point computation
- **Souffle:** C++ Datalog, high-performance
- **Egglog:** E-graph + Datalog, excellent for equality reasoning

---

## Summary

This design extends mettail's code generation to include Ascent Datalog for exploring term rewrite spaces. The key insights are:

1. **Ascent programs for term rewriting have a highly regular structure:**
   - Category relations decompose terms into subterms
   - Equation relations define equivalence (reflexivity/symmetry/transitivity + equation clauses)
   - Rewrite relations apply base rules + declared congruences + extension along equality

2. **Congruences are explicitly declared, not auto-generated:**
   - Users write: `if S => T then (Constructor ... S ...) => (Constructor ... T ...)`
   - Generator parses these and creates corresponding Ascent clauses
   - Much simpler than auto-generating for all constructor fields!

3. **Implementation is straightforward:**
   - Reuse pattern matching logic from `rewrite_gen.rs`
   - 4-week timeline (down from original 6 weeks)
   - Clean separation of concerns

The end result: **users write only the theory definition** (including explicit congruence rules), and mettail generates everything needed to explore and analyze terms—including the Datalog code.

---

**Next Steps:**
1. Review this design with team
2. Get approval on architecture
3. Begin Phase 1 implementation
4. Iterate with testing and refinement

---

**Last Updated:** November 4, 2025
**Status:** Ready for review and implementation

