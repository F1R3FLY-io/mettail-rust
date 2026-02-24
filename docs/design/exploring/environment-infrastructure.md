# Environment Infrastructure Design

## Overview

This document analyzes the environment infrastructure from the `env_infrastructure` branch and outlines how to integrate it with our unified Pattern-based architecture.

## What the Old Environment Infrastructure Did

The `env_infrastructure` branch added automatic support for:

1. **Auto-generated `Assign` variant** for all categories
2. **Auto-generated `env_var_<category>` relations** for variable binding/lookup
3. **`TheoryNameCategoryEnv` struct** for storing variable→value bindings
4. **`parse_and_eval_with_env()` function** for parsing with environment context
5. **`has_var_ref_<category>()` helper** to detect unbound variables

### 1. Auto-Generated AST Variants

For each exported category, it automatically generated:

```rust
// For category Int with native type i64:
enum Int {
    // ... explicit constructors from theory ...
    NumLit(i64),           // Auto-generated literal variant
    IVar(OrdVar),          // Auto-generated variable variant  
    Assign(OrdVar, Box<Int>),  // Auto-generated assignment variant
}
```

### 2. Environment Relations

For each category, a Datalog relation was generated:

```rust
// For native types:
relation env_var_int(String, i64);

// For custom types:
relation env_var_proc(String, Proc);
```

These relations store `(variable_name, value)` pairs that can be seeded from an environment struct before running Ascent.

### 3. Environment Struct

For each category, a struct was generated:

```rust
pub struct CalculatorIntEnv {
    vars: HashMap<String, Int>,
}

impl CalculatorIntEnv {
    fn new() -> Self { ... }
    fn set(&mut self, name: String, value: Int) { ... }
    fn get(&self, name: &str) -> Option<Int> { ... }
    fn env_to_facts(&self) -> Vec<(String, Int)> { ... }
}
```

### 4. Parse and Evaluate with Environment

For native type categories, a function was generated:

```rust
pub fn parse_and_eval_with_env(
    input: &str,
    env: &mut CalculatorIntEnv,
) -> Result<i64, String> {
    // 1. Parse input to AST
    // 2. Convert env to facts: Vec<(String, i64)>
    // 3. Run Ascent with:
    //    - int(term.clone())
    //    - env_var_int(name, value) for each env entry
    // 4. Follow rewrite chain to normal form
    // 5. If assignment, update env
    // 6. Extract native value from result
}
```

### 5. Variable Substitution Rule

The key rewrite rule that enables variables:

```
// Declared in theory:
rewrites {
    if env_var(x, v) then (IVar x) => (NumLit v);
}
```

This is translated to:

```rust
rw_int(s, t) <--
    int(s),
    if let Int::IVar(x) = s,
    env_var_int(/* extract var name from x */, v),
    let t = Int::NumLit(v);
```

---

## Current State: What We Have

Our unified Pattern architecture already supports:

1. ✅ Auto-generated `NumLit(native_type)` variant for native types
2. ✅ Auto-generated `XVar(OrdVar)` variant for all categories
3. ✅ `generate_var_label()` and `generate_literal_label()` helpers
4. ✅ `is_var_rule()` and `is_integer_rule()` detection
5. ✅ Native type handling in Pattern code generation
6. ❌ No `Assign` variant auto-generation
7. ❌ No `env_var_<category>` relation generation
8. ❌ No environment struct generation
9. ❌ No `parse_and_eval_with_env()` generation

---

## Migration Plan

### Phase 1: Add Assign Variant (Required for Environments)

**File**: `macros/src/codegen/ast_gen.rs`

Add to `generate_ast_enums`:

```rust
// Check if Assign rule exists
let has_assign = has_assign_rule(cat_name, theory);
if !has_assign {
    variants.push(quote! {
        Assign(mettail_runtime::OrdVar, Box<#cat_name>)
    });
}
```

Also need:
- Substitution handling in `subst.rs`
- Display handling in `display.rs`
- Parser handling in `lalrpop.rs`

### Phase 2: Add Environment Relations

**File**: `macros/src/ascent/relations.rs`

Add `generate_env_relations()`:

```rust
fn generate_env_relations(theory: &TheoryDef) -> Vec<TokenStream> {
    let mut relations = Vec::new();
    
    for export in &theory.exports {
        let cat_lower = export.name.to_string().to_lowercase();
        let env_rel = format_ident!("env_var_{}", cat_lower);
        
        if let Some(native_type) = &export.native_type {
            relations.push(quote! {
                relation #env_rel(String, #native_type);
            });
        } else {
            let category = &export.name;
            relations.push(quote! {
                relation #env_rel(String, #category);
            });
        }
    }
    
    relations
}
```

### Phase 3: Add Environment Struct Generation

**File**: `macros/src/codegen/ast_gen.rs` or new `env.rs`

Generate:
- `TheoryNameCategoryEnv` struct
- `new()`, `set()`, `get()`, `clear()`, `env_to_facts()` methods
- `Default` impl

### Phase 4: Add Variable Substitution Rewrite

**Option A**: Explicit in theory definition:
```
rewrites {
    if env_var(x, v) then (IVar x) => (NumLit v);
}
```

**Option B**: Auto-generate for all categories with variables

Prefer **Option A** for transparency - users see exactly what rules exist.

### Phase 5: Add `parse_and_eval_with_env` Generation

For native type categories only:
1. Parse input to AST
2. Convert environment to Datalog facts
3. Run Ascent rewriting
4. Follow rewrite chain to normal form
5. Handle assignments (update env)
6. Extract native value

---

## Key Design Decisions

### 1. Relation Naming: `env_var_<category>` vs `env_var`

Use category-specific names (`env_var_int`, `env_var_proc`) to:
- Avoid type conflicts between categories
- Allow different value types per category
- Enable cross-category environments

### 2. Assign Semantics

`Assign(x, expr)` represents `x = expr`:
- LHS is always an `OrdVar` (variable)
- RHS is any expression of the same category
- After evaluation, RHS becomes a value in the environment

### 3. Environment Scope

Environments are per-category:
- `CalculatorIntEnv` for `Int` category
- `RhoCalcProcEnv` for `Proc` category
- This matches how Datalog relations work

### 4. Native vs Custom Type Handling

| Feature | Native (i64) | Custom (Proc) |
|---------|--------------|---------------|
| Env relation type | `env_var_int(String, i64)` | `env_var_proc(String, Proc)` |
| Value extraction | Direct | Pattern match |
| `parse_and_eval` | ✅ Returns native | ❌ Not generated |

---

## Example: Calculator with Environment

Theory definition:
```rust
theory! {
    name: Calculator,
    exports {
        ![i64] as Int
    },
    terms {
        Add . Int ::= Int "+" Int ;
        Sub . Int ::= Int "-" Int ;
        // IVar, NumLit, Assign auto-generated
    },
    rewrites {
        // Variable lookup
        if env_var(x, v) then (IVar x) => (NumLit v);
        
        // Congruence for Assign RHS
        if S => T then (Assign X S) => (Assign X T);
        
        // Congruence for Add/Sub
        if S => T then (Add S R) => (Add T R);
        if S => T then (Add L S) => (Add L T);
        if S => T then (Sub S R) => (Sub T R);
        if S => T then (Sub L S) => (Sub L T);
    },
}
```

Usage:
```rust
let mut env = CalculatorIntEnv::new();

// x = 5
let result = parse_and_eval_with_env("x = 5", &mut env)?;
assert_eq!(result, 5);
assert_eq!(env.get("x"), Some(Int::NumLit(5)));

// x + 3 (uses env to substitute x → 5)
let result = parse_and_eval_with_env("x + 3", &mut env)?;
assert_eq!(result, 8);
```

---

## Timeline

| Phase | Description | Effort |
|-------|-------------|--------|
| 1 | Assign variant generation | 2-3 hours |
| 2 | Environment relations | 1 hour |
| 3 | Environment struct | 1-2 hours |
| 4 | Variable substitution rule | 1 hour |
| 5 | `parse_and_eval_with_env` | 2-3 hours |

**Total**: ~8-10 hours of implementation work.

---

## Relationship to Multi-Communication

The environment infrastructure is **orthogonal** to multi-communication:

- **Environments**: Variable binding for stateful computation (calculator, REPL)
- **Multi-comm**: Collection pattern matching for process calculi (rho, ambient)

Both can be implemented independently. However, environments may be useful for rho-calculus "stores" in future work.
