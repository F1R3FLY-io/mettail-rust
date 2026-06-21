# Moniker Integration: Simplification Analysis

## What Can Be Eliminated/Simplified

### 1. ✅ **Scope Module** → REPLACE with Moniker's Scope

**Current:** `/macros/src/scope.rs`
```rust
pub struct Scope {
    bound_vars: HashSet<String>,
    free_vars: HashSet<String>,
}
```

**Status:** Can be **DELETED** - Moniker provides this automatically via:
- `Var::Free(...)` and `Var::Bound(...)`
- `BoundTerm::free_vars()` method
- Scoping handled by `Scope<P, T>::new()` and `unbind()`

---

### 2. ✅ **Substitution Module** → REPLACE with Moniker-based

**Current:** `/macros/src/substitution.rs`
```rust
pub trait Substitutable {
    fn substitute(&self, var: &str, value: &Self) -> Self;
}
```

**Status:** **ALREADY CLEARED** - Will regenerate using moniker's unbind/rebind:
```rust
impl Proc {
    pub fn substitute(&self, var: &FreeVar<String>, value: &Proc) -> Proc {
        match self {
            Proc::PInput(scope) => {
                let (binder, body) = scope.clone().unbind();
                Proc::PInput(Scope::new(binder, body.substitute(var, value)))
            }
            // ...
        }
    }
}
```

---

### 3. ⚠️ **Variable Validation** → SIMPLIFY

**Current:** `/macros/src/validator.rs`
```rust
fn collect_vars(expr: &Expr, vars: &mut HashSet<String>) { ... }
fn validate_equation_freshness(eq: &Equation) -> Result<...> { ... }
```

**Status:** **SIMPLIFY** - With moniker:
- Free variable checking: Use `BoundTerm::free_vars()`
- Freshness validation: Still needed, but simpler with `FreeVar<String>`

**Keep but simplify:**
```rust
fn validate_equation_freshness(eq: &Equation) -> Result<(), ValidationError> {
    // Just check that freshness variables appear in equation
    // Moniker handles the actual freshness at runtime
}
```

---

### 4. ⚠️ **TypeChecker** → KEEP but enhance for Var<String>

**Current:** `/macros/src/typechecker.rs`
```rust
fn infer_type_with_context(...) -> Result<String, ValidationError>
```

**Status:** **KEEP** - Type-checking still needed, but:
- Variables now have type `Var<String>`
- Binders have type `Binder<String>`
- Scopes have type `Scope<Binder<String>, Body>`

**Update type inference** to handle:
```rust
// New type cases:
Expr::Var(var) => Ok("Name".to_string())  // Variables have a category
Expr::Scope(scope) => {
    // Scope<Binder<Cat>, Body> where Body: BoundTerm
    infer_scope_type(scope)
}
```

---

### 5. ⚠️ **AST** → EXTEND (not eliminate)

**Current:** `/macros/src/ast.rs`
```rust
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
}
```

**Status:** **EXTEND** to add:
```rust
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
    Binder { category: Ident },  // NEW: <Cat>
}

pub struct GrammarRule {
    // ...
    pub bindings: Vec<(usize, Vec<usize>)>,  // NEW: binding structure
}
```

---

### 6. ⚠️ **CodeGen** → ENHANCE for Scope generation

**Current:** `/macros/src/codegen.rs`
```rust
fn generate_variant(rule: &GrammarRule) -> TokenStream { ... }
```

**Status:** **ENHANCE** to generate:
```rust
// For rules with binders:
PInput(Scope<Binder<String>, Box<Proc>>)

// For rules without binders:
PZero
PDrop(Name)
```

---

### 7. ✅ **Parser Generation** → KEEP (orthogonal to moniker)

**Current:** `/macros/src/parser_gen.rs`

**Status:** **KEEP** - Parser generates AST with `Scope::new()`:
```rust
// Parse: for(x){P}
// Generate:
let x_name = parse_identifier()?;  // "x"
let x_var = FreeVar::fresh_named(x_name);
let body = parse_proc()?;
Proc::PInput(Scope::new(Binder(x_var.clone()), body))
```

---

## Summary: What to Do

### DELETE
- [ ] `macros/src/scope.rs` - Replaced by moniker

### SIMPLIFY
- [ ] `macros/src/validator.rs` - Use `BoundTerm::free_vars()`
- [ ] `macros/src/substitution.rs` - Already cleared, will regenerate

### KEEP & ENHANCE
- [ ] `macros/src/ast.rs` - Add `Binder` grammar item
- [ ] `macros/src/codegen.rs` - Generate `Scope<...>` types
- [ ] `macros/src/typechecker.rs` - Handle `Var<String>` types
- [ ] `macros/src/parser_gen.rs` - Generate parsers using `Scope::new()`

### ADD
- [ ] Variable category handling - `Var<String>` as a special category

---

## Detailed Changes Needed

### 1. Delete scope.rs

```bash
rm macros/src/scope.rs
```

Remove from `lib.rs`:
```rust
mod scope;  // DELETE THIS LINE
```

### 2. Simplify validator.rs

```rust
// OLD:
fn collect_vars(expr: &Expr, vars: &mut HashSet<String>) {
    match expr {
        Expr::Var(v) => { vars.insert(v.to_string()); }
        Expr::Apply { func, args } => {
            collect_vars(func, vars);
            for arg in args { collect_vars(arg, vars); }
        }
    }
}

// NEW: (if needed at all)
// Just use the generated BoundTerm::free_vars() method
```

### 3. Update AST

```rust
// macros/src/ast.rs

#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
    Binder { category: Ident },  // NEW: <Cat> syntax
}

pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident,
    pub items: Vec<GrammarItem>,
    // NEW: Track which items are binders and what they bind in
    // e.g., [(0, vec![2])] means item 0 binds in item 2
    pub bindings: Vec<(usize, Vec<usize>)>,
}
```

### 4. Update CodeGen

```rust
// macros/src/codegen.rs

fn generate_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // Check if this rule has bindings
    if let Some((binder_idx, body_indices)) = rule.bindings.first() {
        // This is a binding constructor
        let binder_cat = get_category_at(rule, *binder_idx);
        let body = get_item_at(rule, body_indices[0]);

        quote! {
            #label(mettail_runtime::Scope<
                mettail_runtime::Binder<String>,
                Box<#body>
            >)
        }
    } else {
        // Regular constructor
        generate_regular_variant(rule)
    }
}
```

### 5. Update Parser Gen

```rust
// macros/src/parser_gen.rs

fn generate_binder_parse(rule: &GrammarRule) -> TokenStream {
    let (binder_idx, body_indices) = &rule.bindings[0];

    quote! {
        let var_name = self.parse_identifier()?;
        let var = mettail_runtime::FreeVar::fresh_named(var_name);
        // Parse body with var in scope
        let body = self.parse_body()?;
        // Create scope
        mettail_runtime::Scope::new(
            mettail_runtime::Binder(var.clone()),
            Box::new(body)
        )
    }
}
```

### 6. Update TypeChecker

```rust
// macros/src/typechecker.rs

fn infer_type(&self, expr: &Expr) -> Result<String, ValidationError> {
    match expr {
        Expr::Var(v) => {
            // Variables have their declared category
            self.get_var_type(v)
        }
        Expr::Apply { func, args } => {
            // Check constructor exists and infer result type
            self.infer_constructor_type(func, args)
        }
        // NEW: Handle scoped expressions if needed
    }
}
```

---

## Benefits of This Refactoring

1. **Simpler codebase**: Delete ~200 lines (scope.rs)
2. **Correct by construction**: Moniker handles capture-avoidance
3. **Battle-tested**: Using production-quality library
4. **Alpha-equivalence**: Free with `BoundTerm`
5. **Better errors**: Moniker's types are more precise

---

## Migration Path

### Step 1: Delete scope.rs ✅
- Remove file
- Remove from lib.rs

### Step 2: Update AST for binders
- Add `Binder` grammar item
- Add `bindings` field to rules
- Parse `<Cat>` syntax

### Step 3: Update CodeGen
- Generate `Scope<Binder<String>, Body>` for binding constructors
- Add `#[derive(BoundTerm)]` to generated enums

### Step 4: Update Parser Gen
- Generate code using `Scope::new()`
- Handle variable parsing

### Step 5: Update TypeChecker
- Handle `Var<String>` types
- Validate binding structure

### Step 6: Test
- Update examples to use new syntax
- Verify all tests pass
- Add Rho Calculus example

---

**Next:** Start with Step 1 (delete scope.rs) and Step 2 (update AST).

