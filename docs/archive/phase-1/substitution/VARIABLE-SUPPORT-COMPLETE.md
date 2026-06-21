# Variable Support - Implementation Complete

## Summary

We've successfully implemented variable support in MeTTaIL, making `Var` a built-in type that can be used in grammar rules without requiring explicit export. Variables are represented using `moniker`'s `Var<String>` type, which provides automatic handling of free and bound variables.

## Changes Made

### 1. Validator Updates (`macros/src/validator.rs`)

**Key Change**: Modified category validation to distinguish between:
- **Exported categories**: Result types that the theory exposes to the outside world
- **Defined categories**: Result types from any rule (may or may not be exported)
- **Built-in types**: `Var` and other special types that don't need to be defined

**Before**: Required all non-terminal references to be exported categories.

**After**: Allow non-terminals to reference:
1. Exported categories, OR
2. Defined (result) categories, OR
3. Built-in types like `Var`

```rust
// Build set of all defined categories (result types from all rules)
let defined: HashSet<_> = theory.terms
    .iter()
    .map(|r| r.category.to_string())
    .collect();

// Check that all non-terminal items reference valid categories
for item in &rule.items {
    match item {
        GrammarItem::NonTerminal(ident) => {
            let ref_name = ident.to_string();
            // Built-in types are always valid
            if ref_name == "Var" {
                continue;
            }
            // Must be either exported or defined (or both)
            if !exported.contains(&ref_name) && !defined.contains(&ref_name) {
                return Err(...);
            }
        }
        // ... handle Binder similarly
    }
}
```

### 2. Code Generation Updates (`macros/src/codegen.rs`)

**Key Change**: Special handling for `Var` fields in generated enum variants.

When a rule uses `Var` as a non-terminal (e.g., `EVar . Expr ::= Var ;`), we generate:
```rust
EVar(mettail_runtime::Var<String>)
```

Not `Box<Var>` like other non-terminals, since `Var` is a built-in type from `moniker`.

```rust
} else if fields.len() == 1 && fields[0].to_string() == "Var" {
    // Special case: Var field -> generate Var<String> directly (not boxed)
    quote! { #label(mettail_runtime::Var<String>) }
}
```

**Also Added**: `PartialEq` and `Eq` derives to generated enums for testing support:
```rust
#[derive(Debug, Clone, PartialEq, Eq, mettail_runtime::BoundTerm)]
pub enum #cat_name { ... }
```

### 3. Parser Generation Updates (`macros/src/parser_gen.rs`)

**Key Changes**:
1. Skip parser generation for rules that reference `Var` (placeholder for future implementation)
2. Skip parser generation for rules without terminals (can't be parsed unambiguously)

```rust
// Special handling for built-in Var type
if cat.to_string() == "Var" {
    // For rules that use Var, we skip parser generation for now
    return (vec![], vec![], vec![]);
}

// Check if rule has at least one terminal
let has_terminal = rule.items.iter().any(|item| matches!(item, GrammarItem::Terminal(_)));
if !has_terminal {
    return quote! {
        // TODO: Parser for rule #label (no terminals) not yet implemented
    };
}
```

## Usage Example

```rust
theory! {
    name: LambdaCalc,

    exports {
        Expr
    },

    terms {
        // Variable - uses Var<String> from moniker
        EVar . Expr ::= Var ;

        // Lambda with binder
        ELam . Expr ::= "\\" <Var> "." Expr ;

        // Application
        EApp . Expr ::= Expr Expr ;
    }
}

// Usage in tests:
use mettail_runtime::{FreeVar, Binder, Scope, Var};

// Create a free variable
let x: FreeVar<String> = FreeVar::fresh_named("x");
let var_expr = Expr::EVar(Var::Free(x.clone()));

// Create a lambda: \x.x (identity function)
let body = Expr::EVar(Var::Free(x.clone()));
let lambda = Expr::ELam(Scope::new(
    Binder(x.clone()),
    Box::new(body)
));
```

## Generated Code

For the above `LambdaCalc` theory, MeTTaIL generates:

```rust
#[derive(Debug, Clone, PartialEq, Eq, mettail_runtime::BoundTerm)]
pub enum Expr {
    EVar(mettail_runtime::Var<String>),
    ELam(mettail_runtime::Scope<mettail_runtime::Binder<String>, Box<Expr>>),
    EApp(Box<Expr>, Box<Expr>),
}
```

## Key Design Decisions

### 1. Why `Var` is Built-in

Variables are fundamental to binding and scoping, which are core features of MeTTaIL. Making `Var` a built-in type:
- Simplifies theory definitions (no need to explicitly define or export `Var`)
- Ensures consistency across all theories using variables
- Leverages `moniker`'s robust implementation of locally nameless representation

### 2. Distinction Between Exported and Defined Categories

This change allows theories to use "internal" categories that aren't exposed in the public API:
- **Exported categories** define the theory's interface
- **Defined categories** can be used internally without cluttering the exports
- **Built-in types** like `Var` are always available

This is analogous to public vs. private types in module systems.

### 3. Parser Generation Strategy

For now, we skip generating parsers for:
- Rules using `Var` (requires variable name parsing, which needs more design)
- Rules without terminals (ambiguous without lookahead)

This is marked as TODO for Phase 2, when we integrate with LALRPOP or another proper parser generator.

## Testing

All tests pass successfully:

**Library tests** (`macros`):
- 19 unit tests pass
- 1 compile-fail integration test passes
- 2 ignored tests (unused old tests)

**Example tests**:
- `test_variables.rs`: Creates variables and lambdas with bindings ✓
- `test_moniker.rs`: Tests moniker integration with lambda calculus ✓
- `test_scope_gen.rs`: Verifies `Scope` generation ✓
- `simple_monoid.rs`: Tests basic theory without variables ✓
- `quote_drop.rs`: Tests Rho calculus quote/drop ✓

## Output from Variable Tests

```
Created variable expression: EVar(Free(FreeVar { unique_id: UniqueId(1), pretty_name: Some("x") }))

Created lambda: ELam(Scope {
    unsafe_pattern: Binder(FreeVar { unique_id: UniqueId(0), pretty_name: Some("x") }),
    unsafe_body: EVar(Bound(BoundVar { scope: ScopeOffset(0), binder: BinderIndex(0), pretty_name: Some("x") }))
})
```

Notice how `moniker` automatically converts the free variable `x` to a bound variable when it's used inside the `Scope`!

## Next Steps

With variable support complete, we can now proceed to:

1. **Rewrite Rules** (TODO #11): Parse and validate rewrite rules that use substitution
2. **Rho Calculus Implementation** (TODO #12, #18): Implement communication as a rewrite involving substitution
3. **Documentation** (TODO #9): Document the complete Phase 1 implementation

## Related Documents

- [MONIKER-SUCCESS.md](MONIKER-SUCCESS.md) - Successful moniker integration
- [BINDER-SYNTAX-CORRECTED.md](BINDER-SYNTAX-CORRECTED.md) - Corrected binder syntax
- [VARIABLE-SUPPORT-PLAN.md](VARIABLE-SUPPORT-PLAN.md) - Original plan for variable support
- [PHASE-1-PLAN.md](PHASE-1-PLAN.md) - Overall Phase 1 roadmap

