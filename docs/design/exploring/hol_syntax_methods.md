# HOL-Based Method Specification: Design Document

**Date**: January 2026  
**Status**: Design Exploration  
**Related**: 

- [hol_syntax.md](hol_syntax.md) - HOL syntax specification
- [string_float_bool_methods.md](string_float_bool_methods.md) - String, float, and bool operation design
- [native_types_and_operations.md](../made/native_types_and_operations.md)

---

## Problem Statement

Semantics are defined in grammar rules using HOL syntax with native Rust code blocks (`![...]` in the `terms` section). This document focuses on:

- Integration of Rust code blocks (`![...]`) into HOL syntax
- Standard library import propagation to Rust code blocks
- Implementation details for code generation and type checking

For HOL syntax specification, see [hol_syntax.md](hol_syntax.md).  
For string, float, and bool operation requirements, see [string_float_bool_methods.md](string_float_bool_methods.md).

**Current Implementation:**

- Grammar rules in `terms` carry optional `rust_code` and `eval_mode`; evaluation and folding are generated from these.
- `macros/src/gen/native/eval.rs`: Generated `eval`/`try_eval` from rust_code in rules.
- `macros/src/logic/mod.rs`: Step and fold rule generation from rust_code.

**Constraints:**

- Type safety must be preserved at compile time
- Code generation must handle varying arities and return types
- Backward compatibility is not critical (breaking changes acceptable)

---

## Design Goals

1. **Native code integration** - Direct Rust code for implementations in grammar rules
2. **Import propagation** - Standard library and external crate imports available in Rust code blocks
3. **Type safety** - Compile-time validation of Rust code against parameter and return types
4. **Evaluation mode control** - Per-operation folding/congruence control
5. **Extensibility** - Support any Rust expression or method call

---

## Rust Code Block Integration

### Overview

HOL syntax allows embedding native Rust code directly in grammar rules using `![RustCode]` blocks. The code block has access to:

- Typed parameters from the rule's parameter list
- Standard library imports (via import propagation)
- External crate imports (via import propagation)

**Syntax Reference:** See [hol_syntax.md](hol_syntax.md) for complete HOL syntax specification.

**Example:**

```rust
Add . a:Int, b:Int |- a "+" b:Int ![a + b] fold;
```

The `![a + b]` block is parsed as a Rust expression and injected into the generated `eval()` method.

### Implementation

**AST Changes:**

```rust
pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident,
    pub parameters: Vec<TypedParameter>,
    pub items: Vec<GrammarItem>,
    pub return_type: Ident,
    pub rust_code: Option<RustCodeBlock>,  // NEW
    pub eval_mode: Option<EvalMode>,
}

pub struct RustCodeBlock {
    pub code: syn::Expr,  // Parsed Rust expression
}
```

**Code Generation:**

Rust code blocks are injected into `eval()` method generation:

```rust
fn generate_eval_method(category: &Ident, rules: &[GrammarRule], theory: &TheoryDef) -> TokenStream {
    let mut match_arms = Vec::new();
    
    for rule in rules {
        if let Some(ref rust_code) = rule.rust_code {
            let label = &rule.label;
            let param_names: Vec<_> = rule.parameters.iter().map(|p| &p.name).collect();
            
            // Generate parameter bindings: let param = arg.eval();
            let param_bindings: Vec<_> = param_names.iter()
                .map(|name| quote! { let #name = #name.as_ref().eval(); })
                .collect();
            
            match_arms.push(quote! {
                #category::#label(#(param_names),*) => {
                    #(#param_bindings)*
                    #rust_code.code
                }
            });
        }
    }
    
    quote! {
        pub fn eval(&self) -> #native_type {
            match self {
                #(#match_arms,)*
                _ => panic!("Cannot evaluate - missing implementation"),
            }
        }
    }
}
```

**Type Checking:**

Rust compiler validates:

- Parameter types match exported categories or native types
- Return type matches Rust code evaluation result
- All referenced types and methods are available

---

## Standard Library Import Design

### Problem Statement

Rust code blocks may require standard library imports (e.g., `std::collections::HashMap`, `std::time::Instant`) or external crates (e.g., `regex::Regex`). We need a mechanism to:

- Import modules at the theory or file level
- Propagate imports to all Rust code blocks within the theory
- Support both standard library and external crate imports
- Maintain namespace clarity and avoid conflicts

**Challenges:**

- Macro expansion context: imports must be injected into generated code
- Multiple theories: each theory may need different imports
- Namespace collisions: conflicting imports across theories
- Dependency management: external crates require Cargo.toml entries

---

### Design Options

#### Option 1: Theory-Level Import Block

**Syntax:**

```rust
theory! {
    name: TimedCalculator,
    imports {
        std::collections::HashMap,
        std::time::{Instant, Duration},
        regex::Regex,
    },
    exports {
        ![i64] as Int,
    },
    terms {
        CacheLookup . k:Str, cache:Cache 
            |- "lookup" "(" k "," cache ")":Int 
            ![cache.get(&k).copied().unwrap_or(0)] fold;
    }
}
```

**Implementation:**

- Add `imports` block to `TheoryDef` AST
- Store imports as `Vec<syn::ItemUse>`
- Generate `use` statements at the top of each code generation module
- Inject imports into Rust code block expansion context

**Pros:**

- Explicit and clear: imports visible at theory level
- Centralized: all imports in one place
- Scoped: imports specific to theory

**Cons:**

- Verbose: requires listing all imports explicitly
- Duplication: same imports may be needed across multiple theories
- Namespace pollution: imports affect entire generated module

**Risks:**

- Import conflicts: multiple theories with conflicting imports
- Missing dependencies: external crates not in Cargo.toml cause build errors

**Mitigation:**

- Validate imports at compile time
- Support qualified paths to avoid conflicts

---

#### Option 2: File-Level Imports with Propagation

**Syntax:**

```rust
// At top of theory file
use std::collections::HashMap;
use std::time::Instant;

theory! {
    name: TimedCalculator,
    exports {
        ![i64] as Int,
    },
    terms {
        CacheLookup . k:Str, cache:Cache 
            |- "lookup" "(" k "," cache ")":Int 
            ![cache.get(&k).copied().unwrap_or(0)] fold;
    }
}
```

**Implementation:**

- Parse `use` statements at file level (outside `theory!` macro)
- Store file-level imports in macro invocation context
- Propagate to all theories in the file
- Inject into generated code modules

**Pros:**

- Familiar Rust syntax: standard `use` statements
- DRY: shared imports across multiple theories in file
- Flexible: can use standard Rust import features (aliases, globs)

**Cons:**

- Complex parsing: must extract imports from surrounding code
- Ambiguity: unclear which imports apply to which theories
- Tooling: IDE may not recognize imports in macro context

**Risks:**

- Parsing complexity: extracting imports from token stream is fragile
- Context leakage: file-level imports affect all theories, potentially unintended
- Macro hygiene: standard Rust macro hygiene may interfere with import propagation

**Mitigation:**

- Use `proc_macro2::Span` to track import locations
- Validate import scope at code generation time

---

#### Option 3: Hybrid Approach (Recommended)

**Syntax:**

```rust
// File-level imports (propagate to all theories)
use std::collections::HashMap;
use std::time::Instant;

theory! {
    name: TimedCalculator,
    // Theory-specific imports (override/add to file-level)
    imports {
        regex::Regex,
        serde_json::Value,
    },
    exports {
        ![i64] as Int,
    },
    terms {
        // Can use HashMap, Instant, Regex, Value
        CacheLookup . k:Str, cache:Cache 
            |- "lookup" "(" k "," cache ")":Int 
            ![cache.get(&k).copied().unwrap_or(0)] fold;
    }
}
```

**Implementation:**

- Parse file-level `use` statements
- Parse theory-level `imports` block
- Merge imports: file-level + theory-level
- Resolve conflicts: theory-level overrides file-level
- Generate merged import list in code

**Pros:**

- Best of both: shared imports at file level, specific at theory level
- Flexible: supports common and specific use cases
- Clear precedence: theory-level overrides file-level

**Cons:**

- Most complex: two import mechanisms to maintain
- Overhead: import merging and conflict resolution
- Cognitive load: users must understand two import scopes

**Risks:**

- Conflict resolution: unclear behavior when same import exists at both levels
- Performance: import merging may slow down macro expansion
- Debugging: harder to trace import source (file vs theory)

**Mitigation:**

- Clear precedence rules: theory-level always wins
- Warning messages for overridden imports
- Debug mode to show import resolution

---

#### Option 4: Implicit Common Imports

**Syntax:**

```rust
theory! {
    name: TimedCalculator,
    exports {
        ![i64] as Int,
    },
    terms {
        // Common stdlib imports always available
        CacheLookup . k:Str, cache:Cache 
            |- "lookup" "(" k "," cache ")":Int 
            ![cache.get(&k).copied().unwrap_or(0)] fold;
    }
}
```

**Implementation:**

- Pre-populate import context with common standard library modules
- Provide mechanism to opt-out if needed
- No user-visible import syntax required

**Pros:**

- Minimal syntax: no explicit imports needed
- Convenient: common operations work out of the box
- Fast: no parsing overhead

**Cons:**

- Hidden behavior: imports not visible to user
- Limited: cannot use external crates without additional mechanism
- Bloat: may import unused modules

**Risks:**

- Namespace pollution: too many implicit imports may cause conflicts
- Surprise: users may not expect certain imports to be available
- Maintenance: must curate list of "common" imports

**Mitigation:**

- Limit implicit imports to most common modules (collections, time, etc.)
- Document implicit imports clearly
- Provide opt-out mechanism if needed

---

### Recommended Approach

**Option 3 (Hybrid Approach)** is recommended.

**Rationale:**

- File-level imports support shared dependencies across multiple theories
- Theory-level imports allow fine-grained control for specific needs
- Clear precedence rules (theory overrides file) reduce ambiguity
- Flexible enough to handle both common and specialized use cases

**Implementation Strategy:**

**Phase 1: Theory-Level Imports**

1. Add `imports` block to `TheoryDef` AST
2. Parse imports as `Vec<syn::ItemUse>`
3. Generate `use` statements in code generation modules
4. Inject imports into Rust code block context

**Phase 2: File-Level Import Propagation**

1. Parse file-level `use` statements from surrounding code
2. Store in macro invocation metadata
3. Merge with theory-level imports
4. Resolve conflicts (theory-level wins)

**Phase 3: Validation and Error Handling**

1. Validate import syntax at parse time
2. Check for missing dependencies in Cargo.toml
3. Detect and warn about import conflicts
4. Provide clear error messages

**Architectural Decisions:**

**Decision 1: Import Resolution Order**

- File-level imports are applied first
- Theory-level imports override file-level for same path
- Conflicts generate warnings, theory-level wins

**Decision 2: Qualified Path Support**

- Support both `use std::collections::HashMap` and `std::collections::HashMap::new()` in code
- Qualify paths in generated code if conflicts detected
- Provide namespace aliases if needed

**Decision 3: External Crate Support**

- Require external crates in Cargo.toml
- Validate crate availability at compile time
- Generate helpful error messages for missing dependencies

**Risks and Mitigations:**

**Risk 1: Import Parsing Complexity**

- **Risk:** Extracting imports from token stream is fragile
- **Mitigation:** Use `syn::ItemUse` parsing, comprehensive tests

**Risk 2: Namespace Conflicts**

- **Risk:** Multiple theories with conflicting imports
- **Mitigation:** Qualify paths in generated code, support aliases

**Risk 3: Macro Hygiene**

- **Risk:** Standard Rust macro hygiene may interfere with imports
- **Mitigation:** Use `quote!` with proper span tracking, test thoroughly

**Risk 4: Performance Impact**

- **Risk:** Import parsing and merging adds overhead
- **Mitigation:** Cache parsed imports, optimize merge algorithm

---

### Example Usage

**File-level imports with theory-specific additions:**

```rust
// Shared imports for all theories in this file
use std::collections::HashMap;
use std::time::Instant;

theory! {
    name: TimedCalculator,
    // Theory-specific imports
    imports {
        regex::Regex,
    },
    exports {
        ![i64] as Int,
        ![String] as Str,
    },
    terms {
        // Can use HashMap, Instant, Regex
        TimedAdd . a:Int, b:Int 
            |- "timed_add" "(" a "," b ")":Int 
            ![{
                let start = Instant::now();
                let result = a + b;
                result
            }] fold;
        
        RegexMatch . s:Str, pattern:Str 
            |- "match" "(" s "," pattern ")":Bool 
            ![Regex::new(&pattern).unwrap().is_match(&s)] fold;
    }
}

theory! {
    name: CacheCalculator,
    // Inherits file-level imports (HashMap, Instant)
    exports {
        ![i64] as Int,
    },
    terms {
        // Can use HashMap, Instant
        CachedAdd . a:Int, b:Int, cache:Cache 
            |- "cached_add" "(" a "," b "," cache ")":Int 
            ![{
                let key = format!("{}+{}", a, b);
                *cache.entry(key).or_insert_with(|| a + b)
            }] fold;
    }
}
```

---

## Type System Integration

### Parameter Type Resolution

**Rules:**

1. If parameter type matches an exported category → use that category's native type
2. If parameter type is a native Rust type (`i64`, `String`, `bool`, etc.) → use directly
3. Type checking: compiler validates parameter types match grammar production

**Example:**

```rust
exports {
    ![i64] as Int,
    ![String] as Str,
}

terms {
    // a:Int resolves to i64 (from export)
    Add . a:Int, b:Int |- a "+" b:Int ![a + b] fold;
    
    // Can also use native types directly
    AddNative . a:i64, b:i64 |- a "+" b:Int ![a + b] fold;
}
```

### Return Type Validation

**Rules:**

1. Return type must match an exported category
2. Rust code must evaluate to the native type of that category
3. Compiler validates type correctness at code generation time

**Example:**

```rust
exports {
    ![i64] as Int,
    ![bool] as Bool,
}

terms {
    // Return type Bool, Rust code must return bool
    Eq . a:Int, b:Int |- a "==" b:Bool ![a == b] fold;
    
    // Compiler error if types don't match
    // Eq . a:Int, b:Int |- a "==" b:Int ![a == b] fold;  // ERROR: bool != i64
}
```

For detailed discussion of cross-type operations, see [string_float_bool_methods.md](string_float_bool_methods.md).

---

## Implementation Phases

### Phase 1: Core HOL Syntax with Rust Code Blocks

**Scope:** Basic HOL syntax parsing and Rust code block integration.

**Changes:**

1. Extend `GrammarRule` AST with parameters, return type, Rust code, eval mode
2. Update parser to recognize HOL syntax (see [hol_syntax.md](hol_syntax.md))
3. Generate `eval()` method from Rust code blocks
4. Support basic evaluation modes

**Timeline:** 3-4 days

**Files:**

- `macros/src/ast/types.rs`: AST extensions
- `macros/src/codegen/ast_gen.rs`: Code generation updates
- `macros/src/ascent/mod.rs`: Rule generation updates

### Phase 2: Type System Integration

**Scope:** Full type checking and validation.

**Changes:**

1. Parameter type resolution (category → native type)
2. Return type validation
3. Rust code type checking
4. Compiler error messages for type mismatches

**Timeline:** 2-3 days

**Files:**

- `macros/src/validation/typechecker.rs`: Type checking updates

### Phase 3: Evaluation Modes

**Scope:** Full evaluation mode support.

**Changes:**

1. Generate constant folding rules for `fold` and `both` modes
2. Generate congruence rules for `step` and `both` modes
3. Per-operation mode control

**Timeline:** 2 days

**Files:**

- `macros/src/ascent/mod.rs`: Mode-aware rule generation

### Phase 4: Standard Library Import Support

**Scope:** Theory-level and file-level import propagation.

**Changes:**

1. Add `imports` block to `TheoryDef` AST
2. Parse file-level `use` statements from surrounding code
3. Merge imports (file-level + theory-level)
4. Inject imports into generated code modules
5. Validate imports and check for missing dependencies

**Timeline:** 3-4 days

**Files:**

- `macros/src/ast/types.rs`: `imports` field in `TheoryDef`
- `macros/src/codegen/ast_gen.rs`: Import injection in code generation
- `macros/src/validation/validator.rs`: Import validation

### Phase 5: Advanced Features

**Scope:** Error handling, method chaining, complex operations.

**Changes:**

1. Support `Result<T, E>` return types
2. Enhanced error messages
3. Documentation and examples

**Timeline:** 2-3 days

---

## Architectural Decisions

### Decision 1: Rust Code Block Syntax

**Decision:** Use `![RustCode]` syntax for native code blocks.

**Rationale:**

- Distinctive syntax clearly marks native code
- Brackets provide clear boundaries
- Exclamation mark indicates "native" or "raw" code

**Alternative Considered:** `{RustCode}` or `|RustCode|`. Rejected due to potential conflicts with grammar syntax.

### Decision 2: Import Propagation Strategy

**Decision:** Hybrid approach with file-level and theory-level imports.

**Rationale:**

- Supports both shared and specific import needs
- Clear precedence rules reduce ambiguity
- Flexible enough for common and specialized cases

**Alternative Considered:** Theory-level only. Rejected due to verbosity for shared imports.

### Decision 3: Type Validation Strategy

**Decision:** Leverage Rust compiler for type checking.

**Rationale:**

- Compiler provides comprehensive type checking
- No need to reimplement type system
- Clear error messages from compiler

**Alternative Considered:** Custom type checker. Rejected due to complexity and maintenance burden.

---

## Risks and Mitigations

### Risk 1: Parsing Complexity

**Risk:** HOL syntax with Rust code blocks may be difficult to parse correctly.

**Mitigation:**

- Use Rust's `syn` crate for robust parsing
- Comprehensive test cases for edge cases
- Clear error messages for syntax errors

### Risk 2: Type Checking Complexity

**Risk:** Validating Rust code types against parameter and return types is complex.

**Mitigation:**

- Leverage Rust compiler for type checking
- Generate code that compiler can validate
- Provide clear error messages pointing to mismatches

### Risk 3: Import Propagation Complexity

**Risk:** Extracting and propagating imports from file context is fragile.

**Mitigation:**

- Use `syn::ItemUse` for reliable parsing
- Comprehensive tests for import scenarios
- Clear error messages for missing or conflicting imports

### Risk 4: Macro Hygiene

**Risk:** Standard Rust macro hygiene may interfere with import propagation.

**Mitigation:**

- Use `quote!` with proper span tracking
- Test thoroughly with various import scenarios
- Document limitations clearly

---

## Recommendation

**Recommended Approach: HOL-Based Syntax with Hybrid Import Strategy**

**Rationale:**

- Unified syntax: grammar and semantics in one place
- Native code: direct Rust implementation
- Flexible imports: file-level for shared, theory-level for specific
- Type safety: compiler validates all code

**Implementation Strategy:**

1. Phase 1: Core HOL syntax parsing and code generation
2. Phase 2: Type system integration and validation
3. Phase 3: Evaluation mode support
4. Phase 4: Standard library import support
5. Phase 5: Advanced features (error handling, etc.)

**Success Criteria:**

- All string, float, and bool operations supported (see [string_float_bool_methods.md](string_float_bool_methods.md))
- Type safety preserved at compile time
- Clear, readable syntax (see [hol_syntax.md](hol_syntax.md))
- Standard library imports work correctly
- Evaluation modes work correctly

---

