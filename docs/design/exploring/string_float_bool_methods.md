# String, Float, and Bool Method Specification: Design Options

**Date**: January 2026  
**Status**: Design Exploration  
**Related**: [native_types_and_operations.md](../made/native_types_and_operations.md)

---

## Problem Statement

The current semantics system supports only binary arithmetic operators (`+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `<<`, `>>`) for `i32`/`i64` types. We need to extend support for:

- String operations: concatenation, length, substring, case conversion, comparison
- Float operations: arithmetic, trigonometric functions, comparison
- Bool operations: logical AND/OR/NOT, comparison
- Cross-type operations: operations returning different types (e.g., `int == int` → `bool`)
- Unary operations: negation, length, trigonometric functions
- Custom methods: user-defined or standard library methods

**Current Implementation:**
- `macros/src/ast/types.rs`: `SemanticRule` with `BuiltinOp` enum (10 operators)
- `macros/src/codegen/ast_gen.rs`: Hardcoded operator token generation in `eval()`
- `macros/src/ascent/mod.rs`: Constant folding rule generation

**Constraints:**
- Type safety must be preserved at compile time
- Code generation must handle varying arities and return types
- Backward compatibility is not critical (breaking changes acceptable)

---

## Design Goals

1. **Minimal boilerplate** for common operations
2. **Progressive complexity** from simple operators to custom implementations
3. **Type safety** with compile-time validation
4. **Extensibility** for future operation types
5. **Clarity and explicitness** in method specification

---

## Design Options

### Option 1: Extended BuiltinOp Enum

**Approach:** Extend the existing `BuiltinOp` enum with predefined operators for strings, floats, and bools.

**Syntax:**
```rust
semantics {
    Add: +,
    Concat: ++,        // String concatenation
    Length: |s|,       // String length (unary)
    And: &&,           // Bool AND
    Not: !,            // Bool NOT (unary)
    Eq: ==,            // Comparison (returns bool)
    Sin: sin,          // Float math (unary)
}
```

**Implementation:**
- Extend `BuiltinOp` enum with 20-30 new variants
- Parser recognizes new operator tokens (`++`, `&&`, `||`, `!`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `sin`, `cos`, etc.)
- Code generation handles unary vs binary based on rule arity
- Return type inference: comparison operators → `bool`, others → input type

**Pros:**
- Minimal implementation effort (extend existing infrastructure)
- Familiar operator syntax for users
- Compile-time type checking via enum variants
- Zero runtime overhead (direct operator calls)

**Cons:**
- Limited to predefined operations (enum must be extended for new operations)
- Cannot leverage standard library methods directly
- Enum grows large and becomes maintenance burden
- No user extensibility without modifying core code
- Perpetuates existing limitations of enum-based approach

**Risks:**
- Enum bloat: adding every possible operation makes the enum unwieldy
- Incomplete coverage: some operations may be missing, forcing workarounds
- Maintenance: new Rust stdlib methods require enum updates

**Decision Criteria:** Suitable if we can identify a fixed, small set of common operations that cover 80% of use cases.

---

### Option 2: Method Path Syntax

**Approach:** Allow specifying Rust method paths (e.g., `String::push_str`, `str::len`) directly in semantics.

**Syntax:**
```rust
semantics {
    Add: +,                           // Operator shorthand
    Concat: String::push_str,         // Method on type
    Length: str::len,                // Associated function
    ToString: i32::to_string,        // Cross-type conversion
    Sin: f64::sin,                    // Float math
    ParseInt: str::parse::<i32>,      // Generic method with type param
}
```

**Implementation:**
- Replace or extend `SemanticOperation` enum:
  ```rust
  pub enum SemanticOperation {
      Builtin(BuiltinOp),              // Optional: for operator shorthand
      MethodPath(syn::Path),            // e.g., String::push_str
      FunctionName(syn::Ident),         // user-defined function
  }
  ```
- Parser: if token is operator → `Builtin`, if path-like → `MethodPath`, else → `FunctionName`
- Code generation: emit direct method calls with proper argument extraction
- Type checking: compiler validates method existence and signature

**Pros:**
- Direct access to entire Rust standard library
- Type-safe: compiler validates method signatures
- Self-documenting: method path indicates implementation
- Extensible: users can define custom functions
- No enum maintenance: new stdlib methods work automatically

**Cons:**
- More verbose than operators
- Requires knowledge of Rust method names
- Generic methods need explicit type parameters (`str::parse::<i32>`)
- Parser complexity: must distinguish paths from identifiers and operators
- Potential ambiguity: `str::len` vs `String::len` (different signatures)

**Risks:**
- Method signature mismatches: user specifies wrong method, compiler error at codegen time
- Generic method inference: type parameters may be ambiguous
- Method chaining: cannot express `s.trim().to_uppercase()` directly

**Decision Criteria:** Suitable if we want maximum flexibility with standard library integration and are willing to accept verbosity.

---

### Option 3: Lambda/Expression Syntax

**Approach:** Allow inline Rust expressions (closures) for semantic operations.

**Syntax:**
```rust
semantics {
    Add: +,                                    // Operator shorthand
    Concat: |a: String, b: String| -> String { format!("{}{}", a, b) },
    Length: |s: String| -> i64 { s.len() as i64 },
    Substring: |s, start, len| s.get(start..start+len).unwrap_or(""),
    ParseInt: |s: String| -> Result<i64, _> { s.parse() },
    Sin: |x: f64| -> f64 { x.sin() },
}
```

**Implementation:**
- Extend `SemanticOperation`:
  ```rust
  pub enum SemanticOperation {
      Builtin(BuiltinOp),
      Lambda {
          params: Vec<(syn::Ident, Option<syn::Type>)>,
          return_type: Option<syn::Type>,
          body: syn::Expr,
      },
  }
  ```
- Parser: recognize lambda syntax `|params| -> ReturnType { body }` or `|params| expr`
- Code generation: emit closure and invoke in `eval()` method
- Type inference: optional type annotations, infer from context

**Pros:**
- Maximum flexibility: any Rust code can be expressed
- Complex operations: error handling, multiple statements, method chaining
- Type inference: optional annotations reduce verbosity
- Error handling: supports `Result<T, E>` return types

**Cons:**
- Most verbose syntax
- Requires Rust expertise from users
- Complex parsing: full expression parsing needed
- Less declarative: looks like implementation rather than specification
- Potential security: arbitrary code execution in macro context (mitigated by compile-time only)

**Risks:**
- Parsing complexity: Rust expression grammar is complex, may conflict with theory syntax
- Error messages: compiler errors in lambda bodies may be cryptic
- Performance: closure overhead (minimal, but exists)
- Code bloat: large lambda bodies increase generated code size

**Decision Criteria:** Suitable for complex operations, error handling, or when standard methods are insufficient.

---

### Option 4: Hybrid Approach (Recommended)

**Approach:** Combine all three options with clear precedence: operators for common cases, method paths for standard library, lambdas for complex cases.

**Syntax:**
```rust
semantics {
    // 1. Operator shorthand (most common)
    Add: +,
    Concat: ++,
    And: &&,
    Eq: ==,
    
    // 2. Method path (standard library)
    Length: str::len,
    ToUpper: String::to_uppercase,
    Sin: f64::sin,
    
    // 3. Lambda (custom/complex)
    Format: |fmt, val| format!(fmt, val),
    ParseFloat: |s: String| -> Result<f64, _> { s.parse() },
}
```

**Implementation Strategy:**
- Phase 1: Extend `BuiltinOp` with common operators (`++`, `&&`, `||`, `!`, `==`, `!=`, `<`, `>`, `<=`, `>=`)
- Phase 2: Add `MethodPath` variant, parse path syntax
- Phase 3: Add `Lambda` variant, parse lambda expressions

**Pros:**
- Progressive complexity: users choose appropriate syntax
- Covers all use cases: simple to complex operations
- Optimal for each case: operators for speed, methods for clarity, lambdas for flexibility
- Flexible migration: can adopt new syntax incrementally

**Cons:**
- More implementation work: three syntaxes to support
- Parser precedence: must decide parsing order (operators → paths → lambdas)
- Documentation burden: must explain when to use each syntax
- Cognitive load: users must understand three different syntaxes

**Risks:**
- Syntax ambiguity: `sin` could be operator, method, or identifier
- Migration path: users may not know which syntax to use
- Maintenance: three code paths to maintain and test

**Mitigation:**
- Clear parsing precedence: try operator first, then path, then lambda
- Comprehensive examples in documentation
- Linter suggestions: recommend simpler syntax when possible

**Decision Criteria:** Recommended if we want to support the full spectrum of use cases while maintaining simplicity for common operations.

---

### Option 5: Declarative DSL

**Approach:** Explicit method specification with type signatures and implementation details.

**Syntax:**
```rust
semantics {
    Concat {
        op: ++,
        types: (String, String) -> String,
        impl: String::push_str,
        mode: fold,
    },
    Length {
        op: |s|,
        types: (String) -> i64,
        impl: str::len,
    },
}
```

**Implementation:**
- Structured AST with explicit type signatures
- Type validation: check signature matches implementation
- Evaluation mode control: per-operation folding/congruence control

**Pros:**
- Explicit types: self-documenting, enables validation
- Evaluation mode: fine-grained control per operation
- Type safety: can validate signatures before code generation
- Structured: clear separation of concerns (operator, types, implementation, mode)
- Extensible: easy to add new fields (e.g., error handling strategy)

**Cons:**
- Most verbose syntax
- Complex parser: structured syntax requires more parsing logic
- Learning curve: users must understand structured format

**Risks:**
- Adoption barrier: verbosity may discourage use for simple cases
- Over-engineering: may be too complex for common operations

**Decision Criteria:** Suitable if we prioritize explicitness, validation, and structured specification over conciseness. Since backward compatibility is not critical, this option becomes more viable.

---

## Cross-Type Operations

### Problem

Operations like `int == int` return `bool`, not `int`. Current system assumes return type matches input type.

### Solution Options

**Option A: Return Type Detection**
- Hardcode return types for known operators (comparisons → `bool`)
- Pros: Automatic, no syntax changes
- Cons: Limited to predefined operators, not extensible

**Option B: Explicit Return Type Annotation**
- Syntax: `Eq: == -> bool`
- Pros: Explicit and clear
- Cons: Additional syntax, must specify for every cross-type operation

**Option C: Rule Category Determines Return Type (Recommended)**
- The rule's category in `terms` block determines return type
- Example: `Eq . Bool ::= Int "==" Int` means `Eq` returns `Bool`
- Pros: Type-safe, explicit, consistent with existing system
- Cons: Requires separate category for return type (e.g., `Bool` category)

**Decision:** Option C. The rule's category already serves as the return type in the type system. This is the most architecturally consistent approach and requires no syntax changes.

---

## Unary Operations

### Problem

Current code generation only handles binary operations. Need support for unary: `!`, `-`, `|s|`, `sin`, etc.

### Solution

Extend code generation to detect arity from grammar rule:

```rust
let arg_count = rule.items.iter()
    .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
    .count();

match arg_count {
    1 => generate_unary_eval(op, category, label),
    2 => generate_binary_eval(op, category, label),
    _ => generate_nary_eval(op, category, label, arg_count),
}
```

**Implementation Notes:**
- Unary operations: `!val`, `-val`, `val.sin()`, `val.len()`
- Type preservation: unary operations typically preserve type (except conversions)
- Error handling: unary operations may fail (e.g., `sqrt` of negative number)

**Risk:** Arity detection from grammar may be incorrect if rule has optional or variadic arguments. Mitigation: validate arity matches semantic operation expectations.

---

## Type-Specific Operations

### String Operations

**Required Operations:**
- Concatenation: `++` operator or `String::push_str`
- Length: `|s|` operator or `str::len` (returns `i64`)
- Substring: `String::get` or lambda with range slicing
- Case conversion: `String::to_uppercase`, `String::to_lowercase`
- Trim: `str::trim`
- Contains: `str::contains` (returns `bool`)

**Design Decision:** Start with operator syntax for common operations (`++`, `|s|`), use method paths for less common operations. This balances conciseness with flexibility.

### Float Operations

**Required Operations:**
- Arithmetic: reuse `+`, `-`, `*`, `/` operators (type-specific via category)
- Math functions: `f64::sin`, `f64::cos`, `f64::tan`, `f64::sqrt`, etc.
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=` (return `bool`)

**Special Considerations:**
- Precision: f32 vs f64 choice affects accuracy and performance
- NaN/Infinity: error handling strategy (panic vs Result)
- Type promotion: `int + float` requires explicit conversion (see Type Coercion)

**Design Decision:** Use method paths for math functions (`f64::sin`) to leverage standard library. Arithmetic and comparison use operators for consistency.

### Bool Operations

**Required Operations:**
- Logical AND: `&&` operator
- Logical OR: `||` operator
- Logical NOT: `!` operator (unary)
- Comparison: `==`, `!=` operators

**Implementation:** Straightforward operator syntax. All operations are binary except NOT.

---

## Type Coercion and Promotion

### Problem

Mixed-type operations (e.g., `int + float`, `string + int`) require type conversion.

### Solution Options

**Option A: Explicit Conversion (Recommended)**
- User defines conversion constructors: `ToFloat . Float ::= "float" "(" Int ")"`
- Usage: `float(3) + 2.0`
- Pros: Explicit, type-safe, clear intent
- Cons: Verbose, requires manual conversions

**Option B: Implicit Promotion**
- System auto-converts types based on promotion rules
- Pros: Convenient, less boilerplate
- Cons: Hidden conversions, potential precision loss, type ambiguity

**Option C: Type Classes/Traits**
- Define promotion rules declaratively: `promotions { Int -> Float: |x| x as f64 }`
- Pros: Explicit rules, extensible
- Cons: Additional syntax, more complex implementation

**Decision:** Start with Option A (explicit). Add Option C (type classes) in future if implicit promotion is needed. Avoid Option B initially to prevent hidden behavior.

**Risk:** Explicit conversions may be verbose for common cases (e.g., `float(3) + float(4)`). Mitigation: provide conversion helpers or consider implicit promotion for lossless conversions only.

---

## Evaluation Modes

Current system generates both constant folding and congruence rules for all operations. Per-operation mode control allows fine-grained evaluation strategy.

**Syntax:**
```rust
semantics {
    Add: +,              // Default: both folding and congruence
    Sub: - fold,          // Only constant folding
    Mul: * step,          // Only step-by-step (congruence)
}
```

**Implementation:** Extend `SemanticRule` with optional `EvalMode` field. Code generation checks mode before emitting folding or congruence rules.

**Use Cases:**
- `fold`: Production code, fast evaluation
- `step`: Educational/debugging, see all intermediate steps
- `both`: Default, flexible evaluation

See [native_types_and_operations.md](../made/native_types_and_operations.md) for detailed evaluation mode design.

---

## Implementation Phases

### Phase 1: Method Path Syntax (Foundation)

**Scope:** Establish method path syntax as the primary mechanism for semantic operations.

**Changes:**
1. Extend or replace `SemanticOperation` enum: add `MethodPath(syn::Path)` and `FunctionName(syn::Ident)` variants
2. Update parser: recognize path syntax (`String::push_str`, `str::len`) and distinguish from identifiers
3. Code generation: emit method calls with proper argument extraction and type handling
4. Support unary operations: detect arity from grammar rule, generate appropriate method calls
5. Cross-type operations: use rule's category for return type determination

**Timeline:** 2-3 days

**Files:**
- `macros/src/ast/types.rs`: `SemanticOperation` enum extension, parser updates
- `macros/src/codegen/ast_gen.rs`: Method call generation, unary operation support
- `macros/src/ascent/mod.rs`: Cross-type semantic rule generation

**Risk:** Generic methods require explicit type parameters. Mitigation: Document requirement clearly, provide examples.

**Alternative:** If operator shorthand is preferred, Phase 1 can extend `BuiltinOp` enum instead. However, method path provides more flexibility and avoids enum bloat.

### Phase 2: Operator Shorthand (Optional)

**Scope:** Add operator shorthand as syntactic sugar for common operations.

**Changes:**
1. Extend `BuiltinOp` enum: `Concat` (`++`), `And` (`&&`), `Or` (`||`), `Not` (`!`), `Eq` (`==`), `Ne` (`!=`), `Lt` (`<`), `Le` (`<=`), `Gt` (`>`), `Ge` (`>=`)
2. Update parser: recognize operator tokens, map to `Builtin(BuiltinOp)` variant
3. Code generation: emit operator calls (same as method path but with operator tokens)
4. Maintain compatibility: operators map to standard library methods internally

**Timeline:** 1-2 days

**Files:**
- `macros/src/ast/types.rs`: Extend `BuiltinOp` enum, update parser
- `macros/src/codegen/ast_gen.rs`: Operator token generation

**Risk:** Enum may grow large if extended too far. Mitigation: Limit to most common operations, use method path for others.

**Note:** This phase is optional. If conciseness is less important than explicitness, this phase can be skipped.

### Phase 3: Lambda Syntax

**Scope:** Maximum flexibility for custom operations.

**Changes:**
1. Extend `SemanticOperation`: add `Lambda` variant with parameter and body AST
2. Parser: recognize lambda syntax `|params| -> ReturnType { body }`
3. Code generation: emit closures and invoke in `eval()`
4. Error handling: support `Result<T, E>` return types

**Timeline:** 3-4 days

**Files:**
- `macros/src/ast/types.rs`: Lambda AST structure
- `macros/src/codegen/ast_gen.rs`: Closure generation

**Risk:** Parsing complexity may conflict with theory syntax. Mitigation: Use distinct lambda syntax, test edge cases.

### Phase 4: Type Coercion

**Scope:** Support mixed-type operations via explicit conversions.

**Changes:**
1. Add `conversions` block to theory AST
2. Generate conversion constructors from conversion rules
3. Optional: implicit promotion for lossless conversions

**Timeline:** 2-3 days

**Files:**
- `macros/src/ast/types.rs`: `ConversionRule` AST
- `macros/src/codegen/ast_gen.rs`: Conversion constructor generation

---

## Architectural Decisions

### Decision 1: Return Type for Cross-Type Operations

**Decision:** Use rule's category to determine return type. The grammar rule `Eq . Bool ::= Int "==" Int` means `Eq` returns `Bool`.

**Rationale:** Consistent with existing type system, no syntax changes needed, type-safe.

**Alternative Considered:** Explicit return type annotation (`Eq: == -> bool`). Rejected due to verbosity and redundancy with category.

### Decision 2: Operator Precedence

**Decision:** Use standard Rust operator precedence for new operators.

**Rationale:** Familiar to users, reduces cognitive load, consistent with language expectations.

**Alternative Considered:** Theory-level precedence definition. Rejected due to complexity and limited benefit.

### Decision 3: Error Handling Strategy

**Decision:** Phase 1-2: panic on error. Phase 3: support `Result<T, E>` via lambda syntax.

**Rationale:** Progressive enhancement, allows simple operations to remain simple, complex operations can handle errors.

**Alternative Considered:** Always return `Result`. Rejected due to verbosity for simple operations.

### Decision 4: Generic Method Support

**Decision:** Require explicit type parameters: `str::parse::<i32>`.

**Rationale:** Clarity, avoids ambiguity, compiler validates types.

**Alternative Considered:** Type inference from context. Rejected due to complexity and potential ambiguity.

### Decision 5: Method Chaining

**Decision:** Support via lambda syntax: `|s| s.trim().to_uppercase()`.

**Rationale:** Flexible, no special syntax needed, leverages Rust's method chaining.

**Alternative Considered:** Special chaining syntax. Rejected due to complexity and limited use cases.

---

## Examples

### Example 1: String Operations

```rust
theory! {
    name: StringCalc,
    exports {
        ![String] as Str,
        ![i64] as Int,
        ![bool] as Bool,
    },
    terms {
        Concat . Str ::= Str "++" Str ;
        Length . Int ::= "|" Str "|" ;
        EqStr . Bool ::= Str "==" Str ;
        ToString . Str ::= "str" "(" Int ")" ;
    },
    semantics {
        Concat: ++,                    // Operator
        Length: str::len,               // Method path
        EqStr: ==,                      // Comparison (returns Bool)
        ToString: i32::to_string,       // Conversion
    }
}
```

### Example 2: Float Math

```rust
theory! {
    name: FloatMath,
    exports {
        ![f64] as Float,
        ![bool] as Bool,
    },
    terms {
        AddFloat . Float ::= Float "+" Float ;
        Sin . Float ::= "sin" "(" Float ")" ;
        LtFloat . Bool ::= Float "<" Float ;
    },
    semantics {
        AddFloat: +,
        Sin: f64::sin,                  // Method path
        LtFloat: <,                     // Returns bool
    }
}
```

### Example 3: Complex Operations with Lambda

```rust
theory! {
    name: AdvancedStrings,
    exports {
        ![String] as Str,
        ![i64] as Int,
    },
    terms {
        Format . Str ::= "format" "(" Str "," Str ")" ;
        ParseInt . Int ::= "parse" "(" Str ")" ;
    },
    semantics {
        Format: |fmt, val| format!(fmt, val),
        ParseInt: |s: String| -> Result<i64, _> { s.parse() },
    }
}
```

---

## Recommendation

**Recommended Approach: Option 4 (Hybrid) or Option 5 (Declarative DSL)**

**Option 4 Rationale:**
- Covers full spectrum: simple operators to complex lambdas
- Progressive complexity: users choose appropriate syntax
- Optimal for each case: operators for speed, methods for clarity, lambdas for flexibility
- Flexible migration path

**Option 5 Rationale:**
- Maximum explicitness and type safety
- Structured format enables validation and tooling
- Evaluation mode control built-in
- Since backward compatibility is not critical, breaking changes are acceptable

**Recommendation:** Evaluate Option 5 (Declarative DSL) more seriously given that backward compatibility is not required. The structured format provides better long-term maintainability and extensibility, though at the cost of verbosity for simple cases.

**Alternative Hybrid Approach:**
If Option 5 is too verbose, Option 4 remains viable with implementation order:
1. Phase 1: Method Path (standard library integration, most flexible)
2. Phase 2: Operator shorthand (syntactic sugar for common operations)
3. Phase 3: Lambda (maximum flexibility for complex cases)
4. Phase 4: Type Coercion (mixed-type operations)

**Key Architectural Decisions:**
- Return type: rule's category determines return type
- Unary operations: detect arity from grammar rule
- Type coercion: explicit conversions initially, consider implicit later
- Error handling: panic initially, `Result` support via lambda syntax

**Success Criteria:**
- Common operations (strings, floats, bools) supported with clear, explicit syntax
- Advanced operations (custom methods, error handling) fully supported
- Type safety preserved at compile time
- Performance: no runtime overhead for direct method calls
- Extensibility: easy to add new operation types without core changes

---

**Last Updated**: January 2026
