# Native Types and Operations: Design Document

**Status**: Implemented (Partial)
**Date**: December 2025

---

## Vision

Allow theories to use **Rust native types** (like `i32`, `String`, `bool`) directly in category definitions, enabling:
1. **Zero-cost abstractions** - Direct use of Rust primitives without wrapper enums
2. **Native operator support** - Use Rust operators (`+`, `-`, `*`) directly via semantics
3. **Performance** - No enum dispatch overhead for primitive operations
4. **Interoperability** - Easy integration with Rust standard library and third-party crates

**Goal**: Make MeTTaIL theories that use primitive types as efficient and natural as writing Rust code, while maintaining the rewrite system's flexibility.

---

## Current Implementation

### Syntax

Native types are declared in the `exports` section using the `![Type] as Name` syntax:

```rust
theory! {
    name: Calculator,
    exports {
        ![i32] as Int  // Int category uses native Rust i32 type
    },
    // ...
}
```

**Key Points**:
- The `![]` syntax marks a native type export
- The type inside `[]` is the Rust native type (e.g., `i32`, `String`, `bool`)
- The `as Name` part defines the category name used in the theory
- Multiple native types can be declared: `![i32] as Int, ![bool] as Bool`

---

## Key Components

### 1. Export Declaration

**Location**: `macros/src/ast/types.rs`

```rust
pub struct Export {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
}
```

**Parsing**: The syntax `![Type] as Name` is parsed to extract the native type:
- `![i32] as Int` → `Export { name: Int, native_type: Some(i32) }`
- `Proc` → `Export { name: Proc, native_type: None }`

**Parsing Location**: `macros/src/ast/types.rs`

### 2. AST Generation

**Location**: `macros/src/codegen/ast_gen.rs`

**Critical Understanding**: Categories with native types **still generate enums**, not type aliases. The native type is used **within enum variant fields** where appropriate.

**Generated Structure**:
```rust
// For exports { ![i32] as Int }
// Generated enum (NOT a type alias):
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, BoundTerm)]
pub enum Int {
    NumLit(i32),                    // Native type directly in field
    VarRef(OrdVar),                 // Variable reference (no native type)
    Add(Box<Int>, Box<Int>),        // Recursive enum variant
    Sub(Box<Int>, Box<Int>),        // Recursive enum variant
    Assign(OrdVar, Box<Int>),       // Assignment with variable and expression
}
```

**Key Behaviors**:
1. **Enum Generation**: Categories with native types generate enums like non-native categories
2. **Native Type in Fields**: When a constructor uses the `Integer` keyword, the field type is the native type (e.g., `i32`)
3. **No Auto-Generated Var Variant**: Native type categories skip the auto-generated `Var` variant
4. **Auto-Generated Assign Variant**: All categories (including native types) automatically get an `Assign` variant if not explicitly defined
5. **Recursive Types**: Other constructors still use `Box<Category>` for recursive references

**Implementation Details**:
- When `Integer` keyword is encountered in a grammar rule, codegen checks if the category has a native type
- If native type exists, generates field with native type: `#label(#native_type)`
- Example: `NumLit . Int ::= Integer` → `NumLit(i32)`
- The `Integer` keyword is a special non-terminal that triggers native type field generation

### 3. Literal Parsing

**Location**: `macros/src/codegen/parser/lalrpop.rs`

**Behavior**:
- `Integer` keyword generates token parser for the native type
- For `i32`: parses integer literals directly into `i32`
- Token type is the native type itself (e.g., `i32`, not a wrapper)

**Generated Parser** (for `i32` native type):
```lalrpop
// Token parser for native integer type
Integer: i32 = {
    r"[0-9]+" => <>.parse().unwrap_or(0),
};

// Usage in grammar rules:
IntAtom: Int = {
    "(" <Int> ")",
    "-" <i:Integer> => Int::NumLit(-i),  // Unary minus support
    <v:Ident> => Int::VarRef(...),
    <i:Integer> => Int::NumLit(i),  // i is i32, passed directly to NumLit
};
```

**Parser Generation Logic**:
- Checks if category has native type via `has_native_type()`
- Generates `Integer: i32` token parser for integer native types
- Generates unary minus support for native integer types
  - Allows parsing `-42` as `Int::NumLit(-42)` directly
- Other native types (future) would generate appropriate token parsers

### 4. Eval Method Generation

**Location**: `macros/src/codegen/ast_gen.rs`

**Purpose**: Generate `eval()` method that evaluates expressions to native type values.

**Generated Code Example** (what appears in macro expansion):
```rust
impl Int {
    /// Evaluate the expression to its native type value.
    /// Variables must be substituted via rewrites before evaluation.
    pub fn eval(&self) -> i32 {
        match self {
            Int::NumLit(n) => *n,  // Extract native i32 directly
            Int::Add(a, b) => a.as_ref().eval() + b.as_ref().eval(),  // Recursive eval with operator
            Int::Sub(a, b) => a.as_ref().eval() - b.as_ref().eval(),
            Int::VarRef(_) => loop { panic!("Cannot evaluate variable") },
            Int::Assign(_, expr) => expr.as_ref().eval(),  // Evaluate RHS
            _ => panic!("Cannot evaluate expression - contains unevaluated terms. Apply rewrites first."),
        }
    }
}
```

**Generation Logic**:
1. Only generates for categories with native types
2. Builds map of constructor → semantic operation from `semantics` block
3. Generates match arms:
   - **Integer rule** (`NumLit`): Direct value extraction
   - **Var rule**: Panic (variables must be substituted first)
   - **Semantic operators**: Recursive eval with operator
   - **Other constructors**: Skip or handle specially

**Key Constraint**: Only binary operators (2 non-terminal arguments) are currently supported for eval generation.

### 5. Environment Queries

**Location**: `macros/src/ascent/relations.rs`, `macros/src/ascent/rewrites/patterns.rs`, `macros/src/ascent/rewrites/rhs.rs`

**Behavior**:
- `env_var(x, v)` relation uses native types directly
- Relation type: `relation env_var(String, i32)` when category has native type `i32`
- When matching `if env_var(x, v) then (VarRef x) => (NumLit v)`, the `v` binding is the native type value

**Generated Ascent Code** (from `calculator-datalog.rs`):
```rust
relation env_var(String, i32);  // Native type in relation

// Rewrite rule:
rw_int(s, t) <--
    int(s),
    if let Int::VarRef(s_f0) = s,
    // Extract variable name from OrdVar...
    env_var(var_name, v),  // v is i32 (native type)
    let t = Int::NumLit(*v);  // Use v directly, dereference for NumLit(i32)
```

**Key Implementation** (from `macros/src/ascent/rewrites/rhs.rs`):
- Native type values are bound directly in patterns
- RHS construction uses native type directly without wrapping

### 6. Substitution

**Location**: `macros/src/codegen/subst.rs`

**Behavior**:
- **Native types skip substitution entirely** - they're values, not terms that need substitution
- No `substitute()` method generated for native type categories
- No Var variant means no variable substitution is needed at the category level

**Rationale**: Native types are primitive values. Variables are handled via rewrite rules (e.g., `VarRef` → `NumLit` via environment queries).

**Generated Code**:
```rust
impl Int {
    // No substitute methods generated for native types
    // Native types are values, variable substitution handled via rewrites
}
```

### 7. Display

**Location**: `macros/src/codegen/display.rs`

**Behavior**:
- Display implementation generated normally for native type categories
- Native type fields displayed using standard Rust formatting
- `NumLit(i32)` displays as the integer value (e.g., "42")

**Implementation**: No special handling needed - Rust's `Display` formatting for native types works automatically.

### 8. Ascent Code Generation

**Location**: `macros/src/ascent/relations.rs`, `macros/src/ascent/rewrites/*.rs`

**Behavior**:
- Relations use native types directly: `relation env_var(String, i32)`
- Pattern matching handles native types specially (direct value binding, no `Box`)
- RHS construction uses native types without wrapping

**Example** (from generated `calculator-datalog.rs`):
```rust
// Relation uses native type
relation env_var(String, i32);

// Pattern matching extracts native value directly
if let Int::NumLit(a) = left.as_ref(),  // a is i32
// ...

// RHS uses native type directly
let t = Int::NumLit(a + b);  // a and b are i32, result is i32
```

---

## Current Example: Calculator Theory

**Location**: `theories/src/calculator.rs`

**Complete Theory Definition**:
```rust
theory! {
    name: Calculator,
    exports {
        ![i32] as Int
    },
    terms {
        VarRef . Int ::= Var ;           // Variable reference
        NumLit . Int ::= Integer ;       // Integer literal (uses native i32)
        
        Add . Int ::= Int "+" Int ;      // Addition
        Sub . Int ::= Int "-" Int ;      // Subtraction
        
        // Assign is automatically generated for all categories
    },
    equations {
        // No equations - arithmetic is handled via semantics
    },
    rewrites {
        // Variable substitution and Assign congruence are now auto-generated
        // Congruence rules: propagate rewrites through operators
        if S => T then (Add S R) => (Add T R);
        if S => T then (Add L S) => (Add L T);
        if S => T then (Sub S R) => (Sub T R);
        if S => T then (Sub L S) => (Sub L T);
    },
    semantics {
        Add: +,  // Map Add constructor to Rust + operator
        Sub: -,  // Map Sub constructor to Rust - operator
    }
}
```

**Generated Enum Structure**:
```rust
pub enum Int {
    VarRef(OrdVar),
    NumLit(i32),                    // Native i32 type
    Add(Box<Int>, Box<Int>),
    Sub(Box<Int>, Box<Int>),
    Assign(OrdVar, Box<Int>),       // Auto-generated for all categories
}
```

**Usage Example**:
```rust
// Note: The actual usage pattern depends on the REPL or runtime environment
// This is a conceptual example showing the flow

let parser = calculator::IntParser::new();
let term = parser.parse("x + 3").unwrap();  
// Result: Int::Add(Int::VarRef(...), Int::NumLit(3))

// In practice, variable substitution happens via Ascent rewrite rules
// with environment facts: env_var("x", 5)
// After rewrites: Int::Add(Int::NumLit(5), Int::NumLit(3))

// Evaluate to native type (after variable substitution)
let result: i32 = term.eval();  // Returns 8 (if x was substituted to 5)
```

**Note**: The actual environment and rewrite application depends on the runtime/REPL implementation. See `repl/src/theories/calculator.rs` for the actual integration.

---

## Implementation Details

### Helper Functions

**Location**: `macros/src/utils.rs`

```rust
/// Check if a category has a native type and return it
pub fn has_native_type<'a>(category: &Ident, theory: &'a TheoryDef) -> Option<&'a syn::Type> {
    theory.exports
        .iter()
        .find(|e| e.name == *category)
        .and_then(|e| e.native_type.as_ref())
}

/// Get native type as string for comparison
pub fn native_type_to_string(native_type: &syn::Type) -> String {
    match native_type {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                segment.ident.to_string()
            } else {
                "unknown".to_string()
            }
        },
        _ => "unknown".to_string(),
    }
}
```

### Type Detection Throughout Codegen

Native type detection via `has_native_type()` is used in:

1. **AST generation** (`macros/src/codegen/ast_gen.rs`):
   - Skip Var variant generation for native types
   - Use native type in `Integer` field generation
   - Auto-generate Assign variant for all categories (including native types)

2. **Parser generation** (`macros/src/codegen/parser/lalrpop.rs`):
   - Generate appropriate token parsers for native types

3. **Substitution** (`macros/src/codegen/subst.rs`):
   - Skip substitution methods entirely for native types

4. **Display** (`macros/src/codegen/display.rs`):
   - Skip auto-var display arm generation for native types (but display impl still generated)

5. **Ascent generation** (`macros/src/ascent/*.rs`):
   - `relations.rs`: Use native type in relation definitions
   - `rewrites/patterns.rs`: Handle native type bindings correctly
   - `rewrites/rhs.rs`: Use native types in RHS construction

6. **Rewrite generation** (`macros/src/ascent/rewrites/clauses.rs`):
   - Handle native type bindings in rewrite patterns

---

## Operations and Semantics

### Overview

The `semantics` block allows mapping constructors to **Rust built-in operators**, enabling direct evaluation of operations on native types. This is essential for making native types behave like native Rust code.

### Syntax

```rust
theory! {
    name: Calculator,
    exports {
        ![i32] as Int
    },
    terms {
        NumLit . Int ::= Integer ;
        Add . Int ::= Int "+" Int ;
        Sub . Int ::= Int "-" Int ;
        Mul . Int ::= Int "*" Int ;
        Div . Int ::= Int "/" Int ;
    },
    semantics {
        Add: +,   // Map Add constructor to Rust + operator
        Sub: -,   // Map Sub constructor to Rust - operator
        Mul: *,   // Map Mul constructor to Rust * operator
        Div: /,   // Map Div constructor to Rust / operator
    }
}
```

**Key Points**:
- `Constructor: Operator` syntax maps a constructor to a Rust operator
- Operators are parsed as Rust tokens (e.g., `+`, `-`, `*`, `/`)
- Only constructors with native type categories can use semantics
- Semantics are optional - constructors without semantics won't generate eval code

### Supported Operators

**Location**: `macros/src/ast/types.rs`

Currently supported built-in operators (10 total):

**Arithmetic**:
- `+` (Add) - Addition
- `-` (Sub) - Subtraction
- `*` (Mul) - Multiplication
- `/` (Div) - Division
- `%` (Rem) - Remainder/Modulo

**Bitwise**:
- `&` (BitAnd) - Bitwise AND
- `|` (BitOr) - Bitwise OR
- `^` (BitXor) - Bitwise XOR
- `<<` (Shl) - Left shift
- `>>` (Shr) - Right shift

**Not Yet Supported**:
- Comparison operators: `==`, `!=`, `<`, `>`, `<=`, `>=` (would return `bool`)
- Logical operators: `&&`, `||`, `!` (would require `bool` native type)
- Unary operators: `-x`, `!x`, `~x` (only binary operators currently supported)

### Implementation Details

#### 1. AST Representation

**Location**: `macros/src/ast/types.rs`

```rust
/// Semantic rule for operator evaluation
pub struct SemanticRule {
    pub constructor: Ident,  // e.g., "Add"
    pub operation: SemanticOperation,
}

pub enum SemanticOperation {
    Builtin(BuiltinOp),  // Currently only built-in operators supported
}

pub enum BuiltinOp {
    Add, Sub, Mul, Div, Rem,
    BitAnd, BitOr, BitXor, Shl, Shr,
}
```

**Parsing**: Operators are parsed as Rust tokens (in `macros/src/ast/types.rs`):
```rust
semantics {
    Add: +,  // Parses Token![+] → BuiltinOp::Add
    Sub: -,  // Parses Token![-] → BuiltinOp::Sub
}
```

#### 2. Eval Method Generation

**Location**: `macros/src/codegen/ast_gen.rs`

The `semantics` block drives generation of the `eval()` method:

**Input**:
```rust
semantics {
    Add: +,
    Sub: -,
}
```

**Generated Code**:
```rust
impl Int {
    pub fn eval(&self) -> i32 {
        match self {
            Int::NumLit(n) => *n,
            Int::Add(a, b) => a.as_ref().eval() + b.as_ref().eval(),
            Int::Sub(a, b) => a.as_ref().eval() - b.as_ref().eval(),
            // ... other cases
        }
    }
}
```

**Generation Algorithm**:
1. Check if constructor has semantics via `semantics_map` lookup
2. Count non-terminal arguments
3. If 2 arguments (binary operator), generate eval code:
   - Map `BuiltinOp` to Rust token
   - Generate: `#label(a, b) => a.as_ref().eval() #op_token b.as_ref().eval()`
4. Otherwise skip (unary/other arity not yet supported)

**Key Constraints**:
- Only **binary operators** (2 non-terminal arguments) are currently supported
- Unary operators are skipped (future enhancement)
- Recursively evaluates operands, then applies the operator
- Type-safe: operators use native type values directly

#### 3. Ascent Semantic Rules (Constant Folding)

**Location**: `macros/src/ascent/mod.rs`

Semantics also generate **rewrite rules** for constant folding in Ascent:

**Generated Ascent Code**:
```rust
// For semantics { Add: + }
rw_int(s, t) <--
    int(s),
    if let Int::Add(left, right) = s,
    if let Int::NumLit(a) = left.as_ref(),
    if let Int::NumLit(b) = right.as_ref(),
    let t = Int::NumLit(a + b);
```

**Purpose**: Automatically rewrite `Add(NumLit(5), NumLit(3))` → `NumLit(8)` during Ascent evaluation.

**Current Limitations**:
- Only generates rules for `Add`, `Sub`, `Mul`, `Div`, `Rem` (not bitwise operators)
- Only matches when **both operands are `NumLit`** (no partial evaluation)
- Future: Could generate rules for partial evaluation: `Add(NumLit(0), x) => x`
- The constant folding uses the constructor name `NumLit` by default

**Example Usage**:
```rust
let term = Int::Add(
    Box::new(Int::NumLit(5)),
    Box::new(Int::NumLit(3))
);

// Ascent automatically rewrites to:
// Int::NumLit(8)

// Then eval() can extract the value:
let value: i32 = term.eval();  // 8
```

#### 4. Operator Precedence and Associativity

**Current State**: Operator precedence is handled by the **parser** (LALRPOP grammar), not by semantics.

**Parser Approach** (from `calculator.lalrpop`):
```lalrpop
// Generated parser has precedence tiers
IntInfix: Int = {
    <left:IntInfix> "+" <right:IntAtom> => Int::Add(Box::new(left), Box::new(right)),
    <left:IntInfix> "-" <right:IntAtom> => Int::Sub(Box::new(left), Box::new(right)),
    <IntAtom>
};

IntAtom: Int = {
    "(" <Int> ")",
    "-" <i:Integer> => Int::NumLit(-i),
    <v:Ident> => Int::VarRef(...),
    <i:Integer> => Int::NumLit(i)
};
```

**Semantics Block**: Does NOT specify precedence - it only maps constructors to operations. Precedence comes from grammar structure.

**Future Enhancement**: Could allow precedence annotations:
```rust
semantics {
    Add: + @prec(6),    // Lower precedence
    Mul: * @prec(5),    // Higher precedence
}
```

### Design Decisions

#### Decision 1: Built-in Operators Only

**Chosen**: Only Rust built-in operators (`+`, `-`, `*`, etc.)

**Rationale**:
- Simple and type-safe
- Direct mapping to Rust operations
- No function call overhead
- Compiler optimizes operations

**Alternative Considered**: User-defined functions
- More flexible but more complex
- Requires function signatures
- Type checking becomes harder

**Future**: May add user-defined function support for standard library functions

#### Decision 2: Binary Operators Only (for eval)

**Chosen**: Only generate eval() code for binary operators (2 arguments)

**Rationale**:
- Most common case
- Simpler code generation
- Can be extended later

**Missing**:
- Unary operators (`-x`, `!x`, `~x`)
- Ternary operators (if supported)
- Variable-arity operators

**Future**: Add unary operator support

#### Decision 3: Constant Folding in Ascent

**Chosen**: Generate Ascent rewrite rules for constant folding

**Rationale**:
- Enables automatic simplification during evaluation
- Reduces evaluation overhead
- Natural fit for rewrite-based semantics

**Trade-off**:
- More Ascent rules = more computation
- But saves eval() calls on constants

**Future**: Could generate more aggressive constant folding rules

#### Decision 4: Separate eval() and Ascent Rules

**Chosen**: Generate both eval() method AND Ascent rewrite rules

**Rationale**:
- eval() for direct evaluation (no rewrite system)
- Ascent rules for rewrite-based evaluation
- Different use cases:
  - eval(): Fast, direct evaluation
  - Ascent: Full rewrite exploration with constant folding

**Usage Pattern**:
```rust
// Option 1: Direct evaluation (faster)
let value = term.eval();

// Option 2: Rewrite-based (more flexible)
let prog = ascent_run! {
    include_source!(calculator_source);
    int(term);
};
// Ascent automatically applies constant folding rewrites
```

### Current Limitations

#### Missing Operators

1. **Comparison operators**: `==`, `!=`, `<`, `>`, `<=`, `>=`
   - Would return `bool` (different native type)
   - Requires support for multiple native types per theory
   
2. **Logical operators**: `&&`, `||`, `!`
   - Would require `bool` native type support
   - Unary `!` not yet supported
   
3. **Unary operators**: `-x`, `!x`, `~x`
   - Codegen only handles binary operators
   - Need to extend eval() generation

#### No Partial Evaluation

**Current**: Only folds when BOTH operands are constants
```rust
// Works:
Add(NumLit(5), NumLit(3)) → NumLit(8)

// Doesn't work:
Add(NumLit(0), x) → x  // Identity simplification
Add(x, NumLit(0)) → x  // Identity simplification
```

**Future**: Generate identity/zero rules:
```rust
semantics {
    Add: + @identity(0),  // Add(NumLit(0), x) => x
    Mul: * @identity(1) @zero(0),  // Mul(NumLit(1), x) => x, Mul(NumLit(0), x) => NumLit(0)
}
```

#### No Operator Overloading

**Current**: One operator per constructor
```rust
// Can't do:
semantics {
    Add: |a, b| a + b + 1,  // Custom behavior
}
```

**Future**: Support lambda-based semantics for custom operations

#### No Type Coercion

**Current**: Operators only work with matching native types
```rust
// Can't do:
Add(i32_value, f64_value)  // Type mismatch
```

**Future**: Add type coercion rules (see Type Conversions section)

### Examples

#### Example 1: Basic Arithmetic

```rust
theory! {
    name: Arithmetic,
    exports {
        ![i32] as Int
    },
    terms {
        NumLit . Int ::= Integer ;
        Add . Int ::= Int "+" Int ;
        Mul . Int ::= Int "*" Int ;
    },
    semantics {
        Add: +,
        Mul: *,
    }
}

// Usage:
let expr = Int::Mul(
    Box::new(Int::Add(
        Box::new(Int::NumLit(2)),
        Box::new(Int::NumLit(3))
    )),
    Box::new(Int::NumLit(4))
);

let result = expr.eval();  // (2 + 3) * 4 = 20
```

#### Example 2: Bitwise Operations

```rust
theory! {
    name: BitOps,
    exports {
        ![u32] as Word
    },
    terms {
        WordLit . Word ::= Integer ;
        And . Word ::= Word "&" Word ;
        Or . Word ::= Word "|" Word ;
        Xor . Word ::= Word "^" Word ;
    },
    semantics {
        And: &,
        Or: |,
        Xor: ^,
    }
}

// Usage:
let a = Word::WordLit(0b1010);
let b = Word::WordLit(0b1100);
let result = Word::And(Box::new(a), Box::new(b)).eval();  // 0b1000
```

**Note**: Bitwise operators are supported in eval() generation but **NOT** in Ascent constant folding rules (only arithmetic operators are folded).

#### Example 3: Division and Remainder

```rust
theory! {
    name: DivMod,
    exports {
        ![i32] as Int
    },
    terms {
        NumLit . Int ::= Integer ;
        Div . Int ::= Int "/" Int ;
        Mod . Int ::= Int "%" Int ;
    },
    semantics {
        Div: /,
        Mod: %,
    }
}

// Usage:
let div = Int::Div(
    Box::new(Int::NumLit(10)),
    Box::new(Int::NumLit(3))
).eval();  // 3

let rem = Int::Mod(
    Box::new(Int::NumLit(10)),
    Box::new(Int::NumLit(3))
).eval();  // 1
```

**Important**: Division by zero will panic (Rust's default behavior). Future enhancement: return `Result<i32, EvalError>`.

---

## Current Limitations

### What Works

1. Basic native type declaration (`![i32] as Int`)
2. Integer literal parsing (`Integer` keyword for `i32`)
3. Eval method generation with semantics
4. Environment variable queries (`env_var`)
5. Rewrite rules with native type values
6. Type-safe code generation
7. Ascent constant folding for arithmetic operators (`+`, `-`, `*`, `/`, `%`)

### What's Missing

1. **Other native types**: Only `i32` fully supported and tested
   - `String`, `bool`, `f64`, `u32`, etc. partially supported in codegen but not fully tested
   - No standard library types (`Vec<T>`, `Option<T>`, etc.)
   
2. **Type registry/validation**: No validation that native types are "allowed"
   - Could allow arbitrary Rust types (risky)
   - Should have whitelist of safe primitive types
   
3. **Multiple native types per theory**: Can declare multiple, but interaction unclear
   - Can have `![i32] as Int, ![bool] as Bool`
   - But operations between different native types not supported
   
4. **Native type conversions**: No automatic coercion
   - Can't convert `i32` → `i64` automatically
   
5. **Standard library integration**: No easy way to use `std::` functions
   - Would need `use stdlib;` directive
   - Function registry for allowed functions

6. **Bitwise constant folding**: Bitwise operators (`&`, `|`, `^`, `<<`, `>>`) supported in eval() but NOT in Ascent constant folding

---

## Design Decisions

### Decision 1: Enum Wrapper (Not Type Alias)

**Chosen**: Categories with native types generate enums, not type aliases

**Rationale**:
- Enum allows multiple constructors (`NumLit`, `Add`, `VarRef`, etc.)
- Type alias would only allow one constructor
- Maintains consistency with non-native categories
- Enables pattern matching and recursive types

**Actual Structure**:
```rust
// What's generated (enum):
pub enum Int {
    NumLit(i32),                    // Native type in field
    Add(Box<Int>, Box<Int>),       // Recursive structure
    // ...
}

// NOT generated (type alias):
// pub type Int = i32;  // Would lose ability to have multiple constructors
```

**Trade-off**:
- Slight overhead (enum discriminant)
- But constructors can still use native types in fields
- Maintains flexibility for non-value constructors

### Decision 2: No Var Variant for Native Types

**Chosen**: No auto-generated Var variant for native type categories

**Rationale**:
- Native types are values, not terms
- Variables handled via explicit `VarRef` constructor
- Cleaner separation: native values vs. term variables

**Example**:
```rust
// Native type: no auto-generated Var variant
pub enum Int {
    NumLit(i32),     // Value
    VarRef(OrdVar),  // Explicit variable reference (user-defined)
    Add(Box<Int>, Box<Int>),
    // No IVar(OrdVar) auto-generated
}

// Non-native type: has auto-generated Var variant
pub enum Proc {
    PVar(OrdVar),    // Auto-generated variable variant
    PZero,
    PPar(HashBag<Box<Proc>>),
}
```

**Implementation**: `macros/src/codegen/ast_gen.rs` check `export.native_type.is_none()` before adding Var variant. The check ensures native types don't get an auto-generated Var variant, as they use explicit `VarRef` constructors instead.

### Decision 3: Skip Substitution for Native Types

**Chosen**: No substitution methods generated for native type categories

**Rationale**:
- Native types are immutable values
- Variable substitution handled via rewrite rules (e.g., `VarRef` → `NumLit` via `env_var`)
- Simpler codegen (no special cases needed)

**Implementation**: `macros/src/codegen/subst.rs` checks for native type and returns empty impl block.

### Decision 4: Integer Keyword for Literals

**Chosen**: Reserved `Integer` keyword (not user-defined)

**Rationale**:
- Clear signal for native type literal
- Parser can generate appropriate token parser automatically
- Consistent across all native integer types (`i8`, `i16`, `i32`, `i64`, `u32`, etc.)
- Type-safe: parser knows to use native type

**Alternative Considered**: User-defined keyword (e.g., `IntLit`)
- More flexible but harder to generate parsers
- Less clear semantic meaning
- Would require type inference

**Implementation**: `macros/src/codegen/parser/lalrpop.rs` detect `Integer` keyword and generate appropriate token parser based on native type. The parser also generates unary minus support (`-42`) for native integer types.

---

## Future Enhancements

### Phase 1: Expand Native Type Support

**Goal**: Support common Rust primitive types

**Tasks**:
1. Support `i32` (current)
2. Support `i64`, `u32`, `u64`, `i8`, `u8`, `i16`, `u16`, `i128`, `u128`
3. Support `f32`, `f64` (floating point)
4. Support `bool` (boolean)
5. Support `String` (string literals)
6. Support `char` (character literals)

**Parser Changes**:
```rust
// Generate appropriate token parsers for each type
Integer: i32 = { r"[0-9]+" => <>.parse().unwrap() };
Float: f64 = { r"[0-9]+\.[0-9]+" => <>.parse().unwrap() };
Boolean: bool = { "true" => true, "false" => false };
StringLit: String = { "\"" <s:r"[^\"]*"> "\"" => s.to_string() };
CharLit: char = { "'" <c:r"."> "'" => c.chars().next().unwrap() };
```

**Semantics**:
```rust
semantics {
    // Integer operations
    Add: +, Sub: -, Mul: *, Div: /, Rem: %,
    
    // Float operations
    FAdd: +, FSub: -, FMul: *, FDiv: /,
    
    // Boolean operations
    And: &&, Or: ||, Not: !,  // Requires unary operator support
    
    // Comparison (returns bool) - requires multiple native types
    Eq: ==, Ne: !=, Lt: <, Le: <=, Gt: >, Ge: >=,
}
```

### Phase 2: Type Registry and Validation

**Goal**: Validate native types and provide registry of allowed types

**Design**:
```rust
// In codegen validation
const ALLOWED_NATIVE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128",
    "u8", "u16", "u32", "u64", "u128",
    "f32", "f64",
    "bool", "char", "String",
];

fn validate_native_type(ty: &syn::Type) -> Result<(), Error> {
    let type_str = native_type_to_string(ty);
    if !ALLOWED_NATIVE_TYPES.contains(&type_str.as_str()) {
        return Err(Error::new_spanned(
            ty,
            format!("Native type '{}' is not allowed. Allowed types: {:?}", 
                    type_str, ALLOWED_NATIVE_TYPES)
        ));
    }
    Ok(())
}
```

**User-facing**:
```rust
theory! {
    name: MyTheory,
    exports {
        ![i32] as Int,        // Allowed
        ![MyType] as MyCat,   // Error: not in registry
    },
}
```

### Phase 3: Standard Library Integration

**Goal**: Use Rust standard library functions in theories

**Design**:
```rust
theory! {
    name: StringTheory,
    exports {
        ![String] as Str
    },
    terms {
        Concat . Str ::= Str "+" Str ;
        Length . Int ::= "len" "(" Str ")" ;
        Substring . Str ::= Str "[" Int ".." Int "]" ;
    },
    semantics {
        Concat: std::string::String::push_str,  // Or macro expansion
        Length: str::len,
        Substring: str::get,  // Needs bounds checking
    },
    stdlib {
        use std::string::String;
        use std::str;
    }
}
```

**Challenges**:
- Function signatures must match exactly
- Error handling (Result types)
- Lifetime management
- Generic functions

**Alternative**: Custom semantics block that generates wrapper functions:
```rust
semantics {
    Concat: |a: String, b: String| -> String { 
        format!("{}{}", a, b) 
    },
}
```

### Phase 4: Type Conversions

**Goal**: Automatic type coercion and conversions

**Design**:
```rust
theory! {
    name: MixedTypes,
    exports {
        ![i32] as Int,
        ![f64] as Float
    },
    terms {
        ToFloat . Float ::= "float" "(" Int ")" ;
        ToInt . Int ::= "int" "(" Float ")" ;
        AddMixed . Float ::= Int "+" Float ;  // Auto-convert Int → Float
    },
    conversions {
        Int → Float: |x: i32| x as f64,
        Float → Int: |x: f64| x as i32,  // Truncates
    },
}
```

**Implementation**:
- Generate conversion functions
- Insert conversions in eval() and rewrite RHS
- Warn on lossy conversions

### Phase 5: Generic Native Types (Future)

**Goal**: Support generic types like `Vec<T>`, `Option<T>`

**Challenges**:
- Generic type parameters in exports
- Type inference for constructors
- Lifetime parameters
- Trait bounds

**Example** (future):
```rust
theory! {
    name: ListTheory,
    exports {
        ![Vec<Int>] as IntList,
        ![Option<Int>] as OptInt,
    },
    // ...
}
```

---

## Technical Challenges

### Challenge 1: Type Safety in Generated Code

**Problem**: Ensuring native types match between parser, AST, and eval

**Solution**: 
- Use `syn::Type` throughout codegen (parsed from user input)
- Generate type-parameterized code using `quote!` macro
- Rust compiler catches mismatches at compile time

**Status**: Working - type errors caught by Rust compiler

### Challenge 2: Environment Variable Typing

**Problem**: `env_var(String, T)` relation needs correct type for `T`

**Solution**:
- Detect native type from category via `has_native_type()`
- Generate relation with correct type: `relation env_var(String, i32)`
- Pattern matching extracts native type value directly (no wrapping)

**Implementation**: `macros/src/ascent/relations.rs`

**Status**: Working

### Challenge 3: Pattern Matching Native Types

**Problem**: Matching native type values in rewrite LHS/RHS

**Solution**:
- Special handling in pattern generation (`macros/src/ascent/rewrites/patterns.rs`)
- Native type fields bind directly (no `Box` or wrapper)
- RHS construction uses native type directly (`macros/src/ascent/rewrites/rhs.rs`)

**Example**:
```rust
// Pattern: (NumLit v) where v is i32
if let Int::NumLit(v) = term {  // v: i32 directly
    // Use v as i32
}

// RHS: NumLit(5)
let result = Int::NumLit(5);  // Direct i32 literal
```

**Status**: Working

### Challenge 4: Eval Error Handling

**Problem**: Current `eval()` panics on errors (variables, incomplete evaluation)

**Current Behavior**: Panics with message:
- `"Cannot evaluate {} - variables must be substituted via rewrites first"` for VarRef
- `"Cannot evaluate expression - contains unevaluated terms. Apply rewrites first."` for unmatched cases

**Future Solution**:
```rust
#[derive(Debug)]
pub enum EvalError {
    UnboundVariable(OrdVar),
    IncompleteEvaluation,
    DivisionByZero,
}

impl Int {
    pub fn eval(&self) -> Result<i32, EvalError> {
        match self {
            Int::NumLit(n) => Ok(*n),
            Int::VarRef(v) => Err(EvalError::UnboundVariable(v.clone())),
            Int::Add(a, b) => Ok(a.as_ref().eval()? + b.as_ref().eval()?),
            Int::Div(a, b) => {
                let b_val = b.as_ref().eval()?;
                if b_val == 0 {
                    Err(EvalError::DivisionByZero)
                } else {
                    Ok(a.as_ref().eval()? / b_val)
                }
            }
            _ => Err(EvalError::IncompleteEvaluation),
        }
    }
}
```

**Status**: Not implemented - breaking change would be required

---

## Testing Strategy

### Unit Tests

1. **Parser Tests**: Verify native type literals parse correctly
   ```rust
   #[test]
   fn test_integer_literal() {
       let parser = calculator::IntParser::new();
       let result = parser.parse("42").unwrap();
       assert_eq!(result, Int::NumLit(42));
   }
   ```

2. **Eval Tests**: Verify evaluation produces correct native values
   ```rust
   #[test]
   fn test_eval_addition() {
       let term = Int::Add(Box::new(Int::NumLit(5)), Box::new(Int::NumLit(3)));
       assert_eq!(term.eval(), 8);
   }
   ```

3. **Environment Tests**: Verify env_var rewrites work
   ```rust
   #[test]
   fn test_env_substitution() {
       let mut env = CalculatorIntEnv::new();
       env.set("x", Int::NumLit(10));
       
       let term = Int::VarRef(/* ... */);
       let result = apply_rewrites_with_env(&term, &env).unwrap();
       assert_eq!(result, Int::NumLit(10));
   }
   ```

### Integration Tests

1. **Full Calculator Example**: End-to-end parsing and evaluation (`theories/tests/calculator.rs`)
2. **Multiple Native Types**: Test theories with `i32` and `String` (future)
3. **Semantics Block**: Verify operator semantics work correctly

### Compile-Fail Tests

1. **Invalid Native Type**: Test that non-allowed types error (future - when validation added)
2. **Type Mismatch**: Test that native type mismatches are caught by Rust compiler
3. **Missing Semantics**: Test that eval fails gracefully without semantics (panics currently)

---

## Success Metrics

### Phase 1 Success (Current)

- `i32` native type fully supported
- Calculator theory works end-to-end
- Eval method generates correctly
- Environment queries work
- No compilation errors
- Ascent constant folding works for arithmetic operators

### Phase 2 Success (Expand Types)

- All integer types supported (`i8`-`i128`, `u8`-`u128`)
- Float types supported (`f32`, `f64`)
- Boolean and character types supported
- String type supported
- All tests pass for each type

### Phase 3 Success (Stdlib Integration)

- Standard library functions callable from theories
- Type-safe function registration
- Error handling works correctly

### Overall Success

- **Performance**: Native type operations have zero overhead vs. Rust
- **Type Safety**: All type mismatches caught at compile time
- **Documentation**: Examples for each native type
- **Tests**: 100% coverage for native type features

---

## Related Features

### Operations (Semantics Block)

Native types work closely with operations defined via the `semantics` block:
- See "Operations and Semantics" section above
- Operations enable direct evaluation of Rust operators on native types

### Environment Queries

Environment variable queries (`env_var`) are essential for variable substitution with native types:
- Relation type uses native type: `relation env_var(String, i32)`
- Enables variable substitution via rewrite rules

### Rewrite Engine

Native types interact with rewrite rules for evaluation:
- Rewrite rules can substitute variables to native values
- Constant folding via semantic rules
- See `design/made/ascent_generation.md` for rewrite system details

---

## Open Questions

### Q1: Should native types support pattern matching in rewrite LHS?

**Current**: No - native types are values, not patterns in rewrite rules

**Proposed**: Allow patterns like `(NumLit 5)` in rewrite LHS
```rust
rewrites {
    (Add (NumLit 0) x) => x;  // Constant folding
}
```

**Verdict**: Defer - current approach works, pattern matching adds complexity. Can use semantic rules for constant folding instead.

### Q2: Should eval() return Result instead of panicking?

**Current**: Panics on errors

**Proposed**: Return `Result<i32, EvalError>`

**Verdict**: **Should implement** - better error handling, but breaking change. Requires updating all call sites.

### Q3: Should we support custom native types (user-defined structs)?

**Current**: Only primitive types

**Proposed**: Allow `![MyStruct] as MyCat` if `MyStruct` implements certain traits (e.g., `Clone`, `Eq`, `Hash`)

**Verdict**: **Future work** - requires trait bounds, more complex type checking, unclear use cases

### Q4: How to handle native type overflow/underflow?

**Current**: Rust's default behavior (wrapping or panic depending on build mode)

**Proposed**: Configurable overflow handling (wrapping, saturating, checked)

**Verdict**: **Defer** - use Rust's behavior for now. Can be addressed when adding Result-based eval.

---

## Migration Notes

### For Existing Theories

No breaking changes - native types are opt-in:
- Existing theories continue to work unchanged
- Add native types incrementally
- No migration needed

### For New Theories

Recommendation: Use native types for primitive operations:
```rust
// Good: Use native types for arithmetic
exports { ![i32] as Int }
terms {
    NumLit . Int ::= Integer ;
    Add . Int ::= Int "+" Int ;
}
semantics {
    Add: +,
}

// Avoid: Wrapping primitives in enums without native types
exports { Int }  // Int would be enum with just numeric variants, no eval() method
```

---

## References

### Implementation Files

- `macros/src/ast/types.rs` - Export definition with `native_type` field, `SemanticRule`, `BuiltinOp`
- `macros/src/utils.rs` - `has_native_type()`, `native_type_to_string()` helper functions
- `macros/src/codegen/ast_gen.rs` - AST and eval() method generation
- `macros/src/codegen/parser/lalrpop.rs` - Parser generation with native type token parsers
- `macros/src/codegen/subst.rs` - Substitution (skips native types)
- `macros/src/codegen/display.rs` - Display implementation (normal handling for native types)
- `macros/src/ascent/relations.rs` - Ascent relation generation with native types
- `macros/src/ascent/rewrites/*.rs` - Ascent rewrite code generation with native type handling
- `macros/src/ascent/mod.rs` - Semantic rule generation for constant folding

### Example Theories

- `theories/src/calculator.rs` - Calculator with `i32` native type (complete working example)
- `theories/tests/calculator.rs` - Tests for calculator theory

### Generated Files (for reference)

- `theories/src/generated/calculator.lalrpop` - Generated parser showing Integer token and grammar
- `theories/src/generated/calculator-datalog.rs` - Generated Ascent code showing native type usage

### Design Documents

- `design/made/ascent_generation.md` - How Ascent code is generated
- `main_goals.md` - Original vision for native types

---

**Last Updated**: December 2025
**Status**: Core implementation complete (i32), expanding to more types
