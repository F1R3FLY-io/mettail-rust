# Environments: Design Document

**Status**: Implemented (Core), Design Evolving
**Date**: December 2025

---

## Overview

Environments provide **all data structures required to interpret code** written in MeTTaIL theory languages. This includes variable bindings, execution state, shadowed variables, and any other runtime information needed for evaluation. This document explores the design space, current implementation, and future directions for environment support. It is structured for team review and discussion.

**Key Questions for Review**:
1. What environment models do we need to support?
2. What types of execution state should environments manage?
3. How should environments integrate with the rewrite system?
4. What properties can we prove about environments?
5. How do we balance simplicity with expressiveness?

---

## Table of Contents

1. [Motivation and Goals](#motivation-and-goals)
2. [Design Space Exploration](#design-space-exploration)
3. [Current Implementation](#current-implementation)
4. [Environment Models](#environment-models)
5. [Integration with Rewrite System](#integration-with-rewrite-system)
6. [Formal Properties](#formal-properties)
7. [Design Alternatives](#design-alternatives)
8. [Future Directions](#future-directions)
9. [Open Questions](#open-questions)

---

## Motivation and Goals

### Why Environments?

MeTTaIL theories need to support **all execution state** required to interpret code in the theory language. Environments serve as the container for this state:

1. **Variable Bindings**: `x = 5` stores a value for later use; `x + 3` retrieves and uses stored values
2. **Execution Point**: Track current position in program execution (e.g., program counter, continuation)
3. **Shadowed Variables**: Variables that are shadowed by inner scopes or contexts (e.g., variables in nested blocks that hide outer variables)
4. **Stateful Rewrites**: Rewrite rules query and update execution state
5. **Interactive Evaluation**: REPL and interactive tools need persistent state storage
6. **Control Flow State**: Stack frames, call history, exception handlers
7. **Resource Tracking**: Memory allocation, file handles, network connections

The current implementation focuses on **variable bindings** as the primary use case, but the design is intended to support all forms of execution state.

### Design Goals

1. **Automatic**: Environments should be available without explicit declaration
2. **Type-Safe**: Each category gets its own type-safe environment
3. **Composable**: Environments should work with both native and custom types
4. **Comprehensive**: Support all execution state needed for interpretation, not just variables
5. **Formalizable**: We should be able to reason about environment properties
6. **Extensible**: Support for different environment models (flat, scoped, etc.) and different types of state

---

## Design Space Exploration

### What Kinds of Environments Do Users Want?

We've identified several environment models that users might need:

#### 1. **Flat Environment** (Current Implementation)
- Single global mapping: `name → value`
- No scoping or shadowing
- Simple and efficient
- **Use Case**: Calculator, simple scripting

**Example**:
```rust
let mut env = CalculatorIntEnv::new();
env.set("x", 5);
env.set("y", 10);
// x and y are both in the same flat namespace
```

#### 2. **Scoped Environment** (Future)
- Stack of scopes: `[scope₁, scope₂, ..., scopeₙ]`
- Variable shadowing: inner scopes hide outer ones
- Lexical scoping semantics
- **Use Case**: Functions with local variables, closures

**Example**:
```rust
let mut env = CalculatorIntEnv::new();
env.set("x", 5);        // Outer scope
env.push_scope();
env.set("x", 10);       // Inner scope shadows outer
assert_eq!(env.get("x"), Some(10));
env.pop_scope();
assert_eq!(env.get("x"), Some(5));
```

#### 3. **Hierarchical Environment** (Future)
- Tree structure: environments can have parent environments
- Inheritance: lookups search up the tree
- **Use Case**: Module systems, namespaces

**Example**:
```rust
let mut global = CalculatorIntEnv::new();
global.set("x", 5);

let mut local = CalculatorIntEnv::with_parent(&global);
local.set("y", 10);
// local.get("x") searches parent, finds 5
// local.get("y") finds 10 in local scope
```

#### 4. **Functional Environment** (Future)
- Immutable: operations return new environments
- No mutation, pure functional style
- **Use Case**: Functional programming, theorem proving

**Example**:
```rust
let env1 = CalculatorIntEnv::new();
let env2 = env1.set("x", 5);  // Returns new environment
let env3 = env2.set("y", 10); // Returns new environment
// env1 unchanged, env2 and env3 are new
```

#### 5. **Typed Environment** (Future)
- Type information stored with values
- Runtime type checking
- **Use Case**: Dynamic typing, gradual typing

**Example**:
```rust
let mut env = TypedEnv::new();
env.set("x", Value::Int(5));
env.set("y", Value::String("hello"));
// Values carry type information
```

### Design Question: Which Models Should We Support?

**Current Approach**: Start with flat environments, add others as needed.

**Discussion Points**:
- Should we support multiple models simultaneously?
- Can we abstract over different models with a trait?
- How do we avoid over-engineering while staying flexible?

### What Types of Data Do Environments Hold?

Environments are designed to hold **all execution state** needed to interpret theory code. This includes:

#### 1. **Variable Bindings** (Current Implementation)
- User-visible variables: `x = 5`, `y = "hello"`
- Direct mapping from variable names to values
- **Current Status**: Implemented

**Example**:
```rust
env.set("x", Int::NumLit(5));
env.set("y", Int::NumLit(10));
```

#### 2. **Execution Point** (Future)
- Current position in program execution
- Program counter, instruction pointer, continuation
- Stack of execution contexts
- **Use Case**: Step-by-step execution, debugging, control flow

**Example**:
```rust
env.set_execution_point(ExecutionPoint::Line(42));
env.set_continuation(Continuation::CallStack(vec![...]));
```

#### 3. **Shadowed Variables** (Future)
- Variables shadowed by inner scopes or contexts
- Variables in nested blocks that hide outer variables
- Lexical scoping with variable shadowing
- **Use Case**: Functions with local variables, closures, nested scopes

**Example**:
```rust
env.set("x", Int::NumLit(5));  // Outer scope
env.push_scope();
env.set("x", Int::NumLit(10)); // Inner scope shadows outer x
// env.get("x") returns 10 (from inner scope)
env.pop_scope();
// env.get("x") returns 5 (from outer scope)
```

#### 4. **Control Flow State** (Future)
- Call stack, activation records
- Exception handlers, error contexts
- Break/continue targets
- **Use Case**: Function calls, exception handling, loops

**Example**:
```rust
env.push_frame(Frame { function: "foo", locals: ... });
env.set_exception_handler(ExceptionHandler { ... });
```

#### 5. **Resource Tracking** (Future)
- Memory allocations, file handles
- Network connections, locks
- Reference counts, garbage collection state
- **Use Case**: Resource management, memory safety

**Example**:
```rust
env.track_allocation(ptr, size);
env.track_file_handle(file_id, path);
```

#### 6. **Metadata** (Future)
- Source location information
- Debug symbols, profiling data
- Type information, annotations
- **Use Case**: Debugging, profiling, type checking

**Example**:
```rust
env.set_metadata("x", Metadata { 
    source_line: 10, 
    type_info: Type::Int 
});
```

**Design Question**: Should different types of state be in separate namespaces or unified?

**Current Approach**: Variable bindings use a unified `HashMap<String, Value>`. Future state types may use separate storage or namespaced keys (e.g., `exec:pc`, `shadowed:x`).

---

## Current Implementation

### Automatic Generation

Environments are **automatically generated** for ALL exported categories:

```rust
theory! {
    name: Calculator,
    exports { ![i32] as Int },
    // ...
}

// Automatically generates:
pub struct CalculatorIntEnv {
    vars: HashMap<String, Int>,
}
```

**Key Principle**: Environment generation is **independent** of rewrite rule analysis. Every exported category gets an environment, making it available even if not immediately used.

**Current Focus**: The implementation currently focuses on **variable bindings** as the primary use case. The design is extensible to support other types of execution state (execution point, shadowed variables, control flow state, etc.) in the future.

### Generated Structure

For each exported category `Category` in theory `Theory`:

```rust
pub struct TheoryCategoryEnv {
    vars: HashMap<String, Category>,
}

impl TheoryCategoryEnv {
    pub fn new() -> Self;
    pub fn set(&mut self, name: String, value: Category);
    pub fn get(&self, name: &str) -> Option<Category>;
    pub fn clear(&mut self);
    pub fn env_to_facts(&self) -> Vec<(String, Category)>;
}
```

### Ascent Integration

Environment relations are automatically generated:

```rust
// For native types: relation env_var_int(String, i32);
// For custom types: relation env_var_proc(String, Proc);
```

### Rewrite Rule Integration

Environments integrate with rewrite rules via `env_var` conditions:

```rust
rewrites {
    // Query environment: if env_var(x, v) then (VarRef x) => (NumLit v)
    if env_var(x, v) then (VarRef x) => (NumLit v);
    
    // Create environment fact: (Assign x e) => e then env_var(x, e)
    (Assign x e) => e then env_var(x, e);
}
```

---

## Environment Models

### Model 1: Flat Environment (Implemented)

**Structure**: `HashMap<String, Value>`

**Properties**:
- Simple and efficient
- O(1) lookup and insertion
- No scoping complexity
- No variable shadowing
- No lexical scoping

**Formal Model**:
```
Env = String → Value

lookup(env, name) = env[name] if name ∈ dom(env), else ⊥
update(env, name, value) = env[name ↦ value]
```

**Use Cases**:
- Calculator
- Simple scripting
- Global variable storage

### Model 2: Scoped Environment (Planned)

**Structure**: `Vec<HashMap<String, Value>>` (stack of scopes)

**Properties**:
- Lexical scoping
- Variable shadowing
- Natural for closures
- More complex lookup (O(n) where n = depth)
- Requires explicit scope management

**Formal Model**:
```
Env = [Scope₁, Scope₂, ..., Scopeₙ] where Scope = String → Value

lookup(env, name) = 
    if name ∈ dom(Scopeₙ) then Scopeₙ[name]
    else if name ∈ dom(Scopeₙ₋₁) then Scopeₙ₋₁[name]
    ...
    else ⊥

update(env, name, value) = 
    [Scope₁, ..., Scopeₙ[name ↦ value]]

push_scope(env) = env ++ [∅]
pop_scope(env) = env[..n-1]
```

**Use Cases**:
- Functions with local variables
- Closures
- Block-scoped languages

**Design Question**: Should scopes be explicit or implicit?
- **Explicit**: User calls `push_scope()`/`pop_scope()`
- **Implicit**: Automatically managed by rewrite system

### Model 3: Functional Environment (Exploratory)

**Structure**: Immutable map with structural sharing

**Properties**:
- Pure functional
- No mutation
- Easier to reason about
- Performance overhead (copying)
- More complex implementation

**Formal Model**:
```
Env = String → Value (immutable)

lookup(env, name) = env[name] if name ∈ dom(env), else ⊥
update(env, name, value) = env' where env'[name] = value and env'[x] = env[x] for x ≠ name
```

**Use Cases**:
- Functional programming
- Theorem proving
- Concurrent access

**Design Question**: Is functional style worth the performance cost?

### Model 4: Typed Environment (Exploratory)

**Structure**: `HashMap<String, (Type, Value)>`

**Properties**:
- Runtime type checking
- Type-safe operations
- Dynamic typing support
- More storage overhead
- Type checking overhead

**Formal Model**:
```
Env = String → (Type × Value)

lookup(env, name, expected_type) = 
    if name ∈ dom(env) and type_of(env[name]) = expected_type
    then value_of(env[name])
    else ⊥
```

**Use Cases**:
- Dynamic typing
- Gradual typing
- Type inference

**Design Question**: Should types be explicit or inferred?

---

## Integration with Rewrite System

### Current Approach: Environment Relations

Environments integrate with Ascent rewrite rules via relations:

```rust
// Relation declaration
relation env_var_int(String, i32);

// Query in rewrite rule
if env_var(x, v) then (VarRef x) => (NumLit v);

// Create fact in rewrite rule
(Assign x e) => e then env_var(x, e);
```

**Advantages**:
- Declarative: rewrites specify environment operations
- Composable: multiple rewrites can use same environment
- Formalizable: relations are first-class in Ascent

**Challenges**:
- Environment updates are facts, not direct mutation
- Need to convert between environment struct and facts
- Ascent's fixed-point semantics may cause issues

### Alternative Approach: Direct Mutation

Instead of relations, environments could be directly mutated:

```rust
// In rewrite RHS
let mut env = get_env();
env.set("x", value);
```

**Advantages**:
- More intuitive for imperative style
- Direct mutation, no conversion
- Better performance (no fact conversion)

**Disadvantages**:
- Harder to reason about (mutation in rewrite system)
- Less composable
- Breaks declarative style

**Design Question**: Should we support both approaches?

### Hybrid Approach: Environment as State

Treat environment as part of the rewrite state:

```rust
// Rewrite with state
rw_int_with_env(s, t, env_in, env_out) <--
    int(s),
    env_state(env_in),
    // ... pattern matching ...
    let t = ...,
    let env_out = update_env(env_in, "x", value);
```

**Advantages**:
- Explicit state threading
- Easier to reason about
- Supports functional environments

**Disadvantages**:
- More verbose
- Requires state threading through all rewrites

**Design Question**: Is state threading worth the complexity?

---

## Formal Properties

### What Can We Prove About Environments?

#### Property 1: Environment Consistency

**Statement**: If `env_var(x, v₁)` and `env_var(x, v₂)` are both true, then `v₁ = v₂`.

**Formalization**:
```
∀ env, x, v₁, v₂. 
    env_var(x, v₁) ∧ env_var(x, v₂) ⇒ v₁ = v₂
```

**Current Status**: Enforced by `HashMap` (single value per key)

**Discussion**: Should we allow multiple bindings? (e.g., for scoped environments)

#### Property 2: Environment Preservation

**Statement**: If a rewrite doesn't mention `env_var`, the environment is unchanged.

**Formalization**:
```
∀ rewrite r, env₁, env₂.
    (r doesn't contain env_var) ∧ 
    (rewrite applies with env₁) ⇒ 
    (env₂ = env₁)
```

**Current Status**: Not enforced (rewrites can create facts independently)

**Discussion**: Should we enforce this? How?

#### Property 3: Variable Substitution Correctness

**Statement**: If `env_var(x, v)` and rewrite `(VarRef x) => (NumLit v)` applies, then the result is correct.

**Formalization**:
```
∀ env, x, v, term.
    env_var(x, v) ∧ 
    (term = VarRef(x)) ∧ 
    (rewrite applies: term => NumLit(v')) ⇒ 
    v' = v
```

**Current Status**: Enforced by rewrite rule structure

#### Property 4: Assignment Soundness

**Statement**: After `(Assign x e) => e then env_var(x, e)`, the environment contains the correct binding.

**Formalization**:
```
∀ env, x, e, e_val.
    (e evaluates to e_val) ∧ 
    (rewrite applies: Assign(x, e) => e_val then env_var(x, e_val)) ⇒ 
    (lookup(env', x) = e_val) where env' = env ∪ {x ↦ e_val}
```

**Current Status**: Enforced by rewrite rule structure

### Design Question: What Properties Should We Enforce?

**Options**:
1. **Runtime Checks**: Verify properties during execution
2. **Static Analysis**: Check properties at compile time
3. **Formal Verification**: Prove properties using theorem prover
4. **Documentation**: Document properties, rely on implementation

**Recommendation**: Start with documentation, add runtime checks for critical properties.

---

## Design Alternatives

### Alternative 1: Explicit Environment Declaration

**Current**: Automatic generation for all categories

**Alternative**: Explicit declaration in theory:

```rust
theory! {
    name: Calculator,
    exports { ![i32] as Int },
    environments {
        Int  // Explicitly declare environment
    },
    // ...
}
```

**Pros**:
- More explicit
- Can opt-out if not needed
- Can configure environment type

**Cons**:
- More boilerplate
- Easy to forget
- Less automatic

**Decision**: Keep automatic generation (simpler, less error-prone)

### Alternative 2: Single Unified Environment

**Current**: Separate environment per category

**Alternative**: Single environment for all categories:

```rust
pub struct CalculatorEnv {
    int_vars: HashMap<String, Int>,
    // ... other categories
}
```

**Pros**:
- Single struct to manage
- Easier for REPL
- Unified API

**Cons**:
- Less type-safe (mixing categories)
- Harder to reason about
- Less composable

**Decision**: Keep separate environments (better type safety, composability)

### Alternative 3: Environment Traits

**Current**: Concrete structs per category

**Alternative**: Trait-based abstraction:

```rust
trait Environment<T> {
    fn get(&self, name: &str) -> Option<T>;
    fn set(&mut self, name: String, value: T);
    // ...
}
```

**Pros**:
- Abstract over different implementations
- Can swap implementations
- More flexible

**Cons**:
- More complex
- Trait objects have overhead
- May be over-engineering

**Decision**: Defer (current approach is sufficient, can add traits later if needed)

### Alternative 4: Environment as First-Class Term

**Current**: Environment is separate from terms

**Alternative**: Environment is a term category:

```rust
terms {
    Env . EnvType ::= "{" Var "->" Value "}" ;
    Lookup . Value ::= Env "[" Var "]" ;
    Update . Env ::= Env "[" Var ":=" Value "]" ;
}
```

**Pros**:
- Environments are terms
- Can reason about them in rewrite system
- More uniform

**Cons**:
- More complex
- Performance overhead
- Harder to optimize

**Decision**: Reject (separate environments are more efficient and clearer)

---

## Future Directions

### Immediate Lookups: Bypassing the Rewrite System (Planned)

**Goal**: Environment lookups should bypass the Ascent rewrite system entirely.

**Current Limitation**: Variable lookups are mediated through Ascent relations, requiring rewrite system computation.

**Proposed Solution**:
- Add `immediate_lookup(name: &str) -> Option<T>` method to environment structs
- Direct O(1) HashMap access, no rewrite system overhead
- Use in REPL and expression evaluation before parsing
- Keep rewrite system integration for formal environment reasoning

**Implementation**:
1. Direct lookup API on environment structs
2. Variable substitution in expressions: `"x + 2"` → `"5 + 2"` (if x=5)
3. REPL uses direct lookups for immediate feedback
4. Rewrite system handles formal environment state changes

**Benefits**: Faster lookups, simpler REPL interaction, reduced Ascent overhead

---

### Phase 1: Enhanced API

**Goal**: Add convenience methods to environment structs

**Proposed Methods**:
- `contains(name)` - Check if variable exists
- `keys()` - Get all variable names
- `len()` - Get number of bindings
- `set_if_new(name, value)` - Set only if doesn't exist
- `update(other)` - Merge another environment


### Phase 2: Execution State Support

**Goal**: Extend environments to support execution point, shadowed variables, and control flow state

**Design**:
- Add separate storage for execution state: `execution_point: Option<ExecutionPoint>`
- Shadowed variable tracking: `shadowed: HashMap<String, Vec<Value>>` (stack of shadowed values)
- Control flow stack: `call_stack: Vec<Frame>`
- Methods: `set_execution_point()`, `get_execution_point()`, `push_shadowed()`, `pop_shadowed()`, `push_frame()`, `pop_frame()`


**Open Questions**:
- Should execution state be per-category or global?
- How do shadowed variables interact with rewrite rules?
- Should execution point be part of the rewrite state?
- How do we model continuations?

### Phase 3: Scoped Environments

**Goal**: Support lexical scoping with variable shadowing

**Design**:
- Stack-based scopes: `Vec<HashMap<String, Value>>`
- `push_scope()` / `pop_scope()` methods
- Lookup searches from innermost to outermost


**Open Questions**:
- Should scopes be explicit or implicit?
- How do scopes interact with rewrite rules?
- Should we support both flat and scoped in same theory?

### Phase 4: Environment Persistence

**Goal**: Serialize/deserialize environments

**Design**:
- Add `serde` support to environment structs
- `to_json()` / `from_json()` methods
- Support for saving/loading state


**Open Questions**:
- What format? JSON, binary, other?
- How to handle custom types?
- Versioning strategy?

### Phase 5: Functional Environments

**Goal**: Support immutable, functional-style environments

**Design**:
- Immutable map with structural sharing
- `set()` returns new environment
- No mutation


**Open Questions**:
- Performance impact?
- When is functional style needed?
- Can we support both mutable and immutable?

### Phase 6: Typed Environments

**Goal**: Support runtime type information

**Design**:
- Store `(Type, Value)` pairs
- Runtime type checking
- Dynamic typing support


**Open Questions**:
- When is this needed?
- Performance impact?
- Integration with static type system?

---

## Open Questions

### Q1: Should We Support Multiple Environment Models Simultaneously?

**Current**: Only flat environments

**Options**:
1. **Single Model**: Choose one model, use everywhere
2. **Multiple Models**: Support different models, user chooses
3. **Unified Interface**: Trait that abstracts over models

**Discussion Points**:
- What's the use case for multiple models?
- Can we abstract over them?
- Is the complexity worth it?

**Recommendation**: Start with flat, add scoped when needed. Consider trait abstraction if we add more models.

### Q2: How Should Scopes Interact with Rewrite Rules?

**Current**: Flat environment, no scopes

**Options**:
1. **Explicit Scopes**: User manages scopes, rewrites see current scope
2. **Implicit Scopes**: Rewrite system manages scopes automatically
3. **Scope-Aware Rewrites**: Rewrites can push/pop scopes

**Discussion Points**:
- When do scopes change? (function calls, blocks, etc.)
- How do rewrites know about scopes?
- Should scopes be part of rewrite state?

**Recommendation**: Start with explicit scopes, explore implicit later.

### Q3: Should Environments Support Concurrent Access?

**Current**: Single-threaded, mutable

**Options**:
1. **Mutable**: Current approach, requires synchronization
2. **Immutable**: Functional style, no synchronization needed
3. **Concurrent**: Thread-safe with locks or atomics

**Discussion Points**:
- Do we need concurrent access?
- Performance impact of synchronization?
- Is immutable style sufficient?

**Recommendation**: Defer until we have a concrete use case.

### Q4: How Do We Model Environment Properties Formally?

**Current**: Informal documentation

**Options**:
1. **Informal**: Document properties, rely on implementation
2. **Formal Specification**: Write properties in logic
3. **Proofs**: Prove properties using theorem prover
4. **Runtime Checks**: Verify properties during execution

**Discussion Points**:
- What properties are critical?
- How do we verify them?
- Is formal verification worth the effort?

**Recommendation**: Start with documentation and runtime checks for critical properties. Consider formal verification for safety-critical applications.

### Q5: How Should Execution State Be Organized in Environments?

**Current**: Only variable bindings

**Options**:
1. **Unified Storage**: All state (variables, execution point, shadowed vars) in one structure
2. **Separate Fields**: Different fields for different state types (`vars`, `execution_point`, `shadowed`)
3. **Namespaced Keys**: Use key prefixes (`var:x`, `exec:pc`, `shadowed:x`)
4. **Separate Environments**: Different environment types for different state

**Discussion Points**:
- How do different state types interact?
- Should execution state be per-category or global?
- How do rewrite rules access different state types?
- Performance implications of different organizations?

**Recommendation**: Start with separate fields for clarity, consider unified storage if performance becomes an issue.

### Q6: Should Environments Be Part of the Term Language?

**Current**: Separate from terms

**Options**:
1. **Separate**: Current approach, environments are external
2. **First-Class**: Environments are terms, can be manipulated
3. **Hybrid**: Environments are separate but can be converted to terms

**Discussion Points**:
- Do we need to reason about environments in rewrite system?
- Performance impact?
- Complexity trade-off?

**Recommendation**: Keep separate (current approach). Revisit if we need to reason about environments as terms.

---

## Review Checklist

Please review the following aspects:

- **Environment Models**: Are the identified models sufficient? Missing any?
- **Current Implementation**: Is the automatic generation approach correct?
- **Integration**: Is the rewrite system integration appropriate?
- **Formal Properties**: Are the identified properties correct? Missing any?
- **Design Alternatives**: Are the decisions sound? Should we reconsider any?
- **Future Directions**: Are the planned phases appropriate? Priorities correct?
- **Open Questions**: Are there other questions we should address?

---

## References

### Implementation Files

**Location**: `macros/src/codegen/ast_gen.rs`
- Environment struct generation (`generate_env_infrastructure()`)

**Location**: `macros/src/ascent/relations.rs`
- Environment relation generation (`generate_env_relations()`)

**Location**: `macros/src/ascent/rewrites/clauses.rs`
- `env_var` condition handling in rewrite rules

**Location**: `macros/src/ast/types.rs`
- Environment query/action syntax (`Condition::EnvQuery`, `EnvAction`)

### Example Theories

**Location**: `theories/src/calculator.rs`
- Calculator with native type environment

**Location**: `theories/src/rhocalc.rs`
- RhoCalc with custom type environments

**Location**: `theories/tests/calculator.rs`
- Environment usage examples

### Related Design Documents

- `design/made/native_types_and_operations.md` - Native type integration
- `design/made/ascent_generation.md` - Rewrite system details

### Verification Tests

**Location**: `examples/env_infrastructure_verify.rs`
- Comprehensive verification of environment infrastructure

**Location**: `examples/rhocalc_env_test.rs`
- Usage examples for RhoCalc environments

---

**Last Updated**: December 2025
**Status**: Core implementation complete, design evolving based on the team feedback

