# MeTTaIL: System Architecture

Technical overview of MeTTaIL's implementation architecture.

---

## High-Level Architecture

```
┌─────────────────────────────────────────────┐
│         User Theory Definition              │
│         (theory! { ... })                   │
└──────────────────┬──────────────────────────┘
                   │
         ┌─────────▼──────────┐
         │   Procedural       │
         │   Macro Layer      │
         │   (mettail-macros) │
         └─────────┬──────────┘
                   │
    ┌──────────────┼──────────────┐
    │              │              │
    ▼              ▼              ▼
┌────────┐   ┌─────────┐   ┌──────────┐
│  Rust  │   │ Parser  │   │ Ascent   │
│  AST   │   │(LALRPOP)│   │ Datalog  │
└────┬───┘   └────┬────┘   └────┬─────┘
     │            │              │
     └────────────┼──────────────┘
                  │
         ┌────────▼────────┐
         │   Runtime       │
         │   (collections, │
         │    bindings)    │
         └────────┬────────┘
                  │
         ┌────────▼────────┐
         │   Application   │
         │   (REPL, tests) │
         └─────────────────┘
```

---

## Component Details

### Macro Layer (`macros/`)

Transforms theory definitions into executable code through multiple stages:

#### 1. AST (`ast/`)
```
language! { ... }
    ↓ syn::parse
LanguageDef {
    name: Ident,
    types: Vec<LangType>,
    terms: Vec<GrammarRule>,
    equations: Vec<Equation>,
    rewrites: Vec<RewriteRule>,
}
```

**Key Types**:
- `TheoryDef` - Complete theory specification
- `GrammarRule` - Constructor definition with category
- `Equation` - Equality axiom
- `RewriteRule` - Reduction rule
- `Expr` - Pattern expression (Var, Apply, CollectionPattern, Subst)

#### 2. Validation (`validation/`)

Semantic checking before code generation:

**Checks**:
- All referenced categories are defined
- All referenced constructors exist
- Variables are properly bound
- Freshness conditions reference bound vars
- Type consistency across equations/rewrites

**Modules**:
- `validator.rs` - Main validation orchestration
- `typechecker.rs` - Category inference and checking
- `error.rs` - Error types and messages

#### 3. Code Generation (`gen/`)

Generate Rust code from validated AST:

**`types/enums.rs`**: Rust enum generation
```rust
pub enum Proc {
    PZero,
    PPar(HashBag<Proc>),
    PNew(Scope<Proc>),
    // ...
}
```

**`syntax/parser/`**: LALRPOP grammar generation
- `lalrpop.rs` - Grammar string generation
- `actions.rs` - Semantic actions
- `writer.rs` - File writing

**`syntax/display.rs`**: Pretty-printing implementation
```rust
impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Proc::PNew(scope) => write!(f, "new({})", scope),
            // ...
        }
    }
}
```

**`term_ops/subst.rs`**: Substitution functions
```rust
impl Proc {
    pub fn substitute_name(&self, var: &Binder<String>, term: &Name) -> Proc {
        // Capture-avoiding substitution
    }
}
```

**`term_gen/`**: Term generation
- `exhaustive.rs` - All terms at depth N
- `random.rs` - Random term sampling

#### 4. Ascent Generation (`datalog/`)

Generate Datalog rules for term rewriting:

**Generated Relations**:
- `proc(Proc)` - All reachable terms
- `eq_proc(Proc, Proc)` - Equivalence relation
- `rw_proc(Proc, Proc)` - Rewrite relation
- `ppar_contains(Proc, Proc)` - Collection projection

**Generated Rules**:
1. **Exploration**: `proc(c1) <-- proc(c0), rw_proc(c0, c1)`
2. **Deconstruction**: Extract subterms
3. **Equations**: Reflexivity + congruence + axioms
4. **Rewrites**: Pattern → RHS with freshness
5. **Congruence**: Propagate rewrites through constructors

---

### Runtime Layer (`runtime/`)

**Purpose**: Provide runtime types and utilities for generated code.

**Key Components**:

#### Collections
```rust
pub struct HashBag<T: Hash + Eq> {
    map: HashMap<T, usize>,  // element → count
}
```
- O(1) insert, remove, contains
- O(1) equality (structural)
- Implements Ord for total ordering

#### Bindings
```rust
pub struct Scope<T> {
    binder: Binder<String>,
    body: Box<T>,
}
```
- Wrapper around `moniker::Scope`
- Alpha-equivalence via `moniker`
- Capture-avoiding substitution

#### Variable Representation
```rust
pub enum Var<N> {
    Free(FreeVar<N>),
    Bound(BoundVar),
}
```

#### Native types (Int, Float, Bool, Str)
Category enums for native types (e.g. `![i32] as Int`, `![f64] as Float`) are generated like other categories. Float (f32/f64) is represented via the runtime **canonical float** type (`CanonicalFloat64`/`CanonicalFloat32` in `runtime/src/canonical_float.rs`) so that Float satisfies `Eq`/`Hash`/`Ord` and can be used in Ascent relations. See `docs/design/exploring/float-support-ascent.md` for design and semantics.

---

## Ascent Execution Model

### Relation Materialization

Ascent uses **bottom-up evaluation**:

1. **Seed**: Add initial terms to `proc(...)` relation
2. **Iterate**: Apply rules until fixpoint
3. **Materialize**: All derived facts stored in memory

### Rule Types

#### Deconstruction Rules
```datalog
% Extract subterms
name(field) <-- proc(t), if let Proc::PDrop(field) = t
```

#### Equation Rules
```datalog
% Reflexivity
eq_proc(t, t) <-- proc(t)

% Congruence
eq_proc(PNew(x, s), PNew(x, t)) <--
    proc(PNew(x, s)),
    eq_proc(s, t)

% User axioms
eq_name(NQuote(PDrop(N)), N) <-- name(N)
```

#### Rewrite Rules
```datalog
% Base rewrites
rw_proc(s, t) <--
    proc(s),
    if let Proc::PPar(bag) = s,
    for (elem, _) in bag,
    if let Proc::PDrop(...) = elem,
    // ... pattern matching
    let t = (...)  // RHS construction
```

#### Congruence Rules
```datalog
% Propagate rewrites through constructors
rw_proc(PDrop(s), PDrop(t)) <--
    proc(PDrop(s)),
    rw_proc(s, t)
```

---

## Pattern Matching Strategy

### Simple Patterns

Direct `if let` matching:
```rust
if let Proc::PDrop(n) = term {
    // n is bound
}
```

### Collection Patterns

Iterate over collection elements:
```rust
if let Proc::PPar(bag) = parent {
    for (elem, _count) in bag.iter() {
        // elem is bound
    }
}
```

### Shared Variables

Use projection relations and joins:
```rust
// Project both patterns
in_proj(parent, n, x, p, elem1) <-- ...
out_proj(parent, n, q, elem2) <-- ...

// Join on shared variable n
rw(parent, result) <--
    in_proj(parent, n, x, p, elem1),
    out_proj(parent, n, q, elem2),
    eq_name(n, n)  // Ensure same n
```

### Nested Patterns

Recursive pattern matching with intermediate variables:
```rust
if let Proc::PDrop(inner) = elem {
    let inner_val = inner.as_ref();
    if let Name::NQuote(quoted) = inner_val {
        // quoted is bound
    }
}
```

---

## Optimization Techniques

### 1. Lazy Deconstruction
Only generate deconstruction rules for constructors used in rewrite patterns.

**Before**: 100+ deconstruction rules
**After**: ~10 rules (only what's needed)
**Speedup**: 42x

### 2. Projection-Based Matching
Generate specialized projection relations instead of nested iteration.

**Benefit**: Efficient joins in Ascent, handles arbitrary nesting.

### 3. Automatic Flattening
Flatten collections during construction (not during matching).

**Benefit**: Fewer terms to explore, simpler equality.

### 4. Type-Aware Generation
Generate category-specific relations (not generic `term(...)`).

**Benefit**: Better type safety, smaller relation sizes.

---

## Future Architecture Evolution

### Near-Term: Native Compilation

```
Theory → IR → Cranelift → Native Code
                        ↘ WASM
```

**Changes**:
- New `ir/` module for intermediate representation
- Cranelift backend in `codegen/native/`
- WASM backend in `codegen/wasm/`
- Keep Ascent backend for rapid development

### Long-Term: Distributed Runtime

```
┌─────────┐   ┌─────────┐   ┌─────────┐
│  Node 1 │───│  Node 2 │───│  Node 3 │
│ (Ascent)│   │ (Ascent)│   │ (Ascent)│
└────┬────┘   └────┬────┘   └────┬────┘
     └─────────────┼─────────────┘
                   │
            ┌──────▼───────┐
            │  Coordinator │
            │  (Consensus) │
            └──────────────┘
```

**Changes**:
- Distributed Ascent backend
- Network protocol for term exchange
- Consensus on reduction order
- Fault tolerance and recovery

---

## Key Invariants

### Type Safety
- Generated code always type-checks
- Category mismatches caught at theory compile-time
- No runtime type errors possible

### Correctness
- Alpha-equivalence via moniker (proven correct)
- Ascent fixpoint computation (always terminates)
- Equations are symmetric and transitive (via `eqrel`)

### Performance
- O(1) collection equality
- Efficient indexed joins for shared variables
- Lazy computation where possible

---

## See Also

- `main_goals.md` - Project vision
- `getting_started.md` - Quick start guide
- `design/` - Detailed design docs
- Source code comments - Implementation details

**Last Updated**: December 2025

