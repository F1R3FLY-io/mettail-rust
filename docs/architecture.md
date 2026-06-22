# MeTTaIL: System Architecture

Technical overview of MeTTaIL's implementation architecture.

> **Authoritative runtime/backend reference:**
> [`architecture/runtime-backend-spine.md`](architecture/runtime-backend-spine.md).
> The production rewrite path is **Dovetail** (exact-key equality saturation over a
> runtime e-graph) plus the **Rho-native** backend. **Ascent/CESK appear below only as
> historical/oracle context.** The generated Ascent engine (structs, `eqrel`, BYODS
> provider, `oracle-ascent` feature) was **removed in P6**; `Language::run_ascent`
> survives as a fail-closed differential-oracle hook only. Sections still written in
> the Ascent present tense are retained for history, not as the current execution path.

---

## High-Level Architecture

The current architecture should be read in two layers:

| Layer | Current role |
|---|---|
| parser and language-definition layer | `language!` and the active WPDA parser remain the source of typed language terms and generated metadata |
| runtime backend layer | Dovetail is the replacement rewrite engine, and the Rho-native backend is the replacement execution path for the CESK runtime backend |

The older generated Ascent path still exists as reference/oracle evidence
during rollout, but it is legacy for production rewrite execution. The runtime
replacement spine is:

`language! spec → LanguageDef → LanguageMetadata → typed AST → DovetailRunReport`

and then either:

`DovetailRunReport → RuntimeBackendOutput::Dovetail`

or:

`DovetailRunReport → RhoNet plan → rhoapi::Par → RhoRuntime observations → RuntimeBackendReport`

This means an implementation discussion about parsing is usually about
MeTTaIL/WPDA, an implementation discussion about rewrite correctness is usually
about Dovetail, and an implementation discussion about host parallel execution
is usually about the Rho backend and F1r3node.

For the shortest cohesive walkthrough of those handoffs, read
[architecture/runtime-backend-spine.md](architecture/runtime-backend-spine.md)
before entering the detailed Dovetail and Rho-native suites. That page defines
the exact artifact chain, the two production runtime lanes, and the terms that
must not be conflated.

```
┌─────────────────────────────────────────────┐
│        User Language Definition             │
│        (language! { ... })                  │
└──────────────────┬──────────────────────────┘
                   │
         ┌─────────▼──────────┐
         │   Procedural       │
         │   Macro Layer      │
         │   (macros) │
         └─────────┬──────────┘
                   │
    ┌──────────────┼──────────────┐
    │              │              │
    ▼              ▼              ▼
┌────────┐   ┌─────────┐   ┌──────────┐
│  Rust  │   │ Parser  │   │ Ascent   │
│  AST   │   │(WPDA +  │   │ Datalog  │
│        │   │syntax)  │   │          │
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

> **Diagram note:** the third macro output above (labeled "Ascent Datalog") is
> **historical**. The generated Ascent engine was removed in P6; the macro now emits a
> **Dovetail** rewrite inventory (+ optional **Rho-native** lowering) as the production
> rewrite/execution path. Ascent survives only as the fail-closed `run_ascent`
> differential oracle.

---

## Rewrite Engine Architecture Tracks

The diagram above is historical context for the existing generated Ascent
execution path, which is legacy for production rewrite execution. Dovetail
itself is documented in
[architecture/dovetail/README.md](architecture/dovetail/README.md). That suite
covers the standalone rewrite engine: exact-key equality saturation, rules as
data, weighted-tree-automaton interpretation, checked extraction, cyclic
boundedness, formal verification, tests, traceability, and engineering
handoff.

The downstream Rho-native execution design is documented separately in
[architecture/rho-native-integration/README.md](architecture/rho-native-integration/README.md).
That suite is scoped to replacement of the CESK runtime backend path and the
Ascent production rewrite backend; it does not make the active WPDA
parser/recognizer legacy, and it retains Ascent only as a reference/oracle path
for differential evidence during rollout.

The *theory-of-guards* layer — the semantic-predicate substrate that decides which
guarded rewrites and communications a generated language may perform — is documented
in a third suite,
[architecture/semantic-predicates/README.md](architecture/semantic-predicates/README.md).
That suite covers the effective Boolean algebras, symbolic finite automata and
transducers, the Heyting algebra tower for behavioral constraints, and the
end-to-end path from a `language!` guard through classification and the fail-closed
flip gate to run-time enforcement.

Together, the three suites explain how MeTTaIL source snippets are parsed into
typed terms, how the semantic-predicate substrate classifies their guards, how
Dovetail supplies substrate-neutral rewrite semantics, how the Rho backend lowers
rewrite networks into normalized Rholang AST and RSpace dataflow, and how
F1r3node's Rho machine schedules enabled rewrites in parallel.

---

## Component Details

### Macro Layer (`macros/`)

Transforms `language!` definitions into executable code through multiple stages:

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
- `LanguageDef` - Complete language specification (parsed from `language!`)
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

**`syntax/parser/` and WPDA codegen**: generated syntax and active parser/recognizer support
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

#### 4. Historical: Ascent oracle generation (`datalog/`) — retired in production

> Retained for history. The generated Ascent/Datalog engine was **removed in P6**; the
> production rewrite engine is **Dovetail**. The rules below describe the legacy oracle
> path that the fail-closed `Language::run_ascent` hook can still reproduce for
> differential evidence.

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
Category enums for native types (e.g. `![i32] as Int`, `![f64] as Float`) are generated like other categories. Float (f32/f64) is represented via the runtime **canonical float** type (`CanonicalFloat64`/`CanonicalFloat32` in `runtime/src/canonical_float.rs`) so that Float satisfies `Eq`/`Hash`/`Ord` and is usable as a Dovetail e-graph key (and in legacy Ascent oracle relations). See `docs/design/exploring/float-support-ascent.md` for design and semantics.

---

## Historical: Ascent oracle execution model

> Retained for history (legacy oracle path). Production execution is the Dovetail
> direct lane or the Rho-native lane; see the
> [runtime-backend spine](architecture/runtime-backend-spine.md).

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
- Keep Ascent only as a reference/oracle backend for differential regression
  evidence while Dovetail/Rho becomes the production rewrite path

### Long-Term: Distributed Runtime

```
┌─────────┐   ┌─────────┐   ┌─────────┐
│  Node 1 │───│  Node 2 │───│  Node 3 │
│  (Rho)  │   │  (Rho)  │   │  (Rho)  │
└────┬────┘   └────┬────┘   └────┬────┘
     └─────────────┼─────────────┘
                   │
            ┌──────▼───────┐
            │  Coordinator │
            │  (Consensus) │
            └──────────────┘
```

**Changes**:
- Distributed Rho-native backend driven by Dovetail semantics
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
- Dovetail exact-key equality/rewrite saturation with checked, complete extraction
  (`SatReport` / `DovetailRunReport`), backed by zero-admission Rocq proofs
- Rho-native lowering is total-or-explicit-reject; the bridge is a formally-verified
  one-way `MeTTaIL → F1r3node` dependency
- *(Historical)* Ascent fixpoint computation via `eqrel` — oracle path only

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

**Last Updated**: 2026-06-21 (Ascent/CESK reconciled to the runtime-backend spine; production path is Dovetail + Rho-native)
