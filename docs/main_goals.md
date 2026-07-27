# Theory Features

## Rust-native types and functions
use stdlib in theories. (may need a "registry" of accepted types and funcs.)

- Th(Calculator): 
    ```
    exports { ![i32] as Int }
    terms { Plus . Int ::= Int "+" Int }
    rewrites { (Plus M N) => M + N }
    ```
(equations are automatic when evaluated in rust)

## Binding support
1. specify the location of binding (currently "\<X\> Y" binds X to Y)

- Th(Rholang):
```
PInput . Proc ::= "for" "(" $x0:Name "<-" Name ")" "{" (x0)Proc "}"
```

2. first-class abstraction.
- form type [Name->Proc] whose terms \x:Name.p:Proc have an eval method

Later:

3. multiple binding locations (join)

```
{ n1!(a) | n2!(b) | for(x<-n1,y<-n2){p} } => p[a/x,b/y]
```

(will have to add new type Recv, with<br>
    ```ForBind . Recv ::= List(<Name>) "<-" Name``` and <br>
    ```PInput . Proc ::= "for" "(" List(Recv) ")" "{" Proc "}"```<br>
-- collections of bindings, this may be complex.)

## Use Syntax for Eqs/Rws

- ```@(*(n)) == n``` instead of ```(NQuote (PDrop N)) == N```

- ```p[n/x]``` instead of ```(subst x P N)```

## Named Rewrites

```
COMM . { n!(q) | for(x<-n){p} } => p[@q/x]
```

## Data Structures
Lists, Sets, Maps, Trees, user-defined

```
terms {
    POutput . Proc ::= Name "!" List(Proc) sep "," delim "(" ")"
    PInput . Proc ::= "for" "(" $xs:List(Name) "<-" Name ")" "{" xs.Proc "}"
}
```

(then COMM has to check that lengths match!)

## Composition & Modularity
import theories in other theories

(already supported in ascent; maybe can use as a guide)

## Term Definitions
define (parameterized) terms and use them in programs.

```
defs { 
    D(n:Name):Proc = for(x<-n){{\*(x) | n!(\*(x))}};
}
```

## Predicate Type System
**Current**: Category-based type checking
**Needed**:
- Predicates on terms: `x:phi` where `phi` is a logical formula
- Conditional rewrites: `for(x:phi <- n){q} | n!(p) => q[p/x]` only when `p` satisfies `phi`
- Type inference for predicates
- Decidable checking strategy

---

# Theory Exploration

**Goal**: Make theories debuggable, testable, and understandable through automated exploration.

## Term Generation
**Current**: Basic exhaustive and random generation (not yet working for collections)
**Needed**:
- Full collection support in generators
- Property-based testing (QuickCheck-style)
- Counterexample shrinking
- Coverage metrics

## Interactive Exploration (REPL)
**Current**: Basic REPL with rewrite navigation
**Needed**:
- History and backtracking
- Equivalence class visualization
- Path finding between terms
- Statistics dashboard
- Query language for graph exploration

## Fuzzing & Testing
**Needed**:
- Automatic test case generation
- Confluence checking
- Termination analysis
- Property verification
- Regression test suites

---


# Term Execution & Performance

**Goal**: Execute term rewrites at production speed for real-world applications.

**Near-Term** (6 months):
- Native code generation via Cranelift
- 100x speedup target
- < 1 second compile time
- JIT for hot rewrites

**Long-Term** (1+ years):
- Distributed execution across nodes
- Incremental recomputation
- Parallel Ascent backend
- < 10ms latency for federated rewrites

---

# Term Communication

**Goal**: Integrate MeTTaIL theories with f1r3fly distributed network for real-world execution.

**Background**: f1r3fly is a network running RhoLang (Rho Calculus) for decentralized computation.

**Integration Points**:
- Network protocol for term exchange
- Serialization/deserialization
- Remote rewriting capabilities
- Consensus on reduction order
- Fault tolerance

**Architecture**:
```
MeTTaIL Theory ─→ Compiled Code ─→ f1r3fly Node
                                   ├─ Local Execution
                                   ├─ Remote Communication
                                   └─ Network Coordination
```

**Milestones**:
1. Define wire protocol for terms
2. Implement serialization for runtime types
3. Build f1r3fly adapter/shim
4. Deploy test theory on network
5. Full integration with production f1r3fly

---


# Theory Translation

**Goal**: Automatically compile between theories with proven correctness.

**Current**: None - each theory is isolated

**Vision**: Define formal mappings between theories to enable:
- Lambda Calculus ↔ Rho Calculus
- High-level spec → Optimized implementation
- Cross-theory reasoning and proof reuse

## Theory Morphisms
- Define translation functions between theories
- Prove correctness conditions (semantics preservation)
- Handle partial translations (not all constructs map)
- Generate bidirectional translators where possible

## Use Cases
1. **Optimization**: Translate high-level theory to efficient low-level theory
2. **Interop**: Execute Lambda terms in Rho Calculus runtime
3. **Verification**: Prove in one theory, execute in another
4. **Legacy**: Formalize old language, translate to modern theory

## Example
```rust
morphism! {
    name: LambdaToRho,
    from: LambdaCalc,
    to: Rholang,

    // λx.M ↦ new(x.P) where M ↦ P
    translate Lam(x, m) => PNew(x, translate(m)),

    // M N ↦ for(y <- M){N!(*y)}
    translate App(m, n) => ...,
}
```

---
