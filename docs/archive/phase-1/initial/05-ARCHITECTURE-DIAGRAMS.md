# Architecture Diagrams

Visual representations of the proposed MeTTaIL Rust implementation.

---

## Current Architecture (Scala + BNFC)

```
┌─────────────────────────────────────────────────────────┐
│                    MeTTaIL (Scala)                       │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Rholang.module (text file)                         │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ BNFC Parser (generated from .cf grammar)           │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ InstInterpreter (theory composition)               │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ BasePres (presentation/grammar output)             │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ BNFC Output (generated grammar for Rholang)        │ │
│  └────────────────────────────────────────────────────┘ │
└──────────────────────┬──────────────────────────────────┘
                       │ (FFI boundary)
                       ↓
┌─────────────────────────────────────────────────────────┐
│                  rholang/ (Rust)                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │ External Parser (rholang-parser crate)             │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Compiler & Normalizer                              │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Interpreter (reduce/dispatch)                      │ │
│  └──────────────┬─────────────────────────────────────┘ │
└─────────────────┼──────────────────────────────────────┘
                  ↓
┌─────────────────────────────────────────────────────────┐
│                 rspace++/ (Rust)                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Tuple Space (pattern matching, storage)            │ │
│  └────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘

Problems:
- Language boundary (Scala ↔ Rust)
- Runtime validation only
- External parser dependency
- No network transmission path
```

---

## Proposed: Procedural Macros Approach

```
┌─────────────────────────────────────────────────────────┐
│              macros/ (Rust)                      │
│                                                          │
│  theory! {                                               │
│      name: Rholang,                                      │
│      // ... theory definition in Rust syntax            │
│  }                                                       │
│       │                                                  │
│       ↓ (compile-time expansion)                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Proc Macro Expansion                                │ │
│  │ 1. Parse theory! {} syntax (syn)                    │ │
│  │ 2. Validate (compile-time!)                         │ │
│  │ 3. Generate code (quote)                            │ │
│  └──────────────┬─────────────────────────────────────┘ │
│                 ↓                                        │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Generated Rust Code:                                │ │
│  │ • pub enum Proc { ... }                             │ │
│  │ • pub enum Name { ... }                             │ │
│  │ • impl RholangParser { ... }                        │ │
│  │ • impl RholangInterpreter { ... }                   │ │
│  └────────────────────────────────────────────────────┘ │
└──────────────────────┬──────────────────────────────────┘
                       │ (native Rust, no boundary!)
                       ↓
┌─────────────────────────────────────────────────────────┐
│                  rholang/ (Rust)                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Use generated types directly:                       │ │
│  │ let ast = Rholang::parse(input)?;                   │ │
│  │ Rholang::interpret(&mut space, ast);                │ │
│  └──────────────┬─────────────────────────────────────┘ │
└─────────────────┼──────────────────────────────────────┘
                  ↓
┌─────────────────────────────────────────────────────────┐
│                 rspace++/ (Rust)                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │ Tuple Space (unchanged)                             │ │
│  └────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘

Benefits:
✓ Compile-time validation
✓ Type-safe ASTs
✓ Zero overhead
✓ Native Rust integration
✓ IDE support

Challenges:
✗ Complex implementation
✗ Dynamic loading difficult
```

---

## Proposed: Hybrid Approach (Recommended)

```
                      ┌──────────────────────┐
                      │  Theory Definition   │
                      └──────────┬───────────┘
                                 │
                  ┌──────────────┴──────────────┐
                  │                             │
            Static (known)              Dynamic (network)
                  │                             │
                  ↓                             ↓
    ┌──────────────────────────┐   ┌──────────────────────────┐
    │  Compile-Time Path       │   │   Runtime Path           │
    │  (Procedural Macros)     │   │   (Interpreter)          │
    └──────────┬───────────────┘   └──────────┬───────────────┘
               │                               │
               │ theory! { ... }               │ parse_module(...)
               ↓                               ↓
    ┌──────────────────────────┐   ┌──────────────────────────┐
    │  Generated at             │   │  Interpreted at          │
    │  Compile Time:            │   │  Runtime:                │
    │  • AST types              │   │  • Dynamic dispatch      │
    │  • Parser                 │   │  • Validation            │
    │  • Interpreter            │   │  • Serializable          │
    └──────────┬───────────────┘   └──────────┬───────────────┘
               │                               │
               └───────────┬───────────────────┘
                           ↓
              ┌──────────────────────────────┐
              │     Unified Interface        │
              │  trait Theory {              │
              │    fn parse(...);            │
              │    fn interpret(...);        │
              │  }                           │
              └──────────────┬───────────────┘
                             ↓
              ┌──────────────────────────────┐
              │        rholang/               │
              │     (uses either path)        │
              └──────────────┬───────────────┘
                             ↓
              ┌──────────────────────────────┐
              │       rspace++/               │
              └──────────────────────────────┘

Decision Flow:
  Is theory known at compile time?
    ├─ Yes → Use macro path (optimal)
    └─ No  → Use runtime path (flexible)
```

---

## Theory Composition Flow

```
Theory A: ParMonoid
┌────────────────────┐
│ exports { Proc; }  │
│ terms {            │
│   PZero . Proc     │
│   PPar . Proc      │
│ }                  │
└─────────┬──────────┘
          │
          │ Conjunction (∧)
          ↓
Theory B: QuoteDropCalc
┌────────────────────┐
│ extends ParMonoid  │
│ exports { Name; }  │
│ terms {            │
│   PDrop . Proc     │
│   NQuote . Name    │
│ }                  │
└─────────┬──────────┘
          │
          │ Disjunction (∨)
          ↓
Theory C: RhoCalc
┌────────────────────┐
│ extends QDCalc     │
│ terms {            │
│   PSend . Proc     │
│   PRecv . Proc     │
│ }                  │
│ rewrites {         │
│   RComm: ...       │
│ }                  │
└─────────┬──────────┘
          │
          │ Instantiate
          ↓
    FreeRholang
┌────────────────────┐
│ Full language def  │
│ All categories     │
│ All terms          │
│ All rewrites       │
└────────────────────┘

Implementation Approaches:

Macros:
  theory! { A }  ∧  theory! { B }  →  Combined at compile time

Runtime:
  let a = interpret(A);
  let b = interpret(B);
  let combined = a.conjoin(b);
```

---

## Network Transmission (f1r3fly)

```
         Node A                         Network                Node B
┌─────────────────────┐                            ┌─────────────────────┐
│  Define Theory      │                            │                     │
│  theory! { X }      │                            │                     │
│         │           │                            │                     │
│         ↓           │                            │                     │
│  Serialize Theory   │                            │                     │
│  TheoryDescriptor { │                            │                     │
│    name: "X",       │                            │                     │
│    exports: [...],  │                            │                     │
│    terms: [...],    │                            │                     │
│    ...              │                            │                     │
│  }                  │                            │                     │
│         │           │                            │                     │
│         ↓           │                            │                     │
│  bincode::serialize │                            │                     │
│         │           │                            │                     │
│         ↓           │                            │                     │
│  ┌───────────┐     │       ┌─────────┐          │                     │
│  │   bytes   │────────────→│ Network │─────────────────────────────────│
│  └───────────┘     │       └─────────┘          │                     │
│                    │                            │         ↓           │
│                    │                            │  Receive bytes      │
│                    │                            │         ↓           │
│                    │                            │  Validate Theory    │
│                    │                            │  • Categories valid │
│                    │                            │  • No malicious code│
│                    │                            │  • Resource bounds  │
│                    │                            │         ↓           │
│                    │                            │  Instantiate Theory │
│                    │                            │  let theory = ...   │
│                    │                            │         ↓           │
│                    │                            │  Use Theory         │
│                    │                            │  let ast = theory   │
│                    │                            │    .parse(prog)?;   │
│                    │                            │  theory.interpret   │
│                    │                            │    (&mut space, ast)│
└─────────────────────┘                            └─────────────────────┘

Security Layers:
1. Schema validation (valid theory structure)
2. Semantic validation (categories, types consistent)
3. Resource limits (prevent DoS)
4. Sandboxing (WASM or restricted interpreter)
```

---

## Minimal POC Scope

```
Input: theory! { ... }
  ↓
┌────────────────────────────────────────┐
│ Phase 1: Parse Macro Input             │
│ • Use syn to parse theory! {} syntax   │
│ • Build TheoryDef AST                  │
└───────────┬────────────────────────────┘
            ↓
┌────────────────────────────────────────┐
│ Phase 2: Compile-Time Validation       │
│ • Check all categories exported        │
│ • Check no dangling references         │
│ • Emit compile errors if invalid       │
└───────────┬────────────────────────────┘
            ↓
┌────────────────────────────────────────┐
│ Phase 3: Code Generation                │
│ • Generate enum for each category      │
│ • Generate variants for each term      │
│ • Use quote to emit Rust code          │
└───────────┬────────────────────────────┘
            ↓
Output: Generated Rust Code
  pub enum Elem {
      Zero,
      Plus(Box<Elem>, Box<Elem>),
  }

Scope Limits:
✓ Single theory (no composition)
✓ Simple terms (no binders)
✓ Basic validation (category references)
✗ NO parser generation
✗ NO interpreter generation
✗ NO rewrite rules
✗ NO equations
✗ NO parameterization
```

---

## Implementation Timeline

```
Week 1
├─ POC Implementation (11-14 hours)
│  ├─ Setup workspace (1h)
│  ├─ AST definition (30m)
│  ├─ Parser logic (2h)
│  ├─ Validation (2h)
│  ├─ Code generation (3h)
│  ├─ Testing (2h)
│  └─ Documentation (1h)
│
└─ Decision Point
   ├─ Macros viable? → Continue
   └─ Too complex? → Runtime only

Month 1
├─ Runtime Implementation (if approved)
│  ├─ Week 1: Parser for .module files
│  ├─ Week 2: Theory interpreter
│  ├─ Week 3: Validation logic
│  └─ Week 4: Testing & integration
│
└─ Checkpoint: Runtime working

Month 2
├─ Network Integration
│  ├─ Serialization protocol
│  ├─ Dynamic loading
│  ├─ Security validation
│  └─ f1r3fly integration
│
└─ Checkpoint: Language transmission

Month 3+ (Optional)
├─ Full Macro Implementation
│  ├─ Expand macro features
│  ├─ Parser generation
│  ├─ Rewrite rules
│  ├─ Theory composition
│  └─ Optimization
│
└─ Checkpoint: Hybrid system complete
```

---

## Risk Mitigation Strategy

```
┌─────────────────────────────────────────────────────────┐
│                   Risk Management                        │
└─────────────────────────────────────────────────────────┘

Risk 1: Macros Too Complex
├─ Probability: Medium
├─ Impact: High (wasted effort)
└─ Mitigation:
   ├─ POC validates early (11h)
   ├─ Time-boxed exploration
   └─ Fallback: Runtime only

Risk 2: Performance Issues
├─ Probability: Low
├─ Impact: Medium
└─ Mitigation:
   ├─ Profile early
   ├─ Optimize hot paths
   └─ Optional JIT (Cranelift)

Risk 3: Team Unfamiliarity
├─ Probability: Medium
├─ Impact: Low (slower dev)
└─ Mitigation:
   ├─ Comprehensive docs
   ├─ Training sessions
   └─ Gradual adoption

Risk 4: Scope Creep
├─ Probability: High
├─ Impact: Medium (delays)
└─ Mitigation:
   ├─ Clear POC scope
   ├─ Phase-gated approval
   └─ MVP mindset

Decision Tree:
┌──────────────────┐
│  Implement POC   │
└────────┬─────────┘
         │
    Is it viable?
    ├─ Yes ──→ Continue to runtime
    │          ├─ Works well? → Add macros
    │          └─ Sufficient? → Done
    │
    └─ No ───→ Runtime only
               ├─ Good enough? → Done
               └─ Not enough? → Revisit
```

This visual summary should help understand the architecture and decision flow!

