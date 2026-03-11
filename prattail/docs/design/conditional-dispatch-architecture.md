# Conditional Dispatch Architecture

End-to-end architecture for the conditional dispatch pipeline, from grammar
input through Phase 7B module spawning, covering grammar-level and
predicate-level dispatch, feature gates, cost-benefit integration, and the
sequential fallback path.

**Key source files:**

| File | Role |
|------|------|
| `prattail/src/predicate_dispatch.rs` | Dispatch classification, algebra, SFA verification |
| `prattail/src/pipeline.rs` | `run_math_analyses_parallel()`, `run_math_analyses_sequential()` |
| `prattail/src/cost_benefit.rs` | `Optimization::PredicateDispatch`, `GrammarProfile` |

---

## 1. Overview

The conditional dispatch pipeline determines which of the 11 advanced automata
modules (M1--M11) should run for a given grammar. It operates at two levels:

1. **Compile-time gating** -- `#[cfg(feature = "...")]` removes code for
   disabled features entirely from the binary.
2. **Runtime gating** -- `GrammarDispatchPlan::requires()` inspects the
   grammar's aggregate `PredicateSignature` bitfield to skip modules that are
   structurally irrelevant.

Both gates must pass for a module to execute. This double-gating ensures zero
overhead for disabled features (no code in binary) and minimal overhead for
enabled-but-irrelevant features (early return before analysis begins).

### Full Pipeline Diagram

```text
                    LanguageSpec
                         │
                         ▼
              ┌─────────────────────┐
              │   Extract Bundles   │
              │  (ParserBundle,     │
              │   LexerBundle)      │
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  FIRST / FOLLOW     │
              │  WFST Construction  │
              │  Decision Tree      │
              │  GrammarProfile     │
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  evaluate_          │
              │  optimizations()    │◄─── cost_benefit.rs
              │  (PD01 = Diagnostic)│
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  DB03 gate check    │
              │  (ParallelAnalysis  │
              │   eligible?)        │
              └───────┬─────────┬───┘
                      │         │
             eligible │         │ not eligible
                      │         │
                      ▼         ▼
         ┌────────────────┐  ┌───────────────────┐
         │ run_math_      │  │ run_math_         │
         │ analyses_      │  │ analyses_         │
         │ parallel()     │  │ sequential()      │
         └───────┬────────┘  └────────┬──────────┘
                 │                    │
                 ▼                    ▼
       ┌─────────────────┐  ┌─────────────────┐
       │  Phase 7A:      │  │  Phase 7A:      │
       │  classify_      │  │  classify_      │
       │  grammar()      │  │  grammar()      │
       │  (before scope) │  │  (before macro) │
       └────────┬────────┘  └────────┬────────┘
                │                    │
                ▼                    ▼
       ┌─────────────────┐  ┌─────────────────┐
       │  Phase 7B:      │  │  Phase 7B:      │
       │  thread::scope  │  │  dispatch_gate! │
       │  {              │  │  macro in each  │
       │    per-module   │  │  closure        │
       │    s.spawn(||{  │  │  (sequential)   │
       │      #[cfg] +   │  │                 │
       │      requires() │  │                 │
       │    })           │  │                 │
       │  }              │  │                 │
       └────────┬────────┘  └────────┬────────┘
                │                    │
                └────────┬───────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  MathAnalysisResults│
              │  (per-module Option)│
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  Lint Layer         │
              │  (DispatchDiag-     │
              │   nostics, PD01-04) │
              └─────────────────────┘
```

---

## 2. Phase 7A: Dispatch Classification

Phase 7A runs `classify_grammar()` **before** the `thread::scope` block (in the
parallel path) or **before** the `MathAnalysisResults` struct expression (in the
sequential path). This ensures the `GrammarDispatchPlan` is available as a
shared borrow to all spawned threads without requiring `Arc` or cloning.

### `classify_grammar()` Algorithm

The function performs a single pass over `all_syntax` (the grammar's
`(label, category, Vec<SyntaxItemSpec>)` triples) and accumulates heuristic
signals into a `PredicateSignature` bitfield:

```text
Input: all_syntax: &[(String, String, Vec<SyntaxItemSpec>)]
       categories: &[CategoryInfo]

 1. Initialize aggregate = PredicateSignature::new()   // M1 | M10 always set
 2. Build category reference graph:
    - For each rule, collect NonTerminal/Binder/Collection references
    - Track rules_per_category, has_binders, has_branching (>= 3 NTs)
    - Collect terminal symbols for bracket detection
    - Build ChannelContext: bind param_name -> category
 3. Heuristic activation:
    a. Cross-category (>= 2 referenced categories in one rule)
       -> M8 (Multi-Tape); if cross-category differs -> M11 (Two-Way)
    b. Collection/Sep patterns -> M9 (Multiset)
    c. Recursive categories (self-referencing in category_refs) -> M2 (Buchi)
    d. Branching (>= 3 NT children) -> M3 (AWA)
    e. Paired brackets (call + return terminals) -> M4 (VPA)
    f. Recursive + branching -> M5 (Parity Tree)
    g. Binder items -> M6 (Register)
    h. Ambiguity (>= 3 rules in same category) -> M7 (Probabilistic)
 4. Build module_schedule sorted by estimated_cost (cheapest first)
 5. Return GrammarDispatchPlan { aggregate_signature, predicate_profiles,
                                  module_schedule, modules_skipped }
```

### `GrammarDispatchPlan` Structure

```rust
pub struct GrammarDispatchPlan {
    /// Union of all predicate signatures in the grammar.
    pub aggregate_signature: PredicateSignature,
    /// Profile for each predicate found in the grammar.
    pub predicate_profiles: Vec<PredicateProfile>,
    /// Modules to invoke, ordered by estimated cost (cheapest first).
    pub module_schedule: Vec<ModuleId>,
    /// Number of modules that would have run unconditionally but are now skipped.
    pub modules_skipped: u32,
}

impl GrammarDispatchPlan {
    /// Check if a module is needed by this grammar.
    pub fn requires(&self, module: ModuleId) -> bool {
        self.aggregate_signature.contains(module.bit())
    }

    /// Modules that are NOT needed (for diagnostic reporting).
    pub fn skipped_modules(&self) -> Vec<ModuleId> {
        ModuleId::ALL
            .iter()
            .copied()
            .filter(|m| !self.requires(*m))
            .collect()
    }
}
```

The `requires()` method is the single predicate that controls runtime dispatch.
It tests whether the module's bit is set in the aggregate signature using a
constant-time bitwise AND.

### `PredicateSignature` Bitfield Layout

```text
Bit  Module  Name             Variety
───  ──────  ───────────────  ──────────────────────────
 0   M1      Symbolic         REG (regular, Boolean closure)
 1   M2      Buchi            omega-REG (omega-regular)
 2   M3      AWA              ALT (alternating, universal branching)
 3   M4      VPA              VPL (visibly pushdown)
 4   M5      Parity Tree      mu-CLR (mu-calculus)
 5   M6      Register         DATA (data languages)
 6   M7      Probabilistic    PROB (stochastic)
 7   M8      Multi-Tape       k-TAPE (multi-stream)
 8   M9      Multiset         MSET (commutative)
 9   M10     Weighted MSO     MSO (full definability)
10   M11     Two-Way          2-WAY (bidirectional)

BASE = M1 | M10 = 0x0201    (always active)
ALL  = 0x07FF               (all 11 bits)
```

### Predicate-Level Feature Extraction

When predicated types are available (via `PredicateExpr` ASTs), the alternative
entry point `extract_features()` performs a single O(|AST|) post-order
traversal that maps AST node types to module bits:

| AST Node | Module Bits Set |
|----------|-----------------|
| `ForallFinite` | M3 (AWA) |
| `ExistsFinite` | _(depth only)_ |
| `ForallInfinite` | M2 (Buchi) + M3 (AWA) |
| `ExistsInfinite` | M2 (Buchi) |
| `Relation { name: eq/neq/fresh/... }` | M6 (Register) |
| `Relation { name: count/size/... }` | M9 (Multiset) |
| `Relation { name: letprop/fixpoint/mu/nu/... }` | M4 (VPA) + M5 (Parity Tree) |
| Cross-channel variable reference | M8 (Multi-Tape) + M11 (Two-Way) |
| `>= 2` distinct channels in one predicate | M7 (Probabilistic) + M8 (Multi-Tape) |

The signature is a **conservative approximation**: it may activate extra modules
but never misses a needed one (soundness over completeness).

---

## 3. Phase 7B: Conditional Spawning

Phase 7B executes the 11 advanced automata analyses. Each module is
**double-gated**:

1. **Compile-time**: `#[cfg(feature = "...")]` -- if the feature is not enabled,
   the entire `s.spawn(|| { ... })` block is omitted from the binary.
2. **Runtime**: `dispatch_plan.requires(ModuleId::Xxx)` -- if the module's bit
   is not set in the aggregate signature, the closure returns `None` immediately.

### Parallel Path Pattern

In `run_math_analyses_parallel()`, the dispatch plan is computed before
`thread::scope` so that spawned closures can borrow it:

```rust
fn run_math_analyses_parallel(
    bundle: &ParserBundle,
    wpds_analysis: Option<&crate::wpds::WpdsAnalysis>,
) -> MathAnalysisResults {
    // Phase 7A: Predicate dispatch classification (before thread scope so
    // spawned threads can borrow it)
    #[cfg(feature = "predicate-dispatch")]
    let dispatch_plan = crate::predicate_dispatch::classify_grammar(all_syntax, categories);

    std::thread::scope(|s| {
        // ... Phases 1-6 spawn here (TRS, VPA, WPDS, Petri, etc.) ...

        // Phase 7B: Advanced automata -- conditional spawning via dispatch plan
        #[cfg(feature = "symbolic-automata")]
        let h_symbolic = s.spawn(|| {
            #[cfg(feature = "predicate-dispatch")]
            if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::Symbolic) {
                return None;
            }
            Some(crate::symbolic::analyze_from_bundle(all_syntax, categories))
        });

        // ... same pattern for all 11 modules ...

        // Collect results
        MathAnalysisResults {
            // ...
            #[cfg(feature = "symbolic-automata")]
            symbolic_result: h_symbolic.join().expect("DB03: symbolic analysis thread panicked"),
            // ...
        }
    })
}
```

Each module follows the identical pattern:

```rust
#[cfg(feature = "<feature-gate>")]               // compile-time gate
let h_xxx = s.spawn(|| {
    #[cfg(feature = "predicate-dispatch")]        // dispatch gate exists only
    if !dispatch_plan.requires(ModuleId::Xxx) {   //   when predicate-dispatch
        return None;                              //   feature is enabled
    }
    Some(module::analyze_from_bundle(all_syntax, categories))
});
```

When `predicate-dispatch` is not enabled, the inner `#[cfg]` block compiles
away, and all modules run unconditionally (gated only by their own feature flag).

---

## 4. Dispatch Gate Table

| Module | Feature Gate | Pipeline Phase | Dispatch Gate | Status | Heuristic Trigger |
|--------|-------------|----------------|---------------|--------|-------------------|
| M1 | `symbolic-automata` | 7B | `requires()` | BASE | Always active |
| M2 | `omega` | 7B | `requires()` | Conditional | Recursive categories |
| M3 | `alternating` | 7B | `requires()` | Conditional | >= 3 NT children in a rule |
| M4 | `vpa` | 7B | `requires()` | Conditional | Paired call/return brackets |
| M5 | `parity-tree-automata` | 7B | `requires()` | Conditional | Recursive + branching |
| M6 | `register-automata` | 7B | `requires()` | Conditional | Binder items present |
| M7 | `probabilistic` | 7B | `requires()` | Conditional | >= 3 rules in same category |
| M8 | `multi-tape` | 7B | `requires()` | Conditional | >= 2 referenced categories |
| M9 | `multiset-automata` | 7B | `requires()` | Conditional | Collection/Sep patterns |
| M10 | `weighted-mso` | 7B | `requires()` | BASE | Always active |
| M11 | `two-way-transducer` | 7B | `requires()` | Conditional | Cross-category reference |

**Status definitions:**

- **BASE**: Bit is always set in `PredicateSignature::new()` (M1 and M10 form
  the algebraic foundation -- M1 provides the predicate algebra, M10 provides
  the MSO specification language). These modules can still be skipped at
  compile time if their feature flag is disabled.

- **Conditional**: Bit is set only when the corresponding heuristic fires during
  `classify_grammar()` or `extract_features()`. If the grammar lacks the
  structural patterns that trigger the heuristic, the module is skipped at
  runtime.

### Module Cost Ordering

The `module_schedule` in `GrammarDispatchPlan` is sorted by `estimated_cost()`:

| Cost | Modules |
|------|---------|
| 1 | M1 (Symbolic), M10 (Weighted MSO) |
| 2 | M6 (Register), M9 (Multiset) |
| 3 | M2 (Buchi), M3 (AWA) |
| 4 | M4 (VPA), M5 (Parity Tree) |
| 5 | M7 (Probabilistic), M8 (Multi-Tape) |
| 6 | M11 (Two-Way) |

---

## 5. Sequential Fallback

When the DB03 (`ParallelAnalysis`) optimization gate is off, or the grammar is
not eligible for parallel analysis, `run_math_analyses_sequential()` is called
instead. This function respects the same dispatch gates via a local
`dispatch_gate!` macro.

### `dispatch_gate!` Macro

```rust
fn run_math_analyses_sequential(
    bundle: &ParserBundle,
    wpds_analysis: Option<&crate::wpds::WpdsAnalysis>,
    eligible: bool,
) -> MathAnalysisResults {
    // Build dispatch plan for sequential path so dispatch gates are respected.
    #[cfg(feature = "predicate-dispatch")]
    let dispatch_plan = crate::predicate_dispatch::classify_grammar(
        &bundle.all_syntax, &bundle.categories,
    );

    /// Helper macro: returns `None` when dispatch says module is not needed.
    /// The inner `#[cfg]` gate ensures this compiles when `predicate-dispatch` is off.
    #[allow(unused_macros)]
    macro_rules! dispatch_gate {
        ($module:ident) => {
            {
                #[cfg(feature = "predicate-dispatch")]
                if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::$module) {
                    return None;
                }
            }
        };
    }

    MathAnalysisResults {
        // ...
    }
}
```

### Sequential Closure Pattern

Each dispatch-gated module in the sequential path is wrapped in an
immediately-invoked closure (`(|| { ... })()`) so that the `return None` inside
`dispatch_gate!` exits the closure rather than the entire function:

```rust
#[cfg(feature = "symbolic-automata")]
symbolic_result: if eligible {
    (|| {
        dispatch_gate!(Symbolic);
        Some(crate::symbolic::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
    })()
} else { None },
```

This pattern is repeated for each of the 11 advanced automata modules:

```rust
#[cfg(feature = "omega")]
buchi_result: if eligible {
    (|| {
        dispatch_gate!(Buchi);
        Some(crate::buchi::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
    })()
} else { None },

#[cfg(feature = "weighted-mso")]
mso_result: if eligible {
    (|| {
        dispatch_gate!(Mso);
        Some(crate::weighted_mso::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
    })()
} else { None },

// ... and so on for Probabilistic, Register, ParityTree, MultiTape,
//     Multiset, TwoWay, Awa, Vpa
```

Modules **without** dispatch gating (e.g., TRS confluence, WTA, Petri,
Nominal, LTL, Provenance, CRA, Morphism, KAT) run unconditionally in the
sequential path, guarded only by their feature flag and the `eligible` flag.

---

## 6. Code Patterns

### Pattern A: Parallel Spawn with Double Gate

Used in `run_math_analyses_parallel()` for each of the 11 advanced modules:

```rust
// Outer gate: compile-time feature flag (code absent from binary if disabled)
#[cfg(feature = "register-automata")]
let h_register = s.spawn(|| {
    // Inner gate: runtime dispatch check (early return if grammar doesn't need M6)
    #[cfg(feature = "predicate-dispatch")]
    if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::Register) {
        return None;
    }
    Some(crate::register_automata::analyze_from_bundle(all_syntax, categories))
});
```

The `dispatch_plan` variable lives outside `thread::scope`, so all spawned
closures borrow it by shared reference. When `predicate-dispatch` is not
enabled, the inner `#[cfg]` block is erased and the closure unconditionally
returns `Some(...)`.

### Pattern B: Sequential Closure with `dispatch_gate!`

Used in `run_math_analyses_sequential()`:

```rust
#[cfg(feature = "multiset-automata")]
multiset_result: if eligible {
    (|| {
        dispatch_gate!(Multiset);   // expands to requires() check + return None
        Some(crate::multiset_automata::analyze_from_bundle(
            &bundle.all_syntax, &bundle.categories
        ))
    })()
} else { None },
```

The immediately-invoked closure `(|| { ... })()` is necessary because
`dispatch_gate!` expands to a `return None` statement, which must return from
the closure, not from `run_math_analyses_sequential()` itself.

### Pattern C: Non-Gated Module (Phases 1--6)

Modules in Phases 1--6 (TRS, WTA, WPDS, Petri, etc.) are not subject to
predicate dispatch. They run unconditionally when their feature flag is enabled:

```rust
#[cfg(feature = "trs-analysis")]
let h_confluence = s.spawn(|| {
    crate::confluence::analyze_from_bundle(all_syntax, 100)
});
```

The VPA module is an exception: it participates in Phase 2 (automata analysis)
but is also part of the M4 dispatch gate:

```rust
#[cfg(feature = "vpa")]
let h_vpa = s.spawn(|| {
    #[cfg(feature = "predicate-dispatch")]
    if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::Vpa) {
        return None;
    }
    crate::vpa::analyze_from_bundle(categories, all_syntax)
});
```

---

## 7. Interaction with Cost-Benefit

### `GrammarProfile` and Analysis Gating

The cost-benefit framework (`cost_benefit.rs`) builds a `GrammarProfile` from
pipeline data (WFST states, FIRST sets, decision tree metrics) and evaluates
all optimizations via `evaluate_optimizations()`. The predicate dispatch
optimization is registered as:

```rust
#[cfg(feature = "predicate-dispatch")]
PredicateDispatch,
```

Its `OptimizationStatus` is `Diagnostic` -- meaning it produces diagnostic
output (PD01--PD04 lint codes) but does not directly modify code generation.
The cost-benefit framework does not gate predicate dispatch itself; instead,
predicate dispatch gates the _other_ advanced automata modules.

### Information Flow

```text
GrammarProfile
     │
     ├──► evaluate_optimizations()
     │         │
     │         ├──► DB03:ParallelAnalysis  ──► chooses parallel vs sequential path
     │         │
     │         ├──► SYM01, O01, N06, V05, PT01, RA01, PR01, MT01, MS01,
     │         │    MSO01, TW01  ──► individual module recommendations
     │         │
     │         └──► PD01:PredicateDispatch ──► diagnostic only (OptimizationStatus::Diagnostic)
     │
     └──► classify_grammar()
               │
               └──► GrammarDispatchPlan
                         │
                         ├──► requires(M_i)  ──► gates Phase 7B module spawning
                         │
                         └──► DispatchDiagnostics::from_plan()
                                   │
                                   └──► PD01-PD04 lint diagnostics
```

The `GrammarProfile` drives cost-benefit decisions _about_ the advanced
modules (e.g., "is `RA01:RegisterAnalysis` worth running given rule_count?"),
while the `GrammarDispatchPlan` makes a structural determination ("does this
grammar contain register-relevant patterns at all?"). Both must agree for a
module to execute: the dispatch plan must `require()` it, and the cost-benefit
framework should not have marked the analysis as inapplicable.

In practice, the dispatch gate is the stronger filter: if a grammar has no
binder items, `requires(ModuleId::Register)` returns `false` regardless of
what the cost-benefit framework recommends.

### `Optimization::PredicateDispatch` (PD01)

The PD01 optimization entry exists in the `Optimization` enum but is not
evaluated with a speedup/cost score in `evaluate_optimizations()`. Its status
is purely `Diagnostic`:

```rust
#[cfg(feature = "predicate-dispatch")]
Self::PredicateDispatch => OptimizationStatus::Diagnostic,
```

This means PD01 appears in diagnostic output (reporting how many modules were
skipped, which heuristics fired, etc.) but does not compete in the
lexicographic `ProductWeight<speedup, compile_cost>` ranking.

---

## 8. Self-Referential SFA Verification

The dispatch layer is **self-referential**: it uses M1's own `BooleanAlgebra`
trait to verify its own completeness and consistency.

### `DispatchAlgebra`

`DispatchAlgebra` implements `BooleanAlgebra` with:
- **Domain**: `PredicateSignature` (u16 bitfields)
- **Predicates**: `SignaturePred` (bit-membership tests + Boolean connectives)

```text
SignaturePred ::= True
               | False
               | HasBit(u16)
               | And(SignaturePred, SignaturePred)
               | Or(SignaturePred, SignaturePred)
               | Not(SignaturePred)
```

Satisfiability and witness generation use brute-force enumeration over all
2^11 = 2048 possible signatures (fast enough for 11 bits).

### Dispatch SFA

`build_dispatch_sfa()` constructs a 13-state symbolic finite automaton:

```text
         ┌── HasBit(0) ──► q_M1  (Symbolic)       [accept]
         │
         ├── HasBit(1) ──► q_M2  (Buchi)           [accept]
         │
         ├── HasBit(2) ──► q_M3  (AWA)             [accept]
         │
         ├── HasBit(3) ──► q_M4  (VPA)             [accept]
         │
q_0 ─────├── HasBit(4) ──► q_M5  (Parity Tree)    [accept]
         │
         ├── HasBit(5) ──► q_M6  (Register)        [accept]
         │
         ├── HasBit(6) ──► q_M7  (Probabilistic)   [accept]
         │
         ├── HasBit(7) ──► q_M8  (Multi-Tape)      [accept]
         │
         ├── HasBit(8) ──► q_M9  (Multiset)        [accept]
         │
         ├── HasBit(9) ──► q_M10 (Weighted MSO)    [accept]
         │
         ├── HasBit(10)──► q_M11 (Two-Way)         [accept]
         │
         └── not(any) ──► q_bot                     [reject]
```

**Theorem 3.1 (Completeness):** For every sigma in D with sigma != 0, the
dispatch SFA A_D accepts sigma. Verified by `verify_completeness()` which
checks all 2047 non-zero signatures.

**Theorem 3.2 (Zero Rejection):** The zero signature (no modules active) is
rejected. Verified by `verify_zero_rejected()`.

These properties guarantee that `classify_grammar()` always produces a
dispatchable plan: every non-empty grammar activates at least M1 + M10, and
no grammar produces a degenerate zero-module plan.

---

## 9. Diagnostic Integration

### `DispatchDiagnostics`

After Phase 7B completes, `DispatchDiagnostics::from_plan()` extracts lint-
relevant data from the dispatch plan:

```rust
pub struct DispatchDiagnostics {
    pub profiles: Vec<PredicateProfile>,
    pub degenerate_predicates: Vec<usize>,       // PD01: only M1+M10 active
    pub full_activation_predicates: Vec<usize>,  // PD02: all 11 modules active
    pub total_modules_skipped: u32,              // PD03: skipped count
    pub cross_channel_without_two_way: Vec<usize>, // PD04: feature gap
}
```

| Lint Code | Severity | Condition |
|-----------|----------|-----------|
| PD01 | Note | Predicate activates only base modules (may be over-simplified) |
| PD02 | Warning | Predicate activates all 11 modules (likely too broad) |
| PD03 | Info | Reports total modules skipped (dispatch efficiency metric) |
| PD04 | Warning | Cross-channel constraint found but `two-way-transducer` feature disabled |

### `PredicateCompiler` Trait

For future per-predicate compilation, each module can implement:

```rust
pub trait PredicateCompiler {
    type Output;
    fn compile_predicate(
        &self,
        pred: &PredicateExpr,
        profile: &PredicateProfile,
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
        categories: &[CategoryInfo],
    ) -> Self::Output;
}
```

Currently, `compile_predicate_pipeline()` delegates to
`DispatchDiagnostics::from_plan()`. Per-predicate compilation will be wired in
when modules implement `PredicateCompiler`.

---

## 10. Feature Flag Dependencies

The conditional dispatch infrastructure uses the following feature flags:

| Feature Flag | Purpose | Default |
|-------------|---------|---------|
| `predicate-dispatch` | Enables `classify_grammar()` and `dispatch_gate!` macro | Off |
| `symbolic-automata` | M1: Symbolic guard analysis | Off |
| `omega` | M2: Weighted Buchi analysis | Off |
| `alternating` | M3: AWA polynomial transitions | Off |
| `vpa` | M4: Weighted VPA inclusion | Off |
| `parity-tree-automata` | M5: Mu-calculus emptiness checking | Off |
| `register-automata` | M6: Data language analysis | Off |
| `probabilistic` | M7: Stochastic disambiguation | Off |
| `multi-tape` | M8: Multi-channel tape analysis | Off |
| `multiset-automata` | M9: Commutative cardinality analysis | Off |
| `weighted-mso` | M10: MSO formula classification | Off |
| `two-way-transducer` | M11: Bidirectional transduction | Off |

When `predicate-dispatch` is **disabled**, all feature-enabled modules run
unconditionally (the inner `#[cfg(feature = "predicate-dispatch")]` blocks
compile away). This is the conservative default: no module is accidentally
skipped.

When `predicate-dispatch` is **enabled**, `classify_grammar()` performs the
structural analysis described in Section 2 and modules are skipped at runtime
when their heuristic does not fire. The `modules_skipped` count in
`GrammarDispatchPlan` records how many modules were suppressed.

---

## 11. Invariants

1. **M1 + M10 always active**: `PredicateSignature::new()` sets `BASE =
   M1_SYMBOLIC | M10_MSO`. No heuristic can unset these bits.

2. **Conservative approximation**: `classify_grammar()` may set extra bits
   (false positives) but never misses a needed module (no false negatives).
   This is a soundness guarantee: running an unnecessary module wastes time
   but produces no incorrect results; skipping a needed module could miss
   diagnostics.

3. **Determinism**: `classify_grammar()` is deterministic -- the same grammar
   always produces the same `GrammarDispatchPlan`. Verified by property test
   `prop_classify_grammar_deterministic`.

4. **Monotonicity**: Adding rules to a grammar can only set additional bits,
   never clear existing ones. Verified by property test
   `prop_classify_grammar_monotonic`.

5. **Complementarity**: `requires(module)` and `skipped_modules()` are
   complementary: a module appears in exactly one of the two sets. Verified by
   property test `prop_requires_skipped_complementary`.

6. **Thread safety**: `GrammarDispatchPlan` is `Send + Sync` (all fields are
   owned values). It is computed once and borrowed immutably by all spawned
   threads.
