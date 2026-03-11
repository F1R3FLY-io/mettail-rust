# Predicate Dispatch Automaton — Architecture

| Field | Value |
|-------|-------|
| **Date** | 2026-03-10 |
| **Status** | Implemented |
| **Feature Gate** | `predicate-dispatch` |
| **Dependencies** | `symbolic-automata`, `weighted-mso` |
| **Module** | `prattail/src/predicate_dispatch.rs` |

## Overview

The Predicate Dispatch Automaton decomposes predicate formulas into algebraic
"morphemes" (structural features), classifies them into automata varieties via
Eilenberg's variety theorem, and directs only the applicable advanced automata
modules (M1–M11) to run in Phase 7 of the pipeline. This replaces the previous
unconditional spawning of all 11 modules.

## Problem Statement

PraTTaIL has 11 advanced automata modules that were spawned unconditionally in
Phase 7. Every enabled module ran on every grammar, doing trivial stub work even
when the grammar's predicates had no structural features relevant to that module.

```
BEFORE:                                AFTER:
┌──────────┐                           ┌──────────┐
│ Grammar  │──→ ALL 11 modules         │ Grammar  │──→ extract_features()
└──────────┘    (unconditional)        └──────────┘         │
                                                            ▼
                                                  PredicateSignature(u16)
                                                       │
                                                  ┌────┴────┐
                                                  │ Dispatch │──→ {M1,M6,M8,M11}
                                                  │   SFA    │    (targeted)
                                                  └─────────┘
```

## Architecture Diagram

```
PredicateExpr / WeightedMsoFormula
        │
        ▼  extract_features() / extract_features_mso()   ← O(|AST|) walk
PredicateProfile {
    signature: PredicateSignature(u16),   ← bitfield: which varieties
    quantifier_depth, channel_count, ...  ← quantitative metrics
    decidability_tier: T1..T4             ← from classify_decidability()
}
        │
        ▼  classify_grammar()   ← union across all rules
GrammarDispatchPlan {
    aggregate_signature,        ← which modules to spawn
    predicate_profiles,         ← per-predicate detail
    module_schedule,            ← ordered by estimated cost
}
        │
        ├──→  Phase 7B (pipeline.rs)
        │     Only spawn modules whose bits are set
        │
        ├──→  lint.rs (PD01–PD04)
        │     Dispatch-related diagnostics
        │
        └──→  cost_benefit.rs (Optimization::PredicateDispatch)
              Gate for enabling/disabling dispatch
```

## Core Types

### PredicateSignature(u16) — Bitfield

```
Bit 0  │ M1  │ Symbolic        │ Always on (base)
Bit 1  │ M2  │ Büchi           │ ω-regular
Bit 2  │ M3  │ AWA             │ Alternating
Bit 3  │ M4  │ VPA             │ Visibly pushdown
Bit 4  │ M5  │ Parity Tree     │ μ-calculus
Bit 5  │ M6  │ Register        │ Data languages
Bit 6  │ M7  │ Probabilistic   │ Stochastic
Bit 7  │ M8  │ Multi-Tape      │ k-tape
Bit 8  │ M9  │ Multiset        │ Commutative
Bit 9  │ M10 │ Weighted MSO    │ Always on (base)
Bit 10 │ M11 │ Two-Way         │ Bidirectional
```

`PredicateSignature::BASE = M1_SYMBOLIC | M10_MSO` — always active.

### PredicateProfile

Per-predicate quantitative analysis:
- `signature: PredicateSignature` — which modules are relevant
- `quantifier_depth: u32` — nesting depth of quantifiers
- `channel_count: u32` — distinct channels referenced
- `register_count: u32` — data variables in equality/freshness relations
- `has_backward_constraint: bool` — cross-channel backward reference
- `has_cardinality: bool` — count/≥/≤ atoms present
- `has_recursive_predicate: bool` — letprop / fixpoint definition
- `decidability_tier: DecidabilityTier` — from `classify_decidability()`

### GrammarDispatchPlan

Per-grammar orchestration:
- `aggregate_signature: PredicateSignature` — union of all predicate signatures
- `predicate_profiles: Vec<PredicateProfile>` — per-predicate detail
- `module_schedule: Vec<ModuleId>` — sorted by estimated cost (cheapest first)

### ModuleId

Enumeration of all 11 modules with:
- `bit() -> u16` — corresponding signature bit
- `name() -> &str` — human-readable name
- `feature_gate() -> &str` — Cargo feature name
- `estimated_cost() -> u32` — relative cost for scheduling

## Feature Extraction Algorithm

Single post-order traversal of the AST, O(|φ|) time:

```
extract_features(φ, Γ):
    sig ← PredicateSignature::BASE         ▷ M1 | M10 always
    match φ:
        True | False | Atom(_)         → sig
        Not(ψ)                         → sig ∪ extract(ψ)
        And(a, b) | Or(a, b)           → sig ∪ extract(a) ∪ extract(b)
        ForallFinite { body, .. }      → sig ∪ {M3} ∪ extract(body)
        ExistsFinite { body, .. }      → sig ∪ extract(body)
        ForallInfinite { body, .. }    → sig ∪ {M2, M3} ∪ extract(body)
        ExistsInfinite { body, .. }    → sig ∪ {M2} ∪ extract(body)
        Relation { name, args }        →
            if is_equality(name)       → sig ∪ {M6}
            if is_cardinality(name)    → sig ∪ {M9}
            if is_fixpoint(name)       → sig ∪ {M4, M5}
            if cross_channel(args, Γ)  → sig ∪ {M8, M11}
            else                       → sig ∪ {M6}
        Bounded { body, .. }           → sig ∪ extract(body)
    if channel_count ≥ 2               → sig ∪ {M7, M8}
```

### Worked Example: Rholang Cross-Channel Constraint

```rholang
for (@x <- ch1, @y : related(x) <- ch2) { P }
```

1. **Parse**: `related(x)` → `Relation { name: "related", args: ["x"] }`
2. **Channel context**: `x` bound on `ch1`, guard on `ch2` references `x` → cross-channel
3. **Feature extraction**:
   - `Relation` → M6_REGISTER
   - Cross-channel reference → M8_MULTI_TAPE | M11_TWO_WAY
   - 2 channels → M7_PROBABILISTIC
   - Result: `signature = M1 | M6 | M7 | M8 | M10 | M11`
4. **Dispatch**: Phase 7 spawns M1, M6, M7, M8, M10, M11. Skips M2–M5, M9.

## Dispatch SFA — Verification Layer

The dispatch is verified by a Symbolic Finite Automaton (SFA) that reuses M1's
`BooleanAlgebra` trait. The `DispatchAlgebra` implements `BooleanAlgebra` where:

- **Domain** = `PredicateSignature` (u16 bitfields)
- **Predicates** = `SignaturePred` (bit-membership tests)
- `HasBit(i)` evaluates to true iff bit `i` is set in the signature

The SFA has 13 states (q₀ + 11 module states + q_⊥), with transitions from q₀
to q_Mᵢ guarded by `HasBit(i)`. Verification functions:

- `verify_completeness()` — every non-zero signature reaches an accepting state
- `verify_zero_rejected()` — the zero signature is rejected
- `dispatch_overlap_pairs()` — identifies always-co-activated module pairs

## Pipeline Integration

### Phase 7A: Dispatch Classification

```rust
#[cfg(feature = "predicate-dispatch")]
let dispatch_plan = predicate_dispatch::classify_grammar(all_syntax, categories);
```

Computed **before** `std::thread::scope` so scoped threads can borrow it.

### Phase 7B: Conditional Spawning

```rust
#[cfg(feature = "symbolic-automata")]
let h_symbolic = s.spawn(|| {
    #[cfg(feature = "predicate-dispatch")]
    if !dispatch_plan.requires(ModuleId::Symbolic) {
        return None;
    }
    Some(symbolic::analyze_from_bundle(all_syntax, categories))
});
```

When `predicate-dispatch` is disabled, the existing unconditional code runs unchanged.

## Cost-Benefit Integration

`Optimization::PredicateDispatch` in `cost_benefit.rs` gates the dispatch
mechanism. Status: `Diagnostic` (always reports, no user opt-out needed).

Speedup model: `modules_skipped × per_module_cost`. For a typical grammar with
2–3 active varieties, dispatch skips 6–8 modules.

## Lint Diagnostics

| Code | Severity | Trigger |
|------|----------|---------|
| PD01 | Warning | Predicate activates no specialized module (degenerate guard) |
| PD02 | Note | Predicate activates all 11 modules (no dispatch benefit) |
| PD03 | Info | Dispatch skipped N module invocations (savings report) |
| PD04 | Warning | Cross-channel predicate but `two-way-transducer` feature not enabled |

## Module Selection Table

| Module | Variety | Predicate Morpheme | Grammar Heuristic | Feature Gate |
|--------|---------|-------------------|-------------------|--------------|
| M1 Symbolic | REG | Always on | Always on | `symbolic-automata` |
| M2 Büchi | ω-REG | `ForallInfinite`/`ExistsInfinite` | Recursive category | `omega` |
| M3 AWA | ALT | `ForallFinite`/`ForallInfinite` | ≥3 non-terminals | `alternating` |
| M4 VPA | VPL | `letprop`/`fixpoint`/`mu`/`nu` | Paired brackets | `vpa` |
| M5 Parity Tree | μCLR | Recursive fixpoint | Recursive + branching | `parity-tree-automata` |
| M6 Register | DATA | `eq`/`neq`/`fresh` | Binder items | `register-automata` |
| M7 Probabilistic | PROB | Multi-guard conjunction | ≥3 same-cat rules | `probabilistic` |
| M8 Multi-Tape | k-TAPE | ≥2 channels in join | ≥2 cross-cat refs | `multi-tape` |
| M9 Multiset | MSET | `count()`/`>=`/`<=` | Collection/Sep items | `multiset-automata` |
| M10 W. MSO | MSO | Always on | Always on | `weighted-mso` |
| M11 Two-Way | 2-WAY | Cross-channel variable ref | Cross-cat differs | `two-way-transducer` |

## Grammar-Structure Heuristics

When predicates are not yet available (before the predicated-types codegen pipeline
provides parsed predicates), `classify_grammar()` uses grammar-structure heuristics
to conservatively activate modules. These heuristics detect structural patterns in
grammar rules that are *syntactic fingerprints* of the computational classes that
will eventually appear in predicates.

**Design principle**: Grammar heuristics may over-activate modules (false positives)
but never under-activate (no false negatives). This preserves the soundness
guarantee from Lemma 1.1 in variety-classification.md.

### Heuristic Summary

| Heuristic | Pattern | Module(s) | Rationale |
|-----------|---------|-----------|-----------|
| Direct recursion | Category C references itself | M2 | Unbounded derivations → ω-regular |
| High branching | Rule has ≥3 non-terminal children | M3 | Universal branching → alternating |
| Paired delimiters | `()`/`{}`/`[]`/`begin`..`end` present | M4 | Visible pushdown structure |
| Recursive + branching | Both direct recursion and high branching | M5 | Ranked tree fixpoints |
| Name binding | `Binder` items in rules | M6 | Scope/freshness tracking |
| Ambiguity | ≥3 rules in same category | M7 | Statistical disambiguation |
| Cross-category | ≥2 distinct categories in one rule | M8, M11 | Multi-tape / two-way |
| Collection | `Collection`/`Sep` items | M9 | Commutative structure |

For full theoretical justification, see:
- [Grammar-Structure Heuristics Theory](../theory/dispatch/grammar-structure-heuristics.md)
- [Conservative Approximation Soundness](../theory/dispatch/conservative-approximation.md)

## PredicateCompiler Trait

Each module implements `PredicateCompiler` for per-predicate compilation:

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

Current implementations delegate to `analyze_from_bundle()`. Future work will
use `profile` to specialize the analysis per-predicate.

## References

- Eilenberg, S. (1976). *Automata, Languages, and Machines*, Vol. B. Academic Press.
- Pin, J.-É. (1986). *Varieties of Formal Languages*. Plenum.
- Straubing, H. (1994). *Finite Automata, Formal Logic, and Circuit Complexity*. Birkhäuser.
- D'Antoni, L. & Veanes, M. (2017). The power of symbolic automata and transducers. *CAV 2017*.
- Droste, M. & Gastin, P. (2007). Weighted automata and weighted logics. *TCS* 380(1–2).
