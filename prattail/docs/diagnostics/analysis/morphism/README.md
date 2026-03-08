# Morphism Analysis Diagnostics (M-Category)

**Date:** 2026-03-08
**Source:** `prattail/src/lint.rs` (emission), `prattail/src/morphism.rs` (theory morphisms), `prattail/src/repair.rs` (repair suggestions)

## 1 Overview

The M-category lints report results from theory morphism analysis between formal theories derived from PraTTaIL grammars. Theory morphisms are structure-preserving maps that enable verified cross-grammar translation, desugaring verification, and grammar embedding proofs.

The morphism analysis has two phases, each producing a distinct lint:

```
  Source Theory T_1                    Target Theory T_2
  (sorts, operations, axioms)          (sorts, operations, axioms)
          |                                    |
          └──────────────┬─────────────────────┘
                         |
                         v
           ┌─────────────────────────────┐
           │  Phase 1: Structural Check  │
           │  For each op f in T_1:      │
           │    Does phi(f) exist in T_2? │
           └─────────────────────────────┘
                    |           |
                    v           v
               No gaps      Gaps found
                    |           |
                    v           v
              (continue)      M01
                    |        (Warning)
                    v
           ┌─────────────────────────────┐
           │  Phase 2: Semantic Check    │
           │  For each axiom eq in T_1:  │
           │    Does phi(eq) hold in T_2? │
           └─────────────────────────────┘
                    |           |
                    v           v
              All preserved  Failures
                    |           |
                    v           v
              (silent)        M02
                            (Warning)
```

Both M-category lints require the `morphisms` feature gate to be enabled at compile time.

## 2 Lint Index

| ID | Severity | Name | Description |
|----|----------|------|-------------|
| [M01](M01-morphism-gap.md) | Warning | morphism-gap | Missing constructor mapping in theory morphism |
| [M02](M02-morphism-preservation-failure.md) | Warning | morphism-preservation-failure | Axiom not preserved under morphism |

## 3 Theoretical Background

### 3.1 Theory Morphisms

A theory morphism `phi: T_1 -> T_2` consists of:

1. **Sort mapping:** `phi_S: Sorts(T_1) -> Sorts(T_2)` -- maps each sort in the source to a sort in the target.
2. **Operation mapping:** `phi_O: Ops(T_1) -> Terms(T_2)` -- maps each operation symbol to a term in the target theory (not necessarily a single operation).
3. **Axiom preservation:** For every axiom `forall x. s = t` in `T_1`, the translated equation `forall x. phi(s) = phi(t)` is a theorem of `T_2`.

The morphism is:
- **Total** if `phi_O` is defined for every operation in `T_1` (no M01 gaps).
- **Sound** if every axiom is preserved (no M02 failures).
- **Complete** if it is both total and sound.

### 3.2 Commutation Diagram

The fundamental property of a theory morphism is that the following diagram commutes for every n-ary operation `f`:

```
  phi_S(A_1) x ... x phi_S(A_n) ──── phi_O(f) ────> phi_S(B)
         ^                                              ^
         |                                              |
   phi_S x...x phi_S                               phi_S
         |                                              |
     A_1 x ... x A_n ──────────── f ──────────────> B
```

### 3.3 PraTTaIL Grammar Interpretation

| Theory Component | PraTTaIL Analog |
|-----------------|-----------------|
| Sort | Grammar category |
| Operation | Grammar rule (constructor) |
| Axiom | Associativity, commutativity, cancellation equations |
| Morphism | Cross-grammar translation map |

## 4 Repair Integration

When the `repair` module is active, M01 and M02 findings are enriched with repair suggestions. The repair engine proposes concrete grammar modifications to complete incomplete morphisms:

- **For M01 gaps:** Suggests adding a rule to the target category with the appropriate sort signature.
- **For M02 failures:** Suggests adding axioms or quotients to the target theory to establish the required equation.

## 5 Related Diagnostic Categories

- **L (Temporal):** LTL properties can verify that morphism-translated parse traces preserve temporal invariants.
- **K (KAT):** KAT equivalence can verify that morphism-translated parse programs are behaviorally equivalent.
- **E (Extension):** Provenance polynomials can be translated through morphisms to track derivation lineage across grammar versions.
- **P (Performance):** P06 reports the total analysis phase time, which includes morphism analysis.
