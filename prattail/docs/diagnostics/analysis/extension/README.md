# Extension Analysis Diagnostics (E-Category)

**Date:** 2026-03-08
**Source:** `prattail/src/lint.rs` (emission), `prattail/src/provenance.rs` (provenance semiring), `prattail/src/cra.rs` (cost register automata)

## 1 Overview

The E-category lints report results from extended analysis modules that go beyond the core grammar structure to provide quantitative and lineage insights. These analyses answer deeper questions about the grammar's derivation structure:

- **E01 (provenance):** HOW is each parse fact derived? Which base rules and tokens combine to produce it?
- **E02 (CRA):** HOW MUCH does each derivation cost? Do any cost registers exhibit anomalous growth?

```
  Grammar Rules + Token Patterns
               |
       ┌───────┴───────┐
       |               |
       v               v
  ┌──────────┐   ┌──────────────┐
  │Provenance│   │  CRA Cost    │
  │  N[X]    │   │  Registers   │
  │ semiring │   │  (streaming) │
  └──────────┘   └──────────────┘
       |               |
       v               v
  Polynomials      Register
  computed         anomalies
       |               |
       v               v
     E01             E02
   (Note)          (Warning)
```

Both E-category lints are gated behind their respective feature flags (`provenance` for E01, `cra` for E02). Without the feature enabled, the analysis module is not compiled and no diagnostics are produced.

## 2 Lint Index

| ID | Severity | Name | Feature | Description |
|----|----------|------|---------|-------------|
| [E01](E01-provenance-trace.md) | Note | provenance-trace | `provenance` | How-provenance: N polynomial(s) computed |
| [E02](E02-cra-cost-anomaly.md) | Warning | cra-cost-anomaly | `cra` | CRA register value exceeds threshold |

## 3 Theoretical Background

### 3.1 Provenance Semirings

The provenance framework is based on Green, Karvounarakis & Tannen (2007). The key insight is that different "questions" about derivations correspond to different semiring homomorphisms from the universal provenance semiring `N[X]`:

```
                     N[X]
                      |
        ┌─────────────┼──────────────┐──────────────┐
        |             |              |              |
        v             v              v              v
    Boolean       Powerset      Tropical       Viterbi
  (which-prov)  (why-prov)   (cost-prov)   (confidence)
        |             |              |              |
        v             v              v              v
   "derivable?"  "which        "cheapest      "most
                  combos?"     derivation?"   confident?"
```

### 3.2 Cost Register Automata

CRAs (Alur, D'Antoni, Deshmukh, Raghothaman & Yuan, 2013) extend finite automata with semiring-valued registers that are updated at each input step. Key properties:

- **Expressiveness:** CRAs capture exactly the class of regular cost functions.
- **Decidability:** Equivalence of CRAs is decidable in polynomial time.
- **Streaming:** CRAs process input in a single left-to-right pass, making them suitable for online cost monitoring.

The register update language is built from:

```
Expr ::= r_i             (register value)
       | cost            (input cost)
       | 0 | 1           (semiring constants)
       | Expr + Expr     (semiring addition)
       | Expr x Expr     (semiring multiplication)
```

## 4 PraTTaIL Integration

Extension analyses run during the mathematical analysis phase of the pipeline, after core grammar structure analysis (WFST, WPDS, decision tree) but before lint emission. Their results are stored in the `LintContext` and consumed by the lint functions `lint_e01_provenance_trace` and `lint_e02_cra_cost_anomaly`.

## 5 Related Diagnostic Categories

- **L (Temporal):** LTL model checking uses the same WPDS infrastructure. Temporal properties constrain trace structure; extension analyses quantify trace cost and provenance.
- **P (Performance):** P06 reports the total analysis phase time that includes extension analyses.
- **M (Morphism):** Theory morphisms may transform provenance polynomials between grammar versions.
