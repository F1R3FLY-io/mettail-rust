# P06: analysis-pipeline-cost

**Severity:** Note
**Category:** performance
**Feature Gate:** always-on

## Description

Reports the wall-clock time spent in the mathematical analysis phase of the PraTTaIL compile-time pipeline. This phase runs all feature-gated analysis modules (LTL model checking, provenance tracking, CRA cost analysis, morphism verification, KAT checking, and others) and produces results consumed by the lint system. P06 helps grammar authors and pipeline developers understand the time cost of enabling various analysis features.

P06 is always-on: it does not require any feature gate. However, it only fires when the analysis phase takes at least 100 microseconds, filtering out trivially fast executions where no meaningful analysis work was performed.

### Timing Interpretation

The elapsed time reported by P06 includes all analysis modules that ran during the phase. The dominant contributors depend on which feature gates are enabled:

```
  Mathematical Analysis Phase
  ┌────────────────────────────────────────┐
  │                                        │
  │  ┌─────────────┐  ┌─────────────────┐  │
  │  │ TRS Analysis │  │ Confluence      │  │
  │  │ (trs-analysis)│ │ (trs-analysis) │  │
  │  └─────────────┘  └─────────────────┘  │
  │                                        │
  │  ┌─────────────┐  ┌─────────────────┐  │
  │  │ VPA         │  │ Safety          │  │
  │  │ (vpa)       │  │ (verify)        │  │
  │  └─────────────┘  └─────────────────┘  │
  │                                        │
  │  ┌─────────────┐  ┌─────────────────┐  │
  │  │ LTL + Buchi │  │ KAT Hoare +    │  │
  │  │ (ltl)       │  │ Equivalence    │  │
  │  │             │  │ (kat)          │  │
  │  └─────────────┘  └─────────────────┘  │
  │                                        │
  │  ┌─────────────┐  ┌─────────────────┐  │
  │  │ Provenance  │  │ CRA Cost       │  │
  │  │ (provenance)│  │ (cra)          │  │
  │  └─────────────┘  └─────────────────┘  │
  │                                        │
  │  ┌─────────────┐  ┌─────────────────┐  │
  │  │ Morphisms   │  │ CEGAR, Petri,  │  │
  │  │ (morphisms) │  │ Nominal, etc.  │  │
  │  └─────────────┘  └─────────────────┘  │
  │                                        │
  │  elapsed = t_end - t_start             │
  │  (reported by P06 if >= 100us)         │
  └────────────────────────────────────────┘
```

**Typical timing ranges:**

| Configuration | Expected Range | Dominant Cost |
|---------------|---------------|---------------|
| No analysis features enabled | < 100us (P06 silent) | None (phase is a no-op) |
| `trs-analysis` only | 0.1 -- 2ms | Confluence / termination checking |
| `ltl` | 1 -- 50ms | Buchi product construction + SCC |
| `kat` | 0.5 -- 10ms | Bounded bisimulation |
| `provenance` | 0.1 -- 5ms | Polynomial computation |
| `cra` | 0.1 -- 3ms | Register evaluation |
| `morphisms` | 0.2 -- 5ms | Preservation checking |
| All features | 2 -- 100ms | LTL dominates for large grammars |

### Threshold: 100 Microseconds

P06 suppresses output when the elapsed time is below 100 microseconds. This threshold eliminates noise from empty analysis phases (no features enabled) or trivially small grammars where the analysis overhead is negligible. The 100us threshold corresponds to approximately the timer measurement overhead plus minimal setup/teardown costs.

## Trigger Conditions

P06 fires when all of the following hold:

- The pipeline has recorded `math_analysis_elapsed` (a `Duration`).
- The elapsed duration is strictly greater than 100 microseconds.
- A single P06 diagnostic is emitted with the elapsed time formatted in milliseconds (two decimal places).

If the analysis phase was not executed or completed in under 100 microseconds, P06 is silent.

## Example

### Grammar

Any grammar compiled with one or more analysis feature gates enabled.

### Output

```
note[P06] (MyGrammar): mathematical analysis phase completed in 3.47ms
```

For a grammar with many categories and all features enabled:

```
note[P06] (LargeGrammar): mathematical analysis phase completed in 87.21ms
```

## Resolution

No action is required. P06 is an informational diagnostic. If the analysis time is a concern:

1. **Identify the dominant analysis module.** Enable features one at a time to isolate which module contributes the most time. LTL model checking (Buchi product) is typically the most expensive for grammars with many categories and deep recursion.

2. **Reduce grammar complexity.** Fewer categories, less mutual recursion, and simpler rule structures reduce analysis time across all modules.

3. **Disable unused features.** If a feature gate (e.g., `provenance`) is enabled but its results are not being used, disabling it eliminates its contribution to the analysis time.

4. **Compare with P05.** P05 reports WPDS analysis time separately. If P06 time is dominated by WPDS-dependent analyses (LTL, KAT), P05 provides finer-grained insight into the WPDS construction cost.

5. **Use the cost-benefit framework.** The I05 diagnostic (cost-benefit-recommendations) can recommend which analysis gates to enable based on the grammar's structural profile.

## Related Lints

- [P05](../performance/P05-wpds-pipeline-cost.md) -- WPDS pipeline cost. P05 reports the time for WPDS core analysis (poststar/prestar saturation, SCC detection, depth bounds). P06 reports the time for all mathematical analyses, which may include WPDS as a substrate but also covers provenance, CRA, morphisms, KAT, LTL, and others.
- [D14](../wpds/D14-wpds-complexity-report.md) -- WPDS complexity report. Structural metrics (|Gamma|, |Delta|, SCCs) that help predict WPDS-related analysis cost.
- [L01](temporal/L01-ltl-violated.md), [L02](temporal/L02-ltl-verified.md) -- LTL analysis results. The LTL module is often the largest contributor to the analysis time reported by P06.
- [E01](extension/E01-provenance-trace.md), [E02](extension/E02-cra-cost-anomaly.md) -- Extension analysis results. Their computation time is included in the P06 total.
- [K01](kat/K01-hoare-failure.md), [K02](kat/K02-kat-equivalence.md) -- KAT analysis results. Their computation time is included in the P06 total.
- [M01](morphism/M01-morphism-gap.md), [M02](morphism/M02-morphism-preservation-failure.md) -- Morphism analysis results. Their computation time is included in the P06 total.
