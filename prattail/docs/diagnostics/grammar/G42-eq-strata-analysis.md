# G42: eq-strata-analysis / rule-fusion-analysis / rule-fusion-codegen

**Severity:** Note
**Category:** grammar
**Feature Gate:** None (always enabled)

## Description

G42 is a multi-purpose diagnostic ID covering two related codegen optimizations:
**BCG06 equation stratification** and **BCG02 rule fusion**. The same ID is used
for three distinct diagnostic names:

### eq-strata-analysis (BCG06)

Reports the SCC-based stratification analysis of equation rules. The
stratification decomposes the grammar's equation rules (reflexivity, congruence,
user-defined) into dependency strata, where each stratum's rules depend only on
rules in the same or lower strata. This enables the Ascent engine to evaluate
equations in topological order, avoiding redundant cross-stratum fixpoint
iterations.

```
  Equation stratification:

  stratum 0: [eq_refl_Expr, eq_refl_Name]      (base: reflexivity)
  stratum 1: [eq_cong_Add, eq_cong_Neg]         (depends on stratum 0)
  stratum 2: [eq_user_simplify]                  (depends on stratum 1)

  Evaluation order: 0 -> 1 -> 2 (each stratum reaches fixpoint before next)
```

### rule-fusion-analysis (BCG02)

Reports the results of fusion potential analysis for chained deconstruction-
rewrite patterns. When a deconstruction rule extracts subterms that are then
matched by a rewrite rule, the intermediate relation insertion can potentially
be eliminated by fusing the two rules. The analysis identifies safe and blocked
fusion candidates along with estimated tuple reduction.

```
  Deconstruction-rewrite chain:

  ┌────────────────────────────────┐     ┌──────────────────────────────┐
  │ decon: PPar(children)          │ --> │ rw: PNew(x) -> PNil          │
  │   extracts children into proc  │     │   matches constructor PNew   │
  └────────────────────────────────┘     └──────────────────────────────┘
                    │
            intermediate proc(PNew(x)) tuple
            ⟹ fusable if PNew is consumed by only this rewrite
```

### rule-fusion-codegen (BCG02)

Reports that fused rules were actually generated in the Ascent codegen output.
These are **additive** -- the original unfused rules remain, and the fused rules
provide an alternative derivation path that fires in the same iteration as the
parent deconstruction, eliminating the intermediate tuple step.

## Trigger Conditions

### eq-strata-analysis

- The grammar has at least one equation rule.
- `stratify_equation_rules()` produces a non-empty stratification with
  `total_rules > 0`.

### rule-fusion-analysis

- The grammar has at least one deconstruction rule and at least one rewrite rule.
- `analyze_fusion_potential()` finds at least one fusion candidate (safe or
  blocked). If zero candidates are found, the diagnostic is emitted only in
  verbose mode (`PRATTAIL_LINT_VERBOSE=1`).
- If all candidates are blocked, the diagnostic is emitted only in verbose mode.

### rule-fusion-codegen

- At least one safe fusion candidate exists.
- `generate_all_fused_rules()` produces at least one fused rule.

One diagnostic is emitted per analysis type per grammar.

## Example

### Equation Stratification Output

```
note[G42] (RhoCalc): BCG06 equation stratification: 3 strata, 12 rules, max stratum depth 2
  = hint: stratum 0: [eq_refl_Proc, eq_refl_Name]; stratum 1: [eq_cong_PPar, eq_cong_PNew, eq_cong_NSend]; stratum 2: [eq_user_simplify]
```

### Rule Fusion Analysis Output

```
note[G42] (RhoCalc): BCG02: 3 fusion candidate(s) detected (2 safe, 1 blocked); estimated tuple reduction: 4
  = hint: safe candidates can be fused to eliminate intermediate tuple production; blocked candidates have multiple consumers of the intermediate relation
```

### Rule Fusion Codegen Output

```
note[G42] (RhoCalc): BCG02: 2 fused rule(s) generated for safe deconstruction-rewrite chains
  = hint: fused rules provide an alternative derivation path, eliminating intermediate tuples
```

### Per-Candidate Detail (verbose mode only)

```
note[G42] (RhoCalc): BCG02 [SAFE]: deconstruction of PPar (Proc) -> rewrite rw_simplify_new (Name) matching PNew -- fusable
  = in category `Proc`, rule `rw_simplify_new`

note[G42] (RhoCalc): BCG02 [BLOCKED]: deconstruction of NSend (Name) -> rewrite rw_unfold (Proc) matching PFold -- blocked by: eq_cong_PFold, rw_inline
  = in category `Name`, rule `rw_unfold`
```

## Resolution

### For Equation Stratification

No action required. G42 (eq-strata-analysis) is informational. The
stratification is computed automatically and used to order Ascent rule
evaluation. A deeper stratum structure indicates more dependency layers,
which is normal for grammars with layered congruence and user-defined
equations.

### For Rule Fusion

1. **Review blocked candidates.** If a fusion candidate is blocked because
   multiple consumers reference the intermediate relation, consider whether
   the additional consumers can be refactored to reference the fused result
   instead.

2. **Accept blocked candidates.** If the blocked consumers are legitimately
   needed, the original unfused rules remain and the analysis is informational.

3. **Inspect generated fused rules.** For safe candidates, the generated fused
   rules can be inspected in the Ascent debug file to verify correctness.

## Hint Explanation

- **eq-strata-analysis hint**: shows the stratum decomposition (truncated to 5
  strata by default; set `PRATTAIL_LINT_VERBOSE=1` for full listing).
- **rule-fusion-analysis hint**: **"safe candidates can be fused to eliminate
  intermediate tuple production; blocked candidates have multiple consumers of
  the intermediate relation"** explains the safety criterion.
- **rule-fusion-codegen hint**: **"fused rules provide an alternative derivation
  path, eliminating intermediate tuples"** confirms the additive nature of the
  optimization.

## Related Lints

- [G35](G35-ground-rewrite-short-circuit.md) -- Ground rewrite short-circuit.
  Complements rule fusion: ground rewrites are seeded, non-ground fusable
  chains are fused.
- [G38](G38-bloom-filter-rw-congruence-guard.md) -- Bloom filter rewrite
  congruence guard. Discriminant pre-checks that complement stratified
  evaluation.
- [G41](G41-normalize-dedup-active.md) -- Normalize dedup active. Hash-based
  dedup that reduces redundant fixpoint work alongside stratification.
- [C-AP03](../codegen-antipattern/C-AP03-deep-congruence-chains.md) -- Deep
  congruence chains. Stratification helps manage the impact of deep chains by
  ordering evaluation layers.
