# SYM01-DCE: Symbolic Guard Dead Code Elimination

Advanced Automata Codegen Optimization — M1 Symbolic → Dead Rules

## 1. Quick Start

**What it does**: Eliminates grammar rules whose guards are provably unsatisfiable
by Boolean algebra evaluation. Unsatisfiable guards can never fire on any input,
so the rules behind them are dead weight.

**When it activates**: When the `symbolic-automata` feature is enabled and
`SymbolicAnalysis.unsatisfiable_rule_labels` is non-empty.

**Feature gate**: `symbolic-automata`

**Optimization gate**: `symbolic_guard_dce` (env: `PRATTAIL_OPT_SYMBOLIC_GUARD_DCE`)

**Status**: `OptimizationStatus::Auto`

## 2. Intuition

Consider a grammar with character class guards:

```
rule digit:    [0-9]   → Digit
rule upper:    [A-Z]   → Upper
rule conflict: [0-9] ∧ [A-Z] → Conflict  // impossible!
```

The guard `[0-9] ∧ [A-Z]` is the intersection of two disjoint character classes.
The SFA evaluator proves `sat([0-9] ∧ [A-Z]) = false` — no character can be both
a digit and an uppercase letter. Rule `conflict` is dead.

Without SYM01-DCE, the dead rule persists in the generated Ascent code: it
participates in fixpoint iteration, generates match arms, and consumes compilation
time — all for zero benefit.

## 3. Algorithm

```
Input:  SymbolicAnalysis from Phase 7B
Output: Labels added to dead_rule_labels

for each (description, is_satisfiable) in guard_satisfiability:
    if not is_satisfiable:
        extract rule_label from description
        dead_rule_labels.insert(rule_label)
```

The SFA satisfiability check uses the `BooleanAlgebra` trait:
- `KatBooleanAlgebra`: O(2^n) truth table enumeration for propositional guards
- `IntervalAlgebra`: O(k) interval intersection for numeric range predicates
- `CharClassAlgebra`: O(k) range overlap check for character class patterns

## 4. Integration

SYM01-DCE extends the existing A4 Enhanced DCE optimization. Dead rules from
symbolic analysis are added to the same `dead_rule_labels` set used by WFST
dead-rule detection. The macros crate's existing check
`a.dead_rule_labels.contains(&label)` picks up the new entries automatically —
no new codegen hooks needed.

```
Pipeline:
  WFST dead rules ──┐
  SFA unsat guards ──┼──→ dead_rule_labels ──→ skip in Ascent codegen
  PA low selectivity─┘
```

## 5. Safety

A guard proven unsatisfiable by Boolean algebra evaluation cannot match any input.
By the SFA semantics (Veanes et al. 2010), if φ is unsatisfiable then
{a ∈ Σ | φ(a)} = ∅, so no symbol matches, no transition fires, and the rule
is dead. Removing it cannot change the recognized language.

See [codegen-soundness.md](../theory/optimization/codegen-soundness.md) §2 for
the formal proof.

## 6. Diagnostics

- **SYM01** (unsatisfiable-guard): Emitted as a lint diagnostic when a guard is
  proven unsatisfiable. The lint fires regardless of whether the codegen
  optimization is enabled.

## 7. Related

- [A4 Enhanced DCE](README.md) — Base dead-rule elimination
- [PR01-DCE](PR01-DCE.md) — Probabilistic dead-rule elimination
- [Symbolic Automata Design](../design/symbolic-automata.md) — Full M1 module design
- [Codegen Soundness](../theory/optimization/codegen-soundness.md) — Formal proofs
