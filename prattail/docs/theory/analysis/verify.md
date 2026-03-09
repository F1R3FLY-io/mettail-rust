# Safety and Liveness Verification

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | always-on (no feature gate)            |
| Source file    | `prattail/src/verify.rs` (~792 lines)  |
| Pipeline phase | Post-WPDS analysis                     |
| Lint codes     | S01 (safety violation), S02 (weak safety) |

## Rationale

Analysis modules detect structural problems (non-confluence, dead rules, scope violations) but do not answer the fundamental question: "Can the parser reach a bad configuration?" Safety verification via WPDS prestar reachability provides a definitive answer. Given a set of bad configurations (encoded as a P-automaton), prestar computes all configurations from which a bad configuration is reachable. If the initial configuration is not in this set, the property holds. Quantitative semirings extend this to resource bounds (minimum cost to reach bad state) and path counting (number of distinct paths to bad state).

## Theoretical Foundations

**Definition (Safety Property).** A safety property `P` asserts that "something bad never happens." Formally, `P` holds for a WPDS `W` with initial configuration `c_0` and bad states `B` iff `c_0 not in pre*(B)`, where `pre*` is the backward reachability operator.

**Definition (Prestar).** Given a WPDS `W = (P, Gamma, Delta)` and a set of configurations `C` (encoded as a P-automaton `A`), `pre*(C)` is the smallest set of configurations containing `C` and closed under backward application of rules in `Delta`.

**Theorem (Prestar Correctness, Schwoon 2002).** The prestar saturation procedure terminates and computes exactly the set of all configurations from which a configuration in `C` is reachable.

**Definition (Witness Trace).** When a safety violation is detected (`safe = false`), the witness trace is a sequence of stack symbols along the path from the initial configuration to a bad state in the prestar result.

**Definition (Quantitative Safety).** The initial weight `w_0 = pre*(B).weight(c_0)` provides quantitative information depending on the semiring:
- `BooleanWeight`: `w_0 = true` means reachable (unsafe), `false` means unreachable (safe).
- `TropicalWeight`: `w_0` = minimum cost to reach bad state (resource bound).
- `CountingWeight`: `w_0` = number of distinct paths to bad state.

**Definition (Repair Suggestions).** Repair confidence is inversely proportional to witness trace length: `confidence = clamp(1/|trace|, 0.1, 1.0)`. Shorter traces yield higher confidence because the causal chain is more direct.

### References

1. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.
2. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*.
3. Bouajjani, A., Esparza, J. & Maler, O. (1997). "Reachability analysis of pushdown automata." *CONCUR*.

## Algorithm Pseudocode

### 1. Safety Check (Prestar-Based)

```
FUNCTION check_safety(wpds, bad_states):
    prestar_result := prestar(wpds, bad_states)

    initial_weight := prestar_result.symbol_weight(wpds.initial_symbol)
    safe := initial_weight.is_zero()

    witness_trace := IF NOT safe THEN
        extract_witness_trace(prestar_result, wpds.initial_symbol)
    ELSE
        []

    RETURN SafetyResult(safe, initial_weight, witness_trace)
```

### 2. Bad-State Automaton Construction

```
FUNCTION build_bad_state_automaton(wpds, bad_labels):
    automaton := new PAutomaton(initial_state = 0)
    final_state := automaton.add_state()
    automaton.mark_final(final_state)

    FOR EACH label in bad_labels:
        FOR EACH sym in wpds.stack_symbols:
            IF sym.rule_label == label OR sym.category == label:
                automaton.add_transition(initial_state, sym, final_state, W::one())

    RETURN automaton
```

### 3. Repair Suggestion Generation

```
FUNCTION suggest_safety_repairs(result, wpds):
    IF result.safe THEN RETURN empty RepairSet

    base_confidence := clamp(1.0 / |result.witness_trace|, 0.1, 1.0)

    // Per-step guard suggestions
    FOR EACH (step_idx, sym) in result.witness_trace:
        repairs.add(RepairSuggestion(
            kind = FixTermination,
            description = "Add guard at {sym} (trace step {step_idx})",
            confidence = base_confidence,
            edit_cost = step_idx + 1,
            alternatives = |trace|
        ))

    // Restrict initial configuration
    repairs.add(RepairSuggestion(
        kind = RestrictInitialConfig,
        description = "Restrict initial configuration to exclude unsafe paths",
        confidence = 0.5,
        edit_cost = 3,
        alternatives = 1
    ))

    RETURN repairs
```

## Complexity Analysis

| Operation                          | Time            | Space           |
|------------------------------------|-----------------|-----------------|
| `check_safety`                     | O(|pre*|)       | O(|A|)          |
| `build_bad_state_automaton`        | O(L . S)        | O(L . S)        |
| `extract_witness_trace`            | O(V + E)        | O(V)            |
| `suggest_safety_repairs`           | O(T)            | O(T)            |
| `suggest_invariant_strengthening`  | O(1)            | O(W)            |
| `verify_from_bundle`              | O(|pre*|)       | O(|A|)          |

Where |pre*| = prestar saturation cost, |A| = automaton size, L = bad labels, S = stack symbols, V = states, E = transitions, T = witness trace length, W = witness description size.

## Verification Pipeline Diagram

```
  ┌──────────────────────────────────────────────────────────────┐
  │                    Safety Verification Pipeline               │
  │                                                              │
  │  WpdsAnalysis                                                │
  │       │                                                      │
  │       ├── unreachable_rules                                  │
  │       │       │                                              │
  │       │       ▼                                              │
  │       │  build_bad_state_automaton()                         │
  │       │       │                                              │
  │       │       ▼                                              │
  │       │  PAutomaton (bad states)                             │
  │       │       │                                              │
  │       │       ▼                                              │
  │       │  check_safety()                                      │
  │       │       │                                              │
  │       │       ├── prestar(wpds, bad_states)                  │
  │       │       ├── symbol_weight(initial_symbol)              │
  │       │       ├── extract_witness_trace() [if unsafe]        │
  │       │       │                                              │
  │       │       ▼                                              │
  │       │  SafetyResult<W>                                     │
  │       │       │                                              │
  │       │       ├── safe: bool                                 │
  │       │       ├── initial_weight: W                          │
  │       │       └── witness_trace: Vec<StackSymbol>            │
  │       │                │                                     │
  │       │                ▼                                     │
  │       │  suggest_safety_repairs()                            │
  │       │       │                                              │
  │       │       ▼                                              │
  │       │  RepairSet (ranked suggestions)                      │
  │       │                                                      │
  │       └── verify_from_bundle()                               │
  │               (pipeline entry point)                         │
  └──────────────────────────────────────────────────────────────┘
```

## Semiring Interpretation

```
  Weight Domain     │ initial_weight   │ Interpretation
  ──────────────────┼──────────────────┼──────────────────────────
  BooleanWeight     │ false → safe     │ yes/no reachability
                    │ true  → unsafe   │
  ──────────────────┼──────────────────┼──────────────────────────
  TropicalWeight    │ +inf  → safe     │ min cost to reach bad state
                    │ finite → unsafe  │ (resource bound)
  ──────────────────┼──────────────────┼──────────────────────────
  CountingWeight    │ 0     → safe     │ number of distinct paths
                    │ n>0   → unsafe   │ to bad state
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`verify_from_bundle(wpds_analysis, categories, all_syntax)`** -- Builds a bad-state automaton from WPDS-unreachable rules and checks safety via prestar. Returns `None` when there are no unreachable rules; `Some(SafetyResult<BooleanWeight>)` otherwise.
- **`suggest_safety_repairs(result, wpds)`** -- Generates per-step guard suggestions and an initial-configuration restriction suggestion from a failed safety check.
- **`suggest_invariant_strengthening(result)`** -- For a `Violated` verification result, generates two complementary suggestions: strengthen precondition (confidence 0.7) and weaken postcondition (confidence 0.6).

### Lint Emission

- **S01 (safety violation)**: Emitted when `check_safety` returns `safe = false` -- a bad configuration is reachable from the initial state.
- **S02 (weak safety)**: Emitted when the safety check passes but the initial weight is close to the boundary (e.g., TropicalWeight is finite but large).

## Rust Implementation Notes

| Type                    | Role                                                     |
|-------------------------|----------------------------------------------------------|
| `SafetyResult<W>`       | Check result: safe flag, initial_weight, witness_trace   |
| `Verdict`               | Enum: Verified, Violated, Unknown                        |
| `VerificationResult<W>` | Full result: verdict, property description, weight, witness |
| `RepairKind`            | Used: FixTermination, StrengthenPrecondition, WeakenPostcondition, Custom |

## Worked Example

A grammar has an unreachable rule `DeadRule` in category `Expr`.

**Step 1: Build bad-state automaton.**

```
Stack symbols: [Expr (entry), Expr.DeadRule@0]
Bad labels: ["DeadRule"]
PAutomaton: q0 --Expr.DeadRule@0--> q1 (final)
```

**Step 2: Run prestar.**

The WPDS has no rules (minimal construction for the unreachable check). Prestar returns the initial P-automaton unchanged.

**Step 3: Check safety.**

```
initial_weight = prestar_result.symbol_weight(Expr_entry)
```

If the initial symbol has no transition to the bad state's final state, `initial_weight = BooleanWeight(false)` (zero), so `safe = true`. The dead rule is genuinely unreachable.

**Step 4: If unsafe (different scenario).**

If the grammar inadvertently creates a path to `DeadRule`:

```
SafetyResult {
  safe: false,
  initial_weight: BooleanWeight(true),
  witness_trace: [Expr (entry), Expr.DeadRule@0]
}
```

Repair suggestions:
```
1. Add guard at Expr (entry) (trace step 0) [confidence: 0.50, cost: 1]
2. Add guard at Expr.DeadRule@0 (trace step 1) [confidence: 0.50, cost: 2]
3. Restrict initial configuration at Expr to exclude unsafe paths [confidence: 0.50, cost: 3]
```

## References

1. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.
2. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*.
3. Bouajjani, A., Esparza, J. & Maler, O. (1997). "Reachability analysis of pushdown automata." *CONCUR*.
4. Le Goues, C. et al. (2012). "GenProg: A generic method for automatic software repair." *IEEE TSE*, 38(1).
5. Reps, T., Schwoon, S., Jha, S. & Melski, D. (2005). "Weighted pushdown systems and their application to interprocedural dataflow analysis." *SCP*, 58(1-2).
