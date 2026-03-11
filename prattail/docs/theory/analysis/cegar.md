# CEGAR -- Counterexample-Guided Abstraction Refinement

| Property | Value |
|----------|-------|
| **Feature gate** | always-on |
| **Source file** | `prattail/src/cegar.rs` (~2404 lines) |
| **Pipeline phase** | Post-WPDS verification |
| **Lint codes** | S03 (`cegar-refinement`) |

## 1. Rationale

Verifying properties of PraTTaIL grammars against their WPDS models is expensive
when performed at full precision (TropicalWeight). Many properties hold at coarser
abstractions (e.g., simple reachability), and the cost of full analysis is wasted
when the property is trivially true. CEGAR inverts the cost profile: start with the
cheapest abstraction and only refine when a counterexample is found that cannot be
validated at the concrete level.

This follows the standard CEGAR paradigm: verify cheaply, refine lazily.

## 2. Theoretical Foundations

**Formal verification**: See `formal/rocq/mathematical_analyses/theories/CegarSoundness.v`
for Rocq proofs of soundness (Theorem `cegar_soundness`), relative completeness
(Theorem `cegar_relative_completeness`), and termination (Theorem `cegar_terminates`).

### 2.1. Abstraction Hierarchy

The CEGAR loop walks a lattice of semiring precision:

```
BooleanWeight   (coarsest: reachability only)
      |
      | refine
      v
CountingWeight  (intermediate: exact path multiplicity)
      |
      | refine
      v
TropicalWeight  (most precise: minimum-cost path)
```

**Definition (Abstraction Function).** An abstraction function
`alpha_L: W_concrete -> W_abstract` maps concrete weights to abstract weights
such that:

- `alpha_L(0_concrete) = 0_abstract`
- `alpha_L(w) != 0_abstract` for all `w != 0_concrete`

**Definition (Galois Connection).** The abstraction functions form a Galois
connection `(alpha, gamma)` between the concrete and abstract weight domains:

- `alpha` is the projection (e.g., `TropicalWeight -> BooleanWeight`)
- `gamma` is the concretization (e.g., `true -> {w | w != 0}`)

**Theorem (Soundness of Abstraction).** If the abstract model verifies a
property (no counterexample), then the concrete model also verifies it.
Formally, if `prestar(alpha(WPDS), alpha(bad)) cap alpha(initial) = emptyset`,
then `prestar(WPDS, bad) cap initial = emptyset`.

*Proof sketch.* Since `alpha` is an over-approximation (it preserves non-zero
reachability), every concrete path maps to an abstract path. If no abstract path
reaches the bad states, no concrete path can either.

### 2.2. Refinement Criterion

A counterexample trace `sigma = [gamma_0, gamma_1, ..., gamma_k]` found at
abstraction level `L` is **spurious** if its validation at the concrete level
yields zero weight:

```
weight_concrete(sigma) = 0_TropicalWeight
```

When a spurious counterexample is detected, the CEGAR loop advances to the next
refinement level `L' > L` in the hierarchy, gaining strictly more discriminating
power.

### 2.3. Termination

The hierarchy has three levels (Boolean, Counting, Tropical). The CEGAR loop
terminates after at most 3 refinement steps (plus a configurable `max_refinements`
bound). At the Tropical level, the analysis is fully precise and cannot produce
spurious counterexamples.

## 3. Algorithm Pseudocode

### 3.1. Main CEGAR Loop

```
function cegar_verify(wpds, bad_states, config):
    level := config.initial_level   // typically Boolean
    log := CegarLog::new()

    for iteration in 0..config.max_refinements:
        // Step 1: Project WPDS to current abstraction level
        (abstract_wpds, abstract_bad) := project(wpds, bad_states, level)

        // Step 2: Model-check via prestar
        (verdict, counterexample) := abstract_check(abstract_wpds, abstract_bad)

        // Step 3: If verified, return success
        if verdict == Verified:
            log.add_step(level, Verified, None, false, "")
            return CegarResult::Verified(level, log)

        // Step 4: Validate counterexample at concrete level
        concrete_weight := validate_trace(wpds, counterexample)
        is_spurious := concrete_weight.is_zero()

        if not is_spurious:
            log.add_step(level, Violated, counterexample, false, "")
            return CegarResult::Refuted(counterexample, log)

        // Step 5: Counterexample is spurious -- refine
        level := next_level(level)
        log.add_step(level, Violated, counterexample, true,
                     "spurious -- refining to " + level)

    return CegarResult::Inconclusive(log)
```

### 3.2. Abstract Model Check

```
function abstract_check(wpds, bad_states):
    result := prestar(wpds, bad_states)
    if accepts_initial_config(result, wpds.initial_symbol):
        trace := extract_trace(result, wpds.initial_symbol)
        return (Violated, Some(trace))
    else:
        return (Verified, None)
```

### 3.3. Weight Projection

```
function project_wpds_to_boolean(wpds: Wpds<TropicalWeight>):
    for each rule in wpds.rules:
        rule.weight := BooleanWeight(!rule.weight.is_zero())
    return projected_wpds
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `project_wpds_to_*` | O(R) | O(R) |
| `prestar` at Boolean level | O(R * S^2) | O(S^2) |
| `prestar` at Counting level | O(R * S^2) | O(S^2) |
| `prestar` at Tropical level | O(R * S^2) | O(S^2) |
| `validate_trace` | O(k * R) | O(k) |
| Full CEGAR loop (worst case) | O(3 * R * S^2) | O(S^2) |

Where: R = number of WPDS rules, S = number of stack symbols,
k = counterexample trace length.

The key insight is that the Boolean prestar is significantly cheaper in practice
(bitwise operations vs. floating-point min) even though the asymptotic complexity
is the same.

## 5. Unicode Diagrams

### 5.1. CEGAR Loop State Machine

```
                    ┌─────────────────────────────────┐
                    │          CEGAR Loop              │
                    └─────────────────────────────────┘
                                  │
                                  v
                    ┌─────────────────────────────────┐
                    │  Project WPDS to level L        │
                    └──────────────┬──────────────────┘
                                   │
                                   v
                    ┌─────────────────────────────────┐
                    │  Run prestar(abstract_wpds)      │
                    └──────────────┬──────────────────┘
                                   │
                          ┌────────┴────────┐
                          │                 │
                    Verified            Violated
                          │                 │
                          v                 v
                    ┌──────────┐   ┌─────────────────┐
                    │  DONE    │   │ Validate trace   │
                    │ (proof)  │   │ at concrete      │
                    └──────────┘   └────────┬────────┘
                                            │
                                   ┌────────┴────────┐
                                   │                 │
                               Genuine          Spurious
                                   │                 │
                                   v                 v
                            ┌──────────┐   ┌─────────────────┐
                            │  DONE    │   │ level := next(L) │
                            │ (refute) │   │ goto Project     │
                            └──────────┘   └─────────────────┘
```

### 5.2. Abstraction Hierarchy

```
    ┌─────────────────────────────────────────────┐
    │            Abstraction Ladder                │
    ├─────────────────────────────────────────────┤
    │                                             │
    │  Level 0: BooleanWeight                     │
    │  ─────────────────────                      │
    │  alpha(w) = { true  if w != 0               │
    │             { false if w == 0               │
    │  Answers: "Is the bad state reachable?"     │
    │                        │                    │
    │                        │ refine             │
    │                        v                    │
    │  Level 1: CountingWeight                    │
    │  ───────────────────────                    │
    │  alpha(w) = { 1 if w != 0                   │
    │             { 0 if w == 0                   │
    │  Answers: "How many paths reach bad?"       │
    │                        │                    │
    │                        │ refine             │
    │                        v                    │
    │  Level 2: TropicalWeight                    │
    │  ───────────────────────                    │
    │  alpha(w) = w  (identity)                   │
    │  Answers: "What is the cheapest bad path?"  │
    │                                             │
    └─────────────────────────────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `cegar_verify(wpds, bad_states, config)` -- Entry point. Called from
  `pipeline.rs` when the S03 cost-benefit gate is enabled.
- `abstract_check(wpds, bad_states)` -- Generic over any semiring `W`. Uses
  `crate::wpds::prestar` internally.
- `project_wpds_to_boolean(wpds)` -- Projects `Wpds<TropicalWeight>` to
  `Wpds<BooleanWeight>`.
- `project_wpds_to_counting(wpds)` -- Projects `Wpds<TropicalWeight>` to
  `Wpds<CountingWeight>`.

### 6.2. Lint Emission

- **S03** (`cegar-refinement`): Emitted when the CEGAR loop encounters a
  spurious counterexample and refines. Severity: Note. The diagnostic includes
  the abstraction level, the spurious trace, and the refinement action.

### 6.3. Repair Integration

No direct repair suggestions. CEGAR produces a `CegarResult` that downstream
analyses (safety verification, WPDS optimization) consume to decide whether
further analysis is needed.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `AbstractionLevel` | Enum: Boolean, Counting, Tropical, Custom |
| `CounterexampleTrace` | Stack symbol sequence witnessing a violation |
| `RefinementStep` | Single iteration record: level, verdict, trace, is_spurious |
| `CegarLog` | Chronological sequence of `RefinementStep`s |
| `CegarConfig` | Configuration: max_refinements, initial_level |
| `CegarResult` | Outcome enum: Verified, Refuted, Inconclusive |

Key design decision: Rust's static typing prevents changing the semiring type at
runtime. The implementation uses three separate projection functions
(`project_wpds_to_boolean`, `project_wpds_to_counting`, identity for Tropical)
rather than a single generic projection with runtime dispatch. This avoids
dynamic dispatch overhead and keeps each projection monomorphized.

## 8. Worked Example

Consider a grammar with 3 stack symbols (`A`, `B`, `C`) and WPDS rules:

```
A -> B  (weight 3.0)
B -> C  (weight 2.0)
C -> A  (weight 1.0)   // cycle
B -> bad (weight 5.0)  // bad state
```

**CEGAR iteration 1 (Boolean):**
- Project: all non-zero weights become `true`.
- Prestar: backward reachability from `bad`. Path `B -> bad` exists.
- Counterexample: `[B, bad]`.
- Validate at concrete: weight = 5.0 (non-zero). Genuine counterexample.
- Result: `Refuted([B, bad])`.

**Alternative scenario (spurious):**
If the bad-state rule had weight 0.0 (unreachable), Boolean would still report
it as reachable (since `!0.0.is_zero()` might be `true` for non-infinity values).
The validation step would find weight = 0.0, mark it spurious, and refine to
Counting, which would correctly report zero paths.

## 9. References

1. Clarke, E., Grumberg, O., Jha, S., Lu, Y. & Veith, H. (2000).
   "Counterexample-Guided Abstraction Refinement."
   *Proc. 12th International Conference on Computer Aided Verification (CAV)*,
   LNCS 1855, Springer, pp. 154--169.

2. Ball, T., Rajamani, S.K. (2001).
   "The SLAM Project: Debugging System Software via Static Analysis."
   *Proc. 28th ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)*, pp. 1--3.

3. Reps, T., Lal, A. & Kidd, N. (2007).
   "Program Analysis Using Weighted Pushdown Systems."
   *Proc. 27th International Conference on Foundations of Software Technology
   and Theoretical Computer Science (FSTTCS)*, LNCS 4855, Springer.

4. Clarke, E., Grumberg, O. & Peled, D. (1999).
   *Model Checking*. MIT Press.

5. Henzinger, T.A., Jhala, R., Majumdar, R. & Sutre, G. (2002).
   "Lazy Abstraction."
   *Proc. 29th ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)*, pp. 58--70.
