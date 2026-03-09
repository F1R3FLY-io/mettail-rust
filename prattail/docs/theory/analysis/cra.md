# Cost Register Automata (CRA)

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `cra`                                  |
| Source file    | `prattail/src/cra.rs` (~664 lines)     |
| Pipeline phase | Post-WPDS analysis                     |
| Lint codes     | E02 (cost anomaly)                     |

## Rationale

Weighted automata assign a single semiring value to each accepted word but cannot express register-based accumulation patterns. Cost Register Automata extend finite automata with a finite set of registers holding semiring values, updated at each transition via semiring operations. CRAs capture exactly the class of regular functions (Mealy machines extended to semiring-valued outputs) while retaining decidable equivalence. In PraTTaIL, CRAs model streaming cost accumulation during parsing: as the parser processes tokens, registers accumulate costs (nesting depth, ambiguity count, error recovery penalty) via semiring operations. The final register values provide quantitative parse quality metrics.

## Theoretical Foundations

**Definition (Cost Register Automaton).** A CRA is `M = (Q, Sigma, R, delta, q_0, nu_0, mu)` where:
- `Q` is a finite set of control states
- `Sigma` is the input alphabet
- `R = {r_0, ..., r_{k-1}}` is a finite set of registers
- `delta` is the transition function with register updates: `delta(q, a) = (q', f)` where `f` maps each register to a `RegisterExpr`
- `q_0` is the initial state
- `nu_0: R -> S` is the initial register valuation
- `mu: Q -> R` maps each state to its output register

**Definition (Register Expression).** Register update expressions are built from:
- `Reg(r)` -- current value of register `r`
- `InputCost` -- the input cost/weight for the current symbol
- `Zero`, `One` -- semiring constants
- `Plus(e_1, e_2)` -- semiring addition
- `Times(e_1, e_2)` -- semiring multiplication

**Theorem (Regular Functions, Alur et al. 2013).** CRAs compute exactly the class of regular functions from words to semiring values. This class is closed under composition and admits decidable equivalence.

**Theorem (Decidable Equivalence, Alur & Raghothaman 2013).** Two CRAs over a commutative semiring are equivalent iff they agree on all input streams. For the semirings of interest (tropical, counting), this is decidable in polynomial time.

**Definition (CRA Evaluation).** On input stream `(a_1, c_1), (a_2, c_2), ..., (a_n, c_n)`:
1. Start in state `q_0` with register valuation `nu_0`
2. For each `(a_i, c_i)`: find transition `(q, a_i) -> (q', f)`, update registers via `f` with input cost `c_i`
3. Output `nu(mu(q_final))` -- the output register value at the final state

### References

1. Alur, R., D'Antoni, L., Deshmukh, J., Raghothaman, M. & Yuan, Y. (2013). "Regular functions and cost register automata." *LICS*.
2. Alur, R. & Raghothaman, M. (2013). "Decision problems for additive regular functions." *ICALP*.
3. Colcombet, T. (2013). "The theory of stabilisation monoids and regular cost functions." *ICALP*.

## Algorithm Pseudocode

### 1. CRA Evaluation (Stream Processing)

```
FUNCTION evaluate_stream(cra, stream):
    state := cra.initial_state
    registers := copy(cra.initial_values)

    FOR EACH (symbol, cost) in stream:
        transition := find_transition(cra, state, symbol)
        IF transition is None:
            RETURN W::zero()   // CRA is stuck — no accepting run

        // Compute new register values from old snapshot
        new_registers := copy(registers)
        FOR EACH (reg_idx, expr) in transition.updates:
            new_registers[reg_idx] := eval_expr(expr, registers, cost)

        registers := new_registers
        state := transition.to

    // Return output register value at final state
    IF cra.output_registers contains state:
        RETURN registers[cra.output_registers[state]]
    ELSE:
        RETURN W::zero()
```

### 2. Register Expression Evaluation

```
FUNCTION eval_expr(expr, registers, input_cost):
    CASE expr OF
        Reg(r):           RETURN registers[r.index]
        InputCost:        RETURN input_cost
        Zero:             RETURN W::zero()
        One:              RETURN W::one()
        Plus(a, b):       RETURN eval_expr(a) OPLUS eval_expr(b)
        Times(a, b):      RETURN eval_expr(a) OTIMES eval_expr(b)
```

### 3. Bounded Equivalence Checking

```
FUNCTION cra_check_equivalence_bounded(a, b, max_length):
    alphabet := combined_alphabet(a, b)
    cost := W::one()

    FOR length := 0 TO max_length:
        num_sequences := |alphabet|^length
        IF num_sequences > 100,000 THEN BREAK

        FOR seq_idx := 0 TO num_sequences - 1:
            stream := decode_sequence(seq_idx, alphabet, length, cost)
            out_a := evaluate_stream(a, stream)
            out_b := evaluate_stream(b, stream)
            IF out_a != out_b:
                RETURN false

    RETURN true
```

## Complexity Analysis

| Operation                         | Time                | Space            |
|-----------------------------------|---------------------|------------------|
| `evaluate_stream`                 | O(n . T . k)        | O(k)             |
| `eval_expr`                       | O(|e|)              | O(d)             |
| `cra_check_equivalence_bounded`   | O(A^L . n . T . k)  | O(k)             |
| `CostRegisterAutomaton::new`      | O(k)                | O(k)             |
| `add_transition`                  | O(1)                | O(U)             |

Where n = stream length, T = transitions per state, k = registers, |e| = expression size, d = expression depth, A = alphabet size, L = max_length bound, U = register updates per transition.

## Architecture Diagram

```
  ┌──────────────────────────────────────────────────────────────┐
  │                   Cost Register Automaton                     │
  │                                                              │
  │  Input Stream: (a₁, c₁), (a₂, c₂), (a₃, c₃), ...         │
  │       │                                                      │
  │       ▼                                                      │
  │  ┌─────────────────────────────────────┐                     │
  │  │  Control State: q                   │                     │
  │  │  ┌──────┬──────┬──────┬───────┐     │                     │
  │  │  │ r₀   │ r₁   │ r₂   │ ...  │     │                     │
  │  │  │ (acc) │(depth)│(err) │      │     │  Registers         │
  │  │  └──┬───┴──┬───┴──┬───┴──────┘     │                     │
  │  │     │      │      │                 │                     │
  │  │     ▼      ▼      ▼                 │                     │
  │  │  Register Update Function           │                     │
  │  │  r₀ := r₀ ⊗ cost                   │                     │
  │  │  r₁ := r₁ ⊕ 1                      │                     │
  │  │  r₂ := r₂ (preserved)              │                     │
  │  └─────────────────────────────────────┘                     │
  │       │                                                      │
  │       ▼                                                      │
  │  Output: registers[mu(q_final)]                              │
  └──────────────────────────────────────────────────────────────┘
```

## Register Update State Machine

```
  Example: cost accumulator on tokens "a", "b"

  ┌────┐  a / r₀ := r₀ ⊗ cost   ┌────┐  b / r₀ := r₀ ⊕ r₁
  │ q₀ │ ───────────────────────▶│ q₁ │ ──────────────────┐
  └────┘                         └────┘                    │
    ▲                              │                       │
    │    a / r₀ := r₀ ⊗ cost      │                       │
    └──────────────────────────────┘                       │
                                                           ▼
                                                     ┌──────────┐
                                                     │ q₂ (out) │
                                                     │ mu = r₀  │
                                                     └──────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`analyze_from_bundle(all_syntax)`** -- Builds a lightweight CRA summary from grammar structure. Each distinct category contributes one state, and a single register counts rule applications. Returns `None` if `all_syntax` is empty.

### Lint Emission

- **E02 (cost anomaly)**: Emitted when register values at the final state exceed thresholds, indicating anomalous parsing cost (e.g., excessive nesting depth or ambiguity count).

## Rust Implementation Notes

| Type                         | Role                                                 |
|------------------------------|------------------------------------------------------|
| `Register`                   | Register reference by index                          |
| `RegisterExpr`               | Expression: Reg, InputCost, Zero, One, Plus, Times   |
| `CraTransition`              | Transition: from, to, guard, updates map             |
| `CostRegisterAutomaton<W>`   | Full CRA generic over semiring W                     |
| `CraAnalysis`                | Pipeline result: cost_anomalies, state/register counts |

## Worked Example

Build a CRA that accumulates tropical costs during token processing.

**Step 1: Define CRA.**

```
States: {q₀}  (single self-loop state)
Registers: {r₀}  (accumulator)
Initial: r₀ = 0.0 (TropicalWeight::one())
Output: mu(q₀) = r₀
Transition: q₀ --"a"--> q₀ [r₀ := r₀ ⊗ cost]
```

Where `⊗` in the tropical semiring is real addition: `r₀ := r₀ + cost`.

**Step 2: Evaluate stream.**

Input: `[("a", 1.0), ("a", 2.0), ("a", 3.0)]`

| Step | Symbol | Cost | r₀ before | Update          | r₀ after |
|------|--------|------|-----------|-----------------|----------|
| 0    | a      | 1.0  | 0.0       | 0.0 + 1.0       | 1.0      |
| 1    | a      | 2.0  | 1.0       | 1.0 + 2.0       | 3.0      |
| 2    | a      | 3.0  | 3.0       | 3.0 + 3.0       | 6.0      |

Output: `r₀ = 6.0` (TropicalWeight(6.0)).

**Step 3: Equivalence checking.**

A second CRA with identical structure produces the same outputs on all test sequences up to length 6. The bounded equivalence check confirms they are equivalent.

## References

1. Alur, R., D'Antoni, L., Deshmukh, J., Raghothaman, M. & Yuan, Y. (2013). "Regular functions and cost register automata." *LICS*.
2. Alur, R. & Raghothaman, M. (2013). "Decision problems for additive regular functions." *ICALP*.
3. Colcombet, T. (2013). "The theory of stabilisation monoids and regular cost functions." *ICALP*.
4. Alur, R. & Cerny, P. (2011). "Streaming transducers for algorithmic verification of single-pass list-processing programs." *POPL*.
5. Droste, M., Kuich, W. & Vogler, H. (Eds.) (2009). *Handbook of Weighted Automata.* Springer.
