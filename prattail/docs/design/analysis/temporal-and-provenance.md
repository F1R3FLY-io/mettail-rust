# Temporal Logic, Provenance, and Streaming Cost Analysis

**Source files:** `ltl.rs`, `buchi.rs`, `provenance.rs`, `cra.rs`
**Pipeline phase:** 5 (after concurrency analyses)
**Feature gates:** `ltl` (requires `omega`), `provenance`, `cra`
**Lint codes:** L01--L02, P06

## Rationale

PraTTaIL generates parsers that operate on potentially infinite input
streams (REPLs, incremental editors, long-running servers).  Three
complementary analyses target the temporal and quantitative dimensions of
such executions:

- **LTL model checking** verifies temporal invariants of the grammar's
  control flow under WPDS execution: "every open delimiter is eventually
  closed" (liveness), "the parser never enters error state after a valid
  prefix" (safety).
- **Provenance tracking** records HOW a fact is derived, not merely whether
  it is derivable.  The polynomial semiring `N[X]` captures all derivation
  alternatives, enabling diagnosis of ambiguity and dependency analysis.
- **Cost Register Automata** model streaming quantitative computation:
  as the parser processes tokens, registers accumulate semiring-valued costs
  (nesting depth, ambiguity count, recovery penalty), providing parse quality
  metrics.

---

## 1. Linear Temporal Logic (`ltl.rs`)

### 1.1 Intuition

Linear Temporal Logic extends propositional logic with four temporal
operators that talk about the future evolution of a system:

| Operator       | Notation    | Meaning                                       |
|----------------|-------------|-----------------------------------------------|
| Next           | `X phi`     | `phi` holds at the next state                 |
| Eventually     | `F phi`     | `phi` holds at some future state              |
| Always         | `G phi`     | `phi` holds at all future states              |
| Until          | `phi U psi` | `phi` holds until `psi` holds (and `psi` eventually does) |

Two derived operators appear in the implementation as first-class variants
for ergonomics:

| Operator       | Definition            | Meaning                                    |
|----------------|-----------------------|--------------------------------------------|
| Release        | `phi R psi = not(not phi U not psi)` | Dual of Until                  |
| Weak Until     | `phi W psi = (phi U psi) or G(phi)` | Until without the liveness obligation |
| Implies        | `phi -> psi = not phi or psi`        | Standard implication              |

### 1.2 Formal Semantics

An LTL formula `phi` is interpreted over an infinite word
`pi = pi_0, pi_1, pi_2, ...` where each `pi_i` is a set of atomic
propositions that hold at step `i`.  The suffix of `pi` starting at
position `i` is written `pi^i`.

The satisfaction relation `pi, i |= phi` is defined inductively:

```
  pi, i |= true                                     always
  pi, i |= p           iff  p in pi_i               (atomic proposition)
  pi, i |= not phi     iff  pi, i |/= phi
  pi, i |= phi and psi iff  pi, i |= phi  and  pi, i |= psi
  pi, i |= phi or psi  iff  pi, i |= phi  or   pi, i |= psi
  pi, i |= X phi       iff  pi, i+1 |= phi
  pi, i |= F phi       iff  exists j >= i:  pi, j |= phi
  pi, i |= G phi       iff  forall j >= i:  pi, j |= phi
  pi, i |= phi U psi   iff  exists j >= i:  pi, j |= psi
                             and forall i <= k < j:  pi, k |= phi
  pi, i |= phi R psi   iff  forall j >= i:  (pi, j |= psi)
                             or exists k < j:  pi, k |= phi
```

We write `pi |= phi` as shorthand for `pi, 0 |= phi`.

### 1.3 LTL Formula AST

The Rust representation mirrors the formal syntax:

```rust
pub enum LtlFormula {
    True, False,
    Atom(String),
    Not(Box<LtlFormula>),
    And(Box<LtlFormula>, Box<LtlFormula>),
    Or(Box<LtlFormula>, Box<LtlFormula>),
    Implies(Box<LtlFormula>, Box<LtlFormula>),
    Next(Box<LtlFormula>),
    Eventually(Box<LtlFormula>),
    Always(Box<LtlFormula>),
    Until(Box<LtlFormula>, Box<LtlFormula>),
    Release(Box<LtlFormula>, Box<LtlFormula>),
    WeakUntil(Box<LtlFormula>, Box<LtlFormula>),
}
```

The parser (`parse_ltl`) uses recursive descent with precedence levels:

| Precedence | Operators                       | Associativity  |
|:----------:|---------------------------------|----------------|
| 1 (tight)  | atoms, `true`, `false`, `(...)`  | --             |
| 2          | `!`, `X`, `G`, `F`              | prefix (unary) |
| 3          | `U`, `R`, `W`                   | right          |
| 4          | `&&`                            | left           |
| 5          | `||`                            | left           |
| 6 (loose)  | `->`                            | right          |

### 1.4 LTL to Buchi Compilation (GPVW Tableau)

The automata-theoretic approach to model checking (Vardi & Wolper, 1986)
reduces LTL satisfaction to language emptiness.  A system satisfies `phi`
iff:

```
  L(system) intersection L(Buchi(not phi)) = emptyset
```

The GPVW algorithm (Gerth, Peled, Vardi & Wolper, 1995) constructs a
nondeterministic Buchi automaton from an LTL formula via a tableau method.
PraTTaIL implements a simplified structural recursion that handles each
formula form by direct Buchi construction:

```
function ltl_to_buchi(phi: LtlFormula) -> BuchiAutomaton:
    match phi:
        True =>
            // Single accepting state q0 with self-loop on __true__
            q0 (accepting, initial), q0 --__true__--> q0

        False =>
            // Single non-accepting state (empty language)
            q0 (non-accepting, initial)

        Atom(p) =>
            // q0 --p--> q1 (accepting), q1 --__true__--> q1
            // Accepts words where p holds at the first instant

        Not(Atom(p)) =>
            // q0 --!p--> q1 (accepting), q1 --__true__--> q1

        Not(phi) =>
            // Push negation inward (NNF), then compile the result
            ltl_to_buchi(negate_ltl(phi))

        And(phi, psi) =>
            // L(phi and psi) = L(phi) intersect L(psi)
            buchi_intersect(ltl_to_buchi(phi), ltl_to_buchi(psi))

        Or(phi, psi) =>
            // L(phi or psi) = L(phi) union L(psi)
            buchi_union(ltl_to_buchi(phi), ltl_to_buchi(psi))

        Next(phi) =>
            // q0 --__true__--> [embedded phi automaton]
            // Delay by one step, then require phi

        Eventually(phi) =>
            // q0 with __true__ self-loop + nondeterministic jump
            // into phi automaton (F phi = true U phi)

        Always(Atom(p)) =>
            // q0 (accepting) with p self-loop (G p)

        Always(phi) =>
            // Embed phi automaton, add back-edges from accepting
            // to initial states (re-verify phi at every step)

        Until(phi, psi) =>
            // q0: self-loop with phi labels (waiting)
            //     nondeterministic jump into psi automaton
            // Accepting iff psi automaton accepts

        Release(phi, psi) =>
            // Desugar: phi R psi = not(not phi U not psi)

        WeakUntil(phi, psi) =>
            // Desugar: phi W psi = (phi U psi) or G(phi)

        Implies(phi, psi) =>
            // Desugar: phi -> psi = not phi or psi
```

### 1.5 Negation Normal Form

The `negate_ltl` function pushes negation inward using De Morgan and
temporal duality laws:

```
  not(not phi)     = phi
  not(phi and psi) = (not phi) or (not psi)
  not(phi or psi)  = (not phi) and (not psi)
  not(X phi)       = X(not phi)
  not(F phi)       = G(not phi)
  not(G phi)       = F(not phi)
  not(phi U psi)   = (not phi) R (not psi)
  not(phi R psi)   = (not phi) U (not psi)
  not(phi W psi)   = (not phi) U (not psi)       [for non-liveness]
  not(phi -> psi)  = phi and (not psi)
```

### 1.6 Model Checking Pipeline

```
function check_ltl_property(system, property) -> LtlCheckResult:
    // Step 1: Compile the negated property to a Buchi automaton
    neg_formula := negate_ltl(property.formula)
    neg_buchi   := ltl_to_buchi(neg_formula)

    // Step 2: Intersect with the system automaton
    product     := buchi_intersect(system, neg_buchi)

    // Step 3: Check emptiness of the product
    if is_empty(product):
        return Satisfied   // No counterexample exists
    else:
        // Extract a lasso-shaped counterexample:
        // finite prefix + repeating suffix (lasso loop)
        return Violated { prefix, lasso }
```

The `LtlCheckResult` carries three variants:

| Variant        | Meaning                                           |
|----------------|---------------------------------------------------|
| `Satisfied`    | `system |= phi` -- the property holds             |
| `Violated`     | Counterexample found: finite prefix + lasso loop  |
| `Inconclusive` | State space too large or timeout                  |

### 1.7 Diagram: LTL Model Checking Data Flow

```
  LTL property phi
       │
       ▼
  negate_ltl(phi) ──→ not phi
       │
       ▼
  ltl_to_buchi(not phi) ──→ B_neg
       │                        │
       │                        ▼
  System Buchi B_sys ──→ buchi_intersect(B_sys, B_neg) ──→ B_product
                                                               │
                                                               ▼
                                                         is_empty(B_product)?
                                                           ╱          ╲
                                                      yes ╱            ╲ no
                                                         ╱              ╲
                                                  Satisfied        Violated
                                                                  {prefix, lasso}
```

### 1.8 Pipeline Bridge

```rust
pub fn check_from_bundle(
    system_buchi: &BuchiAutomaton,
    properties: &[LtlProperty],
) -> LtlAnalysis
```

Iterates over LTL properties, compiles each to a Buchi automaton via
`ltl_to_buchi`, intersects with the system Buchi, checks emptiness, and
collects results.  Returns `LtlAnalysis` with per-property verdicts.

### 1.9 Complexity

| Operation               | Time                                          |
|-------------------------|-----------------------------------------------|
| LTL formula parsing     | O(n) in formula length                        |
| `ltl_to_buchi`          | O(2^n) in formula size (GPVW worst case)      |
| Buchi intersection      | O(|Q_1| * |Q_2| * |Sigma|) via 3-counter product |
| Emptiness check         | O(|Q| + |delta|) via SCC decomposition        |

---

## 2. Provenance Semiring `N[X]` (`provenance.rs`)

### 2.1 Intuition

Classical Boolean analysis asks: "Is this fact derivable?"  The provenance
semiring asks: "HOW is this fact derivable, and in how many ways?"  Instead
of collapsing all derivation alternatives into a single yes/no answer,
provenance tracks the algebraic structure of alternatives and conjunctions.

The key insight from Green, Karvounarakis & Tannen (2007) is that
different provenance questions arise from different semiring homomorphisms
applied to the same underlying polynomial:

```
  ┌────────────────────────────────────────────────────────────┐
  │                    N[X]  (how-provenance)                  │
  │                   ╱    │     ╲                             │
  │                  ╱     │      ╲   (semiring homomorphisms) │
  │                 ╱      │       ╲                           │
  │    BooleanWeight  CountingWeight  TropicalWeight           │
  │  (which-prov.)   (how-many-prov.)  (cheapest deriv.)      │
  └────────────────────────────────────────────────────────────┘
```

### 2.2 Formal Definition

The provenance semiring `(N[X], +, *, 0, 1)` has:

- **Carrier set** -- multivariate polynomials with natural number
  coefficients over a set of base-fact variables `X = {x_1, x_2, ...}`.
- **Plus** (union of alternatives):
  ```
  (sum_i c_i * m_i) + (sum_j d_j * n_j) = sum_k e_k * p_k
  ```
  where coefficients of matching monomials are added.
- **Times** (conjunction of derivation steps):
  ```
  (sum_i c_i * m_i) * (sum_j d_j * n_j) = sum_{i,j} (c_i * d_j) * (m_i * n_j)
  ```
  Monomials are multiplied by adding exponents.
- **Zero** -- the empty polynomial (no derivation exists).
- **One** -- the constant polynomial `1` (trivial derivation, no base
  facts needed).

### 2.3 Monomial Representation

A monomial is a product of variables with exponents:

```
  m = x_1^{a_1} * x_2^{a_2} * ... * x_n^{a_n}
```

Represented as a sorted map `BTreeMap<ProvenanceVar, u32>` for canonical
form.  The empty monomial (empty map) represents the constant `1`.

```rust
pub struct Monomial {
    pub factors: BTreeMap<ProvenanceVar, u32>,
}
```

Monomial multiplication adds exponents:

```
  (x^a * y^b) * (x^c * z^d) = x^{a+c} * y^b * z^d
```

### 2.4 Polynomial Operations

A provenance weight is a sum of weighted monomials:

```rust
pub struct ProvenanceWeight {
    pub terms: BTreeMap<Monomial, u64>,
}
```

**Plus** (polynomial addition):

```
function plus(p1: ProvenanceWeight, p2: ProvenanceWeight) -> ProvenanceWeight:
    result := clone(p1.terms)
    for (monomial, coefficient) in p2.terms:
        result[monomial] += coefficient
    remove zero-coefficient entries
    return ProvenanceWeight { terms: result }
```

**Times** (polynomial multiplication):

```
function times(p1: ProvenanceWeight, p2: ProvenanceWeight) -> ProvenanceWeight:
    result := empty map
    for (m1, c1) in p1.terms:
        for (m2, c2) in p2.terms:
            product_mono := m1.multiply(m2)    // add exponents
            result[product_mono] += c1 * c2
    remove zero-coefficient entries
    return ProvenanceWeight { terms: result }
```

### 2.5 Valuation Homomorphisms

The universal property of `N[X]` is that it is the *free commutative
semiring* generated by `X`.  Any valuation `v: X -> W` (mapping base facts
to elements of a target semiring `W`) extends uniquely to a semiring
homomorphism `v_hat: N[X] -> W`:

```
function evaluate(p: ProvenanceWeight, v: X -> W) -> W:
    result := W.zero
    for (monomial, coefficient) in p.terms:
        mono_val := W.one
        for (var, exponent) in monomial.factors:
            var_val := v(var)
            mono_val := mono_val * var_val^exponent
        term_val := coefficient *_W mono_val     // repeated addition
        result := result +_W term_val
    return result
```

This collapses provenance into concrete weights:

| Valuation target | Collapses to            | Example                       |
|------------------|------------------------|-------------------------------|
| BooleanWeight    | Is fact derivable?      | `v(x) = true` for all `x`    |
| CountingWeight   | How many derivations?   | `v(x) = 1` for all `x`       |
| TropicalWeight   | Cheapest derivation?    | `v(x) = cost(x)`             |
| ViterbiWeight    | Most probable?          | `v(x) = prob(x)`             |

### 2.6 Example: Ambiguity Diagnosis

Consider a grammar where fact `result` can be derived two ways:
using rule `A` with rule `B`, or using rule `A` twice:

```
  provenance(result) = x_A * x_B + x_A^2
```

This polynomial tells us:
1. Two derivation alternatives exist (`num_alternatives() = 2`).
2. One alternative uses `A` and `B` together (`x_A * x_B`).
3. The other uses `A` twice (`x_A^2`).
4. Evaluating with `CountingWeight` and `v(x) = 1` gives `1*1 + 1 = 2`
   (total derivation count).

### 2.7 Diagram: Provenance Semiring Lattice

```
                        N[X]
                     (most informative)
                    ╱    │     ╲
                   ╱     │      ╲
                  ╱      │       ╲
           N (counting)  │    Tropical (cost)
                  ╲      │       ╱
                   ╲     │      ╱
                    ╲    │     ╱
                     Boolean
                  (least informative)

  Arrow direction: "can be obtained from via homomorphism"
  N[X] is the universal (free) provenance semiring.
  Every other provenance type is a quotient of N[X].
```

### 2.8 Pipeline Bridge

```rust
pub fn track_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    categories: &[CategoryInfo],
) -> Option<ProvenanceAnalysis>
```

Creates a single-variable provenance polynomial for each grammar rule
(the rule label becomes a `ProvenanceVar`).  Returns `ProvenanceAnalysis`
with displayable provenance traces for diagnostic output.  Returns `None`
for empty grammars.

### 2.9 Semiring Laws

`N[X]` satisfies all semiring axioms:

```
  Additive identity:     p + 0 = p
  Additive commutativity: p + q = q + p
  Additive associativity: (p + q) + r = p + (q + r)
  Multiplicative identity: p * 1 = p = 1 * p
  Multiplicative assoc.:  (p * q) * r = p * (q * r)
  Left distributivity:   p * (q + r) = p*q + p*r
  Right distributivity:  (p + q) * r = p*r + q*r
  Annihilation:          p * 0 = 0 = 0 * p
```

These are verified by the test suite (`test_distributive`,
`test_associativity_of_times`, `test_zero_annihilates`,
`test_one_identity`, `test_zero_identity_for_plus`,
`test_commutativity_of_plus`).

---

## 3. Cost Register Automata (`cra.rs`)

### 3.1 Intuition

Weighted automata compute a single value for an entire input word.
Cost Register Automata generalize this by maintaining a finite set of
*registers* that are updated at each step via semiring operations.  This
allows CRAs to express streaming computations that accumulate multiple
independent or interacting quantities as the input is processed.

For PraTTaIL, CRAs model the quantitative aspects of parsing: nesting
depth tracking, ambiguity accumulation, error recovery cost, and other
streaming metrics that evolve as tokens are consumed.

### 3.2 Formal Definition

A Cost Register Automaton over semiring `(W, +, *, 0, 1)` is:

```
  M = (Q, Sigma, R, delta, q_0, nu_0, mu)
```

where:

- `Q` -- finite set of control states
- `Sigma` -- input alphabet (token types)
- `R = {r_0, r_1, ..., r_{k-1}}` -- finite set of registers holding
  semiring values
- `delta: Q x Sigma -> Q x (R -> Expr_R)` -- transition function with
  register updates
- `q_0 in Q` -- initial state
- `nu_0: R -> W` -- initial register valuation
- `mu: Q -> R` -- output register map (which register to read at the end)

### 3.3 Register Expressions

Register updates are built from a small expression language:

```rust
pub enum RegisterExpr {
    Reg(Register),      // current value of a register
    InputCost,          // the input cost for the current symbol
    Zero,               // semiring zero
    One,                // semiring one
    Plus(Box<RegisterExpr>, Box<RegisterExpr>),   // semiring addition
    Times(Box<RegisterExpr>, Box<RegisterExpr>),  // semiring multiplication
}
```

This language is closed under semiring operations and ensures that register
updates are semiring-expressible.

### 3.4 Streaming Evaluation

```
function evaluate_stream(cra, stream: [(symbol, cost)]) -> W:
    state    := cra.initial_state
    registers := cra.initial_values.clone()

    for (symbol, cost) in stream:
        transition := find_enabled(cra.transitions, state, symbol)
        if transition is None:
            return W.zero       // CRA is stuck, no accepting run

        new_registers := registers.clone()
        for (reg_idx, expr) in transition.updates:
            new_registers[reg_idx] := eval_expr(expr, registers, cost)
        // Registers not mentioned in updates are preserved (identity)

        registers := new_registers
        state     := transition.to

    // Return the output register value at the final state
    match cra.output_registers.get(state):
        Some(reg_idx) => registers[reg_idx]
        None          => W.zero
```

The `eval_expr` function evaluates a register expression against the
current register snapshot and input cost:

```
function eval_expr(expr, registers, input_cost) -> W:
    match expr:
        Reg(r)       => registers[r.index]
        InputCost    => input_cost
        Zero         => W.zero
        One          => W.one
        Plus(a, b)   => eval_expr(a) + eval_expr(b)
        Times(a, b)  => eval_expr(a) * eval_expr(b)
```

### 3.5 Example: Tropical Cost Accumulation

A CRA that sums costs using the tropical semiring (where `times` is real
addition and `plus` is `min`):

```
  States: {q0}        (single self-loop state)
  Registers: {r0}     (accumulates total cost)
  Initial: r0 = 0.0   (tropical one = 0.0)
  Output: mu(q0) = r0

  Transition:
    q0 --a--> q0 : r0 := r0 * cost    (tropical * = real +)

  Stream: [(a, 1.0), (a, 2.0), (a, 3.0)]
  Result: 0.0 + 1.0 + 2.0 + 3.0 = 6.0
```

### 3.6 Diagram: CRA Streaming Evaluation

```
  Input stream:  (a, c1)   (b, c2)   (a, c3)   ...
                    │          │          │
                    ▼          ▼          ▼
  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐
  │  q0      │  │  q0      │  │  q1      │  │  ...     │
  │  r0 = v0 │─→│  r0 = v1 │─→│  r0 = v2 │─→│          │
  │  r1 = w0 │  │  r1 = w1 │  │  r1 = w2 │  │          │
  └──────────┘  └──────────┘  └──────────┘  └──────────┘

  v1 = eval(update_expr, [v0, w0], c1)
  w1 = w0                                   (identity update)
  v2 = eval(update_expr, [v1, w1], c2)
  ...

  Final output: registers[mu(final_state)]
```

### 3.7 Bounded Equivalence Checking

Two CRAs are equivalent if they compute the same function from input
streams to semiring values.  For semirings of interest (tropical, counting),
this is decidable in polynomial time (Alur et al., 2013).

The implementation uses bounded testing:

```
function cra_check_equivalence_bounded(a, b, max_length) -> bool:
    alphabet := combined alphabet from a and b transition guards
    cost := W.one    // uniform cost for equivalence testing

    for length in 0..=max_length:
        num_sequences := |alphabet|^length
        if num_sequences > 100_000: break   // safety bound

        for seq_idx in 0..num_sequences:
            stream := build_sequence(seq_idx, alphabet, cost, length)
            if evaluate_stream(a, stream) != evaluate_stream(b, stream):
                return false

    return true
```

The default equivalence length bound is `EQUIVALENCE_LENGTH_BOUND = 6`.

### 3.8 Pipeline Bridge

```rust
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
) -> Option<CraAnalysis>
```

Builds a lightweight CRA summary where each distinct category contributes
one state and a single register counts rule applications.  Returns
`CraAnalysis` with `cost_anomalies`, `state_count`, and `register_count`.
Returns `None` for empty grammars.

### 3.9 Complexity

| Operation                   | Time complexity                              |
|-----------------------------|----------------------------------------------|
| Stream evaluation           | O(|stream| * |updates|) per transition       |
| Bounded equivalence check   | O(sum_{l=0}^{L} |Sigma|^l * (|stream_l| * |updates|)) |
| Register expression eval    | O(|expr|) per evaluation                     |

---

## 4. Interaction Between Temporal and Provenance Analyses

The three analyses complement each other in the pipeline:

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                   WPDS Execution Model                          │
  │                                                                  │
  │   ┌───────────────┐  ┌──────────────────┐  ┌────────────────┐  │
  │   │     LTL       │  │   Provenance     │  │      CRA       │  │
  │   │               │  │                  │  │                │  │
  │   │  "Does the    │  │  "HOW is this    │  │  "What is the  │  │
  │   │   system      │  │   fact derived?" │  │   streaming    │  │
  │   │   satisfy     │  │                  │  │   cost?"       │  │
  │   │   temporal    │  │  Polynomial      │  │                │  │
  │   │   property    │  │  N[X] tracks     │  │  Registers     │  │
  │   │   phi?"       │  │  all derivation  │  │  accumulate    │  │
  │   │               │  │  alternatives    │  │  semiring      │  │
  │   │  Buchi        │  │                  │  │  quantities    │  │
  │   │  intersection │  │  Homomorphism    │  │  per token     │  │
  │   │  + emptiness  │  │  collapses to    │  │                │  │
  │   │               │  │  any semiring    │  │  Equivalence   │  │
  │   │               │  │                  │  │  is decidable  │  │
  │   └───────┬───────┘  └────────┬─────────┘  └───────┬────────┘  │
  │           │                   │                     │           │
  │           ▼                   ▼                     ▼           │
  │       L01/L02              P06                  (metrics)      │
  └──────────────────────────────────────────────────────────────────┘
```

- **LTL + Provenance**: when an LTL property is violated, provenance
  tracks WHICH base facts contributed to the violating derivation,
  enabling targeted repair.
- **LTL + CRA**: CRA cost metrics can serve as atomic propositions in
  LTL formulas (e.g., `G(nesting_cost < threshold)`).
- **Provenance + CRA**: the provenance polynomial can be evaluated under
  CRA-computed costs to determine the cheapest or most probable derivation.

---

## 5. References

- A. Pnueli (1977). "The temporal logic of programs." *FOCS 1977*,
  pp. 46--57.
- M.Y. Vardi & P. Wolper (1986). "An automata-theoretic approach to
  automatic program verification." *LICS 1986*, pp. 332--344.
- R. Gerth, D. Peled, M.Y. Vardi & P. Wolper (1995). "Simple on-the-fly
  automatic verification of linear temporal logic." *PSTV 1995*,
  pp. 3--18.
- P. Gastin & D. Oddoux (2001). "Fast LTL to Buchi automata translation."
  *CAV 2001*, LNCS 2102, pp. 53--65.
- T.J. Green, G. Karvounarakis & V. Tannen (2007). "Provenance semirings."
  *PODS 2007*, pp. 31--40.
- R. Alur, L. D'Antoni, S. Deshmukh, M. Raghothaman & Y. Yuan (2013).
  "Regular functions and cost register automata." *LICS 2013*,
  pp. 13--22.
- R. Alur & M. Raghothaman (2013). "Decision problems for additive
  regular functions." *ICALP 2013*, LNCS 7966, pp. 37--48.
- T. Colcombet (2013). "The theory of stabilisation monoids and regular
  cost functions." *Automata, Languages, and Programming*, ICALP 2013.
