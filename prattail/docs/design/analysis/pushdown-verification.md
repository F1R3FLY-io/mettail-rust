# Pushdown Verification Stack

**Source files:** `verify.rs`, `cegar.rs`, `algebraic.rs`, `newton.rs`,
`ewpds.rs`, `ara.rs`, `relational.rs`
**Pipeline phase:** 3 (depends on WPDS construction)
**Feature gates:** `wpds-extended`, `wpds-ara`, `wpds-relational` (verify,
cegar, algebraic, newton are always-on)

## Rationale

The WPDS (Weighted Pushdown System) models PraTTaIL's parser as a pushdown
automaton with semiring-weighted transitions.  Stack symbols represent parse
positions within grammar rules; push/pop/replace transitions model category
entry, return, and rule progression.  The verification stack exploits this
model to answer questions about parser behavior that go beyond syntactic
well-formedness:

- **Safety:** Can the parser reach a known-bad state?
- **Precision:** At what abstraction level is the property decidable?
- **Cost:** What is the minimum-cost path through a grammar region?
- **Invariants:** What affine relationships hold between parser variables?
- **Fixpoints:** How quickly do iterative analyses converge?

---

## 1. Safety Verification (`verify.rs`)

### 1.1 Intuition

Safety properties assert that "something bad never happens."  In the WPDS
framework, "bad" configurations are encoded as a P-automaton (pushdown
automaton recognising a regular set of stack configurations).  The prestar
algorithm computes the set of *all* configurations from which a bad
configuration is reachable.  If the parser's initial configuration is
outside this set, the property holds.

### 1.2 P-Automaton Encoding

A P-automaton `A = (Q, Gamma, delta, q0, F)` recognises a set of stack
configurations `<p, gamma1 ... gamman>` when:

```
  q0 --gamma1--> q1 --gamma2--> ... --gamman--> qf  where qf in F
```

Each state transition is weighted by a semiring value.  The weight of an
accepted configuration is the semiring product of all transition weights
along the accepting path.

### 1.3 Prestar Algorithm

Prestar saturates the P-automaton backward through the WPDS rules:

```
function prestar(wpds, initial_automaton) -> PAutomaton:
    A := copy(initial_automaton)
    worklist := all transitions in A
    while worklist is non-empty:
        (q, gamma, q') := worklist.pop()
        for each WPDS rule matching target gamma:
            match rule:
                Pop(from_gamma, weight):
                    // <p, from_gamma> --> <p', epsilon>
                    new_weight := weight * A.weight(q, gamma, q')
                    if A.add_or_update(q, from_gamma, q', new_weight):
                        worklist.push(q, from_gamma, q')

                Replace(from_gamma, to_gamma, weight):
                    // <p, from_gamma> --> <p', to_gamma>
                    new_weight := weight * A.weight(q, gamma, q')
                    if A.add_or_update(q, from_gamma, q', new_weight):
                        worklist.push(q, from_gamma, q')

                Push(from_gamma, to_bottom, to_top, weight):
                    // <p, from_gamma> --> <p', to_top to_bottom>
                    // Two-step: need intermediate state
                    q_mid := A.get_or_create_state(to_bottom, q')
                    new_weight := weight * A.weight(q_mid, to_top, ?)
                                        * A.weight(q, to_bottom, q')
                    // ... (saturation continues)
    return A
```

### 1.4 SafetyResult

```rust
pub struct SafetyResult<W: Semiring> {
    pub safe: bool,
    pub initial_weight: W,
    pub witness_trace: Vec<StackSymbol>,
}
```

- `safe = true` iff `initial_weight.is_zero()` (unreachable)
- `witness_trace` records the stack symbols along the violating path

### 1.5 Diagram: Prestar Saturation

```
  Bad state automaton (input):         Saturated automaton (output):
  ┌──────────────────────┐             ┌──────────────────────────────┐
  │  q0 --BadRule--> qf  │    prestar  │  q0 --BadRule--> qf         │
  │                      │  ========>  │  q0 --Expr.Add@0--> q0      │
  │                      │             │  q0 --Expr--> q0             │
  │                      │             │  (all configs reaching bad)  │
  └──────────────────────┘             └──────────────────────────────┘

  If initial_symbol is in the saturated automaton
  with non-zero weight: UNSAFE (violated).
```

### 1.6 Semiring Instantiations

| Semiring         | Interpretation of `initial_weight`             |
|------------------|-------------------------------------------------|
| `BooleanWeight`  | `true` = reachable (unsafe), `false` = safe     |
| `TropicalWeight` | Minimum cost to reach bad state (inf = safe)     |
| `CountingWeight` | Number of distinct paths to bad state            |

### 1.7 Repair Suggestions

`suggest_safety_repairs` produces:

1. **Per-step guards:** For each step `i` in the witness trace, suggest
   inserting a guard predicate.  Edit cost increases linearly with trace
   position (earlier = cheaper to fix).

2. **Restrict initial configuration:** Suggest narrowing the entry point
   to exclude the unsafe path.  Confidence = 0.5, edit cost = 3.

Confidence is inversely proportional to trace length:
`confidence = clamp(1/|trace|, 0.1, 1.0)`.

---

## 2. CEGAR: Counterexample-Guided Abstraction Refinement (`cegar.rs`)

### 2.1 Intuition

Full-precision verification may be expensive.  CEGAR starts with the
coarsest abstraction (Boolean reachability) and iteratively refines only
when the current abstraction produces *spurious* counterexamples --
counterexamples that exist in the abstract model but not in the concrete
system.

### 2.2 Abstraction Hierarchy

```
  BooleanWeight (coarsest: yes/no reachability)
       │
       │  refine: spurious CE found
       ▼
  CountingWeight (path multiplicity)
       │
       │  refine: spurious CE found
       ▼
  TropicalWeight (minimum-cost path -- most precise)
```

Each level strictly subsumes the one above:
- Boolean distinguishes reachable from unreachable.
- Counting distinguishes "one path" from "many paths."
- Tropical distinguishes "cheap path" from "expensive path."

### 2.3 Algorithm

```
function cegar_loop(wpds_tropical, bad_states, max_refinements) -> CegarResult:
    level := 0  // start at Boolean
    for iteration in 0..max_refinements:
        match level:
            0 => result := abstract_check_boolean(wpds_tropical, bad_states)
            1 => result := abstract_check_counting(wpds_tropical, bad_states)
            2 => result := check_safety_tropical(wpds_tropical, bad_states)

        if result.safe:
            return Verified { level, iterations: iteration }

        // Validate counterexample against finer abstraction
        if level < 2:
            if is_spurious(result.witness_trace, level + 1):
                level += 1  // refine
                continue
            else:
                return RealCounterexample { trace, level }
        else:
            return RealCounterexample { trace, level: 2 }

    return Inconclusive { max_level_reached: level }
```

### 2.4 Projection Functions

Since Rust is statically typed, CEGAR does not change the semiring type at
runtime.  Instead, the concrete `TropicalWeight` WPDS is projected down:

```
  Boolean projection:  w -> if w != 0 then true else false
  Counting projection: w -> if w != 0 then 1    else 0
  Tropical (identity): w -> w
```

### 2.5 Diagram: CEGAR Loop

```
  ┌───────────────┐     property holds     ┌──────────┐
  │   Abstract    │ ────────────────────▶  │ VERIFIED │
  │  model-check  │                        └──────────┘
  └───────┬───────┘
          │ counterexample found
          ▼
  ┌───────────────┐     real CE            ┌──────────┐
  │   Validate    │ ────────────────────▶  │ VIOLATED │
  │     CE        │                        └──────────┘
  └───────┬───────┘
          │ spurious CE
          ▼
  ┌───────────────┐
  │    Refine     │──── level++ ───▶ back to model-check
  │  abstraction  │
  └───────────────┘
```

---

## 3. Extended WPDS: Merge Functions (`ewpds.rs`)

### 3.1 Problem

Standard WPDS composes caller and callee weights via semiring
multiplication: `w_combined = w_caller * w_callee`.  This conflates local
and global state.  When a caller has local variables invisible to the
callee (as in PraTTaIL's `PNew` and `PInput` constructs), the callee's
weight should not overwrite the caller's local state.

### 3.2 Solution: Merge Functions

An EWPDS push rule `<p, gamma> --> <p', gamma' gamma''>` carries a merge
function `g: D x D -> D` that replaces the standard multiplication:

```
  w_return = g(w_caller, w_callee)
```

The `MergeFunction` trait:

```rust
pub trait MergeFunction<W: Semiring>: Debug + Send + Sync {
    fn merge(&self, caller_weight: &W, callee_weight: &W) -> W;
}
```

### 3.3 Merge Strategies

| Strategy        | Formula                   | Use case                           |
|-----------------|---------------------------|------------------------------------|
| `DefaultMerge`  | `w1 * w2`                 | No local state (standard WPDS)     |
| `OverrideMerge` | `w1 * mask + w2 * (1-mask)`| Callee writes specific variables  |

### 3.4 Pipeline Bridge

`extend_from_bundle` scans `all_syntax` for rules containing
`SyntaxItemSpec::Binder` items.  Each binder marks a call/return boundary
where an EWPDS merge function applies.  Returns `None` if no binders exist
(standard WPDS suffices).

### 3.5 Diagram: EWPDS Saturation

```
  Standard WPDS:              EWPDS:
  caller ──push──▶ callee     caller ──push──▶ callee
    w₁       w₂                 w₁       w₂
       ╲   ╱                       ╲   ╱
        ╲ ╱                    merge fn g
       w₁⊗w₂                   g(w₁,w₂)
         │                         │
      return                    return
```

---

## 4. Affine-Relation Analysis (`ara.rs`)

### 4.1 Intuition

ARA discovers all affine relationships `xi = c0 + c1*x1 + ... + cn*xn`
that hold at each program point, interprocedurally.  It strictly subsumes
constant propagation, copy-constant propagation, and linear-constant
propagation.

### 4.2 Weight Domain

The ARA weight domain is `(VectorSpaces, span-union, span-product, {}, {I})`:

- **Carrier:** sets of `(n+1) x (n+1)` matrices (`n` = number of
  variables), representing the *basis* of a vector space of affine
  transformations.

- **Plus (combine):** span-union -- compute the union of two bases, then
  reduce to a minimal spanning set.  This yields the *join* (least common
  superspace) of two vector spaces.

- **Times (extend):** span-product -- all pairwise products of basis
  elements from the two operands, then basis reduction.  This composes two
  affine transformations.

- **Zero:** empty set of matrices (unreachable)
- **One:** `{I}` -- the identity matrix (no transformation)

### 4.3 Affine Encoding

An assignment `x2 := 3*x1 + 5` is encoded as the matrix:

```
  ┌           ┐
  │ 1  0  5   │     row 0: constant row (homogeneous coord)
  │ 0  1  0   │     row 1: x1 is unchanged
  │ 0  3  0   │     row 2: x2 = 3*x1 + 5*1
  └           ┘
```

The `(n+1)`-th column encodes the constant offset; the `(n+1)`-th row is
always `[0, 0, ..., 0, 1]` for homogeneous coordinates.

### 4.4 Basis Reduction

After span-union or span-product, the basis may be redundant.  Gaussian
elimination produces a reduced row echelon form, eliminating linearly
dependent matrices:

```
function reduce_basis(matrices: [Matrix]) -> [Matrix]:
    // Flatten each matrix to a vector of (n+1)^2 entries
    vectors := [flatten(M) for M in matrices]
    // Gaussian elimination on the resulting (|matrices| x (n+1)^2) matrix
    pivots := row_echelon_form(vectors)
    return [unflatten(v) for v in pivots if v != 0]
```

### 4.5 Feature Gate

`wpds-ara` depends on `wpds-relational` (for the `HeapSemiring` trait) and
`nalgebra` (for matrix operations).

---

## 5. Newton's Method for Semiring Fixpoints (`newton.rs`)

### 5.1 Intuition

Many analyses reduce to solving a system of polynomial equations
`X = F(X)` over a semiring.  Kleene iteration (`kappa_{i+1} = F(kappa_i)`)
converges monotonically but may need many iterations.  Newton's method
accelerates convergence by linearising `F` at each iterate and solving the
linearised system via matrix star closure.

### 5.2 Algorithm

```
function newton_fixpoint(system, max_iterations) -> [W]:
    nu := [W::zero(); system.num_variables]
    for i in 0..max_iterations:
        // 1. Evaluate F at current iterate
        f_nu := system.evaluate(nu)
        // 2. Compute Jacobian matrix J_F(nu)
        jacobian := system.jacobian(nu)
        // 3. Compute J* (Kleene closure of the Jacobian)
        j_star := matrix_star(jacobian)
        // 4. Newton update: nu_{i+1} = J* . F(nu)
        nu_new := matrix_vector_product(j_star, f_nu)
        if converged(nu, nu_new):
            return nu_new
        nu := nu_new
    return nu
```

### 5.3 Matrix Star Closure

`matrix_star(M)` computes `M* = I + M + M^2 + M^3 + ...` via the
generalised Floyd-Warshall algorithm:

```
function matrix_star(M: n x n matrix over StarSemiring) -> n x n matrix:
    R := M
    for k in 0..n:
        for i in 0..n:
            for j in 0..n:
                R[i][j] := R[i][j] + R[i][k] * R[k][k].star() * R[k][j]
    // Add identity
    for i in 0..n:
        R[i][i] := R[i][i] + W::one()
    return R
```

This requires the weight to implement `StarSemiring::star()`.

### 5.4 Convergence Properties

| Semiring kind    | Convergence bound                          |
|------------------|--------------------------------------------|
| Idempotent       | At most `h + 1` iterations (h = strahler number) |
| Non-idempotent, omega-continuous | Guaranteed but iteration count depends on semiring |
| General          | May not converge; bounded by `max_iterations` |

### 5.5 Equation System Representation

```rust
pub struct EquationSystem<W: StarSemiring> {
    pub equations: Vec<Equation<W>>,
    pub num_variables: usize,
}

pub struct Equation<W: StarSemiring> {
    pub lhs_var: usize,           // variable index
    pub terms: Vec<Term<W>>,       // RHS terms
}

pub enum Term<W: StarSemiring> {
    Constant(W),
    Variable(usize),
    Product(Box<Term<W>>, Box<Term<W>>),
    Sum(Box<Term<W>>, Box<Term<W>>),
}
```

---

## 6. Algebraic Path Expressions (`algebraic.rs`)

### 6.1 Intuition

Decompose the WPDS's control flow graph into a regular expression over
semiring weights using Tarjan's path-expression algorithm.  The regular
expression captures all paths through the CFG; evaluating it over a
semiring yields the abstract summary.

### 6.2 Path Expression Grammar

```
  e ::= 0           (no path)
      | 1           (empty path)
      | w           (single edge with weight w)
      | e1 . e2     (sequential composition)
      | e1 + e2     (alternation)
      | e*          (Kleene star -- zero or more repetitions)
```

### 6.3 Tarjan Decomposition

```
function tarjan_decompose(cfg) -> PathExpression:
    sccs := tarjan_scc(cfg)
    for each SCC in reverse topological order:
        if SCC is singleton (no self-loop):
            expr[SCC] := weight of the single node
        else:
            // Build local path expression within the SCC
            inner := build_scc_expression(SCC, cfg)
            expr[SCC] := inner.star()
    // Compose SCCs in topological order
    result := compose_scc_expressions(sccs, expr)
    return result
```

### 6.4 Evaluation

```
function evaluate(expr: PathExpression, semiring: W) -> W:
    match expr:
        Zero     => W::zero()
        One      => W::one()
        Weight(w)=> w
        Seq(a,b) => evaluate(a).times(evaluate(b))
        Alt(a,b) => evaluate(a).plus(evaluate(b))
        Star(a)  => evaluate(a).star()
```

### 6.5 Semiring Instantiations

| Semiring         | Analysis                         |
|------------------|----------------------------------|
| `BooleanWeight`  | Reachability (is there any path?)|
| `TropicalWeight` | Shortest / minimum-cost path     |
| `CountingWeight` | Path counting                    |

---

## 7. Relational Weight Domain (`relational.rs`)

### 7.1 Definition

The relational weight domain on a finite set `G` is:

```
  (2^{G x G}, union, composition, emptyset, id_G)
```

- **Carrier:** binary relations on `G` (sets of `(source, target)` pairs)
- **Plus:** set union (any pair reachable via either relation)
- **Times:** relational composition `R1 ; R2 = { (a,c) | exists b. (a,b) in R1 and (b,c) in R2 }`
- **Zero:** empty relation (unreachable)
- **One:** identity relation `{ (g, g) | g in G }`

### 7.2 HeapSemiring Trait

Because `HashSet<(G, G)>` is heap-allocated and cannot implement `Copy`,
`RelationalWeight` implements a separate `HeapSemiring` trait that mirrors
`Semiring` without the `Copy` bound:

```rust
pub trait HeapSemiring: Clone + Debug + PartialEq + Send + Sync + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

### 7.3 Application

Relational weights model the operational semantics of `language!`
specifications as WPDS rules weighted by state transformations.  The
meet-over-all-valid-paths (MOVP) solution for these weights gives the net
state transformation from initial to target configurations -- this is the
same approach used by SLAM and BLAST for Boolean program analysis.

---

## 8. Diagram: CEGAR + Saturation Interaction

```
  ┌─────────────────────────────────────────────────────────────────┐
  │                        CEGAR Driver                             │
  │                                                                 │
  │  Level 0: Boolean     Level 1: Counting    Level 2: Tropical   │
  │  ┌──────────────┐    ┌──────────────┐     ┌──────────────┐    │
  │  │ project to   │    │ project to   │     │  identity    │    │
  │  │ BooleanWt    │    │ CountingWt   │     │  (concrete)  │    │
  │  └──────┬───────┘    └──────┬───────┘     └──────┬───────┘    │
  │         │                   │                    │             │
  │         ▼                   ▼                    ▼             │
  │  ┌──────────────┐    ┌──────────────┐     ┌──────────────┐    │
  │  │   prestar    │    │   prestar    │     │   prestar    │    │
  │  │  (Boolean)   │    │  (Counting)  │     │  (Tropical)  │    │
  │  └──────┬───────┘    └──────┬───────┘     └──────┬───────┘    │
  │         │                   │                    │             │
  │         ▼                   ▼                    ▼             │
  │     safe / CE           safe / CE            safe / CE         │
  │         │                   │                    │             │
  │     validate CE         validate CE         (concrete CE)      │
  │         │                   │                    │             │
  │    spurious?───▶level++   spurious?──▶level++  real CE         │
  └─────────────────────────────────────────────────────────────────┘
```

---

## 9. Diagram: ARA Matrix Composition

```
  Assignment x₂ := 3·x₁ + 5           Assignment x₁ := x₁ + 1

  A = ┌       ┐                         B = ┌       ┐
      │ 1 0 5 │                             │ 1 0 1 │
      │ 0 1 0 │                             │ 0 1 0 │
      │ 0 3 0 │                             │ 0 0 1 │
      └       ┘                             └       ┘

  Composition A ; B = A × B  (matrix multiplication):

  A × B = ┌       ┐     After: x₂ = 3·(x₁+1) + 5 = 3·x₁ + 8
          │ 1 0 6 │            x₁ = x₁ + 1
          │ 0 1 1 │
          │ 0 3 3 │
          └       ┘

  Span-union {A} union {B}:  two basis matrices representing
  "either assignment A or assignment B is possible at this point"
```

---

## 10. References

- T. Reps, A. Lal & N. Kidd (2007). "Program Analysis Using Weighted
  Pushdown Systems." *SAS 2007*, LNCS 4634.
- S. Schwoon (2002). *Model-Checking Pushdown Systems*. PhD thesis,
  Technical University of Munich.
- E.M. Clarke, O. Grumberg, S. Jha, Y. Lu & H. Veith (2000).
  "Counterexample-Guided Abstraction Refinement." *CAV 2000*, LNCS 1855.
- A. Lal & T. Reps (2006). "Improving Pushdown System Model Checking."
  *CAV 2006*, LNCS 4144.
- J. Esparza, S. Kiefer & S. Luttenberger (2010). "Newton's method for
  omega-continuous semirings." *ICALP 2010*, LNCS 6199.
- Z. Kincaid, J. Cyphert, J. Breck & T. Reps (2019). "Algebraic Program
  Analysis." *CAV 2019*, LNCS 11562.
- R.E. Tarjan (1981). "A unified approach to path problems." *JACM*,
  28(3), pp. 577--593.
