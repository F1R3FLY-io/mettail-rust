# Weighted MSO Logic and the Buchi-Elgot-Trakhtenbrot Theorem — Theoretical Foundations

## Motivation

Automata provide an **operational** view of computation: states, transitions, acceptance. Logic provides a **declarative** view: formulas, quantifiers, satisfaction. A classical result in automata theory — the Buchi-Elgot-Trakhtenbrot theorem — establishes that these two views are equivalent for regular languages: a language is regular if and only if it is definable by a sentence in monadic second-order (MSO) logic. The **weighted** generalization by Droste & Gastin (2007) extends this equivalence to **formal power series**: a series S : Sigma* -> K over a commutative semiring K is recognizable (accepted by a weighted finite automaton) if and only if it is definable by a sentence in the **restricted fragment** of weighted MSO logic.

**Core question**: Which weighted MSO formulas correspond to recognizable formal power series, and how does the fragment hierarchy determine decidability?

**Historical context**: Buchi (1960) proved that MSO-definable languages over omega-words coincide with omega-regular languages. Elgot (1961) and Trakhtenbrot (1961) independently established the MSO-regularity equivalence for finite words. Droste & Gastin (2005, 2007) generalized this to weighted automata, introducing the restricted MSO fragment and proving the weighted Buchi-Elgot-Trakhtenbrot theorem (their Theorem 3.7). The key challenge in the weighted setting is that universal quantification (`forall`) corresponds to semiring products over positions, which may diverge or lose recognizability unless the body is suitably restricted.

**Connection to the Chomsky hierarchy**: The weighted Buchi-Elgot-Trakhtenbrot theorem precisely delineates the boundary of the regular tier (T1) in weighted computation. Formulas in the restricted fragment define recognizable series (T1); restricted existential extensions remain recognizable (T2); unrestricted formulas may fall outside the recognizable class (T3/T4).

## Definitions

**Definition 10.1** (Formal Power Series). A **formal power series** over alphabet Sigma and semiring (K, +, *, 0, 1) is a function S : Sigma* -> K assigning a weight S(w) in K to each word w in Sigma*. The series is **recognizable** if there exists a weighted finite automaton M with [[M]](w) = S(w) for all w.

*Intuition*: A formal power series generalizes a language. Where a language assigns true/false to each word, a power series assigns a semiring value — a cost, a probability, a count, a multiplicity. Recognizability means the series can be computed by a finite-state machine.

In MeTTaIL: Formal power series are implicit in all weighted automata modules. The `weighted_mso.rs` module provides the logical specification side of this duality.

**Definition 10.2** (Weighted MSO Syntax; Droste & Gastin, 2007, Definition 3.1). The **weighted MSO formulas** over alphabet Sigma and semiring K are given by the grammar:

    phi ::= k                        (constant, k in K)
          | P_a(x)                   (label test: position x has label a)
          | neg P_a(x)               (negated label test)
          | x <= y                   (order: position x precedes y)
          | neg(x <= y)              (negated order)
          | x in X                   (set membership)
          | neg(x in X)              (negated set membership)
          | phi_1 or phi_2           (disjunction)
          | phi_1 and phi_2          (conjunction)
          | exists x. phi            (first-order existential)
          | exists X. phi            (second-order existential)
          | forall x. phi            (first-order universal)
          | forall X. phi            (second-order universal)

where x, y are first-order variables (ranging over positions) and X is a second-order variable (ranging over position sets).

In MeTTaIL: The `WeightedMsoFormula` enum encodes this grammar with variants `Constant(String)`, `AtomicPos { label, var }`, `NegAtomicPos`, `Order`, `NegOrder`, `InSet`, `NotInSet`, `Or`, `And`, `ExistsFirst`, `ExistsSecond`, `ForallFirst`, `ForallSecond`.

**Definition 10.3** (Weighted MSO Semantics; Droste & Gastin, 2007, Definition 3.2). For a word w in Sigma*, a variable assignment sigma mapping first-order variables to positions and second-order variables to position sets, the **semantics** [[phi]](w, sigma) in K is:

    [[k]](w, sigma)           = k
    [[P_a(x)]](w, sigma)      = 1_K  if w[sigma(x)] = a,  else 0_K
    [[phi or psi]](w, sigma)   = [[phi]](w, sigma) + [[psi]](w, sigma)
    [[phi and psi]](w, sigma)  = [[phi]](w, sigma) * [[psi]](w, sigma)
    [[exists x. phi]](w, sigma) = Sum_{i in pos(w)} [[phi]](w, sigma[x -> i])
    [[exists X. phi]](w, sigma) = Sum_{I subseteq pos(w)} [[phi]](w, sigma[X -> I])
    [[forall x. phi]](w, sigma) = Prod_{i in pos(w)} [[phi]](w, sigma[x -> i])
    [[forall X. phi]](w, sigma) = Prod_{I subseteq pos(w)} [[phi]](w, sigma[X -> I])

where Sum denotes semiring addition (+) and Prod denotes semiring multiplication (*).

*Intuition*: The logical connectives map to semiring operations: disjunction is addition (combining alternatives), conjunction is multiplication (requiring both conditions). Existential quantification sums over witnesses; universal quantification takes the product over all values. In the Boolean semiring, these reduce to the classical logical operations (or, and, exists, forall).

In MeTTaIL: `evaluate_formula_bool()` implements these semantics for `K = BooleanWeight`, with short-circuit evaluation for efficiency.

**Definition 10.4** (Sentence). A formula phi is a **sentence** if it has no free variables (neither first-order nor second-order). A sentence defines a formal power series S_phi : Sigma* -> K where S_phi(w) = [[phi]](w, empty_assignment).

In MeTTaIL: `is_sentence()` checks `free_variables(phi).is_empty() && free_set_variables(phi).is_empty()`. The `evaluate_sentence_bool()` function evaluates sentences directly.

**Definition 10.5** (Recognizable Step Function; Droste & Gastin, 2007, Definition 4.1). A formula phi is a **recognizable step function** if it is a finite sum (disjunction) of terms of the form `k and psi`, where:
- k is a semiring constant
- psi is a **Boolean formula**: a formula using only atomic predicates, negations, disjunction, conjunction, and existential quantifiers (no weighted constants other than the Boolean values true/false)

*Intuition*: A step function partitions the space of (word, assignment) pairs into finitely many regions (defined by the Boolean formulas psi_i) and assigns a constant weight k_i to each region. The step function form ensures that the universal product Prod_i [[phi]](w, sigma[x -> i]) remains a finite product of constants, which is always well-defined and recognizable.

In MeTTaIL: `is_step_function()` recursively checks this structural property. `is_boolean_formula()` verifies the Boolean sub-formula requirement (no constants other than "true"/"false").

**Definition 10.6** (Formula Classification Hierarchy; Droste & Gastin, 2007, Section 4). The weighted MSO fragment hierarchy, in order of increasing power:

    FirstOrder  subset  Restricted  subset  RestrictedExistential  subset  Full

- **FirstOrder**: No set quantifiers (exists X, forall X) at all. All quantifiers are first-order (exists x, forall x).
- **Restricted**: May use set quantifiers, but no forall X, and forall x only with step-function bodies.
- **RestrictedExistential**: exists X_1 ... exists X_n . psi where psi is in the Restricted fragment.
- **Full**: May include forall X or unrestricted forall x. Generally undecidable over non-finite semirings.

In MeTTaIL: `MsoFormulaClass` enum with variants `FirstOrder`, `Restricted`, `RestrictedExistential`, `Full`. The `classify_formula()` function performs structural analysis to determine the class.

## Key Theorems

**Theorem 10.1** (Weighted Buchi-Elgot-Trakhtenbrot; Droste & Gastin, 2007, Theorem 3.7):
For any commutative semiring (K, +, *, 0, 1) and finite alphabet Sigma, a formal power series S : Sigma* -> K is **recognizable** (accepted by a weighted finite automaton) if and only if S is **definable** by a sentence in the **restricted fragment** of weighted MSO logic over K.

*Proof structure*:
1. **(Recognizable => Restricted MSO)**: Given a weighted automaton M = (Q, Sigma, delta, I, F), construct a restricted MSO sentence phi_M such that [[phi_M]](w) = [[M]](w) for all w. The construction uses second-order existential quantification to "guess" the sequence of states visited during a run, first-order universal quantification over positions to verify transition consistency, and constant-weighted conjunction to accumulate transition weights. The forall x body is a step function because it selects a constant (transition weight) based on a Boolean condition (label match and state sequence consistency).

2. **(Restricted MSO => Recognizable)**: Given a restricted MSO sentence phi, construct a weighted automaton M_phi by structural induction on phi. Atomic predicates yield single-transition automata. Boolean connectives use product and union constructions. Existential quantification uses projection. The key case is forall x with step-function body: the step function partitions positions into finitely many classes, each assigned a constant weight, and the product over positions is computable by a finite automaton tracking the current class assignment.

*Consequence for MeTTaIL*: Formulas classified as `Restricted` or `FirstOrder` define recognizable series and are assigned decidability tier T1 (compile-time decidable). The `check_decidability()` function implements this mapping.

*Reference*: Droste, M. & Gastin, P. (2007). "Weighted automata and weighted logics." *Theoretical Computer Science*, 380(1-2), pp. 69-86.

**Theorem 10.2** (Restricted Existential Closure; Droste & Gastin, 2007, Proposition 4.6):
If phi is a sentence in the restricted fragment, then exists X_1 ... exists X_n . phi also defines a recognizable formal power series. That is, the restricted existential fragment is closed under existential second-order projection.

*Proof sketch*: Existential second-order quantification corresponds to automata-theoretic projection: given an automaton M operating on an extended alphabet Sigma x {0,1}^n (encoding set membership), project away the set-membership tracks to obtain an automaton over Sigma. Projection preserves regularity (it introduces nondeterminism but does not leave the class of finite automata). The weight aggregation under projection is semiring addition (Sum over all possible set assignments), which preserves recognizability.

*Consequence for MeTTaIL*: `RestrictedExistential` formulas are assigned tier T2 (runtime decidable). They define recognizable series, so automata-based algorithms are applicable, but the projection may involve exponential blowup in the number of states.

**Theorem 10.3** (Full MSO Undecidability for Non-Finite Semirings):
Over any semiring K with infinitely many distinct elements, the satisfiability problem for full weighted MSO (with forall X) is undecidable.

*Proof sketch*: The universal second-order quantifier forall X ranges over all subsets of positions. For a word of length n, there are 2^n subsets, so the product Prod_{I subseteq pos(w)} [[phi]](w, sigma[X -> I]) involves 2^n factors. When K is infinite, this product can encode arithmetic over unbounded integers, reducing the halting problem to satisfiability. Even for the Boolean semiring, full MSO over infinite structures (omega-words) is decidable (Buchi 1960), but the weighted version over non-finite semirings loses this property.

*Consequence for MeTTaIL*: Formulas containing `ForallSecond` are assigned tier T4 (undecidable). Formulas that are `Full` due to unrestricted `ForallFirst` (non-step-function body) but without `ForallSecond` are assigned tier T3 (semi-decidable).

**Theorem 10.4** (Boolean Semiring Specialization):
When K = Boolean = ({0, 1}, or, and, 0, 1), weighted MSO reduces to classical MSO. The restricted fragment captures all MSO-definable properties (since every Boolean formula is a step function). Therefore, the full power of classical MSO is available at tier T1 for the Boolean semiring.

*Proof*: In the Boolean semiring, every constant is either 0 or 1, so every formula is trivially a step function (the body of any forall x is "select 1 if condition, 0 otherwise" — which is exactly a Boolean formula). Therefore, the restricted fragment coincides with full MSO for K = Boolean. By Buchi's theorem (1960), MSO over finite words characterizes exactly the regular languages.

*Consequence for MeTTaIL*: `evaluate_formula_bool()` evaluates formulas using the Boolean semiring. All Boolean MSO sentences can be compiled to automata (T1). This justifies using MSO as a specification language for grammar properties — any MSO-expressible grammar property is decidable.

*Reference*: Buchi, J.R. (1960). "Weak Second-Order Arithmetic and Finite Automata." *Mathematical Logic Quarterly*, 6(1-6), pp. 66-92.

**Theorem 10.5** (First-Order Fragment Characterization; McNaughton & Papert, 1971):
The first-order fragment of MSO (no set quantifiers) defines exactly the **star-free** regular languages — those expressible by regular expressions using only union, concatenation, and complement (no Kleene star). Equivalently, the first-order definable languages are exactly those recognized by **aperiodic** finite automata (syntactic monoid is group-free).

*Consequence for MeTTaIL*: `FirstOrder` formulas in the weighted setting define a subclass of recognizable series. This class is sufficient for many grammar predicates (label tests, ordering constraints, local pattern matching) and avoids the complexity of set quantifiers entirely.

*Reference*: McNaughton, R. & Papert, S. (1971). *Counter-Free Automata*. MIT Press.

## Algorithms

### Algorithm 1: Formula Classification

```
PROCEDURE CLASSIFY-FORMULA(phi)
  INPUT:  Weighted MSO formula phi
  OUTPUT: MsoFormulaClass

  1. Scan phi recursively:
     has_forall_second ← false
     has_unrestricted_forall_first ← false
     has_exists_second ← false
     has_forall_first_with_step ← false

  2. For each ForallSecond node: set has_forall_second ← true
     For each ForallFirst node with body beta:
       If IS-STEP-FUNCTION(beta): set has_forall_first_with_step ← true
       Else: set has_unrestricted_forall_first ← true
     For each ExistsSecond node: set has_exists_second ← true

  3. Classification:
     If has_forall_second OR has_unrestricted_forall_first:
       Return Full
     Else if has_exists_second:
       Return RestrictedExistential
     Else if has_forall_first_with_step:
       Return Restricted
     Else:
       If HAS-ANY-SET-QUANTIFIERS(phi): Return Restricted
       Else: Return FirstOrder

  COMPLEXITY: O(|phi|) — single recursive scan
```

### Algorithm 2: Decidability Mapping

```
PROCEDURE CHECK-DECIDABILITY(phi)
  INPUT:  Weighted MSO formula phi
  OUTPUT: DecidabilityTier

  1. class ← CLASSIFY-FORMULA(phi)
  2. Match class:
     FirstOrder | Restricted → T1 (CompileTimeDecidable)
     RestrictedExistential → T2 (RuntimeDecidable)
     Full:
       If HAS-FORALL-SECOND(phi): T4 (Undecidable)
       Else: T3 (SemiDecidable)

  COMPLEXITY: O(|phi|)
```

### Algorithm 3: Boolean Evaluation

```
PROCEDURE EVALUATE-FORMULA-BOOL(phi, w, sigma)
  INPUT:  Formula phi, word w, assignment sigma
  OUTPUT: BooleanWeight

  1. Match phi:
     Constant(s):
       Return one() if s in {"true", "1"}, else zero()

     AtomicPos { label, var }:
       pos ← sigma.first_order[var]
       Return one() if pos < |w| AND w[pos] = label, else zero()

     Or(a, b):
       Return EVAL(a, w, sigma).plus(EVAL(b, w, sigma))

     And(a, b):
       Return EVAL(a, w, sigma).times(EVAL(b, w, sigma))

     ExistsFirst { var, body }:
       result ← zero()
       For i = 0 to |w| - 1:
         sigma' ← sigma[var → i]
         result ← result.plus(EVAL(body, w, sigma'))
         If result = one(): break  // short-circuit
       Return result

     ExistsSecond { var, body }:
       result ← zero()
       For each I subseteq {0, ..., |w|-1}:  // 2^|w| subsets
         sigma' ← sigma[var → I]
         result ← result.plus(EVAL(body, w, sigma'))
         If result = one(): break
       Return result

     ForallFirst { var, body }:
       result ← one()
       For i = 0 to |w| - 1:
         sigma' ← sigma[var → i]
         result ← result.times(EVAL(body, w, sigma'))
         If result = zero(): break  // short-circuit
       Return result

     ForallSecond { var, body }:
       result ← one()
       For each I subseteq {0, ..., |w|-1}:
         sigma' ← sigma[var → I]
         result ← result.times(EVAL(body, w, sigma'))
         If result = zero(): break
       Return result

  COMPLEXITY:
    First-order quantifiers: O(|w|) per quantifier
    Second-order quantifiers: O(2^|w|) per quantifier
    Total: O(|w|^k₁ · 2^(k₂·|w|)) where k₁ = # first-order, k₂ = # second-order quantifiers
```

### Algorithm 4: Free Variable Analysis

```
PROCEDURE FREE-VARIABLES(phi)
  INPUT:  Weighted MSO formula phi
  OUTPUT: (free_first_order: Set<String>, free_second_order: Set<String>)

  1. Traverse phi recursively with bound-variable stack
  2. For each atomic predicate referencing variable v:
     If v not in bound set: add v to free set
  3. For each ExistsFirst/ForallFirst { var, body }:
     Push var onto first-order bound set
     Recurse into body
     Pop var from bound set
  4. For each ExistsSecond/ForallSecond { var, body }:
     Push var onto second-order bound set
     Recurse into body
     Pop var from bound set

  COMPLEXITY: O(|phi|)
```

### Algorithm 5: Existential/Universal Closure

```
PROCEDURE CLOSE-EXISTENTIALLY(phi)
  INPUT:  Weighted MSO formula phi with free first-order variables
  OUTPUT: Sentence (formula with no free first-order variables)

  1. free ← FREE-VARIABLES(phi).first_order
  2. Sort free alphabetically (for deterministic output)
  3. result ← phi
  4. For each var in free:
       result ← ExistsFirst { var, body: result }
  5. Return result

  COMPLEXITY: O(|phi| + |free| · log|free|)
```

## Decidability Analysis

| Formula Class | Tier | Compile-Time | Runtime | Justification |
|--------------|:----:|:------------:|:-------:|--------------|
| FirstOrder | T1 | Decidable | N/A | Star-free regular ⊆ regular; automata construction in O(\|phi\|) |
| Restricted | T1 | Decidable | N/A | Theorem 10.1 (weighted B-E-T); recognizable series |
| RestrictedExistential | T2 | May be expensive | Decidable | Theorem 10.2; projection preserves recognizability |
| Full (no forall X) | T3 | Not guaranteed | Semi-decidable | Unrestricted forall x with non-step body |
| Full (with forall X) | T4 | Undecidable | Undecidable | Theorem 10.3; encodes arithmetic |

## Diagrams

### The Weighted Buchi-Elgot-Trakhtenbrot Bridge

```
       OPERATIONAL                              LOGICAL
  ┌──────────────────┐                   ┌──────────────────┐
  │  Weighted Finite  │   Theorem 10.1   │ Restricted MSO   │
  │  Automaton (WFA)  │◄═══════════════▶│ Sentence         │
  │                   │   equivalence    │                   │
  │  M = (Q,Σ,δ,I,F) │                   │  phi: no forall X │
  │  [[M]]: Σ* → K   │                   │  forall x: step  │
  │                   │                   │  fn body only     │
  └──────────────────┘                   └──────────────────┘
         ↕                                        ↕
  Recognizable series                    Definable series
  S(w) = Sum over                        S(w) = [[phi]](w)
  accepting runs
```

### Fragment Hierarchy with Examples

```
  Full MSO (T3/T4)
  ┌──────────────────────────────────────────────────────┐
  │ forall X. phi(X)  — universal over position sets     │
  │ forall x. phi(x)  where phi is NOT a step function   │
  │                                                       │
  │  RestrictedExistential (T2)                           │
  │  ┌──────────────────────────────────────────────┐     │
  │  │ exists X₁...exists Xₙ. psi                  │     │
  │  │ where psi is in Restricted fragment          │     │
  │  │                                              │     │
  │  │  Restricted (T1)                             │     │
  │  │  ┌────────────────────────────────────┐      │     │
  │  │  │ forall x. (k and boolean_phi(x))   │      │     │
  │  │  │ exists X. phi (no forall X)        │      │     │
  │  │  │                                    │      │     │
  │  │  │  FirstOrder (T1)                   │      │     │
  │  │  │  ┌──────────────────────────┐      │      │     │
  │  │  │  │ exists x. P_a(x)        │      │      │     │
  │  │  │  │ forall x. P_a(x)        │      │      │     │
  │  │  │  │ x <= y, P_a(x) and P_b(y)│     │      │     │
  │  │  │  │ No set quantifiers       │      │      │     │
  │  │  │  └──────────────────────────┘      │      │     │
  │  │  └────────────────────────────────────┘      │     │
  │  └──────────────────────────────────────────────┘     │
  └──────────────────────────────────────────────────────┘
```

### Step Function Structure

```
A step function for forall x. phi(x):

  phi(x) = (k₁ and psi₁(x)) or (k₂ and psi₂(x)) or ... or (kₙ and psiₙ(x))

  where each psi_i is Boolean (no weighted constants)

  Example: forall x. ( (3 and P_a(x)) or (7 and P_b(x)) or (1 and true) )

  Evaluation over word "a b a":
    Position 0 (a): (3 and true) or (7 and false) or (1 and true) = 3 + 0 + 1 = 4
    Position 1 (b): (3 and false) or (7 and true) or (1 and true) = 0 + 7 + 1 = 8
    Position 2 (a): (3 and true) or (7 and false) or (1 and true) = 3 + 0 + 1 = 4

    forall x result = 4 * 8 * 4 = 128  (product over positions)
```

### MeTTaIL Classification Pipeline

```
  WeightedMsoFormula
        │
        ▼
  classify_formula()
        │
        ├── ForallSecond found? ─── yes ──→ Full
        ├── ForallFirst with non-step body? ── yes ──→ Full
        ├── ExistsSecond found? ─── yes ──→ RestrictedExistential
        ├── ForallFirst with step body? ─── yes ──→ Restricted
        └── No set quantifiers? ─── yes ──→ FirstOrder
                                    no ──→ Restricted
        │
        ▼
  check_decidability()
        │
        ├── FirstOrder / Restricted ──→ T1 (CompileTimeDecidable)
        ├── RestrictedExistential ─────→ T2 (RuntimeDecidable)
        ├── Full without ForallSecond ─→ T3 (SemiDecidable)
        └── Full with ForallSecond ────→ T4 (Undecidable)
```

## Connections

**To Module 1 (Symbolic)**: The `DecidabilityTier` enum is defined in `symbolic.rs` and imported by `weighted_mso.rs`. Symbolic automata operations (emptiness, equivalence) are the compile-time decision procedures for T1 formulas.

**To Module 2 (Buchi)**: The classical Buchi theorem is the omega-word specialization of the B-E-T theorem. `WeightedBuchiAutomaton` handles the infinite-word case; weighted MSO handles the finite-word case. Together they cover both halting and non-halting computations.

**To Module 5 (Parity Tree)**: The mu-calculus and MSO are closely related: over trees, MSO and the mu-calculus have the same expressive power (Janin & Walukiewicz, 1996). Parity tree automata decide mu-calculus formulas; weighted MSO provides the string-level logical specification language.

**To Pipeline**: The `analyze_from_bundle()` function constructs MSO formulas from grammar rules and classifies them for decidability. Grammar properties expressible in restricted MSO are guaranteed to be compile-time checkable, enabling fully static lint rules.

**To Lint Layer**: MSO formulas can serve as lint specifications: a lint rule "every position with label X must be preceded by a position with label Y" translates to `forall x. (P_X(x) => exists y. (P_Y(y) and y <= x))`, which is in the restricted fragment (T1) and thus statically decidable.

**Open problems**:
1. **Weighted MSO over trees**: Extending the framework to tree structures (parse trees, ASTs) requires tree-walking weighted automata or weighted tree automata, connecting to Module 5 (parity tree automata).
2. **Efficient compilation**: The B-E-T theorem is constructive but the resulting automata may have non-elementary size blowup (tower of exponentials). Practical compilation requires heuristic optimizations for common formula patterns.
3. **Quantitative model checking**: Using weighted MSO as a specification language for quantitative properties of parse derivations (cost, probability, resource consumption).

## Bibliography

1. Droste, M. & Gastin, P. (2007). "Weighted automata and weighted logics." *Theoretical Computer Science*, 380(1-2), pp. 69-86.

2. Droste, M. & Gastin, P. (2005). "Weighted automata and weighted logics." In *ICALP 2005*, LNCS 3580, pp. 513-525. Springer.

3. Buchi, J.R. (1960). "Weak Second-Order Arithmetic and Finite Automata." *Mathematical Logic Quarterly*, 6(1-6), pp. 66-92.

4. Elgot, C.C. (1961). "Decision Problems of Finite Automata Design and Related Arithmetics." *Transactions of the American Mathematical Society*, 98(1), pp. 21-51.

5. Trakhtenbrot, B.A. (1961). "Finite automata and the logic of one-place predicates." *Doklady Akademii Nauk SSSR*, 140, pp. 326-329.

6. McNaughton, R. & Papert, S. (1971). *Counter-Free Automata*. MIT Press.

7. Droste, M., Kuich, W. & Vogler, H. (eds.) (2009). *Handbook of Weighted Automata*. Springer.

8. Janin, D. & Walukiewicz, I. (1996). "On the Expressive Completeness of the Propositional mu-Calculus with respect to Monadic Second Order Logic." In *CONCUR '96*, LNCS 1119, pp. 263-277. Springer.
