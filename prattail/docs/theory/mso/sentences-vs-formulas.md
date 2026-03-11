# Sentences vs Formulas in Weighted MSO — When Quantifiers Determine Computability

## Motivation

The distinction between **formulas** (which may have free variables) and **sentences** (which have none) is far more consequential in the weighted setting than in classical logic. In Boolean logic, a formula with free variable x simply defines a set of positions {i : phi(i) is true}; closing it existentially (exists x. phi) asks whether the set is non-empty. In a weighted semiring, a formula with free variable x defines a **function** from positions to semiring values, and closing it involves a **semiring sum** (or product) over all positions. The algebraic properties of this sum/product critically determine whether the resulting computation is recognizable, decidable, or even well-defined.

**Core question**: How does the presence or absence of free variables, and the choice of quantifier for closing them, affect the expressiveness and decidability of weighted MSO formulas?

**Historical context**: The sentences-vs-formulas distinction in classical MSO is well-understood: a sentence defines a language (set of words), while a formula with free first-order variable x defines a set of (word, position) pairs, and a formula with free second-order variable X defines a set of (word, position-set) pairs. Droste & Gastin (2007) showed that in the weighted setting, this distinction becomes critical for recognizability. A sentence in the restricted fragment defines a recognizable formal power series (Theorem 3.7). But a formula with free variables defines a formal power series over an extended alphabet (encoding the variable assignment), and the recognizability of this extended series depends on the fragment and the semiring.

**Design implications for MeTTaIL**: The weighted MSO module must carefully distinguish formulas from sentences because:
1. Only sentences can be directly evaluated as "is this grammar property satisfied?"
2. Formulas with free variables require an assignment, which may come from pipeline context (e.g., a specific parse position or a set of token positions).
3. The choice of closure (existential vs universal) affects the decidability tier.

## The Structural Distinction

### Formulas: Open Specifications

A **formula** phi with free first-order variables x_1, ..., x_m and free second-order variables X_1, ..., X_n defines a function:

    [[phi]] : Sigma* x Pos^m x P(Pos)^n -> K

mapping a word w, m position assignments, and n position-set assignments to a semiring value.

**In MeTTaIL**: `free_variables(phi)` returns the set of free first-order variables. `free_set_variables(phi)` returns the set of free second-order variables. A formula with non-empty free variable sets is **not** a sentence and cannot be evaluated without an explicit `Assignment`.

**Use cases for formulas (non-sentences)**:
- **Token-level properties**: `P_keyword(x)` — "position x carries the keyword label." This formula, with free variable x, can be applied to specific positions identified by the parser.
- **Relational constraints**: `P_open(x) and P_close(y) and x <= y` — "x is an opening delimiter and y is a matching closing delimiter with x preceding y." The free variables x and y are bound by the surrounding parse context.
- **Feature annotations**: `x in X and P_identifier(x)` — "position x belongs to the feature set X and carries an identifier label." Both x and X are free, to be bound by downstream analysis.

### Sentences: Closed Specifications

A **sentence** is a formula with no free variables. It defines a formal power series:

    [[phi]] : Sigma* -> K

mapping each word to a single semiring value, with no external parameter dependence.

**In MeTTaIL**: `is_sentence(phi)` checks `free_variables(phi).is_empty() && free_set_variables(phi).is_empty()`. The function `evaluate_sentence_bool(phi, word)` evaluates a sentence directly using `BooleanWeight`, asserting that phi has no free variables.

**Use cases for sentences**:
- **Grammar properties**: `exists x. P_keyword(x)` — "there exists a position with the keyword label." This sentence can be evaluated over any word to yield a definitive yes/no (Boolean) or a weight (general semiring).
- **Lint rules**: `forall x. (P_open(x) => exists y. (P_close(y) and x <= y))` — "every opening delimiter has a matching closing delimiter to its right." This sentence defines a lint check that is T1 decidable (the forall x body is a step function over Boolean).
- **Acceptance criteria**: `exists x. exists y. (P_begin(x) and P_end(y) and x <= y)` — "the word contains both a begin and an end marker in order."

## Closure Operations

### Existential Closure

**Operation**: Given a formula phi with free first-order variables {x_1, ..., x_m} (sorted alphabetically), existential closure produces:

    exists x_m. exists x_{m-1}. ... exists x_1. phi

The wrapping order is outermost-to-innermost by reverse alphabetical order (so the last sorted variable is outermost), matching MeTTaIL's `close_existentially()` implementation.

**Semantic effect**: Each free variable x_i is summed over all positions:

    [[exists x_i. phi]](w, sigma) = Sum_{j in pos(w)} [[phi]](w, sigma[x_i -> j])

In the Boolean semiring, this becomes "does there exist a position j such that phi holds with x_i = j?" — the standard existential quantifier.

**Decidability impact**: Existential closure with first-order variables preserves the formula's class. If phi is FirstOrder, the closed sentence is FirstOrder. If phi is Restricted, the closed sentence is Restricted. The decidability tier is unchanged.

**Fragment preservation**: For the restricted fragment, existential first-order closure is harmless: it adds only ExistsFirst nodes, which do not affect the fragment classification (existential quantifiers are allowed in all fragments).

In MeTTaIL: `close_existentially(phi)` wraps each free first-order variable with `ExistsFirst`. Note: it does **not** close free second-order variables. For full closure, the caller must additionally wrap with `ExistsSecond` for each free set variable.

### Universal Closure

**Operation**: Given a formula phi with free first-order variables {x_1, ..., x_m}, universal closure produces:

    forall x_m. forall x_{m-1}. ... forall x_1. phi

**Semantic effect**: Each free variable x_i is multiplied over all positions:

    [[forall x_i. phi]](w, sigma) = Prod_{j in pos(w)} [[phi]](w, sigma[x_i -> j])

In the Boolean semiring, this becomes "does phi hold for ALL positions j with x_i = j?" — the standard universal quantifier.

**Decidability impact**: Universal closure may change the formula's fragment class. The resulting sentence is in the Restricted fragment **only if** the body of each forall x_i is a recognizable step function (Definition 10.5). If the body is not a step function, the sentence is classified as Full MSO, which may be T3 or T4.

**Critical warning**: Universal closure is the most dangerous operation from a decidability perspective. A simple formula like `P_a(x)` (FirstOrder, T1) becomes `forall x. P_a(x)` after universal closure. This particular case is fine (P_a(x) is a Boolean formula, hence a step function), but `forall x. (3 * P_a(x) + 7 * P_b(x))` also works (step function), while `forall x. (forall y. P_a(y))` does NOT (the body of the outer forall contains a forall, which is not a step function).

In MeTTaIL: `close_universally(phi)` wraps each free first-order variable with `ForallFirst`. The `classify_formula()` function will correctly classify the result, potentially promoting it from FirstOrder/Restricted to Full.

### The Asymmetry of Closure

The fundamental asymmetry between existential and universal closure in weighted MSO:

| Property | Existential Closure | Universal Closure |
|----------|:------------------:|:-----------------:|
| Semiring operation | Sum (+) over positions | Product (*) over positions |
| Fragment preservation | Always preserves fragment | Preserves only if body is step function |
| Decidability impact | No tier change | May promote to T3/T4 |
| Boolean specialization | "exists position with property" | "all positions have property" |
| Tropical specialization | "minimum cost position" | "total cost across positions" |
| Counting specialization | "count of satisfying positions" | "product of per-position counts" |

This asymmetry arises because semiring multiplication is typically more "dangerous" than semiring addition: infinite products may diverge (non-convergent), while infinite sums over idempotent semirings always converge. The step-function restriction on universal bodies ensures the product remains well-defined and recognizable.

## Second-Order Quantification

### Free Second-Order Variables

A formula with free second-order variable X ranges over all subsets of positions. The space of assignments is 2^|w|, making explicit enumeration exponentially expensive.

**Example**: `x in X and P_identifier(x)` has free variables x (first-order) and X (second-order). Evaluating this formula requires specifying both a position (for x) and a set of positions (for X).

**Closure with exists X**: Existential second-order closure sums over all 2^|w| subsets:

    [[exists X. phi]](w, sigma) = Sum_{I subseteq pos(w)} [[phi]](w, sigma[X -> I])

This is the RestrictedExistential fragment if phi was in the Restricted fragment.

**Closure with forall X**: Universal second-order closure takes the product over all 2^|w| subsets:

    [[forall X. phi]](w, sigma) = Prod_{I subseteq pos(w)} [[phi]](w, sigma[X -> I])

This immediately pushes the formula into the Full fragment, which is T3 or T4.

### The Hierarchical Impact

```
Open formula: P_a(x)  [FirstOrder, T1]
    |
    +-- exists x. P_a(x)  [FirstOrder sentence, T1]
    |
    +-- forall x. P_a(x)  [Restricted sentence, T1]
    |       (body is step function: P_a(x) is Boolean)
    |
    +-- forall x. (3 * P_a(x))  [Restricted sentence, T1]
    |       (body is step function: 3 AND P_a(x))
    |
    +-- forall x. forall y. P_a(y)  [Full sentence, T3]
            (body of outer forall is NOT step function)

Open formula with set variable: x in X  [no set quantifiers, but has free set var]
    |
    +-- exists X. x in X  [RestrictedExistential, T2]
    |       (still has free first-order var x)
    |
    +-- exists x. exists X. x in X  [RestrictedExistential sentence, T2]
    |
    +-- forall X. x in X  [Full, T4]
            (universal second-order quantification)
```

## Practical Consequences for MeTTaIL

### Grammar Property Specification

When specifying grammar properties as MSO formulas, the guideline is:

1. **Prefer sentences**: Formulate properties as closed sentences whenever possible. This enables direct evaluation and clear decidability classification.

2. **Prefer existential closure**: When a formula has free variables, close existentially rather than universally. Existential closure preserves the fragment class and decidability tier.

3. **Use universal closure only with step-function bodies**: If universal closure is needed (e.g., "all positions satisfy property P"), ensure the body is a recognizable step function. The `is_step_function()` check will catch violations.

4. **Avoid second-order universal quantification**: `forall X. phi` pushes the formula to T4. Use `exists X` when set quantification is needed, or reformulate the property to avoid set quantification entirely.

### The analyze_from_bundle Bridge

The `analyze_from_bundle()` function constructs MSO formulas from grammar rules and ensures they are sentences:

```
For each rule (label, category, items) in all_syntax:
    Create exists x_i. P_{label}(x_i)     // existential first-order
Conjoin all: phi_1 AND phi_2 AND ... AND phi_n
```

The resulting formula is always a sentence (all variables are bound by exists) and is always FirstOrder (no set quantifiers, no universal quantifiers). This guarantees T1 decidability for the grammar analysis.

### Assignment Management

When evaluating formulas (not sentences), the `Assignment` struct provides the variable binding:

- `assignment.first_order: HashMap<String, usize>` maps first-order variables to positions.
- `assignment.second_order: HashMap<String, HashSet<usize>>` maps second-order variables to position sets.

The `evaluate_formula_bool()` function uses the assignment to resolve variable references. Unbound variables cause a panic with a descriptive message ("unbound first-order variable: {var}").

### Short-Circuit Evaluation

For the Boolean semiring, the evaluator implements short-circuit optimization:
- `ExistsFirst`/`ExistsSecond`: stop as soon as `result = one()` (Boolean OR short-circuit).
- `ForallFirst`/`ForallSecond`: stop as soon as `result = zero()` (Boolean AND short-circuit).

This optimization is sound because `BooleanWeight::plus(one, x) = one` and `BooleanWeight::times(zero, x) = zero`. For non-Boolean semirings, short-circuit would require detecting absorbing elements, which is semiring-dependent.

## Diagrams

### Formula vs Sentence Evaluation Flow

```
Formula phi with free vars {x, y}:

  Pipeline context             Assignment sigma
  ┌──────────────┐             ┌───────────────┐
  │ "token at    │             │ x → position 3│
  │  position 3  │ ──builds──▶ │ y → position 7│
  │  and 7"      │             └───────┬───────┘
  └──────────────┘                     │
                                       ▼
                         evaluate_formula_bool(phi, w, sigma)
                                       │
                                       ▼
                                 BooleanWeight


Sentence psi (no free vars):

  evaluate_sentence_bool(psi, w)
        │
        │  (creates empty assignment internally)
        ▼
  BooleanWeight
```

### Closure Decision Tree

```
Formula phi has free variables?
    │
    ├── No → phi is already a sentence
    │        Evaluate directly with evaluate_sentence_bool()
    │
    └── Yes → Which kind?
              │
              ├── First-order only → Choose closure:
              │   │
              │   ├── Existential: close_existentially(phi)
              │   │   Result is same fragment, same tier
              │   │
              │   └── Universal: close_universally(phi)
              │       CHECK: is_step_function(body)?
              │       │
              │       ├── Yes → Restricted, T1
              │       └── No → Full, T3 or T4!
              │
              └── Has second-order free vars → Choose carefully:
                  │
                  ├── exists X. phi → RestrictedExistential, T2
                  │   (if phi was Restricted)
                  │
                  └── forall X. phi → Full, T4!
                      AVOID: undecidable in general
```

### Semiring-Dependent Evaluation

```
Formula: forall x. (k AND P_a(x))

Boolean semiring (K = {0, 1}, OR, AND):
  Word "a a a": forall x → AND over positions → 1 AND 1 AND 1 = 1 (true)
  Word "a b a": forall x → AND over positions → 1 AND 0 AND 1 = 0 (false)

Tropical semiring (K = R+inf, min, +):
  k = 5, Word "a a a":
  forall x → + over positions → 5 + 5 + 5 = 15
  forall x → + over positions for "a b a": 5 + inf + 5 = inf

Counting semiring (K = N, +, ×):
  k = 3, Word "a a a":
  forall x → × over positions → 3 × 3 × 3 = 27
  forall x → × over positions for "a b a": 3 × 0 × 3 = 0
```

## Connections

**To Module 10 (Weighted MSO)**: This document provides the conceptual framework for the sentences-vs-formulas distinction implemented in `weighted_mso.rs`. The `is_sentence()`, `close_existentially()`, `close_universally()`, `free_variables()`, and `free_set_variables()` functions are the programmatic interface to these concepts.

**To the Decidability Classification**: The tier assignments in `check_decidability()` directly reflect the analysis in this document. The critical insight is that universal closure over non-step-function bodies is the primary mechanism by which formulas escape the recognizable (T1/T2) regime.

**To the Pipeline**: The `analyze_from_bundle()` function's strategy of using only existential first-order quantification is a deliberate design choice to guarantee T1 classification. Any future extension to universal quantification or second-order quantification must be accompanied by step-function validation.

**To Lint Specification**: Lint rules specified as MSO sentences inherit the decidability tier of the sentence's fragment class. Lint authors should prefer the FirstOrder fragment (no set quantifiers, no universal quantifiers) for maximum efficiency and guaranteed T1 decidability.

## Bibliography

1. Droste, M. & Gastin, P. (2007). "Weighted automata and weighted logics." *Theoretical Computer Science*, 380(1-2), pp. 69-86.

2. Buchi, J.R. (1960). "Weak Second-Order Arithmetic and Finite Automata." *Mathematical Logic Quarterly*, 6(1-6), pp. 66-92.

3. Elgot, C.C. (1961). "Decision Problems of Finite Automata Design and Related Arithmetics." *Transactions of the American Mathematical Society*, 98(1), pp. 21-51.

4. Trakhtenbrot, B.A. (1961). "Finite automata and the logic of one-place predicates." *Doklady Akademii Nauk SSSR*, 140, pp. 326-329.

5. McNaughton, R. & Papert, S. (1971). *Counter-Free Automata*. MIT Press.

6. Droste, M., Kuich, W. & Vogler, H. (eds.) (2009). *Handbook of Weighted Automata*. Springer.

7. Thomas, W. (1997). "Languages, Automata, and Logic." In *Handbook of Formal Languages*, Vol. 3, pp. 389-455. Springer.
