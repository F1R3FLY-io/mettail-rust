# Weighted MSO Logic -- Logical Specification Language for Grammar Properties

## Quick Start

Weighted Monadic Second-Order (MSO) logic provides a declarative specification language for grammar properties, following Droste & Gastin's framework for weighted automata and weighted logics. The module provides `WeightedMsoFormula` (a full weighted MSO formula AST), `classify_formula()` (fragment classification into Restricted/RestrictedExistential/FirstOrder/Full), decidability analysis via `DecidabilityTier` (T1--T4), free variable computation, existential/universal closure, and Boolean evaluation. The key theorem is the Weighted Buchi-Elgot-Trakhtenbrot correspondence: recognizable formal power series are exactly those definable in the restricted MSO fragment.

**Motivating example**: The lint rule "there exists a position where token X follows token Y" is an MSO formula `exists x. exists y. P_X(x) /\ P_Y(y) /\ (y <= x)`. This formula is first-order (no set quantifiers), classified T1 (compile-time decidable), and evaluable against concrete words.

```
WeightedMsoFormula (AST)
      |
      +---> classify_formula()        -> MsoFormulaClass
      |                                      |
      |                                      +---> DecidabilityTier (T1-T4)
      |
      +---> free_variables()          -> HashSet<String>
      +---> free_set_variables()      -> HashSet<String>
      +---> is_sentence()             -> bool
      +---> close_existentially()     -> WeightedMsoFormula
      +---> close_universally()       -> WeightedMsoFormula
      +---> evaluate_formula_bool()   -> BooleanWeight
      +---> evaluate_sentence_bool()  -> BooleanWeight
```

## Intuition

Think of weighted MSO as a spreadsheet formula language. Each cell in the spreadsheet corresponds to a position in a word. Atomic predicates (`P_a(x)`) check which symbol is at a position (like `=IF(A1="a", 1, 0)`). Existential quantification (`exists x`) searches the spreadsheet for a row satisfying a condition. Universal quantification (`forall x`) checks that every row satisfies a condition. Set quantification (`exists X`) searches over column selections. Weights are semiring values that replace the Boolean true/false with quantitative measures -- costs, probabilities, or counts.

**Before this module**: Grammar properties were expressed procedurally as Rust code, with no connection to the formal logic-automata correspondence.

**After this module**: Properties are expressed declaratively as MSO formulas, automatically classified into decidability tiers, and evaluated against concrete words. The Droste-Gastin theorem guarantees that restricted formulas correspond exactly to weighted automata.

**Key insight**: The restricted fragment (no `forall X`, `forall x` only with step-function bodies) is exactly the fragment that corresponds to weighted finite automata. Formulas outside this fragment are flagged as T3/T4 (semi-decidable/undecidable), guiding the user toward expressible specifications.

## Theoretical Foundations

**Definition 10.1 (Weighted MSO Formula, Droste & Gastin 2007).** A weighted MSO formula over semiring `K` and alphabet `Sigma` is defined inductively:

```
phi ::= k                   (constant, k in K)
      | P_a(x)              (position x has label a)
      | neg P_a(x)          (negated label test)
      | x <= y              (position ordering)
      | neg(x <= y)         (negated ordering)
      | x in X              (set membership)
      | neg(x in X)         (negated membership)
      | phi \/ psi           (disjunction -> ⊕)
      | phi /\ psi           (conjunction -> ⊗)
      | exists x. phi        (first-order existential -> sum over positions)
      | exists X. phi        (second-order existential -> sum over subsets)
      | forall x. phi        (first-order universal -> product over positions)
      | forall X. phi        (second-order universal -> product over subsets)
```

**Definition 10.2 (Formula Semantics).** For word `w in Sigma*` and variable assignment `sigma`:

```
[[k]](w, sigma)              = k
[[P_a(x)]](w, sigma)         = 1_K if w[sigma(x)] = a, else 0_K
[[phi \/ psi]](w, sigma)     = [[phi]](w, sigma) ⊕ [[psi]](w, sigma)
[[phi /\ psi]](w, sigma)     = [[phi]](w, sigma) ⊗ [[psi]](w, sigma)
[[exists x. phi]](w, sigma)  = ⊕_{i in pos(w)} [[phi]](w, sigma[x -> i])
[[exists X. phi]](w, sigma)  = ⊕_{I ⊆ pos(w)} [[phi]](w, sigma[X -> I])
[[forall x. phi]](w, sigma)  = ⊗_{i in pos(w)} [[phi]](w, sigma[x -> i])
[[forall X. phi]](w, sigma)  = ⊗_{I ⊆ pos(w)} [[phi]](w, sigma[X -> I])
```

**Definition 10.3 (Recognizable Step Function).** A formula `phi` is a recognizable step function if it is a finite sum (disjunction) of terms `k /\ psi` where `k` is a semiring constant and `psi` is a Boolean formula (containing no semiring constants other than `"true"` and `"false"`).

**Definition 10.4 (Formula Classification).** The fragment hierarchy:

```
FirstOrder ⊂ Restricted ⊂ RestrictedExistential ⊂ Full
```

- **FirstOrder**: No set quantifiers at all. Decidable (T1).
- **Restricted**: May use set quantifiers but no `forall X`, and `forall x` only with step-function bodies. Decidable (T1).
- **RestrictedExistential**: `exists X_1 ... exists X_n. psi` with `psi` restricted. Runtime decidable (T2).
- **Full**: Contains `forall X` or unrestricted `forall x`. Semi-decidable (T3) or undecidable (T4).

**Theorem 10.1 (Weighted Buchi-Elgot-Trakhtenbrot, Droste & Gastin 2007).** For any commutative semiring K and finite alphabet Sigma: A formal power series `S: Sigma* -> K` is **recognizable** (accepted by a weighted finite automaton) if and only if `S` is **definable** by a sentence in the **restricted fragment** of weighted MSO logic over K.

## Design

### Core types

```rust
pub enum WeightedMsoFormula {
    Constant(String),                                    // k in K
    AtomicPos { label: String, var: String },            // P_a(x)
    NegAtomicPos { label: String, var: String },         // neg P_a(x)
    Order { x: String, y: String },                      // x <= y
    NegOrder { x: String, y: String },                   // neg(x <= y)
    InSet { var: String, set_var: String },               // x in X
    NotInSet { var: String, set_var: String },             // neg(x in X)
    Or(Box<WeightedMsoFormula>, Box<WeightedMsoFormula>), // phi \/ psi
    And(Box<WeightedMsoFormula>, Box<WeightedMsoFormula>),// phi /\ psi
    ExistsFirst { var: String, body: Box<WeightedMsoFormula> },    // exists x.
    ExistsSecond { var: String, body: Box<WeightedMsoFormula> },   // exists X.
    ForallFirst { var: String, body: Box<WeightedMsoFormula> },    // forall x.
    ForallSecond { var: String, body: Box<WeightedMsoFormula> },   // forall X.
}

pub enum MsoFormulaClass {
    Restricted,              // no forall X, forall x only with step body
    RestrictedExistential,   // exists X ... restricted
    FirstOrder,              // no set quantifiers
    Full,                    // forall X or unrestricted forall x
}
```

### Classification and decidability flow

```
  WeightedMsoFormula
        |
        v
  classify_formula()
        |
        +-- FirstOrder ---------> T1 (compile-time)
        +-- Restricted ----------> T1 (compile-time)
        +-- RestrictedExistential -> T2 (runtime)
        +-- Full -----------------> T3/T4 (semi/undecidable)
```

## Algorithms

### Formula Classification

```
Input:  WeightedMsoFormula
Output: MsoFormulaClass

1. Recursively scan formula:
   - Track: has_forall_second, has_unrestricted_forall_first,
            has_exists_second, has_forall_first_with_step
2. If ForallSecond found: Full
3. If ForallFirst with non-step body: Full
4. If ExistsSecond found (no ForallSecond): RestrictedExistential
5. If ForallFirst with step body (no set quantifiers): Restricted
6. If no set quantifiers at all: FirstOrder
```

**Complexity**: O(|formula|).

### Step Function Check

```
Input:  WeightedMsoFormula
Output: bool

A formula is a step function if:
  Constant(_)       -> true
  Atomic predicates -> true (Boolean)
  Or(a, b)          -> is_step_function(a) && is_step_function(b)
  And(a, b):
    If both constants: true
    If one constant, other Boolean: true
    If both non-constant: both must be Boolean
  Exists (body)     -> is_step_function(body)
  Forall (body)     -> false (nested products violate step form)
```

### Boolean Evaluation

```
Input:  WeightedMsoFormula, word: &[&str], assignment: sigma
Output: BooleanWeight

eval(formula, w, sigma):
  Constant("true") -> one; Constant("false") -> zero
  AtomicPos{label, var} -> one if w[sigma(var)] == label, else zero
  Order{x, y} -> one if sigma(x) <= sigma(y), else zero
  InSet{var, set_var} -> one if sigma(var) in sigma(set_var), else zero
  Or(a, b) -> eval(a) ⊕ eval(b)
  And(a, b) -> eval(a) ⊗ eval(b)
  ExistsFirst{var, body} -> ⊕_{i in 0..|w|} eval(body, sigma[var->i])
  ExistsSecond{var, body} -> ⊕_{I ⊆ 0..|w|} eval(body, sigma[var->I])
  ForallFirst{var, body} -> ⊗_{i in 0..|w|} eval(body, sigma[var->i])
```

**Complexity**: O(|formula| * |w|^(first-order vars) * 2^(|w| * second-order vars)).

### Free Variable Analysis

```
Input:  WeightedMsoFormula
Output: HashSet<String>

Collect variables from atomic predicates, then subtract bound variables
from enclosing quantifiers. A formula with no free variables is a sentence.
```

## Integration

- **Symbolic module** (`symbolic.rs`): The `DecidabilityTier` enum is shared. Symbolic guard analysis uses the same T1--T4 classification.
- **Pipeline** (`pipeline.rs`): `MsoAnalysis` reports formula classification, decidability tier, free variables, and sentence status.
- **Lint module**: MSO formulas serve as the specification language for lint rules -- each lint condition can be expressed as a weighted MSO sentence.

## Diagnostics

No dedicated lint codes. The `MsoAnalysis` report includes:
- `class`: Formula classification (FirstOrder / Restricted / RestrictedExistential / Full)
- `decidability`: Decidability tier (T1 / T2 / T3 / T4)
- `free_variables`: Set of free first-order variables
- `free_set_variables`: Set of free second-order variables
- `is_sentence`: Whether the formula has no free variables

## Examples

### Example 1: First-order formula classification

```rust
// "there exists a position with label 'a'"
let formula = WeightedMsoFormula::ExistsFirst {
    var: "x".into(),
    body: Box::new(WeightedMsoFormula::AtomicPos {
        label: "a".into(),
        var: "x".into(),
    }),
};

let class = classify_formula(&formula);
assert_eq!(class, MsoFormulaClass::FirstOrder); // no set quantifiers
```

### Example 2: Restricted MSO formula

```rust
// "for all positions, the label is 'a' or 'b'"
let formula = WeightedMsoFormula::ForallFirst {
    var: "x".into(),
    body: Box::new(WeightedMsoFormula::Or(
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "a".into(), var: "x".into(),
        }),
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "b".into(), var: "x".into(),
        }),
    )),
};

let class = classify_formula(&formula);
assert_eq!(class, MsoFormulaClass::Restricted);
// Body is a Boolean formula (step function) => restricted fragment
```

### Example 3: Full MSO (undecidable)

```rust
// "for all position sets X, ..."
let formula = WeightedMsoFormula::ForallSecond {
    var: "X".into(),
    body: Box::new(WeightedMsoFormula::Constant("true".into())),
};

let class = classify_formula(&formula);
assert_eq!(class, MsoFormulaClass::Full);
// Contains forall X => full MSO, generally undecidable
```

## Advanced Topics

**Edge cases**: The `Constant` variant stores semiring values as strings to support `Eq` and `Hash` without requiring the semiring type to implement those traits. Canonical values are `"true"`, `"false"`, `"0"`, `"1"`. Boolean evaluation of `ExistsSecond` is exponential in word length (2^n subsets) -- this is inherent in second-order quantification.

**Interaction with other modules**: The decidability classification connects to the symbolic automata module's `DecidabilityTier`. The Buchi-Elgot-Trakhtenbrot theorem connects restricted MSO to the weighted automata constructed by other modules (WFST, Buchi, etc.).

**Performance**: Classification and free-variable analysis are linear in formula size. Boolean evaluation is polynomial for first-order formulas (O(|w|^k) for k quantifiers) but exponential for second-order formulas. The restricted fragment check (`is_step_function`) is linear.

**Future extensions**: Compilation of restricted MSO formulas to weighted automata (the constructive direction of the Buchi-Elgot-Trakhtenbrot theorem), enabling formula-to-automaton synthesis.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `classify_formula(phi)` | `&WeightedMsoFormula` | `MsoFormulaClass` | O(\|phi\|) |
| `is_step_function(phi)` | `&WeightedMsoFormula` | `bool` | O(\|phi\|) |
| `is_boolean_formula(phi)` | `&WeightedMsoFormula` | `bool` | O(\|phi\|) |
| `free_variables(phi)` | `&WeightedMsoFormula` | `HashSet<String>` | O(\|phi\|) |
| `evaluate_formula_bool(...)` | formula + word + assignment | `BooleanWeight` | O(\|phi\| * \|w\|^k * 2^(n*m)) |
| `evaluate_sentence_bool(...)` | sentence + word | `BooleanWeight` | same as above |
| `close_existentially(phi)` | `&WeightedMsoFormula` | `WeightedMsoFormula` | O(\|phi\|) |
| `close_universally(phi)` | `&WeightedMsoFormula` | `WeightedMsoFormula` | O(\|phi\|) |

### Feature gate

`weighted-mso` (depends on `symbolic-automata`).

### Citations

- Droste, M. & Gastin, P. (2007). "Weighted automata and weighted logics." *Theoretical Computer Science*, 380(1--2), 69--86.
- Buchi, J.R. (1960). "Weak second-order arithmetic and finite automata." *Zeitschrift fur mathematische Logik und Grundlagen der Mathematik*, 6, 66--92.
- Elgot, C.C. (1961). "Decision problems of finite automata design and related arithmetics." *Trans. AMS*, 98, 21--51.
