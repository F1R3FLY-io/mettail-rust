# Kleene Algebra with Tests (KAT)

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | `kat`                                  |
| Source file    | `prattail/src/kat.rs` (~920 lines)     |
| Pipeline phase | Post-WPDS analysis                     |
| Lint codes     | K01 (Hoare violation), K02 (KAT non-equivalence) |

## Rationale

Kleene Algebra with Tests extends Kleene algebra with a Boolean subalgebra of "tests" (predicates). This combination yields a decidable equational theory that subsumes propositional Hoare logic, making KAT ideal for automated verification of parse control flow. In PraTTaIL, sequential composition maps to rule chaining, alternation to dispatch, iteration to Kleene star (recursive categories), and Boolean tests to token predicates (e.g., "current token is '('" or "in recovery mode"). KAT equivalence checking verifies that grammar transformations preserve parse behavior, and Hoare triples verify pre/post-conditions of parse functions.

## Theoretical Foundations

**Definition (Boolean Test).** A Boolean test `b` belongs to the subalgebra `B` of the Kleene algebra. Tests are closed under negation, conjunction, and disjunction:

    B ::= True | False | Atom(name) | Not(b) | And(b, b) | Or(b, b)

**Definition (KAT Expression).** A KAT expression `e` combines Kleene algebra operators with Boolean tests:

    e ::= 0 | 1 | Test(b) | Action(a) | Seq(e, e) | Alt(e, e) | Star(e)

**Definition (Hoare Triple in KAT).** The Hoare triple `{b} p {c}` is valid iff `b . p . not(c) = 0` in the free KAT (Kozen, 1997). This reduces Hoare logic verification to KAT equivalence checking.

**Theorem (Completeness, Kozen 1997).** The equational theory of KAT is complete for the language model. That is, `e1 = e2` holds in all KAT models iff it holds in the language (guarded-string) model.

**Theorem (Decidability, Kozen & Smith 1996).** KAT equivalence is decidable in PSPACE via automata-based methods. Symbolic bisimulation using Brzozowski derivatives provides a practical decision procedure.

**Definition (Brzozowski Derivative).** The derivative of a KAT expression `e` with respect to action `a` under valuation `v` is:

- `D_a(0) = 0`, `D_a(1) = 0`, `D_a(Test(b)) = 0`
- `D_a(Action(a)) = 1`, `D_a(Action(b)) = 0` when `a != b`
- `D_a(Seq(p, q)) = Alt(Seq(D_a(p), q), if nullable(p) then D_a(q) else 0)`
- `D_a(Alt(p, q)) = Alt(D_a(p), D_a(q))`
- `D_a(Star(p)) = Seq(D_a(p), Star(p))`

**Definition (Nullability).** An expression `e` is nullable under valuation `v` iff the empty string is in the language of `e` under `v`:

- `nullable(Zero) = false`, `nullable(One) = true`, `nullable(Star(_)) = true`
- `nullable(Test(b)) = eval(b, v)`, `nullable(Action(_)) = false`
- `nullable(Seq(a, b)) = nullable(a) AND nullable(b)`
- `nullable(Alt(a, b)) = nullable(a) OR nullable(b)`

### References

1. Kozen, D. (1997). "Kleene algebra with tests." *ACM Transactions on Programming Languages and Systems*, 19(3).
2. Kozen, D. & Smith, F. (1996). "Kleene algebra with tests: completeness and decidability." *CSL*.
3. Pous, D. (2015). "Symbolic algorithms for language equivalence and Kleene algebra with tests." *POPL*.
4. Kozen, D. (2000). "On Hoare logic and Kleene algebra with tests." *ACM Transactions on Computational Logic*, 1(1).

## Algorithm Pseudocode

### 1. Symbolic Bisimulation Equivalence Check

```
FUNCTION check_equivalence_bounded(a, b, depth_limit):
    atoms := collect_atoms(a) UNION collect_atoms(b)
    actions := collect_actions(a) UNION collect_actions(b)
    valuations := all 2^|atoms| Boolean valuations

    worklist := [(a, b)]
    visited := {(a, b)}
    iterations := 0

    WHILE worklist is not empty AND iterations < depth_limit:
        (e1, e2) := dequeue(worklist)
        iterations := iterations + 1

        FOR EACH valuation v in valuations:
            // Check nullability agreement
            IF nullable(e1, v) != nullable(e2, v):
                RETURN false

            // Compute derivatives for each action
            FOR EACH action act in actions:
                d1 := simplify(derivative(e1, act, v))
                d2 := simplify(derivative(e2, act, v))
                IF d1 != d2 AND (d1, d2) not in visited:
                    visited.insert((d1, d2))
                    worklist.enqueue((d1, d2))

    RETURN true   // No counterexample found within depth limit
```

### 2. Hoare Triple Verification

```
FUNCTION verify_hoare_triple(pre, program, post):
    // {pre} program {post} holds iff pre . program . not(post) = 0
    condition := Seq(Test(pre), Seq(program, Test(Not(post))))
    RETURN check_equivalence(condition, Zero)
```

### 3. Algebraic Simplification

```
FUNCTION simplify(expr):
    CASE expr OF
        Seq(Zero, _) | Seq(_, Zero):    RETURN Zero
        Seq(One, x)  | Seq(x, One):     RETURN simplify(x)
        Alt(Zero, x) | Alt(x, Zero):    RETURN simplify(x)
        Alt(x, x):                       RETURN simplify(x)  // idempotence
        Star(Zero)   | Star(One):        RETURN One
        Star(Star(x)):                   RETURN Star(simplify(x))
        Test(True):                      RETURN One
        Test(False):                     RETURN Zero
        _:                               RETURN expr with subterms simplified
```

## Complexity Analysis

| Operation                    | Time              | Space            |
|------------------------------|-------------------|------------------|
| `check_equivalence_bounded`  | O(D . 2^n . A)   | O(D . 2^n)      |
| `verify_hoare_triple`        | O(D . 2^n . A)   | O(D . 2^n)      |
| `simplify`                   | O(|e|)            | O(|e|)           |
| `nullable`                   | O(|e|)            | O(1)             |
| `derivative`                 | O(|e|)            | O(|e|)           |
| `collect_atoms`              | O(|e|)            | O(n)             |
| `eval_test`                  | O(|b|)            | O(1)             |

Where D = depth limit, n = number of atomic tests, A = number of actions, |e| = expression size, |b| = test size.

## Architecture Diagram

```
  ┌──────────────────────────────────────────────────────────────┐
  │                    KAT Verification Pipeline                  │
  │                                                              │
  │  WPDS Call Graph                                             │
  │       │                                                      │
  │       ▼                                                      │
  │  check_from_bundle()                                         │
  │       │                                                      │
  │       ├──────────────────────────┐                           │
  │       │                          │                           │
  │       ▼                          ▼                           │
  │  Hoare Triples              Equivalence Checks               │
  │  (per call edge)            (per mutual-recursion SCC)       │
  │       │                          │                           │
  │       ▼                          ▼                           │
  │  verify_hoare_triple()      check_equivalence()              │
  │       │                          │                           │
  │       ▼                          ▼                           │
  │  KatExpr::hoare_condition   Symbolic Bisimulation            │
  │       │                    (Brzozowski derivatives)          │
  │       ▼                          │                           │
  │  check_equivalence()             │                           │
  │  (condition = Zero?)             │                           │
  │       │                          │                           │
  │       └──────────┬───────────────┘                           │
  │                  ▼                                           │
  │            KatCheck                                          │
  │    (hoare_results, equivalence_results)                      │
  └──────────────────────────────────────────────────────────────┘
```

## Symbolic Bisimulation State Space

```
  Worklist-based exploration of derivative pairs:

  ┌─────────┐                    ┌─────────┐
  │ (a, b)  │ ── nullable(v)? ──│ PASS /  │
  │ initial │    for all v       │ FAIL    │
  └────┬────┘                    └─────────┘
       │
       │ compute D_act(a, v), D_act(b, v)
       │ for each action, each valuation
       ▼
  ┌─────────────────────────────────────────┐
  │ Worklist: { (d1, d2), (d3, d4), ... }  │
  │ Visited:  { (a, b), (d1, d2), ... }    │
  └─────────────────────┬───────────────────┘
                        │
                        │ iterations < depth_limit?
                        ▼
               ┌────────────────┐
               │ true (equiv)   │ worklist exhausted
               │ false (differ) │ nullability mismatch found
               └────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`check_from_bundle(wpds_analysis, all_syntax)`** -- Extracts program flow from the WPDS call graph and verifies Hoare triples. Each directed call edge becomes a Hoare triple `{caller_reachable} call_action {callee_reachable}`. Mutual-recursion SCCs are checked for Kleene star idempotence (`p* ; p* = p*`). Categories with syntax rules generate parse Hoare triples `{has_syntax} parse {category_parsed}`.

### Lint Emission

- **K01 (Hoare violation)**: Emitted when a Hoare triple `{b} p {c}` fails -- the parse control flow does not preserve the specified pre/post-condition.
- **K02 (KAT non-equivalence)**: Emitted when two KAT expressions that should be equivalent are not -- a grammar transformation has changed parse behavior.

## Rust Implementation Notes

| Type            | Role                                                          |
|-----------------|---------------------------------------------------------------|
| `BooleanTest`   | Boolean test subalgebra: True, False, Atom, Not, And, Or     |
| `KatExpr`       | KAT expression: Zero, One, Test, Action, Seq, Alt, Star      |
| `HoareTriple`   | Hoare triple: precondition, program, postcondition, name      |
| `KatCheck`      | Pipeline result: hoare_results, equivalence_results           |

## Worked Example

Verify that a recursive descent parser for `Expr` preserves reachability.

**Step 1: Build KAT expressions from WPDS call graph.**

```
Call graph: Expr -> Term, Term -> Factor
```

KAT expressions:
```
{Expr_reachable} call_Expr_Term {Term_reachable}
{Term_reachable} call_Term_Factor {Factor_reachable}
```

**Step 2: Verify Hoare triples.**

For `{Expr_reachable} call_Expr_Term {Term_reachable}`:
```
condition = [Expr_reachable] ; call_Expr_Term ; [~Term_reachable]
```

The symbolic bisimulation explores 2^2 = 4 valuations (2 atoms: `Expr_reachable`, `Term_reachable`). Under `Expr_reachable = true, Term_reachable = true`: the condition is nullable iff `[true] ; call_Expr_Term ; [false]` accepts the empty string. Since `call_Expr_Term` is an action (not nullable), the sequential composition is not nullable. The condition equals Zero -- the Hoare triple holds.

**Step 3: Check mutual-recursion SCC idempotence.**

If `Expr -> Term -> Expr` forms a cycle, the SCC check verifies:
```
(call_Expr_Term ; call_Term_Expr)* ; (call_Expr_Term ; call_Term_Expr)*
  =? (call_Expr_Term ; call_Term_Expr)*
```

By the Kleene algebra identity `p* ; p* = p*`, this always holds.

**Step 4: Output.**

```
KatCheck {
  hoare_results: [("{Expr_reachable} call_Expr_Term {Term_reachable}", true), ...],
  equivalence_results: [("(cycle)*", "(cycle)* ; (cycle)*", true)]
}
```

## References

1. Kozen, D. (1997). "Kleene algebra with tests." *ACM TOPLAS*, 19(3).
2. Kozen, D. & Smith, F. (1996). "Kleene algebra with tests: completeness and decidability." *CSL*.
3. Pous, D. (2015). "Symbolic algorithms for language equivalence and Kleene algebra with tests." *POPL*.
4. Kozen, D. (2000). "On Hoare logic and Kleene algebra with tests." *ACM TOCL*, 1(1).
5. Brzozowski, J.A. (1964). "Derivatives of regular expressions." *JACM*, 11(4).
