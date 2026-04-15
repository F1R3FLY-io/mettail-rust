# FreeWeight: The Free Semiring as Universal Construction

## What Is It?

The `FreeWeight` is a semiring whose carrier is a **symbolic expression tree** (`FreeExpr`). Rather than evaluating semiring operations immediately (as numeric semirings do), the free semiring builds an abstract syntax tree that records the algebraic structure of the computation. It is the **initial object** in the category of semirings: it satisfies the semiring laws and no others.

Located in `simulation/src/semiring/free.rs`.

## What Does It Do?

The free semiring:

1. **Preserves provenance**: each generator (named atom) represents a data source, and the expression tree records which sources contributed to a result and how they were combined.
2. **Defers evaluation**: the expression is not reduced to a number; it remains as a symbolic tree that can be inspected, simplified, or evaluated later.
3. **Enables symbolic computation**: algebraic simplification, common subexpression elimination, and structural analysis are possible on the expression tree.

## Why Was It Chosen?

### The Universal Property

The free semiring over a set of generators X, denoted ℕ[X], is the initial object in the category of semirings. This means:

**For any semiring S and any function f: X → S, there exists a unique semiring homomorphism h: ℕ[X] → S extending f.**

In other words, the free semiring is the "most general" semiring: it makes no assumptions about the generators beyond the semiring axioms. Any concrete semiring can be obtained by evaluating the free semiring's expressions under an appropriate interpretation.

### Symbolic Provenance

Green, Karvounarakis, and Tannen (2007) introduced provenance semirings for database queries, showing that the free semiring naturally tracks **why** a tuple appears in a query result. The expression tree records:

- Which input tuples contributed (generators)
- Whether they were combined via union (⊕) or join (⊗)
- The algebraic structure of the derivation

In the MeTTaIL context, this means we can track which rewrite rules contributed to a normal form and how they combined, providing a complete derivation audit trail.

### Relationship to ℕ[X]

The polynomial semiring ℕ[X] over indeterminates X is isomorphic to the free commutative semiring. The `FreeWeight` represents the **non-commutative** free semiring (since ⊗ is not assumed commutative), which is more general. Commutativity of ⊕ is enforced by the semiring axioms, but ⊗ preserves operand order.

## Mathematical Definition

### Carrier (FreeExpr)

```
FreeExpr ::= Zero                            // additive identity
           | One                             // multiplicative identity
           | Gen(name: String)               // generator (atomic weight)
           | Plus(FreeExpr, FreeExpr)        // a ⊕ b
           | Times(FreeExpr, FreeExpr)       // a ⊗ b
```

This is a binary tree with five node types.

### Operations

**Plus (⊕):**

```
a ⊕ b = Plus(a, b)     (if neither is Zero)
0̄ ⊕ b = b              (identity short-circuit)
a ⊕ 0̄ = a              (identity short-circuit)
```

**Times (⊗):**

```
a ⊗ b = Times(a, b)    (if neither is Zero or One)
0̄ ⊗ b = 0̄              (annihilation short-circuit)
a ⊗ 0̄ = 0̄              (annihilation short-circuit)
1̄ ⊗ b = b              (identity short-circuit)
a ⊗ 1̄ = a              (identity short-circuit)
```

**Zero (0̄) = FreeExpr::Zero**

**One (1̄) = FreeExpr::One**

The short-circuit rules prevent expression bloat by applying the simplest algebraic identities eagerly.

### SemiringRef (Not Semiring)

Because `FreeExpr` involves heap allocation (`Box<FreeExpr>`, `String`), it cannot implement `Copy`. Therefore, `FreeWeight` implements `SemiringRef` instead of `Semiring`:

```rust
impl SemiringRef for FreeWeight {
    fn zero_ref() -> Self { FreeWeight { expr: FreeExpr::Zero } }
    fn one_ref() -> Self { FreeWeight { expr: FreeExpr::One } }
    fn plus_ref(&self, other: &Self) -> Self { /* ... */ }
    fn times_ref(&self, other: &Self) -> Self { /* ... */ }
    fn is_zero_ref(&self) -> bool { self.expr == FreeExpr::Zero }
    fn is_one_ref(&self) -> bool { self.expr == FreeExpr::One }
}
```

## Simplification

The `simplify()` method applies basic algebraic identities iteratively:

```
0̄ ⊕ a → a      (additive identity)
a ⊕ 0̄ → a      (additive identity)
1̄ ⊗ a → a      (multiplicative identity)
a ⊗ 1̄ → a      (multiplicative identity)
0̄ ⊗ a → 0̄      (annihilation)
a ⊗ 0̄ → 0̄      (annihilation)
```

**Crucially, simplification does NOT apply:**
- Commutativity of ⊗ (a ⊗ b ≠ b ⊗ a in general)
- Associativity (expressions are not flattened)
- Distributivity (a ⊗ (b ⊕ c) is not expanded)

Applying these would quotient the free semiring, losing the ability to distinguish structurally different derivations.

### Trampoline-Based Simplification

The simplification algorithm uses an explicit work stack to avoid stack overflow on deeply nested expressions:

```
PROCEDURE simplify(expr) → FreeExpr:
    stack ← []
    result_stack ← []
    current ← expr

    // Decompose: push frames for sub-expressions
    LOOP:
        MATCH current:
            Zero | One | Gen(_):
                result_stack.push(current)
                BREAK
            Plus(left, right):
                stack.push(SimplifyPlus(right))
                current ← left
            Times(left, right):
                stack.push(SimplifyTimes(right))
                current ← left

    // Assemble: pop frames, apply identities
    WHILE stack not empty:
        frame ← stack.pop()
        MATCH frame:
            SimplifyPlus(right):
                left ← result_stack.pop()
                stack.push(AssemblePlus(left))
                // process right sub-expression...
            AssemblePlus(left):
                right ← result_stack.pop()
                result ← MATCH (left, right):
                    (Zero, _) → right
                    (_, Zero) → left
                    _ → Plus(left, right)
                result_stack.push(result)
            // ... similarly for Times

    RETURN result_stack.pop()
```

This handles expressions nested 100+ levels deep without stack overflow.

## Introspection Methods

### Generator Counting

```rust
pub fn generator_count(&self) -> usize     // total generator occurrences
pub fn generators(&self) -> HashSet<String>  // unique generator names
```

**Example:**
```
expr = (a ⊕ (b ⊗ a))
generator_count = 3    // a appears twice, b once
generators = {"a", "b"}
```

### Evaluation

The `evaluate()` method interprets the expression tree in the standard real-number semiring (ℝ, +, ×, 0, 1):

```rust
pub fn evaluate(&self, env: &HashMap<String, f64>) -> f64
```

**Example:**
```
expr = (x ⊕ (y ⊗ z))
env = {x: 2.0, y: 3.0, z: 4.0}
evaluate(expr, env) = x + y * z = 2.0 + 3.0 * 4.0 = 14.0
```

The evaluator uses a trampoline (explicit stack) to avoid stack overflow:

```
PROCEDURE evaluate_trampoline(expr, env) → f64:
    stack ← [Eval(expr)]
    values ← []

    WHILE stack not empty:
        frame ← stack.pop()
        MATCH frame:
            Eval(Zero)     → values.push(0.0)
            Eval(One)      → values.push(1.0)
            Eval(Gen(name)) → values.push(env[name] or 0.0)
            Eval(Plus(l, r)):
                stack.push(ApplyPlus)
                stack.push(Eval(r))
                stack.push(Eval(l))
            Eval(Times(l, r)):
                stack.push(ApplyTimes)
                stack.push(Eval(r))
                stack.push(Eval(l))
            ApplyPlus:
                b ← values.pop(); a ← values.pop()
                values.push(a + b)
            ApplyTimes:
                b ← values.pop(); a ← values.pop()
                values.push(a * b)

    RETURN values.pop()
```

### Display

The `Display` implementation produces a human-readable infix representation:

```
Zero          → "0"
One           → "1"
Gen("x")      → "x"
Plus(a, b)    → "(a + b)"
Times(a, b)   → "(a * b)"
```

**Example:** `FreeExpr::Plus(Gen("x"), Times(Gen("y"), Gen("z")))` displays as `(x + (y * z))`.

## Use in Simulation

### Derivation Provenance

Label each rewrite rule with a generator: `FreeWeight::gen("Comm")`, `FreeWeight::gen("Exec")`, etc. After running the weighted automaton, the accumulated `FreeWeight` is an expression tree showing exactly which rules contributed to the result and how they combined.

### Debugging

When a simulation produces an unexpected result, the free weight expression reveals the algebraic derivation:

```
result = ((Comm * ParCong) + (Exec * NewCong * Comm))
```

This means there were two paths to the result: one via Comm followed by ParCong, another via Exec, NewCong, and Comm.

### Optimization

By simplifying the free weight expression, common sub-expressions can be identified and redundant computations eliminated. This is the algebraic analog of common subexpression elimination in compiler optimization.

## References

- Green, T.J., Karvounarakis, G., and Tannen, V. (2007). "Provenance Semirings." Proceedings of the 26th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS), pp. 31-40.
- Mohri, M. (2002). "Semiring Frameworks and Algorithms for Shortest-Distance Problems." Journal of Automata, Languages and Combinatorics, 7(3), pp. 321-350.
- Droste, M. and Kuich, W. (2009). "Semirings and Formal Power Series." In Handbook of Weighted Automata, Springer, pp. 3-28.
