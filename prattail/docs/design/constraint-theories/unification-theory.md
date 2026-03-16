# Unification Theory -- Structural Pattern Matching

**Feature gate:** `unification`
**Module:** `prattail/src/unification.rs`
**Dependencies:** `logict` (for `ConstraintTheory` trait)

---

## Intuition: Structural Unification for MeTTa/Rholang

Pattern matching is fundamental to both MeTTa and Rholang. When a Rholang `for` receive binds `@{x!(y)}`, the runtime must decompose the incoming name into its structural components and extract bindings for `x` and `y`. When MeTTa evaluates `(= (foo $x) (foo (bar 42)))`, it must determine that `$x` should be bound to `(bar 42)`.

Both operations are instances of *first-order syntactic unification*: given two terms (possibly containing variables), find a substitution that makes them identical. The algorithm is deterministic, terminates in near-linear time, and either produces a most general unifier (MGU) or reports failure with a precise reason (constructor clash, arity mismatch, or occurs-check violation).

The unification theory integrates this into PraTTaIL's constraint framework as a `ConstraintTheory`, enabling symbolic automata to reason about pattern compatibility at compile time: are two patterns guaranteed to never match the same term? Does one pattern subsume another?

---

## Term Language

Terms form a free algebra over three constructors:

```
TermExpr ::= Var(usize)                          -- variable (by index)
          |  Const(String)                        -- named constant
          |  App { head: String, args: Vec<TermExpr> }  -- function application
```

| Construct | Example | Meaning |
|-----------|---------|---------|
| `Var(0)` | x0 | The 0th variable |
| `Const("a")` | a | A constant symbol |
| `App { head: "f", args: [Var(0), Const("a")] }` | f(x0, a) | Application of `f` to two arguments |

Variables are identified by index (not name) for efficient lookup and substitution. The `TermSignature` type optionally constrains constructor arities for well-formedness checking.

---

## Martelli-Montanari Algorithm

The unification algorithm of Martelli and Montanari (1982) is the standard reference implementation. It maintains:

1. A **work stack** of pending equations `s ≡ t`
2. A **substitution** sigma mapping variable indices to terms

At each step, pop an equation from the work stack, apply the current substitution to both sides, then dispatch on structure:

### Pseudocode

```
function unify(equations, sigma):
    work_stack = equations
    while work_stack is not empty:
        (s, t) = pop(work_stack)
        s' = apply(sigma, s)
        t' = apply(sigma, t)
        match (s', t'):
            case (Var(x), Var(x)):      -- same variable
                continue                 -- trivial identity
            case (Var(x), t'):
                if occurs(x, t'):        -- occurs check
                    return FAILURE("infinite term: x occurs in t'")
                sigma[x] = t'
                update_all_bindings(sigma, {x -> t'})
            case (s', Var(y)):           -- orient: variable on right
                if occurs(y, s'):
                    return FAILURE("infinite term: y occurs in s'")
                sigma[y] = s'
                update_all_bindings(sigma, {y -> s'})
            case (App(f, args_s), App(f, args_t)):  -- same head
                if |args_s| != |args_t|:
                    return FAILURE("arity mismatch")
                for (a_s, a_t) in zip(args_s, args_t):
                    push(work_stack, (a_s, a_t))     -- decompose
            case (App(f, _), App(g, _)) where f != g:
                return FAILURE("constructor clash: f != g")
            case (Const(a), Const(a)):   -- same constant
                continue
            case (Const(a), Const(b)) where a != b:
                return FAILURE("constant clash: a != b")
            case (Const(_), App(_, _)) or (App(_, _), Const(_)):
                return FAILURE("kind clash")
    return sigma
```

### Step-by-Step Trace

Unify `f(x0, a) ≡ f(b, x1)`:

```
Work stack:  [(f(x0, a), f(b, x1))]
Sigma:       {}

Step 1: Pop (f(x0, a), f(b, x1))
  Apply sigma: no change
  Match: App("f", [x0, a]) ≡ App("f", [b, x1])
  Same head "f", same arity 2 → decompose
  Push: [(x0, b), (a, x1)]

Step 2: Pop (x0, b)
  Apply sigma: no change
  Match: Var(0) ≡ Const("b")
  Occurs check: 0 not in Const("b") → OK
  Bind: sigma[0] = Const("b")
  Update existing bindings: none
  Sigma: {x0 -> b}

Step 3: Pop (a, x1)
  Apply sigma: a (unchanged), x1 (unbound)
  Match: Const("a") ≡ Var(1)
  Orient: Var(1) ≡ Const("a")
  Occurs check: 1 not in Const("a") → OK
  Bind: sigma[1] = Const("a")
  Sigma: {x0 -> b, x1 -> a}

Work stack empty → SUCCESS
Result: {x0 -> b, x1 -> a}
```

### Occurs Check

The occurs check prevents circular bindings. Without it, unifying `x ≡ f(x)` would produce the substitution `{x -> f(x)}`, which represents the infinite term `f(f(f(f(...))))`. The occurs check detects that variable `x` appears in `f(x)` and rejects the equation.

```
function occurs(var, term):
    work_stack = [term]
    while work_stack is not empty:
        current = pop(work_stack)
        match current:
            case Var(v):
                if v == var: return true
            case Const(_):
                pass
            case App(_, args):
                for arg in args:
                    push(work_stack, arg)
    return false
```

Both `occurs` and the main unification loop use explicit work stacks rather than recursion, consistent with PraTTaIL's stack-safe design philosophy.

---

## ConstraintTheory Integration

### Constraint and Store Types

```
Constraint = UnificationEquation { lhs: TermExpr, rhs: TermExpr }
Assignment = Substitution { bindings: HashMap<usize, TermExpr> }
Store      = UnificationStore {
               substitution: HashMap<usize, TermExpr>,
               pending: Vec<UnificationEquation>
             }
```

### propagate: Martelli-Montanari

`propagate(store, equation)` collects all pending equations plus the new one, then runs the full Martelli-Montanari algorithm starting from the current substitution:

```
propagate(store, eq) =
    all_equations = store.pending ++ [eq]
    unify(store.substitution, all_equations)
      → Some(new_store) if unification succeeds
      → None if clash, arity mismatch, or occurs-check failure
```

The algorithm is **deterministic**: for any set of equations, either there is a unique most general unifier or the system is unsatisfiable. No search is needed.

### label: empty (decidable)

Because syntactic unification is decidable and deterministic, `label()` returns `LogicStream::empty()`. Propagation alone determines satisfiability.

```rust
fn label(&self, _store: &UnificationStore) -> LogicStream<UnificationEquation> {
    LogicStream::empty()
}
```

### witness: Extract Substitution

`witness(store)` returns the current substitution as a `Substitution` if the store is solved (no pending equations remain):

```rust
fn witness(&self, store: &UnificationStore) -> Option<Substitution> {
    if store.is_solved() {
        Some(Substitution::from_bindings(store.substitution().clone()))
    } else {
        None
    }
}
```

### evaluate: Check Equation Against Assignment

```rust
fn evaluate(&self, eq: &UnificationEquation, subst: &Substitution) -> bool {
    let lhs = subst.apply(&eq.lhs);
    let rhs = subst.apply(&eq.rhs);
    lhs == rhs
}
```

---

## Subsumption

**Definition.** A substitution sigma *subsumes* a substitution tau (written sigma <= tau) if there exists a substitution rho such that tau = rho compose sigma. Equivalently, sigma is more general than tau.

In terms of patterns: pattern P1 subsumes pattern P2 if every term matching P2 also matches P1. This is checked by attempting to unify P1 against P2 and verifying that the resulting substitution only binds P1's variables (P2's variables are unconstrained).

Subsumption connects to `BooleanAlgebra` implication: `implies(phi_P1, phi_P2)` holds iff pattern P1 subsumes pattern P2.

```
Subsumption example:
  P1 = f(x, y)      -- matches any f with two arguments
  P2 = f(a, y)      -- matches f with first argument = a

  Unify P1 against P2: {x -> a}
  Only P1's variable x is bound → P1 subsumes P2
  (everything matching P2 also matches P1, but not vice versa)
```

---

## MeTTa Examples

### Pattern Matching

MeTTa patterns use variables (prefixed with `$`) and constructors:

```metta
(= (foo $x) result)          -- pattern: foo applied to any argument
(= (foo (bar 42)) result)    -- concrete: foo applied to (bar 42)
```

In unification terms:

```
Pattern:  App("foo", [Var(0)])
Concrete: App("foo", [App("bar", [Const("42")])])

Unification: {x0 -> App("bar", [Const("42")])}
```

### Polymorphic Type Solving

MeTTa type constraints can be expressed as unification problems:

```metta
(: identity (-> $a $a))       -- identity has type a -> a
(identity True)                -- applying to True (: True Bool)
```

Type inference unifies `$a` with `Bool`:

```
Equation: Var(a) ≡ Const("Bool")
Result:   {a -> Bool}
Inferred: identity : Bool -> Bool (for this application)
```

### Failure Case: Constructor Clash

```metta
(= (cons $x $xs) (nil))
```

```
App("cons", [Var(0), Var(1)]) ≡ App("nil", [])
Constructor clash: "cons" != "nil" → FAILURE
```

This means a `cons` pattern and a `nil` pattern can never match the same term -- useful for exhaustiveness checking.

---

## Rholang Examples

### Quoted Process Matching

Rholang receives names (quoted processes) on channels. Pattern matching decomposes the quoted process:

```rholang
for (@{x!(y)} <- ch) { ... }
```

The guard `@{x!(y)}` is the Name pattern `NQuote(POutput(NVar(x), PVar(y)))`. As a term:

```
App("NQuote", [
    App("POutput", [
        Var(0),        -- x (Name)
        Var(1),        -- y (Proc)
    ])
])
```

Receiving `@{alice!(compute(42))}` produces:

```
Concrete: App("NQuote", [
    App("POutput", [
        Const("alice"),
        App("compute", [Const("42")])
    ])
])

Unification result:
  {x0 -> Const("alice"), x1 -> App("compute", [Const("42")])}
```

### Comm Rule Unification

The rho-calculus comm rule matches an output `x!(P)` with an input `for(@Q <- x) { R }`. The pattern matching determines whether the output's payload matches the input's guard:

```
Output payload:  App("Pair", [Const("3"), Const("5")])
Input guard:     App("Pair", [Var(0), Var(1)])

Unification: {x0 -> Const("3"), x1 -> Const("5")}
→ comm event fires, continuation R[3/x0, 5/x1] proceeds
```

### Failure: Kind Clash

```rholang
for (@{x!(y)} <- ch) { ... }
-- receiving @(Nil) on ch
```

```
Pattern:  App("POutput", [Var(0), Var(1)])
Concrete: Const("Nil")

Kind clash: App(...) ≡ Const(...) → FAILURE
→ comm event does NOT fire (pattern doesn't match)
```

---

## Algorithmic Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Unification (basic) | O(n * alpha(n)) | With path compression; n = total term size |
| Unification (this impl) | O(n * d) | d = max nesting depth; explicit substitution |
| Occurs check | O(n) | Single pass over term |
| Substitution application | O(n) | Single pass with transitive following |
| Subsumption check | O(n) | One unification attempt |

The implementation uses explicit substitution application (rather than union-find with path compression) for clarity. For the term sizes encountered in grammar-level analysis, this is more than sufficient.

---

## Citations

- Robinson, J. A. (1965). "A Machine-Oriented Logic Based on the Resolution Principle." *Journal of the ACM*, 12(1), 23--41. DOI: [10.1145/321250.321253](https://doi.org/10.1145/321250.321253)
- Martelli, A. & Montanari, U. (1982). "An Efficient Unification Algorithm." *ACM Transactions on Programming Languages and Systems*, 4(2), 258--282. DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)
- Baader, F. & Snyder, W. (2001). "Unification Theory." In *Handbook of Automated Reasoning*, vol. 1, ch. 8, pp. 445--533. Elsevier.
