# Martelli-Montanari Unification

PraTTaIL implements first-order syntactic unification as a `ConstraintTheory` plugin, using the Martelli-Montanari algorithm (1982). This provides bidirectional pattern matching with occurs check for type inference, polymorphic instantiation, and custom logic rules.

**Prerequisites:** [Pattern Matching Overview](overview.md)

---

## 1. TermExpr: The Free Algebra

Terms are represented by the `TermExpr` enum (`unification.rs:66-78`):

```rust
pub enum TermExpr {
    Var(usize),                          // Variable (identified by index)
    Const(String),                       // Constant (identified by name)
    App { head: String, args: Vec<TermExpr> },  // f(t₁, ..., tₙ)
}
```

| Variant | Example | Display |
|---------|---------|---------|
| `Var(0)` | Variable x₀ | `x0` |
| `Const("a")` | Constant a | `a` |
| `App { head: "f", args: [Var(0), Const("a")] }` | f(x₀, a) | `f(x0, a)` |

Variables are identified by `usize` index (not names), providing an implicit form of De Bruijn numbering that avoids alpha-equivalence issues.

---

## 2. The Unification Problem

Given two terms `s` and `t`, find a substitution σ such that:

```text
σ(s) = σ(t)
```

**Matching** (one-directional) is the special case where `t` is ground (no variables):

```text
find σ such that σ(pattern) = ground_term
```

**Unification** (bidirectional) is strictly more general:

```text
Unify:  f(x₀, a) ≡ f(b, x₁)
Result: σ = {x₀ ↦ b, x₁ ↦ a}
Check:  σ(f(x₀, a)) = f(b, a) = σ(f(b, x₁))  ✓
```

---

## 3. The Martelli-Montanari Algorithm

The algorithm maintains a work stack of pending equations and a substitution σ. At each step, it pops an equation, applies σ to both sides, then dispatches on the structure:

| Case | LHS | RHS | Action |
|------|-----|-----|--------|
| Trivial identity | `Var(x)` | `Var(x)` | Skip (x = x is trivially true) |
| Variable binding | `Var(x)` | `t` | Occurs check; if passes, bind x ↦ t in σ |
| Variable binding | `t` | `Var(x)` | Symmetric: bind x ↦ t |
| Decomposition | `App(f, [a₁,...])` | `App(f, [b₁,...])` | Push {a₁≡b₁, ..., aₙ≡bₙ} |
| Constructor clash | `App(f, _)` | `App(g, _)` | **Fail** (f ≠ g) |
| Arity mismatch | `App(f, [a₁,...,aₘ])` | `App(f, [b₁,...,bₙ])` | **Fail** (m ≠ n) |
| Constant identity | `Const(a)` | `Const(a)` | Skip |
| Constant clash | `Const(a)` | `Const(b)` | **Fail** (a ≠ b) |
| Kind clash | `Const(_)` | `App(_, _)` | **Fail** |

### Implementation

The `unify()` method (`unification.rs:460-499`) implements this as an iterative work-stack loop:

```rust
fn unify(
    &self,
    mut substitution: HashMap<usize, TermExpr>,
    initial_equations: &[UnificationEquation],
) -> Option<HashMap<usize, TermExpr>> {
    let mut work_stack: Vec<(TermExpr, TermExpr)> = /* ... */;

    while let Some((lhs, rhs)) = work_stack.pop() {
        let s = lhs.apply_substitution(&substitution);
        let t = rhs.apply_substitution(&substitution);

        match (&s, &t) {
            (Var(x), Var(y)) if x == y => continue,
            (Var(x), _) => {
                if TermExpr::occurs_in(*x, &t) { return None; }
                // Apply new binding to all existing bindings (solved form)
                // ...
                substitution.insert(*x, t);
            }
            (_, Var(x)) => { /* symmetric */ }
            (App { head: f, args: as_ }, App { head: g, args: bs })
                if f == g && as_.len() == bs.len() => {
                for (a, b) in as_.iter().zip(bs.iter()) {
                    work_stack.push((a.clone(), b.clone()));
                }
            }
            _ => return None,  // clash
        }
    }
    Some(substitution)
}
```

---

## 4. Occurs Check

The occurs check prevents circular bindings like `x₀ ↦ f(x₀)`, which would create an infinite term.

`TermExpr::occurs_in()` (`unification.rs:144-162`) uses an explicit work stack:

```rust
pub fn occurs_in(var: usize, term: &TermExpr) -> bool {
    let mut work_stack: Vec<&TermExpr> = vec![term];
    while let Some(current) = work_stack.pop() {
        match current {
            TermExpr::Var(idx) if *idx == var => return true,
            TermExpr::App { args, .. } => work_stack.extend(args),
            _ => {}
        }
    }
    false
}
```

Without the occurs check, the algorithm would loop infinitely or produce unsound results. The check adds O(|t|) per variable binding step but is essential for correctness.

---

## 5. Supporting Types

### UnificationEquation

```rust
pub struct UnificationEquation {
    pub lhs: TermExpr,
    pub rhs: TermExpr,
}
```

### Substitution

```rust
pub struct Substitution {
    pub bindings: HashMap<usize, TermExpr>,
}
```

Provides `apply()` (apply to a term), `domain()` (bound variables), and display formatting (`{x0 ↦ b, x1 ↦ a}`).

### UnificationStore

```rust
pub struct UnificationStore {
    substitution: HashMap<usize, TermExpr>,
    pending: Vec<UnificationEquation>,
}
```

The constraint store for the `ConstraintTheory` implementation. Maintains both the current substitution and pending equations awaiting decomposition.

### TermSignature

```rust
pub struct TermSignature {
    pub constructors: HashMap<String, usize>,  // name → arity
}
```

Optional metadata for well-formedness checking. Not enforced during unification (the algorithm works on arbitrary term structures).

---

## 6. ConstraintTheory Integration

`UnificationTheory` implements `ConstraintTheory` (`unification.rs:423-428`):

```rust
impl ConstraintTheory for UnificationTheory {
    type Constraint = UnificationEquation;
    type Assignment = Substitution;
    type Store = UnificationStore;

    fn propagate(&self, store: &Store, eq: &UnificationEquation) -> Option<Store>;
    fn label(&self, _store: &Store) -> LogicStream<UnificationEquation>;
    fn witness(&self, store: &Store) -> Option<Substitution>;
    fn evaluate(&self, eq: &UnificationEquation, assignment: &Substitution) -> bool;
}
```

Key properties:
- **`propagate`** runs the full Martelli-Montanari algorithm, returning `None` on failure
- **`label`** returns `LogicStream::empty()` — unification is decidable, so no search is needed
- **`witness`** extracts the solved substitution from a consistent store
- **`evaluate`** checks whether an assignment satisfies an equation

---

## 7. Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Unify n equations, max term depth d | O(n · d) | O(n · d) |
| Occurs check per binding | O(\|t\|) | O(\|t\|) |
| Apply substitution | O(\|σ\| · \|t\|) | O(\|t\|) |

The theoretical optimal complexity is O(n · α(n)) with union-find and path compression (where α is the inverse Ackermann function). The current implementation uses explicit substitution application for clarity, giving O(n · d) in practice — sufficient for PraTTaIL's typical term sizes.

---

## 8. Connection to the Paper

Peyton Jones & Graf acknowledge in Appendix B of "Triemaps that match" that **"triemaps that unify"** is an open problem. The paper's matching trie supports *one-directional* matching (pattern variables in keys, concrete term as query); full unification (variables in both key and query) requires a separate mechanism.

PraTTaIL makes this separation explicit:
- **Matching** (one-directional): PathMap trie + generated `match_pattern()` functions
- **Unification** (bidirectional): Martelli-Montanari as a `ConstraintTheory`

The two mechanisms complement each other: the trie quickly identifies *which* patterns match, and unification resolves *how* variables bind when both sides have unknowns.

---

## References

1. **Martelli, A. & Montanari, U.** (1982). "An Efficient Unification Algorithm." *ACM Transactions on Programming Languages and Systems* 4(2), 258-282.

2. **Robinson, J. A.** (1965). "A Machine-Oriented Logic Based on the Resolution Principle." *Journal of the ACM* 12(1), 23-41. — Original unification algorithm (exponential; Martelli-Montanari improves to near-linear).

3. **Baader, F. & Snyder, W.** (2001). "Unification Theory." In *Handbook of Automated Reasoning*, vol. 1, ch. 8, pp. 445-533. — Comprehensive survey of unification variants.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `prattail/src/unification.rs` | ~500 | TermExpr, UnificationTheory, Martelli-Montanari |
| `prattail/src/logict.rs` | 463-495 | `ConstraintTheory` trait definition |

---

**Next:** [De Bruijn Encoding](de-bruijn-encoding.md) — alpha-equivalence via canonical variable numbering.
