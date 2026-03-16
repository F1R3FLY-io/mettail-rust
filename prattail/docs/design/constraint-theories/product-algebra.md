# Product Algebra -- Composing Independent Constraint Domains

**Feature gate:** (always-on, no feature gate required)
**Module:** `prattail/src/symbolic.rs` (within the symbolic automata module)
**Dependencies:** `symbolic-automata` (for `BooleanAlgebra` trait)

---

## Intuition: Composing Independent Domains

Real guard predicates often combine constraints from independent domains. A guard like `x > 0 /\ ch in [a-z]` mixes numeric arithmetic (Presburger) with character classification (CharClass). Neither algebra alone can handle the full guard, but the two domains are *independent*: the satisfiability of the numeric part does not depend on the character part, and vice versa.

`ProductAlgebra<A, B>` formalizes this independence. It takes two `BooleanAlgebra` implementations and produces a new `BooleanAlgebra` over the Cartesian product of their domains. Satisfiability factors per-disjunct: a product predicate `(phi_A, phi_B)` is satisfiable iff `phi_A` is satisfiable in `A` *and* `phi_B` is satisfiable in `B`.

---

## Mathematical Definition

Given Boolean algebras `A = (D_A, Psi_A, ...)` and `B = (D_B, Psi_B, ...)`:

```
ProductAlgebra<A, B> = (D_A x D_B, ProductPred<A,B>, ...)

where:
  Domain    = (A::Domain, B::Domain)
  Predicate = ProductPred<A, B>

  T(product)  = (T_A, T_B)
  bot(product) = bot_A OR bot_B

  SAT(Both(a, b)) = SAT_A(a) AND SAT_B(b)
  SAT(LeftOnly(a)) = SAT_A(a)
  SAT(RightOnly(b)) = SAT_B(b)
  SAT(And(p, q)) = exists disjunct in DNF(And(p,q)) such that SAT(disjunct)
  SAT(Or(p, q))  = SAT(p) OR SAT(q)
  SAT(Not(p))    = SAT(negate_pred(p))    -- push negation down

  WIT(p) = (WIT_A(proj_A(p)), WIT_B(proj_B(p)))
    for the first satisfiable DNF disjunct

  EVAL(p, (d_a, d_b)) = structural recursion:
    EVAL(Both(a,b), (d_a, d_b)) = EVAL_A(a, d_a) AND EVAL_B(b, d_b)
    EVAL(LeftOnly(a), (d_a, _)) = EVAL_A(a, d_a)
    EVAL(RightOnly(b), (_, d_b)) = EVAL_B(b, d_b)
    ...
```

---

## ProductPred Variants

```
ProductPred<A, B> ::= True                                -- always satisfied
                   |  False                               -- never satisfied
                   |  Both(A::Predicate, B::Predicate)    -- both must hold
                   |  LeftOnly(A::Predicate)               -- only left constrained
                   |  RightOnly(B::Predicate)              -- only right constrained
                   |  And(ProductPred, ProductPred)         -- conjunction
                   |  Or(ProductPred, ProductPred)          -- disjunction
                   |  Not(ProductPred)                      -- negation
```

The variants `Both`, `LeftOnly`, and `RightOnly` are the atomic forms. `And`, `Or`, and `Not` build Boolean combinations. `True` and `False` are the identity elements.

### Why Separate LeftOnly/RightOnly?

A guard may constrain only one domain. Without `LeftOnly`/`RightOnly`, the caller would need to write `Both(phi, true_pred())`, which obscures intent and adds unnecessary satisfiability checks for the unconstrained component. The specialized variants make this explicit and avoid the overhead.

### DNF-Based Satisfiability

The satisfiability check converts the product predicate to Disjunctive Normal Form (DNF), where each disjunct is a pair `(left_pred, right_pred)`. A disjunct is satisfiable iff *both* components are satisfiable (since the domains are independent). The overall predicate is satisfiable iff *any* disjunct is satisfiable:

```
to_dnf(True)         = [(true_A, true_B)]
to_dnf(False)        = []
to_dnf(Both(a, b))   = [(a, b)]
to_dnf(LeftOnly(a))  = [(a, true_B)]
to_dnf(RightOnly(b)) = [(true_A, b)]
to_dnf(And(p, q))    = { (and_A(l1, l2), and_B(r1, r2))
                          | (l1, r1) in dnf(p), (l2, r2) in dnf(q) }
to_dnf(Or(p, q))     = dnf(p) ++ dnf(q)
to_dnf(Not(p))       = to_dnf(negate_pred(p))

is_satisfiable(p) = any (l, r) in to_dnf(p) such that SAT_A(l) AND SAT_B(r)
```

### Negation Push-Down

Negation is handled by pushing it down to atomic predicates using De Morgan's laws:

```
negate(True)         = False
negate(False)        = True
negate(Both(a, b))   = Or(LeftOnly(not_A(a)), RightOnly(not_B(b)))
negate(LeftOnly(a))  = LeftOnly(not_A(a))
negate(RightOnly(b)) = RightOnly(not_B(b))
negate(And(p, q))    = Or(negate(p), negate(q))
negate(Or(p, q))     = And(negate(p), negate(q))
negate(Not(p))       = p
```

The negation of `Both(a, b)` uses De Morgan over independent domains: `NOT(a AND b) = NOT(a) OR NOT(b)`, where each negation stays within its own algebra.

---

## Use Cases

### ProductAlgebra<PresburgerAlgebra, CharClassAlgebra>

Combine numeric constraints with character class constraints:

```rust
let left = PresburgerAlgebra::new(8);
let right = CharClassAlgebra::new();
let product = ProductAlgebra::new(left, right);

// Guard: x in [65, 91) AND ch in [a-z]
let pred = ProductPred::Both(
    PresburgerPred::And(
        Box::new(PresburgerPred::geq(vec![(0, 1)], 65)),
        Box::new(PresburgerPred::leq(vec![(0, 1)], 90)),
    ),
    CharClassPred::Range('a', 'z'),
);

assert!(product.is_satisfiable(&pred));
```

### ProductAlgebra<IntervalAlgebra, IntervalAlgebra>

Two independent numeric ranges (e.g., x-coordinate and y-coordinate):

```rust
let x_axis = IntervalAlgebra::new(0, 1000);
let y_axis = IntervalAlgebra::new(0, 1000);
let product = ProductAlgebra::new(x_axis, y_axis);

// Point in rectangle [10, 100) x [200, 500)
let rect = ProductPred::Both(
    IntervalPred::Range(10, 100),
    IntervalPred::Range(200, 500),
);

let witness = product.witness(&rect).expect("rectangle is non-empty");
assert!(witness.0 >= 10 && witness.0 < 100);
assert!(witness.1 >= 200 && witness.1 < 500);
```

### Integration with SymbolicAutomaton

`ProductAlgebra<A, B>` implements `BooleanAlgebra`, so it can be used directly with `SymbolicAutomaton`:

```rust
let product = ProductAlgebra::new(
    IntervalAlgebra::new(0, 100),
    IntervalAlgebra::new(0, 100),
);

let mut sfa = SymbolicAutomaton::new(product.clone());
let q0 = sfa.add_state(false, Some("start".into()));
let q1 = sfa.add_state(true, Some("accept".into()));
sfa.set_initial(q0);
sfa.add_transition(q0, q1,
    ProductPred::Both(IntervalPred::Range(10, 20), IntervalPred::Range(30, 40)));

assert!(!sfa.is_empty());
assert!(sfa.accepts(&[ProductDomain(15, 35)]));
assert!(!sfa.accepts(&[ProductDomain(5, 35)]));
```

All SFA operations -- emptiness, intersection, complement, determinization, equivalence -- work automatically with product predicates.

### Nesting Products

`ProductAlgebra` composes arbitrarily: `ProductAlgebra<ProductAlgebra<A, B>, C>` creates a three-domain product. The domain is `((A::Domain, B::Domain), C::Domain)`. This enables combining any number of independent constraint domains without modification to the `ProductAlgebra` implementation.

---

## Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| `is_satisfiable` | O(\|DNF\| * (SAT_A + SAT_B)) | DNF size can be exponential in nesting |
| `witness` | O(\|DNF\| * (WIT_A + WIT_B)) | First satisfiable disjunct |
| `evaluate` | O(\|pred\|) | Structural recursion |
| `and`/`or`/`not` | O(1) | Structural (build AST node) |
| `to_dnf` | O(2^depth) worst case | DNF expansion of nested And/Or |

For typical guard predicates (shallow nesting, 2--3 conjuncts), DNF expansion is small and the cost is dominated by the component algebras' satisfiability checks.

---

## Citations

- D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and transducers." *CAV 2017*. (Product construction for SFA intersection generalizes to product algebras.)
