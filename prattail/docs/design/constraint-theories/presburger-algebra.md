# Presburger Arithmetic -- Automata-Based Decision Procedure

**Feature gate:** `presburger` (core), `presburger` + `symbolic-automata` (PresburgerAlgebra)
**Module:** `prattail/src/presburger.rs`
**Dependencies:** `logict` (for `ConstraintTheory` trait)

---

## Intuition: Why Linear Integer Arithmetic for Guard Predicates

Many guard predicates in MeTTaIL and Rholang specifications involve relationships between integer-valued variables:

```rholang
for (@x : x > 0 /\ x < 1000 <- ch) { P }           -- single variable
for (@x, @y : x + y <= budget <- ch1, ch2) { P }     -- multi-variable
for (@n : 2*n + 1 <= max_depth <- ch) { P }           -- linear combination
```

Single-variable constraints can be handled by `IntervalAlgebra` -- ranges like `[1, 1000)` are its bread and butter. But the moment a guard involves *two or more* variables, `IntervalAlgebra` cannot help: it has no way to express `x + y <= 100` because its domain is a single `i64`, not a tuple.

Presburger arithmetic -- the first-order theory of the natural numbers with addition (but *not* multiplication) -- is the weakest theory that handles multi-variable linear constraints while remaining decidable. Buchi's 1960 theorem shows that the sets definable in Presburger arithmetic are *exactly* the regular languages over binary-encoded integers, giving us an elegant automata-based decision procedure that fits naturally into PraTTaIL's automata framework.

---

## Buchi's Theorem: Formal Statement

**Theorem (Buchi, 1960).** A subset S of Z^k is Presburger-definable if and only if the set of binary encodings of elements of S is a regular language over the alphabet {0, 1}^k.

### What This Means

Every Presburger formula -- any Boolean combination of linear inequalities over integer variables, with quantifiers -- corresponds to a finite automaton that reads the binary representations of the variables *bit by bit*, LSB-first, and accepts exactly those tuples satisfying the formula.

This gives us:
- **Satisfiability** = NFA language non-emptiness (reachability from initial to accepting states)
- **Validity** = NFA language universality (complement is empty)
- **Implication** = intersection with complement is empty
- **Witness** = shortest accepting path decoded to integers

### LSB-First Binary Encoding

Variables are encoded in binary, read one bit at a time starting from the **least significant bit**. For `k` variables, each "symbol" is a k-bit vector giving the current bit of each variable:

```
Variables: x0 = 5 (binary: 101), x1 = 3 (binary: 011)

Step 0 (LSB): symbol = (1, 1) -- x0 bit 0 = 1, x1 bit 0 = 1
Step 1:       symbol = (0, 1) -- x0 bit 1 = 0, x1 bit 1 = 1
Step 2:       symbol = (1, 0) -- x0 bit 2 = 1, x1 bit 2 = 0
```

The alphabet is Sigma = {0, 1}^k, where each symbol is a u32 bitmask with bit `i` representing variable x_i.

### Two's Complement for Negative Integers

For signed integers in [-2^(w-1), 2^(w-1)-1] where `w` is the bit width, the NFA reads `w` bits per variable in LSB-first order using standard two's complement representation. The sign bit (bit `w-1`) extends the value negatively. The default bit width is 16, covering [-32768, 32767].

---

## NFA Construction: Step by Step

### The Remainder Automaton (Bartzis-Bultan 2003)

For an atomic constraint `a1*x1 + a2*x2 + ... + ak*xk <= b` with `k` variables and bit width `w`:

**Step 1: Compute coefficient vector.**

Build a vector `coeffs[0..k]` from the constraint terms. Missing variables get coefficient 0.

**Step 2: Precompute bit sums.**

For each possible alphabet symbol `sym` in {0, 1}^k (there are 2^k of them), precompute the weighted bit sum:

```
bit_sum(sym) = sum over v in 0..k of (coeffs[v] * bit(sym, v))
```

where `bit(sym, v)` is the v-th bit of `sym`.

**Step 3: Build the remainder automaton.**

States represent "remainders" -- the value `r` tracking how much of the constraint's bound `b` remains after processing the bits seen so far:

```
Initial state:  (position = 0, remainder = b)

Transition at position j, remainder r, reading symbol sym:
  r' = floor((r - bit_sum(sym)) / 2)
  Next state: (position = j + 1, remainder = r')

Accepting states: (position = w, remainder >= 0)
```

The key insight is that the remainder `r` at each position captures exactly the carry propagation: dividing by 2 after subtracting the current bits' contribution moves to the next bit position, just like long division.

### State Machine Diagram

For the constraint `x0 + x1 <= 2` with 2 variables and bit width 3:

```
                         sym=(0,0)
                         r'=floor(2/2)=1
  ┌────────────┐ ────────────────────────── ┌────────────┐
  │ pos=0      │                            │ pos=1      │
  │ rem=2      │ ──sym=(1,0)──────────────▶ │ rem=1      │
  │ (initial)  │   r'=floor((2-1)/2)=0      │            │
  └────────────┘ ──sym=(0,1)──────────────▶ └────────────┘
        │          r'=floor((2-1)/2)=0            │
        │                                         │
        │ sym=(1,1)                               │ ...
        │ r'=floor((2-2)/2)=0                     │
        ▼                                         ▼
  ┌────────────┐                          ┌────────────┐
  │ pos=1      │         ...              │ pos=2      │
  │ rem=0      │ ─────────────────────▶   │ rem >= 0   │
  └────────────┘                          │ (accept)   │
                                          └────────────┘
```

### Carry Propagation

The division by 2 in `r' = floor((r - bit_sum) / 2)` is the automata-theoretic analog of carry propagation in binary addition. Consider `x + y <= 2`:

- Reading LSBs (1, 1): sum contribution = 2, remainder goes from 2 to floor((2-2)/2) = 0
- Reading next bits (0, 0): no contribution, remainder goes from 0 to floor(0/2) = 0
- At the end: remainder 0 >= 0, so accept. Indeed, x=1, y=1 satisfies x+y <= 2.

If we had read (1, 1) then (1, 0): after first step remainder = 0, after second step remainder = floor((0-1)/2) = floor(-1/2) = -1. At the end: -1 < 0, reject. Indeed, x=3, y=1 gives 3+1=4 > 2.

---

## Boolean NFA Operations

Once atomic constraints are compiled to NFAs, Boolean combinations are handled by standard NFA operations:

### Intersection (AND)

```
Input:  NFA_A for phi, NFA_B for psi
Output: NFA_C for phi AND psi

Construction: Product automaton
  States: (a_state, b_state) pairs
  Initial: all (a_init, b_init) pairs
  Transitions: (a, b) --[sym]--> (a', b')
    iff a --[sym]--> a' in NFA_A  AND  b --[sym]--> b' in NFA_B
  Accepting: (a, b) where a in F_A AND b in F_B
```

```
NFA_A          NFA_B          NFA_A AND NFA_B (product)

q0 --a--> q1   p0 --a--> p1   (q0,p0) --a--> (q1,p1)
     --b--> q2       --b--> p2        --b--> (q2,p2)

Accept: q1     Accept: p1     Accept: (q1,p1) only
```

**Complexity:** O(|Q_A| * |Q_B| * |Sigma|)

### Union (OR)

Same product construction as intersection, but accepting states are those where *either* component is accepting:

```
Accepting: (a, b) where a in F_A OR b in F_B
```

### Complement (NOT)

For the fixed-length language (all inputs are exactly `w` bits), complement uses determinization followed by acceptance flip:

```
1. Determinize NFA via subset construction
   (track sets of reachable NFA states)
2. Flip accepting/non-accepting on the resulting DFA
3. Dead state (empty set of NFA states) becomes accepting
   in the complement
```

The key subtlety is that Presburger NFAs are position-unfolded (state depends on bit position), so complement must track the bit position to avoid incorrectly accepting intermediate states. Terminal states have self-loops to absorb any remaining input after `w` bits.

**Complexity:** O(2^|Q| * |Sigma|) worst case for determinization

### Projection (EXISTS)

Existential quantification `exists x_v. phi` is implemented by dropping variable `v`'s bit from each symbol:

```
Input:  NFA for phi over k variables
Output: NFA for (exists x_v. phi) over k-1 variables

Construction:
  For each transition (s, sym, s') in the input:
    Create transitions for both sym_with_bit_v=0 and sym_with_bit_v=1
    (both bit choices are merged)
  The projected symbol is sym with bit v removed (or both values tried).
```

Projection introduces nondeterminism (merging transitions) but cannot increase the state count. It effectively "sums out" variable `v` by accepting if *any* value of `x_v` leads to acceptance.

```
Before projection (2 vars, projecting x1):

  q0 --sym=(0,0)--> q1    q0 --sym=(0,1)--> q2
  q0 --sym=(1,0)--> q3    q0 --sym=(1,1)--> q4

After projection (1 var):

  q0 --sym=0--> {q1, q2}   q0 --sym=1--> {q3, q4}
```

---

## Complexity Analysis

| Operation | k Variables | Bit Width w | Complexity | Practical Notes |
|-----------|------------|-------------|-----------|-----------------|
| Atomic NFA construction | k | w | O(w * R * 2^k) where R = reachable remainders | R typically O(max\|a_i\|), small |
| Intersection | k | w | O(\|Q_A\| * \|Q_B\| * 2^k) | Quadratic in states |
| Union | k | w | O(\|Q_A\| * \|Q_B\| * 2^k) | Same as intersection |
| Complement | k | w | O(2^{\|Q\|} * 2^k) | Exponential worst case; rare in practice |
| Projection | k | w | O(\|Q\| * 2^k) | No state increase, adds nondeterminism |
| Emptiness check | k | w | O(\|Q\| + \|transitions\|) | BFS from initial to accepting |
| Witness extraction | k | w | O(\|Q\| + \|transitions\|) | BFS shortest path |

For typical grammar-level constraints (k <= 4 variables, w = 16 bits), all operations complete in microseconds. The exponential factors are in `k` (number of variables) and `|Q|` (complement), both of which are small for guard predicates.

### Practical Bounds for Small k

| k | Alphabet size 2^k | Typical atomic NFA states | Notes |
|---|-------------------|--------------------------|-------|
| 1 | 2 | ~w | Single-variable: delegate to IntervalAlgebra for speed |
| 2 | 4 | ~2w | Most common multi-variable case |
| 3 | 8 | ~3w | Still fast |
| 4 | 16 | ~4w | Practical limit for guard predicates |

---

## Single-Variable Fast Path

When a constraint mentions only one variable (`k = 1`), the NFA construction still works but is unnecessarily heavy. The Presburger module detects this case and can delegate to `IntervalAlgebra`:

```
Single-variable constraint:  a*x <= b
  If a > 0: equivalent to x <= floor(b/a)  →  IntervalPred::Range(min, floor(b/a)+1)
  If a < 0: equivalent to x >= ceil(-b/a)  →  IntervalPred::Range(ceil(-b/a), max)
  If a = 0: trivially true (0 <= b) or false (0 > b)
```

This is not currently wired as an automatic delegation in the `PresburgerAlgebra` implementation, but the `PresburgerTheory::propagate()` method handles single-variable constraints efficiently through the constraint store without NFA construction.

---

## Dual Implementation: Direct BooleanAlgebra vs ConstraintTheory

The Presburger module provides *two* independent implementations:

### PresburgerAlgebra (Direct Path)

`PresburgerAlgebra` implements `BooleanAlgebra` directly, using NFA construction + emptiness check for satisfiability:

```rust
impl BooleanAlgebra for PresburgerAlgebra {
    type Predicate = PresburgerPred;
    type Domain = IntAssignment;

    fn is_satisfiable(&self, pred: &PresburgerPred) -> bool {
        let nfa = PresburgerNfa::from_pred(pred, self.bit_width);
        nfa.is_nonempty()
    }

    fn witness(&self, pred: &PresburgerPred) -> Option<IntAssignment> {
        let nfa = PresburgerNfa::from_pred(pred, self.bit_width);
        nfa.witness()
    }
    // ... and, or, not are structural (build PresburgerPred AST)
}
```

This is the **fast path**: no constraint store, no LogicT search. The entire decision procedure reduces to NFA construction and graph reachability.

### PresburgerTheory (ConstraintTheory Path)

`PresburgerTheory` implements `ConstraintTheory`, using a constraint store (`PresburgerStore`) that accumulates linear constraints:

```rust
impl ConstraintTheory for PresburgerTheory {
    type Constraint = LinearConstraint;
    type Store = PresburgerStore;

    fn propagate(&self, store: &Store, c: &LinearConstraint) -> Option<Store> {
        // Add constraint to store, check feasibility via NFA
        let mut new_store = store.clone();
        new_store.add_constraint(c.clone());
        if new_store.is_feasible(self.bit_width) { Some(new_store) } else { None }
    }

    fn label(&self, _store: &Store) -> LogicStream<LinearConstraint> {
        LogicStream::empty()  // Decidable: no labeling needed
    }
}
```

When wrapped in `TheoryAlgebra<PresburgerTheory>`, this provides a second `BooleanAlgebra` implementation that can be cross-validated against the direct path.

### Cross-Validation

Both paths must agree on satisfiability for all predicates. The test suite includes cross-validation tests that construct identical predicates in both representations and assert agreement:

```rust
fn cross_validate(direct_pred: &PresburgerPred, theory_pred: &TheoryPred<PresburgerTheory>) {
    let direct = PresburgerAlgebra::new(8);
    let theory = TheoryAlgebra::new(PresburgerTheory::new(8), 100);

    assert_eq!(
        direct.is_satisfiable(direct_pred),
        theory.is_satisfiable(theory_pred),
    );
}
```

One known divergence: atomic negation. `PresburgerAlgebra` uses classical NFA complement (`NOT(x <= 5)` = `x > 5`, which is satisfiable). `TheoryAlgebra` uses negation-as-failure (NAF), which may disagree depending on the store state. This is documented in the cross-validation tests.

---

## Worked Examples

### Example 1: x > 5 AND y < 10

**Predicate:** `PresburgerPred::And(x >= 6, y <= 9)` (normalized to <= form)

```
Step 1: Build NFA for x >= 6
  Normalized: -x <= -6
  Remainder automaton with initial remainder = -6
  Reads 16 bits of x (k=2 variables for cross-domain, but only x has nonzero coeff)

Step 2: Build NFA for y <= 9
  Remainder automaton with initial remainder = 9

Step 3: Intersect NFAs (product construction)
  Accept iff both components accept

Step 4: Emptiness check
  BFS from initial state → find accepting state → SAT

Step 5: Witness extraction
  BFS shortest path → decode bits → x=6, y=0 (or any valid pair)
```

### Example 2: x + y <= 100

**Predicate:** `PresburgerPred::Atom(LinearConstraint::new(vec![(0, 1), (1, 1)], 100))`

```
Coefficient vector: coeffs = [1, 1]
Bit sums:
  sym=00: 0    sym=01: 1    sym=10: 1    sym=11: 2

Initial state: (pos=0, rem=100)

Reading sym=11 (x_bit=1, y_bit=1):
  r' = floor((100 - 2) / 2) = 49
  → state (pos=1, rem=49)

Reading sym=01 (x_bit=0, y_bit=1):
  r' = floor((49 - 1) / 2) = 24
  → state (pos=2, rem=24)

... after 16 bits ...

Final state: (pos=16, rem=R)
Accept iff R >= 0
```

**Witness:** BFS finds shortest accepting path, e.g., x=50, y=50.

---

## Negation Normal Form (NNF) Conversion

Before NFA compilation, predicates are converted to Negation Normal Form (NNF) where negation only appears directly on atoms. This avoids the expensive general complement construction:

```
NOT(Sigma a_i * x_i <= b)  →  Sigma (-a_i) * x_i <= -(b+1)
                                (equivalently: Sigma a_i * x_i > b)

NOT(A AND B)  →  NOT(A) OR NOT(B)     (De Morgan)
NOT(A OR B)   →  NOT(A) AND NOT(B)    (De Morgan)
NOT(NOT(A))   →  A                     (double negation)
NOT(TRUE)     →  FALSE
NOT(FALSE)    →  TRUE

NOT(EXISTS x. A) remains as NOT(EXISTS x. A)
  → handled by complement of the projected NFA
```

Atomic negation is resolved algebraically: negating `Sigma a_i*x_i <= b` produces a new `LinearConstraint` with negated coefficients and adjusted bound, which is then compiled to its own NFA. No NFA complement needed for atoms.

The only case requiring NFA complement is `NOT(EXISTS x. A)` -- universal quantification over a projected NFA.

---

## PresburgerPred AST

```
PresburgerPred ::= True                              -- always true
                |  False                             -- always false
                |  Atom(LinearConstraint)             -- a1*x1 + ... + ak*xk <= b
                |  And(PresburgerPred, PresburgerPred) -- conjunction
                |  Or(PresburgerPred, PresburgerPred)  -- disjunction
                |  Not(PresburgerPred)                -- negation
                |  Exists { var: usize, body: PresburgerPred }  -- existential
```

Convenience constructors handle normalization:

| Surface form | Normalized to |
|-------------|--------------|
| a <= b | `Atom(a_i*x_i <= b)` |
| a >= b | `Atom((-a_i)*x_i <= -b)` |
| a < b | `Atom(a_i*x_i <= b-1)` |
| a > b | `Atom((-a_i)*x_i <= -(b+1))` |
| a = b | `And(a <= b, a >= b)` |
| a != b | `Or(a < b, a > b)` |

---

## Citations

- Buchi, J. R. (1960). "Weak second-order arithmetic and finite automata." *Zeitschrift fur mathematische Logik und Grundlagen der Mathematik*, 6, 66--92.
- Wolper, P. & Boigelot, B. (1995). "An automata-theoretic approach to Presburger arithmetic constraints." *SAS 1995*. LNCS 983, 21--32. DOI: [10.1007/3-540-60360-3_30](https://doi.org/10.1007/3-540-60360-3_30)
- Bartzis, C. & Bultan, T. (2003). "Efficient symbolic representations for arithmetic constraints in verification." *International Journal of Foundations of Computer Science*, 14(4), 605--624. DOI: [10.1142/S0129054103001959](https://doi.org/10.1142/S0129054103001959)
