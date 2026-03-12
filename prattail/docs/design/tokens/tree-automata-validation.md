# Tree Automata Validation of Token Trees

## Overview

Once VPA-based delimiter grouping has converted a flat token stream into a
hierarchical `TokenTree<T>` (see `vpa-delimiter-grouping.md`), a natural
question arises: does this tree have the right *shape*? Are the tokens
inside each delimited group arranged in a structurally valid way?

Finite automata answer this question for *sequences* (words). Tree automata
answer it for *trees* (terms). Since `TokenTree<T>` values are trees, tree
automata are the natural formalism for structural validation.

PraTTaIL provides two tree automata formalisms at different levels of
expressiveness:

| Formalism | What it checks | Complexity | Feature gate |
|-----------|---------------|------------|--------------|
| **WTA** (Weighted Tree Automaton) | Term membership + ranking | Polynomial | `tree-automata` |
| **PATA** (Parity Alternating Tree Automaton) | Recursive structural invariants via mu-calculus | EXPTIME | `parity-tree-automata` |


## 1. Intuition: From Words to Trees

A finite automaton reads a word left to right, transitioning between states.
A tree automaton does the same thing, but on a tree -- processing nodes
rather than characters. The *bottom-up* variant starts at the leaves and
works toward the root, combining child states at each internal node.

Consider validating the expression `(a + b)` represented as a tree:

```
      Group("(")
     /    |     \
  Token  Token  Token
   "a"    "+"    "b"
```

A bottom-up tree automaton assigns states to the leaves first (e.g., "a"
gets state q_id), then combines child states at each internal node using
transition rules (e.g., Group(q_id, q_op, q_id) --> q_expr). If the root
reaches an accepting state, the tree is valid.


## 2. Weighted Tree Automata (WTA)

### 2.1 Formal Definition

A WTA is a tuple:

    A = (Q, Sigma_ranked, Delta, F, w)

where:

- **Q** is a finite set of states
- **Sigma_ranked** is a ranked alphabet -- each symbol f has a fixed arity
  rank(f) in N
- **Delta** is the set of transitions: f(q_1, ..., q_n) --> q, where
  rank(f) = n
- **F subset Q** is the set of final (accepting) states
- **w : Delta --> W** assigns a weight from semiring W to each transition

A *run* rho assigns a state to every node, from leaves to root. Its weight
is the semiring product of all transition weights along the run:

    weight(rho) = bigotimes_{v in nodes(t)} w(delta_v)

The weight of a term t is the semiring sum over all accepting runs:

    weight(t) = bigoplus_{rho : rho(root) in F} weight(rho)

### 2.2 Semiring Instantiations

The choice of semiring W determines what the WTA computes:

| Semiring | oplus | otimes | Meaning |
|----------|-------|--------|---------|
| BooleanWeight | or | and | Tree language membership |
| TropicalWeight | min | + | Minimum-cost derivation |
| CountingWeight | + | * | Number of accepting runs |
| ViterbiWeight | max | * | Most probable derivation |
| LogWeight | log-add | + | Log-probability aggregation |


## 3. Bottom-Up Evaluation: `bottom_up_evaluate()`

The core evaluation function processes a term from leaves to root:

```rust
pub fn bottom_up_evaluate<W: Semiring>(
    automaton: &TreeAutomaton<W>,
    term: &Term,
) -> HashMap<usize, W>
```

**Algorithm**:

1. Recursively evaluate all children, producing a state-to-weight map for
   each child.
2. For each transition f(q_1, ..., q_n) --> q with weight w_t:
   - Check that the symbol and arity match the current node
   - Check that each required child state q_i is reachable in child i
   - Compute combined weight: w_t otimes w_1 otimes ... otimes w_n
3. Accumulate via semiring oplus when multiple transitions reach the same
   target state.

**Returns**: A map from state ID to accumulated weight at the root.

### Worked Example

WTA with transitions: `"a" --> q_id [1.0]`, `"+" --> q_op [1.0]`,
`Group(q_id, q_op, q_id) --> q_expr [0.5]`, final states = {q_expr}.

Evaluating `Group("(", children=[Token("a"), Token("+"), Token("b")])`:

```
Leaves:   "a" --> {q_id: 1.0},  "+" --> {q_op: 1.0},  "b" --> {q_id: 1.0}
Internal: Group(q_id, q_op, q_id) --> q_expr, weight = 0.5 * 1.0^3 = 0.5
Root:     {q_expr: 0.5}  <-- final state reached, term accepted
```


## 4. TokenTree-to-Term Conversion: `token_tree_to_term()`

The bridge between VPA's `TokenTree<T>` and WTA's `Term` is a simple O(n)
recursive mapping:

```rust
pub fn token_tree_to_term<T: Debug>(
    tt: &TokenTree<T>,
    token_to_symbol: &dyn Fn(&T) -> String,
) -> Term
```

The conversion rules:

| TokenTree variant | Term result |
|-------------------|-------------|
| `Token(tok, _)` | `Term { symbol: name(tok), children: [] }` |
| `Group { open, children, .. }` | `Term { symbol: name(open.0), children: [recursive...] }` |

The closer token is not included in the term -- the opener alone identifies
the group kind. Requires `#[cfg(all(feature = "tree-automata", feature = "vpa"))]`.


## 5. Validation Pipeline: `validate_token_tree()`

The full validation function chains conversion and evaluation:

```rust
pub fn validate_token_tree<W: Semiring, T: Debug>(
    automaton: &TreeAutomaton<W>,
    tree: &TokenTree<T>,
    token_to_symbol: &dyn Fn(&T) -> String,
) -> Result<W, TreeValidationError>
```

**Algorithm**: Converts `TokenTree` to `Term`, runs `bottom_up_evaluate()`,
aggregates weights across final states via oplus, and returns `Ok(weight)`
if any final state has non-zero weight, or `Err(TreeValidationError)` with
a diagnostic message otherwise.

### Integration with Lint Diagnostics

Two WTA-related lints report structural anomalies:

**V03 -- wta-unrecognized-term** (Warning): A term pattern was not in the
regular tree language. The WTA found no accepting run, indicating a
structural mismatch between the token tree and the grammar's expected
shapes.

**V04 -- wta-hot-path** (Note): A term pattern has unusually high weight
(via `WeightHeat`), making it a candidate for hot-path specialization.
This is purely informational -- it identifies optimization opportunities.


## 6. Hot-Path Specialization

### 6.1 The `WeightHeat` Trait

To rank transitions by importance for specialization, each semiring
implements the `WeightHeat` trait:

```rust
pub trait WeightHeat: Semiring {
    fn to_heat(&self) -> f64;
}
```

The mapping is semiring-dependent:

| Semiring | Heat formula | Rationale |
|----------|-------------|-----------|
| TropicalWeight | 1 / (1 + cost) | Lower cost = hotter |
| CountingWeight | count as f64 | More derivations = hotter |
| BooleanWeight | 1.0 if true, 0.0 | Reachable = hot |
| ViterbiWeight | probability | Higher probability = hotter |
| EditWeight | 1 / (1 + distance) | Lower edit distance = hotter |
| FuzzyWeight | membership degree | Direct membership = heat |
| LogWeight | exp(-value) | Lower neglog = hotter |

### 6.2 Hot-Path Analysis and `specialize()`

`hot_path_analysis()` ranks transitions by heat and identifies candidates
whose heat exceeds 2x the average. `specialize()` creates dedicated
fast-path states for these candidates, preserving the recognized tree
language and all weights while giving frequent patterns a shorter path.


## 7. Parity Alternating Tree Automata (PATA)

While WTAs verify that a tree has the right *shape*, some structural
properties require reasoning about *recursive patterns* -- properties like
"no brace group is directly nested inside another brace group" or "every
function call has at least one argument." These are naturally expressed in
the modal mu-calculus, which PATA can check.

### 7.1 Formal Definition

A PATA is a tuple:

    A = (Q, Sigma, delta, q_0, Omega, k)

where:

- **Q = Q_E union Q_A** partitions states into existential (disjunctive)
  and universal (conjunctive)
- **Sigma** is the ranked alphabet
- **delta : Q x Sigma --> B^+(Dir x Q)** maps states and symbols to
  positive Boolean combinations of direction-state pairs, where
  Dir = {0, 1, ..., k-1} indexes child positions
- **q_0 in Q** is the initial state
- **Omega : Q --> N** is the priority function
- **k** is the maximum arity

**Acceptance**: A run is accepting iff on every infinite path, the minimum
priority occurring infinitely often is *even* (subsuming Buchi and co-Buchi).

**Alternation**: Existential states require *some* direction-state pair to
succeed; universal states require *all* to succeed. This lets a single PATA
express properties requiring exponentially many non-alternating states.

### 7.2 The `tree_invariants { ... }` DSL

PraTTaIL grammars declare structural invariants in the `tokens { ... }` block:

```
tree_invariants {
    no_nested_braces:  forall down Brace { not Brace }
    has_body:          forall down FnDecl { exists Brace }
}
```

DSL operators: `forall`/`exists` (quantifiers), `not`/`and`/`or` (Boolean),
`match`/`in` (atom), `down`/`child` (modality). Each invariant compiles to
a `TreeInvariantSpec { name: String, formula: String }`.

### 7.3 Compilation to `MuCalculusFormula`

The DSL formulas compile to the `MuCalculusFormula` enum, whose variants
are: `Var`, `True`, `False`, `Atom`, `Not`, `And`, `Or`, `Diamond{child_idx, body}`,
`Box{child_idx, body}`, `Mu{var, body}`, and `Nu{var, body}`.

The fixed-point operators are the key to recursive properties:

- **mu X. phi** (least fixpoint): The smallest set of nodes satisfying phi.
  Captures *finite* reachability -- properties that must eventually hold.

- **nu X. phi** (greatest fixpoint): The largest set of nodes satisfying
  phi. Captures *invariant* properties -- conditions that hold forever.

### 7.4 Worked Example: No Nested Braces

The invariant "no brace group directly contains another brace group":

```
no_nested_braces: forall down Brace { not Brace }
```

Compiles to:

    nu("X", And(Not(And(Atom("Brace"), Diamond(0, Atom("Brace")))), Box(0, Var("X"))))

Reading this formula:

    nu X.                    Greatest fixpoint (invariant: holds everywhere)
      And(
        Not(                 It is NOT the case that:
          And(
            Atom("Brace"),     this node is a Brace, AND
            Diamond(0,         some child (direction 0)
              Atom("Brace")    is also a Brace
            )
          )
        ),
        Box(0, X)            AND this property holds for all children (recursive)
      )

The nu operator makes this a *global* invariant -- it must hold at every
node in the tree, not just the root.

### 7.5 From Mu-Calculus to PATA: `mu_calculus_to_pata()`

```rust
pub fn mu_calculus_to_pata(
    formula: &MuCalculusFormula,
    max_arity: usize,
) -> ParityAlternatingTreeAutomaton<BooleanWeight>
```

The compilation recursively translates each formula constructor into PATA
states and transitions. `True`/`False` become accepting/rejecting leaf
states. `Atom(a)` becomes an existential state matching label a. `Diamond`
and `Box` produce existential and universal states respectively, with
direction triples pointing into child subtrees. Each fixpoint (`Mu`/`Nu`)
allocates a fresh priority level -- Mu gets odd priority (rejecting unless
escaped), Nu gets even priority (accepting by default) -- ensuring the
parity condition distinguishes least from greatest fixpoints.

### 7.6 Evaluation and Emptiness

**`evaluate_term(automaton, term) -> bool`**: Checks whether a concrete
term satisfies the invariant via fixpoint computation.

**`check_emptiness(automaton) -> bool`**: Determines whether *any* tree
satisfies the formula, via parity game reduction.


## 8. Feature Gates

```toml
[features]
tree-automata = []           # WTA: bottom_up_evaluate, hot_path_analysis, specialize
vpa = []                     # VPA: TokenTree, skip table (see vpa-delimiter-grouping.md)
parity-tree-automata = []    # PATA: MuCalculusFormula, tree_invariants DSL
```

The TokenTree validation bridge (`token_tree_to_term`, `validate_token_tree`)
requires both `tree-automata` and `vpa`. PATA invariants are orthogonal --
they operate on abstract grammar structure and do not require `vpa`.


## 9. Complexity Summary

| Operation | Time | Space |
|-----------|------|-------|
| `bottom_up_evaluate` | O(n * d * t) | O(n * s) |
| `token_tree_to_term` | O(n) | O(n) |
| `validate_token_tree` | O(n * d * t) | O(n * s) |
| `hot_path_analysis` | O(t log t) | O(t) |
| `specialize` | O(c * t) | O(s + c) |
| `mu_calculus_to_pata` | O(f) | O(f) |
| `evaluate_term` (PATA) | O(n * s^2) | O(n * s) |
| `check_emptiness` (PATA) | O(s^k) | O(s^k) |

Where: n = term nodes, d = max arity, t = transitions, s = states,
c = specialization candidates, f = formula size, k = parity index.


## 10. End-to-End Pipeline

```
tokens { ... }
      |
      v
VPA grouping --> Vec<TokenTree<T>> --> token_tree_to_term() --> Term
                                                                  |
                      +-------------------------------------------+
                      |                        |
                      v                        v
              bottom_up_evaluate()     evaluate_term() [PATA]
                      |                (structural invariants)
                      v
              validate_token_tree() --> Ok(W) or Err
                      |
              hot_path_analysis() --> specialize()
```


## References

- **Comon, H., Dauchet, M., Gilleron, R., et al. (2007)**. *Tree Automata
  Techniques and Applications* (TATA). Available online. The standard
  reference for tree automata theory: bottom-up and top-down variants,
  determinization, minimization, closure properties, and decidability
  results.

- **Kempe, A. (2004)**. "Weighted tree automata." In *Handbook of Weighted
  Automata*, Chapter 9. Semiring-weighted tree transitions; the algebraic
  framework behind PraTTaIL's `TreeAutomaton<W>`.

- **Emerson, E. A. & Jutla, C. S. (1991)**. "Tree automata, mu-calculus
  and determinacy." *FOCS*, pp. 368--377. Equivalence between mu-calculus
  satisfiability and parity tree automaton emptiness.

- **Thatcher, J. W. & Wright, J. B. (1968)**. "Generalized finite automata
  theory with an application to a decision problem of second-order logic."
  *Mathematical Systems Theory*, 2(1), pp. 57--81. Introduces finite tree
  automata and proves closure under Boolean operations.
