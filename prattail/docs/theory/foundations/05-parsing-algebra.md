# Parsing Algebra

This document establishes the algebraic foundations underlying PraTTaIL's
parsing pipeline: fixed-point computation of FIRST and FOLLOW sets on complete
lattices, the interpretation of parsing as an algebra homomorphism from strings
to syntax trees, and multi-semiring evaluation of WFSTs for extracting diverse
analyses from a single automaton topology.

---

## 1  FIRST and FOLLOW Sets as Fixed-Point Computations

### 1.1  The FIRST Lattice

**Definition 1.1 (Grammar).** A grammar G = (C, T, P, S) consists of a finite
set of categories (nonterminals) C = {C_1, ..., C_k}, a finite set of
terminals T = {T_1, ..., T_m}, a finite set of productions P, and a start
category S in C.

**Definition 1.2 (FIRST Lattice).** The *FIRST lattice* of grammar G is the
tuple L = (L, sqsubseteq, bot, top, sqcup, sqcap) where:

- **Carrier**: L = prod_{i=1}^{k} P(T) -- a k-tuple of subsets of terminals,
  one component per category C_i.

- **Order**: Componentwise subset inclusion:

      (S_1, ..., S_k) sqsubseteq (S'_1, ..., S'_k)  ⟺  forall i in {1,...,k}: S_i subseteq S'_i

- **Bottom**: bot = (emptyset, ..., emptyset) -- all FIRST sets empty.

- **Top**: top = (T, ..., T) -- every terminal in every FIRST set.

- **Join**: (S_1, ..., S_k) sqcup (S'_1, ..., S'_k) = (S_1 union S'_1, ..., S_k union S'_k).

- **Meet**: (S_1, ..., S_k) sqcap (S'_1, ..., S'_k) = (S_1 intersect S'_1, ..., S_k intersect S'_k).

**Lemma 1.3.** L is a complete lattice.

*Proof.* Each component P(T) is a complete lattice under subset inclusion
(a finite power-set lattice). The finite product of complete lattices is a
complete lattice with componentwise join and meet (see `01-order-theory.md`
Section 3). The carrier has |L| = (2^m)^k = 2^{mk} elements, so L is finite.
QED.

### 1.2  The FIRST Operator

**Definition 1.4 (FIRST Operator).** The *FIRST operator* F: L to L is defined
as follows. Given an input tuple S = (S_1, ..., S_k), the output F(S) has
component i equal to:

    F(S)_i = S_i union bigcup_{(C_i to alpha beta ...) in P} first_rule(alpha, S)

where first_rule(alpha, S) extracts the contribution of the leading symbol:

    first_rule(t, S) = {t}           if t in T  (terminal)
    first_rule(C_j, S) = S_j         if C_j in C  (nonterminal)

That is, F scans every production for C_i and adds the terminal(s) that can
begin the right-hand side, resolving nonterminal references through the current
approximation S.

**Lemma 1.5 (Monotonicity).** F is monotone on L: if S sqsubseteq S', then
F(S) sqsubseteq F(S').

*Proof.* Let S sqsubseteq S', so for all j: S_j subseteq S'_j. For any
production C_i to C_j beta ..., we have first_rule(C_j, S) = S_j subseteq S'_j
= first_rule(C_j, S'). For terminal-leading productions, first_rule(t, S) =
{t} = first_rule(t, S'). Since F(S)_i is a union of S_i and the first_rule
contributions, and every contributing term is weakly larger under S' than under
S, we obtain F(S)_i subseteq F(S')_i for all i. Hence F(S) sqsubseteq F(S').
QED.

### 1.3  Fixed-Point Computation

**Theorem 1.6 (FIRST Sets via Kleene Iteration).** The FIRST sets of grammar G
are the least fixed point of F, computed as:

    FIRST = bigsqcup_{n >= 0} F^n(bot)

The iteration converges in at most |C| * |T| = k * m steps.

*Proof.*

1. L is a complete lattice (Lemma 1.3).

2. F is monotone (Lemma 1.5).

3. L is finite, so every monotone function on L is Scott-continuous (every
   directed set in a finite poset has a greatest element, and monotonicity
   implies continuity).

4. By the Kleene Fixed-Point Theorem (`01-order-theory.md` Section 5):
   lfp(F) = bigsqcup_{n >= 0} F^n(bot).

5. **Convergence bound**: Each application of F either adds at least one
   terminal to at least one category's FIRST set, or reaches a fixed point.
   The total number of (category, terminal) pairs is k * m. Therefore, the
   ascending chain bot sqsubseteq F(bot) sqsubseteq F^2(bot) sqsubseteq ...
   stabilizes after at most k * m iterations. QED.

**Concrete Grounding**: `compute_first_sets()` at `prediction.rs:213`.

- The `loop { changed = false; ...; if !changed { break; } }` pattern is
  Kleene iteration over the FIRST lattice L.
- Initial state: all FIRST sets empty (bot).
- Each loop body applies F: scans all rules, propagates terminals from
  nonterminal references.
- The `changed` flag is a dirty-flag optimization from the Pipeline Allocation
  Sprint: if no component changed in an iteration, the fixed point has been
  reached. This avoids a separate equality check on the full lattice element.
- Convergence is guaranteed by the finite lattice and monotonicity of F.

### 1.4  FOLLOW Sets

**Definition 1.7 (FOLLOW Operator).** The *FOLLOW operator* G_F: L to L is
defined analogously to F, but tracks which terminals can appear *after* a
nonterminal rather than at the beginning. For each production C_i to ... C_j
beta ..., the FOLLOW operator adds:

- FIRST(beta) to FOLLOW(C_j), if beta is not empty.
- FOLLOW(C_i) to FOLLOW(C_j), if beta can derive epsilon.

**Lemma 1.8.** G_F is monotone on L, and its least fixed point is computed by
the same Kleene iteration pattern with the same convergence bound.

*Proof.* The argument is identical to Lemma 1.5 and Theorem 1.6: the FOLLOW
operator is a union of set-valued functions, each monotone in its inputs, over
the same finite complete lattice L. QED.

**Concrete Grounding**: `compute_follow_sets_from_inputs()` at
`prediction.rs:288` uses the same `loop { changed = false; ... }` Kleene
iteration pattern as FIRST, over the same lattice structure.

---

## 2  Parsing as Algebra Homomorphism

### 2.1  Domain and Codomain

**Definition 2.1 (Free Monoid).** Let Sigma be a finite alphabet. The free
monoid (Sigma*, dot, epsilon) is the set of all finite strings over Sigma with
concatenation and the empty string as identity (see `02-automata-theory.md`
Definition 2.1 for full axioms).

**Definition 2.2 (Term Algebra).** Given grammar G = (C, T, P, S), the *term
algebra* Tree(G) is the initial algebra of G's signature:

- Each production p: C_i to X_1 X_2 ... X_n defines a constructor
  p: Tree(X_1) * Tree(X_2) * ... * Tree(X_n) to Tree(C_i).
- Each terminal t defines a nullary constructor t: 1 to Tree(t).
- Tree(G) is the smallest set closed under these constructors.

### 2.2  The Parser Homomorphism

**Definition 2.3 (Parser).** A parser for grammar G is a partial function

    P: Sigma* to Tree(G) union {bot}

that decomposes into two phases:

1. **Lexing** (L): Sigma* to T* union {bot} -- segments raw characters into a
   token sequence.
2. **Parsing** (Pi): T* to Tree(G) union {bot} -- maps token sequences to
   syntax trees.

The parser is the composition P = Pi circ L. The result bot indicates a
syntactically ill-formed input.

**Definition 2.4 (Structure Preservation).** P is *structure-preserving* in
the sense that it maps the concatenation structure of the input to the tree
structure of the output: substrings of the input map to subtrees of the output,
and the nesting of substrings is reflected in the nesting of subtrees.

### 2.3  Pratt Parsing as Iterative Homomorphism

**Theorem 2.5 (Compositional Pratt Parsing).** A Pratt parser implements the
parser homomorphism P compositionally through two mutually recursive operations:

1. **nud** (null denotation): Maps a prefix token t to a sub-tree.
   nud: T to Tree(G) handles prefix operators, literals, and grouping.

2. **led** (left denotation): Combines a left tree with an infix/postfix
   operator and a right sub-tree.
   led: Tree(G) * T * Tree(G) to Tree(G).

3. **Pratt loop**: For minimum binding power min_bp:

       tree := nud(next_token())
       while bp(peek()) > min_bp:
           op := next_token()
           right := parse_bp(right_bp(op))
           tree := led(tree, op, right)
       return tree

   Each iteration produces a well-formed sub-tree that is immediately composed
   into the growing tree via led.

*Proof.* We show by induction on the depth d of the parse tree that the Pratt
loop produces the correct tree for any well-formed input.

**Base case** (d = 1): The input is a single token t (a literal or nullary
constructor). The loop calls nud(t), which returns the leaf node. The while
condition fails (no operator follows with sufficient binding power), so the
loop returns the correct single-node tree.

**Inductive step** (d > 1): Assume the Pratt loop correctly parses all
sub-expressions of depth less than d. The current expression has the form
"left op right" (for infix) or "op arg" (for prefix). In the infix case:

- nud produces the correct left sub-tree (depth < d, by induction).
- The while loop finds op with bp(op) > min_bp.
- The recursive call parse_bp(right_bp(op)) produces the correct right
  sub-tree (depth < d, by induction).
- led(left, op, right) constructs the correct tree node.

The binding power mechanism ensures that higher-precedence operators bind more
tightly (are parsed in deeper recursive calls), reproducing the intended tree
structure. Right-associative operators use right_bp(op) = left_bp(op) - 1 to
allow same-precedence operators to associate rightward. QED.

**Concrete Grounding**: In PraTTaIL's generated code:

- `parse_Cat_nud()` = null denotation: handles prefix operators, literals,
  grouping via `(` ... `)`.
- `parse_Cat_led()` = left denotation: handles infix and postfix operators.
- `parse_Cat_bp()` = Pratt loop parameterized by minimum binding power.
- The trampoline (`trampoline.rs`) makes the recursive structure explicit:
  each `Frame_Cat` on the continuation stack corresponds to one level of the
  parsing homomorphism. The stack replaces the call stack, providing
  stack-safety for arbitrarily deep nesting (100K+ depth vs ~10K native
  stack crash).

---

## 3  Multi-Semiring Evaluation

### 3.1  Semiring Evaluation of WFSTs

**Definition 3.1 (Semiring).** A semiring is a tuple (K, oplus, otimes, 0bar,
1bar) satisfying the axioms in `03-semiring-theory.md` Definition 1.1:
(K, oplus, 0bar) is a commutative monoid, (K, otimes, 1bar) is a monoid,
otimes distributes over oplus, and 0bar annihilates under otimes.

**Definition 3.2 (WFST).** A weighted finite-state transducer over semiring K
is a tuple W = (Q, Sigma_in, Sigma_out, delta, I, F) where Q is a finite set
of states, delta subseteq Q * Sigma_in * Sigma_out * K * Q is the transition
relation, I: Q to K assigns initial weights, and F: Q to K assigns final
weights (see `02-automata-theory.md` Section 5).

**Definition 3.3 (Path Weight).** For a path pi = (e_1, e_2, ..., e_n) through
W, the path weight is:

    w(pi) = I(q_0) otimes w(e_1) otimes w(e_2) otimes ... otimes w(e_n) otimes F(q_n)

**Definition 3.4 (String Weight).** The total weight assigned to input string
x by WFST W over semiring K is:

    W_K(x) = bigoplus_{pi in paths(x)} w(pi)

where paths(x) is the set of all accepting paths labeled with x.

### 3.2  The Multi-Semiring Principle

**Key Insight**: The same WFST topology (states, transitions) can be evaluated
over different semirings to extract different analyses. The WFST is a *schema*;
the semiring is a *query*.

**PraTTaIL's Multi-Semiring Architecture**:

| Query              | Semiring K     | oplus     | otimes   | Result            |
|--------------------|----------------|-----------|----------|-------------------|
| Best parse?        | TropicalWeight | min       | +        | Lowest-cost path  |
| Rule reachable?    | BooleanWeight  | lor       | land     | Reachability bit  |
| How many parses?   | CountingWeight | +         | *        | Derivation count  |
| Repair cost?       | EditWeight     | min       | +        | Minimum-edit path |
| Total probability? | LogWeight      | log-oplus | +        | Log-partition fn  |
| Combined query?    | ProductWeight  | pairwise  | pairwise | Simultaneous      |

### 3.3  Semiring Homomorphism Preservation

**Theorem 3.5 (Semiring Homomorphism Preservation).** Let h: K_1 to K_2 be a
semiring homomorphism, i.e., h preserves oplus, otimes, 0bar, and 1bar:

    h(a oplus_1 b) = h(a) oplus_2 h(b)
    h(a otimes_1 b) = h(a) otimes_2 h(b)
    h(0bar_1) = 0bar_2
    h(1bar_1) = 1bar_2

Let W be a WFST with weights in K_1, and let h(W) denote the same WFST with
each weight w replaced by h(w). Then for all input strings x:

    h(W_{K_1}(x)) = h(W)_{K_2}(x)

That is, evaluating over K_1 and then applying h gives the same result as
re-weighting and evaluating over K_2.

*Proof.* By structural induction on paths and sums.

**Step 1 (Single edge).** For edge e with weight w(e) in K_1:
h(w(e)) = w_{h(W)}(e) by construction of h(W).

**Step 2 (Path weight).** For path pi = (e_1, ..., e_n):

    h(w_{K_1}(pi)) = h(I_1(q_0) otimes_1 w(e_1) otimes_1 ... otimes_1 w(e_n) otimes_1 F_1(q_n))

Since h preserves otimes:

    = h(I_1(q_0)) otimes_2 h(w(e_1)) otimes_2 ... otimes_2 h(w(e_n)) otimes_2 h(F_1(q_n))
    = I_2(q_0) otimes_2 w_{h(W)}(e_1) otimes_2 ... otimes_2 w_{h(W)}(e_n) otimes_2 F_2(q_n)
    = w_{K_2}(pi)

where I_2 = h circ I_1 and F_2 = h circ F_1.

**Step 3 (String weight).** For input string x with accepting paths
paths(x) = {pi_1, ..., pi_r}:

    h(W_{K_1}(x)) = h(bigoplus_{1, j=1}^{r} w_{K_1}(pi_j))

Since h preserves oplus:

    = bigoplus_{2, j=1}^{r} h(w_{K_1}(pi_j))
    = bigoplus_{2, j=1}^{r} w_{K_2}(pi_j)    (by Step 2)
    = h(W)_{K_2}(x)

QED.

### 3.4  Application: Dead-Rule Detection

**Corollary 3.6 (Tropical-Boolean Consistency).** Define h: TropicalWeight to
BooleanWeight by:

    h(w) = true   if w != infinity
    h(w) = false  if w = infinity

Then h is a semiring homomorphism (h(min(a,b)) = h(a) lor h(b), h(a+b) =
h(a) land h(b), h(infinity) = false, h(0) = true). Therefore, dead-rule
detection over BooleanWeight is consistent with dispatch over TropicalWeight:
a rule has tropical weight infinity if and only if its boolean projection is
false (unreachable).

*Proof.* We verify the four homomorphism conditions:

1. h(min(a,b)) = h(a) lor h(b): If either a or b is finite, the min is finite,
   and at least one of h(a), h(b) is true. If both are infinity, the min is
   infinity and both are false. In all cases equality holds.

2. h(a+b) = h(a) land h(b): a+b = infinity iff at least one of a, b is
   infinity. So h(a+b) = false iff h(a) = false or h(b) = false. Equivalently,
   h(a+b) = true iff both h(a) and h(b) are true. This is exactly land.

3. h(infinity) = false = 0bar_{Boolean}.

4. h(0) = true = 1bar_{Boolean}. QED.

**Concrete Grounding**: PraTTaIL exploits this at compile time:

- `pipeline.rs`: Builds one `PredictionWfst`, then evaluates over
  BooleanWeight for dead-rule detection, TropicalWeight for dispatch ordering,
  and CountingWeight for ambiguity warnings -- all from the same topology.
- `lattice.rs`: `viterbi_generic<W: Semiring + Ord>()` implements the Viterbi
  algorithm parameterized over any semiring with a total order, enabling the
  same shortest-path algorithm to compute best parses (Tropical), reachability
  (Boolean), or combined queries (ProductWeight).
- `wfst.rs`: `predict_with_confidence()` uses
  ProductWeight<TropicalWeight, CountingWeight> for simultaneous dispatch and
  ambiguity analysis, exploiting the product semiring's componentwise
  operations.

---

## 4  References

1. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). *Compilers:
   Principles, Techniques, and Tools* (2nd ed.). Pearson. Chapters 4.4
   (FIRST/FOLLOW), 4.6 (bottom-up parsing).

2. Pratt, V. R. (1973). "Top down operator precedence." *Proceedings of the
   1st Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming
   Languages (POPL '73)*, 41--51. ACM.

3. Mohri, M. (2002). "Semiring frameworks and algorithms for shortest-distance
   problems." *Journal of Automata, Languages and Combinatorics*, 7(3),
   321--350.

4. Goodman, J. (1999). "Semiring parsing." *Computational Linguistics*, 25(4),
   573--605.

5. Kuich, W. (1997). "Semirings and formal power series." In G. Rozenberg &
   A. Salomaa (Eds.), *Handbook of Formal Languages*, Vol. 1, Ch. 9.
   Springer.

6. Davey, B. A. & Priestley, H. A. (2002). *Introduction to Lattices and
   Order* (2nd ed.). Cambridge University Press. (Kleene fixed-point theorem,
   complete lattices.)
