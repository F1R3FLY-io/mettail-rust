# Optimization Theory Foundations for PraTTaIL

This document establishes the optimization-theoretic foundations underlying
PraTTaIL's weighted parsing pipeline. Every path-finding, beam-pruning, and
multi-objective decision in the codebase rests on the definitions and theorems
proven here. Cross-references to source files use the format `semiring.rs:36`,
meaning line 36 of `prattail/src/automata/semiring.rs`.

---

## 1  Bellman's Principle of Optimality

**Definition 1.1 (Optimal Substructure).**
A problem exhibits *optimal substructure* if every optimal solution to the
problem contains within it optimal solutions to its sub-problems. Formally,
let P be a problem decomposed into sub-problems P₁, ..., Pₖ. Then P has
optimal substructure when: if S* is an optimal solution to P, then for each
sub-problem Pᵢ, the restriction of S* to Pᵢ is an optimal solution to Pᵢ.

**Theorem 1.2 (Bellman's Principle).**
An optimal policy has the property that, regardless of the initial state and
initial decision, the remaining decisions must constitute an optimal policy
with regard to the state resulting from the first decision.

**Formal Statement.**
Let G = (V, E, w) be a weighted directed acyclic graph (DAG) over a semiring
(K, ⊕, ⊗, 0̄, 1̄) where ⊕  is idempotent and K admits a total order ≤
compatible with the natural semiring order (a ≤ b ⟺ a ⊕  b = a). Let s ∈ V
be the designated source vertex and define, for each v ∈ V:

    d(v) = the ⊕-optimal weight of any path from s to v

Then:

    d(s) = 1̄

    d(v) = ⊕_{(u,v) ∈ E} (d(u) ⊗  w(u,v))    for v ≠ s

This recurrence is well-defined when G is acyclic, because a topological
ordering of V guarantees that d(u) is fully determined before any vertex v
with (u, v) ∈ E is processed.

**Proof.**
We show the recurrence correctly computes d(v) for all v ∈ V by induction on
topological rank.

*Base case (rank 0).* The only vertex of rank 0 is s. The sole path from s to
s is the empty path, whose weight is 1̄ (the multiplicative identity). Hence
d(s) = 1̄. ✓

*Inductive step.* Let v have topological rank k > 0 and assume d(u) is
correct for all u with rank < k. Every path from s to v must traverse some
final edge (u, v) ∈ E where rank(u) < k. The weight of a path
π = s → ⋯ → u → v is w(π_u) ⊗ w(u, v), where π_u is the prefix path
from s to u. We compute:

    d(v) = ⊕_{all paths π from s to v} w(π)
         = ⊕_{(u,v) ∈ E} ⊕_{paths π_u from s to u} (w(π_u) ⊗ w(u,v))
         = ⊕_{(u,v) ∈ E} ((⊕_{paths π_u from s to u} w(π_u)) ⊗ w(u,v))     [⊗ distributes over ⊕]
         = ⊕_{(u,v) ∈ E} (d(u) ⊗ w(u,v))                                   [inductive hypothesis]

The third equality uses distributivity of ⊗ over ⊕ — a semiring axiom. The
fourth uses the inductive hypothesis that d(u) = ⊕ over all s-to-u paths.
This matches the recurrence, so d(v) is correct. ∎

**Concrete Grounding.** The semiring shortest-path recurrence is instantiated
wherever PraTTaIL processes a weighted DAG. The `Semiring` trait
(`semiring.rs:36`) requires `plus` (⊕) and `times` (⊗) with `zero` (0̄) and
`one` (1̄). Every concrete semiring — `TropicalWeight` (min, +, ∞, 0),
`EditWeight` (min, +, ∞, 0), `CountingWeight` (+, *, 0, 1),
`BooleanWeight` (∨, ∧, false, true), `ComplexityWeight` (min, max, ∞, 0) —
satisfies these axioms, enabling Bellman's recurrence to be applied
generically. The Viterbi implementations at `lattice.rs:377` and
`lattice.rs:490` are direct instantiations of this recurrence.

---

## 2  Viterbi as Semiring Dynamic Programming

**Theorem 2.1 (Viterbi Correctness).**
Let G = (V, E, w) be a weighted DAG over an idempotent semiring
(K, ⊕, ⊗, 0̄, 1̄) with a compatible total order. Let s be the source and t be
the sink. The following algorithm computes d(t), the ⊕-optimal path weight
from s to t, and recovers the optimal path via backtracking.

**Algorithm (Viterbi).**

    d(s) ← 1̄
    d(v) ← 0̄   for all v ≠ s
    back(v) ← ⊥  for all v

    for v in topological_order(V):
        if d(v) = 0̄: continue                              // unreachable
        for each edge (v, u) ∈ E:
            candidate ← d(v) ⊗ w(v, u)
            if candidate < d(u):                             // under total order
                d(u) ← candidate
                back(u) ← (v, edge_index)

    // Backtrack: follow back(t), back(back(t)), ..., s

**Proof.**
By strong induction on topological rank, identical to the proof of
Theorem 1.2. The `<` comparison under the total order selects the unique
⊕-optimal predecessor at each vertex, since for idempotent ⊕ with compatible
order, a ⊕ b = a ⟺ a ≤ b, and the `<` test ensures we retain only
strictly improving updates.

*Base case.* d(s) = 1̄. The empty path from s to s has weight 1̄. ✓

*Inductive step.* Assume d(u) is correct for all u with rank < rank(v).
For vertex v, the algorithm examines all predecessors u with (u, v) ∈ E and
retains d(v) = min_{(u,v) ∈ E} (d(u) ⊗ w(u,v)) under the total order.
By the inductive hypothesis and distributivity (as in Theorem 1.2):

  d(v) = ⊕_{(u,v) ∈ E} (d(u) ⊗ w(u,v)) = ⊕_{all paths s→v} w(path)

The `back` pointer records the argmin predecessor, so the chain
back(t) → back(back(t)) → ⋯ → s reconstructs the ⊕-optimal path. ✓

*Termination.* The algorithm iterates once over each vertex in topological
order, visiting each edge exactly once. Time complexity is O(|V| + |E|).

*Backtracking correctness.* At each vertex v ≠ s on the optimal path,
back(v) = (u*, idx) where u* is the predecessor achieving the minimum
d(u*) ⊗ w(u*, v). Since d(v) was set from d(u*), and d(u*) is correct by
hypothesis, the chain back(t), back(back(t)), ..., s traces the optimal path
in reverse. Reversing this chain yields the forward optimal path. ∎

**Concrete Grounding.** `viterbi_generic<W: Semiring + Ord>()` at
`lattice.rs:490` is a direct implementation of this algorithm. The `dist`
vector (`lattice.rs:499`) corresponds to d(v), initialized to `W::zero()`
(= 0̄) with `dist[0] = W::one()` (= 1̄). The `pred` vector
(`lattice.rs:502`) corresponds to back(v). The forward loop
(`lattice.rs:504–518`) processes nodes in order 0..n — valid because
`TokenLattice` edges go strictly forward (target > source), making node
index a topological order. The `new_dist < dist[edge.target]` comparison
(`lattice.rs:514`) uses the `Ord` instance on W. This function works for
any semiring with `Ord`: `TropicalWeight` finds minimum-cost paths,
`EditWeight` finds minimum-edit paths, `ComplexityWeight` finds
minimum-bottleneck paths, and `ProductWeight` finds lexicographic optima.

---

## 3  Beam Search as Bounded A*

**Definition 3.1 (A* Search).**
A* search uses evaluation function f(n) = g(n) + h(n) where g(n) is the
cost from the source to n and h(n) is a heuristic estimate of the cost from
n to the goal. A* is optimal when h is *admissible* (∀ n: h(n) ≤ h*(n),
the true cost to goal) and *consistent* (∀ edges (n, m): h(n) ≤ w(n, m) + h(m)).

**Definition 3.2 (Beam Search).**
Beam search with width B retains only the B most promising partial paths at
each expansion level. This is equivalent to A* with bounded open-set size:
at each level, the open set is truncated to its B best entries. A continuous
variant uses a weight threshold rather than a count: retain all states with
cost within threshold w of the best state at each level.

**Theorem 3.3 (Beam Degeneracy).**
Let V be the set of all vertices at each level. Then:
1. Beam search with B = |V| (all states retained) is equivalent to exact Viterbi.
2. Beam search with B = 1 (single state retained) is equivalent to greedy search.

**Proof.**

*Part 1.* When B = |V|, no states are pruned at any level. Every state
reachable by at least one path is retained. The algorithm therefore considers
every path from source to sink, which is identical to the exhaustive forward
pass of Viterbi (Theorem 2.1). The minimum-cost path among all paths is
found. ✓

*Part 2.* When B = 1, at each level the algorithm retains only the single
state with minimum accumulated cost. All other partial paths are discarded.
This is exactly greedy search: at each step, commit irrevocably to the
locally best option. ✓

*Combined.* B interpolates between greedy (B = 1) and exact (B = |V|).
Increasing B monotonically increases the set of explored paths, so the
solution quality is monotonically non-decreasing in B. ∎

**Theorem 3.4 (Weight-Threshold Beam Equivalence).**
Let d* be the optimal (minimum) accumulated cost at a given level. A
weight-threshold beam with threshold w retains all states v with
d(v) ≤ d* + w. Then:
1. Threshold w = 0 retains only optimal-cost states (tightest beam).
2. Threshold w = ∞ retains all states (equivalent to exact Viterbi).

**Proof.**

*Part 1.* With w = 0, the condition d(v) ≤ d* + 0 = d* retains only states
achieving the minimum cost d*. All suboptimal states are pruned. ✓

*Part 2.* With w = ∞, the condition d(v) ≤ d* + ∞ = ∞ is trivially
satisfied for all finite-cost states. No pruning occurs, recovering exact
Viterbi. ✓ ∎

**Concrete Grounding.** `viterbi_best_path_beam()` at `lattice.rs:377`
implements weight-threshold beam search. The `beam_width: Option<TropicalWeight>`
parameter (`lattice.rs:380`) controls the threshold: `None` disables pruning
(exact Viterbi, Theorem 3.4 part 2), `Some(w)` prunes states exceeding
`best_final.value() + beam.value()` (`lattice.rs:405`). The variable
`best_final` (`lattice.rs:395`) tracks the best known cost to the final node,
enabling progressive beam tightening as the algorithm discovers better
complete paths. This is used in error recovery to bound the exploration of
alternative repair paths while guaranteeing the optimal path is found when it
falls within the beam threshold.

---

## 4  Minimax and Bottleneck Optimization

**Definition 4.1 (Two-Player Zero-Sum Game).**
A two-player zero-sum game on a tree T = (V, E) alternates between a
*maximizing* player (who selects the child with maximum value) and a
*minimizing* player (who selects the child with minimum value). The
*minimax value* at the root is:

  minimax(root) = max_{player 1} min_{player 2} payoff(leaf)

**Definition 4.2 (Bottleneck Path).**
Given a graph G = (V, E, w) with edge weights, the *bottleneck* of a
path π = e₁, e₂, ..., eₙ is:

  bottleneck(π) = max(w(e₁), w(e₂), ..., w(eₙ))

The *bottleneck shortest path* from s to t minimizes the bottleneck over
all s-t paths:

  d*(s, t) = min_{paths π from s to t} max_{e ∈ π} w(e)

This is a minimax problem: the adversary (max) selects the worst edge on
each path; the optimizer (min) selects the path minimizing the worst edge.

**Theorem 4.3 (ComplexityWeight is the Bottleneck Semiring).**
The algebraic structure (N ∪ {∞}, min, max, ∞, 0) is an idempotent
semiring, and Viterbi over this semiring computes bottleneck shortest paths.

**Proof.**
We verify the semiring axioms for (N ∪ {∞}, min, max, ∞, 0):

1. *⊕ = min is a commutative monoid with identity 0̄ = ∞.*
   - Commutativity: min(a, b) = min(b, a). ✓
   - Associativity: min(a, min(b, c)) = min(min(a, b), c). ✓
   - Identity: min(a, ∞) = a for all a. ✓

2. *⊗ = max is a monoid with identity 1̄ = 0.*
   - Associativity: max(a, max(b, c)) = max(max(a, b), c). ✓
   - Identity: max(a, 0) = a for all a ∈ N ∪ {∞}. ✓

3. *⊗ distributes over ⊕.*
   - Left: max(a, min(b, c)) = min(max(a, b), max(a, c)). This is the
     distributive law of max over min in any totally ordered set. ✓
   - Right: max(min(b, c), a) = min(max(b, a), max(c, a)). By commutativity
     of max. ✓

4. *0̄ = ∞ annihilates under ⊗.*
   - max(a, ∞) = ∞ = 0̄ for all a. ✓

5. *⊕ is idempotent.* min(a, a) = a. ✓

All five axiom groups hold, confirming (N ∪ {∞}, min, max, ∞, 0) is an
idempotent semiring.

Now, for a path π = e₁, ..., eₙ, its semiring weight is:

  w(π) = w(e₁) ⊗ w(e₂) ⊗ ⋯ ⊗ w(eₙ) = max(w(e₁), ..., w(eₙ)) = bottleneck(π)

The ⊕-optimal path has weight:

  d*(s, t) = ⊕_{all paths π} w(π) = min_{all paths π} bottleneck(π)

This is exactly the bottleneck shortest path, which is the minimax value
of the path structure (Definition 4.2). By Theorem 2.1, Viterbi correctly
computes this value. ∎

**Concrete Grounding.** `ComplexityWeight` at `semiring.rs:781` implements
this bottleneck semiring. The `plus` method (`semiring.rs:837`) computes
min; the `times` method (`semiring.rs:843`) computes max. The `zero`
(`semiring.rs:825`) is `u32::MAX` (representing ∞) and `one`
(`semiring.rs:831`) is 0. The `value` field represents estimated lookahead
depth for a dispatch decision point. When Viterbi runs over a lattice
weighted by `ComplexityWeight`, it finds the parse path whose hardest
dispatch point (bottleneck) is minimized — bounding the worst-case
backtracking depth. Named constructors `deterministic()` (0),
`single_lookahead()` (1), `multi_lookahead(depth)`, and `infinite()` (∞)
at `semiring.rs:795–817` provide domain-specific weight values.

---

## 5  Multi-Objective Optimization via ProductWeight

**Definition 5.1 (Lexicographic Order).**
Given two totally ordered sets (A, ≤_A) and (B, ≤_B), the *lexicographic
order* on A x B is defined by:

  (a₁, b₁) ≤_lex (a₂, b₂) ⟺ (a₁ <_A a₂) ∨ (a₁ = a₂ ∧ b₁ ≤_B b₂)

**Definition 5.2 (Lexicographic Optimization).**
Given two objective functions f₁: X → A and f₂: X → B, the *lexicographic
optimum* x* ∈ X satisfies:
1. f₁(x*) ≤ f₁(x) for all x ∈ X (primary objective is optimal).
2. Among all x achieving optimal f₁, f₂(x*) ≤ f₂(x) (secondary objective
   is optimal subject to primary constraint).

**Theorem 5.3 (ProductWeight Viterbi Computes Lexicographic Optima).**
Let S₁ and S₂ be idempotent semirings with compatible total orders. Then
Viterbi over ProductWeight<S₁, S₂> with lexicographic Ord computes the
lexicographic optimum: first optimizing with respect to S₁, then breaking
ties with S₂.

**Proof.**
The ProductWeight semiring (K, ⊕, ⊗, 0̄, 1̄) is defined by:

  K = S₁ x S₂
  (a₁, b₁) ⊕ (a₂, b₂) = (a₁ ⊕₁ a₂, b₁ ⊕₂ b₂)     [component-wise plus]
  (a₁, b₁) ⊗ (a₂, b₂) = (a₁ ⊗₁ a₂, b₁ ⊗₂ b₂)     [component-wise times]
  0̄ = (0̄₁, 0̄₂)
  1̄ = (1̄₁, 1̄₂)

The Ord instance is lexicographic:

  (a₁, b₁) < (a₂, b₂) ⟺ a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)

The Viterbi algorithm (Theorem 2.1) uses `<` under the total order for the
argmin selection (the `new_dist < dist[edge.target]` test). The semiring
`plus` is used implicitly to combine path weights. We must show that:

*Step 1: The DP recurrence is correct.* Path weights are computed via ⊗,
which is component-wise. For a path π with edges e₁, ..., eₙ:

  w(π) = w(e₁) ⊗ w(e₂) ⊗ ⋯ ⊗ w(eₙ) = (⊗₁ᵢ w₁(eᵢ), ⊗₂ᵢ w₂(eᵢ))

The first component is the S₁-weight of the path; the second is the
S₂-weight. This is correct by component-wise composition.

*Step 2: The argmin selects the lexicographic optimum.* Among all paths
reaching vertex v, the Viterbi algorithm retains the one with minimum
weight under the lexicographic order. This path has:
- Minimum first component (S₁-weight) among all paths to v.
- Among paths with minimum S₁-weight, minimum second component (S₂-weight).

This is exactly the lexicographic optimum (Definition 5.2).

*Step 3: Distributivity holds component-wise.* Since both S₁ and S₂ are
semirings, ⊗ distributes over ⊕ in each component:

    (a₁, b₁) ⊗ ((a₂, b₂) ⊕ (a₃, b₃))
      = (a₁, b₁) ⊗ (a₂ ⊕₁ a₃, b₂ ⊕₂ b₃)
      = (a₁ ⊗₁ (a₂ ⊕₁ a₃), b₁ ⊗₂ (b₂ ⊕₂ b₃))
      = ((a₁ ⊗₁ a₂) ⊕₁ (a₁ ⊗₁ a₃), (b₁ ⊗₂ b₂) ⊕₂ (b₁ ⊗₂ b₃))
      = (a₁ ⊗₁ a₂, b₁ ⊗₂ b₂) ⊕ (a₁ ⊗₁ a₃, b₁ ⊗₂ b₃)
      = ((a₁, b₁) ⊗ (a₂, b₂)) ⊕ ((a₁, b₁) ⊗ (a₃, b₃))

Distributivity holds, so the Bellman recurrence (Theorem 1.2) applies. ∎

**Remark 5.4 (Component-wise plus vs. lexicographic Ord).**
The semiring `plus` is component-wise, not lexicographic. This means `plus`
identifies the Pareto-optimal frontier component-by-component, while `Ord`
then selects among candidates lexicographically. In the Viterbi algorithm,
only `Ord` is used for the argmin comparison — `plus` is not invoked
directly. The correctness of this approach relies on the fact that for
idempotent semirings with compatible total order, a ⊕ b = min(a, b), so
the argmin via `<` is equivalent to applying `plus` and checking which
operand was selected.

**Concrete Grounding.** `ProductWeight<S1, S2>` at `semiring.rs:513`
implements the product semiring with lexicographic `Ord` at
`semiring.rs:590–594`:
```rust
impl<S1: Semiring + Ord, S2: Semiring + Ord> Ord for ProductWeight<S1, S2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left.cmp(&other.left).then_with(|| self.right.cmp(&other.right))
    }
}
```
Two primary instantiations appear in PraTTaIL:
- `RecoveryCost = ProductWeight<TropicalWeight, EditWeight>` at
  `recovery.rs:58`: lexicographic optimization of parse quality (tropical
  cost, primary) then repair minimality (edit count, secondary). Used
  throughout error recovery (`recovery.rs:881–888`) to find minimum-cost
  repair sequences that also minimize the number of token edits.
- `ProductWeight<TropicalWeight, CountingWeight>`: parse priority first,
  then derivation count. Used by `predict_with_confidence()` at `wfst.rs:362`
  to rank predictions by priority with ambiguity as a secondary signal.

---

## 6  References

- Bellman, R. (1957). *Dynamic Programming*. Princeton University Press.
- Viterbi, A. J. (1967). "Error bounds for convolutional codes and an
  asymptotically optimum decoding algorithm." *IEEE Trans. Information
  Theory*, 13(2), 260--269.
- Mohri, M. (2002). "Semiring frameworks and algorithms for shortest-distance
  problems." *Journal of Automata, Languages and Combinatorics*, 7(3),
  321--350.
- Russell, S. J. & Norvig, P. (2021). *Artificial Intelligence: A Modern
  Approach* (4th ed.). Pearson.
- Hart, P. E., Nilsson, N. J., & Raphael, B. (1968). "A formal basis for the
  heuristic determination of minimum cost paths." *IEEE Trans. Systems
  Science and Cybernetics*, 4(2), 100--107.
- Kuich, W. & Salomaa, A. (1986). *Semirings, Automata, Languages*.
  Springer-Verlag.
