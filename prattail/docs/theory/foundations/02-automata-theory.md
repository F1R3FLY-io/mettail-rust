# Automata Theory

This document establishes the automata-theoretic foundations underlying
PraTTaIL's two-phase architecture: a Type-3 DFA lexer feeding a Type-2
Pratt/recursive-descent parser. We state the Myhill-Nerode theorem with a
constructive proof sketch that maps directly onto PraTTaIL's DFA minimizer,
then extend classical automata to weighted automata over semirings.

---

## 1  Chomsky Hierarchy

The Chomsky hierarchy classifies formal grammars into four types.
PraTTaIL's architecture exploits the bottom two levels:

| Type | Grammar           | Language Class         | Recognizer         | PraTTaIL Component  |
|------|-------------------|------------------------|--------------------|---------------------|
| 0    | Unrestricted      | Recursively enumerable | Turing machine     | --                  |
| 1    | Context-sensitive | CSL                    | Linear-bounded NTM | --                  |
| 2    | Context-free      | CFL                    | Pushdown automaton | Parser (Pratt + RD) |
| 3    | Regular           | Regular                | Finite automaton   | Lexer (DFA)         |

PraTTaIL's two-phase pipeline maps directly onto this classification:

- **Lexer** (Type 3): Regular expressions are compiled to NFAs
  (`automata/nfa.rs:27`), determinized via subset construction
  (`automata/subset.rs:48`), and minimized (`automata/minimize.rs:95`).
  The resulting minimal DFA recognizes exactly the regular token language.

- **Parser** (Type 2): The trampoline-based Pratt/recursive-descent parser
  (`trampoline.rs`) recognizes context-free structure. Operator precedence
  and associativity are encoded via binding powers; recursive descent handles
  mixfix, optional, and n-ary constructs.

---

## 2  Myhill-Nerode Theorem

### 2.1  Preliminaries

**Definition 2.1 (Free Monoid).** Let Sigma be a finite alphabet. The
*free monoid* Sigma* is the set of all finite strings over Sigma, equipped
with concatenation as the binary operation and the empty string epsilon as the
identity element. That is, (Sigma*, ., epsilon) satisfies:

1. **Closure**: For all x, y in Sigma*, x . y in Sigma*.
2. **Associativity**: For all x, y, z in Sigma*, (x . y) . z = x . (y . z).
3. **Identity**: For all x in Sigma*, epsilon . x = x . epsilon = x.

**Definition 2.2 (Right-Invariant Equivalence).** An equivalence relation ~
on Sigma* is *right-invariant* if:

    x ~ y  ⟹  xz ~ yz    for all z in Sigma*

The relation ~ *refines* a language L if Sigma* if:

    x ~ y  ⟹  (x in L ⟺ y in L)

**Definition 2.3 (Nerode Equivalence).** For a language L in Sigma*, the
*Nerode equivalence* equiv_L is defined by:

    x equiv_L y  ⟺  forall z in Sigma*: xz in L ⟺ yz in L

Equivalently, x equiv_L y iff x and y are indistinguishable by any right
context. The equivalence class of x under equiv_L is written [x]_L.

**Lemma 2.4.** The Nerode equivalence equiv_L is the coarsest right-invariant
equivalence relation on Sigma* that refines L.

*Proof.* First, equiv_L is right-invariant: suppose x equiv_L y. For any
w in Sigma* and any z in Sigma*, we have xwz in L iff ywz in L (taking wz as
the distinguishing suffix). Hence xw equiv_L yw. Second, equiv_L refines L:
take z = epsilon to get x in L iff y in L. Third, coarseness: let ~ be any
right-invariant equivalence refining L and suppose x ~ y. For any z in Sigma*,
right-invariance gives xz ~ yz, and refinement gives xz in L iff yz in L.
Hence x equiv_L y, so ~ refines equiv_L. QED.

### 2.2  The Theorem

**Theorem 2.5 (Myhill-Nerode).** For a language L in Sigma*, the following
are equivalent:

1. L is regular (accepted by some DFA).
2. L is the union of equivalence classes of some right-invariant equivalence
   of finite index on Sigma*.
3. The Nerode equivalence equiv_L has finite index.

*Proof.*

**(1 => 2):** Let M = (Q, Sigma, delta, q_0, F) be a DFA accepting L.
Define the relation ~_M on Sigma* by:

    x ~_M y  ⟺  delta*(q_0, x) = delta*(q_0, y)

where delta* is the extended transition function. Then:

- **Equivalence**: ~_M is an equivalence relation (reflexive, symmetric,
  transitive) because equality of states is an equivalence.
- **Right-invariance**: If delta*(q_0, x) = delta*(q_0, y), then for any
  z in Sigma*, delta*(q_0, xz) = delta*(delta*(q_0, x), z) =
  delta*(delta*(q_0, y), z) = delta*(q_0, yz). Hence x ~_M y implies
  xz ~_M yz.
- **Finite index**: The number of equivalence classes is at most |Q|.
- **Refines L**: x in L iff delta*(q_0, x) in F. If delta*(q_0, x) =
  delta*(q_0, y), then x in L iff y in L.

Thus L is the union of those equivalence classes [x]_{~_M} for which
delta*(q_0, x) in F.

**(2 => 3):** Let ~ be a right-invariant equivalence of finite index that
refines L. By Lemma 2.4, ~ refines equiv_L, meaning every equiv_L class is a
union of ~-classes. Therefore the index of equiv_L is at most the index of ~,
which is finite.

**(3 => 1):** Assume equiv_L has finite index n. Construct the DFA
M_L = (Q_L, Sigma, delta_L, q_0, F_L) as follows:

- **States**: Q_L = { [x]_L : x in Sigma* }, so |Q_L| = n.
- **Initial state**: q_0 = [epsilon]_L.
- **Transition function**: delta_L([x]_L, a) = [xa]_L for each a in Sigma.
  This is well-defined: if [x]_L = [y]_L then x equiv_L y, so by
  right-invariance xa equiv_L ya, giving [xa]_L = [ya]_L.
- **Accepting states**: F_L = { [x]_L : x in L }.
  This is well-defined: if [x]_L = [y]_L then x equiv_L y, so (taking
  z = epsilon) x in L iff y in L.

For any string w = a_1 a_2 ... a_k, we have delta_L*(q_0, w) =
[a_1 a_2 ... a_k]_L = [w]_L. So M_L accepts w iff [w]_L in F_L iff w in L.

Moreover, M_L is *minimal*: any DFA for L has at least n states (by the
direction (1 => 2 => 3), the index of equiv_L lower-bounds the state count).
QED.

### 2.3  Concrete Grounding

The constructive direction (3 => 1) is realized by `minimize_dfa()` at
`automata/minimize.rs:95`. The implementation uses Hopcroft-style partition
refinement:

1. **Initial partition** (line 131): States are grouped by their acceptance
   signature -- (accepting, weight, alt_accepts). This is the initial
   approximation: two states in different groups are already distinguished.

2. **Worklist refinement** (lines 159--200+): For each (partition, equivalence
   class) splitter pair, the algorithm checks whether any existing block
   contains states that differ on transitions through that class. If so, the
   block is split, producing finer partitions.

3. **Convergence**: The algorithm terminates when no block can be split. At
   this point, each block corresponds to exactly one Nerode equivalence class
   [x]_L. The number of blocks equals the index of equiv_L.

4. **DFA construction**: Each converged block becomes a single state in the
   minimal DFA. Transitions are inherited from any representative state in
   each block (well-defined because all states in a block agree on
   transitions modulo the partition).

The bitset-based `partition_seen` tracking (Sprint 2 of performance
optimization) replaces a linear scan with word-level bitmask operations,
achieving O(n log n) time complexity via Hopcroft's algorithm rather than the
naive O(n^2) refinement.

---

## 3  Weighted Automata over Semirings

Classical finite automata answer a binary question: "Does the string belong to
the language?" Weighted automata generalize this by assigning a *weight* from
a semiring to each computation, enabling quantitative reasoning about
priorities, costs, probabilities, and ambiguity.

### 3.1  Weighted Finite Automaton

**Definition 3.1 (Weighted Finite Automaton).** A *weighted finite automaton*
(WFA) over a semiring (K, direct_sum, direct_product, zero_bar, one_bar) is a
5-tuple A = (Q, Sigma, delta, I, F) where:

- Q is a finite set of states.
- Sigma is a finite input alphabet.
- delta: Q x Sigma x Q -> K assigns a weight to each transition.
- I: Q -> K assigns an initial weight to each state.
- F: Q -> K assigns a final weight to each state.

**Definition 3.2 (Path Weight).** The weight of a path
pi = q_0 --(a_1)--> q_1 --(a_2)--> ... --(a_n)--> q_n is:

    w(pi) = I(q_0) ⊗ delta(q_0, a_1, q_1) ⊗ delta(q_1, a_2, q_2) ⊗ ... ⊗ delta(q_{n-1}, a_n, q_n) ⊗ F(q_n)

**Definition 3.3 (String Weight).** The weight assigned to a string
x in Sigma* is the semiring sum over all accepting paths for x:

    w_A(x) = ⊕_{pi in Paths(x)} w(pi)

where Paths(x) is the set of all paths in A that spell x.

**Theorem 3.4 (Subsumption).** A classical DFA is a WFA over the Boolean
semiring ({true, false}, or, and, false, true), where:

- I(q_0) = true, I(q) = false for q != q_0
- F(q) = true iff q in F, false otherwise
- delta(p, a, q) = true iff the DFA has transition (p, a) -> q

Then w_A(x) = true iff x in L(A).

*Proof.* By definition, w(pi) = true iff every transition along pi exists
(all and-factors are true) and the path starts from q_0 and ends in an
accepting state. The or-sum over all paths is true iff at least one accepting
path exists, which is exactly the DFA acceptance condition. QED.

### 3.2  PraTTaIL's Semiring Instantiations

PraTTaIL's `Semiring` trait (`automata/semiring.rs:36`) makes the automaton
parametric over the weight domain K. The same DFA topology is evaluated over
different semirings for different analyses:

| Setting        | K                           | ⊕           | ⊗ | Interpretation   | PraTTaIL Use                           |
|----------------|-----------------------------|-------------|---|------------------|----------------------------------------|
| Classical DFA  | `BooleanWeight` (line 301)  | ∨           | ∧ | Acceptance       | `is_accepting` bitmap (codegen.rs:426) |
| Priority lexer | `TropicalWeight` (line 69)  | min         | + | Best priority    | Weighted dispatch (dispatch.rs)        |
| Path counting  | `CountingWeight` (line 219) | +           | x | Derivation count | Ambiguity detection (pipeline.rs)      |
| Edit distance  | `EditWeight` (line 385)     | min         | + | Repair cost      | Error recovery (recovery.rs)           |
| Probabilistic  | `LogWeight` (line 916)      | log-sum-exp | + | Log-probability  | Forward-backward (wfst-log feature)    |

**Concrete Grounding**: Each semiring serves a distinct role in the pipeline:

- **BooleanWeight**: Dead-rule detection in `pipeline.rs`. A rule whose token
  pattern has w_A(x) = false (the zero element) for all reachable x is
  provably dead and triggers a lint warning.

- **TropicalWeight**: Weighted dispatch in `dispatch.rs`. When multiple token
  rules match, the one with minimal tropical weight (highest priority) wins.
  The min-plus structure ensures that the shortest-path (highest-priority)
  interpretation is selected.

- **CountingWeight**: Ambiguity warnings in `pipeline.rs`. If the path count
  for a token position exceeds 1, the grammar is ambiguous at that point.
  Note: CountingWeight is not Viterbi-compatible because its zero element (0)
  is the smallest value under the natural ordering.

- **EditWeight**: Error recovery in `recovery.rs`. Repair actions (insert,
  delete, substitute) are assigned edit costs, and the recovery engine selects
  the minimum-cost repair sequence.

- **LogWeight**: Training and parameter estimation under the `wfst-log`
  feature gate. The log-semiring supports the forward-backward algorithm for
  computing expected counts over all paths.

### 3.3  Weighted Finite-State Transducers

**Definition 3.5 (WFST).** A *weighted finite-state transducer* over semiring
K is a WFA extended with an output alphabet Gamma and output labels on
transitions: delta: Q x (Sigma union {epsilon}) x (Gamma union {epsilon}) x Q -> K.

PraTTaIL's `PredictionWfst` (`wfst.rs:236`) instantiates this with:

- **Input labels**: Token types (lexer output).
- **Output labels**: Grammar rule predictions (parser expectations).
- **Weights**: TropicalWeight encoding rule priorities.

The composition of the lexer WFST with the prediction WFST yields a
single transducer that maps character sequences directly to weighted grammar
rule predictions, enabling the parser to make priority-informed decisions
before full parsing.

```
                    ┌─────────────┐           ┌──────────────────┐
  characters ──────>│  Lexer DFA  │──tokens──>│  PredictionWfst  │──rule predictions──>
                    │  (Type 3)   │           │  (WFST)          │
                    └─────────────┘           └──────────────────┘
```

---

## 4  References

1. Hopcroft, J. E. & Ullman, J. D. (1979). *Introduction to Automata Theory,
   Languages, and Computation*. Addison-Wesley.
2. Myhill, J. (1957). "Finite automata and the representation of events."
   WADD TR-57-624.
3. Nerode, A. (1958). "Linear automaton transformations." *Proceedings of the
   AMS*, 9(4), 541--544.
4. Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted
   Automata*. Springer.
5. Chomsky, N. (1956). "Three models for the description of language."
   *IRE Transactions on Information Theory*, 2(3), 113--124.
6. Mohri, M. (2009). "Weighted automata algorithms." In *Handbook of Weighted
   Automata*, Ch. 6. Springer.
