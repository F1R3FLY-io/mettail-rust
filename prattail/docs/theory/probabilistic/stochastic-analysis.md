# Probabilistic Automata and Stochastic Analysis — Theoretical Foundations

## Motivation

Grammar disambiguation, error recovery ranking, and training-based weight learning all require **probabilistic reasoning**: computing the likelihood of parse derivations, finding the most probable parse (Viterbi), measuring uncertainty (entropy), and learning transition probabilities from data (Baum-Welch). **Probabilistic automata** provide the mathematical framework for these tasks, operating in the **log-probability domain** for numerical stability.

**Core question**: How can we assign, compute, and learn probability distributions over parse derivations to enable disambiguation, ranking, and adaptive optimization?

**Historical context**: Rabin (1963) introduced probabilistic automata. Rabiner (1989) provided the foundational tutorial on Hidden Markov Models (HMMs) and the forward, backward, and Baum-Welch algorithms. Mohri (2009) unified these algorithms within the weighted automata framework, showing that the forward algorithm is a semiring shortest-distance computation, Viterbi is the tropical-semiring variant, and entropy uses the expectation semiring.

**Connection to the Chomsky hierarchy**: Probabilistic finite automata (PFA) define distributions over regular languages. Probabilistic context-free grammars (PCFG) extend this to context-free languages. The forward/backward algorithms for PFA are the finite-state specialization of the inside/outside algorithms for PCFG.

## Definitions

**Definition 7.1** (Probabilistic Automaton). A **probabilistic automaton** (PA) is a tuple M = (Q, Σ, δ, π, η) where:
- Q = {q₁, ..., q_n} is a finite set of states
- Σ is the input alphabet
- δ : Q × Σ × Q → [0, 1] is the transition probability function with ∑_{q'∈Q} δ(q, a, q') ≤ 1 for all q, a
- π : Q → [0, 1] is the initial distribution with ∑_{q∈Q} π(q) = 1
- η : Q → [0, 1] is the accepting weight function

The **probability of a word** w = a₁...aₙ is:
    P(w) = ∑_{q₀,...,qₙ} π(q₀) · ∏_{i=0}^{n-1} δ(qᵢ, aᵢ₊₁, qᵢ₊₁) · η(qₙ)

*Intuition*: A probabilistic automaton is an HMM where the observation symbols are the input. The probability of a word is the sum over all possible state sequences of the product of transition probabilities, weighted by initial and accepting probabilities.

**Definition 7.2** (Log-Domain Representation). MeTTaIL represents probabilities in the **negative log domain** using `LogWeight`:
- A probability p ∈ (0, 1] is stored as −ln(p) ∈ [0, ∞)
- `LogWeight::zero()` = +∞ (probability 0)
- `LogWeight::one()` = 0.0 (probability 1)
- `times(a, b)` = a + b (probability multiplication: ln(p·q) = ln(p) + ln(q))
- `plus(a, b)` = −ln(exp(−a) + exp(−b)) (log-sum-exp for probability addition)

*Intuition*: Working in log-domain prevents underflow when multiplying many small probabilities. The log-sum-exp operation is numerically stable and preserves the semiring axioms.

*Example*: In `ProbabilisticAutomaton`, `transitions[q]` contains `(target, symbol, LogWeight)` triples. `LogWeight::new(0.0)` means probability 1; `LogWeight::new(2.3)` means probability e^{−2.3} ≈ 0.1.

**Definition 7.3** (Forward Variable). The **forward variable** α_t(q) is the total probability of being in state q after reading the first t symbols:
    α₀(q) = π(q)
    α_{t+1}(j) = ∑_i α_t(i) · δ(i, w_{t+1}, j)

The total probability of the word is: P(w) = ∑_j α_T(j) · η(j)

In log-domain: α values are `LogWeight`, ∑ becomes `logsumexp`, · becomes `+`.

**Definition 7.4** (Backward Variable). The **backward variable** β_t(q) is the total probability of generating the remaining symbols w_{t+1}...w_T from state q:
    β_T(q) = η(q)
    β_t(i) = ∑_j δ(i, w_{t+1}, j) · β_{t+1}(j)

**Definition 7.5** (Entropy). The **Shannon entropy** of the distribution over words defined by a probabilistic automaton measures the average surprise:
    H(M) = −∑_w P(w) · ln P(w)

Using the **expectation semiring** `EntropyWeight = (p, p·ln(p))`, entropy can be computed via a single forward pass.

## Key Theorems

**Theorem 7.1** (Forward Algorithm Correctness; Rabiner, 1989, Equation 19):
The forward algorithm computes P(w | M) = ∑_{q∈Q} α_T(q) · η(q) in O(T · |Q|²) time and O(|Q|) space (single time step retained).

*Intuition*: Rather than summing over all O(|Q|^T) possible state sequences (exponential), the forward algorithm uses dynamic programming: at each time step, it aggregates all paths leading to each state, reducing the computation to O(T · |Q|²).

*Proof sketch*: By induction on t. Base case: α₀(q) = π(q), which is correct by definition. Inductive step: α_{t+1}(j) = ∑_i α_t(i) · δ(i, w_{t+1}, j). By the inductive hypothesis, α_t(i) is the total probability of reaching state i in t steps. Multiplying by δ(i, w_{t+1}, j) and summing over all predecessors i gives the total probability of reaching j in t+1 steps.

*Consequence for MeTTaIL*: The `probability_of()` method implements the forward algorithm in log-domain using `LogWeight`. The `backward()` method computes backward variables for use in Baum-Welch training.

*Reference*: Rabiner, L.R. (1989). "A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition." *Proceedings of the IEEE*, 77(2), pp. 257–286. Equation 19.

**Theorem 7.2** (Viterbi as Tropical Forward; Mohri, 2009, Section 4.2):
The Viterbi algorithm (finding the most probable state sequence) is equivalent to the forward algorithm over the **tropical semiring** (min-plus), where `plus = min` and `times = +`. The result is the weight of the best (minimum-cost) path.

*Intuition*: Where the forward algorithm sums probabilities (log-sum-exp), Viterbi takes the minimum (in log-domain, minimum = most probable). The optimal path can be recovered by backtracking through the argmin at each step.

*Consequence for MeTTaIL*: The `viterbi()` method uses `TropicalWeight` arithmetic for the forward pass, then backtracks to recover the optimal state sequence. This enables "best parse" selection for disambiguation.

*Reference*: Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213–254. Springer. Section 4.2.

**Theorem 7.3** (Baum-Welch Convergence; Baum, 1972):
The Baum-Welch (EM) algorithm for estimating probabilistic automaton parameters converges to a local maximum of the log-likelihood function. Each iteration is guaranteed to increase (or maintain) the log-likelihood: ℒ(θ^{(t+1)}) ≥ ℒ(θ^{(t)}).

*Intuition*: Baum-Welch alternates between computing expected counts (E-step, using forward-backward) and re-estimating parameters (M-step, normalizing counts). By the EM theorem, each iteration increases the data log-likelihood.

*Proof sketch*: The auxiliary function Q(θ, θ') = E_{θ'}[ln P(w, z | θ)] (expected complete-data log-likelihood) satisfies: Q(θ^{(t+1)}, θ^{(t)}) ≥ Q(θ^{(t)}, θ^{(t)}) by the M-step maximization. By Jensen's inequality, this implies ℒ(θ^{(t+1)}) ≥ ℒ(θ^{(t)}).

*Consequence for MeTTaIL*: The `train_from_corpus()` method implements Baum-Welch EM, iterating until convergence (log-likelihood change < ε) or a maximum number of iterations. The `PR03` lint reports convergence statistics.

*Reference*: Baum, L.E. (1972). "An Inequality and Associated Maximization Technique in Statistical Estimation for Probabilistic Functions of Markov Chains." *Inequalities*, 3, pp. 1–8.

**Theorem 7.4** (Selectivity via Matrix Star; Mohri, 2009):
The total probability mass of a probabilistic automaton (selectivity) can be computed via the matrix Kleene star of the transition matrix. For a normalized PA, selectivity ≤ 1; a value significantly below 1 indicates that many paths lead to non-accepting states.

*Consequence for MeTTaIL*: The `selectivity()` method computes the total mass via matrix star closure. Rules with low selectivity trigger the `PR01` lint, flagging them as effectively dead despite structural reachability.

*Reference*: Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213–254. Springer.

## Algorithms

### Algorithm 1: Forward Algorithm (Log-Domain)

```
PROCEDURE FORWARD(M, word = a₁...a_T)
  INPUT:  Probabilistic automaton M, word
  OUTPUT: P(word | M) as LogWeight

  1. α[q] ← π(q) for all q ∈ Q          // initial distribution
  2. For t = 1 to T:
     α'[j] ← LogWeight::zero() for all j
     For each state i with α[i] ≠ zero:
       For each transition (i, aₜ, j, w):
         α'[j] ← logsumexp(α'[j], α[i] + w)   // LogWeight::plus
     α ← α'
  3. total ← LogWeight::zero()
     For each accepting state q:
       total ← logsumexp(total, α[q] + η(q))
  4. Return total

  COMPLEXITY: O(T · |Q|² · |Σ|) time, O(|Q|) space
```

### Algorithm 2: Viterbi (Tropical Domain)

```
PROCEDURE VITERBI(M, word = a₁...a_T)
  INPUT:  Probabilistic automaton M, word
  OUTPUT: Best state sequence and its weight

  1. v[q] ← π(q) for all q             // TropicalWeight (min)
     back[0][q] ← None
  2. For t = 1 to T:
     v'[j] ← TropicalWeight::zero() (+∞) for all j
     For each (i, aₜ, j, w):
       candidate ← v[i] + w
       If candidate < v'[j]:
         v'[j] ← candidate
         back[t][j] ← i
     v ← v'
  3. q* ← argmin_q(v[q] + η(q))        // best final state
  4. Backtrack: path ← [q*]
     For t = T down to 1:
       path.prepend(back[t][path[0]])
  5. Return (path, v[q*] + η(q*))

  COMPLEXITY: O(T · |Q|² · |Σ|) time, O(T · |Q|) space (backpointers)
```

### Algorithm 3: Baum-Welch (EM Training)

```
PROCEDURE BAUM-WELCH(M, corpus, max_iter, ε)
  INPUT:  Initial PA M, training corpus, convergence params
  OUTPUT: Re-estimated PA M'

  Repeat until convergence:
    // E-step: compute expected counts
    For each word w in corpus:
      α ← forward_trellis(M, w)
      β ← backward(M, w)
      P_w ← Σ_q α[T][q] · η(q)

      For each transition (i, a, j, w_t):
        ξ_t(i,j) ← α[t][i] · w_t · β[t+1][j] / P_w
        expected_count(i,a,j) += Σ_t ξ_t(i,j)

    // M-step: normalize expected counts
    For each state i, symbol a:
      δ(i, a, j) ← expected_count(i,a,j) / Σ_{j'} expected_count(i,a,j')

    // Check convergence
    LL ← Σ_w ln P(w)
    If |LL - LL_prev| < ε: break

  Return M with updated parameters
```

## Decidability Analysis

| Property | Complexity | Tier |
|----------|-----------|------|
| P(w) computation | O(\|w\| · \|Q\|²) | T1 |
| Best path (Viterbi) | O(\|w\| · \|Q\|²) | T1 |
| Entropy | O(\|Q\|³) (matrix star) | T1 |
| Selectivity | O(\|Q\|³) (matrix star) | T1 |
| PA equivalence | Undecidable (Condon & Lipton, 1989) | T4 |
| PA emptiness (P(w) > 0) | Decidable (graph reachability) | T1 |
| Baum-Welch convergence | Local max guaranteed | T1 (convergence), T3 (global opt) |

**Boundary cases**: PA equivalence is undecidable because checking whether two PAs define the same distribution reduces to the emptiness problem for probabilistic automata with cutpoints, which is undecidable. However, approximate equivalence testing via sampling is T2.

## Diagrams

### Forward Algorithm Trellis

```
Word: a b a

Time:    0         1         2         3
       ┌───┐  a  ┌───┐  b  ┌───┐  a  ┌───┐
State  │q₀ │────▶│q₀ │────▶│q₀ │────▶│q₀ │ → η(q₀)
  q₀   │α₀₀│    │α₁₀│    │α₂₀│    │α₃₀│
       └───┘    └─┬─┘    └───┘    └───┘
         │    ╱   │  ╲       │
         ▼  ╱     ▼    ╲     ▼
       ┌───┐  a  ┌───┐  b  ┌───┐  a  ┌───┐
State  │q₁ │────▶│q₁ │────▶│q₁ │────▶│q₁ │ → η(q₁)
  q₁   │α₀₁│    │α₁₁│    │α₂₁│    │α₃₁│
       └───┘    └───┘    └───┘    └───┘

Each α = logsumexp of (predecessor α + transition weight)
P(aba) = logsumexp(α₃₀ + η(q₀), α₃₁ + η(q₁))
```

### Log-Domain vs. Probability Domain

```
Probability domain:         Log-domain (MeTTaIL):
  p₁ · p₂ · p₃               w₁ + w₂ + w₃
  = 0.01 × 0.02 × 0.03       = 4.6 + 3.9 + 3.5
  = 0.000006                  = 12.0
  (underflow risk!)           (no underflow)

  p₁ + p₂                    logsumexp(w₁, w₂)
  = 0.01 + 0.02              = -ln(e^{-4.6} + e^{-3.9})
  = 0.03                     = 3.5
  (exact)                    (numerically stable)
```

### Semiring Correspondence

```
  ┌──────────────┬───────────┬───────────────┬──────────────┐
  │   Task       │ Semiring  │  ⊕ (plus)     │  ⊗ (times)   │
  ├──────────────┼───────────┼───────────────┼──────────────┤
  │ Total prob.  │ LogWeight │ logsumexp     │ addition     │
  │ Best path    │ Tropical  │ min           │ addition     │
  │ Entropy      │ Entropy   │ (p+q, H_p+H_q)│ (p·q, ...)  │
  │ Count paths  │ Counting  │ addition      │ multiplication│
  │ Reachability │ Boolean   │ OR            │ AND          │
  └──────────────┴───────────┴───────────────┴──────────────┘
```

## Connections

**To WFST module**: The forward algorithm in `probability_of()` is a specialization of the generic semiring forward pass to LogWeight. The `forward_backward.rs` module provides the general framework for DAG-based computation; `probabilistic.rs` provides labeled-automaton-specific implementations.

**To Training module**: `train_from_corpus()` implements Baum-Welch EM for structure-free probabilistic automata. The `training.rs` module provides grammar-aware SGD training. The two can be composed: Baum-Welch for lexer-level distributions, SGD for parser-level rule weights.

**To Module 4 (VPA)**: Weighted VPA with LogWeight enables probabilistic parsing of nested structures. The VPA's visible stack discipline ensures that the probability model remains well-defined despite recursion.

**To Lint module**: The probabilistic analysis produces four lint codes: PR01 (low selectivity), PR02 (high entropy), PR03 (convergence report), PR04 (non-normalized automaton).

**Open problems**:
1. **Spectral learning**: Parameter estimation without EM via the method of moments (Hsu, Kakade & Zhang, 2012). Avoids local optima but requires careful rank estimation.
2. **Bayesian probabilistic automata**: Posterior inference over PA parameters for uncertainty quantification.
3. **Online training**: Incremental Baum-Welch for streaming data (update parameters as new training examples arrive).

## Bibliography

1. Rabiner, L.R. (1989). "A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition." *Proceedings of the IEEE*, 77(2), pp. 257–286.

2. Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213–254. Springer.

3. Baum, L.E. (1972). "An Inequality and Associated Maximization Technique in Statistical Estimation for Probabilistic Functions of Markov Chains." *Inequalities*, 3, pp. 1–8.

4. Rabin, M.O. (1963). "Probabilistic Automata." *Information and Control*, 6(3), pp. 230–245.

5. Condon, A. & Lipton, R.J. (1989). "On the Complexity of Space Bounded Interactive Proofs." *FOCS*, pp. 462–467. IEEE.

6. Hsu, D., Kakade, S.M. & Zhang, T. (2012). "A Spectral Algorithm for Learning Hidden Markov Models." *J. Computer and System Sciences*, 78(5), pp. 1460–1480.
