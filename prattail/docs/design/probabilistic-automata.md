# Probabilistic Automata -- Statistical Analysis, Disambiguation, and Training

## Quick Start

Probabilistic automata provide statistical analysis of parse grammars in the log-probability domain. All weights use `LogWeight` (negative log-probability space), where `plus = log-sum-exp` (probability addition) and `times = addition` (probability multiplication), ensuring numerical stability for long sequences and very small probabilities. The module provides `ProbabilisticAutomaton` with operations: `probability_of()` (forward algorithm), `viterbi()` (best-path decoding), `entropy()` (Shannon entropy via `EntropyWeight`), `selectivity()` (total language weight via matrix star closure), and `train_from_corpus()` (Baum-Welch EM parameter estimation).

**Motivating example**: Given ambiguous grammar rules, the probabilistic automaton assigns probabilities to alternative parses. The Viterbi algorithm selects the most likely parse, while entropy quantifies the degree of ambiguity at each dispatch point.

```
Grammar rules + corpus
      |
      v
ProbabilisticAutomaton
      |
      +---> normalize()            (per-state weight normalization)
      +---> probability_of(word)   (forward algorithm -> LogWeight)
      +---> viterbi(word)          (best path -> (TropicalWeight, Vec<usize>))
      +---> entropy()              (Shannon entropy -> f64 nats)
      +---> selectivity()          (total weight -> LogWeight)
      +---> train_from_corpus()    (Baum-Welch EM)
```

## Intuition

Think of a probabilistic automaton as a weather forecaster with multiple prediction models (states). Each model transitions to another based on observed weather symbols (sunny, rainy, etc.), with probabilities on each transition. The forward algorithm computes the total probability of a weather sequence under all models. The Viterbi algorithm finds the single most likely sequence of models. Entropy measures how uncertain the forecaster is at each step.

**Before this module**: Grammar disambiguation relied on hand-tuned priority rules without statistical grounding. There was no systematic way to learn rule weights from data.

**After this module**: Rule probabilities are learned from corpora via Baum-Welch EM. Entropy analysis identifies high-ambiguity dispatch points. Selectivity analysis identifies rules with negligible probability mass.

**Key insight**: Operating in the log domain (negative log-probabilities) avoids numerical underflow for long sequences. The `LogWeight` semiring's `plus = log-sum-exp` provides numerically stable probability summation, while `times = addition` gives stable probability multiplication.

## Theoretical Foundations

**Definition 7.1 (Probabilistic Automaton).** A probabilistic automaton is `M = (Q, Sigma, delta, pi, F)` where:
- `Q = {q_0, ..., q_{n-1}}` is the state set
- `Sigma` is the alphabet (input symbols)
- `delta: Q x Sigma -> dist(Q)` maps each state-symbol pair to a distribution over successor states, with weights in `LogWeight`
- `pi in dist(Q)` is the initial distribution
- `F: Q -> LogWeight` maps accepting states to acceptance weights

**Definition 7.2 (Forward Algorithm).** The forward score `alpha[t][q]` is the total probability of all paths from the initial distribution to state `q` after consuming `t` symbols:

```
alpha[0][q] = pi[q]
alpha[t+1][j] = logsumexp_i( alpha[t][i] + delta(i, w[t], j) )
P(w) = logsumexp_j( alpha[T][j] + F[j] )
```

where `+` denotes `LogWeight::times` (addition in log space) and `logsumexp` denotes `LogWeight::plus`.

**Definition 7.3 (Viterbi Algorithm).** The Viterbi score `delta[t][q]` is the minimum-cost (maximum-probability) path:

```
delta[0][q] = pi[q]                (as TropicalWeight)
delta[t+1][j] = min_i( delta[t][i] + trop_delta(i, w[t], j) )
best = min_j( delta[T][j] + trop_F[j] )
```

Backtracking recovers the optimal state sequence.

**Definition 7.4 (Shannon Entropy).** The entropy `H = -sum_w P(w) ln P(w)` is computed via the `EntropyWeight` (expectation semiring) using iterative matrix star closure:

```
x_new[i] = accept[i] + sum_j A[i][j] * x[j]
```

This converges to `x = A* * accept` for contractive automata.

**Theorem 7.1 (Baum-Welch EM, Rabiner 1989).** The Baum-Welch algorithm iterates E-step (compute expected transition counts from forward-backward scores) and M-step (re-estimate parameters from counts), monotonically increasing the log-likelihood `sum_w ln P(w)` until convergence.

## Activation: ≥3 Same-Category Rules → M7

M7 (Probabilistic) is activated by predicate dispatch when the grammar or its
predicates indicate parse ambiguity requiring statistical disambiguation.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features()
      │                                 │
      ▼                                 ▼
CategoryAmbiguity(≥3)            MultiGuard (≥2 channels)
  ≥3 rules in same category        Multi-guard conjunction
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M7_PROBABILISTIC bit set
```

**Grammar heuristic**: When a category has ≥3 alternative rules, parse ambiguity is
likely. Two rules represent a simple binary choice (often deterministic from lookahead);
three or more alternatives create genuine ambiguity that benefits from statistical
ranking to select the most likely parse.

**Predicate trigger**: When ≥2 distinct channels are referenced in a predicate's
channel context, multi-guard selectivity ordering benefits from probabilistic weights.

**Example grammar rule set triggering M7**:
```
("Add", "Expr", [Terminal("+")]),
("Sub", "Expr", [Terminal("-")]),
("Mul", "Expr", [Terminal("*")])
   ↑ 3 rules in "Expr" → ambiguity → M7 activated
```

**Theoretical justification**: Multiple rules in the same category create parse
ambiguity. Statistical disambiguation via probabilistic weights (Viterbi decoding,
entropy analysis, Baum-Welch training) provides principled ranking of alternatives,
selecting the most likely parse from corpus statistics rather than arbitrary choice.

## Design

### Core types

```rust
pub struct ProbabilisticState {
    pub id: usize,
    pub label: Option<String>,
}

pub struct ProbabilisticAutomaton {
    pub states: Vec<ProbabilisticState>,
    pub alphabet: HashSet<String>,
    pub transitions: Vec<Vec<(usize, Option<String>, LogWeight)>>,
    pub initial_distribution: Vec<LogWeight>,
    pub accepting_weights: HashMap<usize, LogWeight>,
    pub is_normalized: bool,
}
```

### Semiring pipeline diagram

```
  Operation          Semiring         Algorithm
  +-----------+      +---------+     +------------------+
  | P(word)   | ---> | LogWeight| --> | Forward           |
  | best path | ---> | Tropical | --> | Viterbi           |
  | entropy   | ---> | Entropy  | --> | Matrix star       |
  | selectivity| --> | LogWeight| --> | Matrix star       |
  | training  | ---> | LogWeight| --> | Baum-Welch EM     |
  +-----------+      +---------+     +------------------+
```

## Algorithms

### Forward Algorithm

```
Input:  ProbabilisticAutomaton, word[0..T]
Output: LogWeight (total probability)

1. alpha[q] = initial_distribution[q] for all q
2. For t = 0 to T-1:
   alpha_next[j] = LogWeight::zero() for all j
   For each (from, to, label, w) in transitions:
     If label matches word[t] and alpha[from] not zero:
       alpha_next[to] ⊕= alpha[from] ⊗ w
   alpha = alpha_next
3. result = ⊕_j (alpha[j] ⊗ accepting_weights[j])
4. Return result
```

**Complexity**: O(|w| * |Q| * |delta|).

### Viterbi Algorithm

```
Input:  ProbabilisticAutomaton, word[0..T]
Output: (TropicalWeight, Vec<usize>)

1. delta[q] = TropicalWeight(initial_distribution[q].value()) for all q
2. backpointers = []
3. For t = 0 to T-1:
   delta_next[j] = TropicalWeight::zero() for all j
   bp[j] = 0 for all j
   For each (from, to, label, w) in transitions:
     If label matches word[t] and delta[from] not zero:
       cost = delta[from].value() + w.value()
       If cost < delta_next[to].value():
         delta_next[to] = TropicalWeight(cost)
         bp[to] = from
   backpointers.push(bp)
   delta = delta_next
4. best_state = argmin_j (delta[j].value() + trop_accept[j].value())
5. Backtrack through backpointers to recover path
6. Return (best_cost, path)
```

**Complexity**: O(|w| * |Q| * |delta|).

### Entropy via Expectation Semiring

```
Input:  ProbabilisticAutomaton
Output: f64 (entropy in nats)

1. Build n x n adjacency matrix in EntropyWeight:
   adj[i][j] = ⊕ over transitions i -> j of EntropyWeight(w, w)
2. x[j] = EntropyWeight(accept[j], 0.0) for accepting states
3. Fixpoint: x_new[i] = accept[i] + sum_j adj[i][j] * x[j]
   Iterate until convergence (eps = 1e-10, max 200 iterations)
4. total = sum_i init_ew[i] * x[i]
5. Return total.expectation()
```

**Complexity**: O(|Q|^2 * max_iter).

### Baum-Welch EM Training

```
Input:  ProbabilisticAutomaton, corpus, max_iterations, tolerance
Output: (updates automaton weights in place)

For each iteration:
  E-step:
    For each word in corpus:
      Compute forward trellis alpha[t][q]
      Compute backward trellis beta[t][q]
      P(word) = logsumexp_q(alpha[T][q] + accept[q])
      gamma(t, i) = alpha[t][i] * beta[t][i] / P(word)
      xi(t, i, j, a) = alpha[t][i] * w(i,a,j) * beta[t+1][j] / P(word)
      Accumulate expected counts (in probability space)
  M-step:
    P_new(j, a | i) = sum_words xi(t,i,j,a) / sum_words gamma(t,i)
    Update initial distribution from gamma(0, q) counts
  Convergence: stop if |LL_new - LL_old| < tolerance
```

**Complexity**: O(iterations * |corpus| * |w_max| * |Q|^2).

## Integration

- **Forward-backward module** (`forward_backward.rs`): The forward algorithm here is a specialization of the generic semiring forward pass to `LogWeight`.
- **Training module** (`training.rs`): `train_from_corpus()` complements grammar-aware SGD training -- Baum-Welch learns lexer-level token distributions, SGD learns parser-level rule weights.
- **Pipeline** (`pipeline.rs`): `ProbabilisticAnalysis` reports selectivity, entropy, and low-selectivity rules.
- **WFST module** (`wfst.rs`): Probabilistic weights feed into the WFST lattice for weighted disambiguation.

## Diagnostics

| Code | Severity | Description |
|------|----------|-------------|
| PR01 | Warning | Low-selectivity rule: `selectivity < 0.01` (effectively dead) |
| PR02 | Note | High-entropy dispatch: `entropy > 3.0 bits` (high ambiguity) |
| PR03 | Info | Convergence report: Baum-Welch converged after k iterations |
| PR04 | Warning | Non-normalized automaton: transition weights do not sum to 1.0 |

## Examples

### Example 1: Forward probability computation

```rust
let mut pa = ProbabilisticAutomaton::new();
let q0 = pa.add_state(Some("start".into()));
let q1 = pa.add_state(Some("end".into()));
pa.set_initial(q0, LogWeight::new(0.0));  // P(start) = 1.0
pa.set_accepting(q1, LogWeight::new(0.0)); // accept with P = 1.0
pa.add_transition(q0, Some("a".into()), q1, LogWeight::new(0.5)); // P = e^{-0.5}
pa.normalize();

let prob = pa.probability_of(&["a"]);
// prob encodes -ln(P("a")) in log domain
```

### Example 2: Viterbi best path

```rust
let mut pa = ProbabilisticAutomaton::new();
let q0 = pa.add_state(None);
let q1 = pa.add_state(None);
let q2 = pa.add_state(None);
pa.set_initial(q0, LogWeight::new(0.0));
pa.set_accepting(q1, LogWeight::new(0.0));
pa.set_accepting(q2, LogWeight::new(0.0));
pa.add_transition(q0, Some("x".into()), q1, LogWeight::new(1.0)); // cost 1.0
pa.add_transition(q0, Some("x".into()), q2, LogWeight::new(0.5)); // cost 0.5

let (cost, path) = pa.viterbi(&["x"]);
// cost = TropicalWeight(0.5) -- cheaper path through q2
// path = [0, 2] -- started at q0, ended at q2
```

### Example 3: Baum-Welch training

```rust
let mut pa = ProbabilisticAutomaton::new();
// ... (configure states and initial transitions)

let corpus = vec![
    vec!["a".to_string(), "b".to_string()],
    vec!["a".to_string(), "a".to_string()],
    vec!["b".to_string(), "a".to_string()],
];

pa.train_from_corpus(&corpus, 100, 1e-6);
assert!(pa.is_normalized);
// Transition weights now reflect corpus statistics
```

## Advanced Topics

**Edge cases**: An automaton with no states returns `LogWeight::zero()` for all operations. The `normalize()` method skips states with no outgoing transitions (zero probability mass). Empty words contribute only to the initial + accepting weight product.

**Interaction with other modules**: The probabilistic automaton feeds entropy analysis to the lint module (PR02) and selectivity to dead-rule detection (PR01). The `EntropyWeight` semiring from the semiring module enables Shannon entropy computation.

**Performance**: Forward and Viterbi are linear in word length and quadratic in states. Entropy and selectivity converge in O(200) iterations for well-conditioned automata. Baum-Welch training is the bottleneck at O(iterations * corpus_size * word_length * states^2).

**Numerical stability**: All computations use `LogWeight` (negative log-probabilities). The `log-sum-exp` operation prevents underflow that would occur with direct probability multiplication. The Baum-Welch E-step converts to probability space only for the expected-count accumulation.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `normalize()` | `&mut self` | `()` | O(\|Q\| * \|delta\|) |
| `probability_of(word)` | `&[&str]` | `LogWeight` | O(\|w\| * \|Q\| * \|delta\|) |
| `viterbi(word)` | `&[&str]` | `(TropicalWeight, Vec<usize>)` | O(\|w\| * \|Q\| * \|delta\|) |
| `entropy()` | `&self` | `f64` | O(\|Q\|^2 * max_iter) |
| `selectivity()` | `&self` | `LogWeight` | O(\|Q\|^2 * max_iter) |
| `train_from_corpus(...)` | corpus + params | `()` | O(iter * \|corpus\| * \|w\| * \|Q\|^2) |

### Lint codes

| Code | Severity | Description |
|------|----------|-------------|
| PR01 | Warning | Low-selectivity rule |
| PR02 | Note | High-entropy dispatch point |
| PR03 | Info | Convergence report |
| PR04 | Warning | Non-normalized automaton |

### Feature gate

`probabilistic-automata`

### Citations

- Rabiner, L.R. (1989). "A tutorial on hidden Markov models and selected applications in speech recognition." *Proceedings of the IEEE*, 77(2), 257--286.
- Mohri, M. (2009). "Weighted automata algorithms." In *Handbook of Weighted Automata*, Springer, 213--254.
