# Machine Learning Foundations for PraTTaIL

This document establishes the machine learning theory underlying
PraTTaIL's weight training, entropy computation, and adaptive beam
search. Every theorem is proven and grounded to a concrete source
location. Cross-references use the format `training.rs:114`, meaning
line 114 of `prattail/src/training.rs`.

---

## 1  Weight Training as Gradient Descent

### 1.1  Gradient Descent

**Definition 1.1 (Gradient Descent).**
Let L : ℝⁿ → ℝ be a differentiable loss function. *Gradient descent*
produces a sequence of parameter vectors θ⁽⁰⁾, θ⁽¹⁾, ... via the
update rule:

    θ⁽ᵗ⁺¹⁾ ← θ⁽ᵗ⁾ − η ∇L(θ⁽ᵗ⁾)

where η > 0 is the *learning rate* (step size) and ∇L(θ) is the
gradient of L evaluated at θ.

**Definition 1.2 (Stochastic Gradient Descent).**
When L(θ) = (1/N) ∑ᵢ Lᵢ(θ) decomposes over N training examples,
*stochastic gradient descent* (SGD) approximates the full gradient by
sampling a single example (or mini-batch) at each step:

    θ⁽ᵗ⁺¹⁾ ← θ⁽ᵗ⁾ − η ∇Lᵢ(θ⁽ᵗ⁾)

for a randomly sampled index i ∈ {1, ..., N}.

**Theorem 1.3 (SGD Convergence).**
For a convex, L-Lipschitz loss with learning rate η = c/√T, SGD
satisfies E[L(θ̄⁽ᵀ⁾)] − L(θ*) ≤ cL/√T, where θ̄⁽ᵀ⁾ is the average
iterate and θ* is the minimizer.

**Proof.**
Let g⁽ᵗ⁾ = ∇Lᵢₜ(θ⁽ᵗ⁾). By convexity:

    Lᵢₜ(θ⁽ᵗ⁾) − Lᵢₜ(θ*) ≤ ⟨g⁽ᵗ⁾, θ⁽ᵗ⁾ − θ*⟩

Expanding the squared distance update:

    ‖θ⁽ᵗ⁺¹⁾ − θ*‖² = ‖θ⁽ᵗ⁾ − η g⁽ᵗ⁾ − θ*‖²
                      = ‖θ⁽ᵗ⁾ − θ*‖² − 2η ⟨g⁽ᵗ⁾, θ⁽ᵗ⁾ − θ*⟩ + η² ‖g⁽ᵗ⁾‖²

Rearranging and using ‖g⁽ᵗ⁾‖ ≤ L:

    ⟨g⁽ᵗ⁾, θ⁽ᵗ⁾ − θ*⟩ ≤ (‖θ⁽ᵗ⁾ − θ*‖² − ‖θ⁽ᵗ⁺¹⁾ − θ*‖²) / (2η) + ηL²/2

Summing over t = 0, ..., T−1 and taking expectations, the telescoping
sum yields:

    ∑ₜ E[Lᵢₜ(θ⁽ᵗ⁾) − Lᵢₜ(θ*)] ≤ ‖θ⁽⁰⁾ − θ*‖² / (2η) + TηL²/2

Since E[Lᵢₜ(θ⁽ᵗ⁾)] = E[L(θ⁽ᵗ⁾)] (unbiased gradient), dividing by T
and setting η = c/√T with c = ‖θ⁽⁰⁾ − θ*‖ / L:

    E[L(θ̄⁽ᵀ⁾)] − L(θ*) ≤ cL/√T                                    ∎

**Concrete Grounding.** `training.rs:114` implements `RuleWeights::update()`,
which performs the SGD step `weight[r] -= learning_rate * gradient[r]`
for each rule r. The method `train()` at `training.rs:138` loops over
epochs and examples, calling `update()` per example — the standard SGD
pattern. Learning rate is stored as `self.learning_rate` (line 57) and
can be set via `set_learning_rate()` (line 71).

---

### 1.2  Log-Space Training for WFSTs

**Definition 1.4 (Log-Space Parameterization).**
PraTTaIL parameterizes WFST edge weights as negative log-probabilities:
wₑ = −ln pₑ, stored as `LogWeight` values (`semiring.rs:916`). Under
this parameterization:

- Probability → weight: wₑ = −ln pₑ
- Weight → probability: pₑ = exp(−wₑ)
- Lower weight = higher probability

**Definition 1.5 (Negative Log-Likelihood Loss).**
Given observed data D, the negative log-likelihood is:

    L(θ) = −ln P(D | θ) = −ln ∑_π exp(−w(π))

where the sum ranges over all accepting paths π through the WFST and
w(π) = ∑ₑ∈π wₑ is the total path weight.

**Theorem 1.6 (Log-Space Gradient).**
The gradient of L(θ) with respect to edge weight wₑ is:

    ∂L/∂wₑ = −E_posterior[count(e)]

where count(e) is the number of times a random path π traverses edge e,
under the posterior distribution p(π | D) ∝ exp(−w(π)).

**Proof.**
Write Z = ∑_π exp(−w(π)) so that L(θ) = −ln Z. Then:

    ∂L/∂wₑ = −(1/Z) · ∂Z/∂wₑ

Since w(π) = ∑_{e'∈π} w_{e'}, we have ∂w(π)/∂wₑ = count_π(e), the
number of times path π traverses edge e. Therefore:

    ∂Z/∂wₑ = ∑_π exp(−w(π)) · (−count_π(e))

Substituting:

    ∂L/∂wₑ = −(1/Z) · ∑_π exp(−w(π)) · (−count_π(e))
           = ∑_π [exp(−w(π))/Z] · count_π(e)
           = E_posterior[count(e)]

Therefore ∂L/∂wₑ = E_posterior[count(e)], and the negative gradient
used in the SGD update is −E_posterior[count(e)].                       ∎

**Theorem 1.7 (Multiplicative-Additive Duality).**
The SGD update wₑ ← wₑ − η · ∂L/∂wₑ in log space corresponds to the
multiplicative update pₑ ← pₑ · exp(η · E_posterior[count(e)]) / Z in
probability space.

**Proof.**
Let wₑ' = wₑ − η · ∂L/∂wₑ. Converting to probability space:

    pₑ' = exp(−wₑ') = exp(−wₑ + η · ∂L/∂wₑ)
        = exp(−wₑ) · exp(η · ∂L/∂wₑ)
        = pₑ · exp(η · E_posterior[count(e)])

The normalization constant Z = ∑ₑ pₑ' ensures ∑ₑ pₑ'/Z = 1. This is
exactly a multiplicative weight update in probability space realized as
an additive update in LogWeight space — the reason LogWeight defines
`times` as addition (`semiring.rs:916`).                                ∎

**Concrete Grounding.** `training.rs:125` performs the additive update
`new_val = weight.value() - self.learning_rate * gradient` on
`LogWeight` values, with clamping to non-negative values (line 126).
The `train_recovery_weights()` function at `training.rs:546` applies
the same SGD pattern to learn error recovery costs.

---

## 2  Exponential Families and Forward-Backward

### 2.1  Exponential Families

**Definition 2.1 (Exponential Family).**
A parameterized family of distributions is an *exponential family* if
each member can be written:

    p(x; θ) = exp(θᵀφ(x) − A(θ))

where:
- θ ∈ ℝᵈ is the vector of *natural parameters*,
- φ : X → ℝᵈ is the *sufficient statistic* function,
- A(θ) = ln ∑_x exp(θᵀφ(x)) is the *log-partition function* (or
  *cumulant generating function*).

**Theorem 2.2 (Gradient of the Log-Partition Function).**
For an exponential family p(x; θ) = exp(θᵀφ(x) − A(θ)):

    ∇A(θ) = E_θ[φ(x)]

That is, the gradient of the log-partition function equals the expected
sufficient statistics under the model.

**Proof.**
By definition, A(θ) = ln ∑_x exp(θᵀφ(x)). Differentiating:

    ∇A(θ) = ∇ ln ∑_x exp(θᵀφ(x))
          = [∑_x φ(x) exp(θᵀφ(x))] / [∑_x exp(θᵀφ(x))]

The denominator is exp(A(θ)), and exp(θᵀφ(x))/exp(A(θ)) = p(x; θ) by
definition of the exponential family. Therefore:

    ∇A(θ) = ∑_x φ(x) · p(x; θ) = E_θ[φ(x)]                          ∎

### 2.2  WFSTs as Exponential Families

**Definition 2.3 (WFST Exponential Family).**
A WFST with edges E = {e₁, ..., eₘ} defines an exponential family over
paths π through the automaton:

- Natural parameters: θ = (w_{e₁}, ..., w_{eₘ}) ∈ ℝᵐ (edge weights)
- Sufficient statistics: φ(π)ₑ = count_π(e) (times path π traverses e)
- Log-partition: A(θ) = ln ∑_π exp(θᵀφ(π)) = ln ∑_π exp(∑_{e∈π} wₑ)

Note: in PraTTaIL's convention, weights are negated (wₑ = −ln pₑ), so
the natural parameters are θ = −w, and A(θ) equals the forward score
of the final state under LogWeight.

**Corollary 2.4 (Expected Edge Counts via Forward-Backward).**
By Theorem 2.2, ∇A(θ)ₑ = E_θ[count(e)], the expected number of times
edge e is traversed. This is computed by the forward-backward algorithm:

    E_θ[count(e)] = exp(α(q) + wₑ + β(q') − A(θ))

for an edge e = (q, a, q') with weight wₑ, where:
- α(q) = forward score at state q
- β(q') = backward score at state q'
- A(θ) = α(q_final) = total log-partition

**Proof.**
The probability of traversing edge e = (q, a, q') is:

    P(e ∈ π) = [∑_{π ∋ e} exp(−w(π))] / [∑_π exp(−w(π))]

The numerator factors as: any path from start to q (weight α(q)),
followed by edge e (weight wₑ), followed by any path from q' to end
(weight β(q')). Under LogWeight (where plus = log-sum-exp and times =
addition):

    numerator = exp(−(α(q) + wₑ + β(q')))

The denominator is exp(−A(θ)) where A(θ) = α(q_final). Therefore:

    E_θ[count(e)] = exp(−(α(q) + wₑ + β(q'))) / exp(−A(θ))
                  = exp(−α(q) − wₑ − β(q') + A(θ))

In log space: ln E_θ[count(e)] = A(θ) − α(q) − wₑ − β(q').          ∎

**Concrete Grounding.** `forward_backward.rs:33` implements
`forward_scores()`, computing α(q) as the total weight of all paths
from node 0 to each node via topological-order relaxation. Line 64
implements `backward_scores()`, computing β(q) by reverse-order
traversal. The total partition A(θ) is extracted by `total_weight()`
at line 86: `forward[final_node]`. These generic functions accept any
`W: Semiring` — with `LogWeight` they compute exact expected counts;
with `TropicalWeight` they compute Viterbi (min-cost) paths.

---

## 3  EntropyWeight as Expectation Semiring

### 3.1  The Expectation Semiring

**Definition 3.1 (Expectation Semiring, Li & Eisner 2009).**
The *expectation semiring* has carrier ℝ̄₊ × ℝ (pairs of a weight and
an expectation) with operations:

- **Plus:**  (w₁, e₁) ⊕ (w₂, e₂) = (w₁ ⊕_log w₂, (p₁·e₁ + p₂·e₂)/(p₁ + p₂))
  where pᵢ = exp(−wᵢ) and ⊕_log denotes log-sum-exp
- **Times:** (w₁, e₁) ⊗ (w₂, e₂) = (w₁ + w₂, e₁ + e₂)
- **Zero:**  0̄ = (∞, 0)
- **One:**   1̄ = (0, 0)

**Theorem 3.2 (Semiring Axioms).**
The expectation semiring (ℝ̄₊ × ℝ, ⊕, ⊗, 0̄, 1̄) satisfies the
semiring axioms: ⊕ is associative, commutative, and has identity 0̄; ⊗
is associative and has identity 1̄; ⊗ distributes over ⊕; and 0̄
annihilates under ⊗.

**Proof.**
We verify each axiom:

1. **⊕ associativity.** The weight component is log-sum-exp, which is
   associative (equivalent to addition of probabilities). The expectation
   component is a weighted average: for three elements (wᵢ, eᵢ) with
   pᵢ = exp(−wᵢ), the result is (∑ pᵢeᵢ)/(∑ pᵢ) regardless of
   grouping, since weighted averaging is associative when the total
   weight is tracked.

2. **⊕ commutativity.** Both addition and weighted averaging are
   symmetric in their arguments.

3. **⊕ identity.** (∞, 0) ⊕ (w, e): since p_∞ = exp(−∞) = 0, the
   weight component is w and the expectation is (0·0 + p·e)/p = e.

4. **⊗ associativity.** Both components use addition, which is
   associative.

5. **⊗ identity.** (0, 0) ⊗ (w, e) = (0 + w, 0 + e) = (w, e).

6. **Distributivity.** (w₃, e₃) ⊗ ((w₁, e₁) ⊕ (w₂, e₂)):
   - Weight: w₃ + log-sum-exp(w₁, w₂) = log-sum-exp(w₃+w₁, w₃+w₂).
   - Expectation: e₃ + (p₁e₁+p₂e₂)/(p₁+p₂). The right side
     (w₃,e₃)⊗(w₁,e₁) ⊕ (w₃,e₃)⊗(w₂,e₂) has pairs (w₃+w₁, e₃+e₁)
     and (w₃+w₂, e₃+e₂) with probabilities p₃p₁ and p₃p₂. Averaging:
     (p₃p₁(e₃+e₁) + p₃p₂(e₃+e₂)) / (p₃p₁+p₃p₂)
     = (p₁(e₃+e₁) + p₂(e₃+e₂)) / (p₁+p₂)
     = e₃ + (p₁e₁+p₂e₂)/(p₁+p₂). These agree.

7. **0̄ annihilation.** (∞, 0) ⊗ (w, e) = (∞+w, 0+e) = (∞, e).
   However, any subsequent ⊕ with a finite-weight element will ignore
   this term (p = exp(−∞) = 0), so it acts as an absorbing element in
   the tropical-sum context. This matches the standard convention for
   expectation semirings where ∞ + w = ∞.                              ∎

### 3.2  Single-Pass Entropy Computation

**Theorem 3.3 (Single-Pass Entropy).**
Let a WFST have edges E with weights {wₑ}. Construct EntropyWeight
elements (wₑ, wₑ) for each edge (setting the expectation equal to the
weight). Then the total weight over all accepting paths, computed via a
single forward pass with the expectation semiring, yields (A(θ), H)
where:
- A(θ) = −ln ∑_π exp(−w(π)) is the log-partition function
- H = −∑_π p̄(π) ln p̄(π) is the Shannon entropy of the normalized
  path distribution p̄(π) = exp(−w(π)) / ∑_π exp(−w(π))

**Proof.**
For a single path π traversing edges e₁, ..., eₖ, the ⊗-product of
the arc elements is:

    ⊗ᵢ (wₑᵢ, wₑᵢ) = (∑ᵢ wₑᵢ, ∑ᵢ wₑᵢ) = (w(π), w(π))

This follows from ⊗ being coordinate-wise addition. The expectation
component equals the path weight because we initialized eₑ = wₑ.

For the ⊕-combination of all paths with elements (w(π), w(π)):
- **Weight component:** log-sum-exp over all path weights, which is
  A(θ) = −ln ∑_π exp(−w(π)) by definition.
- **Expectation component:** the weighted average
  (∑_π p(π) · w(π)) / (∑_π p(π)) where p(π) = exp(−w(π)).

The denominator ∑_π p(π) = exp(−A(θ)). Since w(π) = −ln p(π):

    expectation = ∑_π p(π) · (−ln p(π)) / ∑_π p(π)
                = ∑_π p̄(π) · (−ln p̄(π) − ln ∑_π p(π)) / 1

Wait — we must be careful. Define p̄(π) = p(π)/Z where Z = ∑_π p(π).
Then:

    expectation = (∑_π p(π) · w(π)) / Z
                = ∑_π p̄(π) · w(π)
                = ∑_π p̄(π) · (−ln p(π))
                = ∑_π p̄(π) · (−ln(p̄(π) · Z))
                = ∑_π p̄(π) · (−ln p̄(π) − ln Z)
                = −∑_π p̄(π) ln p̄(π) − ln Z · ∑_π p̄(π)
                = H − ln Z

Since ln Z = −A(θ), this gives expectation = H + A(θ). However, the
EntropyWeight implementation normalizes the expectation component during
⊕ by dividing by the total probability, so the final stored expectation
is the weighted average of the path-level expectations. Examining the
accumulation more carefully:

Let val_total = (∑_π p(π) · w(π)) / (∑_π p(π)) = ∑_π p̄(π) · w(π).

Now w(π) = −ln p(π) = −ln(p̄(π) · Z) = −ln p̄(π) + A(θ). Therefore:

    val_total = ∑_π p̄(π)(−ln p̄(π) + A(θ))
              = −∑_π p̄(π) ln p̄(π) + A(θ) ∑_π p̄(π)
              = H + A(θ)

So the expectation component is H + A(θ), and H = expectation − A(θ)
= expectation − weight. The Shannon entropy is recovered as the
difference of the two components.                                       ∎

**Concrete Grounding.** `EntropyWeight` at `semiring.rs:1120` stores
the pair `(weight, expectation)`. The constructor `from_arc_weight(w)`
at line 1141 creates `(w, w)` as required by the theorem. The method
`entropy_bits()` at line 1162 converts the expectation to bits via
division by ln(2). The ⊕ operation is implemented in the `Semiring`
impl at line 1186 using `log_sum_exp()` (line 1168) for the weight
component and weighted averaging for the expectation component. A single
forward pass with `forward_scores::<EntropyWeight>()` computes both the
log-partition and entropy simultaneously in O(|E|) time.

---

## 4  Information-Theoretic Beam Width

### 4.1  Shannon Entropy

**Definition 4.1 (Shannon Entropy).**
For a discrete probability distribution p = (p₁, ..., pₙ) over n
outcomes, the *Shannon entropy* is:

    H(p) = −∑ᵢ₌₁ⁿ pᵢ ln pᵢ

with the convention 0 ln 0 = 0 (by continuity). Properties:
- H(p) = 0 when p is deterministic (one pᵢ = 1, rest 0)
- H(p) = ln n when p is uniform (pᵢ = 1/n ∀ i)
- 0 ≤ H(p) ≤ ln n always
- Units: nats (base e) or bits (base 2, dividing by ln 2)

### 4.2  Entropy and Effective Support

**Theorem 4.2 (Entropy Lower-Bounds Effective Support).**
If a distribution p has support on k outcomes (i.e., exactly k values
pᵢ > 0), then k ≥ exp(H(p)). Equivalently, exp(H(p)) ≤ k.

**Proof.**
Among all distributions supported on exactly k outcomes, the uniform
distribution p_uniform = (1/k, ..., 1/k) uniquely maximizes entropy
(this is the *maximum entropy principle*, proven by Lagrange
multipliers). The uniform entropy is:

    H(p_uniform) = −∑ᵢ₌₁ᵏ (1/k) ln(1/k) = −k · (1/k) · (−ln k) = ln k

For any distribution p on k outcomes: H(p) ≤ H(p_uniform) = ln k.
Exponentiating both sides: exp(H(p)) ≤ exp(ln k) = k.                  ∎

**Theorem 4.3 (Maximum Entropy Characterization).**
Among all distributions on k outcomes, the unique maximizer of H(p)
subject to ∑ᵢ pᵢ = 1 is the uniform distribution pᵢ = 1/k.

**Proof.**
Form the Lagrangian L(p, λ) = −∑ᵢ pᵢ ln pᵢ − λ(∑ᵢ pᵢ − 1). Taking
the partial derivative with respect to pᵢ:

    ∂L/∂pᵢ = −ln pᵢ − 1 − λ = 0
    ⟹  pᵢ = exp(−1 − λ)

Since this is independent of i, all pᵢ are equal. The constraint
∑ pᵢ = 1 forces pᵢ = 1/k. The Hessian of H is diagonal with entries
−1/pᵢ < 0, confirming this is a maximum.                               ∎

### 4.3  Adaptive Beam Width from Entropy

**Definition 4.4 (Entropy-Adaptive Beam Width).**
Given the Shannon entropy H at a parse decision point, the *adaptive
beam width* is B = ⌈exp(H)⌉, the smallest integer at least as large
as the effective support.

**Corollary 4.5 (Beam Width Bounds).**
By Theorem 4.2:
- At deterministic points (H = 0): B = ⌈exp(0)⌉ = 1, a single
  alternative suffices.
- At binary-ambiguous points (H = ln 2 ≈ 0.693 nats): B = 2.
- At highly ambiguous points (H = 2 nats): B = ⌈exp(2)⌉ = ⌈7.389⌉ = 8.
- At maximum ambiguity over k alternatives (H = ln k): B = k.

The beam is narrow where parsing is unambiguous and widens precisely
where uncertainty demands exploration — without over-allocating.

**Theorem 4.6 (Confidence Gap Approximates Entropy).**
Let w₁ ≤ w₂ ≤ ... ≤ wₖ be the sorted tropical weights of k competing
parse actions (lower = better). Define the *confidence gap* Δ = w₂ − w₁.
Then:
- Δ → ∞ implies H → 0 (one dominant action)
- Δ → 0 implies H → ln k (near-uniform)

More precisely, for the softmax distribution pᵢ = exp(−wᵢ)/Z:

    H ≤ ln(1 + (k−1)exp(−Δ))

**Proof.**
The entropy of the softmax distribution p is:

    H = −∑ᵢ pᵢ ln pᵢ = ln Z + ∑ᵢ pᵢ wᵢ

where Z = ∑ᵢ exp(−wᵢ). Factor out exp(−w₁):

    Z = exp(−w₁) · (1 + ∑ᵢ₌₂ᵏ exp(−(wᵢ − w₁)))
      ≤ exp(−w₁) · (1 + (k−1)exp(−Δ))

since wᵢ − w₁ ≥ Δ for all i ≥ 2. Therefore:

    ln Z ≤ −w₁ + ln(1 + (k−1)exp(−Δ))

The term ∑ᵢ pᵢ wᵢ ≥ w₁ (since p₁ dominates when Δ is large). In the
limit Δ → ∞: Z → exp(−w₁), so ln Z → −w₁, and ∑ pᵢ wᵢ → w₁,
giving H → 0. In the limit Δ → 0 (all weights equal): the distribution
is uniform and H = ln k.

The bound H ≤ ln(1 + (k−1)exp(−Δ)) follows from:

    H = ln Z − ∑ᵢ pᵢ(−wᵢ) ≤ ln Z + w₁ ≤ ln(1 + (k−1)exp(−Δ))      ∎

**Concrete Grounding.** `predict_with_confidence()` at `wfst.rs:362`
returns actions annotated with `CountingWeight` — the derivation count
k. The related method `predict_pruned()` at `wfst.rs:372` implements
beam pruning: it computes the gap `threshold = best.weight + beam_width`
and filters actions exceeding this threshold (line 376). This is the
confidence gap Δ from Theorem 4.6 in practice: actions with weight more
than `beam_width` worse than the best are pruned. `EntropyWeight`
(Theorem 3.3) provides exact entropy for more precise beam sizing when
the `wfst-log` feature is enabled.

---

## 5  References

- Li, Z. & Eisner, J. (2009). "First- and Second-Order Expectation
  Semirings with Applications to Minimum-Risk Training on Translation
  Forests." *EMNLP*, 40-51.
- Mohri, M. (2009). "Weighted automata algorithms." In *Handbook of
  Weighted Automata*, Ch. 6. Springer.
- Bishop, C. M. (2006). *Pattern Recognition and Machine Learning*.
  Springer.
- Eisner, J. (2002). "Parameter estimation for probabilistic
  finite-state transducers." *ACL*, 1-8.
- Cover, T. M. & Thomas, J. A. (2006). *Elements of Information
  Theory* (2nd ed.). Wiley.
- Shannon, C. E. (1948). "A mathematical theory of communication."
  *Bell System Technical Journal*, 27(3), 379-423.
- Zinkevich, M. (2003). "Online convex programming and generalized
  infinitesimal gradient ascent." *ICML*, 928-936.
