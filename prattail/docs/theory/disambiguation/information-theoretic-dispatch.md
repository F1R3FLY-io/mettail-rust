# Entropy, Structural Weights, and Beam Width Scaling

## 1. Motivation

When a grammar category has multiple alternative rules, uniform weighting (each rule equally likely) wastes disambiguation budget. Rules of different structural complexity carry different *a priori* likelihoods: a simple `Atom ::= NUMBER` is more likely than a complex `Expr ::= "if" Expr "then" Expr "else" Expr` in a typical program. Assigning non-uniform **structural weights** based on rule complexity produces a probability distribution whose Shannon entropy quantifies the inherent ambiguity of each category.

Categories with high entropy (many equally plausible alternatives) require wider beams during error recovery and disambiguation. Categories with low entropy (one dominant rule) can be dispatched with minimal overhead. This document formalizes structural weights, proves entropy bounds, and derives the beam width scaling implemented in `probabilistic.rs`.

## 2. Definitions

**Definition 4.1** (Structural Weight). For a grammar rule r with body items(r) = s₁ s₂ ... sₖ, the **structural weight** is

    w(r) = 1 / (1 + |items(r)|)

where |items(r)| is the number of syntax items in the rule body. Simpler rules (fewer items) receive higher weight, reflecting the heuristic that shorter productions are more commonly matched.

*Example*: A rule `Atom ::= NUMBER` has |items| = 1, so w = 1/2 = 0.5. A rule `IfExpr ::= "if" Expr "then" Expr "else" Expr` has |items| = 6, so w = 1/7 ≈ 0.143.

**Definition 4.2** (Per-Category Normalization). For a category C with rules r₁, ..., rₙ, the **normalized probability** of rule rᵢ is

    pᵢ = w(rᵢ) / Σⱼ₌₁ⁿ w(rⱼ)

This ensures Σᵢ pᵢ = 1, forming a valid probability distribution over the rules of C.

**Definition 4.3** (Shannon Entropy). The **Shannon entropy** of category C with normalized probabilities p₁, ..., pₙ is

    H(C) = −Σᵢ₌₁ⁿ pᵢ ln(pᵢ)

measured in nats (natural logarithm). H(C) quantifies the expected surprise when selecting a rule from C according to the structural weight distribution.

**Definition 4.4** (Selectivity). The **selectivity** of a rule r within its category C is

    sel(r) = p(r) × (|rules_in_cat(r)| / |total_rules|)

Selectivity combines the rule's within-category probability with the category's share of the total grammar. A rule with high selectivity is both likely within its category and belongs to a category with many rules.

**Definition 4.5** (Per-Category Entropy). The per-category entropy H(C) is computed over the normalized probabilities pᵢ *within a single category C*. This differs from the global entropy (computed over all rules in the grammar) by focusing on the disambiguation difficulty within each category independently.

The **mean entropy** of the grammar is

    H̄ = (1/|categories|) × Σ_C H(C)

This provides a single-number summary of the grammar's overall disambiguation complexity.

## 3. Theorems

**Theorem 4.1** (Entropy Bounds). *For a category C with n rules, the Shannon entropy satisfies*

    *0 ≤ H(C) ≤ ln(n)*

*Left equality holds iff n = 1 (single rule, p₁ = 1). Right equality holds iff all rules have equal weight (uniform distribution).*

*Proof.*

**Lower bound (H ≥ 0)**: Each pᵢ ∈ (0, 1] (positive by definition, since w(r) > 0 for all rules). Therefore ln(pᵢ) ≤ 0, so −pᵢ ln(pᵢ) ≥ 0 for each term. The sum of non-negative terms is non-negative.

**Lower bound achieved**: When n = 1, p₁ = 1, and H = −1 × ln(1) = 0.

**Upper bound (H ≤ ln(n))**: By the log-sum inequality (or equivalently, by the fact that the uniform distribution maximizes entropy over n outcomes):

    H(C) = −Σᵢ pᵢ ln(pᵢ) ≤ −Σᵢ (1/n) ln(1/n) = −n × (1/n) × ln(1/n) = ln(n)

The inequality follows from the strict concavity of the function f(p) = −p ln(p) and Jensen's inequality applied to the constraint Σ pᵢ = 1.

**Upper bound achieved**: When all pᵢ = 1/n (uniform distribution), H = −n × (1/n) × ln(1/n) = ln(n). ∎

**Theorem 4.2** (Structural Weight Monotonicity). *For rules r₁, r₂ with |items(r₁)| < |items(r₂)|, we have w(r₁) > w(r₂).*

*Proof.* The function f(x) = 1/(1 + x) is strictly decreasing for x ≥ 0:

    f'(x) = −1/(1 + x)² < 0    for all x ≥ 0

Since |items(r₁)| < |items(r₂)|, applying f to both sides:

    w(r₁) = f(|items(r₁)|) > f(|items(r₂)|) = w(r₂)

Therefore, simpler rules always receive strictly higher structural weight. ∎

**Theorem 4.3** (Beam Width Scaling via Entropy). *For a category C with entropy H(C), the effective number of equally probable alternatives is*

    N_eff(C) = e^{H(C)}

*This quantity, known as the perplexity, provides a principled basis for beam width scaling: a beam of width ≥ N_eff is sufficient to cover the effective alternatives.*

*Proof.* The perplexity exp(H) is a standard information-theoretic measure (Shannon, 1948). For a uniform distribution over n items, H = ln(n) and exp(H) = n, recovering the number of alternatives. For a peaked distribution with one dominant rule and n − 1 unlikely rules, H ≈ 0 and exp(H) ≈ 1, indicating that a single beam suffices. In general, exp(H) interpolates between these extremes, providing the geometric mean number of choices weighted by probability. ∎

*Consequence.* Categories with high entropy need wider beams during error recovery (more alternatives to explore), while categories with low entropy can use narrow beams (the dominant rule is almost certainly correct).

## 4. Algorithm

### Algorithm 4: Structure-Weighted Probabilistic Analysis

```
PROCEDURE ANALYZE-STRUCTURE-WEIGHTS(all_syntax, categories)
  INPUT:  all_syntax = [(cat, label, items)]  — all grammar rules
          categories = [CategoryInfo]          — category metadata
  OUTPUT: ProbabilisticAnalysis = {
            rule_selectivities: {label → f64},
            low_selectivity_rules: [label],
            category_entropies: {cat → f64},
            mean_entropy: f64,
            is_normalized: bool
          }

  1. // Phase 1: Compute structural weights
     total_rules ← |all_syntax|
     FOR EACH rule (cat, label, items) IN all_syntax:
       weight[label] ← 1.0 / (1.0 + |items|)

  2. // Phase 2: Group by category and normalize
     FOR EACH category C IN categories:
       rules_C ← {(label, weight[label]) : cat = C.name}
       W_C ← Σ_{(l,w) ∈ rules_C} w              // sum of weights in C
       IF W_C > 0 THEN
         FOR EACH (label, w) IN rules_C:
           p[label] ← w / W_C                    // normalized probability

  3. // Phase 3: Compute entropy per category
     FOR EACH category C:
       H_C ← 0.0
       FOR EACH (label, _) IN rules_C:
         IF p[label] > 0 THEN
           H_C ← H_C − p[label] × ln(p[label])
       category_entropies[C] ← H_C

  4. // Phase 4: Compute selectivity
     FOR EACH rule (cat, label, items):
       n_C ← |rules in category cat|
       sel[label] ← p[label] × (n_C / total_rules)

  5. // Phase 5: Identify low-selectivity rules
     low_sel ← {label : sel[label] < LOW_SEL_THRESHOLD}  // e.g., 0.01

  6. // Phase 6: Mean entropy
     mean_H ← (1/|categories|) × Σ_C H_C

  7. RETURN ProbabilisticAnalysis {
       rule_selectivities: sel,
       low_selectivity_rules: low_sel,
       category_entropies,
       mean_entropy: mean_H,
       is_normalized: true
     }

  COMPLEXITY: O(R) where R = total number of rules (single pass)
```

## 5. Worked Example

Consider a grammar with three categories:

```
Expr  ::= Atom             (1 item)
        | Expr "+" Expr     (3 items)
        | Expr "*" Expr     (3 items)
Atom  ::= NUMBER            (1 item)
        | IDENT             (1 item)
Decl  ::= "let" IDENT "=" Expr ";"  (5 items)
```

**Step 1: Structural weights**

| Rule              | |items| | w = 1/(1+\|items\|) |
|-------------------|---------|---------------------|
| Expr::Atom        | 1       | 1/2 = 0.500         |
| Expr::Add         | 3       | 1/4 = 0.250         |
| Expr::Mul         | 3       | 1/4 = 0.250         |
| Atom::Number      | 1       | 1/2 = 0.500         |
| Atom::Ident       | 1       | 1/2 = 0.500         |
| Decl::Let         | 5       | 1/6 = 0.167         |

**Step 2: Per-category normalization**

Category Expr: W = 0.5 + 0.25 + 0.25 = 1.0
- p(Expr::Atom) = 0.5/1.0 = 0.500
- p(Expr::Add) = 0.25/1.0 = 0.250
- p(Expr::Mul) = 0.25/1.0 = 0.250

Category Atom: W = 0.5 + 0.5 = 1.0
- p(Atom::Number) = 0.5/1.0 = 0.500
- p(Atom::Ident) = 0.5/1.0 = 0.500

Category Decl: W = 0.167
- p(Decl::Let) = 0.167/0.167 = 1.000

**Step 3: Shannon entropy**

H(Expr) = −(0.5 × ln 0.5 + 0.25 × ln 0.25 + 0.25 × ln 0.25)
         = −(0.5 × (−0.693) + 0.25 × (−1.386) + 0.25 × (−1.386))
         = −(−0.347 + (−0.347) + (−0.347))
         = 1.040 nats

H(Atom) = −(0.5 × ln 0.5 + 0.5 × ln 0.5)
         = −(2 × 0.5 × (−0.693))
         = 0.693 nats

H(Decl) = −(1.0 × ln 1.0)
         = 0 nats

**Step 4: Effective alternatives (perplexity)**

N_eff(Expr) = e^{1.040} ≈ 2.83 (between 2 and 3 effective rules)
N_eff(Atom) = e^{0.693} = 2.00 (exactly 2 effective rules)
N_eff(Decl) = e^{0.000} = 1.00 (single effective rule)

**Step 5: Mean entropy**

H̄ = (1.040 + 0.693 + 0) / 3 = 0.578 nats

**Interpretation**: Expr is the most ambiguous category (N_eff ≈ 2.83), suggesting a beam width of at least 3 for recovery. Decl is deterministic (N_eff = 1).

## 6. Diagram

### Entropy vs. Rule Distribution

```
  H(C) (nats)
  │
  │  ln(3) = 1.099  ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄  max for 3 rules (uniform)
  │                                           ╱
  │  1.040 ─────── ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓ ◁── Expr (non-uniform: 0.5, 0.25, 0.25)
  │
  │  ln(2) = 0.693  ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄ ┄  max for 2 rules (uniform)
  │                  ░░░░░░░░░░░░░░░░ ◁── Atom (uniform: 0.5, 0.5)
  │
  │
  │  0.000 ─────── ═══════════════════ ◁── Decl (single rule: 1.0)
  │
  └──────────────────────────────────────────▶ category

  Legend:
    ▓  high entropy — multiple competitive alternatives
    ░  moderate entropy — balanced binary choice
    ═  zero entropy — deterministic dispatch
```

### Structural Weight Function

```
  w(r) = 1/(1+|items|)
  │
  1.0 ┤
      │
  0.5 ┤ ●
      │   ╲
  0.33┤     ╲ ●
      │       ╲
  0.25┤         ╲ ●
  0.2 ┤           ╲ ●
  0.17┤             ╲ ●
      │               ╲ ●
  0.1 ┤                 ╲ ● ╲ ● ╲ ●
      │
  0.0 ┤
      └──┬──┬──┬──┬──┬──┬──┬──┬──┬──▶ |items(r)|
         0  1  2  3  4  5  6  7  8  9

  Strictly decreasing: simpler rules always get higher weight.
  Approaches zero asymptotically but never reaches it.
```

### Beam Width Recommendation

```
  ┌─────────────────────────────────────────────────────────┐
  │  Category    │ H(C) │ N_eff │ Recommended Beam Width   │
  ├─────────────┼──────┼───────┼──────────────────────────┤
  │  Decl       │ 0.00 │  1.0  │ 1 (deterministic)        │
  │  Atom       │ 0.69 │  2.0  │ 2 (binary choice)        │
  │  Expr       │ 1.04 │  2.8  │ 3 (round up perplexity)  │
  │  [uniform-5]│ 1.61 │  5.0  │ 5 (all alternatives)     │
  └─────────────┴──────┴───────┴──────────────────────────┘
```

## 7. Implementation References

- **`analyze_from_bundle()`** — `probabilistic.rs:1101`: Entry point for structure-weighted analysis. Computes structural weights, normalizes per category, calculates entropy and selectivity.
- **`ProbabilisticAnalysis`** — `probabilistic.rs`: Result struct with `rule_selectivities`, `low_selectivity_rules`, `mean_entropy`, `is_normalized`.
- **`ProbabilisticCompiler`** — `probabilistic.rs:1245`: Compiler adapter delegating to `analyze_from_bundle()`.
- **Pipeline entropy computation** — `pipeline.rs`: Consumes `ProbabilisticAnalysis` to set beam widths and recovery parameters.

## 8. Cross-References

- `theory/probabilistic/stochastic-analysis.md` — Full probabilistic automata theory (forward, Viterbi, Baum-Welch)
- `theory/disambiguation/symbolic-guard-algebra.md` — Guard-based disambiguation (complementary)
- `theory/disambiguation/predicate-dispatch-ordering.md` — Subsumption-based ordering (complementary)
- `docs/diagnostics/probabilistic/PR01.md` — PR01 lint: low selectivity rule
- `docs/diagnostics/probabilistic/PR02.md` — PR02 lint: high entropy category

## 9. Bibliography

1. Shannon, C.E. (1948). "A Mathematical Theory of Communication." *Bell System Technical Journal*, 27(3), pp. 379–423.

2. Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted Automata*, pp. 213–254. Springer.

3. Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory.* 2nd edition. Wiley-Interscience. Chapter 2: Entropy.

4. Rabiner, L.R. (1989). "A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition." *Proceedings of the IEEE*, 77(2), pp. 257–286.
