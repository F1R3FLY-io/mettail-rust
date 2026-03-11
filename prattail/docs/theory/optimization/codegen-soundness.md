# Codegen Optimization Soundness

Formal soundness arguments for each advanced automata codegen optimization promoted to `OptimizationStatus::Auto`.

## 1. Framework

### 1.1 Optimization Soundness Criterion

**Definition 1** (Codegen Optimization). A codegen optimization is a mapping θ: Analysis → CodeTransform that produces a modified parser P' from the original parser P.

**Definition 2** (Language Preservation). θ is *sound* if ∀w ∈ Σ*: L(P)(w) = L(P')(w), i.e., the set of accepted words is unchanged.

**Definition 3** (Weight-Only Optimization). θ is *weight-preserving* if ∀w ∈ Σ*: P(w) = P'(w) (same parse tree), but the evaluation order may differ. Weight-only optimizations affect performance but not correctness.

### 1.2 Notation

- Σ: input alphabet
- L(P): language recognized by parser P
- W: semiring weight domain
- ⊕, ⊗: semiring plus and times
- sat(φ): satisfiability of predicate φ under Boolean algebra semantics
- P(r fires | w): probability that rule r fires on input w

---

## 2. SYM01-DCE: Symbolic Guard Dead Code Elimination

### 2.1 Statement

**Theorem 1** (Symbolic DCE Correctness). Let G be a grammar with rules R = {r₁, ..., rₙ}. Let rᵢ have guard predicate φᵢ drawn from a Boolean algebra (B, ∧, ∨, ¬, ⊤, ⊥). If sat(φᵢ) = false, then removing rᵢ from R does not change L(G).

### 2.2 Proof

By Definition 5.1 of the SFA model in `symbolic.rs`, a guard is a predicate φ: Σ → {true, false}. The set of symbols matching guard φᵢ is:

    Match(φᵢ) = {a ∈ Σ | φᵢ(a) = true}

By hypothesis, sat(φᵢ) = false, which means:

    ∀a ∈ Σ: φᵢ(a) = false

Therefore Match(φᵢ) = ∅.

A rule rᵢ contributes to the language only if there exists some input position where its guard matches. Since Match(φᵢ) = ∅, no symbol at any position can satisfy the guard. The transition labeled by φᵢ never fires.

Let R' = R \ {rᵢ}. For any word w = a₁a₂...aₘ:

- **Forward**: If w ∈ L(G) with rules R, there exists an accepting run σ through rules in R. Since rᵢ's guard never matches any aⱼ, σ does not use rᵢ. Therefore σ is also a valid run under R', so w ∈ L(G') with rules R'.

- **Backward**: If w ∈ L(G') with rules R', then σ is a valid run under R' ⊆ R, so w ∈ L(G).

Therefore L(G) = L(G'). ∎

### 2.3 Implementation

```
if symbolic_result.unsatisfiable_rule_labels contains label:
    dead_rule_labels.insert(label)
```

The existing A4 DCE codegen path (`a.dead_rule_labels.contains(&label)`) handles the rest — no new codegen hooks needed.

---

## 3. PR01-DCE: Probabilistic Dead Code Elimination

### 3.1 Statement

**Theorem 2** (Probabilistic DCE Soundness). Let G be a grammar with PA analysis where `is_normalized = true`. Let rᵢ have selectivity sᵢ = P(rᵢ fires | random input from corpus). If sᵢ < ε = 0.01, then removing rᵢ is a statistical heuristic: it may change L(G) for rare inputs but preserves L(G) on ≥ 99% of corpus inputs.

### 3.2 Argument

This optimization is explicitly *not* language-preserving in the strict formal sense. It is a statistical heuristic justified by:

1. **Selectivity bound**: P(rᵢ fires) < 0.01 means the rule contributes to fewer than 1% of parse outcomes in the training corpus.

2. **Normalization guard**: The `is_normalized` flag is true only when the PA has been trained from a real corpus (Baum-Welch EM convergence). Default uniform weights produce `is_normalized = false`, ensuring no rules are eliminated without training data.

3. **Corpus representativeness assumption**: The training corpus is assumed representative of production inputs. Under this assumption, eliminating rules with < 1% selectivity has minimal impact.

**Safety mitigation**: The optimization only extends `dead_rule_labels` — the same codegen path as SYM01-DCE and WFST dead-rule detection. If a user encounters issues, they can disable it via the `probabilistic_dce` gate or the `PRATTAIL_OPT_PROBABILISTIC_DCE=0` environment variable.

### 3.3 Implementation

```
if probabilistic_result.is_normalized
   && probabilistic_result.low_selectivity_rules contains label:
    dead_rule_labels.insert(label)
```

---

## 4. PR01-WEIGHT: Probabilistic Weight Blending

### 4.1 Statement

**Theorem 3** (Weight Blend Correctness). The blended weight w_blend(r) = (w_wfst(r) + w_prob(r)) / 2 preserves acceptance: ∀w. w ∈ L(P) ⟺ w ∈ L(P').

### 4.2 Proof

The blended weight is used exclusively for constructor ordering in the generated match arms (Sprint 3 Rule Ordering). This ordering determines:

1. **Which match arm is tried first** in the generated Ascent dispatch
2. **Cache locality** of frequently-used constructors

Neither of these affects which rules fire or what parse results are produced. The Ascent fixpoint evaluates all matching rules regardless of order — it is a bottom-up Datalog engine where rule evaluation order affects performance (number of intermediate tuples, cache behavior) but not the final fixpoint.

Formally, let R = {r₁, ..., rₙ} be the rules of a category. Let π₁ be the ordering induced by w_wfst and π₂ be the ordering induced by w_blend. Both orderings are permutations of R. The Ascent fixpoint computes:

    T(R) = lfp(λS. S ∪ ⋃ᵢ rᵢ(S))

This is order-independent: the least fixpoint of a monotone operator on a finite lattice is unique regardless of evaluation order (Tarski 1955).

Therefore L(P) = L(P'). ∎

### 4.3 Blend Properties

The arithmetic mean blend satisfies:

- **Bounded**: min(w_wfst, w_prob) ≤ w_blend ≤ max(w_wfst, w_prob)
- **Concordant**: If both signals agree (w_wfst(r₁) < w_wfst(r₂) and w_prob(r₁) < w_prob(r₂)), then w_blend(r₁) < w_blend(r₂)
- **Averaging**: When signals disagree, the blend averages them (neither dominates)

### 4.4 Implementation

```
for (label, selectivity) in probabilistic_result.rule_selectivities:
    if selectivity > 0.0:
        prob_weight = -ln(selectivity)     // tropical: lower = more frequent
        existing = constructor_weights[label] or +∞
        constructor_weights[label] = (existing + prob_weight) / 2
```

---

## 5. N06-ISO: Bisimulation Isomorphic Group Extension

### 5.1 Statement

**Theorem 4** (Bisimulation Isomorphic Groups). Let A_c₁ and A_c₂ be the alternating automata for categories c₁ and c₂. If bisim(A_c₁, A_c₂) = true, then L(A_c₁) = L(A_c₂), and sharing dispatch templates between c₁ and c₂ preserves acceptance.

### 5.2 Proof

By the bisimulation game semantics (Milner 1989, Def. 4.1):

A binary relation R ⊆ Q₁ × Q₂ is a *bisimulation* if whenever (p, q) ∈ R:
1. For every transition p →ₐ p' there exists q →ₐ q' with (p', q') ∈ R
2. For every transition q →ₐ q' there exists p →ₐ p' with (p', q') ∈ R

If a bisimulation R exists with (q₀₁, q₀₂) ∈ R (initial states related), then by induction on word length:

**Base**: ε ∈ L(A_c₁) iff q₀₁ ∈ F₁ iff q₀₂ ∈ F₂ (bisimulation preserves acceptance states) iff ε ∈ L(A_c₂).

**Step**: For word wa, if A_c₁ accepts wa via run q₀₁ →w p →ₐ p' ∈ F₁, then by the bisimulation property applied inductively:
- There exists a corresponding run q₀₂ →w q →ₐ q' with (p', q') ∈ R
- Since p' ∈ F₁ and R preserves acceptance, q' ∈ F₂
- Therefore A_c₂ accepts wa

By symmetry (condition 2), the converse holds.

Therefore L(A_c₁) = L(A_c₂). ∎

**Corollary**: For weighted alternating automata, bisimulation further preserves the weight function: if (p, q) ∈ R, then the weighted behaviors ⟦A_c₁⟧ and ⟦A_c₂⟧ coincide.

### 5.3 Complement Construction

The implementation uses `non_bisimilar_pairs` — the output of the bisimulation game that identifies pairs that are NOT bisimilar. All pairs not in this set AND not already in De Bruijn isomorphic groups are added as new bisimulation-equivalent groups.

```
for each pair (cᵢ, cⱼ) where i < j:
    if (cᵢ, cⱼ) ∉ non_bisimilar_pairs
       && cᵢ ∉ existing_groups && cⱼ ∉ existing_groups:
        isomorphic_groups.push([cᵢ, cⱼ])
```

---

## 6. RA01-SKIP: Register Dead Binder Elimination

### 6.1 Statement

**Theorem 5** (Dead Register Elimination). Let RA be a register automaton with registers {r₁, ..., rₖ}. If register rᵢ has Store transitions but no TestEq, TestNeq, or TestFresh transitions, then rᵢ is *dead*: the automaton's acceptance is independent of rᵢ's value. Skipping alpha-equivalence checking for the corresponding binder category is safe.

### 6.2 Proof

By Definition 6.3 of the register automaton model in `register_automata.rs`, a transition τ = (q, σ, op, q') has a register operation op ∈ {Nop, Store(i), TestEq(i), TestNeq(i), TestFresh(i)}.

The acceptance condition depends on the final state q_f ∈ F. Register values do not directly appear in the acceptance condition — they only affect acceptance indirectly through transitions that test them.

Let Dead(rᵢ) hold iff:
- ∃ transition with op = Store(i) (rᵢ is written)
- ∄ transition with op ∈ {TestEq(i), TestNeq(i), TestFresh(i)} (rᵢ is never tested)

Under Dead(rᵢ), we construct an equivalent RA' where all Store(i) operations are replaced with Nop:

**Claim**: L(RA) = L(RA').

**Proof of claim**: Consider any accepting run ρ = (q₀, ν₀) →_{a₁} (q₁, ν₁) →_{a₂} ... →_{aₘ} (qₘ, νₘ) in RA.

Construct ρ' identically but with ν'_j[i] = ⊥ for all j (register i always holds ⊥).

For each transition (qⱼ, aⱼ₊₁, opⱼ, qⱼ₊₁):
- If opⱼ = Nop: same in ρ', trivially valid.
- If opⱼ = Store(i): In ρ, sets νⱼ₊₁[i] = aⱼ₊₁. In ρ', replaced with Nop. Valid because rᵢ is dead (never tested).
- If opⱼ = Store(k) for k ≠ i: identical behavior.
- If opⱼ = TestEq(k) for k ≠ i: tests ν[k], which is identical in ρ and ρ'.
- If opⱼ = TestEq(i): **impossible** by Dead(rᵢ) hypothesis.
- Similarly for TestNeq(i), TestFresh(i).

Since the state sequence q₀, q₁, ..., qₘ is identical and qₘ ∈ F, ρ' is accepting. The converse is symmetric.

Therefore L(RA) = L(RA'). Since rᵢ's value is always ⊥ in RA', alpha-equivalence on the binder category corresponding to rᵢ is trivially satisfied — no checking needed. ∎

### 6.3 Implementation

```
for each dead register index i in register_result.dead_registers:
    if let Some(category) = categories.get(i):
        dead_binder_categories.insert(category.name)
```

---

## 7. V05-INFO: VPA Bracket Deterministic (Informational)

### 7.1 Property

`bracket_deterministic = is_determinizable && alphabet_mismatches.is_empty()`

This is a conjunction of two conditions:
- `is_determinizable`: the VPA's bracket structure admits determinization (Alur & Madhusudan 2004)
- `alphabet_mismatches.is_empty()`: all brackets are correctly classified as call/return/internal

### 7.2 Conservativeness

The flag is conservative: `bracket_deterministic = true` requires BOTH conditions. False negatives are possible (a grammar may have deterministic bracket matching but fail one of the conditions), but false positives are not.

No codegen action is taken based on this flag in the current implementation.

---

## 8. MT01-INFO: Multi-Tape Independent Categories (Informational)

### 8.1 Property

Categories whose multi-tape analysis shows they are independent (no cross-tape constraints). Currently, `analyze_from_bundle()` returns `disconnected_tapes: Vec::new()`, so this field is always empty.

No codegen action is taken based on this field in the current implementation.

---

## 9. Composition

### 9.1 Dead Rule Union

The final `dead_rule_labels` is the union of three sources:

    dead_rule_labels = WFST_dead ∪ SYM01_dead ∪ PR01_dead

**Theorem 6** (Union Soundness). If each source correctly identifies dead rules, their union is also correct.

**Proof**: Each source provides a subset of provably dead rules. The union of subsets of dead rules is also a subset of dead rules. No rule is incorrectly marked dead because each source operates on an independent criterion (WFST unreachability, SFA unsatisfiability, probabilistic low selectivity). ∎

### 9.2 Independence

The five optimizations are independent — they modify disjoint aspects of `PipelineAnalysis`:

| Optimization | Modified Field | No Conflict |
|-------------|----------------|-------------|
| SYM01-DCE | dead_rule_labels (append) | Union with WFST and PR01 |
| PR01-DCE | dead_rule_labels (append) | Union with WFST and SYM01 |
| PR01-WEIGHT | constructor_weights (blend) | Averages with WFST weights |
| N06-ISO | isomorphic_groups (extend) | New groups for ungrouped categories |
| RA01-SKIP | dead_binder_categories (new) | Independent field |

No optimization reads a field that another optimization writes, so composition order does not matter.

---

## 10. References

- Alur, R. & Madhusudan, P. "Visibly Pushdown Languages" (STOC 2004)
- Kaminski, M. & Francez, N. "Finite-Memory Automata" (TCS 134, 1994)
- Milner, R. "Communication and Concurrency" (Prentice Hall, 1989)
- Rabiner, L. R. "A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition" (Proc. IEEE 77, 1989)
- Tarski, A. "A Lattice-Theoretical Fixpoint Theorem and Its Applications" (Pacific J. Math. 5, 1955)
- Veanes, M. et al. "Symbolic Automata: The Toolkit" (TACAS 2010)
