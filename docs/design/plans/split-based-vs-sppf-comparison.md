# Split-Based WCFG Induction Paper vs Current Weighted SPPF — Analysis

**Date**: 2026-05-17
**Paper**: Gabor, Wieczorek, Unold (2021), "Split-Based Algorithm for Weighted
Context-Free Grammar Induction." *Appl. Sci.* 11, 1030. MDPI.
**Source**: `/home/dylon/Papers/Split-Based Algorithm for Weighted Context-Free Grammar Induction.pdf` (10 pages)
**Status**: review complete; recommendation: adopt nothing immediately

---

## TL;DR

**This paper does not apply to the weighted SPPF + WPDA parser at all in its
primary contribution.** It is a *grammar-learning* paper, not a *parsing*
paper. "Induction" means **discovering an unknown grammar from
positive/negative example sentences**, where the grammar is iteratively
constructed by a "split" operation on nonterminals and rule weights are
re-estimated by a contrastive EM variant ("IOCE"). PraTTaIL grammars are
hand-authored via the `language!` proc-macro DSL; there is no scenario
where we would induce them from labeled corpora.

**No primary contribution is adoptable.** The five "secondary" techniques
the paper relies on (stochastic CKY, inside-outside, EM, low-weight rule
pruning, sentence accept/reject classification) are either already
implemented in PraTTaIL in a more general form (forward-backward in
`forward_backward.rs`, SGD training in `training.rs`, expectation semiring
in `EntropyWeight`) or live in a different algorithmic paradigm (CYK
requires CNF and a chart; we have a WPDA walker with Pratt dispatch).

**One micro-tactic is worth a note in our docs**: the contrastive
estimation idea — *penalize rules that fire on examples we know should be
REJECTED* — could improve the `training.rs` SGD loop if we ever start
collecting negative parse examples (currently we only train on positives).
That's an enhancement to existing training infrastructure (~50-100 LoC),
not a parser-engine change. **Status: DEFER until we have
negative-example corpora**.

The paper does **not** overlap, complement, or contradict the Earley
paper's cycle-handling contribution. They live in entirely different
problem spaces.

---

## The Paper in 320 Words

The authors present **WGCS** (Weighted Grammar-based Classifier System), a
grammar-induction pipeline that learns a weighted context-free grammar
(WCFG) — in Chomsky Normal Form — from a tagged set of positive and
negative example sentences. The induced grammar is then used as a binary
classifier: a new sentence is "accepted" iff stochastic CKY assigns it
non-zero weight under the learned grammar.

Three machinery pieces:

1. **Split algorithm** (Alg. 2, §2.4): structural-induction core. Starts
   from an initial grammar with all O(|N|³) possible CNF productions. At
   each iteration, picks the nonterminal `X_i` that EM has assigned the
   highest total count, manufactures a new symbol `X_j`, and creates 8 new
   nonterminal productions covering combinations of `X_i`/`X_j`. Grammar
   grows monotonically — Eq. 12 estimates final size at `k²·|T| + k⁴` for
   k iterations.

2. **Inside-Outside (Baker 1979)** (§2.5.1): standard EM for PCFG weight
   re-estimation. For each rule `X → YZ`, computes expected use count
   `c_ϕ(X→YZ, W) = ϕ(X→YZ)/P(W) · Σ_{i,j,k} α_{ik}(X)β_{ij}(Y)β_{j+1,k}(Z)`,
   then renormalizes by LHS sum.

3. **Inside-Outside Contrastive Estimation (IOCE)** (§2.5.2): the paper's
   novel weight-estimation step. Multiplies standard re-estimated weight by
   `ψ(X→α) = count(X→α) / (count(X→α) + θ·count_neg(X→α))` where `θ` is a
   balance ratio. Rules that explain negative examples are penalized.

Maintenance pass removes rules below 10⁻³ (nonterminal) or 10⁻⁶
(terminal) (§2.6). Wrapped in a 20-iteration outer loop (Alg. 3)
terminating when F1 stabilizes. Complexity: `O((y+z)·k³L⁴(z·n·k+y))`.
Benchmarks: 28 datasets (L₆ balanced parens, L₈ palindromes, L₉/L₁₀
count-based, L₁₁ Łukasiewicz). Beats LS and ADIOS in F1.

---

## Axis-by-Axis Judgment

| Axis | Paper | Current impl | Verdict |
|------|-------|--------------|---------|
| **Problem** | Learn an unknown CFG from positive+negative example sentences | Hand-written grammar via `language!` DSL; parse known languages | **DIFFERENT PROBLEM.** |
| **Grammar form** | CNF only (X→YZ or X→t) | Arbitrary RHS with mixfix, binders, precedence | Restriction is **far too tight**. |
| **Parser** | Stochastic CKY (O(L³|N|³)) | WPDA + Pratt | **PARADIGM MISMATCH** (same as Earley). |
| **Weight semantics** | Probability semiring only | 12+ semirings under uniform `Semiring`/`SemiringRef` | We are **strictly more general**. |
| **Learning machinery** | Inside-Outside (Baker EM) | `training.rs` SGD over LogWeight | We have **most of the EM machinery already**. |
| **Structural induction** | Iteratively grows the grammar | We never grow grammars at runtime | **No application.** |
| **Negative-example use** | IOCE penalizes rules firing on rejected sentences | `training.rs` only on positives | **Only adoptable idea** — see "Worth a note". |
| **Cycle handling** | Not addressed (CNF avoids cycles by construction) | Phase C tri-color skip + Earley `(I⊕A)*` | **Silent.** |
| **Pruning** | Constant thresholds (10⁻³ / 10⁻⁶) | Tropical beam pruning + dead-rule elimination | Ours is **principled**. |
| **PraTTaIL bugs** | Not addressed | All open | **Paper solves NONE.** |

---

## All Augmentations Found

I evaluated the paper against the 8 likely-contribution areas. Verdict for each:

| # | Technique | Where in our codebase | LoC | Risk | Recommendation |
|---|-----------|----------------------|-----|------|----------------|
| 1 | Tree IO over SPPF | sppf.rs + sppf_realize.rs + new outside-weight field | 600-900 | MED-HIGH | DEFER — would solve `training.rs:16-24` "Known Limitation" but no current demand |
| 2 | CKY/CYK split recursion | Replaces walker entirely | 5-8k | HIGH | SKIP — same verdict as Earley paper |
| 3 | EM/Inside-Outside parameter estimation | training.rs::update() | 150-250 | MED | DEFER until #1 (no expected counts without tree IO) |
| 4 | Hyperedge-replacement repr | n/a | — | — | N/A — not in paper |
| 5 | Split factoring for sparse productions | macros/src/logic/mod.rs | unknown | HIGH | SKIP — induction primitive, not parser primitive |
| 6 | Lehmann / matrix closure for cyclic semirings | n/a | — | — | N/A — paper silent; Earley paper covers this |
| 7 | Approximate parsing / beam pruning | transducer.rs::BeamPruning already does better | 0 | — | SKIP — strictly weaker than ours |
| 8 | Streaming / incremental induction | n/a — wrong axis | — | — | N/A |
| 9 (extra) | **Contrastive estimation with negative examples (IOCE)** | training.rs::update() | 50-100 | LOW | DEFER until negative-example corpora exist |

### The one Useful Augmentation (Augmentation 9 in detail)

**Technique**: §2.5.2, Eq. 8. After standard EM re-estimates `count(X→α)`,
multiply by `ψ(X→α) = count(X→α) / (count(X→α) + θ·count_neg(X→α))` where
`count_neg` is the count of the rule firing on negative (rejected)
examples and `θ = #positive / #negative` is a balance factor. Rules firing
more on negatives get smaller `ψ`, so their re-estimated weight shrinks.

**Adoption**: ~50-100 LoC in `prattail/src/training.rs::update()`. Add a
`TrainingExample::expected_rejection: bool` flag; accumulate two count
maps (`expected_correct` for `is_accept=true`, `expected_negative` for
`is_accept=false`); multiply gradient by `ψ` before applying.

**Benefit**: Lets users train grammar disambiguator weights on *bad*
parses ("this string parses as integer multiplication but should be string
concatenation") as well as good ones. Currently only positive supervision.

**Trade-offs**: Requires negative-example corpus collection. Adds a
hyperparameter `θ`. Risks over-penalizing useful rules if negative
examples are noisy.

**Why deferred**: We have no negative-example corpora for any PraTTaIL
grammar today. File as future enhancement docs note.

---

## Comparison with the Earley Paper

| Dimension | Earley (Opedal et al., ACL 2023) | Split-Based (Gabor et al., MDPI 2021) |
|-----------|----------------------------------|---------------------------------------|
| **Subject** | How to parse efficiently given a weighted CFG | How to learn a weighted CFG given example sentences |
| **Algorithm** | Earley deduction system + closed-semiring cycle handling | Stochastic CKY + Inside-Outside EM + Split |
| **Semiring abstraction** | Full (general `<W,⊕,⊗,0,1>`, `⋆` for cycles) | Probability semiring only |
| **Novel result** | Cycle elimination via Lehmann's matrix-star | Split + IOCE for joint structure+weight induction |
| **Relevance to PraTTaIL** | Modest — one adoptable cycle-handling technique (~300-500 LoC) | Essentially none — different problem |
| **Overlap** | None | None |
| **Contradicts** | No | No |
| **Complements** | N/A | N/A |
| **Stronger / weaker than Earley** | Stronger on cycle theory; same problem space | Orthogonal — different problem |

**No interaction.** The Earley paper's `(I⊕A)*` cycle-handling technique
is independent of and unaffected by the Split paper's IOCE training
enhancement. They could both be adopted, separately, with no conflict.

---

## Honest Accounting of the Paper's Caveats

1. **The split operator is monotonically grammar-growing.** §2.6 confirms it leads to grammars that need aggressive pruning. Induced grammars are not minimal.
2. **CNF restriction is severe.** Every interesting NL or PL phenomenon requires non-trivial CNF encoding that obscures structure.
3. **Benchmarks are toy languages.** Maximum sentence length 20, 100-300 examples. No evidence of scalability.
4. **Pruning thresholds (10⁻³, 10⁻⁶) are experimental, not principled.** §2.6: "These values have been determined experimentally."
5. **Runtime is dataset-quadratic.** `O((y+z)·k³L⁴(z·n·k+y))`. For test inputs of length 50-200, `L⁴` would be prohibitive.
6. **IOCE balance factor `θ` is heuristic.** No theoretical justification.
7. **Comparison baselines are weak.** No comparison to modern neural grammar inducers.

---

## Prioritized Recommendation List

1. **Adopt nothing immediately.** None of the paper's contributions are needed for the current weighted-SPPF + WPDA roadmap.
2. **Defer Augmentation 9 (IOCE contrastive training)** to a future docs note in `prattail/docs/design/wfst/weight-training.md`. Cost ~50-100 LoC if/when we collect negative-example corpora.
3. **Defer Augmentation 1 (tree inside-outside over SPPF)** to a future "Phase E" (training-on-parse-forests) plan. Cost ~600-900 LoC.
4. **Reject Augmentations 2, 4, 5, 6, 7, 8** — irrelevant, weaker than existing, or paradigm-incompatible.
5. **Continue with the prior priorities**: Earley paper's `(I⊕A)*` cycle handling (~300-500 LoC, lifts `IdempotentSemiring` bound) remains the single highest-value parser-side adoption from recent papers.
6. **The four PraTTaIL bugs** (cross-category fold discriminator, 21 R1 alt-selection failures, cursor.builder mirror, multi-cat union extract) get **zero help** from this paper.

---

## Critical Files for Implementation

If any augmentation were ever adopted:

- `prattail/src/training.rs` — would receive the IOCE enhancement (Augmentation 9).
- `prattail/src/forward_backward.rs` — would be extended with tree-shaped inside-outside (Augmentation 1).
- `prattail/src/sppf.rs` — would gain an `outside_weight: W` field on `Symbol` nodes for Augmentation 1.
- `prattail/src/sppf_realize.rs` — would gain an outside-recurrence pass.
- `prattail/docs/design/wfst/weight-training.md` — would document the IOCE option.
