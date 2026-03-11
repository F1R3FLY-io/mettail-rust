# N06-ISO: Bisimulation Isomorphic Group Extension

Advanced Automata Codegen Optimization — M3 Alternating → Shared Templates

## 1. Quick Start

**What it does**: Extends isomorphic category groups beyond De Bruijn
structural isomorphism to include bisimulation-equivalent categories.
Categories that accept the same weighted language can share dispatch
templates, reducing generated code volume.

**When it activates**: When the `alternating` feature is enabled and
`AlternatingAnalysis.non_bisimilar_pairs` does not cover all category
pairs (i.e., some pairs are bisimilar).

**Feature gate**: `alternating`

**Optimization gate**: `bisimulation_iso_groups` (env: `PRATTAIL_OPT_BISIMULATION_ISO_GROUPS`)

**Status**: `OptimizationStatus::Auto`

## 2. Intuition

De Bruijn structural isomorphism (Sprint 8) detects categories with
identical WFST structure: same states, transitions, and action shapes,
differing only in labels. This catches cases where two categories are
syntactic copies.

Bisimulation equivalence is strictly more powerful. It detects categories
that accept the same language even when their automata have different
structure:

```
Category Expr:                  Category Pattern:
  q0 →[num] q1                   p0 →[num] p1
  q0 →[var] q1                   p0 →[var] p1
  q0 →[op] q2 →[expr] q3 →...   p0 →[op] p2 →[pat] p3 →...
                                  (same language, different state names)
```

De Bruijn: NOT isomorphic (different internal names)
Bisimulation: EQUIVALENT (same observable behavior)

```
De Bruijn groups ⊂ Bisimulation groups ⊂ All categories
```

## 3. Algorithm

```
Input:  AlternatingAnalysis.non_bisimilar_pairs
        Existing isomorphic_groups from De Bruijn analysis
Output: Extended isomorphic_groups

already_grouped = flatten(existing isomorphic_groups)
non_bisimilar = set(non_bisimilar_pairs ∪ reversed pairs)

for each pair (cᵢ, cⱼ) where i < j:
    if cᵢ ∉ already_grouped && cⱼ ∉ already_grouped:
        if (cᵢ, cⱼ) ∉ non_bisimilar:
            isomorphic_groups.push([cᵢ, cⱼ])
```

## 4. Theory

A bisimulation R ⊆ Q₁ × Q₂ between automata A₁ and A₂ satisfies:
- If (p, q) ∈ R and p →ₐ p', then ∃ q →ₐ q' with (p', q') ∈ R
- If (p, q) ∈ R and q →ₐ q', then ∃ p →ₐ p' with (p', q') ∈ R

Bisimulation is sound and complete for language equivalence on finite
alternating automata (Milner 1989). If bisim(A_c₁, A_c₂) = true, then
L(A_c₁) = L(A_c₂) and sharing dispatch code is correct.

See [codegen-soundness.md](../theory/optimization/codegen-soundness.md) §5.

## 5. Diagnostics

- **N06** (weighted-parity-non-convergent): Related alternating analysis lint
- **N07** (weighted-branching-imbalance): Related alternating analysis lint

## 6. Related

- [Sprint 8 Isomorphic WFST Detection](README.md) — Base De Bruijn isomorphism
- [Alternating Automata Design](../design/polynomial-awa.md) — Full M3 design
