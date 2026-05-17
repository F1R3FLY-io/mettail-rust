# Earley Paper vs Current Weighted SPPF — Comparison

**Date**: 2026-05-17
**Paper**: Opedal et al. (ACL 2023), "Efficient Semiring-Weighted Earley Parsing"
**Source**: `/home/dylon/Papers/Efficient Semiring-Weighted Earley Parsing.pdf`
**Status**: review complete; recommendation below

---

## TL;DR

**DO NOT replace the current weighted SPPF.** The paper targets context-free
chart parsing; our parser is a Weighted Pushdown Automaton walker driving
Pratt-style precedence-climbing infix dispatch. The formalisms are not
interchangeable. The paper's weighted semantics ARE the semantics we already
implement (Goodman 1999); switching would not produce different weights.

**DO consider the closed-semiring cycle-handling technique (paper §6, App E)
as a future Phase C-bis** to lift the `IdempotentSemiring` bound on
`realize_root_to_terms`. ~300-500 LoC integration cost, no walker rewrite.

---

## The Paper in 250 Words

Opedal et al. (ACL 2023) provide a unified reference description of Earley's
1970 CFG parsing algorithm recast as a **deduction system** with three
variants:
- `Earley` (O(N³|G||R|))
- `EarleyFast` (O(N³|G|)) — folds COMP and PRED to remove the `|R|` factor
- `EarleyFSA` (O(N³|M|)) — replaces dotted productions with WFSA states

Items have the form `[i,j,A→μ•ν]` (incomplete) and `[i,j,A→μ•★]` (complete,
`★` = wildcard). The semiring is the standard 5-tuple `<W,⊕,⊗,0,1>`. Each
derivation tree's weight is `⊗` of its productions (eqn. 1); recognition
weight is `⊕` over derivations of x (eqn. 2). Each Earley item carries an
**inside weight** `β̂(V)`; semiring-weighted parsing means each deduction
rule contributes `⊕`-summands of products of antecedent inside weights.

Two principal weighted-parsing contributions:
1. **Cycle elimination by grammar transformation** (Apps E, F): pre-process
   the grammar to remove unary cycles and nullary productions, so the
   deduction system becomes acyclic. Cycles are handled by computing
   `(I⊕A)*` via Kleene-Floyd-Warshall (Lehmann 1977) in *closed semirings*
   — requiring a `⋆` operator for geometric-series sums.
2. **Prefix-weight computation** (§6.1, App G): a second weight `α̇(V)`
   (prefix-outside) on each item; correct without left-recursion unless
   the left-corner transform of App G.1 is applied.

Worst-case complexity matches CYK on a binarized grammar; commutative `⊗`
assumed.

---

## Axis-by-axis Judgment

| Axis | Paper | Current impl | Verdict |
|------|-------|--------------|---------|
| **A. Algorithmic foundation** | Earley deduction system on CFG | WPDA poststar walker + lex-Fork branching → SPPF | Different paradigms. Earley does NOT subsume Pratt: no binding-power dispatch. **Paper not applicable as drop-in.** |
| **B. Weight semantics** | `w(T) = ⊗ w(A→ρ)` (eqn. 1); inside `β̂(V)` aggregates via `⊕` at merge | `Packing.weight` per production, `Symbol.weight_sum = ⊕ packing.weight ⊗ children` | **Mathematically identical** — both Goodman 1999. Our `pending_packing_weight` is the WPDA-flavored way of pulling per-rule weight out of cumulative `cursor.weight`. |
| **C. Cycle handling** | **Pre-process** grammar to remove unary + nullary cycles (Apps E, F). Closed-semiring `⋆` only when SCCs remain | **Run-time** tri-color DFS skips back-edges; correct only under `IdempotentSemiring` | Paper is **more principled** — eliminates the run-time semiring restriction. **However**: paper's elimination can up to double grammar size. **Adaptable but expensive.** |
| **D. Data structure** | Chart (`T_j`) of items; proofs reconstructed from backpointers | Scott-Johnstone packed SPPF (Symbol-dedup by `(nt,lo,hi)`) | **Equivalent worst-case asymptotic** (O(N³|G|)). SPPF is purpose-built for ambiguous parses with shared subtrees; chart is an *implicit* SPPF. **SPPF is more explicit** and supports determinism/checkpoint/realize invariants. |
| **E. Implementation effort** | Would throw out ~11k LoC of WPDA walker | Current impl ~2500 LoC | **Full migration: ~12-15k LoC across walker, SPPF, codegen.** |
| **F. Mandate alignment** | Inside weights `⊕`-aggregated; produces ONE Z_x at the goal | Our `Vec<(Term, W)>` preserves all derivations | **Current impl is more P1-aligned** — paper's "Z_x" → enumeration requires Goodman's derivation semiring (App A passing reference) which is what SPPF gives out of the box. |
| **G. WPDA/walker interaction** | Earley chart; no WPDA concept | Walker drives infix dispatch via binding-power tables | **Paper does not apply to WPDA-derived parse forests.** |
| **H. Specific issues** | Not addressed | We have these as separate bugs | **Paper solves NONE** of: fold-rule discriminator, R1 alt-selection, cursor.builder, multi-cat union extract. All are WPDA-walker bugs, not parse-forest bugs. |

---

## What the Paper DOES Offer (Adoptable as Augmentation)

### 3a. Closed-semiring cycle handling (paper §6, App E)

Phase C constrains `realize_root_to_terms<W: IdempotentSemiring>`; we skip
back-edges via tri-color DFS. The paper does better: solve `(I⊕A)*` for
each SCC via Floyd-Warshall in a closed semiring, supporting non-idempotent
semirings (`CountingWeight`, `LogWeight`).

**Adoption cost: ~300-500 LoC** in `prattail/src/wpda_walker.rs::realize_*`:
1. Detect SCCs in SPPF cycle subgraph during DFS (Tarjan ~80 LoC).
2. Build `W` adjacency matrix per SCC (~60 LoC).
3. Call `matrix_star` via Kleene-Floyd-Warshall (~150 LoC).
4. Replace tri-color skip with `⋆`-aggregated weight at SCC roots (~100 LoC).

**Benefit**: lifts the `W: IdempotentSemiring` bound — enables `LogWeight`,
`CountingWeight`, `EntropyWeight` realize.

**Status**: matches the migration path already documented in
`~/.claude/plans/phase-c-sppf-w-resolved.md` §Q2.B.

### 3b. Grammar pre-processing to eliminate cycles (Apps E, F)

Transform the grammar at codegen time so unary cycles + nullary productions
are gone. **Cost: ~600-1000 LoC**, can up to DOUBLE grammar size. **Skip.**

### 3c. EarleyFSA-style WFSA grammar encoding (paper §7)

Shares structure across productions with common prefixes. Beneficial for
50k-production NLP grammars; **not for PraTTaIL grammars** (rhocalc, calc,
ambient: 10-50 productions). **Skip.**

---

## What We Would LOSE by Switching to Earley

- **Pratt-style binding-power dispatch**: no Earley counterpart.
- **Lex-Fork branching at the WPDA layer**: paper assumes fixed token stream.
- **`LexicographicWeight` left-projection semantics**: paper assumes
  commutative `⊗` (App K notes non-commutative case requires WFSA encoding
  and breaks unary cycle elimination).
- **SPPF determinism and checkpoint/restore**: paper's chart is a HashMap,
  not arena-indexed. Our `SppfId`/checkpoint powers `WpdaIncrementalSession`.
- **Realize-time `ActionResolver` pluggability**: paper has no realize phase
  — proofs reconstructed via backpointers, user-AST construction out of
  scope.

---

## What STAYS the Same

The paper's weighted semantics ARE the semantics we already implement
(Goodman 1999). `Sppf<W>`'s `Packing.weight`, `Symbol.weight_sum`, and
`link_packing_to_symbol`'s `⊕`-accumulation are textbook semiring parsing.
The paper would not change ANY of:
- `prattail/src/sppf.rs` data structures
- `prattail/src/sppf_realize.rs` cartesian-product realize
- The `Semiring`/`SemiringRef`/`IdempotentSemiring` trait hierarchy
- The `pending_packing_weight` cursor mechanism

---

## Recommendation

**DO NOT replace** the current weighted SPPF implementation with the paper's
Earley deduction system. Reasons:
1. Paper targets context-free chart parsing; we have a WPDA + Pratt parser.
   Formalisms are not interchangeable.
2. Our `Sppf<W>` already implements the paper's semantic content. The paper
   would not produce different weights for our grammars.
3. The four "specific issues the paper might solve" are WPDA-walker bugs,
   not parse-forest bugs. The paper is silent on them.
4. Full migration cost: rewrite ~15k LoC for no semantic gain.

**DO consider** the closed-semiring cycle handling (§3a above) as a future
**Phase C-bis** to lift the `IdempotentSemiring` bound. This is the only
paper contribution that is *both* algorithmically more principled than what
we have *and* implementable without rewriting the walker. The infrastructure
exists (`StarSemiring`, `matrix_star` semantics in our `LogWeight`, etc.);
estimated ~300-500 LoC integration. The existing Phase C plan even mentions
this as the explicit migration path ("Q2.B").

**DO NOT** consider the grammar-preprocessing approach (§3b): too much
codegen complexity for too little practical benefit.
