# 16 — In-Rho Matching: Verification Plan

> The end-to-end formal-verification strategy for the in-Rho set-automaton
> integration ([15](15-in-rho-set-automaton-matching.md)). **Rocq is the default
> theorem prover** (zero-admission — `Print Assumptions` = "Closed under the global
> context"; no `Admitted`/`Axiom`/`Parameter`, enforced by
> `formal/scripts/check_rocq_zero_admission.py`). Wolfram 15, TLA+/Apalache, and
> mCRL2/Maude are the finite / symbolic / CLTS-bisimilarity complements — the
> executable floor under each unbounded Rocq theorem, never a substitute for it.
> This document tracks each obligation and its status.

## 1. What must be verified

Correctness is fixed at the context-labelled transition system (CLTS) of
`knotted-topoi.tex` (`prop:opcorr`). Moving matching into Rho preserves it iff the
internal `sa:`/`eq:` COMMs are unobservable (`$\tau$`) and the optimal channel
naming induces the same CLTS as the sound one — the tex's `rem:nonopt` claim,
which the in-Rho realization finally forces to be *proven* rather than inherited.

## 2. Obligations

### 2.1 Structural matching (the two set-automaton papers)

| # | Obligation | Rocq theory | Primary + complement |
|---|---|---|---|
| (i) | in-Rho match set = positional matching relation (sound + complete) | `InRhoMatchPositional.v` | Rocq (reinstantiate `PositionalSetAutomatonSound.v`'s `children_match` with the `sa:`-chain) + the `properties.rs` oracle |
| (ii) | `O1` symbol-once: symbol `$\mapsto$` `sa:`-receive is total + injective | `SymbolOnceInjective.v` | Rocq + Wolfram inspection-count |
| (iii) | `sa:`/`eq:` are `$\tau$` `$\Rightarrow$` same CLTS (weak bisimulation) | `InRhoSameCLTSWeakBisim.v` | mCRL2 + Maude (finite) + Rocq `RhoCommScheduleFamily` (unbounded) |
| (iv) | atomic firing / no partial-match reachable state | `AtomicFiringNoPartialMatch.v` | TLA+/Apalache + mCRL2 + Rocq |
| (v) | whole-`$\llbracket G \rrbracket$` `opcorr` with in-Rho matching (capstone) | `WholeGsltInRhoOpCorrespondence.v` | Rocq (instantiate `EndToEndCommCorrespondence.v`) |
| (vi) | non-linear `eq:` commit `$\Leftrightarrow$` name-equality, reject-safe | `NonLinearEqConsistency.v` | Rocq + Maude/Wolfram |
| (vii) | contextual atomic join (INV-6) + plugging-stability (INV-2) | `ContextualAtomicJoinPlugging.v` | Rocq (`SameChannelJoin` `$2\to n$`) + TLA+/mCRL2 |
| (viii) | injective + coarsest-sound `$tc(K)$` channel naming (`O3`, `$R_{op}$`) | `TcChannelNamingQuotient.v` | Wolfram quotient algebra + Rocq |
| (ix) | total-or-reject + persistence for the in-Rho encoder | `InRhoEncoderTotalOrReject.v` | Rocq (extend `RhoLoweringTotalOrRejects.v`) |
| (x) | compile-once / reuse determinism in Rho | `InRhoReuseDeterminism.v` | Rocq (extend `reuse_is_per_node_deterministic`) |
| O2 | prune-preserves-work | `PrunePreservesWork.v` | Rocq + mCRL2 |

### 2.2 AC matching (beyond the papers — reuse the proven multiset/bipartite algebra)

| # | Obligation | Rocq theory | Reuses |
|---|---|---|---|
| (AC-i) | in-Rho AC match set = AC matching relation (multisets) | `InRhoAcMatchMultiset.v` | `DeltaOneMinCostMatching.v`, `MultisetSemiringLaws.v`, `AmbiguitySetPreservation.v` |
| (AC-atom) | atomic, no partial-consume reachable | `AcAtomicNoPartialConsume.v` | `DeltaOneMinCostJoin.v`, `GuardedCommSoundness.v` |
| (AC-rest) | `rest` reconstruction = host `instantiate` AcApp flatten | `AcRestReconstruction.v` | `MultisetSemiringLaws.v` |
| (AC-nl) | non-linear AC commit `$\Leftrightarrow$` name-equality, reject-safe | `AcNonLinearConsistency.v` | composes (vi) |
| (AC-map) | MapAc key-uniqueness + ZipAc correlation preserved by split | `AcMapKeyUniqueness.v` | `MultisetSemiringLaws.v` |

**AC economy:** because the AC match is ONE atomic `consume` (the pick is internal
to a single COMM), AC contributes zero new `$\tau$` steps — it needs NO (iii)-style
weak-bisimulation, and the capstone (v) gains one rule-family arm.

## 3. The load-bearing discharge: `rem:nonopt`

The tex *asserts* that the sound (location-channel) and optimal
(set-automaton-state) schemes induce the same CLTS; the in-Rho realization forces
a proof. The chain is:

$$ \text{(ii) } O1\text{-totality} \;+\; \text{(viii) } tc\text{-injectivity} / R_{op} \;\Longrightarrow\; \text{(iii) weak bisimulation} \;\Longrightarrow\; \text{(v) whole-}\llbracket G \rrbracket\text{ opcorr} $$

(ii) gives `$R_{\mathrm{forward}}$` (every sound firing has a complete `sa:` chain);
(viii) gives `$R_{\mathrm{backward}}$` (distinct `$\sim_{op}$` contexts get distinct
channels, so no cross-talk; the `$R_{dep}$` relation is excluded by a proven
counterexample). (iii) extends `RhoCommScheduleFamily.v`'s `erase_rho` with
`SaInspect`/`EqCheck` constructors whose observation is `$\tau$`, then builds the
weak bisimulation on `RegisterEquivalence.v`'s `is_bisimulation`; (v) instantiates
the assumption-free abstract lift `EndToEndCommCorrespondence.v` and case-splits by
rule family.

## 4. Authoring order (each proof lands with its implementation slice)

`A` (ii `$\to$` i `$\to$` x, matching core) `$\to$` `B` (viii `$\to$` O2, channel
naming) `$\to$` `C` (iii, the `rem:nonopt` discharge) `$\to$` `D` (iv, vi) `$\to$`
`E` (vii) `$\to$` `F` (ix) `$\to$` `G` capstone (v); the AC obligations land with
Stage AC. The capstone flips INV-2/6/13 in [13](13-knotted-topoi-operational-invariants.md).

## 5. Status

| Slice | Implementation | Verification |
|---|---|---|
| M0 spread | done | INV-10 round-trip property (example + proptest); the `$\nu$`-free assertion is the INV-7 executable form |
| M1 matching | done (base case) | validated end-to-end by the runtime match test (`m1_matches_swap_in_rho_and_fires_the_rewrite`), which the RSpace reducer checks; the arity-general De Bruijn frame + the no-false-positive negative case are covered; the Phase-A Rocq theorems (ii/i/x) are the next verification step |
| M2 channel re-keying | pending | (viii), O2 |
| M3 `$\tau$` internalization | pending | (iii) — the `rem:nonopt` discharge |

The Rust example / property / integration tests are the executable floor; the Rocq
theorems above are the unbounded ceiling, authored one slice at a time under the
zero-admission gate.
