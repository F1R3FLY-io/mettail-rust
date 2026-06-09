# Dovetail-Core — Implementation Plan (design of record)

> Engine-primary foundation. `dovetail` = the standalone, substrate-agnostic, extractable
> core of the off-Ascent GSLT reduction engine (generic-`W` WTA over a runtime e-graph =
> DFTA, with N-best/set-valued cube-pruning extraction). Designed by a Plan agent against
> the live codebase (2026-06-09). Tracked: pgmcp `dovetail-core-standalone-wta-egraph-crate`
> (#279) under epic `dovetail-gslt-reduction-engine-f1r3node-target` (#278); session task #15.

## 0. Executive summary

`dovetail-core` reuses the proven generic algebra from `prattail/src/automata/semiring.rs`
(`Semiring`/`StarSemiringRef` + `solve_scc_weights_newton` + `matrix_star_ref`), the genuine
WTA in `prattail/src/tree_automaton.rs`, and the e-graph core in `prattail/src/egraph.rs`,
**without depending on `prattail`**. Survey findings that drive the plan:
- `tree_automaton.rs`: only **5** call sites in prattail (`pipeline.rs`×3, `type_system.rs`×2).
- `egraph.rs`: ~**6** call sites (`pipeline.rs`, `lint.rs`), all compile-time, off the runtime path.
- `semiring.rs`: 30+ consumers, BUT couples to prattail in exactly **one** place —
  `crate::sppf::PackingFactored<W>` (a 7-line already-generic struct
  `{ target_i: usize, outside_product: W, in_scc_children: Vec<usize> }`), trivially severable.
- `semiring.rs` already contains `NbestEntry` (:2046) + `NbestWeight<const N>` (:2086) — reusable N-best infra.

## 1. Dependency-reuse decision: **move-down + invert, as a 3-layer split** (hybrid a+c)

Create **two** crates:
1. **`dovetail-semiring`** — the pure-algebra subset of `semiring.rs` with zero prattail
   coupling: the trait hierarchy (`Semiring`, `SemiringRef`, `StarSemiring`, `StarSemiringRef`,
   `DetectableZero`, `IdempotentSemiring`, `CompleteSemiring`), the `*Weight` types,
   `matrix_star_ref`, `solve_scc_weights_newton`, and a **relocated, decoupled** `PackingFactored<W>`.
2. **`dovetail`** — WTA + runtime e-graph + N-best extractor + rules-as-data + tuplespace trait;
   depends on `dovetail-semiring`.

`prattail` then depends on `dovetail-semiring` and **re-exports** the moved items from
`prattail::automata::semiring` (`pub use dovetail_semiring::*;`) so its 30+ `use
crate::automata::semiring::...` call sites compile unchanged. `sppf.rs` does
`pub use dovetail_semiring::PackingFactored;`.

**Rejected:** pure-(a) wholesale move into dovetail-core (fails substrate-agnosticism via the
sppf coupling); (b) duplicate/fork (6503-line file under active FV — `SemiringLaws.v` — would
drift, only one copy certified); (c)-alone (doesn't deliver the WTA/e-graph relocation).

**Blast radius (measured):** Increment 1 is a pure move + `pub use` facade ⇒ **zero edits** to
the 30+ consumers; only non-test edits are `sppf.rs` re-export (~3-5 lines) + the
`solve_scc_weights_newton` callsite path. **Gate after Increment 1:** prattail lib **4350/0**,
op-suite **no regression past the 217 baseline** (commit `28d4d26`), `rocq` (SemiringLaws)
green. For `tree_automaton.rs`/`egraph.rs`, dovetail-core grows its OWN clean modules (the
generic WTA is small; the runtime e-graph is payload-generic + exact-keyed, distinct from
prattail's compile-time `String`-keyed one) — prattail's copies stay put; convergence is a
later optional refactor (Increment 9, deferred).

## 2. Crate layout + public API

```
dovetail-semiring/  src/{lib,traits,weights,closure}.rs   # extracted algebra + decoupled PackingFactored
dovetail/           src/lib.rs                             # crate root + feature gates (engine OFF default)
                    src/key.rs                             # ContentKey (exact byte key) + SemanticHash trait
                    src/egraph/{mod,union_find,congruence}.rs  # runtime payload-generic exact-keyed e-graph
                    src/wta/{mod,dfta}.rs                  # generic-W WTA wired to e-classes (DFTA view)
                    src/extract/{mod,nbest,closure}.rs     # N-best/set-valued cube-pruning (research-grade core)
                    src/rules/{mod,driver}.rs              # rules-as-data + saturation driver
                    src/space/{mod,inmem}.rs               # tuplespace-shaped trait (C,P,A,K)+Match seam
formal/rocq/dovetail/theories/{ExactKeyDedup,NBestExtraction}.v   # new rocq-dovetail target
```

**Exact-key linchpin (HARD constraint — NOT 64-bit hash, NOT String):**
```rust
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ContentKey(pub Box<[u8]>);          // owned exact bytes; Ord => total tiebreak
pub trait SemanticHash {
    fn write_content(&self, out: &mut Vec<u8>);  // exact buffer, not a 64-bit Hasher
    fn content_key(&self) -> ContentKey { /* write into Vec<u8> -> boxed slice */ }
}
```
**N-best extractor (HARD: ORDER not PRUNE; equal-weight distinct alts BOTH survive; refute only at `0̄`):**
`extract_nbest<P,W: StarSemiringRef + Ord>(eg, dfta, root, cfg) -> Vec<Derivation<W>>` —
ordered by `(W, ContentKey)`; distinct `ContentKey`s never merge even at equal `W`; a
candidate is discarded only when its composed weight `is_zero()`.

Tuplespace trait `TupleSpace<C,P,A,K>` + `Match<P,A>` seam (in-mem default only; the future
Reified-RSpace mapping inner=PriorityQueue/outer=PathMap/seam=Match is a documented seam, no
reified-rspace dep). Engine `default = []`; added to workspace `members` but nothing in the
existing build path depends on it ⇒ mandatory dependency set unchanged.

## 3. Increments (each: adds / tested / gate = `cargo check --workspace` green + prattail 4350/0 + op-suite ≤217 + relevant `rocq-*` zero-admission)

1. **`dovetail-semiring` extraction** (only prattail-touching step; land + verify ALONE). Move algebra + decoupled `PackingFactored`; prattail `semiring.rs`/`sppf.rs` → `pub use` facades. Gate: prattail 4350/0; op-suite ≤217; SemiringLaws green.
2. **crate skeleton + `key.rs`** (`ContentKey`, `SemanticHash`). Tests: key determinism; distinct byte-streams → distinct keys. *(safe, independent of #1)*
3. **runtime payload-generic exact-keyed e-graph** (`add`/`merge`/`rebuild` + carried `try_add_with_budget`/`rebuild_exact_indices`/`node_limit_reached` from b56e1e5). Tests: port prattail congruence/budget tests; a 64-bit-collision-but-distinct-`ContentKey` pair stays 2 classes (Rust refutation of `hash_only_pair_dedup_can_drop_distinct_keys`).
4. **generic-`W` WTA wired to e-classes** (`WtaTransition<W>`, `EGraphDfta`). Tests: tiny e-graph, assert transitions+weights.
5. **N-best/set-valued cube-pruning extractor (acyclic)** — Huang–Chiang lazy k-best over the hypergraph by composed weight; set semantics. Tests: two equal-weight distinct alts BOTH appear; zero-weight alt dropped; k-truncation = k smallest by `(W,key)`.
6. **cyclic e-class weight closure** — SCC → `PackingFactored` → `solve_scc_weights_newton`. Tests: self-referential class under idempotent semiring terminates.
   — **M-E.0 "inert" milestone = increments 1–6** (skeleton + WTA on runtime e-graph + N-best, engine gated off, no f1r3node binding, zero new mandatory deps).
7. **rules-as-data + reduction driver** (`Sexpr`/`Rule`/`Program` + `saturate`).
8. **tuplespace trait + in-mem impl.**
9. **convergence pass** (prattail `tree_automaton.rs` generic core → `pub use dovetail::wta::*`) — DEFER if it risks the baseline.

## 4. FV obligations (zero-Admitted/zero-Axiom; new `rocq-dovetail` target in `formal/Makefile` mirroring `rocq-egraph`)
1. **`ExactKeyDedup.v`** — generalize `exact_key_pair_dedup_preserves_distinct_keys` (RuntimeModel.v:2639) + `weighted_…` (2843) from 2-element to n-element exact-`ContentKey` lists; carry the negative `hash_only_pair_dedup_can_drop_distinct_keys` (2937) forward. Certifies Increment 3.
2. **`NBestExtraction.v`** — k-best set = k weight-minimal DISTINCT derivations by `(W,key)`; **no distinct alternative dropped except at `0̄`** (runtime analogue of `parser_preserves_ambiguous_alternatives`). Reuse `SemiringLaws.v` monoid/distributivity + `WpdsCorrectness.v` monotonicity pattern. + a lemma that SCC→`PackingFactored` lowering preserves the weight equations (so the existing Newton-SCC proof carries over). Certifies Increments 5-6.
3. **Congruence/rebuild (reuse)** `EGraphCongruence/EGraphSaturation/EGraphBudgetDedup.v` — confirm generic `EGraph<P>` preserves the same invariants.

## 5. Honest scope
- **Quick wins:** Inc 1 (mechanical move; 1 coupling point), Inc 2 (key), Inc 4 (WTA view), Inc 8 (trait).
- **Moderate:** Inc 3 (payload-generic exact-keyed e-graph), Inc 7 (driver).
- **Research-grade (budget generously):** Inc 5+6 + FV §2 — lazy k-best over a *cyclic* hypergraph interleaved with Newton-SCC closure, with set-valued/refute-only-at-`0̄` semantics that FORBID the usual keep-argmin pruning; the no-drop-except-at-zero proof is real, not reuse.
- **Out of scope here:** any f1r3node/RSpace binding; the Reified-RSpace concrete impl; flipping any evaluator off Ascent (M-RHO.4 / task #20); the prattail-egraph→dovetail convergence (Inc 9).

## 6. Critical files
Create: `dovetail-semiring/src/{lib,traits,weights,closure}.rs`; `dovetail/src/{lib,key}.rs`,
`dovetail/src/egraph/*`, `dovetail/src/wta/*`, `dovetail/src/extract/*` (esp. `nbest.rs` — the
research core), `dovetail/src/{rules,space}/*`; `formal/rocq/dovetail/{_CoqProject,theories/*}`.
Modify (small): workspace `Cargo.toml` members; `prattail/Cargo.toml` dep; `prattail/src/automata/semiring.rs`
→ facade; `prattail/src/sppf.rs` re-export; `formal/Makefile` `rocq-dovetail` target.
