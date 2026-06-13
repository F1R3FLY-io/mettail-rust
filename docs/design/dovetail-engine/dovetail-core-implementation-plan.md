# Dovetail-Core — Implementation Plan (design of record)

> Engine-primary foundation. `dovetail` = the standalone, substrate-agnostic, extractable
> core for MeTTaIL rewrite semantics on the CESK runtime-backend replacement path
> (generic-`W` WTA over a runtime e-graph = DFTA, with N-best/set-valued
> demand-driven best-first enumeration extraction). The active WPDA
> parser/recognizer remains upstream. Ascent is legacy for production rewrite
> execution and remains only as a reference/oracle path. Designed by a Plan agent against
> the live codebase (2026-06-09). Tracked: pgmcp `dovetail-core-standalone-wta-egraph-crate`
> (#279) under epic `dovetail-gslt-reduction-engine-f1r3node-target` (#278); session task #15.

## Governing invariant — extraction completeness (NO missed results)

The single gate is **"does it miss a result?"** — the technique's name is irrelevant.
**Admissible search heuristics are DESIRABLE**, not suspect; only *inadmissible / lossy*
heuristics are forbidden. Concretely:
- **Admissible heuristics (A* / KA*) are encouraged.** Guiding the best-first search with
  an *admissible* heuristic — a lower bound on the remaining weight-to-complete (e.g. the
  bottom-up 1-best "inside" weight, computed in one pass) — provably preserves true
  non-decreasing-weight order AND completeness while exploring far less. This is exactly
  "follow the most-likely paths by the metrics," done correctly. **Use such heuristics.**
- **Forbidden: inadmissible / lossy heuristics** that can overestimate and skip a genuine
  result — e.g. a *cube-pruning beam* (bounded frontier) or a top-k *cutoff* that discards
  the rest. These introduce missing-result bugs and are out.
- **Demand only DEFERS** computation — the stream is *resumable to exhaustion*; pulling
  further always yields the next result and can surface every alternative. A "k" is just
  how far the caller has pulled, never a cutoff.
- **The ONLY removal** of an alternative is by **evidence** (rewrite-to-`⊥`, guard/type
  refutation, exact-key observational-equality dedup) — never by weight, beam, or heuristic.
- **Weight ORDERS** the stream; it never PRUNES.
- **Default mechanism:** **A* / KA* best-first enumeration** over the hypergraph with the
  1-best inside weight as the admissible heuristic (provably exhaustive-on-demand,
  optimal-order). Any *different* technique may replace it only with a no-miss proof *plus*
  a differential check that its output set equals the exhaustive enumeration's. (An
  admissible-heuristic A* needs no such extra proof beyond admissibility itself.)

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
1. **`rigail`** — the pure-algebra subset of `semiring.rs` with zero prattail
   coupling: the trait hierarchy (`Semiring`, `SemiringRef`, `StarSemiring`, `StarSemiringRef`,
   `DetectableZero`, `IdempotentSemiring`, `CompleteSemiring`), the `*Weight` types,
   `matrix_star_ref`, `solve_scc_weights_newton`, and a **relocated, decoupled** `PackingFactored<W>`.
2. **`dovetail`** — WTA + runtime e-graph + N-best extractor + rules-as-data + tuplespace trait;
   depends on `rigail`.

`prattail` then depends on `rigail` and **re-exports** the moved items from
`prattail::automata::semiring` (`pub use rigail::*;`) so its 30+ `use
crate::automata::semiring::...` call sites compile unchanged. `sppf.rs` does
`pub use rigail::PackingFactored;`.

**Rejected:** pure-(a) wholesale move into dovetail-core (fails substrate-agnosticism via the
sppf coupling); (b) duplicate/fork (6503-line file under active FV — `SemiringLaws.v` — would
drift, only one copy certified); (c)-alone (doesn't deliver the WTA/e-graph relocation).

**Blast radius (measured):** Increment 1 is a pure move + `pub use` facade ⇒ **zero edits** to
the 30+ consumers; only non-test edits are `sppf.rs` re-export (~3-5 lines) + the
`solve_scc_weights_newton` callsite path. **Gate after Increment 1:** prattail lib **4350/0**,
op-suite **no regression past the 217 baseline** (commit `28d4d26`), `rocq` (SemiringLaws)
green. For `tree_automaton.rs`/`egraph.rs`, dovetail-core grows its OWN clean modules (the
generic WTA is small; the runtime e-graph is payload-generic + exact-keyed, distinct from
prattail's compile-time `String`-keyed one) — prattail's copies stay put; convergence is an
independent convergence refactor (Increment 9), not a prerequisite for the
CESK runtime-backend replacement path.

## 2. Crate layout + public API

```
rigail/  src/{lib,traits,weights,closure}.rs   # extracted algebra + decoupled PackingFactored
dovetail/           src/lib.rs                             # crate root + feature gates (engine OFF default)
                    src/key.rs                             # ContentKey (exact byte key) + SemanticHash trait
                    src/egraph/{mod,union_find,congruence}.rs  # runtime payload-generic exact-keyed e-graph
                    src/wta/{mod,dfta}.rs                  # generic-W WTA wired to e-classes (DFTA view)
                    src/extract/{mod,nbest,closure}.rs     # N-best/set-valued demand-driven best-first enumeration (research-grade core)
                    src/rules/{mod,driver}.rs              # rules-as-data + saturation driver
                    src/space/{mod,inmem}.rs               # tuplespace-shaped trait (C,P,A,K)+Match seam
dovetail/formal/rocq/theories/{ExactKeys,Extraction,InsideWeights,Saturation,Requirements}/
```

**Exact-key linchpin (HARD constraint — NOT 64-bit hash, NOT String):**
```rust
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ContentKey(pub Box<[u8]>);          // owned exact bytes; Ord => total tiebreak
pub unsafe trait SemanticHash {
    fn write_content(&self, out: &mut Vec<u8>);  // exact buffer, not a 64-bit Hasher
    fn content_key(&self) -> ContentKey { /* write into Vec<u8> -> boxed slice */ }
}
```
`SemanticHash` is unsafe because implementors must preserve an injective exact-content
encoding that agrees with `Eq`/`Hash`; composite encodings must frame their parts.
**N-best extractor (HARD: ORDER not PRUNE; equal-weight distinct alts BOTH survive; refute only at `0̄`):**
`Extractor<L,W,F>` requires `W: MonotoneBestOrder`; `kth` returns
`Extraction<Option<Rc<Derivation<L,W>>>>`; `derivations(root)` returns a checked
`Derivations` stream with `next_checked() -> ExtractionStep<_>` and
`collect_checked() -> Extraction<Vec<Rc<Derivation<L,W>>>>`. It intentionally does not
implement plain `Iterator`, because completeness is terminal metadata. Output is ordered by
`(W, ContentKey)`; distinct `ContentKey`s never merge even at equal `W`; a candidate is
discarded only when its composed weight `is_zero()`. Cyclic enumeration boundedness is
explicit through `ExtractionCompleteness`.

Tuplespace trait `TupleSpace<C,P,A,K>` + `Match<P,A>` seam (in-mem default only; the future
Reified-RSpace mapping inner=PriorityQueue/outer=PathMap/seam=Match is a documented seam, no
reified-rspace dep). Engine `default = []`; added to workspace `members` but nothing in the
existing build path depends on it ⇒ mandatory dependency set unchanged.

## 3. Increments (each: adds / tested / gate = `cargo check --workspace` green + prattail 4350/0 + op-suite ≤217 + relevant `rocq-*` zero-admission)

1. **`rigail` extraction** (only prattail-touching step; land + verify ALONE). Move algebra + decoupled `PackingFactored`; prattail `semiring.rs`/`sppf.rs` → `pub use` facades. Gate: prattail 4350/0; op-suite ≤217; SemiringLaws green.
2. **crate skeleton + `key.rs`** (`ContentKey`, `SemanticHash`). Tests: key determinism; distinct byte-streams → distinct keys. *(safe, independent of #1)*
3. **runtime payload-generic exact-keyed e-graph** (`add`/`merge`/`rebuild` + carried `try_add_with_budget`/`rebuild_exact_indices`/`node_limit_reached` from b56e1e5). Tests: port prattail congruence/budget tests; a 64-bit-collision-but-distinct-`ContentKey` pair stays 2 classes (Rust refutation of `hash_only_pair_dedup_can_drop_distinct_keys`).
4. **generic-`W` WTA wired to e-classes** (`WtaTransition<W>`, `EGraphDfta`). Tests: tiny e-graph, assert transitions+weights.
5. **N-best/set-valued demand-driven best-first enumeration extractor (acyclic)** — Huang–Chiang lazy k-best over the hypergraph by composed weight; set semantics. Tests: two equal-weight distinct alts BOTH appear; zero-weight alt dropped; k-truncation = k smallest by `(W,key)`.
6. **cyclic e-class weight closure** — SCC → `PackingFactored` → `solve_scc_weights_newton`. Tests: self-referential class under idempotent semiring terminates.
   — **M-E.0 "inert" milestone = increments 1–6** (skeleton + WTA on runtime e-graph + N-best, engine gated off, no f1r3node binding, zero new mandatory deps).
7. **rules-as-data + reduction driver** (`Sexpr`/`Rule`/`Program` + `saturate`).
8. **tuplespace trait + in-mem impl.**
9. **convergence pass** (prattail `tree_automaton.rs` generic core → `pub use dovetail::wta::*`) — execute only as an independently proved no-regression refactor; it is not required for the CESK runtime-backend replacement path.

## 4. FV obligations (zero-Admitted/zero-Axiom; `rocq-dovetail` target in `formal/Makefile`)
1. **`ExactKeys/ExactKeyDedup.v`** — exact-key dedup preserves every key, distinct keys are never conflated, add-with-budget never overshoots, and overflow reports refusal. Certifies Increment 3.
2. **`Extraction/NBestExtraction.v` + `Extraction/EnumerationCompleteness.v` + `Extraction/LazyFrontierOrder.v` + `Extraction/OrderPreservingFraming.v` + `Extraction/ExtractionOutcome.v`** — k-best/set-valued extraction keeps every distinct non-`0̄` derivation, orders by `(W,key)`, is monotone under demand, enumerates the full hyperedge rank-vector product, proves lazy frontier sortedness/permutation preservation, proves ordered child-key framing, and proves checked terminal completeness cannot silently hide a cycle cut. Certifies Increment 5.
3. **`InsideWeights/InsideWeightSccClosure.v`** — SCC→`PackingFactored` lowering preserves the e-graph inside equations; scalar/self-loop closure is the least fixpoint; trivial SCC skipping is sound. The Rust cyclic path is restricted by sealed `CommutativeStarSemiring` and validates recursive tropical closed weights before Newton. Certifies Increment 6.
4. **`Saturation/DovetailSaturation.v`** — rules-as-data saturation is monotone and sound when generated facts are sound; bounded execution reports `Converged`, `NodeLimit`, or `IterationLimit` explicitly. Certifies Increment 7.
5. **`Requirements/MeTTaILRewriteCoverage.v`** — every current MeTTaIL rewrite requirement is covered by a Dovetail capability or an explicit native/Rho handler contract.

## 5. Honest scope
- **Quick wins:** Inc 1 (mechanical move; 1 coupling point), Inc 2 (key), Inc 4 (WTA view), Inc 8 (trait).
- **Moderate:** Inc 3 (payload-generic exact-keyed e-graph), Inc 7 (driver).
- **Research-grade boundary:** full cyclic k>=2 enumeration remains bounded-by-design and surfaced by `had_cycle_cut`; cyclic inside weights and acyclic/bounded extraction correctness are proven.
- **Out of scope here:** any f1r3node/RSpace binding; the Reified-RSpace concrete impl; per-language CESK runtime-backend flips to Rho default (M-RHO.4 / task #20); the prattail-egraph→dovetail convergence (Inc 9).

## 6. Critical files
Create: `rigail/src/{lib,traits,weights,closure}.rs`; `dovetail/src/{lib,key}.rs`,
`dovetail/src/egraph/*`, `dovetail/src/wta/*`, `dovetail/src/extract/*` (esp. `nbest.rs` — the
research core), `dovetail/src/{rules,space}/*`; `dovetail/formal/rocq/{_CoqProject,theories/*}`.
Modify (small): workspace `Cargo.toml` members; `prattail/Cargo.toml` dep; `prattail/src/automata/semiring.rs`
→ facade; `prattail/src/sppf.rs` re-export; `formal/Makefile` `rocq-dovetail` target.
