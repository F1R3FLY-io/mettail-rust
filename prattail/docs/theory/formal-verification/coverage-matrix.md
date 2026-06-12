# FV Coverage Matrix — mandate/invariant → Rocq → Rust → test → status

**Phase 1 of the Lazy-WPDA-Pipeline + FV-Cleanup plan.** A *living* matrix: every phase
updates it. It exists so we never (a) ship a Rust change without a non-vacuous proof, or
(b) believe a property is proven when its proof is vacuous. Pair with the baseline at
[`baseline-cf03e571.md`](baseline-cf03e571.md).

**Status legend:**
`proven` = non-vacuous Rocq, green under `make -C formal check-capped`, models the real code ·
`modeled-CE` = proven over a faithful model + a code-level counterexample/flip test ·
`regression-only` = guarded by a Rust test, no Rocq yet ·
`GAP` = claimed/assumed but unproven or unguarded ·
`claimed-unverified` = pgmcp `claimed_done` but `verified_at: null` ·
`VACUOUS` = a proof exists but does not constrain the code (must be rewritten).

---

## A. Plan invariants → evidence

| # | Invariant | Rocq theorem(s) | Rust site(s) | Test(s) | Status |
|---|-----------|-----------------|--------------|---------|--------|
| 1 | No dropped alternatives; dedup only by exact tagged key (never 64-bit hash) | `RuntimeModel.v::exact_key_pair_dedup_preserves_distinct_keys`; `hash_only_pair_dedup_can_drop_distinct_keys` (negative) | `language.rs::from_alternatives` (semantic_fingerprint dedup → `Ambiguous`) | `-3!` family; gen_*_op | **proven** (parser-assembly); **GAP** at eval NF-walk (still 64-bit `visited` → Phase 3a) |
| 2 | Ambiguity end-to-end until evidence rejection | `RuntimeModel.v::parser_preserves_ambiguous_alternatives`, `semantic_rejection_preserves_unrejected_siblings`; `EvidenceComplete.v` (closure meta-property) | `from_alternatives`, `substitute_env` (Ambiguous arms) | `-3!`, ambiguity_exposure_* | **proven** (parse) + **proven** closure meta-property (`EvidenceComplete.v`, `31bb90bc`: weights order never prune; removal only by evidence) |
| 3 | Zero `Admitted`/`Axiom`; every change ships a non-vacuous proof | corpus-wide gate | — | `make -C formal check-capped` | **proven** (gate holds; 3 files use stdlib `classic`, all outside touched targets) |
| 4 | Baseline-relative empirical gates | — | — | baseline-cf03e571.md | **proven** (baseline captured: 4350/0 lib + 217 known-red) |
| 5 | Commit at stable points; prove root (flip) before naming a fix | — | — | git history | process invariant |

## B. Mandate areas → evidence

| Area | Rocq | Rust | Status |
|------|------|------|--------|
| State-space bounding (e-graph budget) | `EGraphBudgetDedup.v` (no-overshoot, explicit overflow, dedup membership+NoDup) — **proven from scratch** | `egraph.rs::{try_add_with_budget,rebuild_exact_indices,apply_matches_bounded,SaturationResult::node_limit_reached}` | **proven** (compile-time only; NOT the eval-fixpoint bound — Phase 3 adds that) |
| Recognizer realization laziness | `RuntimeModel.v` (demand-bounded realize; arena-order) | `facade.rs::__mettail_wpda_collect_prefix`; `wpda_walker.rs` realizers | **GAP**: realizer truncates in **arena order, not weight order** → `realized_prefix_is_eager_firstn` would be vacuous until the Phase 2 demand-driven best-first enumeration fix |
| Evaluator demand-laziness | — | Ascent `prog.run()` eager fixpoint | **GAP**: Ascent has no demand knob → Phase 3 Tier A `DemandTransform.v` (or the Dovetail engine) |
| Eval NF dedup soundness | (cite invariant 1) | `runtime/src/language.rs` NF-walk `visited:HashSet<u64>`, `WeightedSeedId` | **GAP** (unsound 64-bit dedup) → Phase 3a re-keying + `reachability_dedup_exact_key_no_loss` |
| Cost / weight axis | reuse f1r3node-rust `CACostMonadInstances.v` ("R-C obstruction"), `JoinConservation.v`, `FuelGateSafety.v`, `UseCaseAdequacy.v` (55 thms) | (Dovetail adapter) | **proven upstream**; engine adds Δ1 min-cost-matching join (new) |
| Lexer laziness | — | `automata/codegen.rs::lex` (eager `Vec`), `runtime_types.rs::lex_dag_core` | **claimed-unverified** (pgmcp item 206 `verified_at: null`) → Phase 2L |

## C. Known GAPs / VACUOUS proofs (red-team-discovered — do not trust until rewritten)

| Item | Why | Resolution phase |
|------|-----|------------------|
| `BCG05_GuardKey.v` uses `normalize := identity` | **VACUOUS** — proves nothing about real congruence dedup | Phase 5B: new `BCG07_CongruenceSeedKey.v` over a real `normalize` |
| `WpdsSimulation.v` is parser-PDA-only | does NOT model eval | Phase 3: `LazyEvalEnum.v` (not "extend WpdsSimulation") |
| `RuntimeModel.v:1419-1493` static count-lemmas ("lazy ≡ eager") | structurally true but vacuous vs the realizer | Phase 2: genuine `LazyRecognizer.v` after the weight-order fix |
| Eval NF dedup on 64-bit `DefaultHasher::finish()` | unsound (collision drops distinct terms) | Phase 3a graph re-keying |
| Lexer item 206 `claimed_done` but `verified_at: null` | eager materialization, no laziness proof | Phase 2L |
| `from_alternatives` weight-drop "violation" (plan premise) | **already fixed** (Phase F.13 Stage 2.3.1: semantic_fingerprint dedup → Ambiguous) | Phase EC: VERIFY no remaining weight-drop site; add `EvidenceComplete.v` + lint guard |

## D. Per-phase NEW Rocq obligations (created as each phase lands)

| Phase | New `.v` | Key theorems | Status |
|-------|----------|--------------|--------|
| EC | `EvidenceComplete.v` (prattail_wpda_runtime, zero-admission, `31bb90bc`) | **proven**: `no_valid_alternative_dropped`, `evidence_only_removal` (removal = observational-equiv merge), `weight_is_order_only` (kept key-set invariant under reweighting), `assemble_keys_nodup` (residual ambiguity surfaced), `weight_drop_can_lose_valid_alternative` (negative fence). `from_alternatives` (language.rs:722) verified already evidence-complete (semantic_fingerprint-only dedup; weight-free). The FV fence subsumes the planned lint guard (no SGLR prefer/avoid in MeTTaIL) |
| 4A | `CD07_NfaFallbackNonLoss.v` | fanout_complete; fanout_sound; lexmin_orders_not_prunes | **proven** (zero-admission, committed `81ad0aa8`) + shipped_drops_boundary, selection_is_member, shipped_spillover_loss (negative fence), nfa_fallback_nonlossy, fixed_empty_boundary_not_present. Both latent-loss sites fixed; dispatch_strategy consumers re-scoped (dead-rule lint + NFA-spillover refinement only — the plan's "Walker Fork" premise was stale) |
| 5A | (extend `RuntimeModel.v`) | cast_edge_source_roundtrip; eoi_ordering_is_permutation | TODO |
| 5C | (extend `RuntimeModel.v`) | budget_overflow_is_surfaced; under_budget_preserves_all; lazy_member_counted_once | TODO |
| 5B | `BCG07_CongruenceSeedKey.v` | congruence_seed_key_disjoint; congruence_propagation_complete | TODO |
| 2 | `LazyRecognizer.v` | realized_prefix_is_eager_firstn (post weight-order fix); realization_prefix_stable; budget_overflow_reported_not_pruned | TODO |
| 3a | (extend `RuntimeModel.v`) | reachability_dedup_exact_key_no_loss | TODO |
| 3 | `LazyEvalEnum.v` + `DemandTransform.v` | demand_eval_equals_eager_in_the_limit; demand_only_computes_reachable; enum_take_k_is_eager_quotient_prefix; fixpoint_bound_reported_not_pruned | TODO |
| 4B | `CD06_SuffixFactor.v` | factor_eq_matching_rule; factor_sound/complete; factor_language_eq | **proven** (zero-admission, all 8 theorems `Closed under the global context`): central `factor_eq_matching_rule` is exact match-LIST equality (labels + grammar order + multiplicity, NO disjointness precondition) ⇒ `factor_sound`/`factor_complete`/`factor_language_eq` + `factor_preserves_ambiguity_degree` are corollaries; T5 `degraded_path_preserved`/`residual_subset` (ineligible alternatives untouched); `factored_aux_counts_eligible` ties the model to the M1.0 measurement. **VERDICT: CD06 STOPPED at diagnostic-only** — measured depth2 ratios (calculator 0.19, rhocalc 0.42, Ambient 0.57, GuardedRho 0) EXCEED the 0.10 screen, but every depth-2 bucket is already leading-literal-disjoint under CD02 top-down dispatch ⇒ a shared tail is parsed once either way ⇒ factoring saves code size only, ZERO parse work ⇒ transform NOT wired (no suffix_trie.rs, no `Optimization::SuffixFactoring`); the I17 `cd06-shared-suffix-measure` diagnostic is retained |

## E. Engine (Dovetail) obligations — `dovetail/formal/rocq/`

**dovetail RUST core SHIPPED + capped-test verified** — Increments 1 (rigail
extraction), 2 (key), 3 (e-graph), 4 (WTA view), 5 (exact no-miss extractor), 6 (Newton-SCC
cyclic closure), 7 (rules-as-data saturation), 8 (tuplespace seam). **Engine FV now COMPLETE
(zero-admission): the extractor MISSES NOTHING across the candidate SET, the ORDER, the
RECURSION, and the cyclic WEIGHT, with cycle-cut boundedness explicit in the Rust API.**
Dovetail also has a formal MeTTaIL rewrite-requirements coverage taxonomy: every current
`LanguageDef` rewrite/equation/fold/guard/pattern class is classified as covered by a
Dovetail core capability or by an explicit external/native/Rho handler contract. Native/Rho
contracts are not core-proven Dovetail behavior; their operational-correspondence obligations
remain in M-RHO.*, below.

| Obligation | Source | Status |
|------------|--------|--------|
| Exact runtime e-graph dedup no-loss (Inc 3) | `ExactKeys/ExactKeyDedup.v` (rocq-dovetail, zero-admission) + invariant 1 | **proven**: exact-key dedup preserves every key, distinct keys are not conflated, add-with-budget never overshoots, overflow preserves state and reports refusal |
| Rules-as-data saturation (Inc 7) | `Saturation/DovetailSaturation.v` (rocq-dovetail, zero-admission) | **proven**: saturation steps are monotone; iterated saturation is monotone; generated-fact soundness preserves state soundness; bounded execution reports `Converged`, `NodeLimit`, or `IterationLimit` explicitly |
| WTA no-miss extraction — SELECTION layer (Inc 5) | `Extraction/NBestExtraction.v` (rocq-dovetail, zero-admission, committed `98a2d0d`) | **proven**: only-`0̄`-removal, no-miss (`select_complete`), equal-weight-both-survive, resumability (`select_prefix_monotone`), exhaustive-on-demand |
| WTA extraction — best-first ORDERING (Inc 5) | `Extraction/NBestExtraction.v` (`select_ordered_sorted`/`_perm`/`_complete`, zero-admission, committed `2ff227b9`) | **proven**: output sorted best-first; a permutation of the kept candidates (ordering reorders, never drops); every non-`0̄` alternative present |
| WTA extraction — lazy frontier ORDERING (Inc 5) | `Extraction/LazyFrontierOrder.v` (rocq-dovetail, zero-admission) | **proven**: heap-popped traces are sorted under the monotone-best-order successor condition; emitted elements plus final frontier are a permutation of the initial frontier plus generated successors; bumping one child rank cannot produce a strictly better candidate |
| WTA extraction — hypergraph-recursion COMPLETENESS (Inc 5) | `Extraction/EnumerationCompleteness.v` (rocq-dovetail, zero-admission, committed `4d482514`) | **proven**: `class_enum_complete` (EVERY hyperedge + EVERY valid rank-vector enumerated — NO derivation dropped), `enum_vectors_complete`/`_sound`, `class_enum_sound`; the per-edge cartesian product unioned over edges = Huang-Chiang Alg.3 candidate set. 9 Rust tests T1-T9 are the operational cross-check |
| WTA extraction — ordered child-key framing (Inc 5) | `Extraction/OrderPreservingFraming.v` (rocq-dovetail, zero-admission) | **proven**: ordered framing is prefix-free, injective, and preserves lexicographic child-key order; distinct derivation keys cannot be conflated by the child-key encoding |
| Cyclic inside-weight closure (Inc 6) | `InsideWeights/InsideWeightSccClosure.v` (rocq-dovetail, zero-admission) | **proven**: `lowering_factor_faithful`/`lowered_eq_recurrence`/`lowering_preserves_fixpoints` (the SCC->PackingFactored re-indexing is faithful + fixpoint-preserving), `star_closure_is_lfp` (scalar/self-loop closure = exact LEAST fixpoint = aggregate over all cycle-unfolded derivations), `trivial_scc_constant` (trivial-SCC `continue` sound), `bool_cka` (non-vacuity). n-D multi-call Newton CONVERGENCE cited (Esparza-Kiefer-Luttenberger 2007, implemented in rigail). Commutativity precondition is enforced by sealed `CommutativeStarSemiring`; currently only `TropicalWeight` implements the cyclic closed path |
| Cyclic e-class k>=2 enumeration closure (Inc 6) | `Extraction/CycleCutBoundary.v`, `Extraction/ExtractionOutcome.v`, extractor `on_stack` cycle guard, checked `Derivations::next_checked()`, `had_cycle_cut()` | **proven bounded-by-design** (NOT a silent miss): exact cyclic INSIDE weight via Newton (1-best/admissible-heuristic exact, proven above); k>=2 lazy enumeration over cyclic SCCs is CUT and SURFACED by `BoundedByCycleCut`/`had_cycle_cut()`. Full k>=2 cyclic unfolding remains research-grade |
| MeTTaIL rewrite-requirement coverage | `Requirements/MeTTaILRewriteCoverage.v` + `ast/tests/dovetail_rewrite_coverage.rs` | **proven + audited taxonomy**: equations, directional rewrites, congruence, folds/native handlers, freshness/env/relation/forall/behavioral/synthetic guards, collection/map/zip/binder/substitution patterns, exact keys, budget reports, demand/ambiguity, cyclic weights/boundaries, and Rho contracts are classified. Dovetail-core capabilities are covered here; external/native/Rho handler contracts remain separate implementation obligations |
| Rust-facing refinement bridge | `Refinement/RustModelBridge.v` | **proven**: Rust-shaped candidates, budget results, rank vectors, ordered framing, lazy frontier ordering, checked extraction outcomes, and cycle reports preserve the existing Rocq extraction/budget/cycle capstones |
| Actual `LanguageDef` inventory | `Requirements/LanguageDefInventory.v` + `ast/tests/dovetail_language_inventory.rs` | **proven + audited**: current in-repo `language!` macro bodies are parsed and classified; inventoried requirements are covered with no silent delegation |
| Pattern/premise lowering coverage | `Lowering/PatternLoweringSoundness.v` | **proven**: recursive pattern and premise lowering requirements map to covered Dovetail requirement constructors |
| Newton-SCC solver boundary | `Rigail/NewtonSccAdequacy.v` | **proven boundary**: scalar/self-loop closure is mechanized; n-D Newton adequacy is represented as an explicit proof-carrying solver contract, never as a global axiom |
| Pure arithmetic SMT + Rust Creusot pilot | `dovetail/formal/why3/key_budget_pilot.mlw` via `why3-dovetail-pilot`; `dovetail/formal/creusot` via `creusot-dovetail-pilot` | **proven pilot**: Why3 proves budget arithmetic directly; Creusot verifies the Rust-level `try_add_with_budget` contract plus no-overshoot, overflow-preserves-state, and add-below-limit wrappers |
| spec→Rholang-VM operational correspondence (up-to-weak-bisim) | new, schematic-over-codegen; reuse `CATranslation`/`Bisimulation`/`CASimulationBicat` | TODO (M-RHO.1) |
| Bridge one-way dependency (M-RHO.0.0) | `BridgeInertness.v` (rocq-rho-bridge, zero-admission, `9c9300ec`) | **proven**: `f1r3node_never_depends_on_mettail`, `f1r3node_does_not_reach_mettail`, `bridge_acyclic` — the invariant the host guard `mettail_rust_is_not_a_cargo_dependency` enforces |
| OslfResourceLogic conformance (4 laws) — M-RHO.0.2 | `MettaOslfLawsConformance.v` + `MettaGsltPresentation.v` (rocq-rho-bridge, zero-admission, `03082acc`) | **proven**: 4 OSLF laws over the modelled `is_funded` (= `delta_sigma`'s `Δ+margin≤Σ`) + lane-decomposition sound/complete; 2nd instance reusing `GSLTOSLFCapstone.v`/`LinearLogicResources.v`. Rust `MettaResourceLogic` delegates to verified `delta_sigma`; 3/3 adapter tests green |
| spec→Rholang lowering total-or-reject (M-RHO.0.3) | `RhoLoweringTotalOrRejects.v` (rocq-rho-bridge, zero-admission, `9478e791`) | **proven**: `lowering_total`/`_sound`/`_disjoint`/`_count` + lowered/rejected characterized by `supported` — every `LanguageDef` rule is lowered OR explicitly rejected, never silently dropped. `mettail-rho-codegen` 3/3 incl. rholang `Compiler::source_to_adt` parse round-trip |
| Differential oracle rho ≡ Ascent (M-RHO.0.4/.0.5) | `OracleQuotientEquivalence.v` (rocq-rho-bridge, zero-admission, `168859e3`) | **proven + run on BOTH backends**: the oracle (weight-erase ∘ eqrel-quotient) is a sound exact equivalence; the lowered calculator runs on a real in-memory `RhoRuntime` (`bfe56c4b`) and its result equals `CalculatorLanguage::run_ascent` normal forms (`7629c828`, 5/5 Int ops: 2+3/10−4/3×7/20÷4/17%5) |
| Ambiguity-set preservation | new (least mature); differential non-confluent parity + `WeakBarbedEquiv` backstop | TODO (M-RHO.1/.3) |
| Δ1 N-ary min-cost-matching join | new cost-math over `CAJoinConservation` | TODO (M-RHO.3) |
| Predicated-types guarded-COMM soundness | new `GuardedCommSoundness.v` + `MsoAutomataEquivalence.v` (recognition) | TODO (M-RHO.3) |

---

*Update protocol: when a phase lands, flip its row(s) to `proven`/`modeled-CE`, link the
commit, and (if it removed baseline failures) update `baseline-cf03e571.md`.*
