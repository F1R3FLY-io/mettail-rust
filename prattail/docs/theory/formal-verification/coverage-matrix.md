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
| 2 | Ambiguity end-to-end until evidence rejection | `RuntimeModel.v::parser_preserves_ambiguous_alternatives`, `semantic_rejection_preserves_unrejected_siblings` | `from_alternatives`, `substitute_env` (Ambiguous arms) | `-3!`, ambiguity_exposure_* | **proven** (parse); Phase EC lifts to a closure meta-property `EvidenceComplete.v` (TODO) |
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
| EC | `EvidenceComplete.v` | evidence_only_removal; weight_is_order_only (Permutation); residual_ambiguity_surfaced; evidence_complete_no_valid_alternative_dropped; weight_drop_can_lose_valid_alternative (fence) | TODO |
| 4A | `CD07_NfaFallbackNonLoss.v` | fanout_complete; fanout_sound; lexmin_orders_not_prunes | TODO |
| 5A | (extend `RuntimeModel.v`) | cast_edge_source_roundtrip; eoi_ordering_is_permutation | TODO |
| 5C | (extend `RuntimeModel.v`) | budget_overflow_is_surfaced; under_budget_preserves_all; lazy_member_counted_once | TODO |
| 5B | `BCG07_CongruenceSeedKey.v` | congruence_seed_key_disjoint; congruence_propagation_complete | TODO |
| 2 | `LazyRecognizer.v` | realized_prefix_is_eager_firstn (post weight-order fix); realization_prefix_stable; budget_overflow_reported_not_pruned | TODO |
| 3a | (extend `RuntimeModel.v`) | reachability_dedup_exact_key_no_loss | TODO |
| 3 | `LazyEvalEnum.v` + `DemandTransform.v` | demand_eval_equals_eager_in_the_limit; demand_only_computes_reachable; enum_take_k_is_eager_quotient_prefix; fixpoint_bound_reported_not_pruned | TODO |
| 4B | `CD06_SuffixFactor.v` | factor_eq_matching_rule; factor_sound/complete; factor_language_eq | TODO (measure-first; may stay diagnostic-only) |

## E. Engine (Dovetail) obligations — `formal/rocq/dovetail/` (new) + reuse

**dovetail RUST core SHIPPED + test-verified (39/39), committed** — Increments 1 (rigail
extraction), 2 (key), 3 (e-graph), 4 (WTA view), 5 (exact no-miss extractor), 6 (Newton-SCC
cyclic closure), 7 (rules-as-data saturation), 8 (tuplespace seam). **Engine FV now COMPLETE
(zero-admission): the extractor MISSES NOTHING across the candidate SET, the ORDER, the
RECURSION, and the cyclic WEIGHT.** Remaining engine FV obligations are M-RHO.* (op-correspondence
etc.), below.

| Obligation | Source | Status |
|------------|--------|--------|
| Exact runtime e-graph dedup no-loss (Inc 3) | **COVERED** by `EGraphBudgetDedup.v` (the dovetail e-graph is a faithful port of the same algorithm) + invariant 1 | **proven** (reuse; traceability: `dovetail/src/key.rs` `ContentKey` exact byte-key + `dovetail/src/egraph.rs` add/merge/rebuild/budget ↔ `formal/rocq/egraph/theories/EGraphBudgetDedup.v` no-overshoot/overflow/dedup-NoDup) |
| WTA no-miss extraction — SELECTION layer (Inc 5) | `NBestExtraction.v` (rocq-dovetail, zero-admission, committed `98a2d0d`) | **proven**: only-`0̄`-removal, no-miss (`select_complete`), equal-weight-both-survive, resumability (`select_prefix_monotone`), exhaustive-on-demand |
| WTA extraction — best-first ORDERING (Inc 5) | `NBestExtraction.v` (`select_ordered_sorted`/`_perm`/`_complete`, zero-admission, committed `2ff227b9`) | **proven**: output sorted best-first; a permutation of the kept candidates (ordering reorders, never drops); every non-`0̄` alternative present |
| WTA extraction — hypergraph-recursion COMPLETENESS (Inc 5) | `EnumerationCompleteness.v` (rocq-dovetail, zero-admission, committed `4d482514`) | **proven**: `class_enum_complete` (EVERY hyperedge + EVERY valid rank-vector enumerated — NO derivation dropped), `enum_vectors_complete`/`_sound`, `class_enum_sound`; the per-edge cartesian product unioned over edges = Huang–Chiang Alg.3 candidate set. 9 Rust tests T1–T9 are the operational cross-check |
| Cyclic inside-weight closure (Inc 6) | `InsideWeightSccClosure.v` (rocq-dovetail, zero-admission) | **proven**: `lowering_factor_faithful`/`lowered_eq_recurrence`/`lowering_preserves_fixpoints` (the SCC→PackingFactored re-indexing is faithful + fixpoint-preserving), `star_closure_is_lfp` (scalar/self-loop closure = exact LEAST fixpoint = ⊕-aggregate over all cycle-unfolded derivations), `trivial_scc_constant` (trivial-SCC `continue` sound), `bool_cka` (non-vacuity). n-D multi-call Newton CONVERGENCE cited (Esparza–Kiefer–Luttenberger 2007, implemented in rigail). Commutativity precondition = the inside-weight cost semirings (Tropical/Viterbi/prob). 3 wta cyclic tests cross-check |
| Cyclic e-class k≥2 enumeration closure (Inc 6) | extractor `on_stack` cycle guard; `had_cycle_cut()` | **bounded-by-design** (NOT a silent miss): exact cyclic INSIDE weight via Newton (1-best/admissible-heuristic exact, proven above); k≥2 lazy enumeration over cyclic SCCs is CUT and SURFACED by `had_cycle_cut()`. Full k≥2 cyclic unfolding = research-grade (pgmcp `fv-cyclic-eclass-k2-enumeration-closure`) |
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
