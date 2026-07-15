# M-RHO.1 — rhocalc NATIVE FAST PATH (Comm→RSpace COMM; non-confluent witness enumeration)

**Staged, verifiable execution contract** — M/D/I/L discipline (the P-series cadence). Branch `feature/wfst-architecture` @ `d8a09323`. Work item `m-rho-1-rhocalc-native-fast-path` (#281, parent #278, in_progress, prio 7). Opens the Dovetail/Rho flip epic now that the P-series ladder is closed.

> **Status: v4 — implemented evidence attached.** Round 1: 2 independent critics, both NOT-CONVERGED on v1 (9 BLOCKERs + 7 MAJORs) → the v2 §0-REVISION decisions D1–D8. Round 2: host critic NOT-CONVERGED on v2 (1 BLOCKER + 3 MAJORs — all resolved below, §0-REVISION v3); the FV critic was lost to a usage limit and its load-bearing checks were performed inline by the caller (renderer/binder feasibility, Ascent API, corpus completeness, Rocq pattern — all verified, with corpus EXPANSION). Findings + resolution maps: `02-red-team-ledger.md`. The implemented proof/runtime evidence is recorded in `formal/rocq/rho_bridge/`, `rholang-runtime/tests/rho_comm_oracle.rs`, and `docs/architecture/rho-native-integration/07-verification-and-rollout.md`.

---

## ★ §0-AMENDMENT (2026-06-12, ground-truth correction — supersedes v1's §0 "load-bearing finding" and risk R1)

The original plan was drafted from session data at `a95c5106` (rhocalc_tests 111/15). **Verified at HEAD `d8a09323` (fresh run): `rhocalc_tests` is 126 passed / 0 failed.** ROOT-A (`9fdaed68`), ROOT-F (`38dcd485`), and the eval-layer closure (`f1ea267c`) all landed between the plan's source data and now.

**Consequences:** risk R1 DISSOLVES — no comm family is parser-blocked; no `#[ignore]` fencing. The residual parser-side items are #313 (ghost packings — does not block the comm corpus) and #312 (trace Heisenbug — constrains the verification METHOD, risk R2 stands). Battery reds for baseline accounting: `gen_rhocalc_op` 530/1 (`castbigrat`, pre-existing); `languages/tests/calculator.rs` has timing-sensitive Welch-panel tests that flake under load (not functional).

## ★ §0-REVISION v2 (2026-06-12, post red-team round 1) — the eight forced decisions

Round 1 (host-grounding critic + mettail/FV critic, independent) refuted v1's §2/§3/§4-item-5/§5 mechanisms. Every decision below is derived from the critics' file:line evidence (deep-dive discipline — no implement-and-observe):

- **D1 — SUPERSEDED for generated backends by §0-REVISION v4.** The original conservative bring-up decision was execution through source text (`evaluate_with_term`), not direct-`Par` `inj`. It was forced by then-unhandled risks: `inj` returned no `EvaluateResult` and ran against an `empty_cost()` budget (`rho_runtime.rs:140-145,1268`; the `bootstrap_registry` manual-cost path `:1244-1252` was the only precedent), and hand-assembled Pars had to reproduce normalizer invariants — `connective_used=false` on a pattern silently degrades matching to syntactic equality and the COMM **never fires** (`spatial_matcher.rs:178-181`), FreeVar levels are bind-local `0..free_count-1` with dispatcher-order flattening and `(level+shift)-k-1` resolution (`match.rs:22-60`, `dispatch.rs:14-19`, `env.rs:33-47`, `reduce.rs:1090-1094`), binds are pre-sorted at normalization only (`p_input_normalizer.rs:394-395`). Those risks are now handled by direct budget installation and generated-AST shape tests; source text is no longer the generated backend boundary.
- **D2 — Free-variable grounding σ** (no free-var convention existed; both paths hard-error: `TopLevelFreeVariablesNotAllowedError` `compiler.rs:106-118`; `eval_var` FreeVar error `reduce.rs:1120-1141`; `evaluate`'s `normalizer_env` is dead in the Rust port — threaded as `_env`, zero consumers under `compiler/normalizer/`). Convention: free **Name** var `c` ⇒ ground channel `@"mtl:c"`; free **Proc** var `p` ⇒ **observation-sentinel send** `@"mtl#out"!("mtl:p")`. The sentinel channel `@"mtl#out"` is **format-disjoint** from the var-grounding image `"mtl:<name>"` (`#` vs `:`), so a free name var literally named `out` cannot collide with it. Applied uniformly at render time to BOTH the source term and the Ascent normal forms before comparison. σ is sound for transport testing: free vars are inert in rhocalc reduction (no rule fires on a bare `Var`), so reduction commutes with σ on the corpus (Rocq lemma `grounding_commutes`, §4); sentinel sends fire only on the disjoint sentinel channel, never perturbing object-channel rendezvous.
- **D3 — Observation = canonicalized RESTING-SPACE fingerprint, gate = membership.** "Read the resting datum from the keyed channel" observed NOTHING for most members (bare-process NFs rest on no channel; the reducer filters process-position exprs to `EVarBody`/`EMethodBody`, `reduce.rs:198-206`). Protocol: evaluate `⟦t⟧σ` AND each `⟦nf_i⟧σ` on fresh in-memory runtimes; observe via the **soft-checkpoint hot-store dump** (`create_soft_checkpoint`, `rho_runtime.rs:152-166`) serialized to a canonical fingerprint; assert `EvaluateResult.errors` empty on every run. **Fingerprint = space CONTENT only**: sorted (channel-`Par`, multiset of data-`Par`s) + (channel-group, multiset of (patterns, body, persist)) entries, ν-quotienting `GPrivate` ids per D5 and **projecting OUT scheduler/provenance metadata** — `ParWithRandom`'s random-state component, produce/consume event refs, sequence numbers — which differ between the `⟦t⟧σ` and `⟦nf_i⟧σ` runs by construction (the two reductions split the Blake2b512Random differently) and are not part of the observable state. **Gate (.1.0): the `⟦t⟧σ` fingerprint equals SOME `⟦nf_i⟧σ` fingerprint** (membership; equality on deterministic members where the NF set is singleton). The proc-var sentinel sends (D2) make variable-valued NFs datum-shaped and discriminating; for ground-inert NFs (e.g. `0`) the discriminator is quiescence itself — an unfired COMM leaves the parked `Receive` (and unconsumed datum) in the dump, so empty-space ⇒ the rendezvous fired.
- **D4 — Ascent side = `normal_forms_reachable_from_seeds([initial])`** (`runtime/src/language.rs:724-735`), NOT raw `normal_forms()` (subterm-polluted: `multi_input_uses_both_vars` has `p`-the-subterm in the raw NF set — set comparisons against it can never be green).
- **D5 — Name identity = ≡_N-canonical RENDERING; ContentKey is the SPEC, never the payload.** v1's "key channels by ContentKey bytes" is unimplementable: RSpace keys channels by the channel `Par` value (`rspace.rs:338-339,373`), `Exec`/`PDrop` requires the body recoverable from the name (opaque key bytes have no rhoapi decoder), and a received datum used as a channel (`comm_with_body_using_channel`) must collide with statically-rendered occurrences of the same name. Realization: a **≡_N canonicalizer** over Name/Proc (exhaustive `QuoteDrop` `@(*(n))→n` / `ExecEq` `*(@(P))→P` cancellation; terminating — each step strictly shrinks the term) applied before rendering, so name-equivalent channels emit byte-identical source ⇒ identical normalized `Par`s ⇒ one RSpace channel. The P4 lesson (R4) is honored as: name identity is **total canonical content** (the host's `ParSortMatcher` sort is content-total) — never insertion order, never a 64-bit hash, never Display-of-uncanonicalized. ν-names (`PNew`): fingerprints quotient `GPrivate` ids by first-occurrence order in the canonical dump (run-to-run and t-vs-nf byte alignment of unforgeables is NOT guaranteed and must not be assumed).
- **D6 — Corpus partition: .1.0 = the TRANSPORT-PURE members only.** The fold-dependent members (`cast_under_send` — needs `IntBinProc` post-transport; `native_ops::bag::remove_comm` — needs `fold_proc`+`RemoveBag`; `native_ops::bag::count_comm` — needs `CountBag`, which moreover lands in category Int) are structurally red under .1's own no-fold scope and have no rhoapi image even as payloads. They are EXCLUDED from the .1.0 oracle with recorded reason (they remain green Ascent tests; they become the M-RHO.2 acceptance bridge). Exact .1.0 corpus in §3.
- **D7 — Witness mechanism inverted-then-fixed: accumulation on a RECEIVE-LESS channel + harness-side sequential enumeration, scoped to EAGER-FIRE races.** v1's "persistent receive on `@witnesses`, drained via `get_data`/`get_joins`" is mechanically backwards: a persistent receive CONSUMES arriving data (nothing rests); `get_joins` returns installed join channel-groups, not data (`rho_runtime.rs:200-202,395-401`); and the `normalize.rs` citation was the wrong layer (persistent receives: `p_input_normalizer.rs:275-281,501`; runtime `reduce.rs:1102`). The host idiom for append-only witness collection is **bare sends to a channel with NO receive** (exactly D2's sentinel sends). Set-coverage: the host's COMM candidate selection is deliberately deterministic (`shuffle_with_index` sorts by `deterministic_candidate_hash` — "A random shuffle can make equally valid matches diverge across validators", `rspace.rs:1211-1233`), so re-running does NOT explore outcomes. The .1.1 harness therefore **enumerates send-arrival orders deterministically**: install the receive part, then evaluate the k producer sends one at a time per permutation π ∈ S_k, collecting the outcome fingerprint per π. **Scope of coverage (derived, honest):** arrival-order enumeration explores exactly the races where a rendezvous fires EAGERLY between arrivals — a 1-bind receive with k contending sends commits to the sole resting datum at each step (π=[a,b] ⇒ x=a; π=[b,a] ⇒ x=b), so the outcome set is covered. A **multi-bind same-channel join** is not covered by the .1 source-text oracle: the host source normalizer rejects duplicate receive channels, while direct RSpace consume can represent the lower-level case. General ambiguity is handled at M-RHO.3 by explicit exact-key witness facts (`AmbiguityCandidate` / `AmbiguityWitnessSet`) and the Rocq `AmbiguityWitnessEnumeration.v` + `AmbiguitySetPreservation.v` proofs. Gate (.1.1): on eager-fire race inputs, the enumerated outcome SET ≡ the Ascent reachable-NF set (both sides keyed by D3 fingerprints); on join inputs, membership. The eager-fire coverage claim is a finite Rocq lemma (§4); no claim is made that the .1 source-text oracle covers every duplicate-channel source shape.
- **D8 — Rocq fences carry NO `Conjecture`** (`Conjecture` ≡ `Parameter` ≡ `Axiom` in Rocq — it would fail the zero-Axiom gate the same section imposes). Fences become **statement-only `Definition …_statement : Prop := …`** (defined, never asserted) + comments citing the upstream `CAForceSeparation.v` proof. Cross-repo reuse is **by faithful re-statement** — `rho_bridge/_CoqProject` maps only `-Q theories RhoBridge`; no path to `f1r3node-rust/formal/rocq/cost_accounted_rho` exists, per the bridge's own precedent (`MettaFundingLawsConformance.v:24`).

## ★ §0-REVISION v3 (2026-06-12, post red-team round 2) — corrections to v2's own mechanisms

Round 2 (fresh host-grounding critic; the FV critic died at a usage limit and its checks were performed inline by the caller — see the ledger):

- **D7-CORRECTION — the "hash-pinned join assignment" claim was FALSE on the host; the negative lemma is KILLED.** The produce path **prepends the ARRIVING datum at the front of the candidate list (index −1) AFTER the hash sort** (`rspace.rs:818-825` `shuffled_data.insert(0, (data, -1))`), and `find_matching_data_candidate` scans in order (`space_matcher.rs:31-66`) — so the first bind takes the LAST-ARRIVED datum and arrival order DOES explore join assignments. Moreover `deterministic_candidate_hash` serializes the WHOLE `Datum` including `ListParWithRandom.random_state` and `source: Produce` (`rspace.rs:139-145`, `internal.rs:16-20`), while every `evaluate_with_*` draws its rand from `thread_rng()` (`rho_runtime.rs:111`; `blake2b512_random.rs:89-93`) — so for ≥2 RESTING candidates the selection is **not even run-deterministic in the harness context** (the `rspace.rs:1221-1224` determinism comment is about validator replay, where rand is deploy-derived). Consequences: (i) the planned `join_assignment_not_arrival_explorable` lemma would have modeled the wrong machine — REMOVED (the round-1 "vacuous-as-implementation-bounds" disease, caught at design time); (ii) the .1 corpus and the .1.1 enumeration rely ONLY on single-candidate-per-step structure — each arrival step has exactly one candidate, which is entropy-independent (critic-verified); (iii) the harness must NEVER rely on resting-candidate selection order; (iv) same-channel multi-bind joins are moot under D1 anyway — the host normalizer rejects them in source (`ReceiveOnSameChannelsError`, `p_input_normalizer.rs:408-423`, an intentional tested rejection class; the round-1 "consume supports duplicate channels" pass was true only at the RSpace API layer below the compiler). Member #8 is source-text EXCLUDED with a parser-boundary regression.
- **D3-PIN — the fingerprint is pinned to the dump's real shape** (the v2 formula would false-RED on nearly every member): fingerprint = the **user `data` + user `continuations` maps ONLY**; **DROP-EMPTY rows** (the hot store is a read-through cache — any lookup miss inserts an empty-history row, `hot_store.rs:358-382,221-231`, and removals leave `[]`-valued entries behind, `:430,:334` — so the t-run dumps `data["@mtl:c"] = []` where the nf-run has no such key); `installed_continuations`/`joins`/`installed_joins` EXCLUDED (`create_rho_env` unconditionally installs std/crypto system processes at fixed single-byte `GPrivate` channels with `TaggedContinuation::ScalaBodyRef` continuations — `rho_runtime.rs:1207,999-1004`, `system_processes.rs:81-139` — deterministic constants, and `ScalaBodyRef` has no `(patterns, body)` reading); continuation tuple = `(patterns, body, persist)` with the host-extension `condition` asserted-`None`; `source` dropped WHOLESALE (the Rust `Produce`/`Consume` carry no seq numbers — `trace/event.rs:97-108` — v2's "sequence numbers" described Scala-shaped fields).
- **Sentinel propagation** — the `@"mtl#out"` rename now applies in §1a′/§2/§3 (v2 left the refuted `@"mtl#out"` in the operational sections an implementer actually reads).
- **Checkpoint mechanics** — `create_soft_checkpoint` is NOT a pure observer: it DRAINS the event log + produce counter via `mem::take` (`rspace.rs:283-294`; harmless to the fingerprint, which reads `cache_snapshot` only). `revert_to_soft_checkpoint` consumes the checkpoint by value — the .1.1 π-loop must `clone()` the post-receive checkpoint before each revert (`SoftCheckpoint` is `Clone`, `checkpoint.rs:10-15`). Revert fully rebuilds the hot store; with `init_registry:false` nothing commits to history, so the loop is sound (`rspace.rs:302-320,1291-1294`).
- **ν-quotient RESTRICTION** — "first-occurrence order in the canonical dump" is circular for ≥2 `GPrivate`s (sorting the dump requires comparing channel `Par`s whose only difference may be the `GPrivate` ids being quotiented — graph canonicalization, not a linear scan). The .1 corpus is restricted to **single-ν members** (every ν member allocates exactly one observable `GPrivate`); a multi-ν member requires an iso-search quotient, recorded as out-of-.1.
- **R10 hardening** — on ANY evaluate error the host REVERTS the space (`rho_runtime.rs:117-120`), so an erroring t-run's dump equals the pre-eval state, which for inert-NF members fingerprint-matches the nf-image's empty dump. The `errors = ∅` assertion is therefore load-bearing against false-GREEN and may never be weakened to warn-only.
- **CORPUS EXPANSION (inline FV-lens verification, replacing the dead critic's sweep):** the v2 partition MISSED transport-pure eval families — Exec (`exec::exec_basic` `{*(@(0))}`→`0`; `exec::exec_with_process` `{*(@(a!(0)))}`→`a!(0)`, datum-shaped), congruence (`congruence::par_cong_exec` `{*(@(0)) | q}`→`{0 | q}`; `congruence::new_cong`), COMM under ν (`new_and_extrusion::new_congruence_reaches_normal_form`), scope extrusion (`new_and_extrusion::extrusion_reaches_result` — operationally native on the host: the receive registers at the free channel from inside the ν-scope, no Extrude step needed), blocked extrusion (`new_and_extrusion::extrusion_blocked_when_not_fresh` — the host's `new`-bound name SHADOWS the free channel natively; stuck on both sides; exercises ν-shadowing + parked-receive discrimination), and the ν-NF smoke (`new_and_extrusion::new_is_normal_when_body_is`). Fold-dependent exclusions GROW by `congruence::add_cong` (`{*(@(1)) + 2}`→`3`) and `congruence::comparison_cong` (`{*(@(1)) == 1}`→`true`). Renderer feasibility VERIFIED: HOL binders generate `Scope<Vec<Binder<String>>, Arc<Proc>>` (`macros/src/gen/types/enums.rs:371-375`) — the generated `Display` already walks this structure to print `(c?x).{*(x)}`, so the harness renderer has established machinery. `normal_forms_reachable_from_seeds(&[u64])` confirmed (`runtime/src/language.rs:732`). D5 scope clarified: the ≡_N canonicalizer applies at ALL positions (equations are identities) — the Exec corpus members verify the CANONICALIZER, while dynamic drop is verified via the comm-bound `*(x)` members.
- **Rocq landing status (updated 2026-06-13):** the monotone `CommReductionCorrespondence.v` remains classified as the M-RHO.2+ rules-as-data saturation layer. The M-RHO.1 linear consumption obligations are now discharged separately by `LinearCommCorrespondence.v`, which proves classifier totality/determinism, linear COMM soundness/completeness, quote/drop name canonicalization, grounding/COMM commutation, one-bind send-arrival permutation coverage, and statement-only fences for the strong-bisimulation/full-abstraction non-claims. `RhoObservationFingerprint.v`, `RhoGroundingAndNames.v`, `AmbiguityWitnessEnumeration.v`, and `RhoBackendFlipGate.v` remain supporting bridge kits with their stage assignments. All compile under `rocq-rho-bridge` with zero `Admitted`/`Axiom`/`Conjecture`.

## ★ §0-REVISION v4 (2026-06-13, AST-first backend course correction) — supersedes D1 for generated backends

The v2 D1 source-text decision was a conservative bring-up boundary, not the
production backend target. It is now superseded for generated MeTTaIL backends:

- **Generated values are normalized Rholang AST**: codegen returns
  `RhoProgram::Ast(RhoAstProgram { par: models::rhoapi::Par, text_annotation })`.
  The Rholang-looking string is a reader/debug annotation only; it is never a
  parser gate for generated backend correctness.
- **Generated execution is validation-gated**: raw `RhoProgram::Ast` values are
  inspectable lowering artifacts, not executable credentials. Runtime dispatch
  consumes the opaque Rust typestate `ValidatedRhoProgram`, which is produced
  only by `validate_rho_program` / `TryFrom<RhoProgram>` after checking the
  normalized contract shape and metadata. `RhoParWellFormedness.v` mirrors this
  with `validate_artifact_sound`, `validate_artifact_rejects_invalid`, and
  `lowered_scalar_program_validates`.
- **Direct injection is budgeted explicitly**: the runtime helper installs
  `Cost::unsafe_max()` before `RhoRuntime::inj(Par, Env<Par>, rand)`, matching
  the old source evaluator's budget while avoiding source parsing.
- **Normalizer invariants are now owned by codegen tests**: emitted contracts are
  inspected as AST for persistent receive shape, operand-first /
  return-channel-last ABI, and reverse de Bruijn binding order.
- **MeTTaIL parser replaces the Rholang parser for this path**: source snippets
  in the design remain pedagogical. The execution artifact is AST today and can
  evolve to Rholang bytecode later without making source text the boundary again.
- **Runtime selection is explicit and fail-closed**: user-facing execution calls
  `Language::run_default_backend_report`, whose inherited transition default
  may still be the legacy Ascent reference backend until a language-specific
  Dovetail or Rho gate installs the replacement backend. The production trait
  no longer exposes generic `AscentResults`-shaped backend/default helper
  methods; `RuntimeBackendDispatch.v` proves absent Dovetail/Rho defaults do
  not silently fall back to Ascent and report shapes must match the selected
  backend.

Hand-authored source-text oracle tests remain useful regressions for historical
host compiler/parser behavior, especially duplicate receive-channel negative
cases. They are not the generated backend architecture.

---

## 0. Frame and scope boundary

**What .1 IS** (per #281 body + design §1.4/§10): rhocalc is itself a ρ-fragment. Its `POutput`/`PInputs`/`PPar`/`PNew`/`PDrop`/`NQuote` map *directly* onto Rholang `Send`/`Receive`/`Par`/`New` — no Milner CBN encoding (that is M-RHO.2, explicitly NOT this stage). The `Comm` rewrite is un-encoded: it IS the host COMM (RSpace produce/consume rendezvous). Parallelism is delegated to `eval_par` (`tokio::spawn` per `P|Q`); MeTTaIL emits `Par`, never forks. Channel identity comes from ≡_N-canonical rendering (D5). First exercise of witness-set parity for non-confluent reduction (D7).

**What .1 is NOT:** the §7 generic CBN/CESK encoding (M-RHO.2); the per-language CESK runtime-backend flip to Rho default (M-RHO.4 — rhocalc uses Rho as its default runtime backend *only after* op-correspondence proofs and runtime gates, never on the blind oracle alone); the Δ1 N-ary min-cost-matching join (M-RHO.3). The active WPDA parser/recognizer remains upstream. Ascent is legacy for production rewrite execution and remains only as a reference/oracle path. The arithmetic/collection `fold` HOL rules (~50 rules + 82 congruence rewrites) are **out of the .1 reduction core** — they are M-RHO.2 HOL-native `Definition` handlers. Per D6, corpus members whose NFs *require* a fold post-transport are excluded from the .1.0 oracle (not "carried as opaque payloads" — non-native constructors have no rhoapi image; the honest boundary is exclusion-with-reason).

**The standing discipline:** a parser-side ERR — should one resurface (#313 lineage) — is never an engine-side oracle divergence. Verification never uses `PRATTAIL_TRACE=actions` (#312).

---

## 1. THE CODEGEN SURFACE — rhocalc rule classification (rule-level) + term-level disposition

### 1.0 Classifier input type (v2 — corrects v1's `&GrammarRule`-only signature)

`LanguageDef` separates `terms: Vec<GrammarRule>`, `equations: Vec<Equation>`, `rewrites: Vec<RewriteRule>`, `logic: Option<LogicBlock>` (`ast/src/language.rs:62-66`; `Equation` :167, `RewriteRule` :773). The Comm rule is a `RewriteRule`; QuoteDrop/ExecEq/Extrude are `Equation`s — a classifier over `&GrammarRule` can never see them. The deliverable is therefore:

```rust
enum RhoRuleRef<'a> {
    Term(&'a GrammarRule),
    Equation(&'a ast::Equation),
    Rewrite(&'a RewriteRule),
    Logic, // the LogicBlock, classified wholesale
}
fn classify_rho_rule(rule: RhoRuleRef) -> RhoClass
// RhoClass = { Comm, Structural, HolNative, Equation, Injection, Rejected }
```

extending `rholang-codegen/src/lower.rs` (today: `lower_language_def` iterates `def.terms` only and returns `RhoLowering { program: RhoProgram, … }` with a `rejected` partition). The existing `RhoLoweringTotalOrRejects.v` is a *boolean filter* partition (`supported : Rule -> bool`); the 5-way tagged classification is a **new** `classify : Rule -> Class` model over the disjoint union — a restatement, not a verbatim extension (mechanical, but stated honestly). The `LogicBlock` (raw Ascent clauses) classifies `HolNative` wholesale, recorded in the totality claim.

### 1a. Terms (`terms { … }`) — the ρ-process constructors

| Rule (rhocalc.rs:line) | Concrete syntax | Class | .1 disposition / image |
|---|---|---|---|
| `PZero` (:67) | `{}` | **structural** | renders `Nil`. |
| `PPar` (:72) | `{ p \| q \| … }` (HashBag) | **structural** | renders `p \| q \| …`; the ambient `Par`. Maximal parallelism is `eval_par`'s spawn-per-member. NEVER fork host-side. |
| `POutput` (:74) | `n!(q)` | **COMM (send half)** | renders `⟦n⟧!(⟦q⟧)` — linear send. |
| `PInputs` (:77) | `(n1?x1,…,nk?xk).{p}` | **COMM (receive half)** | builds the k-bind join AST equivalent to `for(x1 <- ⟦n1⟧ & … & xk <- ⟦nk⟧){ ⟦p⟧ }` — atomic all-or-nothing rendezvous, the host's native polyadic join. Distinct receive channels are green. Lower-level RSpace `consume` supports duplicate channel groups; the historical source parser rejects duplicate receives with `Receiving on the same channels is currently not allowed`, so source-text tests keep that as a negative regression while AST/RSpace evidence owns the positive runtime claim. |
| `PNew` (:83) | `new(xs) in {p}` | **structural-binder** | renders `new x1,…,xj in { ⟦p⟧ }`; RSpace ν-semantics gives unforgeable disjointness; fingerprints ν-quotient `GPrivate`s (D5). |
| `NQuote` (:80) | `@(p)` | **injection (name)** | renders `@{⟦p⟧}` (conservative bracing). A name IS a quoted process. |
| `PDrop` (:70) | `*(n)` | **injection (drop)** | renders `*⟦n⟧`; `*(@(P))→P` is canonicalized statically by D5's ExecEq pass where it occurs under a name position, and is the host's eval where dynamic. |
| `Err` (:88) | `error` | **injection (sentinel)** | NOT in any .1.0 corpus member; renderer treats it as out-of-fragment (loud harness error if encountered) — recorded `Rejected` at term level. |
| `CastInt`/`CastBool`/`CastStr` (:98–100) | scalar→Proc | **injection (native scalar)** | renders the Rholang literal (`GInt`/`GBool`/`GString` image via source). |
| `CastBigInt/BigRat/Fixed/Float/UInt32` (:93–97), `CastList/Bag/Map` (:101–103) | non-native→Proc | **injection (non-native)** | **REJECTED for .1** (no rhoapi image; no Rholang literal syntax for Bag/Map). In `rejected`, miss-nothing. |

### 1a′. Term-level dispositions for constructors with NO LanguageDef rule (v2 — closes the totality gap)

The macro auto-generates per-category constructors that correspond to no rule: `Var(OrdVar)` (`macros/src/gen/types/enums.rs:112-116`), `Apply{Domain}`/`MApply{Domain}` (:155-167), and the `LamProc`/`MLamProc` variants the logic block matches (`rhocalc.rs:1023,1028`). Rule-level totality therefore does NOT give term-level totality of `⟦·⟧`; the renderer recurses over Proc/Name constructors and needs a disposition for each:

| Constructor | .1 disposition |
|---|---|
| `Proc::Var` / `Name::Var`, **free** | grounding σ (D2): Name var → `@"mtl:<name>"`; Proc var → `@"mtl#out"!("mtl:<name>")`. **Load-bearing: every .1.0 corpus member contains free Vars.** |
| `Proc::Var` / `Name::Var`, **bound** (under a `PInputs`/`PNew` binder) | renders as the Rholang bound variable; the HOST normalizer owns de Bruijn/`locally_free`/`connective_used` (D1). |
| `LamProc`/`MLamProc`/`ApplyProc`/`MApplyProc` | **Rejected** for .1 (no corpus member; HOL-lambda is M-RHO.2). Loud renderer error. |

### 1b. HOL `fold` rules (OUT of .1 core)

`IntBinProc UIntBinProc FloatBinProc FixedBinProc BigintCastProc BigratCastProc` (:106–123); `NegInt` (:127 — Int→Int, not Proc); `FractionProc` (:130); `Or And` (:147,157); `BitOr BitAnd BitNot` (:169,195,221); `Eq Ne Gt Lt GtEq LtEq` (:249–399); `Add Sub Mul Div Mod NegProc` (:430–569); `ConcatList ElemList DeleteList` (:600–615); `UnionBag RemoveBag DiffBag CountBag` (:626–659 — CountBag lands in Int); `GetMap PutMap DeleteMap MergeMap HasMap KeysMap ValuesMap` (:670–736); `Not Len ToBool ToStr` (:746–819). All classify **HolNative**; they ride Ascent (the oracle baseline). Corpus members whose NFs need them are excluded per D6.

### 1c. Equations

| Equation (rhocalc.rs:line) | Statement | Class | .1 disposition |
|---|---|---|---|
| `QuoteDrop` (:858) | `@(*(n)) = n` | **equation (≡_N)** | D5 canonicalizer rewrite (static, pre-render). |
| `ExecEq` (:860) | `*(@(P)) = P` | **equation (≡_N)** | D5 canonicalizer rewrite (static, pre-render). |
| `Extrude` (:862) | `{new(xs).p \| rest} = new(xs).{p \| rest}`, `xs # rest` | **equation (scope extrusion)** | host-native ν-mobility; no render-time action. |

### 1d. Rewrites

| Rewrite (rhocalc.rs:line) | Class | .1 disposition |
|---|---|---|
| **`Comm`** (:870–871) | **COMM — THE FAST PATH** | Un-encoded = host COMM. The k-bind `Receive` + k matching `Send`s rendezvous in RSpace; continuation binding is the host's `ReceiveBind` substitution. **M-RHO.1.0's single milestone.** |
| `Exec` (:873) | **structural-reduction** | `*(@(P)) ~> P` — host `*` eval (and D5 static canonicalization where applicable). |
| `ParCong` (:875) | **structural-congruence** | the AMBIENT par-context = `eval_par` itself; not a generated rule. |
| `NewCong` (:877) | **structural-congruence** | reduction under ν; host-native. |
| `AddCongL…ToStrCong` (:881–983, **82 rules**) | **HOL-congruence** | out of .1 core; ride Ascent (M-RHO.2). |

### 1e. Logic block (:986+)

`fold_proc` (:988) + the lambda-application clauses (:1021–1030). **HolNative wholesale**; P6b confirmed no Ascent-side work for this epic.

---

## 2. THE LOWERING — normalized AST generation (v4) + name canonicalization (D5) + grounding (D2)

**Pipeline per corpus term `t`:**

```
t : rhocalc Proc (parsed Term)
  │ 1. ≡_N-canonicalize (QuoteDrop/ExecEq exhaustive cancellation; terminating)
  │ 2. ground free vars σ (Name var → @"mtl:<name>" ; Proc var → @"mtl#out"!("mtl:<name>"))
  │ 3. build normalized Rholang AST (`Par`) directly (the §1a/§1a′ map; partial over the ρ-core, loud on out-of-fragment)
  ▼
rhoapi::Par ──> RhoRuntime::inj (explicit Cost::unsafe_max budget;
              generated AST owns de Bruijn, locally_free, connective_used, bind ordering, Par sorting)
  ▼
inj Ok/Err + soft-checkpoint hot-store dump ──> canonical fingerprint (D3/D5)
```

**AST generator residence:** for .1 the rhocalc-Term→Rholang AST generator is
**harness-level** when it depends on `languages`' generated `Proc`/`Name`
types. The spec-level `rholang-codegen` owns the `LanguageDef → RhoProgram`
surface for generated backends and emits normalized `Par` directly. The
spec-driven, per-language term generator is the M-RHO.4 `generate_rho_vm` codegen
concern. `classify_rho_rule` (§1.0) DOES land in `lower.rs` now (it is
spec-level).

**AST fidelity gate:** malformed generated contracts fail AST-shape tests or
direct injection. `RhoLoweringTotalOrRejects.v` proves no source rule is
silently dropped, `LinearCommCorrespondence.v` proves the linear COMM model, and
the runtime oracle proves the generated AST executes on the host Rho machine.
Rholang source remains an annotation for humans and a separate hand-authored
regression surface.

**Rhoapi accuracy notes:** `Send` also carries `locally_free`/`connective_used`;
`Receive` also carries those plus the host-extension `condition: Option<Par>`
(where-clause guard, evaluated via `check_commit` on BOTH match paths —
`reduce.rs:1059-1064`, `rspace.rs:667-677`, `space_matcher.rs:156-172`);
`Receive.bind_count` is the receive's total FREE-VAR count
(`p_input_normalizer.rs:485`), used as the body env shift (`reduce.rs:1093`) —
numerically equal to the bind count for rhocalc's one-var-per-bind `PInputs`,
divergent in general. Under v4 the AST generator owns these invariants.

**Channel disjointness invariant (replaces v1's ContentKey-payload claim):** two object channels collide in RSpace **iff** name-equivalent (≡_N). Realized by D5: canonical AST generation ⇒ the host's content-total `ParSortMatcher` sort ⇒ one channel `Par`. `ContentKey` remains the comparison-discipline SPEC (exact bytes, never a 64-bit hash, never order) — the fingerprint comparison (D3) satisfies it by construction. Proven as §4 thm 4 (`name_canonicalization_sound_complete`).

---

## 3. THE FIRST VERIFIABLE MILESTONE — M-RHO.1.0

**Milestone: ONE rhocalc reduction — the `Comm` rule — round-trips through `RhoRuntime` with the differential oracle GREEN on the transport-pure comm corpus.**

The smallest end-to-end green, walked concretely:
- **Input:** `{(c?x).{*(x)} | c!(p)}` (`rhocalc_tests::comm::single_channel`). Free `c` (Name), free `p` (Proc).
- **Ascent side:** `normal_forms_reachable_from_seeds([t])` → `{ p }` (singleton on this member).
- **Rho side:** σ-ground + render — `p` in DATA position grounds to the sentinel-send *process*, giving `for(x <- @"mtl:c"){ *x } | @"mtl:c"!({@"mtl#out"!("mtl:p")})`. (A send in data position is quoted data, not executed — the reducer evaluates expressions inside data but does not fire its sends.) Evaluate (in-memory runtime, `Cost::unsafe_max`): COMM fires; `x` binds `@{sentinel-send}`; `*x` runs the sentinel send; datum `"mtl:p"` RESTS at `@"mtl#out"`.
- **Ascent NF image:** `⟦p⟧σ` = the sentinel send alone → evaluates to the same resting datum.
- **Gate:** fingerprint(`⟦t⟧σ`) **= member of** { fingerprint(`⟦nf⟧σ`) } — here singleton equality: datum `"mtl:p"` at `@"mtl#out"`, no NON-EMPTY row at `@"mtl:c"` (the consumed receive is the COMM-fired evidence; per D3-PIN the raw dump WILL contain `[]`-valued rows at touched channels — the read-through-cache residue — which DROP-EMPTY normalization removes). `EvaluateResult.errors = ∅` on every run.

**The .1.0 corpus (exact test paths, transport-pure per D6):**

| # | Test (`languages/tests/rhocalc_tests.rs`) | NF (Ascent, reachable-from-seeds) | Discrimination |
|---|---|---|---|
| 1 | `comm::single_channel` | `p` | sentinel datum |
| 2 | `comm::comm_substitutes_quoted_value` (`{(c?x).{*(x)} \| c!(0)}`) | `0` | quiescence (consumed receive) + ∅ errors |
| 3 | `comm::multi_input_two_channels` | per test | sentinel data |
| 4 | `comm::multi_input_uses_both_vars` | `{p \| q}` | two sentinel data |
| 5 | `comm::multi_input_three_channels` | per test | sentinel data |
| 6 | `comm::comm_with_body_using_channel` (`{(c?x).{x!(0)} \| c!(p)}`) | `p!(0)` | datum `0` at the RECEIVED-name channel — exercises D5's data-as-channel identity |
| 7 | `comm::comm_with_remaining_parallel` | `{p \| q}` | sentinel data |
| 8 | `comm::join_pattern_same_channel` | `{a \| b}` (multiset-singleton) | **source-text excluded today**: the host parser rejects duplicate receive channels (`ReceiveOnSameChannelsError`); covered by a negative runtime regression until direct ADT lowering or a parser-supported encoding lands. |
| 9 | `new_and_extrusion::new_is_normal_when_body_is`: `new(x) in { x!(0) }` (NF = itself) | resting datum `0` at a `GPrivate` channel | forces the ν-quotient mechanism early (single-ν per §0-REVISION v3) |
| 10 | `exec::exec_basic` (`{*(@(0))}`) | `0` | the ≡_N canonicalizer (static ExecEq) + quiescence |
| 11 | `exec::exec_with_process` (`{*(@(a!(0)))}`) | `a!(0)` | datum `0` at `@"mtl:a"` — datum-shaped Exec result |
| 12 | `congruence::par_cong_exec` (`{*(@(0)) \| q}`) | `{0 \| q}` | sentinel datum + canonicalized Exec under par |
| 13 | `congruence::new_cong` (`new(x) in { *(@(0)) }`) | `new(x) in { 0 }` | Exec under ν; quiescence both sides |
| 14 | `new_and_extrusion::new_congruence_reaches_normal_form` (`new(x) in { {(a?z).{*(z)} \| a!(0)} }`) | `new(x) in { 0 }` | COMM under the ν-binder (NewCong territory); quiescence |
| 15 | `new_and_extrusion::extrusion_reaches_result` (`{new(x) in { (a?z).{*(z)} } \| a!(0)}`) | `new(x) in { 0 }` | scope extrusion — operationally NATIVE on the host (the receive registers at the free channel from inside ν; no Extrude step) |
| 16 | `new_and_extrusion::extrusion_blocked_when_not_fresh` (`{new(a) in { (a?z).{*(z)} } \| a!(0)}`) | itself (stuck) | ν-SHADOWING aligns natively: the bound `a` is a fresh `GPrivate` ≠ the free `@"mtl:a"` — no COMM either side; parked receive + resting datum discriminate |

**Excluded with reason (the M-RHO.2 acceptance bridge):** `cast_under_send` (:1033-1040, fold `IntBinProc`), `native_ops::bag::remove_comm` (:683-688, `fold_proc`+`RemoveBag`), `native_ops::bag::count_comm` (:692-694, `CountBag`→Int), `congruence::add_cong` (:274, Exec+`Add` fold), `congruence::comparison_cong` (:280, Exec+`Eq` fold). *(Naming note: v1's "FULL comm family" phrasing is replaced by this exact-path table; renderer-fidelity note — members 10–13 verify the D5 canonicalizer (static ≡_N cancellation), while DYNAMIC drop through a COMM-bound name is verified by members 1/3/4/5.)*

**M/D/I/L for M-RHO.1.0:**
- **M (model, lands first, zero-admission):** the §1.0 `classify` model over the Rule disjoint union (restated `RhoLoweringTotalOrRejects.v` extension or sibling); `CommReductionCorrespondence.v` thms 1–6 + statement-only fences (§4). Axiom-free; NO `Conjecture` vernacular (D8).
- **D (diagnostic):** the `rho_comm_oracle` harness in `rholang-runtime/tests/` reporting per-member `{ascent_nf_fingerprints, rho_fingerprint, member_of?, errors}` before any gate is asserted.
- **I (implement):** ≡_N canonicalizer + σ-grounding + renderer (harness-level); `classify_rho_rule` in `lower.rs`; soft-checkpoint fingerprint reader in `rholang-runtime` (`run.rs` extension beside `get_data`); the oracle gate.
- **L (ledger):** per-member verdicts + the D6 exclusions + any parser-side STOP, program-ledger style; boyscout: fix `rholang-runtime/src/lib.rs`'s stale Status section while in there.

---

## 4. THE Rocq OBLIGATIONS — operational correspondence, funded fragment, up-to-weak-bisim

**File:** `formal/rocq/rho_bridge/theories/CommReductionCorrespondence.v` (new; sixth rho_bridge theory). **Discipline:** Rocq 9.1, zero `Admitted`/`Axiom`/`Assumption`/`Parameter`-as-fact, **and zero `Conjecture`** (≡ Axiom — D8). **Reuse is by faithful re-statement** (the `MettaFundingLawsConformance.v:24` precedent; cross-repo `Require Import` is not wired and stays that way). Schematic over the codegen.

**Scope caveat (binding, from the source plan):** correspondence is **up-to-weak-bisimulation over the funded fragment** — NOT strong bisim (upstream `CAForceSeparation.v` PROVES strong bisim fails at force points), NOT full abstraction.

**The .1 obligation set:**
1. `classify_total` / `classify_buckets_disjoint` — every rule of the disjoint union (terms ∪ equations ∪ rewrites ∪ logic) lands in exactly one `RhoClass` (new model per §1.0; mechanical).
2. `comm_step_sound` — if the lowered image fires a COMM, the source takes the `Comm ~>` step and the post-COMM image is the lowering of the reduct **up to weak barbed equivalence** (abstract `RhoTerm` + `weak_barb` re-statement; fresh-channel names ignored by ≈_b).
3. `comm_step_complete` — funded-fragment completeness: a funded source `Comm` redex (`is_funded` via the verified `delta_sigma` image, `MettaFundingLawsConformance.v`) has a corresponding COMM in the image. Fund-gating is what makes completeness hold.
4. `name_canonicalization_sound_complete` — D5's canonicalizer: `canon(n1) = canon(n2) ⟺ n1 ≡_N n2` (QuoteDrop/ExecEq closure) over the ρ-core Name syntax, plus `canon_terminating`. **This replaces v1's ContentKey-payload theorem** and is cleanly provable over inductive syntax.
5. `grounding_commutes` — D2's σ commutes with `Comm`/`Exec` reduction on the corpus fragment (free vars are inert: no rule fires on a bare `Var`).
6. `send_permutation_enumeration_covers_eager_races` — D7's derived scope: for k contending sends against a **1-bind** receive, enumerating send-arrival permutations covers the rendezvous-outcome set — each arrival step has exactly ONE candidate (the arriving datum against a parked receive, or the sole resting datum), so the per-step commit is total and entropy-independent. *(The v2 companion negative `join_assignment_not_arrival_explorable` is KILLED per §0-REVISION v3 D7-CORRECTION — it modeled a hash-pinned assignment the host does not implement; the produce path prepends the arriving datum after the hash sort, `rspace.rs:818-825`. No lemma about multi-bind same-channel joins is stated: they are source-unreachable under D1.)*
7. **Fences (statement-only, D8):** `Definition strong_bisim_fails_at_force_statement : Prop := …` and `Definition full_abstraction_statement : Prop := …` — defined, never asserted, each with a comment citing the upstream proof/`Conjecture` location in `f1r3node-rust/formal/rocq/cost_accounted_rho/`. A future reader cannot mistake funded weak-bisim for strong bisim, and `Print Assumptions` stays empty.

**Landed-kit map (§0-REVISION v3 — updated):** `LinearCommCorrespondence.v` discharges the §4 M-RHO.1 linear obligations without over-claiming the monotone saturation model. `RhoObservationFingerprint.v` (exact-key/order-irrelevance) is the comparison-discipline layer under the D3 gate; `RhoGroundingAndNames.v` (ν-freshness/no-capture) supplies supporting name-freshness lemmas; `CommReductionCorrespondence.v` models monotone persistent-contract firing for the M-RHO.2+ rules-as-data layer; `RhoAstSendBoundary.v` proves dynamic call and witness sends are AST inputs, never source-text inputs; `AmbiguityWitnessEnumeration.v`/`AmbiguitySetPreservation.v` cover the ambiguity witness model; `RhoBackendFlipGate.v` is the M-RHO.4 gate conjunction.

---

## 5. THE NON-CONFLUENT PARITY EXERCISE (M-RHO.1.1) — witness enumeration, corrected mechanism

rhocalc is intentionally non-confluent: `Comm` chooses among enabled rendezvous. **v1's flagship witness (`join_pattern_same_channel`) is confluent-up-to-multiset** — body `{{*(x) | *(y)}}` makes both bindings the same HashBag NF (`{a|b}` = `{b|a}`; the corpus' own `multiset_eq` exists because of this) — so it exercises nothing. **The .1.1 gate input is an order-SENSITIVE single-bind contention race** (new oracle member, harness-level — NOT a new rhocalc_tests parser test):

```
{ (c?x).{ *(x) }  |  c!(a)  |  c!(b) }      — Ascent reachable-NF set = { {a | b-send-rests}, {b | a-send-rests} }
```

(the linear receive consumes ONE of the two contending sends; the loser RESTS as a datum — both the fired branch and the resting datum are part of the D3 fingerprint, so the two outcomes are distinct fingerprints).

**Mechanism (D7):**
- **Collection:** outcome witnesses are D2's sentinel sends resting on the **receive-less** `@"mtl#out"` channel (the host idiom for append-only accumulation; a persistent receive would CONSUME them).
- **Enumeration:** the host's candidate selection is deterministic by design (`deterministic_candidate_hash`, `rspace.rs:1211-1233`), so outcome coverage comes from the HARNESS enumerating send-arrival orders: evaluate the receive member, then the k producer sends one per step, per permutation π ∈ S_k; soft-checkpoint fingerprint per π; collect the outcome SET. This covers exactly the **eager-fire races** (D7's derived scope): a 1-bind receive commits to the sole resting datum at each arrival step, so π = [a,b] yields `x=a` and π = [b,a] yields `x=b`.
- **Gate:** enumerated rho outcome set ≡ Ascent `normal_forms_reachable_from_seeds` set (both as D3 fingerprints of the grounded NF images). Set-EQUALITY is satisfiable here precisely because enumeration replaces the single run; backstopped by §4 thm 6.
- **Recorded limit (multi-bind same-channel joins):** the .1 source-text host path rejects duplicate receive channels at normalization (`ReceiveOnSameChannelsError`, `p_input_normalizer.rs:408-423`) — these inputs never reach RSpace through the source-text oracle. The lower-level RSpace behavior is covered by direct runtime regressions, and the M-RHO.3 ambiguity layer now represents scheduler alternatives as explicit exact-key witnesses rather than relying on resting-candidate order. *(v2's claim that such a join's assignment is "hash-pinned — arrival order explores nothing" was REFUTED in round 2 — the produce path prepends the arriving datum after the hash sort (`rspace.rs:818-825`) and the hash itself ingests `thread_rng`-derived state in the harness context; see §0-REVISION v3 D7-CORRECTION. The harness must never rely on resting-candidate selection order.)*

This realizes ambiguity-set-preservation ("miss nothing" surviving the flip to RSpace) on the eager-fire fragment: every nondeterministic branch is a first-class witness, none pruned; the same-channel join-assignment and source-parser residue is named and scheduled (M-RHO.3), not dropped.

---

## 6. THE VERIFICATION LADDER (per-stage gates; battery untouched)

1. **Axiom-free Rocq.** `CommReductionCorrespondence.v` + the §1.0 classify model compile with zero `Admitted`/`Axiom`/`Assumption`/`Conjecture`; `Print Assumptions` clean; existing five theories stay green. Build via the rho_bridge `CoqMakefile` target (`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge`).
2. **Differential oracle (.1.0).** `rholang-runtime/tests/rho_comm_oracle.rs`: the §3 corpus (members 1–7, 9–16) green under the D3 membership gate, with member #8 (same-channel join) covered by an explicit parser-boundary regression asserting the `ReceiveOnSameChannelsError` class. Existing `rho_vs_ascent` + `run_calculator` stay green (no regression to M-RHO.0), and their generated invocation sends use `mettail_rholang_codegen::RhoAstSend` normalized AST rather than hand-written source text or test-local raw `Par` assembly.
3. **Non-confluent set-parity (.1.1).** The §5 enumeration harness is green on the order-sensitive one-bind input: `rho_comm_oracle.rs` installs the receive, evaluates sends one at a time in both arrival orders on the same in-memory RhoRuntime, and observes both `{fired=a, resting=b}` and `{fired=b, resting=a}` fingerprints.
4. **AST ambiguity witness gate.** `rholang-runtime/tests/rho_ambiguity_ast.rs` injects receive-less ambiguity witnesses as normalized AST sends, observes grouped key/payload tuples, and feeds them into `AmbiguityWitnessSet`; schedule order preserves the observed set, exact duplicates are idempotent, and conflicting payloads for the same exact key reject.
5. **f1r3node-rust conformance gate.** `mettail_rust_is_not_a_cargo_dependency` (`accounting/resource_logic.rs:292-293`) STAYS PASSING; `BridgeInertness.v` one-way. The bridge-local B1-a conformance kit is the accepted gate for this repository: `MettaFundingLawsConformance.v` proves the modeled laws, and `rholang-adapter` re-hosts the same four generic laws against `OslfResourceLogic<MettaGslt>` without changing the host deploy-admission path.
6. **Welch.** Expect NEUTRAL (the COMM path is host-owned; MeTTaIL emits normalized `rhoapi::Par`, with source text retained only as reader/debug annotation). Panel only if a mettail-side runtime path materially changes; record per the P-series cadence.
7. **Battery sentinel.** `prattail` lib, `gen_calculator_op` 1330/0, `edge_case` 229/0, `gen_rhocalc_op` 530/1 (pre-existing), dovetail 51/0, `ledtest` 220/0, **`rhocalc_tests` 126/0**. **M-RHO.1 changes NO parser codegen and NO `languages/tests` parser tests** (the §5 order-sensitive input lives in the oracle harness).

---

## 7. RISK REGISTER (v2)

| # | Risk | Disposition |
|---|---|---|
| R1 | ~~rhocalc basics don't parse~~ | **DISSOLVED** (§0-AMENDMENT). Residual discipline: parser ERR ≠ engine divergence. |
| R2 | **Trace Heisenbug** (#312): `PRATTAIL_TRACE=actions` perturbs parses. | NEVER verify via action traces; walker-stats + behavioral probes + the outcome-set oracle only. |
| R3 | **dovetail dep scope.** | v2: D5 removed the ContentKey-payload need — .1 requires NO dovetail dependency in the bridge crates (dovetail has no `key` feature anyway; the dep would be whole-crate). `ContentKey` stays the comparison SPEC; the fingerprint realizes it. DV-1 demand-gated saturation remains M-RHO.3. |
| R4 | **Channel-identity nondeterminism (P4's 313× lesson).** | D5: identity = ≡_N-canonical content via the host's content-total sort; never insertion order / 64-bit hash / uncanonicalized Display. §4 thm 4 proves the canonicalizer. |
| R5 | **gxhash/aes toolchain.** | Unchanged mitigation (`Cargo.toml` LLVM scoping verbatim at :72-80); .1 adds no new gxhash-touching deps; do not unify toolchains. |
| R6 | **Over-claiming the correspondence.** | Funded weak-bisim only; D8 statement-only fences; completeness fund-gated by construction. |
| R7 | **Scope creep into .2/.3.** | D6 exclusion list is the boundary; folds/lambdas/Δ1 ride Ascent. |
| R8 | **B1-b blast radius.** | Casper-located (`acceptance.rs:483-492`); USER-OK gated with the location named; guard test green is non-negotiable either way. |
| R9 | **AST fidelity** (new): the rhocalc→Rholang AST generator mis-building a member. | Generated contracts are checked as normalized `Par`; direct `inj` fails loudly; `RhoLoweringTotalOrRejects.v`, `LinearCommCorrespondence.v`, and the runtime oracle cover the generated AST boundary. |
| R10 | **Observation blind spots** (new): empty-space false-greens on inert-NF members. | D3's discrimination argument: an unfired COMM leaves the parked Receive in the dump; sentinel sends make all variable-valued NFs datum-shaped. **The `errors = ∅` assertion is load-bearing and may NEVER be weakened**: on any evaluate error the host REVERTS the space (`rho_runtime.rs:117-120`), so an erroring t-run's dump equals the pre-eval state — which for inert-NF members fingerprint-matches the nf-image's empty dump (a silent false-GREEN without the assertion). |

---

## 8. STAGED EXECUTION SUMMARY (the contract, sequenced)

- **M-RHO.1.0 — single-COMM milestone (keystone).** M: classify model + `CommReductionCorrespondence.v` (thms 1–6, statement-only fences), axiom-free. D: oracle harness diagnostic. I: ≡_N canonicalizer + σ-grounding + renderer (harness-level) + `classify_rho_rule` (`lower.rs`) + soft-checkpoint fingerprint reader (`run.rs`). L: ledger. **Exit:** the §3 nine-member corpus green under the membership gate; `single_channel` round-trips end-to-end.
- **M-RHO.1.1 — witness enumeration (non-confluent parity).** The §5 order-sensitive join input; sequential permutation enumeration; outcome-SET ≡ reachable-NF set. **Exit:** set-parity green; §4 thm 6 compiled.
- **M-RHO.1.2 — conformance + ladder close.** Guard green; bridge-local funding-law kit green; Welch expected neutral because the COMM path is host-owned Rho machine execution; battery sentinel; ledger verdict.
- **Cross-stage coordinates:** #313, #312 constrain method; neither owned by .1.

**The disciplines, restated:** a parser-side ERR is never an engine-side divergence · verify by outcome-set fingerprints, never action traces · name identity = canonical content, never order · prove only funded weak-bisim · fences are statement-only `Definition`s, never `Conjecture`.
