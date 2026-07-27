# M-RHO.1 red-team ledger

Per `feedback_red_team_design_until_convergence`: after the contract was drafted, independent adversarial critics attempt to REFUTE it, iterating until convergence, BEFORE implementation. This ledger records every round — including refuted v1 mechanisms — so failed designs are never re-attempted.

## Round 1 (2026-06-12) — 2 independent critics vs contract v1 → BOTH NOT-CONVERGED

- **Critic H** (host-grounding lens, f1r3node-rust): 5 BLOCKERs, 2 MAJORs, 4 MINORs.
- **Critic F** (mettail+FV lens, mettail-rust): 4 BLOCKERs, 5 MAJORs, 6 MINORs.
- Convergent independent discoveries (both critics, unprompted): the free-variable wall, the missing observation protocol, the oracle type/grounding mismatch, the string-vs-Par unmade decision, single-run-vs-set unsatisfiability.

### Findings → resolutions (v2 decision IDs in `01-mrho1-execution-contract.md` §0-REVISION)

| Finding | Critic(s) | Evidence (key cites) | Resolution |
|---|---|---|---|
| B: "hand the Par to RhoRuntime" names a string-taking entry; the Par-direct `inj` path has empty cost budget + no `EvaluateResult` | H-B1 | `rho_runtime.rs:91-94,140-145,1268,1244-1252` | **D1**: source-text path committed; Par-direct RECORDED-REJECTED for .1 |
| B: hand-assembled Pars — `connective_used=false` silently kills COMM; de Bruijn/`locally_free`/bind-sort conventions unspecified | H-B2 | `spatial_matcher.rs:178-181`; `match.rs:22-60`; `dispatch.rs:14-19`; `env.rs:33-47`; `reduce.rs:1090-1094`; `p_input_normalizer.rs:394-395` | **D1** (normalizer owns all of it); conventions recorded in §2 informational block for any future Par-direct work |
| B: oracle observation reads NOTHING — bare-process NFs rest on no channel; M-RHO.0 precedent is a wrapper capture | H-B3, F-B1 | `reduce.rs:198-206`; `rho_vs_ascent.rs:52`; `run.rs:75-85` | **D3**: soft-checkpoint resting-space fingerprint + sentinel sends + quiescence discrimination |
| B: corpus terms have top-level free vars; both paths hard-error; `normalizer_env` dead in the Rust port | H-B4, F-B1 | `compiler.rs:106-118`; `errors.rs:23`; `reduce.rs:1120-1141`; `normalize.rs:88` (`_env`, zero consumers) | **D2**: σ-grounding (Name→`@"mtl:<name>"`, Proc→sentinel send), applied to BOTH sides; `grounding_commutes` lemma |
| B: witness accumulator inverted — persistent receive CONSUMES; `get_joins` returns join groups not data; `normalize.rs` citation wrong layer | H-B5 | `rho_runtime.rs:200-202,395-401`; `p_input_normalizer.rs:275-281,501`; `reduce.rs:1102` | **D7**: receive-less accumulation channel; citation corrected |
| B: gate type-mismatch (Term vs Par), "established ContentKey oracle" false (it is display-membership), raw `normal_forms()` subterm-polluted, .1.0 set-≡ unsatisfiable on a single run | F-B2 | `runtime/src/language.rs:692,724-735`; `dovetail/src/key.rs:84-96`; `rho_vs_ascent.rs:8-11,80-83` | **D3** (fingerprint domain unifies both sides) + **D4** (reachable-from-seeds) + membership gate at .1.0, set-≡ only under .1.1 enumeration |
| B: `Conjecture` ≡ `Axiom` in Rocq — v1's fences violate the zero-Axiom gate they sit beside | F-B3 | empirical `Print Assumptions`; `_CoqProject` header | **D8**: statement-only `Definition …_statement : Prop`; `Conjecture` banned in §4/§6 |
| B: fold-dependent corpus members structurally red under .1 scope; "opaque payload" encoding doesn't exist (no rhoapi image) | F-B4 | `rholang_tests.rs:683-694,1033-1040`; `rholang.rs:106,635,659,988` | **D6**: exclusion-with-reason; they become the M-RHO.2 acceptance bridge |
| M: single-run vs outcome-set — host COMM selection deliberately deterministic; re-running has no coverage | H-M6 | `rspace.rs:1211-1233` (`deterministic_candidate_hash`), `reduce.rs:279-283` | **D7**: harness-side sequential send-permutation enumeration + `send_permutation_enumeration_covers` lemma |
| M: channel/data double-representation — ContentKey-as-payload kills Exec (no decoder) and breaks data-as-channel rendezvous; `quoted_channel` wraps a GString, not a body | H-M7 | `rspace.rs:338-339,373`; `run.rs:24-31` | **D5**: ≡_N canonicalizer pre-render; ContentKey demoted to comparison SPEC; §4 thm 4 restated as `name_canonicalization_sound_complete` |
| M: classifier type-incoherent (`&GrammarRule` can't see `RewriteRule`/`Equation`); partition model is a restatement, not an extension | F-M5 | `ast/src/language.rs:62-66,167,773`; `lower.rs:124` | §1.0: `RhoRuleRef` disjoint-union input; restatement stated honestly |
| M: auto-generated `Var`/`Lam`/`Apply` constructors unbucketed; `Var` load-bearing in every corpus member | F-M6 | `macros/src/gen/types/enums.rs:112-167`; `rholang.rs:1023,1028` | §1a′: term-level disposition table (free Var→σ, bound Var→host, Lam/Apply→Rejected) |
| M: ContentKey keying has no impl path (zero `SemanticHash` impls outside dovetail; codegen-freeze conflict; missing ≡_N canonicalizer; `lower.rs` is string-emitting and rholang-free) | F-M7 | grep; `rholang-codegen/Cargo.toml`; `lower.rs:29-33` | **D1+D5**; renderer placed harness-level (§2 residence), `classify` stays spec-level |
| M: cross-repo Rocq import not wired; "≈95% reuse" misleads | F-M8 | `rho_bridge/_CoqProject`; `MettaFundingLawsConformance.v:24` | **D8**: reuse-by-faithful-re-statement stated; §4 rewritten |
| M: flagship "non-confluent" witness is confluent-up-to-multiset (HashBag body) — exercise vacuous | F-M9 | `rholang_tests.rs:171-173`; `rholang.rs:72` | §5: order-sensitive join `{(c?x,c?y).{*(x)} \| c!(a) \| c!(b)}` (outcome set `{a,b}`) as the .1.1 gate input, harness-level |
| m: `Send`/`Receive` field omissions (`locally_free`, `connective_used`, host-extension `condition`) | H-m8, H-m11 | `rhoapi.rs:167-179,225-247` | §2 informational block (normalizer-owned under D1; `condition=None` noted) |
| m: `bind_count` = total free-var count, not bind count | H-m9 | `p_input_normalizer.rs:485`; `reduce.rs:1093` | §2 informational block |
| m: B1-b gate seam lives in casper (`acceptance.rs:483-492`), not the accounting module — blast radius understated | H-m10 | `casper/src/rust/util/rholang/acceptance.rs:483-492` | §6 item 4 + R8 name casper; USER-OK gate text updated |
| m: `NegInt` is Int→Int; `CountBag`→Int; congruence count is 82 not ~70; law-kit lines `:120-209` | F-m1,2,3 | `rholang.rs:127,659`; `:881-983`; `conformance.rs:7` | §1b/§1d corrected |
| m: dovetail has no `key` feature (dep would be whole-crate) | F-m4 | `dovetail/Cargo.toml` | Moot under D5 (no dovetail dep needed); R3 rewritten |
| m: `rholang-runtime/src/lib.rs` Status section stale | F-m5 | `lib.rs:13-16` vs Cargo.toml | Boyscout fix scheduled in .1.0-L |
| m: §3's "`normal_forms()` → `["p"]`" was a membership assertion misread as a set claim | F-m6 | `rholang_tests.rs:44-64` | §3 rewritten on reachable-from-seeds + membership |

### Verified-pass items (claims that survived round 1 — do not re-investigate)
- §1 rule names/line cites all exact (Critic F, full sweep); Comm/PInputs shapes read correctly.
- k-distinct-channel joins are supported by the source-text path. Lower-level RSpace `consume` supports duplicate channel groups (`rspace.rs:330-334,652-655`; `space_matcher.rs:81-105`), but `evaluate_with_term` currently rejects duplicate receive channels before runtime evaluation. `join_pattern_same_channel` is therefore a source-text excluded case for .1 and needs direct ADT lowering or a parser-supported encoding before it can be promoted.
- B1-b artifacts real (`resource_logic.rs:120-209,292-293`); `InMemoryStoreManager` no-disk runtime as claimed (`run.rs:50-65`); string-path phlo = `Cost::unsafe_max()` (`rho_runtime.rs:91-94`).
- gxhash LLVM profile scoping verbatim (`mettail-rust/Cargo.toml:72-80`); five rho_bridge theories + claimed contents confirmed; `generate_rho_vm` absence confirmed; CA* capstones exist at `f1r3node-rust/formal/rocq/cost_accounted_rho/theories/`.
- dovetail substrate-agnostic framing correct (constraint is on dovetail's dependencies, not dependents).

### Self-found refinements applied to v2 before round 2 (caller-as-critic, derived from round-1 evidence)

| Finding | Derivation | Resolution |
|---|---|---|
| D7's enumeration premise over-claimed: arrival-order permutation explores NOTHING for multi-bind same-channel joins — the join waits until all binds are satisfiable, then the bind↔datum assignment is hash-pinned given the resting multiset (H-M6's own evidence, `rspace.rs:1211-1233` + `space_matcher.rs:81-105`) | re-derived while restating §4 thm 6 | D7/§5 rescoped: enumeration covers **eager-fire races** (1-bind receive, k contending sends — commits per arrival step); .1.1 gate input changed to the single-bind contention race `{(c?x).{*(x)} \| c!(a) \| c!(b)}`; join-assignment ambiguity membership-gated with the set-coverage residue NAMED and scheduled (M-RHO.3 branch-per-alternative/Lookahead encoding); §4 thm 6 split into a positive coverage lemma + a negative `join_assignment_not_arrival_explorable` |
| Sentinel-channel namespace collision: `@"mtl:out"` collides with a free name var literally named `out` under the `"mtl:<name>"` grounding image | direct inspection of D2 | sentinel channel renamed `@"mtl#out"` — format-disjoint (`#` vs `:`) from the var-grounding image |

## Round 2 (2026-06-12) — fresh independent critics vs contract v2 → host NOT-CONVERGED (resolved in v3); FV critic lost, checks performed inline

- **Critic H2** (host lens): 1 BLOCKER, 3 MAJORs, 3 MINORs → all resolved in v3 (§0-REVISION v3). Its resolutions-verified sweep CONFIRMED every round-1 fix it re-checked (D1/D2/D3 plumbing, D7 mechanics, renderer grammar forms, error surfacing, quiescence-on-return, sequential accumulation, casper seam) — see the v3 contract for the carried citations.
- **Critic F2** (mettail/FV lens): **died at a usage limit after 72 tool calls without delivering a report.** Its load-bearing checks were performed inline by the caller (see below). NOTE: before dying it WROTE four Rocq theories into `formal/rocq/rho_bridge/theories/` + registered them in `_CoqProject` — beyond its review charter; a fifth (`RhoBackendFlipGate.v`) landed minutes later from the continuing parallel session. All assessed below.

### H2 findings → v3 resolutions

| Finding | Evidence (key cites) | Resolution |
|---|---|---|
| B: member #8 (`join_pattern_same_channel`) UNRENDERABLE under D1 — the host normalizer hard-rejects same-channel joins in source; round-1's "consume supports duplicates" was true only BELOW the compiler; nested-receive substitute is non-atomic (unfaithful) | `p_input_normalizer.rs:408-423` (`ReceiveOnSameChannelsError`, normalized-`Par` HashSet check); `cost_accounting_spec.rs:288-296` (expected rejection class) | member #8 → source-text EXCLUDED + parser-boundary regression (user applied this edit directly); §1a PInputs row + §5 + §6 item 2 updated |
| M: v2's "join assignment hash-pinned regardless of π" is FALSE — produce path PREPENDS the arriving datum (index −1) AFTER the hash sort; first bind takes the LAST-ARRIVED datum; and `deterministic_candidate_hash` ingests `random_state` while evaluate draws from `thread_rng` ⇒ resting-candidate selection not even run-deterministic | `rspace.rs:818-825` (`shuffled_data.insert(0, (data, -1))`); `space_matcher.rs:31-66,81-105,140-156`; `rspace.rs:139-145`; `internal.rs:16-20`; `rho_runtime.rs:111`; `blake2b512_random.rs:89-93` | **D7-CORRECTION**: the negative lemma `join_assignment_not_arrival_explorable` KILLED before any Rocq was written (the round-1 vacuous-model disease caught at design time); positive 1-bind lemma retained (each arrival step single-candidate = entropy-independent, critic-verified); "never rely on resting-candidate order" recorded |
| M: sentinel rename `@"mtl#out"` not propagated — §1a′/§2/§3 still shipped the colliding `@"mtl:out"` | contract self-contradiction on a load-bearing constant | propagated everywhere (replace-all) |
| M: D3 fingerprint under-specified vs the real `HotStoreState` — read-through-cache `[]` residue false-REDs nearly every member; 5 maps incl. unconditionally-installed system processes with `ScalaBodyRef` continuations; `condition` field; "sequence numbers" described Scala-shaped fields | `hot_store.rs:85-97,221-231,334,358-382,430`; `rho_runtime.rs:999-1004,1207`; `system_processes.rs:81-139`; `trace/event.rs:97-108` | **D3-PIN**: user `data` + user `continuations` ONLY; DROP-EMPTY; `installed_*`/`joins` excluded; tuple `(patterns, body, persist)` + `condition` asserted-None; `source` dropped wholesale |
| m: `create_soft_checkpoint` not a pure observer (drains event log + produce counter); revert consumes by value | `rspace.rs:283-294,302-320`; `checkpoint.rs:10-15` | recorded in §0-REVISION v3; π-loop clones the post-receive checkpoint |
| m: ν-quotient "first-occurrence order" circular for ≥2 GPrivates (sorting needs the ids being quotiented — graph canonicalization) | direct argument | corpus RESTRICTED to single-ν members; multi-ν = out-of-.1, iso-search quotient recorded |
| m: revert-on-error ⇒ erroring t-run dump = pre-eval state ⇒ false-GREEN on inert-NF members if `errors=∅` ever weakened | `rho_runtime.rs:117-120` | R10 hardened: the assertion is load-bearing, never warn-only |

### Inline FV-lens verification (caller, replacing the dead F2)

| Check | Result |
|---|---|
| Renderer feasibility over the generated AST | VERIFIED — HOL binders generate `Scope<Vec<Binder<String>>, Arc<Proc>>` (`macros/src/gen/types/enums.rs:371-375`; PInputs decl `rholang.rs:77-78`); the generated `Display` already walks it (rholang_tests asserts display strings), so name-recovery machinery exists |
| Ascent gate API | VERIFIED — `normal_forms_reachable_from_seeds(&self, seed_ids: &[u64])` at `runtime/src/language.rs:732` (+ `_iter` :724) |
| Corpus-partition completeness sweep (all eval-asserting rholang tests) | v2 MISSED transport-pure families → corpus EXPANDED to 16 members (+ exec_basic, exec_with_process, par_cong_exec, new_cong, new_congruence_reaches_normal_form, extrusion_reaches_result, extrusion_blocked_when_not_fresh, new_is_normal_when_body_is); fold-dependent exclusions += add_cong (:274), comparison_cong (:280); extrusion + ν-shadowing members align NATIVELY on the host (no Extrude step needed; bound-name shadowing is host-native) |
| Rocq abstraction pattern | VERIFIED — existing theories use Section-local concrete models (`Definition`/`Inductive` over nat keys), zero Parameters (`OracleQuotientEquivalence.v:28-52` pattern) |

### Parallel-session Rocq landing (assessed; kept per no-clobber; NONE discharges the .1 obligations)

| File | Zero-admission | Honest classification |
|---|---|---|
| `CommReductionCorrespondence.v` (280 lines) | ✓ compiles, no Admitted/Axiom/Conjecture | **MONOTONE fact-insertion model with persistent contracts** (premises by membership, never consumed; `insert_exact` only grows) = the M-RHO.2+ rules-as-data saturation layer. NOT .1's linear `Comm` (consumes matched sends + receive). Occupies the §4 keystone filename — the .1 LINEAR model must be added without over-claiming this file (R6) |
| `RhoObservationFingerprint.v` (128) | ✓ | sound exact-key/order-irrelevance comparison kit — reusable as D3's discipline layer |
| `RhoGroundingAndNames.v` (134) | ✓ | sound ν-freshness/no-capture kit — adjacent to (not equal to) `grounding_commutes` |
| `AmbiguityWitnessEnumeration.v` (114) | ✓ | branch-per-alternative witness encoding = the M-RHO.3 mechanism (does NOT model arrival enumeration; notably does NOT contain the killed negative lemma) |
| `RhoBackendFlipGate.v` (69) | ✓ | the M-RHO.4 per-language flip-gate conjunction |

Capped gate re-run after the landing: **GREEN** (`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge`; an initial failure was a race against the mid-write `RhoBackendFlipGate.v`, resolved on completion).

## Round 3 (2026-06-13) — confirmation pass vs contract v3 → CLOSED

The subsequent implementation pass discharged the active M-RHO.1 contract by
adding the separate linear-communication model the round-2 audit required. This
ledger remains a historical adversarial-design record; it is no longer an
active pre-implementation blocker.

Confirmation evidence:

- `LinearCommCorrespondence.v` models the M-RHO.1 one-shot COMM path directly:
  classifier totality and determinism, send/receive consumption, source/target
  soundness and completeness, quote/drop name canonicalization, grounding/COMM
  commutation, one-bind send-arrival coverage, and same-channel join boundary
  theorems.
- `CommReductionCorrespondence.v` remains classified as the monotone
  persistent-contract model for Dovetail/RhoNet saturation and M-RHO.2+ style
  rules-as-data; it is not over-claimed as the M-RHO.1 linear model.
- `RhoObservationFingerprint.v`, `RhoGroundingAndNames.v`,
  `AmbiguityWitnessEnumeration.v`, `AmbiguitySetPreservation.v`, and
  `RhoBackendFlipGate.v` provide the comparison, name, ambiguity, and flip-gate
  side conditions named by the critics.
- Runtime gates now cover source-text COMM oracles, call-by-need observation,
  guarded COMM, the Rho-vs-Ascent scalar oracle, and the codegen flip/deadlock
  gate. Same-channel duplicate receives remain negative at the source-text
  parser boundary and positive only through direct RSpace consume evidence, as
  recorded in the execution contract.

Scope note: all of this is for the Rho-machine replacement path for the CESK
runtime backend. The WPDA parser/recognizer remains active upstream, and Ascent
is legacy for production rewrite execution. It may be consulted only as
temporary transition comparison before deletion from the live production runtime
tree; git history is the archive.

## Round 4 (2026-06-13) — AST-first course correction → CLOSED

The earlier D1 source-text boundary is superseded for generated MeTTaIL
backends. It remains recorded above as the conservative bring-up decision that
exposed the normalizer-invariant and cost-budget risks.

Resolution evidence:

- `rholang-codegen::lower_language_def` now returns `RhoProgram::Ast` with a
  normalized `models::rhoapi::Par` execution artifact and a Rholang-text reader
  annotation.
- Generated backend dispatch consumes opaque `ValidatedRhoProgram`, not raw
  `Par` or unchecked `RhoAstProgram`; the validator is the only codegen path
  that can produce the executable typestate.
- The runtime path uses direct `RhoRuntime::inj(Par, Env<Par>, rand)` after
  installing `Cost::unsafe_max()`, avoiding source parsing while keeping the old
  source path available for hand-authored parser/regression oracles.
- Rust tests inspect the generated AST for persistent contract receives,
  operand-first / return-channel-last ABI, and de Bruijn binding order.
- `run_calculator.rs` and the Rho-vs-Ascent oracle build invocation sends as
  `Par` values and execute through direct AST injection.

The design remains bytecode-ready: future Rholang bytecode should be another
backend artifact variant, not a regression to source text as the execution
boundary.
