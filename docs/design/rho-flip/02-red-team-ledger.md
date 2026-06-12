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
| B: fold-dependent corpus members structurally red under .1 scope; "opaque payload" encoding doesn't exist (no rhoapi image) | F-B4 | `rhocalc_tests.rs:683-694,1033-1040`; `rhocalc.rs:106,635,659,988` | **D6**: exclusion-with-reason; they become the M-RHO.2 acceptance bridge |
| M: single-run vs outcome-set — host COMM selection deliberately deterministic; re-running has no coverage | H-M6 | `rspace.rs:1211-1233` (`deterministic_candidate_hash`), `reduce.rs:279-283` | **D7**: harness-side sequential send-permutation enumeration + `send_permutation_enumeration_covers` lemma |
| M: channel/data double-representation — ContentKey-as-payload kills Exec (no decoder) and breaks data-as-channel rendezvous; `quoted_channel` wraps a GString, not a body | H-M7 | `rspace.rs:338-339,373`; `run.rs:24-31` | **D5**: ≡_N canonicalizer pre-render; ContentKey demoted to comparison SPEC; §4 thm 4 restated as `name_canonicalization_sound_complete` |
| M: classifier type-incoherent (`&GrammarRule` can't see `RewriteRule`/`Equation`); partition model is a restatement, not an extension | F-M5 | `ast/src/language.rs:62-66,167,773`; `lower.rs:124` | §1.0: `RhoRuleRef` disjoint-union input; restatement stated honestly |
| M: auto-generated `Var`/`Lam`/`Apply` constructors unbucketed; `Var` load-bearing in every corpus member | F-M6 | `macros/src/gen/types/enums.rs:112-167`; `rhocalc.rs:1023,1028` | §1a′: term-level disposition table (free Var→σ, bound Var→host, Lam/Apply→Rejected) |
| M: ContentKey keying has no impl path (zero `SemanticHash` impls outside dovetail; codegen-freeze conflict; missing ≡_N canonicalizer; `lower.rs` is string-emitting and rholang-free) | F-M7 | grep; `mettail-rho-codegen/Cargo.toml`; `lower.rs:29-33` | **D1+D5**; renderer placed harness-level (§2 residence), `classify` stays spec-level |
| M: cross-repo Rocq import not wired; "≈95% reuse" misleads | F-M8 | `rho_bridge/_CoqProject`; `MettaOslfLawsConformance.v:24` | **D8**: reuse-by-faithful-re-statement stated; §4 rewritten |
| M: flagship "non-confluent" witness is confluent-up-to-multiset (HashBag body) — exercise vacuous | F-M9 | `rhocalc_tests.rs:171-173`; `rhocalc.rs:72` | §5: order-sensitive join `{(c?x,c?y).{*(x)} \| c!(a) \| c!(b)}` (outcome set `{a,b}`) as the .1.1 gate input, harness-level |
| m: `Send`/`Receive` field omissions (`locally_free`, `connective_used`, host-extension `condition`) | H-m8, H-m11 | `rhoapi.rs:167-179,225-247` | §2 informational block (normalizer-owned under D1; `condition=None` noted) |
| m: `bind_count` = total free-var count, not bind count | H-m9 | `p_input_normalizer.rs:485`; `reduce.rs:1093` | §2 informational block |
| m: B1-b gate seam lives in casper (`acceptance.rs:483-492`), not the accounting module — blast radius understated | H-m10 | `casper/src/rust/util/rholang/acceptance.rs:483-492` | §6 item 4 + R8 name casper; USER-OK gate text updated |
| m: `NegInt` is Int→Int; `CountBag`→Int; congruence count is 82 not ~70; law-kit lines `:120-209` | F-m1,2,3 | `rhocalc.rs:127,659`; `:881-983`; `conformance.rs:7` | §1b/§1d corrected |
| m: dovetail has no `key` feature (dep would be whole-crate) | F-m4 | `dovetail/Cargo.toml` | Moot under D5 (no dovetail dep needed); R3 rewritten |
| m: `mettail-rho-runtime/src/lib.rs` Status section stale | F-m5 | `lib.rs:13-16` vs Cargo.toml | Boyscout fix scheduled in .1.0-L |
| m: §3's "`normal_forms()` → `["p"]`" was a membership assertion misread as a set claim | F-m6 | `rhocalc_tests.rs:44-64` | §3 rewritten on reachable-from-seeds + membership |

### Verified-pass items (claims that survived round 1 — do not re-investigate)
- §1 rule names/line cites all exact (Critic F, full sweep); Comm/PInputs shapes read correctly.
- Same-channel duplicate-bind joins AND k-distinct-channel joins supported by `consume` (`rspace.rs:330-334,652-655`; `space_matcher.rs:81-105`) — `join_pattern_same_channel` → one 2-bind Receive is sound.
- B1-b artifacts real (`resource_logic.rs:120-209,292-293`); `InMemoryStoreManager` no-disk runtime as claimed (`run.rs:50-65`); string-path phlo = `Cost::unsafe_max()` (`rho_runtime.rs:91-94`).
- gxhash LLVM profile scoping verbatim (`mettail-rust/Cargo.toml:72-80`); five rho_bridge theories + claimed contents confirmed; `generate_rho_vm` absence confirmed; CA* capstones exist at `f1r3node-rust/formal/rocq/cost_accounted_rho/theories/`.
- dovetail substrate-agnostic framing correct (constraint is on dovetail's dependencies, not dependents).

### Self-found refinements applied to v2 before round 2 (caller-as-critic, derived from round-1 evidence)

| Finding | Derivation | Resolution |
|---|---|---|
| D7's enumeration premise over-claimed: arrival-order permutation explores NOTHING for multi-bind same-channel joins — the join waits until all binds are satisfiable, then the bind↔datum assignment is hash-pinned given the resting multiset (H-M6's own evidence, `rspace.rs:1211-1233` + `space_matcher.rs:81-105`) | re-derived while restating §4 thm 6 | D7/§5 rescoped: enumeration covers **eager-fire races** (1-bind receive, k contending sends — commits per arrival step); .1.1 gate input changed to the single-bind contention race `{(c?x).{*(x)} \| c!(a) \| c!(b)}`; join-assignment ambiguity membership-gated with the set-coverage residue NAMED and scheduled (M-RHO.3 branch-per-alternative/Lookahead encoding); §4 thm 6 split into a positive coverage lemma + a negative `join_assignment_not_arrival_explorable` |
| Sentinel-channel namespace collision: `@"mtl:out"` collides with a free name var literally named `out` under the `"mtl:<name>"` grounding image | direct inspection of D2 | sentinel channel renamed `@"mtl#out"` — format-disjoint (`#` vs `:`) from the var-grounding image |

## Round 2 (2026-06-12) — fresh independent critics vs contract v2 → PENDING
