# M-RHO.1 — rhocalc NATIVE FAST PATH (Comm→RSpace COMM; non-confluent witness enumeration)

**Staged, verifiable execution contract** — M/D/I/L discipline (the P-series cadence). Branch `feature/wfst-architecture` @ `d8a09323`. Work item `m-rho-1-rhocalc-native-fast-path` (#281, parent #278, in_progress, prio 7). Opens the Dovetail/Rho flip epic now that the P-series ladder is closed.

> **Status: v2 — post red-team round 1 (2 independent critics, both NOT-CONVERGED on v1; all 9 BLOCKERs + 7 MAJORs resolved by the revisions below). UNDER RED-TEAM ROUND 2 — not yet implementation authority.** Round-1 findings + resolution map: `02-red-team-ledger.md`.

---

## ★ §0-AMENDMENT (2026-06-12, ground-truth correction — supersedes v1's §0 "load-bearing finding" and risk R1)

The original plan was drafted from session data at `a95c5106` (rhocalc_tests 111/15). **Verified at HEAD `d8a09323` (fresh run): `rhocalc_tests` is 126 passed / 0 failed.** ROOT-A (`9fdaed68`), ROOT-F (`38dcd485`), and the eval-layer closure (`f1ea267c`) all landed between the plan's source data and now.

**Consequences:** risk R1 DISSOLVES — no comm family is parser-blocked; no `#[ignore]` fencing. The residual parser-side items are #313 (ghost packings — does not block the comm corpus) and #312 (trace Heisenbug — constrains the verification METHOD, risk R2 stands). Battery reds for baseline accounting: `gen_rhocalc_op` 530/1 (`castbigrat`, pre-existing); `languages/tests/calculator.rs` has timing-sensitive Welch-panel tests that flake under load (not functional).

## ★ §0-REVISION v2 (2026-06-12, post red-team round 1) — the eight forced decisions

Round 1 (host-grounding critic + mettail/FV critic, independent) refuted v1's §2/§3/§4-item-5/§5 mechanisms. Every decision below is derived from the critics' file:line evidence (deep-dive discipline — no implement-and-observe):

- **D1 — Execution path = SOURCE-TEXT through the host compiler** (`evaluate_with_term`), NOT direct-`Par` `inj`. Forced by: `inj` returns no `EvaluateResult` and runs against an `empty_cost()` budget (`rho_runtime.rs:140-145,1268`; the `bootstrap_registry` manual-cost hack `:1244-1252` is the only precedent); hand-assembled Pars must reproduce normalizer invariants — `connective_used=false` on a pattern silently degrades matching to syntactic equality and the COMM **never fires** (`spatial_matcher.rs:178-181`), FreeVar levels are bind-local `0..free_count-1` with dispatcher-order flattening and `(level+shift)-k-1` resolution (`match.rs:22-60`, `dispatch.rs:14-19`, `env.rs:33-47`, `reduce.rs:1090-1094`), binds are pre-sorted at normalization only (`p_input_normalizer.rs:394-395`). The string path makes ALL of that the host normalizer's job (its purpose), is the established M-RHO.0 mechanism (`run_calculator.rs`, `Cost::unsafe_max()` phlo at `rho_runtime.rs:91-94`), and keeps `mettail-rho-codegen` rholang-free as its Cargo.toml advertises. Direct-`Par` assembly is RECORDED-REJECTED for .1 (revisit only at M-RHO.4 if compile-cost demands it, with the full invariant spec).
- **D2 — Free-variable grounding σ** (no free-var convention existed; both paths hard-error: `TopLevelFreeVariablesNotAllowedError` `compiler.rs:106-118`; `eval_var` FreeVar error `reduce.rs:1120-1141`; `evaluate`'s `normalizer_env` is dead in the Rust port — threaded as `_env`, zero consumers under `compiler/normalizer/`). Convention: free **Name** var `c` ⇒ ground channel `@"mtl:c"`; free **Proc** var `p` ⇒ **observation-sentinel send** `@"mtl#out"!("mtl:p")`. The sentinel channel `@"mtl#out"` is **format-disjoint** from the var-grounding image `"mtl:<name>"` (`#` vs `:`), so a free name var literally named `out` cannot collide with it. Applied uniformly at render time to BOTH the source term and the Ascent normal forms before comparison. σ is sound for transport testing: free vars are inert in rhocalc reduction (no rule fires on a bare `Var`), so reduction commutes with σ on the corpus (Rocq lemma `grounding_commutes`, §4); sentinel sends fire only on the disjoint sentinel channel, never perturbing object-channel rendezvous.
- **D3 — Observation = canonicalized RESTING-SPACE fingerprint, gate = membership.** "Read the resting datum from the keyed channel" observed NOTHING for most members (bare-process NFs rest on no channel; the reducer filters process-position exprs to `EVarBody`/`EMethodBody`, `reduce.rs:198-206`). Protocol: evaluate `⟦t⟧σ` AND each `⟦nf_i⟧σ` on fresh in-memory runtimes; observe via the **soft-checkpoint hot-store dump** (`create_soft_checkpoint`, `rho_runtime.rs:152-166`) serialized to a canonical fingerprint; assert `EvaluateResult.errors` empty on every run. **Fingerprint = space CONTENT only**: sorted (channel-`Par`, multiset of data-`Par`s) + (channel-group, multiset of (patterns, body, persist)) entries, ν-quotienting `GPrivate` ids per D5 and **projecting OUT scheduler/provenance metadata** — `ParWithRandom`'s random-state component, produce/consume event refs, sequence numbers — which differ between the `⟦t⟧σ` and `⟦nf_i⟧σ` runs by construction (the two reductions split the Blake2b512Random differently) and are not part of the observable state. **Gate (.1.0): the `⟦t⟧σ` fingerprint equals SOME `⟦nf_i⟧σ` fingerprint** (membership; equality on deterministic members where the NF set is singleton). The proc-var sentinel sends (D2) make variable-valued NFs datum-shaped and discriminating; for ground-inert NFs (e.g. `0`) the discriminator is quiescence itself — an unfired COMM leaves the parked `Receive` (and unconsumed datum) in the dump, so empty-space ⇒ the rendezvous fired.
- **D4 — Ascent side = `normal_forms_reachable_from_seeds([initial])`** (`runtime/src/language.rs:724-735`), NOT raw `normal_forms()` (subterm-polluted: `multi_input_uses_both_vars` has `p`-the-subterm in the raw NF set — set comparisons against it can never be green).
- **D5 — Name identity = ≡_N-canonical RENDERING; ContentKey is the SPEC, never the payload.** v1's "key channels by ContentKey bytes" is unimplementable: RSpace keys channels by the channel `Par` value (`rspace.rs:338-339,373`), `Exec`/`PDrop` requires the body recoverable from the name (opaque key bytes have no rhoapi decoder), and a received datum used as a channel (`comm_with_body_using_channel`) must collide with statically-rendered occurrences of the same name. Realization: a **≡_N canonicalizer** over Name/Proc (exhaustive `QuoteDrop` `@(*(n))→n` / `ExecEq` `*(@(P))→P` cancellation; terminating — each step strictly shrinks the term) applied before rendering, so name-equivalent channels emit byte-identical source ⇒ identical normalized `Par`s ⇒ one RSpace channel. The P4 lesson (R4) is honored as: name identity is **total canonical content** (the host's `ParSortMatcher` sort is content-total) — never insertion order, never a 64-bit hash, never Display-of-uncanonicalized. ν-names (`PNew`): fingerprints quotient `GPrivate` ids by first-occurrence order in the canonical dump (run-to-run and t-vs-nf byte alignment of unforgeables is NOT guaranteed and must not be assumed).
- **D6 — Corpus partition: .1.0 = the TRANSPORT-PURE members only.** The fold-dependent members (`cast_under_send` — needs `IntBinProc` post-transport; `native_ops::bag::remove_comm` — needs `fold_proc`+`RemoveBag`; `native_ops::bag::count_comm` — needs `CountBag`, which moreover lands in category Int) are structurally red under .1's own no-fold scope and have no rhoapi image even as payloads. They are EXCLUDED from the .1.0 oracle with recorded reason (they remain green Ascent tests; they become the M-RHO.2 acceptance bridge). Exact .1.0 corpus in §3.
- **D7 — Witness mechanism inverted-then-fixed: accumulation on a RECEIVE-LESS channel + harness-side sequential enumeration, scoped to EAGER-FIRE races.** v1's "persistent receive on `@witnesses`, drained via `get_data`/`get_joins`" is mechanically backwards: a persistent receive CONSUMES arriving data (nothing rests); `get_joins` returns installed join channel-groups, not data (`rho_runtime.rs:200-202,395-401`); and the `normalize.rs` citation was the wrong layer (persistent receives: `p_input_normalizer.rs:275-281,501`; runtime `reduce.rs:1102`). The host idiom for append-only witness collection is **bare sends to a channel with NO receive** (exactly D2's sentinel sends). Set-coverage: the host's COMM candidate selection is deliberately deterministic (`shuffle_with_index` sorts by `deterministic_candidate_hash` — "A random shuffle can make equally valid matches diverge across validators", `rspace.rs:1211-1233`), so re-running does NOT explore outcomes. The .1.1 harness therefore **enumerates send-arrival orders deterministically**: install the receive part, then evaluate the k producer sends one at a time per permutation π ∈ S_k, collecting the outcome fingerprint per π. **Scope of coverage (derived, honest):** arrival-order enumeration explores exactly the races where a rendezvous fires EAGERLY between arrivals — a 1-bind receive with k contending sends commits to the sole resting datum at each step (π=[a,b] ⇒ x=a; π=[b,a] ⇒ x=b), so the outcome set is covered. A **multi-bind same-channel join** is NOT covered: the join waits until all binds are satisfiable, at which point every contending datum is already resting and the bind↔datum assignment is hash-pinned (`rspace.rs:1211-1233` + the shared per-channel candidate cache, `space_matcher.rs:81-105`) — one outcome per input, regardless of π. Join-assignment ambiguity is therefore **membership-gated only** at .1.x, and full set-coverage for it awaits the ambiguity-preserving ENCODING (branch-per-alternative / Lookahead `x!(P)[n]`) that the plan already defers to M-RHO.3 — recorded as an explicit limit, not silently dropped. Gate (.1.1): on eager-fire race inputs, the enumerated outcome SET ≡ the Ascent reachable-NF set (both sides keyed by D3 fingerprints); on join inputs, membership. The eager-fire coverage claim is a finite Rocq lemma (§4); no claim is made about general schedulers.
- **D8 — Rocq fences carry NO `Conjecture`** (`Conjecture` ≡ `Parameter` ≡ `Axiom` in Rocq — it would fail the zero-Axiom gate the same section imposes). Fences become **statement-only `Definition …_statement : Prop := …`** (defined, never asserted) + comments citing the upstream `CAForceSeparation.v` proof. Cross-repo reuse is **by faithful re-statement** — `rho_bridge/_CoqProject` maps only `-Q theories RhoBridge`; no path to `f1r3node-rust/formal/rocq/cost_accounted_rho` exists, per the bridge's own precedent (`MettaOslfLawsConformance.v:24`).

---

## 0. Frame and scope boundary

**What .1 IS** (per #281 body + design §1.4/§10): rhocalc is itself a ρ-fragment. Its `POutput`/`PInputs`/`PPar`/`PNew`/`PDrop`/`NQuote` map *directly* onto Rholang `Send`/`Receive`/`Par`/`New` — no Milner CBN encoding (that is M-RHO.2, explicitly NOT this stage). The `Comm` rewrite is un-encoded: it IS the host COMM (RSpace produce/consume rendezvous). Parallelism is delegated to `eval_par` (`tokio::spawn` per `P|Q`); MeTTaIL emits `Par`, never forks. Channel identity comes from ≡_N-canonical rendering (D5). First exercise of witness-set parity for non-confluent reduction (D7).

**What .1 is NOT:** the §7 generic CBN/CESK encoding (M-RHO.2); the per-language flip off Ascent (M-RHO.4 — rhocalc goes off-Ascent *only after* op-correspondence proofs, never on the blind oracle alone); the Δ1 N-ary min-cost-matching join (M-RHO.3). The arithmetic/collection `fold` HOL rules (~50 rules + 82 congruence rewrites) are **out of the .1 reduction core** — they are M-RHO.2 HOL-native `Definition` handlers. Per D6, corpus members whose NFs *require* a fold post-transport are excluded from the .1.0 oracle (not "carried as opaque payloads" — non-native constructors have no rhoapi image; the honest boundary is exclusion-with-reason).

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

extending `mettail-rho-codegen/src/lower.rs` (today: `lower_language_def` iterates `def.terms` only, `lower.rs:124`; `RhoLowering { source: String, … }` with a `rejected` partition). The existing `RhoLoweringTotalOrRejects.v` is a *boolean filter* partition (`supported : Rule -> bool`); the 5-way tagged classification is a **new** `classify : Rule -> Class` model over the disjoint union — a restatement, not a verbatim extension (mechanical, but stated honestly). The `LogicBlock` (raw Ascent clauses) classifies `HolNative` wholesale, recorded in the totality claim.

### 1a. Terms (`terms { … }`) — the ρ-process constructors

| Rule (rhocalc.rs:line) | Concrete syntax | Class | .1 disposition / image |
|---|---|---|---|
| `PZero` (:67) | `{}` | **structural** | renders `Nil`. |
| `PPar` (:72) | `{ p \| q \| … }` (HashBag) | **structural** | renders `p \| q \| …`; the ambient `Par`. Maximal parallelism is `eval_par`'s spawn-per-member. NEVER fork host-side. |
| `POutput` (:74) | `n!(q)` | **COMM (send half)** | renders `⟦n⟧!(⟦q⟧)` — linear send. |
| `PInputs` (:77) | `(n1?x1,…,nk?xk).{p}` | **COMM (receive half)** | renders the k-bind join `for(x1 <- ⟦n1⟧ & … & xk <- ⟦nk⟧){ ⟦p⟧ }` — atomic all-or-nothing rendezvous, the host's native polyadic join. Same-channel duplicate binds VERIFIED supported (`rspace.rs:330-334`; per-bind datum removal `space_matcher.rs:81-105`). |
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
| `Proc::Var` / `Name::Var`, **free** | grounding σ (D2): Name var → `@"mtl:<name>"`; Proc var → `@"mtl:out"!("mtl:<name>")`. **Load-bearing: every .1.0 corpus member contains free Vars.** |
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

## 2. THE LOWERING — source-text rendering through the host compiler (D1) + name canonicalization (D5) + grounding (D2)

**Pipeline per corpus term `t`:**

```
t : rhocalc Proc (parsed Term)
  │ 1. ≡_N-canonicalize (QuoteDrop/ExecEq exhaustive cancellation; terminating)
  │ 2. ground free vars σ (Name var → @"mtl:<name>" ; Proc var → @"mtl:out"!("mtl:<name>"))
  │ 3. render to Rholang source (the §1a/§1a′ map; partial over the ρ-core, loud on out-of-fragment)
  ▼
Rholang source ──> evaluate_with_term (host parser+normalizer+reducer; Cost::unsafe_max;
                    the host owns de Bruijn, locally_free, connective_used, bind sorting, Par sorting)
  ▼
EvaluateResult{errors must be ∅} + soft-checkpoint hot-store dump ──> canonical fingerprint (D3/D5)
```

**Renderer residence:** for .1 the rhocalc-Term→Rholang renderer is **harness-level** (a support module under `mettail-rho-runtime/tests/`, the `run_calculator.rs` precedent) — it depends on `mettail-languages`' generated `Proc`/`Name` types, which the spec-level `mettail-rho-codegen` (a `LanguageDef → String` translator, deliberately rholang-free) must not absorb. The spec-driven, per-language term renderer is the M-RHO.4 `generate_rho_vm` codegen concern. `classify_rho_rule` (§1.0) DOES land in `lower.rs` now (it is spec-level).

**Renderer fidelity gate:** the host parser is the checker — malformed renders fail loudly at `inj_attempt`'s build-normalized-term phase; per-member round-trip smokes precede the oracle. Formal renderer-correctness is deferred to the M-RHO.4 codegen proof (recorded, not hidden).

**Rhoapi accuracy notes (for any future Par-direct work; informational under D1):** `Send` also carries `locally_free`/`connective_used`; `Receive` also carries those plus the host-extension `condition: Option<Par>` (where-clause guard, evaluated via `check_commit` on BOTH match paths — `reduce.rs:1059-1064`, `rspace.rs:667-677`, `space_matcher.rs:156-172`); `Receive.bind_count` is the receive's total FREE-VAR count (`p_input_normalizer.rs:485`), used as the body env shift (`reduce.rs:1093`) — numerically equal to the bind count for rhocalc's one-var-per-bind `PInputs`, divergent in general. Under D1 the normalizer owns all of these.

**Channel disjointness invariant (replaces v1's ContentKey-payload claim):** two object channels collide in RSpace **iff** name-equivalent (≡_N). Realized by D5: canonical render ⇒ byte-identical source ⇒ the host's content-total `ParSortMatcher` sort ⇒ one channel `Par`. `ContentKey` remains the comparison-discipline SPEC (exact bytes, never a 64-bit hash, never order) — the fingerprint comparison (D3) satisfies it by construction. Proven as §4 thm 4 (`name_canonicalization_sound_complete`).

---

## 3. THE FIRST VERIFIABLE MILESTONE — M-RHO.1.0

**Milestone: ONE rhocalc reduction — the `Comm` rule — round-trips through `RhoRuntime` with the differential oracle GREEN on the transport-pure comm corpus.**

The smallest end-to-end green, walked concretely:
- **Input:** `{(c?x).{*(x)} | c!(p)}` (`rhocalc_tests::comm::single_channel`). Free `c` (Name), free `p` (Proc).
- **Ascent side:** `normal_forms_reachable_from_seeds([t])` → `{ p }` (singleton on this member).
- **Rho side:** σ-ground + render — `p` in DATA position grounds to the sentinel-send *process*, giving `for(x <- @"mtl:c"){ *x } | @"mtl:c"!({@"mtl:out"!("mtl:p")})`. (A send in data position is quoted data, not executed — the reducer evaluates expressions inside data but does not fire its sends.) Evaluate (in-memory runtime, `Cost::unsafe_max`): COMM fires; `x` binds `@{sentinel-send}`; `*x` runs the sentinel send; datum `"mtl:p"` RESTS at `@"mtl:out"`.
- **Ascent NF image:** `⟦p⟧σ` = the sentinel send alone → evaluates to the same resting datum.
- **Gate:** fingerprint(`⟦t⟧σ`) **= member of** { fingerprint(`⟦nf⟧σ`) } — here singleton equality: datum `"mtl:p"` at `@"mtl:out"`, nothing parked at `@"mtl:c"` (the consumed receive is the COMM-fired evidence). `EvaluateResult.errors = ∅` on every run.

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
| 8 | `comm::join_pattern_same_channel` | `{a \| b}` (multiset-singleton) | duplicate-bind join + sentinel data |
| 9 | `new_parses`-family eval smoke: `new(x) in { x!(0) }` (NF = itself) | resting datum `0` at a `GPrivate` channel | forces the ν-quotient mechanism early |

**Excluded with reason (the M-RHO.2 acceptance bridge):** `cast_under_send` (:1033-1040, fold `IntBinProc`), `native_ops::bag::remove_comm` (:683-688, `fold_proc`+`RemoveBag`), `native_ops::bag::count_comm` (:692-694, `CountBag`→Int). *(Naming note: these were never in `mod comm`; v1's "FULL comm family" phrasing is replaced by this exact-path table.)*

**M/D/I/L for M-RHO.1.0:**
- **M (model, lands first, zero-admission):** the §1.0 `classify` model over the Rule disjoint union (restated `RhoLoweringTotalOrRejects.v` extension or sibling); `CommReductionCorrespondence.v` thms 1–6 + statement-only fences (§4). Axiom-free; NO `Conjecture` vernacular (D8).
- **D (diagnostic):** the `rho_comm_oracle` harness in `mettail-rho-runtime/tests/` reporting per-member `{ascent_nf_fingerprints, rho_fingerprint, member_of?, errors}` before any gate is asserted.
- **I (implement):** ≡_N canonicalizer + σ-grounding + renderer (harness-level); `classify_rho_rule` in `lower.rs`; soft-checkpoint fingerprint reader in `mettail-rho-runtime` (`run.rs` extension beside `get_data`); the oracle gate.
- **L (ledger):** per-member verdicts + the D6 exclusions + any parser-side STOP, program-ledger style; boyscout: fix `mettail-rho-runtime/src/lib.rs`'s stale Status section while in there.

---

## 4. THE Rocq OBLIGATIONS — operational correspondence, funded fragment, up-to-weak-bisim

**File:** `formal/rocq/rho_bridge/theories/CommReductionCorrespondence.v` (new; sixth rho_bridge theory). **Discipline:** Rocq 9.1, zero `Admitted`/`Axiom`/`Assumption`/`Parameter`-as-fact, **and zero `Conjecture`** (≡ Axiom — D8). **Reuse is by faithful re-statement** (the `MettaOslfLawsConformance.v:24` precedent; cross-repo `Require Import` is not wired and stays that way). Schematic over the codegen.

**Scope caveat (binding, from the source plan):** correspondence is **up-to-weak-bisimulation over the funded fragment** — NOT strong bisim (upstream `CAForceSeparation.v` PROVES strong bisim fails at force points), NOT full abstraction.

**The .1 obligation set:**
1. `classify_total` / `classify_buckets_disjoint` — every rule of the disjoint union (terms ∪ equations ∪ rewrites ∪ logic) lands in exactly one `RhoClass` (new model per §1.0; mechanical).
2. `comm_step_sound` — if the lowered image fires a COMM, the source takes the `Comm ~>` step and the post-COMM image is the lowering of the reduct **up to weak barbed equivalence** (abstract `RhoTerm` + `weak_barb` re-statement; fresh-channel names ignored by ≈_b).
3. `comm_step_complete` — funded-fragment completeness: a funded source `Comm` redex (`is_funded` via the verified `delta_sigma` image, `MettaOslfLawsConformance.v`) has a corresponding COMM in the image. Fund-gating is what makes completeness hold.
4. `name_canonicalization_sound_complete` — D5's canonicalizer: `canon(n1) = canon(n2) ⟺ n1 ≡_N n2` (QuoteDrop/ExecEq closure) over the ρ-core Name syntax, plus `canon_terminating`. **This replaces v1's ContentKey-payload theorem** and is cleanly provable over inductive syntax.
5. `grounding_commutes` — D2's σ commutes with `Comm`/`Exec` reduction on the corpus fragment (free vars are inert: no rule fires on a bare `Var`).
6. `send_permutation_enumeration_covers_eager_races` — D7's derived scope: for k contending sends against a **1-bind** receive, enumerating send-arrival permutations covers the rendezvous-outcome set (each step commits to the sole resting datum). Companion negative `join_assignment_not_arrival_explorable` — for a multi-bind same-channel join, all arrival orders reach the same hash-pinned assignment (the recorded .1 limit; finite models, both zero-admission; no general-scheduler claim).
7. **Fences (statement-only, D8):** `Definition strong_bisim_fails_at_force_statement : Prop := …` and `Definition full_abstraction_statement : Prop := …` — defined, never asserted, each with a comment citing the upstream proof/`Conjecture` location in `f1r3node-rust/formal/rocq/cost_accounted_rho/`. A future reader cannot mistake funded weak-bisim for strong bisim, and `Print Assumptions` stays empty.

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
- **Recorded limit (multi-bind same-channel joins):** the bind↔datum assignment of a join that waits for all binds is hash-pinned given the resting multiset — arrival order explores nothing (D7). Those inputs stay **membership-gated**; their full set-coverage requires the ambiguity-preserving branch-per-alternative ENCODING (Lookahead `x!(P)[n]`), already deferred to M-RHO.3. This is an explicit, ledgered limit of .1 — not a silent prune: the Ascent side retains the full set; the rho side demonstrably realizes a member of it.

This realizes ambiguity-set-preservation ("miss nothing" surviving the flip to RSpace) on the eager-fire fragment: every nondeterministic branch is a first-class witness, none pruned; the join-assignment residue is named and scheduled (M-RHO.3), not dropped.

---

## 6. THE VERIFICATION LADDER (per-stage gates; battery untouched)

1. **Axiom-free Rocq.** `CommReductionCorrespondence.v` + the §1.0 classify model compile with zero `Admitted`/`Axiom`/`Assumption`/`Conjecture`; `Print Assumptions` clean; existing five theories stay green. Build via the rho_bridge `CoqMakefile` target (`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rho-bridge`).
2. **Differential oracle (.1.0).** `mettail-rho-runtime/tests/rho_comm_oracle.rs`: the §3 nine-member corpus green under the D3 membership gate. Existing `rho_vs_ascent` + `run_calculator` stay green (no regression to M-RHO.0).
3. **Non-confluent set-parity (.1.1).** The §5 enumeration harness green on the order-sensitive join input.
4. **f1r3node-rust conformance gate.** `mettail_rust_is_not_a_cargo_dependency` (`accounting/resource_logic.rs:292-293`) STAYS PASSING; `BridgeInertness.v` one-way. **B1-b** (promote the `#[cfg(test)]` law kit `resource_logic.rs:120-209` to `pub` + make the gate seam `G`-generic): the gate seam is `admit_by_funding_with_logic` in **`casper/src/rust/util/rholang/acceptance.rs:483-492`** — the deploy-admission path used by consensus block creation, a larger blast radius than v1's "a runtime path" phrasing. **Gated on USER OK with the casper location named.** If declined: keep the re-hosted B1-a kit, record B1-b still-deferred.
5. **Welch.** Expect NEUTRAL (the COMM path is host-owned; MeTTaIL renders text). Panel only if a mettail-side runtime path materially changes; record per the P-series cadence.
6. **Battery sentinel.** `prattail` lib, `gen_calculator_op` 1330/0, `edge_case` 229/0, `gen_rhocalc_op` 530/1 (pre-existing), dovetail 51/0, `ledtest` 220/0, **`rhocalc_tests` 126/0**. **M-RHO.1 changes NO parser codegen and NO `languages/tests` parser tests** (the §5 order-sensitive input lives in the oracle harness).

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
| R9 | **Renderer fidelity** (new): the rhocalc→Rholang printer mis-rendering a member. | Host parser fails loudly (`inj_attempt` normalization); per-member round-trip smokes precede the oracle; formal renderer proof deferred to M-RHO.4 codegen (recorded). |
| R10 | **Observation blind spots** (new): empty-space false-greens on inert-NF members. | D3's discrimination argument: an unfired COMM leaves the parked Receive in the dump; `errors = ∅` asserted; sentinel sends make all variable-valued NFs datum-shaped. |

---

## 8. STAGED EXECUTION SUMMARY (the contract, sequenced)

- **M-RHO.1.0 — single-COMM milestone (keystone).** M: classify model + `CommReductionCorrespondence.v` (thms 1–6, statement-only fences), axiom-free. D: oracle harness diagnostic. I: ≡_N canonicalizer + σ-grounding + renderer (harness-level) + `classify_rho_rule` (`lower.rs`) + soft-checkpoint fingerprint reader (`run.rs`). L: ledger. **Exit:** the §3 nine-member corpus green under the membership gate; `single_channel` round-trips end-to-end.
- **M-RHO.1.1 — witness enumeration (non-confluent parity).** The §5 order-sensitive join input; sequential permutation enumeration; outcome-SET ≡ reachable-NF set. **Exit:** set-parity green; §4 thm 6 compiled.
- **M-RHO.1.2 — conformance/B1-b + ladder close.** Guard green; B1-b user-OK (casper named) or recorded-deferred; Welch (expect NEUTRAL); battery sentinel; ledger verdict.
- **Cross-stage coordinates:** #313, #312 constrain method; neither owned by .1.

**The disciplines, restated:** a parser-side ERR is never an engine-side divergence · verify by outcome-set fingerprints, never action traces · name identity = canonical content, never order · prove only funded weak-bisim · fences are statement-only `Definition`s, never `Conjecture`.
