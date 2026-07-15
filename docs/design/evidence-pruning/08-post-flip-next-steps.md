# Evidence-Driven Early Pruning — Post-Flip Next Steps

> **Status:** DRAFT for user review (2026-06-16; **re-reviewed 2026-06-17 against the
> Dovetail native-fold refinement**). Converged after 2 red-team rounds. Successor to
> the closed P-series ladder (`02-program-ledger.md`). Refreshes the program against
> the runtime-backend replacement (Ascent+CESK → Dovetail+Rho).
>
> **Verification provenance:** load-bearing code claims confirmed read-only against
> `feature/wfst-architecture` — a4bd (2026-06-16) + 2 red-team rounds (a7e8 DV-1
> soundness, a64e convergence) + native-fold re-review (HEAD `71cdcd68`) + a **third
> refresh (HEAD `75d7c6df`)**. `[VERIFIED]` marks confirmed claims. **The DV-1 STOP
> verdict has now held stable across THREE tree-states** — its core (production
> extraction = constant-zero weight + `collect_checked`, unchanged) is corpus-robust.
>
> **Third-refresh deltas (HEAD `75d7c6df`):** (1) **P6 LANDED** — `c9cea652`/`d62fc454`
> retired the oracle-ascent surface and reconciled docs; the `oracle-ascent` feature is
> gone. ⇒ **the one actionable TR fix is now UNBLOCKED** (§4/§6). (2) The native-fold
> path was generalized into a **language-agnostic numeric-cast adapter** in
> `runtime` (`e61f9e81`→`ac538866`, derived from rule *shape*); DV-0′ measures
> it as the Calculator native-fold path — the STOP is unaffected (still funded +
> idempotent). (3) **Name-collision note:** the walker's `RC-A`/`RC-B` commits
> (`971efeaf`…`316c34e1`: cross-cat cast-comparison pop-site scheduling, `+BalancedCohortGate.v`
> `+ChainAbsorb.v`) are **unrelated** to this plan's RC stage (Rho-coverage) — renamed
> **RHOCOV** below to disambiguate. They touched the realize/cohort path, so TR-0 must
> re-confirm the `all_alts` ghost still reproduces post-`316c34e1`.

## 0a. Verification headlines (what the read-only pass changed)

The verification pass **materially reshaped** this plan. Four facts dominate:

1. **TWO saturating paths now drive the engine `[VERIFIED 2026-06-17, native-fold
   refinement]`** — and *both already carry shipped, proven evidence gates*: (i)
   **Ambient structural AC** via the generated `dovetail_report_for` (plain
   `eg.saturate`, `dovetail_report.rs:725`); (ii) **Calculator native-folds** via
   `saturate_with_native` (`rules.rs:548`), where a `NativeRule` computes one result
   e-class per matched redex and only *adds* `redex == result` (`rules.rs:169-184,
   533-545`). RhoCalc/GuardedRho remain host-routed (no saturation). So the eval-side
   pruning corpus is **{Ambient AC, Calculator native-folds}** — but see headline #6:
   each path's waste is already gated, so the corpus expanding does *not* reopen DV-1.
2. **DV-0's 93–96%/82–84% numbers were measured on a SYNTHETIC arithmetic
   commutativity+expander system, never on Ambient.** The DV-0 caveat comment
   (`rules.rs:558-564`) is now stale/false ("no live caller"). **DV-0′ re-measure
   on Ambient is therefore a genuine gate that can STOP DV-1, not a formality.**
3. **The "ART06 prior-art" claim is RETRACTED `[VERIFIED round-2]`.** An earlier draft
   leaned on `ART06_DemandAnalysis.v` + `compute_demanded_categories` as a reusable
   skeleton. Two problems: (i) `compute_demanded_categories` was **deleted** by HEAD
   `9d889894` (P6 "excise the Ascent engine generator"); (ii) ART06 models
   **category-granularity Datalog demand over a static grammar** — it has *no* model
   of e-graph congruence, gated firing, or the match→fire→merge→rebuild phase ordering
   that is the hard part (§2.3). Its reachability-closure *mathematics* is reusable for
   a label-gate model, but the label gate prunes nothing on Ambient (§2.2), so there is
   no live construction or faithful e-graph proof to inherit. DV-1's model, if ever
   written, is net-new.
4. **Sub-multiset pollution (TR) survives AND multiplies saturation work.** Distinct
   terms are distinct `ContentKey`s, never merged by exact-key dedup, and the seam
   feeds **all parser alternatives into one e-graph as multiple roots** — so each
   ghost root is an extra class the all-classes match scan traverses every round.
   `[VERIFIED: egraph.rs:32-69, key.rs:50-77, report.rs:106-110]`

5. **The DV-1 ROI premise is a measurement artifact; DV-1 is now PREDICTED-STOP.**
   `[RT-soundness a7e8]`: production extraction uses `Extractor::new(&eg, |_|
   TropicalWeight(0.0))` (constant-zero weight, **no `.with_heuristic()`**) and
   `collect_checked()` — the **entire** derivation stream per root
   (`dovetail_report.rs:672-676`). DV-0's "93–96% untouched / extraction touches
   ~14–18 nodes" came from **1-best early stopping** (`kth(·,1)`), which the
   production path does not do. On the production shape the untouched set is only
   "classes not backward-reachable from any root" — a different, likely much smaller
   quantity. So **DV-0′ must re-measure on the production shape, and is expected to
   FAIL the ≥50% gate ⇒ DV-1 STOP.** Separately, the §2.4 model as first scoped was
   **under-specified/vacuous** (`demand_monotone` misses a phase-ordering hazard; the
   sound form is `demand_closed_under_rebuild`, see §2.3) — a green `Print Assumptions`
   would have constrained nothing, the exact vacuity trap the program's own red-team
   history flags (BCG05/R5-8).

6. **Every live saturation seam is ALREADY evidence-gated — and the native-fold gate
   is PROVEN.** `[VERIFIED 2026-06-17]` Ambient AC: canonical-bag dedup
   (`CollectionAcLowering.v::canon_iff_permutation`) + the non-linear `Var` re-bind
   prune (`ac_open_rule_shared_name_constraint_prunes_mismatch`). Native-folds: **funding
   admission** — a fold fires only if funded, a *sound, monotone, proven*
   demand-/admission gate: `DovetailSaturation.v::{fold_transition_funded,
   fold_funding_sound, fold_funding_supply_monotone, fold_funding_rejects_underfunded,
   funded_fold_demand_within_supply}` (Inc 4+5b) — plus `native_refire_is_noop` (folds
   idempotent ⇒ ~1 result e-class per redex, no equivalent-node fan). The funding gate
   IS evidence-driven early pruning, already realized in-engine with a monotonicity
   lemma. Decisive reinforcement of the DV-1 STOP: no large un-gated waste class
   remains on *either* live path for a generic demand gate to capture.

The honest consequence: the eval-side pruning win the ladder hoped to bank is
**already captured by the architecture at every live seam** (parse: P1 + `into_term`;
Ambient AC: canon-dedup + `Var`-prune; native-fold: the proven funding gate), and
the one stage whose gate passed pre-flip (DV-1) is **predicted to STOP on the real
corpus**. This plan is therefore **mostly measure-first gates that are expected to
STOP**, plus **one concrete actionable parser bug** (the `all_alts()` language-trait
shorter-Ambiguous ghost — NOT "ROOT-F", which is already fixed; see §4) — exactly what
the ladder's "residual waste lives in the replaced architecture" prediction implies.
The disciplined deliverable is the *measurements* (which convert prediction to recorded
verdict) and the one parser fix; no eval-side lever is wired before its production-shape
gate clears, and DV-1's model is not written until DV-0′ passes.

## 0. What changed, and why the program's center of gravity moved

The original program (`evidence-driven-early-pruning.md`, `02-staged-implementation-plan.md`)
had three seams: **lex→parse**, **parse frontier**, and **parse→eval**. Two facts
since 2026-06-12 reshape the remaining work:

1. **The parser-frontier ladder is CLOSED** (`d8a09323`, 26 commits). P1 shipped
   (the cross-cat-LHS delegate consumption win: idx4 −47.3% p=1e-45, idx6 35×,
   `PRATTAIL_EP_P1` default On). P2/P3/P5 were **mechanism-derived STOPs** (not
   abandonment — each STOP is a proof that the lever cannot fire on this grammar
   class). P4 kept ESS reporting, STOP'd demotion. These verdicts are properties
   of the **parser**, which is retained unchanged; the backend flip does not
   reopen them.

2. **The parse→eval seam no longer targets Ascent.** The runtime backend is now
   `typed AST → DovetailRunReport → {direct Dovetail | RhoNet → rhoapi::Par →
   RhoRuntime → RSpace}` (`docs/architecture/runtime-backend-spine.md`). Ascent is
   demoted to an oracle-only feature (`languages/oracle-ascent`); CESK is
   being retired (P6). All four target languages were flipped (P5b, 2026-06-16).

The consequence is stated, then measured, in the ladder's closing line:

> *"The program's residual waste classes live in the architecture the Dovetail/Rho
> flip replaces."*

So the next steps are **not** more parser-frontier levers. They are:

- **DV** — the one eval-side stage whose gate **passed**: demand-gated Dovetail
  saturation (magic-sets for the e-graph). Re-measure post-flip, then implement.
- **RC** — a **new** seam the flip creates: Rho-lowering coverage as monotone
  evidence to prune extraction.
- **TR** — an **architectural-triage sweep**: decide, per banked parser residual,
  whether Dovetail dissolves it or it survives as a genuine parser bug.
- **PL** — parser-side leftovers that survive the flip (2L lazy token frontier),
  and a cheap re-confirmation that the P2/P3/P5 STOPs still hold on the
  now-non-vacuous corpus.

## 1. Invariants (unchanged — every stage obeys these or is rejected)

These carry verbatim from the program (`02-staged-implementation-plan.md §1`):

- **I1 — monotone-evidence only.** A stage may avoid/defer/refute an alternative
  only on evidence that is **monotone under continuation** (true now ⇒ true however
  the computation completes). No heuristic/premature disambiguation.
- **I2 — quotients and refutations, never weight-drops.** Removal is either an
  observational-equivalence quotient or a definite refutation. `weight` orders,
  never prunes (`EvidenceComplete.v::weight_is_order_only`,
  `weight_drop_can_lose_valid_alternative` negative fence).
- **I3 — no-loss proof BEFORE wiring.** Each lever ships a zero-admission model
  instantiating the `EvidenceComplete.{no_valid_alternative_dropped,
  evidence_only_removal}` template first; the implementation is a transcription.
- **I4 — measure-first gate.** A "would-apply" measurement on BOTH a pathological
  and a neutral corpus gates every implementation. Below-threshold ⇒ first-class
  STOP, recorded with numbers. No stage is wired on a synthetic-only signal.
- **I5 — every M-commit is zero-admission** (`Print Assumptions` in the message);
  every D/I-commit carries battery results (ledtest SENTINEL first); every
  L-commit carries the pgmcp experiment id + accept/STOP verdict.

The demand-transformation theorem shape these levers share is **query-equivalence**
([BMSU86][BR91]; subsumptive variant [TL11]): the answer set is unchanged, only
irrelevant work is avoided. That is I1+I2 specialized to demand gating.

## 2. DV — Demand-gated Dovetail saturation (the primary next step)

### 2.1 Why this is the live one

DV-0 (2026-06-12) **passed its gate decisively**: 93.1–95.8% of saturated e-nodes
are **untouched** by exact 1-best extraction (gate ≥50%), and saturation is
82.2–84.1% of eval wall-time (gate ≥20%). Mechanism: saturation materializes
hundreds of equivalent e-nodes; exact extraction touches ~14–18.

The caveat was that DV-0 ran when *"dovetail has no live eval caller."* P5b + the
native-fold refinement changed that — but **not the way DV-0 assumed.** `[VERIFIED
2026-06-17]`: there are now **two** live saturating paths — **Ambient structural AC**
(generated `dovetail_report_for`, plain `eg.saturate`, `dovetail_report.rs:725`) and
**Calculator native-folds** (`saturate_with_native`, `rules.rs:548`). RhoCalc/GuardedRho
host-route to RhoRuntime and never saturate. **DV-1's live corpus is therefore
{Ambient AC, Calculator native-folds}** — and DV-0's 93–96%/82–84% numbers came from a
*synthetic* commutativity+expander probe (`rules.rs:649-684`), neither of them. **DV-0′
(re-measure on BOTH live paths) is a real gate that can STOP DV-1**, not a confirmation
step. Two structural reasons it is expected to STOP: (a) Ambient's AC waste is already
gated (§2.2a); (b) native-folds add ~1 result e-class per redex and are funding-gated
+ idempotent (`native_refire_is_noop`), so there is no equivalent-node fan to demand-gate.

### 2.2 Two gate granularities — and why BOTH are predicted co-STOPs on the live corpus

**DV-1-coarse — static label-reachability gate.** Precompute once, from `LanguageDef`,
the operator labels backward-reachable from the root term's labels through the
rule-dependency graph (`lhs_op → rhs_op` edges); fire a rule only if its LHS operator
label is in that closure. It is **merge-invariant** `[VERIFIED round-2]` (union-find
changes child classes, never the distinct-op set of a class — `egraph.rs:350-355`,
`rebuild_exact_indices:450-500`; `collect_matches` keys on the *node's* op, not a
per-class op — `rules.rs:232-241`), so it carries no phase hazard. **But it is
DEAD-ON-ARRIVAL on the only live corpus** `[VERIFIED round-2]`: Ambient's three
reduction rules have LHS operator labels `{PPar, PAmb}` (`dovetail_report.rs:441-493`)
— the *ubiquitous* structural operators of every non-trivial Ambient term. So the
closure contains them for every input and the gate fires every rule on every term: it
prunes **nothing**. Label-granularity demand has no discriminating power precisely
because Ambient's reductions are rooted at its commonest labels. It is therefore **a
predicted co-STOP, not a fallback** — it STOPs for a *different but equally decisive*
reason than the fine gate.

**DV-1-fine — per-e-class demand gate.** Fire a rule on a class only if that class is
in the demanded set (backward closure from extraction roots). More precise — it could
discriminate *which* `PAmb`/`POpen` instances co-reside — but it is entangled with
congruence dynamics (the RT-1 phase hazard, §2.3) and predicted-STOP by RT-6 (§0a #5):
the production untouched-share is "not root-reachable," likely ≪50%.

Both are the magic-sets / demand transformation [BMSU86] specialized to equality
saturation. **DV-0′ measures BOTH would-prune shares**, expecting ≈0% on Ambient for
both. One `[VERIFIED]` implementation constraint if either ever passed: gate the
**match enumeration**, not just the merge — AC rules materialize complement nodes
(`collect_ac_matches`/`add_canonical_bag`, `rules.rs:295-324`), Ambient's dominant
cost; gating only `instantiate`/`merge` would not prune it.

### 2.2a Why the AC lever is ALSO already captured (the STOP is robust, not a gap)

`[VERIFIED round-2]` Steelmanning "is there an AC-specific lever generic demand
misses?" surfaced none that is unshipped. The real AC explosion is complement-node
materialization (`C(n,k)·k!` per `PPar` bag), but it is already **de-amplified by
exact-key dedup**: `add_canonical_bag` sorts children canonically and hits the memo
(`egraph.rs:327-337`), so selections with the same canonical complement multiset
collapse to one node (`CollectionAcLowering.v::canon_iff_permutation`). And the
channel-matching demand ("only enumerate `PAmb(N,·)`/`POpen(N,·)` where the names
co-occur") is exactly the **non-linear `Var` re-bind check that already exists**
(`collect_matches` Var arm, `rules.rs:220-228`; proven by
`ac_open_rule_shared_name_constraint_prunes_mismatch`, `rules.rs:1007`). So the
AC-specific pruning is shipped and proven — its presence is *why* a further demand
gate finds nothing left to prune. This makes the DV STOP **more** robust, not a gap.

**The native-fold path is gated too — by a PROVEN funding admission `[VERIFIED
2026-06-17]`.** `saturate_with_native` fires a `NativeRule` only when the fold is
**funded** (funding/cost admission), and that gate is sound + monotone:
`DovetailSaturation.v::{fold_transition_funded, fold_funding_sound,
fold_funding_supply_monotone, fold_funding_rejects_underfunded,
funded_fold_demand_within_supply}` (Inc 4+5b). Native folds also only *add*
`redex == result` (`native_generated_sound`) and are **idempotent**
(`native_refire_is_noop`/`native_refire_state_unchanged`) ⇒ one result e-class per
redex, no equivalent-node fan. So the native-fold path's waste is bounded *and*
cost-gated by construction; a generic demand gate (DV-1) has nothing left to capture
there either. The funding gate is itself an instance of the program's own principle —
monotone, evidence-driven, early — already realized and proven in the engine.

### 2.3 RT-1 verdict — the fine gate is unsound as first scoped; the sound form

`[RT-soundness a7e8]` **refuted** the naive per-class gate ("fire R on c only if c ∈
demanded; firing R demands the RHS/sub-pattern classes") and gave the exact sound
form. The mechanism of the bug:

- The saturation loop (`rules.rs:493-530`) is **match-all-then-apply per rule**, with
  `rebuild()` (congruence repair) running **after** each rule's merge batch. So
  congruence equalities materialize *after* the firing decisions for that rule.
- Demand created by a congruence merge therefore arrives at **rebuild time**, *after*
  the gate already read demand at **firing time** — a phase-ordering gap. A rule whose
  LHS root is undemanded gets gated out before a merge would have made it demanded.
- Worse, the phrase "demands the RHS/**sub-pattern** classes" most naturally reads as
  the bound-variable classes (what `subst` carries). A rule whose *result* (the minted
  RHS-root class) is itself a redex for a later rule is then gated out, dropping a
  normal form reachable from a *demanded* root via the merge. `demand_monotone`
  ("merges preserve demand") is **necessary but not sufficient** — it does not say
  demand grows *before* the gate reads it.

**Sound form (the three side-conditions the model must encode):**
- **(X1) `demand_closed_under_rebuild`** — demand closure runs *inside* `rebuild`,
  over both congruence-merge sites (the `pending`-seeded merges and the memo-collapse
  merges, `egraph.rs:386-411` / `414-441`), not only at top-level `merge` calls.
- **(X2) RHS-root demand** — a firing of `R: lhs→rhs` at `(root, subst)` demands the
  **canonical class of the instantiated RHS root** `rhs_id` (`rules.rs:506`) and the
  matched `root`, transitively (every class in the instantiated RHS tree, including
  freshly minted intermediate `App`/`AcApp` nodes), not just the bound-variable
  classes.
- **(X3) demand-stratified fixpoint** — `Converged` (`rules.rs:527`, currently
  `iter_merges == 0`) must also require **demand did not grow this iteration**, or the
  loop can stop one iteration before a newly-demanded class fires ([BMSU86 §4]).

The static label-reachability gate (§2.2 coarse) **avoids all of this**: labels are
merge-invariant, so there is no phase hazard and (X1)–(X3) are unnecessary. That is
the decisive argument for measuring the coarse gate first.

### 2.4 FV obligation

**Only written if DV-0′ passes (§2.5) — which is NOT expected on the current corpus.**
Both gates are predicted co-STOPs (§2.2), so no model is expected to be written at all;
this records what it *would* take if a future corpus surprises the measurement:

- **Coarse gate** → `LabelReachabilityGate.v`: *conservativity* + *fixpoint-projection-
  equality*, short because labels are merge-invariant. The reachability *math* can be
  lifted from `ART06_DemandAnalysis.v` (the construction `compute_demanded_categories`
  is deleted, §0a #3), but on Ambient the gate prunes nothing, so this model is moot
  unless a future language's reductions are rooted at *rare* operators.
- **Fine gate** → `SaturationDemandGate.v` with the RT-1-corrected theorems:
  `demand_closed_under_rebuild` (NOT `demand_monotone` — (X1)), `demand_closure_complete`
  strengthened with the RHS-root obligation (X2), `extraction_invariant_under_demand_gate`
  proved **jointly with `CycleCutBoundary.v` / `ExtractionOutcome.v`** over the
  root-reachable subgraph via `gate_preserves_root_reachable_subgraph` (RT-5, §7).

**Vacuity warning `[RT-soundness a7e8, refined 2026-06-17]`:** the Inc 4+5b update to
`DovetailSaturation.v` now DOES model a firing gate — `native_generated` +
`fold_transition_funded` represent native firing *and* the funding admission, and
`native_refire_is_noop` represents idempotence. So an **admission/funding-style** gate
has faithful proof support today. What the model STILL does not represent is the
**e-class congruence/rebuild phase ordering** (state is a fact-set union, `saturate_step`
over `Fact` sets) — which is exactly where the DV-1-*fine* per-class demand gate's RT-1
hazard lives. So: a `SaturationDemandGate.v` for the *fine* gate written against the
current abstraction would still be **vacuous** (it must add the match→fire→merge→rebuild
phase model); a funding-style admission gate would not. This is the single biggest FV
risk for DV-1-fine and the reason it is gated behind both DV-0′ AND a model-faithfulness
review — but it also means the *funding gate* is the precedent to imitate if any eval-side
gate is ever wired.

### 2.5 Stages

- **DV-0′ (re-measure, 1 commit) — THE GATE, expected to STOP DV-1.** Rebuild the
  `dv0_probe` to mirror the **production extraction shape** `[RT a7e8]`: constant-zero
  weight `|_| TropicalWeight(0.0)` and `collect_checked()` (full derivation stream),
  **not** `kth(·,1)` 1-best. Measure **BOTH live saturating paths** `[VERIFIED
  2026-06-17]`: (1) **Ambient structural AC** (`dovetail_report_for` → `eg.saturate`)
  and (2) **Calculator native-folds** (`saturate_with_native`); include the
  host-routed languages for completeness (empty derivation graphs ⇒ DV-1 gates
  nothing). Per path compute two untouched-shares: (i) classes not on any 1-best path
  (the old, inflated number) and (ii) classes not backward-reachable from any root
  under full-stream extraction (the honest number). Gate on (ii) ≥50% AND saturation
  ≥20% of eval wall. **Prediction: FAIL on both ⇒ DV-1 STOP (recorded, first-class)**
  — Ambient because its AC waste is pre-gated (§2.2a), native-folds because they add
  ~1 funded, idempotent result e-class per redex (no fan). Also record the **coarse
  label-reachability** would-prune share so the STOP compares both granularities on
  real data.
  - **✅ DONE — VERDICT: GATE FAILED ⇒ DV-1 STOP (2026-06-17 @ `75d7c6df`).** Production
    untouched-share = **0.0%** on the synthetic worst-case and **5.9–25.0%** (→0 at
    scale) on the Ambient-faithful AC workload — all ≪ 50%. The 1-best measure
    reproduced the inflated 93–99%; the `collect_checked` cross-check == reachable ==
    added confirmed full-stream extraction touches 100% of added nodes. Ambient
    `added(sat)` was tiny (≈1 node/redex), measuring the canon-dedup gate at work. No
    DV-1 model written. Probe `dovetail/src/rules.rs::dv0_probe`; ledger
    `02-program-ledger.md` (EP POST-FLIP DV-0′) + `/tmp/p6_probes/findings.md`.
- **(only if DV-0′ passes) DV-1-M:** the granularity-appropriate model (§2.4) — coarse
  `LabelReachabilityGate.v` strongly preferred; fine `SaturationDemandGate.v` only if
  the coarse gate leaves a large uncaptured win, and only after the vacuity review.
- **DV-1-D / -I / -L:** demand-set instrumentation (shadow) → gate behind
  `DOVETAIL_DEMAND_GATE` (default Off) → Welch panel (saturation wall-time, e-nodes
  built) + **extraction-output byte-equivalence proof-by-test** on the full corpus →
  default On. The byte-equivalence test is the runtime backstop for the RT-1/RT-5
  silent-drop hazard (`assert_complete` does NOT catch it — §7 RT-5).

## 3. RHOCOV (a.k.a. "RC") — Rho-lowering coverage as monotone evidence (new seam)

> **Disambiguation:** this stage's "RC-0/RC-1" mean *Rho-coverage*. It is unrelated to
> the WPDA walker's `RC-A`/`RC-B` commits (`971efeaf`…`316c34e1`, cross-cat
> cast-comparison pop-site scheduling). Different "RC".

### 3.1 The idea

The Rho-native lane lowers a complete Dovetail report to a `RhoNet` plan
**total-or-explicit-reject**: rules the Rho backend cannot express are rejected.
If a rule's coverage status is **statically knowable from `LanguageMetadata`
before extraction** — i.e. "rule R is not Rho-coverable" is decidable without
running the e-graph — then, **when the selected backend is Rho**, a derivation
rooted in (or requiring) an uncoverable rule is provably going to be rejected
downstream. That rejection is monotone evidence (coverage status does not change
mid-extraction), so it can prune such derivations from extraction early instead of
extracting them and rejecting them afterward.

This is the post-flip realization of the original plan's "parse→eval evidence flow:
carry evidence rejections so eval never explores a refuted alternative" — except
the rejecting authority is now the Rho lowering coverage check, not an Ascent guard.

### 3.2 Feasibility — FEASIBLE, but NARROW `[VERIFIED]`

Coverage **is** statically + monotonically knowable: `lower_language_def`
(`rholang-codegen/src/lower.rs:572-611`) partitions every rule of `def.terms`
into `lowered`/`rejected` from `&LanguageDef` alone — no term, no e-graph. The
decision is per-rule, keyed on `(syntax-pattern-shape, operand native kinds, result
native kind, operator)` via `rho_binop`/`rho_unop` (`lower.rs:353-392`,
`category_rho_native_scalar:401-415`). It is backed by the green, zero-admission
`RhoLoweringTotalOrRejects.v` + `RhoRejectedCoverage.v`. So "rule R is uncoverable"
is monotone evidence usable at extraction time.

**But the payoff surface is narrow**, and this is the deciding caveat:

- It is sound **only for the selected Rho backend** (the direct-Dovetail lane —
  Ambient — has no Rho coverage constraint; its "coverage" is the Dovetail structural
  fragment of `GeneratedReportCompiler.v`, a different predicate). The pruning rule
  must be parameterized by the installed backend (`decide_rho_flip`, `flip.rs:56-75`).
- On the **pure scalar-contract path** (Calculator scalars), lowering operates on
  `LanguageDef` and **never builds a per-term e-graph** — so there is no extraction
  to prune. RC has **zero payoff there**.
- RC therefore only bites where a **Rho-backed language also routes terms through a
  Dovetail report** (a native-fold / process path with extraction). Whether any
  current language hits that intersection is itself a measurement (RC-0 below); if
  none does, **RC is a recorded non-goal today** with the design banked for when a
  future language does.

### 3.3 Stages

- **RC-0 (measure, 1 commit):** count, per Rho-backed language, how many extraction
  candidates are rooted in/contain `rejected`-labelled rules (the would-prune set),
  and whether any Rho-backed language routes terms through a Dovetail report at all.
  **Gate:** would-prune share ≥ a threshold on a real corpus → RC-1; else recorded
  non-goal (design banked).
- **RC-1 (only on gate pass):** the backend-parameterized extraction prune. FV:
  `RhoCoverageEvidence.v` — `uncoverable_root_is_rejected_downstream` (composes with
  `RhoLoweringTotalOrRejects.v`), `coverage_status_monotone_at_extraction`,
  `pruning_preserves_covered_extractions` (no covered derivation dropped).

## 4. TR — Architectural-triage sweep of banked parser residuals

The ladder predicted, and DV-0 measured, that residual waste "lives in the
architecture the flip replaces." This stage **decides each banked residual** with
data, per the user's standing triage directive ("don't solve with the current
architecture what the new one dissolves").

| Residual | Where | Verified verdict | Disposition |
|---|---|---|---|
| ROOT-F proper: `{p\|q}`→spurious `{p}` on the primary `Proc::parse` path | realize seam (`sppf_realize.rs` + 5B splice) | **ALREADY FIXED** `[VERIFIED round-2]` @ `38dcd485` ("gated collection forks") + `9fdaed68`, both ancestors of HEAD; rhocalc 126/0 | **Not actionable** — re-fixing a closed bug. Removed from the actionable list. |
| **shorter-Ambiguous prefix-sub-multiset ghost: `{0\|1}` ALSO listed as `{0}` via the LANGUAGE-TRAIT path only** (`parse_{cat}_via_wpda_all` / `all_alts()`); `Proc::parse` clean | **`macros/src/gen/mod.rs`** language-trait emission, consumed at `dovetail_report.rs:415` (`all_alts()`→roots) | **LIVE + the one actionable bug** `[VERIFIED round-2]`. Distinct `ContentKey`s ⇒ extra `EClassId` roots that survive `dovetail_report.rs:430-431` `dedup()` ⇒ each ghost is an extra root the all-classes `search()` traverses (amplifies saturation). `38dcd485`'s own message classifies the prefix-sub-multiset-surviving-EOI as a **token-soundness violation = legal definite kill** | **Parser-side definite kill** at the `all_alts()` emission, instantiating the `EvidenceComplete` definite-refutation template. The `#313` ghost substrate (`ac88faeb`) is the deferred-*enforcement* counterpart — the residual is the enforcement, not new substrate. **✅ UNBLOCKED: P6 landed (`d62fc454`); the `macros/` surface is settled. Rebaseline against HEAD `75d7c6df` first. TR-0 must re-confirm the ghost still reproduces post-`316c34e1` (the RC-A/RC-B realize/cohort changes touched `sppf.rs`/`wpda_walker.rs`).** |
| `{(1) \| 2}` 867k-step subparse spin (13-subparse hang family) | recognizer | Distinct — a recognizer blowup, not a realize-seam ghost | TR-0 re-measure under `PRATTAIL_EP_P1=On`; if P1's parking bounded it, record dissolved; else its own deep-dive |

**Triage principle (evidenced):** exact-key dedup collapses only **observationally-equal**
terms, **never** distinct ones (`key.rs`/`egraph.rs`), and the seam unions all
alternatives into one e-graph as roots — so a genuinely-distinct ghost term **survives
AND multiplies saturation work**. **DV-1 does not rescue it** (the ghost is a
*demanded* top-level root). The earlier draft mislabeled this: ROOT-F proper is fixed;
the live bug is specifically the **`all_alts()` language-trait route**, and the
"shorter-Ambiguous ghost" is not a row to fold into ROOT-F — it *is* the bug. TR-0
reports correctness-pollution vs saturation-cost per residual so nothing is
double-counted; note the would-prune root set here **overlaps RC's** (§3) on Rho-backed
languages — both prune extraction roots, RC by Rho-rejection, TR by token-unsoundness.

## 5. PL — Parser-side leftovers that survive the flip

- **2L — lazy token frontier — ✅ DONE (IMPLEMENTED + ACCEPTED, experiment 69, 2026-06-18).**
  Lazy on-demand lex-node materialization shipped (`runtime_types.rs::expand_lex_node`,
  `wpda_runtime.rs::LazyLatticeTokenSource`, `automata/codegen.rs::lex_dag_lazy`), proven
  lazy ≡ eager (`lazy_lex_equivalence.rs` 7/7), accepted by rigorous pgmcp Welch
  (calc full-parse −4.6% p=5.5e-21 d=2.39; early-failure −72…−79% time + 90–97% fewer
  nodes; rhocalc full-to-EOI +1% caveat). A prior coarse probe STOP'd this as a
  "0.16% non-goal" — that probe measured only the full-parse path and missed the
  early-failure win; experiment 69 refuted it. See `02-program-ledger.md` §2L.
- **STOP re-confirmation (cheap, 1 probe):** P2 (Parikh) and P3 (pre*) STOP'd on the
  pre-ROOT-A corpus. ROOT-A made the comm tests non-vacuous (new token sequences
  reach the recognizer). Re-run the P2 `would_refute` counter and the P3 must-add
  count on the new corpus. Expected: still STOP (the mechanism reasons — "no RuleAt
  at operator positions" for P2; 5.7× must-add for P3 — are structural, not
  corpus-specific). Record the re-measurement so the STOPs are not stale.

## 6. Sequencing, coordination, FV-first

1. **P6 has LANDED (`d62fc454`, HEAD `75d7c6df`).** The earlier coordination
   constraint is RESOLVED: the `macros/` surface is settled and the `all_alts()` TR
   fix is no longer blocked. **Rebaseline all batteries against HEAD `75d7c6df`
   first** (P6 + native-fold + numeric-cast-adapter + RC-A/RC-B all landed).
2. **DV-0′ first** (re-measure on the production shape across BOTH saturating paths;
   the gate, and cheap). Records the predicted STOP for both gate granularities. Then
   DV-1 M→D→I→L *only if it surprisingly passes*.
3. **RHOCOV-0 (RC-0) measure** in parallel with DV (read-only); pursue RC-1 only on pass.
4. **TR-0 measure** in parallel (re-confirm the ghost post-`316c34e1`); then the
   `all_alts()` definite-kill — **now unblocked**, no longer waiting on P6.
5. **PL** last, measure-first.

Every stage is FV-first (I3): model → diagnostic → implementation → ledger, each
behind a default-Off flag until the Welch panel + battery + extraction-equivalence
clear, mirroring the P1 discipline.

## 7. Red-team questions — status

- **RT-1 (the crux) RESOLVED → fine gate REFUTED as first scoped; SOUND under
  (X1)+(X2)+(X3).** `[RT a7e8]`: the per-class gate has a real phase-ordering
  unsoundness (demand read at firing time vs created at rebuild time; "sub-pattern
  classes" drops RHS-root redexes). Fix = `demand_closed_under_rebuild` + RHS-root
  demand + demand-stratified fixpoint (§2.3). The coarse label-reachability gate
  avoids the hazard entirely (merge-invariant), which is why it is measured first.
- **RT-2 RESOLVED → SOUND.** `[RT a7e8]`: roots are fixed at t=0 (built before
  `saturate`, `dovetail_report.rs:650-659`) and merge-stable via `eg.find`; no
  round-0 starvation path. Lemma `demanded_at_seed_nonempty`, no side-condition.
- **RT-3 RESOLVED → feasible-but-narrow.** `[VERIFIED]`: Rho coverage is static,
  per-rule, per-term-shape, monotone (`lower.rs:520-565`, `RhoLoweringTotalOrRejects.v`).
  It is NOT shape-of-extracted-term dependent, so it IS monotone evidence — but only
  for Rho-backed languages routing through a Dovetail report, and never on the scalar
  path. Demoted to RC-0 measure-first (§3.3).
- **RT-4 RESOLVED → no double-count; DV-1 does NOT rescue the ghost; RC↔TR overlap.**
  `[VERIFIED]`: the ghost roots are handed to Dovetail as *demanded* top-level roots, so the DV-1
  demand gate keeps saturating them. The parser-side fix is therefore necessary and
  non-redundant; TR-0 still reports both axes to be safe.
- **RT-5 RESOLVED → SOUND under (Y); danger SUBSUMED by RT-1.** `[RT a7e8]`: the gate
  can only *break* cycles (upgrade `BoundedByCycleCut→Complete`), never create them —
  it only omits e-nodes. BUT the `assert_complete` safety net (`lib.rs:413`) fails
  closed on `BoundedByCycleCut` and is **blind** to an RT-1-induced silent drop (a
  "wrong but Complete" report). So there is no runtime net for the gate's own failure
  mode except the §2.5 byte-equivalence test. `extraction_invariant_under_demand_gate`
  must be proved jointly with `CycleCutBoundary.v` via `gate_preserves_root_reachable_subgraph`.
- **RT-6 RESOLVED → re-measure mandatory AND DV-1 PREDICTED-STOP.** `[RT a7e8]`: the
  93–96% is a 1-best artifact; production uses constant-zero weight + `collect_checked`
  full-stream, so the honest untouched-share is "not root-reachable," likely ≪50%.
  DV-0′ on the production shape is STOP-capable and expected to STOP (§2.5).
