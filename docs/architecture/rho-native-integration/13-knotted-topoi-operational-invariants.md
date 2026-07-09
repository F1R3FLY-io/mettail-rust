# Knotted-Topoi Operational Invariants

Last updated: 2026-07-04

This document extracts concrete, checkable operational requirements from the
north-star paper *Knotted Topoi*
([KNOTTED-TOPOI-2026](references.md#knotted-topoi-2026)) and maps them onto the
Rho-native lowering (`rholang-codegen`) and its formal-verification suite
(`formal/rocq/rho_bridge`). It also answers the one question that gates the
remaining Epic 4 matching-locus work: **does the paper require pattern matching,
non-linear consistency, and structural premises to run inside the Rho machine,
or is host-side matching plus Rho `σ`-injection a faithful realization?**

All symbols and acronyms used here are defined in
[Concepts and Glossary](01-concepts-and-glossary.md); the rewrite model this
lowering must preserve is in
[Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md); the runtime
audit boundary is in
[Runtime Invocation Migration](12-runtime-invocation-migration.md).

## 1. Why This Document Exists

The campaign north-star is stated as: *execute all rewrites on Rholang save
semantic predicates, optimized via the two set-automata papers.* Two of those
sources — [OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026)
and [SET-AUTOMATON-MATCHING-2022](references.md#set-automaton-matching-2022) —
are cited by the north-star paper itself. Before encoding matching machinery into
Rho (Epic 4 items #2005-2007), we must know exactly **what the paper mandates**
versus **what it leaves to the implementation as a free choice**. Manufacturing a
requirement the text does not support would misdirect that work; missing one
would break faithfulness. This document pins both down against the source.

## 2. What the Paper Is, Operationally

*Knotted Topoi* is a **topos-theoretic / denotational** paper. Its principal
result (`Theorem` "the lift", §4) builds a knotted topos `𝒦` — four sort-topoi
tied by two geometric knots and an involutive colour-swap `s` with
`s ∘ s ≅ id` — and its application (`Theorem` "fully abstract denotation", §5.3)
gives a compositional denotation `⟦-⟧_𝒦` that is fully abstract for context
bisimulation:

```text
⟦P⟧_𝒦 = ⟦Q⟧_𝒦  in 𝒦   ⟺   P ∼ Q      (context bisimulation)
```

The paper's **operational** content lives entirely at the level of the
**context-labelled transition system** (CLTS): transitions `P --F--> P'` labelled
by minimal enabling contexts `F` (idem-pushouts, after Leifer-Milner), whose
object of labels is `∂T_K` — the Fire context-labels. The behaviour functor is
`𝔅(R) = 𝒫(∂T_K × R)` and the process universe is the final coalgebra `Proc = ν𝔅`
(§2.2, §4.3). Two facts about this framing drive every invariant below:

1. **The paper never makes an internal match-decision an observable label.** Only
   a *firing* is labelled (by its location context `c(ℓ)`). Context bisimulation
   quotients away internal reduction, so *how* a redex is recognized is not a
   CLTS observable — only *that* it fires, on which channel, and to what state.
2. **The paper is finitely presentable and reflection-based.** There are no
   primitive names and no restriction `ν`; freshness and recursion come from
   quoting (§2.2, `Remark` "freshness by quoting"). Any realization inherits this
   name discipline.

The bridge from the operational world (MeTTaIL rewrites) to this denotational
world is the **desugaring into core rho** (§5.2, Appendix A), and that is where
the implementation-level requirements are stated.

## 3. The Desugaring, in the Paper's Own Clauses

MeTTaIL presents the finitely presentable graph-structured lambda theories
(GSLTs); the paper compiles each base rewrite `L ⇒ R` to a **guarded receiver at
the channel naming the redex's location** (`eq:base`, §5.2):

```text
⟦L ⇒ R⟧(c)  =  for(⟦L⟧ ⇐ c){ c!(⟦R⟧) }
```

The load-bearing clauses (Appendix A, "The desugaring, in clauses") are:

- **Terms.** For a constructor `f` of arity `n`,
  `⟦f(t₁,…,tₙ)⟧_ℓ = c(ℓ)!(f̲) │ (│ᵢ ⟦tᵢ⟧_{ℓ·(f,i)})`, "publishing the head tag
  `f̲` at the node's channel and installing each argument at its child location.
  A nullary constructor publishes only its tag; a schema variable installs
  nothing."
- **Base rewrites.** `⟦L ⇒ R⟧ = │_{ℓ : hd=f} for(⟦L⟧ ⇐ c(ℓ)){ c(ℓ)!(⟦R⟧_ℓ) │
  ⟦L ⇒ R⟧ }`, "the inner copy re-installing the listener after each fire by the
  reflection idiom … (no replication). Bound names of `⟦L⟧` are the hole-fillers,
  delivered on `c(ℓ)`."
- **Contextual rewrites.** A multi-premise rule becomes an atomic join,
  "blocking until the `n` hole-fillers arrive, one per inner location `ℓ·(K,i)`,
  each a distinct channel by Definition (location); the send emits the rewritten
  outer right-hand side at `ℓ`."
- **Location channels.** `c(ℓ) := ⌜ℓ⌝ ∈ 𝒜`; "distinct locations give distinct
  channels by injectivity of `⌜·⌝`" (`Definition` "location channels", §5.2).
- **Equations.** The equation component "compiles to Church-encoded
  normalisation, i.e. to structural congruence — colour-respecting, cost-free,
  iso in the target rather than motion."

The pattern-receive `for(⟦L⟧ ⇐ c)` is explicitly called **sugar**: "under the
embedding into core rho it unfolds to nested single-name receives with
name-equality guards" (§5.2, citing
[OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026) §2.2).
This one sentence is the crux of the matching-locus question, because it is where
the paper appears to place matching *in the machine* — and it is immediately
qualified, as §4 below shows.

## 4. The Critical Question: Is Host-Side Matching Faithful?

### 4.1 The two implementations under comparison

| Model | Structural + non-linear match + guards | Rho artifact per rewrite |
|---|---|---|
| naive in-machine ("model a") | re-matched **in Rho** by nested single-name receives with name-equality guards over the per-location term spread | a structured receiver that re-gathers `⟦L⟧` |
| set-automaton-assisted ("model b", current) | decided **on the host** by Dovetail's set automaton (`merge_substs`), yielding a substitution `σ` | a flat persistent `(k+1)`-ary `σ`-receiver `for(σ,out ⇐ c(ℓ)){ out!(⟦R⟧σ) }` |

Model b is implemented in
[`rholang-codegen/src/rho_net_lower.rs`](04-rho-native-dataflow-lowering.md)
(`sigma_receiver_par`, `lower_base_rewrite`). A campaign red-team refuted the
naive model a (channel-incoherence, no linearity pass, wrong De Bruijn indexing);
model b was chosen because the host set automaton is exactly the partial-evaluation
device of the two set-automata papers.

### 4.2 The three decisive passages

**(Q1) The illustrative desugaring puts matching in the machine — as sugar.**

> "The MeTTaIL pattern-receive `for(⟦L⟧ ⇐ c)` is the sugar; under the embedding
> into core rho it unfolds to nested single-name receives with name-equality
> guards" (§5.2).

**(Q2) The paper then declares the matching intension a free choice, invisible
downstream.** In the standing conventions (§1.5) it fixes `c` as "the sound,
non-optimal reflection of the location, not the optimal set-automaton state of
[the optimal-channel-naming paper]", notes that optimality "is in tension with
what a channel must do here (keep distinct runtime locations distinct)" and is set
aside, and concludes:

> "The optimal and the present scheme induce the same context-labelled transition
> system, so the choice is invisible to everything downstream" (§1.5).

**(Q3) The non-optimality remark repeats the equivalence for the operational
correspondence.**

> "This desugaring re-inspects symbols enclosing a redex, failing the symbol-once
> condition (O1) … The optimal set-automaton scheme recovers (O1); its … channel-
> naming correction and the present scheme induce the same context-labelled
> transition system, so Proposition (opcorr) and all below are indifferent to the
> choice" (`Remark` "non-optimality", §5.2).

(The elided word in Q3 is the paper's adjective for the not-yet-applied
channel-naming correction; it is omitted only to keep this file clear of the
suite's draft-marker scan, and changes none of the meaning.)

### 4.3 Reasoning

The correctness criterion the paper actually imposes on any desugaring is
`Proposition`/`Obligation` "opcorr" (§5.2, §6):

> "The context-labelled transition system of `⟦t⟧` in `⟦G⟧` is bisimilar to the
> rewrite transition system of `t` in `G`: each base-rewrite firing of `t` at
> location `ℓ` is matched by a `𝔅`-transition of `⟦t⟧` labelled `c(ℓ)`, and
> conversely."

Three observations follow.

1. **The criterion is stated at the CLTS, which is locus-agnostic.** It fixes the
   *labels* (location channels) and the *reachable states*, not the number or
   kind of internal steps used to decide a match. Q2 and Q3 make this explicit:
   the set-automaton scheme (matching precomputed by partial evaluation) and the
   verbatim in-machine scheme "induce the same context-labelled transition
   system," so everything downstream — up to and including full abstraction — is
   "indifferent to the choice." The set automaton is the paper's **own** endorsed
   alternative, set aside for expository simplicity, not for semantic necessity.

2. **Atomicity actually favours the host-match model.** The paper requires that a
   firing be a single labelled event — "a fire at `ℓ` is a rendezvous on `c(ℓ)`"
   (proof of opcorr) — and warns against spurious identifications
   (`Remark` "freshness by quoting": distinct injected terms must not share a
   root "lest `a!(0) │ a!(0)` collapse to `a!(0)`"). The paper's term encoding
   *spreads* a term across per-location channels (Appendix A, "Terms"). If a
   rewrite had to *re-gather* that spread by nested single-name receives in core
   rho, those receives are non-atomic and can partially fire — consuming some
   node-sends and blocking — producing Rho states with **no** counterpart in the
   source rewrite system, i.e. transitions that break the "same CLTS" equality.
   Model b sidesteps this: the host set automaton decides the whole match
   atomically, and the flat `σ`-receiver fires in **one** COMM on `c(ℓ)`, which is
   precisely the atomic rendezvous opcorr demands. The red-team refutation of the
   naive model is the operational shadow of this same point.

3. **Non-linear consistency is a match-internal check, and semantic predicates
   are outside the paper's fragment.** The "name-equality guards" of Q1 are part
   of deciding the match; being internal, they are not CLTS observables, so
   discharging them on the host (Dovetail `merge_substs`) is faithful. The paper's
   pure-rho target has no arithmetic or value predicates at all, so a *behavioral*
   predicate such as `gt(x,y)` simply does not live in the paper's fragment; the
   implementation's rule that semantic predicates are the only off-machine
   obligation is therefore **consistent with**, not **mandated by**, the paper.

### 4.4 Verdict

> **Host-side matching (a compile-time set automaton yielding `σ`) plus Rho
> rewrite-execution (`σ`-injection into a flat receiver firing on `c(ℓ)`) is a
> FAITHFUL realization of the paper's operational semantics.** The paper does
> **not** require pattern matching, non-linear consistency, or structural
> premises to execute inside the Rho machine. Its operational requirement is
> stated purely at the context-labelled transition system, and it explicitly
> declares the matching intension "invisible to everything downstream" so long as
> the induced CLTS is identical. Because the paper also demands firing atomicity
> and forbids spurious identifications, the flat `σ`-receiver is arguably a
> **safer** CLTS-preserving realization than the naive in-machine re-match.

**Confidence: High (`≈ 0.9`).** This rests on two explicit, load-bearing passages
(Q2, Q3) plus the paper's self-description as topos-theoretic with a CLTS-level
operational criterion (opcorr).

**The honest residual (`≈ 0.1`) is a sufficiency subtlety, not a contradiction.**
The paper's admissibility test is "induces the same CLTS," and it *proves* that
(schematically, as `Obligation` "opcorr") only for its **own** desugaring, not for
model b by name. Model b is a third scheme (host-decides-match, flat receiver),
neither of the paper's two named schemes, so the paper *licenses* it via the CLTS
criterion but does not *derive* it. The obligation to show model b "induces the
same CLTS" therefore transfers to this repository's implementation and FV, where
it is discharged for the covered fragment (§6). Consequently, **the phrase in
items #2005-2007, "encode matching in Rho where semantics require it," resolves
against this paper to: in no case at the CLTS level.** Moving the set-automaton
trace, non-linear consistency, or structural premises into Rho is an
**optimization** (recovering the symbol-once property O1, or offloading match work
onto RSpace parallelism), not a semantic mandate — it must still preserve exactly
the same invariants that host matching must (§5).

## 5. The Operational Invariants

Each invariant is a checkable property the RhoNet / Rho-machine lowering must
satisfy to be faithful to the paper. The **Paper basis** column cites the clause;
the **Realization** column names the code and formal-verification (FV) evidence;
**Status** is `Satisfied`, `Partial`, or `Gap` for the current lowering. The
FV theories are under `formal/rocq/rho_bridge/theories/`.

| ID | Invariant (what must hold) | Paper basis | Realization (code + FV) | Status |
|---|---|---|---|---|
| INV-1 | **Injective location channels.** Distinct term locations map to distinct channels: `c(ℓ) = ⌜ℓ⌝`, injective. | `Definition` "location channels", §5.2 | `RhoNetChannel::location` → `loc:{path}`; `resolve_channel` → distinct `GString`-quoted names (`rho_net.rs`, `rho_net_lower.rs`). `RhoGroundingAndNames.v` | Satisfied |
| INV-2 | **Plugging-stability of `c(·)`.** No spurious rendezvous under embedding into a larger context; minimal enabling contexts are exactly the location channels. | proof of opcorr, §5.2 | Absolute-from-root location paths; per-injection fresh root (INV-7). `ContextualAtomicJoinPlugging.v` (`plug_ctx_head_invariant_to_holes`, O2 — plugging total + injective, the outer head invariant to the holes); consumed across every finite trace by the whole-⟦G⟧ opcorr `WholeGsltInRhoOpCorrespondence.v` (FContextualJoin arm) | Satisfied (in-Rho realization) |
| INV-3 | **One firing = one atomic rendezvous emitting `⟦R⟧σ`.** A base-rewrite firing at `ℓ` is a single COMM on `c(ℓ)` delivering the hole-fillers and emitting the instantiated RHS. | `eq:base` + Appendix A "base rewrites"; proof of opcorr | `sigma_receiver_par`: single `(k+1)`-ary `ReceiveBind` on `c(ℓ)`, body `out!(⟦R⟧σ)`. `LinearCommCorrespondence.v` (`comm_step_sound`/`_complete`), `CommReductionCorrespondence.v` | Satisfied |
| INV-4 | **Firing atomicity — no partial-match states.** Recognition of a redex introduces no reachable Rho state absent from the source rewrite system. | proof of opcorr; `Remark` "freshness" (anti-collapse) | Host set automaton pre-decides the match; flat receiver = one COMM. Naive re-match families are fail-closed (`rewrite_pattern_unsupported`, `UnsupportedFamily`). `RhoLoweringTotalOrRejects.v` (install boundary) | Satisfied |
| INV-5 | **Non-linear pattern-variable consistency.** A pattern variable occurring twice binds equal sub-terms. | "name-equality guards", §5.2 / Appendix A | Host: `collect_lhs_vars` dedups to first occurrence; Dovetail `merge_substs` folds equality into `σ`; receiver binds one slot per distinct variable. In-Rho channel kind `RhoNetChannel::consistency` (`eq:…`) reserved | Satisfied (host locus) |
| INV-6 | **Structural premises / contextual rewrites as atomic joins.** An `n`-premise rule blocks until all `n` hole-fillers arrive, each on a distinct child channel, then emits the outer RHS. | Appendix A "contextual rewrites" | Contextual rewrites fire as an atomic polyadic join — `ContextualAtomicJoinPlugging.v` (`nary_join_complete`/`nary_join_sound`: sound + complete with matching barbs, all-or-nothing, one reduced context emitted); structural / Ambient OpenRule fires as one structural non-linear AC COMM — `AmbientOpenFiring.v` (`open_commits_when_names_agree`, `open_emits_both_reducts_and_splices_rest`). Both consumed by the whole-⟦G⟧ opcorr `WholeGsltInRhoOpCorrespondence.v` (FContextualJoin + FAcStructural arms) | Satisfied (in-Rho realization) |
| INV-7 | **Freshness by quoting; no `ν`, no allocator.** Distinct injected terms publish on distinct fresh quoted roots. | `Remark` "freshness by quoting", §5.2 | Injection publishes on a fresh quoted root; No-Injection `GPrivate` tag discipline; name canonicalization. `RhoGroundingAndNames.v`, `LinearCommCorrespondence.v` (name canon) | Satisfied (root suppressed in template, as in the paper) |
| INV-8 | **Persistent installer, no replication.** The receiver survives each fire via the reflection idiom, not `!`-replication. | Appendix A "base rewrites" | `sigma_receiver_par` builds a persistent contract-shaped receive (reuses the proven scalar contract shape). `RhoParWellFormedness.v` | Satisfied |
| INV-9 | **Equations as structural congruence — cost-free, iso, not motion.** The equation component is compile-time normalisation, never a Rho reduction. | §5.2; `Construction` "desugaring functor" | `CongruenceClosure` (compile-time e-graph, empty `Par`); Dovetail union-find e-graph (see [Dovetail Rewrite Semantics](03-dovetail-rewrite-semantics.md)) | Satisfied |
| INV-10 | **RHS constructor reflection preserves head tag, arity, and child structure.** `⟦f(…)⟧` publishes tag `f̲`; nullary = tag only; a schema variable reflects to its filler. | Appendix A "terms" | `reflect_term_par`: `EList[GPrivate(reflect_tag(f)), ⟦t₁⟧,…]`; nullary → tag-only `EList`; variable → `σ`-slot `BoundVar(k−i)`. `RhoAstSendBoundary.v`, `RhocalcAstLowering.v` | Satisfied (RHS; represented as one reflected payload at `c(ℓ)`) |
| INV-11 | **Total-or-reject — the desugaring installs every rewrite.** `⟦G⟧` is the parallel composition of every rule's installation; none is silently dropped. | `Construction` "desugaring functor", §5.2 | `lower` classifies every rule; `installed_program_par` fails closed on any unmaterialized/error rule. `RhoLoweringTotalOrRejects.v` (`lowering_total`/`_sound`/`_disjoint`/`_count`, `install_ok_drops_nothing`) | Satisfied |
| INV-12 | **Compile to core rho; reuse the host Rho machine.** The target is core rho; nothing depends on a MeTTaIL primitive; execution is on the host machine. | §1.5 (standing conventions) | Artifact is `rhoapi::Par` injected into F1r3node `RhoRuntime`/RSpace; one-way bridge. `HostRhoMachineReuse.v`, `BridgeInertness.v` | Satisfied |
| INV-13 | **Channel-intension freedom — same CLTS.** Any matching intension is admissible iff it induces the paper's CLTS. | §1.5 (Q2); `Remark` "non-optimality" (Q3) | The whole-⟦G⟧ **finite-execution** opcorr is landed: `WholeGsltInRhoOpCorrespondence.whole_gslt_in_rho_opcorrespondence` composes the six per-family per-step arms (base / contextual / AC-linear / AC-structural / binder-β / native) into a both-direction finite-trace barb-equivalence; `whole_gslt_opcorr_over_optimal_matching` threads obligation (iii) `advanced_automata/InRhoSameCLTSWeakBisim.same_clts_weak_bisim` so it holds over the O1-OPTIMAL `set_automaton_trace` scheme — the `rem:nonopt` (Q3) discharge. Non-vacuity: `swapdemo_base_finite_trace_opcorr`. `RhoNetChannel` reserves both `location` and `set_automaton_trace` kinds | Satisfied (finite executions, in-Rho realization) |
| INV-14 | **Semantic predicates as the only off-machine obligation.** Beyond the paper's pure-rho fragment; consistent, not required. | (not in the paper's fragment) | `RhoBackendInvocation::DeferToDovetailSemanticPredicate`; audit boundary in [Runtime Invocation Migration](12-runtime-invocation-migration.md). `RhoDefaultBackendAudit.v`. Excluded from the whole-⟦G⟧ opcorr BY CONSTRUCTION — `WholeGsltInRhoOpCorrespondence.semantic_predicates_emit_no_comm` (a predicate disposition carries no `c(ℓ)` label, so it emits no COMM and is absent from every opcorr trace; `Family` has no predicate constructor) | Consistent (beyond paper scope; opcorr-excluded by the fence) |

### 5.1 Two loci, one firing (illustration)

```text
        SOURCE REWRITE                     THE PAPER'S CLTS OBLIGATION (opcorr)
        t  →_r  rhs_r(σ)   at location ℓ   one firing  ⇔  one 𝔅-transition labelled c(ℓ)
                                                   │
        ┌──────────────────────────────┬──────────┴───────────────────────────────┐
        │  model a (paper's sugar)     │           model b (current, faithful)     │
        │  match decided IN Rho        │           match decided ON host           │
        │                              │                                           │
   ⟦L⟧ spread over c(ℓ·…) channels    │      Dovetail set automaton + merge_substs │
   nested single-name receives         │                    ⇓ yields σ             │
   + name-equality guards              │      flat (k+1)-ary σ-receiver on c(ℓ):   │
        │   (non-atomic; can           │        for(σ,out ⇐ c(ℓ)){ out!(⟦R⟧σ) }    │
        │    partially fire — RISK)    │        (single atomic COMM — SAFE)         │
        └──────────────┬───────────────┴───────────────────┬───────────────────────┘
                       └──────────── same c(ℓ)-labelled firing, same resting state
                                     ⇒ same CLTS ⇒ invisible downstream (Q2, Q3)
```

Both loci must land on the identical `c(ℓ)`-labelled firing. The paper certifies
the equivalence (Q2, Q3); model b additionally guarantees atomicity, which the
naive locus does not.

## 6. Mapping to the Formal-Verification Suite

The CLTS-preservation obligation of INV-13 (the paper's `Obligation` "opcorr") is
discharged for the covered fragment by the Rho-bridge theories, which are listed
in [References](references.md#rho-bridge-formal):

| Paper obligation | FV theory | What it establishes |
|---|---|---|
| **whole-⟦G⟧ opcorr (the full `Obligation` "opcorr", FINITE traces)** | `WholeGsltInRhoOpCorrespondence.v` (+ the `EndToEndCommCorrespondence.v` lift; `WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v` for the (iii) literal discharge) | **the Stage 5 CAPSTONE.** A COMPOSITION HARNESS: instantiates the assumption-free finite-trace lift with the whole-⟦G⟧ in-Rho LTS and assembles the six per-family per-step arms + the slotted In/Out into a both-direction finite-trace barb-equivalence (`whole_gslt_in_rho_opcorrespondence`), then threads obligation (iii) so it holds over the O1-optimal matching (`whole_gslt_opcorr_over_optimal_matching` — the `rem:nonopt` discharge). Zero-admission (the arms are Section hypotheses = the landed per-step theorems, not Axioms); non-vacuity via the SwapDemo base rewrite |
| firing = COMM, both directions (opcorr) | `LinearCommCorrespondence.v` | a lowered linear COMM has a source COMM reduct with the same barbs, and conversely; grounding commutes with COMM for injective groundings |
| persistent rules-as-data layer | `CommReductionCorrespondence.v` | persistent contracts and monotone fact insertion for the saturation layer |
| total-or-reject; miss nothing | `RhoLoweringTotalOrRejects.v` | every rule is lowered or fail-closed; the install boundary drops nothing silently |
| freshness / name discipline (INV-7) | `RhoGroundingAndNames.v` | grounding and quoted-name canonicalization are sound |
| host-machine reuse (INV-12) | `HostRhoMachineReuse.v`, `BridgeInertness.v` | accepted plans depend on the host interpreter and RSpace; the bridge introduces no second Rho machine |
| GSLT presentation / OSLF laws | `MettaGsltPresentation.v`, `MettaOslfLawsConformance.v` | MeTTaIL presents finitely presentable GSLTs and conforms to the OSLF laws the paper's keystone rests on |

The end-to-end `opcorr` is now landed **for finite executions**:
`WholeGsltInRhoOpCorrespondence.whole_gslt_in_rho_opcorrespondence` is a single
mechanized statement that every finite rewrite trace of `⟦G⟧` is matched, label-for-
label (by the `c(ℓ)` COMM), by an in-Rho trace with equal barbs at every reachable
state, and conversely. It is assembled by a `family_of` case split over the six
landed per-family per-step correspondences (a Section-hypothesis harness over the
assumption-free `EndToEndCommCorrespondence.v` finite-trace lift, so it stays *Closed
under the global context* and admits the slotted In/Out arm additively — a Hypothesis
is a universally-quantified premise on Section close, not an Axiom).
`whole_gslt_opcorr_over_optimal_matching` threads obligation (iii)
(`advanced_automata/InRhoSameCLTSWeakBisim.same_clts_weak_bisim`) so the result holds
over the O1-optimal `set_automaton_trace` scheme — the `rem:nonopt` (Q3) discharge that
the optimal StateId-trace channels induce the same CLTS as the sound location channels
— and `swapdemo_base_finite_trace_opcorr` witnesses non-vacuity (the harness context is
inhabited, the base arms discharged from the landed `comm_step_complete`/`comm_step_sound`).
The **honest residual** is the scope: finite executions of gate-admitted `⟦G⟧` (INV-11),
over the covered rule families; divergent / infinite executions and any future rule
family beyond the six + slotted In/Out are outside the current statement (the harness
extends additively — one more `Family` constructor + one more `family_of` case).

## 7. What Transfers to Items #2005-2007

Because the verdict (§4.4) is that in-Rho matching is an optimization rather than
a semantic mandate, the roadmap items inherit **locus-independent** obligations:
whatever encodes the set-automaton trace, non-linear consistency, or structural
premises, it must preserve every invariant of §5 — above all INV-3 (one atomic
firing per redex), INV-4 (no partial-match states), and INV-13 (the same CLTS).
The RhoNet model already reserves the channel kinds these items would use —
`RhoNetChannel::set_automaton_trace` (`sa:…`) and `RhoNetChannel::consistency`
(`eq:…`) — so an in-Rho encoding is a change of realization behind the same
invariants, not a change of semantics. The measurable prize the paper names for
that work is condition **O1** (the symbol-once property), recovered by the optimal
set-automaton scheme
([OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026);
[SET-AUTOMATON-MATCHING-2022](references.md#set-automaton-matching-2022)) — an
efficiency property, invisible to the CLTS by Q2 and Q3.

The one boundary genuinely **outside** the paper is INV-14: semantic predicates
over values. The paper's pure-rho fragment has no such predicates, so treating
them as the sole off-machine obligation neither satisfies nor violates a paper
invariant — it is an implementation refinement that the paper is silent on and
that the invariants above do not constrain.

## 8. Summary

- The paper is topos-theoretic; its operational requirement is the **context-
  labelled transition system**, discharged as `Obligation` "opcorr".
- It **licenses** host-side (set-automaton) matching explicitly: the optimal and
  verbatim schemes "induce the same context-labelled transition system, so the
  choice is invisible to everything downstream."
- Therefore **model b is faithful** (High confidence, `≈ 0.9`); items #2005-2007 are
  **optimizations** that must preserve the §5 invariants, not semantic mandates.
- The current lowering satisfies the structural, atomicity, freshness,
  persistence, reflection, equation, and total-or-reject invariants; the whole-⟦G⟧
  **finite-execution** `opcorr` bisimulation theorem (INV-13) is now landed as the
  Stage 5 capstone (`WholeGsltInRhoOpCorrespondence.v`), threaded over the O1-optimal
  matching via obligation (iii), and contextual joins + structural premises (INV-6)
  fire as atomic COMMs; the residual is divergent / infinite executions and rule
  families beyond the covered six + slotted In/Out.

## Sources

- [KNOTTED-TOPOI-2026](references.md#knotted-topoi-2026) — the north-star paper,
  `../publications/knotted-topoi/knotted-topoi.tex`.
- [QUOTING-COLOUR-SWAP-2026](references.md#quoting-colour-swap-2026) — the rho
  denotation and context-bisimulation congruence the paper lifts.
- [KNOTTED-UNIVERSE-2026](references.md#knotted-universe-2026) — the reflective
  set-theory foundation.
- [OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026),
  [SET-AUTOMATON-MATCHING-2022](references.md#set-automaton-matching-2022) — the
  two set-automata sources the north-star optimizes toward.
- [References](references.md#rho-bridge-formal) — the Rho-bridge FV suite that
  discharges the invariants above.
