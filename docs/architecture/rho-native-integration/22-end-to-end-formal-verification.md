# 22 — End-to-End Formal Verification: Operational Correspondence of the In-Rho Compilation

## Abstract

The knotted-topoi program ([KNOTTED-TOPOI-2026](references.md#knotted-topoi-2026))
compiles a **graph-structured lambda theory** (GSLT) — a triple
$`(\text{grammar},\ \text{equations},\ \text{rewrites})`$ presenting a model of
computation — into core Rholang, lowering each base rewrite $`L \Rightarrow R`$ to a
guarded receiver on a channel that names the redex context. This article establishes,
for every install-gate-admitted GSLT $`[\![ G ]\!]`$, that the compiled program is in
**operational correspondence** with the source rewrite system: over every finite
label-indexed execution, the whole-$`[\![ G ]\!]`$ context-labelled transition system
and the source system simulate one another in both directions with equal observations
(barbs), **over the O1-optimal in-Rho matching** rather than a location-keyed baseline.
The binder family is realized natively: $`\beta`$ performs its capture-avoiding
substitution as a de-Bruijn substitution rewriting system that is strongly normalizing
and confluent, with normal form the de-Bruijn reduct $`b[a/0]`$, so the
$`\lambda`$-calculus GSLT reduces directly rather than through an SKI detour.

Every numbered result below is machine-checked and axiom-free: its formal proof depends
on no assumed proposition, no unproven claim, no abstract constant, and no admitted
subgoal (§9). The development spans **37 mechanized theory files** across the
`rho_bridge` and `advanced_automata` libraries ([COQ-ROCQ](references.md#coq-rocq)),
carrying **310 closure certificates** (**161 + 149**, §9.4). Each result closes with a
one-line provenance note citing its mechanized source (branch
`codex/rho-native-set-automata`).

## Scope and related results

This article establishes the correctness results; adjacent questions are treated in the
companion documents, referenced here rather than re-derived:

| Question | Where treated |
|---|---|
| **How** the backend runs (code, channels, data flow, metering) | doc 20 (runtime backend); families in [19](19-in-rho-binder-beta-substitution.md) |
| **Why** the matching is optimal ($`O1`$/$`O2`$/$`O3`$, $`tc(K)`$, the interner as partial evaluator) | doc 21 (optimization theory) |
| **What** is covered (family matrix, corrupted-$`\sigma`$ probes, honest limits) | doc 23 (coverage) |
| Paper-mandate mapping (INV-1..14) | [13](13-knotted-topoi-operational-invariants.md) |
| Per-item paper crosswalk (every labeled KT claim to its mechanized / runtime-tested / denotational-program status) | [29](29-knotted-topoi-satisfaction-crosswalk.md) |
| Shared vocabulary | [01](01-concepts-and-glossary.md) |

The mechanism-level narratives live in the family references (base matching in
[15](15-in-rho-set-automaton-matching.md), AC in
[18](18-in-rho-ac-matching.md), binder-$`\beta`$ in
[19](19-in-rho-binder-beta-substitution.md)); the verification plan those theories
discharge is [16](16-in-rho-verification-plan.md). The present article establishes
correctness.

---

## 1. Introduction

### 1.1 The correctness claim

The knotted-topoi program compiles a GSLT into core Rholang, desugaring each base
rewrite $`L \Rightarrow R`$ into a guarded receiver on a channel that names the redex
context. The paper states correctness as its obligation **`ob:opcorr`**: the compiled
program is in *operational correspondence* with the source rewrite system. This article
establishes that obligation for the landed in-Rho realization, in the strengthened form
the development achieves.

Informally, the main theorem says: *running the compiled program on the f1r3node reducer
reproduces exactly the source rewrites — no source step is lost, no spurious step is
introduced, and each side observes the same resting messages — and this remains true
when the matching COMMs share channels by interned context rather than by physical
location.* Formally:

> **The correctness claim.** For every install-gate-admitted GSLT
> $`[\![ G ]\!]`$, and every finite label-indexed trace, each
> non-semantic-predicate rewrite family **matches and fires fully in-Rho** as one or more
> COMMs on the f1r3node reducer, and the whole-$`[\![ G ]\!]`$ context-labelled
> transition system is in both-direction, barb-preserving operational correspondence
> with the source rewrite system — **over the O1-optimal matching**, not merely a
> location-keyed baseline.

The binder family additionally *reduces* in-Rho: $`\beta`$ performs its capture-avoiding
substitution as a metered de-Bruijn substitution cascade (§6), so the
$`\lambda`$-calculus GSLT is realized directly rather than through an SKI detour.

### 1.2 The setting: the context-labelled transition system

Correctness is fixed at the level of a **context-labelled transition system (CLTS)**
(§2): a labelled transition system whose visible labels are the context-named COMM events
$`c(\ell)`$ the compiler emits, and whose observations are **barbs** (resting sends). Two
principles govern the article.

1. **Each obligation is a theorem with a proof.** Every numbered assertion below states a
   proposition and proves it; the propositions are exactly those the verification plan
   [16](16-in-rho-verification-plan.md) factors the capstone into.
2. **Each proof is complete and axiom-free.** No proof appeals to an assumed proposition,
   an unproven claim, an abstract constant, or an admitted subgoal — equivalently, each
   proof is closed under the ambient logic. The universally-quantified hypotheses of the
   composition theorems are *premises*, discharged at concrete instances (§9.3), not
   `Axiom`s. This certification is stated once, globally, in §9, rather than repeated per
   result.

### 1.3 Contributions and roadmap

This article contributes:

- a characterization of the in-Rho set-automaton match as exactly the positional matching
  relation, under the symbol-once condition $`O1`$, with the interned channel name
  $`tc(K)`$ shown to be the sound $`O1`$/$`O3`$ quotient (§3);
- a weak bisimulation between the location-keyed (sound) and $`tc(K)`$-keyed (optimal)
  matching schemes, proving that channel sharing changes nothing observable (§4);
- seven per-family step correspondences, each a barb-preserving simulation exhibiting a
  source rewrite as one or more COMMs (§5);
- a strong-normalization and confluence analysis of the de-Bruijn substitution rewriting
  system realizing $`\beta`$, identifying its unique normal form with $`b[a/0]`$ (§6);
- and the finite-trace capstone assembling these into whole-$`[\![ G ]\!]`$ operational
  correspondence, first over the sound baseline and then, by transitive composition, over
  the O1-optimal matching (§7).

The remaining sections develop these in order; §8 exhibits the logical dependency spine
threading them together; §9 records the mechanization and rigor; §10 delimits the scope.

---

## 2. Notation, preliminaries, and proof obligations

Every symbol, acronym, and term is defined here before first use. Terms marked **(01)**
are shared with the concepts glossary [01](01-concepts-and-glossary.md); they are recalled
here so the article reads stand-alone. Where a definition is realized by a mechanized
construct, that construct is named in a trailing parenthetical — it is a pointer, not the
definition.

**Definition 2.1 (LTS (01)).** A *labelled transition system* is a triple
$`(S, A, {\to})`$ with $`{\to}\subseteq S\times A\times S`$; write
$`s\xrightarrow{a}s'`$ for $`(s,a,s')\in{\to}`$.

**Definition 2.2 (observation, barb).** An LTS is *observed* by a map
$`\mathrm{barb}:S\to\mathrm{Obs}`$, where $`\mathrm{barb}(s)`$ is the multiset of resting
sends on the output channels of the configuration $`s`$. Write $`s\!\downarrow`$ for
$`\mathrm{barb}(s)`$ (mechanized as `gbarb`, e.g. `rho_outputs` / `source_outputs`).

**Definition 2.3 (COMM (01)).** A *COMM* is one RSpace communication — a send
rendezvousing with a receive — the atomic reduction event of the Rho machine
([RHO-2005](references.md#rho-2005)).

**Definition 2.4 (CLTS).** A *context-labelled transition system* is an observed LTS
whose visible labels are the context-named COMM events $`c(\ell)`$ a GSLT rewrite lowers
to. The correctness statements range over CLTS traces.

**Definition 2.5 ($`\tau`$, visible, weak-visible).** A designated label $`\tau\in A`$ is
*silent* (internal, unobservable): the matching COMMs (`sa:` inspection, `eq:`
consistency, `loc:` spine descent) and every substitution-cascade COMM are $`\tau`$; only
the accept-send $`c(\ell)`$ is *visible*. A *weak-visible* transition bundles a silent
prefix and suffix around one visible step,
```math
s \overset{c(\ell)}{\Longrightarrow} s' \quad:\Longleftrightarrow\quad s \;\xrightarrow{\tau}{}^{*}\;\cdot\; \xrightarrow{c(\ell)}\;\cdot\;\xrightarrow{\tau}{}^{*}\; s',
```
realized as `gstep` (capstone, §7), `weak_step` (§4), and `cwvis` (§6).

**Definition 2.6 (weak bisimulation $`\approx`$).** A relation
$`R\subseteq S_1\times S_2`$ is a *weak bisimulation* iff for all $`(s,t)\in R`$: (i)
$`s\!\downarrow=t\!\downarrow`$; (ii)
$`s\xrightarrow{a}s'\Rightarrow\exists t'.\ t\overset{a}{\Longrightarrow}t'\wedge(s',t')\in R`$;
and (iii) the symmetric clause. Then
$`s\approx t`$ iff some weak bisimulation relates them; it equates systems up to $`\tau`$
activity. (In the mechanization the $`\tau`$-bundling is baked into the transition
relations `gstep` / `weak_step` / `cwvis`, so `is_weak_bisimulation R` verifies the two
transfer squares (ii)+(iii) together with the barb equality (i) on those weak-visible
relations.)

**Definition 2.7 (finite label-indexed trace).** For a fixed LTS, the finite multi-step
relation $`\mathrm{steps}\subseteq S\times A^{*}\times S`$ is defined inductively by
```math
\dfrac{}{\ \mathrm{steps}\ s\ \varepsilon\ s\ }\qquad
\dfrac{\ s\xrightarrow{l}s'\quad \mathrm{steps}\ s'\ \mathit{ls}\ s''\ }{\ \mathrm{steps}\ s\ (l\!:\!\mathit{ls})\ s''\ }
```
so $`\mathrm{steps}\ s\ \mathit{ls}\ s'`$ is the reflexive–transitive closure of
$`\to`$ that additionally records the label word $`\mathit{ls}\in A^{*}`$. Write it
$`s\xrightarrow{\mathit{ls}}{}^{*}s'`$ (mechanized as `steps`,
`EndToEndCommCorrespondence.v` (`:53`), with constructors `steps_nil` and `steps_cons`).

**Definition 2.8 (operational correspondence).** Two observed LTSs related by $`R`$ are
in *finite-trace, barb-preserving operational correspondence* iff for every
$`(s,t)\in R`$ and every label word $`\mathit{ls}`$, each $`R`$-side trace over
$`\mathit{ls}`$ is matched by an $`\mathit{ls}`$-trace on the other side ending in an
$`R`$-related, barb-equal state, and conversely. This is the finite-execution form of
`ob:opcorr`.

**Definition 2.9 (sound scheme, optimal scheme).** Two channel-naming maps for the
matching COMMs. The **sound** map keys a channel by the runtime **location** $`\ell`$
(`sound_key`, the model-b baseline). The **optimal** map keys it by the interned
**StateId trace** $`tc(K)=\ulcorner\delta^{*}(s_0,\ \mathrm{surface}(K))\urcorner`$ of
the locate automaton on the surface of the matched context $`K`$ (`optimal_key`;
condition $`O1`$, symbol-once; see doc 21 and
[OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026)).

**Further vocabulary.** A **premise (hypothesis)** is an antecedent of a result: every
theorem below has the form
$`\forall(\text{premises}).\ \text{premises}\Rightarrow\text{conclusion}`$; a premise is discharged where the theorem is applied, never assumed
globally — it is not an `Axiom` (§9.3; mechanized by Section-generalized `Variable` /
`Hypothesis` declarations). A result is **machine-checked / axiom-free** when its formal
proof depends on no assumed proposition, no admitted subgoal, and no abstract constant
(§9). We abbreviate **strong normalization** (no infinite reduction) as SN,
**confluence** (Church–Rosser: a common reduct exists) as CR, and **normal form** (an
irreducible term) as NF; SN $`+`$ CR give a **unique** NF. The de-Bruijn $`\beta`$-reduct
$`b[a/0]`$ substitutes argument $`a`$ for index $`0`$ in the scope body $`b`$
([DEBRUIJN-1972](references.md#debruijn-1972)). The reflected/lowered image of a source
term or configuration $`t`$ is written $`[\![ t ]\!]`$ (an `rhoapi::Par`, or its
abstraction `lower_state`). The **GSLT** is the knotted-topoi *graph-structured lambda
theory* being compiled; see [13](13-knotted-topoi-operational-invariants.md).

**Object-language constructors.** Where an object term appears in a formula it is typeset
as an operator: $`\mathtt{app}\,op\,\mathit{args}`$ and $`\mathtt{var}`$ for patterns;
$`\mathtt{lam}\,b`$, $`\mathtt{node}\,op\,[t_1,\dots,t_m]`$, $`\mathtt{bound}\,n`$,
$`\mathtt{free}\,x`$, $`\mathtt{shift}\,c\,t`$, $`\mathtt{shiftk}\,k\,a`$, and
$`\mathtt{subst}\,j\,a\,t`$ for the substitution terms of §6.

**The ten obligations.** The verification plan [16](16-in-rho-verification-plan.md)
factors the capstone into ten obligations, cited by roman numeral throughout and drawn
together in §8:

| # | Obligation | Established in (§) |
|---|---|---|
| (i) | in-Rho match $`=`$ positional relation | `InRhoMatchPositional` (§3, T1) |
| (ii) | $`O1`$ symbol-once / chain totality | `SymbolOnceInjective` (§3, T2) |
| (iii) | sound $`\equiv`$ optimal CLTS (the `rem:nonopt` discharge) | `InRhoSameCLTSWeakBisim` (§4, T6) |
| (iv) | atomic firing, no partial match | `AtomicFiringNoPartialMatch` (§5, T10) |
| (v) | whole-$`[\![ G ]\!]`$ finite-trace opcorr | `WholeGsltInRhoOpCorrespondence` (§7, T22/T23) |
| (vi) | non-linear equality consistency | `NonLinearEqConsistency` (§5, T9) |
| (vii) | contextual atomic join + plugging | `ContextualAtomicJoinPlugging` (§5, T8) |
| (viii) | $`tc(K)`$ no cross-talk | `TcChannelNamingQuotient` (§3, T3) |
| (ix) | install gate total-or-reject | `InRhoEncoderTotalOrReject` (§7.3) |
| (x) | reuse determinism ($`\tau`$-prefix) | `InRhoReuseDeterminism` (§3, T4) |

---

## 3. The matching relation (T1–T5)

The matching layer proves that the in-Rho set automaton decides **exactly** the positional
matching relation, that it does so under condition $`O1`$ (each subject symbol inspected
once), that the optimal channel name $`tc(K)`$ is the sound $`O1`$/$`O3`$ quotient, that
reuse is deterministic, and that AC matching decides the sub-multiset relation. These are
match-logic characterizations; §7.4 records precisely how they enter the capstone (as
`gstep` well-formedness and as premises of obligation (iii)), not as independent
step-correspondence arms.

**Proposition 1 (in-Rho match is the positional relation — obligation (i)).**
For every pattern $`p`$ and arity $`n`$, if $`p`$ is an M1 pattern and its arity is
consistent with $`n`$, then the linear `sa:`-chain the automaton emits accepts exactly
when the recursive positional oracle matches:
```math
\forall p,n.\ \ \mathrm{m1}(p)\ \wedge\ \mathrm{arity\text{-}consistent}(p,n)\ \Longrightarrow\ \mathrm{sa\_accept}(p,n)=\mathrm{pmatch\_M1}(p,n).
```

*Proof.* By Boolean extensionality the equality of the two acceptance predicates splits
into two implications. **Soundness**: unfold the M1 acceptance through the head-operator
match and the leaf fold; each argument is a $`\mathtt{var}`$ leaf, which matches any
subterm, so acceptance reduces to agreement of operator and arity. **Completeness** is
the converse fold. The children-fold that yields the positional substitution $`\sigma`$
is the reusable `children_match` idiom, reinstantiated at the general recursion for the
M2 nested case. The hypothesis $`\mathrm{arity\text{-}consistent}(p,n)`$ is a premise —
the serializer realizes arity structurally, as the count of emitted for-receives — and
is justified by the host positional soundness `index_never_drops_match`. $`\blacksquare`$

*Mechanization.* `InRhoMatchPositional.v` — `sa_matches_positional` (`:142`), via
`sa_accept_sound` / `sa_accept_complete`, `children_match` (`:320`).

**Lemma 2 ($`O1`$ symbol-once — obligation (ii)).**
The automaton visits each surface position exactly once and gives distinct positions
distinct channels:
```math
|\mathrm{positions}(\mathtt{app}\,op\,\mathit{args})| = 1+|\mathit{args}|,\qquad
\mathrm{NoDup}\big(\mathrm{map}\,(\mathrm{chan}\ \mathit{site}\ op)\ (\mathrm{positions}(\mathtt{app}\,op\,\mathit{args}))\big).
```

*Proof.* By definition $`\mathrm{positions}=[\,]::\mathrm{map}\,(\lambda i.[i])\,(0..|\mathit{args}|-1)`$
— the root Dewey address plus one address per argument — so the count is $`1+|\mathit{args}|`$
by the length of a map over a range. For distinctness, the root channel lies in a
different summand of the channel coproduct than every child channel, and the child index
$`i\mapsto[i]`$ is injective; a mapped list of a duplicate-free list under an injection is
duplicate-free. This is the $`O1`$ totality consumed by Theorem 6. $`\blacksquare`$

*Mechanization.* `SymbolOnceInjective.v` — `positions_count` (`:71`),
`chan_injective_on_positions` (`:101`).

**Proposition 3 ($`tc(K)`$ is the $`O1`$/$`O3`$ quotient — obligation (viii)).**
The interned trace channel is **sound** ($`O3`$: sharing a channel forces
$`R`$-op-equivalent contexts) and **injective on the quotient** ($`O1`$:
$`R`$-op-equivalent contexts share the channel), and the naive head channel
$`@\mathrm{hd}(K)`$ fails $`O3`$:
```math
\mathrm{m1}(K)\wedge\mathrm{m1}(K')\wedge \mathrm{trace}(K)=\mathrm{trace}(K')\ \Longrightarrow\ K\equiv_{\mathrm{op}}K',
```
its converse, and $`\exists K,K'.\ \mathrm{tc\_hd}(K)=\mathrm{tc\_hd}(K')\ \wedge\ \neg\,(K\equiv_{\mathrm{op}}K')`$.

*Proof.* Both $`K,K'`$ M1 means each is an application over leaves, so $`\mathrm{trace}`$
collapses to the pair $`(\mathrm{op},\mathrm{arity})`$; equating traces forces equal
operator and arity, whence $`K\equiv_{\mathrm{op}}K'`$ by reflexivity of numeric equality,
and the converse runs the equalities backward. For unsoundness of the head channel,
$`\mathtt{app}\,0\,[\mathtt{var}]`$ and $`\mathtt{app}\,0\,[\mathtt{var};\mathtt{var}]`$
share a head but differ in arity, so $`@\mathrm{hd}(K)`$ collapses two distinct rules.
Forward and converse assemble into the quotient equivalence. $`\blacksquare`$

*Mechanization.* `TcChannelNamingQuotient.v` — `tc_sound` (`:63`), `tc_injective`
(`:75`), `hd_violates_O3` (`:98`), assembled as `tc_is_the_op_quotient`.

**Lemma 4 (reuse determinism — obligation (x)).**
The interned-DAG reuse verdict is a deterministic function of the subject node:
```math
\forall p,n_1,n_2.\ \ \mathrm{verdict}(p,n_1)\wedge\mathrm{verdict}(p,n_2)\ \Longrightarrow\ n_1=n_2,
```
and likewise for the reuse-dispatched verdict.

*Proof.* The reuse table sends a node's $`(\mathrm{op},\mathrm{arity})`$ index to a single
interned StateId, so two verdicts for one node are equal by rewriting through the
deterministic dispatch. This makes the $`\tau`$-prefix of a `gstep` deterministic — the
well-formedness role (x) of §7.4. $`\blacksquare`$

*Mechanization.* `InRhoReuseDeterminism.v` — `inrho_verdict_per_node_deterministic`
(`:35`), `inrho_reuse_dispatched_deterministic` (`:48`).

**Proposition 5 (in-Rho AC match is the multiset relation).**
The native sub-multiset consume decides exactly the order-independent partition relation:
a selection matches a bag iff a complementary remainder partitions it:
```math
\forall\,\mathit{sel},\mathit{bag}.\ \ \mathit{sel}\sqsubseteq_{\mathrm{ms}}\mathit{bag}\ \Longleftrightarrow\ \exists\,\mathit{rest}.\ (\mathit{sel}\,\mathbin{+\!\!+}\,\mathit{rest})\sim\mathit{bag},
```
where $`\sim`$ is multiset equality (permutation).

*Proof.* **Forward**: take $`\mathit{rest}:=\mathit{bag}\setminus\mathit{sel}`$ and show
it partitions the bag. **Backward**: induct on $`\mathit{sel}`$, peeling the head pick off
both the permutation witness (one-element removal preserves permutation) and the bag, so
order is immaterial. This AC primitive is reused per level by the structural and nested AC
firing (§5, Proposition 15). $`\blacksquare`$

*Mechanization.* `InRhoAcMatchMultiset.v` — `ac_match_iff_partition` (`:55`), via
`selection_rest_partition` and `partition_sub_multiset`.

---

## 4. Soundness of channel sharing: sound $`\equiv`$ optimal (T6)

The optimal channel scheme *shares* a channel across every occurrence of the same context,
where the sound scheme *separates* by location. The paper asserts, without proof, that this
sharing changes nothing observable. Theorem 6 discharges that assertion — the load-bearing
obligation (iii) — by exhibiting a weak bisimulation between the two schemes' CLTSs.

**Theorem 6 (sound and optimal induce the same CLTS — obligation (iii)).**
The location-keyed (sound) and $`tc(K)`$-keyed (optimal) in-Rho matching schemes induce
the same CLTS. This is three facts.

*(A) Equal visible schedule under $`\tau`$-erasure.* For every firing order,
```math
\mathrm{erase}\big(\mathrm{sched}\ \mathrm{opt\_ch}\ \mathit{order}\big)=\mathrm{erase}\big(\mathrm{sched}\ \mathrm{sound\_ch}\ \mathit{order}\big).
```
*(B) Weak bisimulation.* With the fired-set relation
$`R\,f_o\,f_s:\Longleftrightarrow \forall r.\ (r\in f_o\Leftrightarrow r\in f_s)`$, the
relation $`R`$ is a weak bisimulation between the two `weak_step` systems keyed by
`optimal_key` and by `sound_key`.
*(C) Non-vacuity.* There exist two redexes sharing an optimal channel yet separated by
the sound scheme.

*Proof.* **The $`\tau`$-erasure argument for (A).** Model a firing as a schedule of match
events; the observation map sends every reservation, `sa:` inspection, `eq:` check, and
`loc:` context-descent to the empty observation, and only $`\mathtt{Fire}`$ and
$`\mathtt{Complete}`$ to a visible one. Because $`\mathrm{erase}`$ is a monoid
homomorphism on schedule concatenation, one computes, **independently of the channel
payload type**,
```math
\mathrm{erase}\big(\mathrm{sched}\ \mathrm{ch}\ \mathit{order}\big)=\mathrm{map}\ \mathtt{ObsFire}\ \mathit{order}\ \mathbin{+\!\!+}\ [\mathtt{ObsComplete}].
```
The right-hand side does not mention $`\mathrm{ch}`$, so instantiating at $`\mathrm{opt\_ch}`$
and $`\mathrm{sound\_ch}`$ gives (A) by reflexivity. The contextual analogue holds too: the
`loc:` spine-descent events also erase to nothing, so the discharge survives the contextual
$`\tau`$.

**The bisimulation construction for (B).** The `weak_step` relation has two rules: a *fire*
rule $`f\xrightarrow{\mathtt{ObsFire}\,r}(r\!::\!f)`$, enabled when $`r`$ is a redex,
$`r\notin f`$, the chain is complete, and there is no cross-talk on $`r`$'s key; and a
*complete* rule $`f\xrightarrow{\mathtt{ObsComplete}}f`$ when all redexes are fired. The
relation $`R`$ equates configurations with equal fired sets. Verify the two transfer
squares.

- *Forward (an optimal fire is matched on the sound side).* Invert the optimal transition.
  For a *fire* of $`r`$, exhibit the sound fire of the same $`r`$, re-establishing its two
  side conditions on the sound scheme: **chain totality** from `positions_count` (Lemma 2)
  and **no cross-talk** from the location injectivity `site_inj`. The membership premise
  $`r\notin f_s`$ transfers across $`R`$, and appending $`r`$ to both sides preserves equal
  fired sets. For a *complete*, the same completion fires on the sound side, with $`R`$
  unchanged.
- *Backward (a sound fire is matched on the optimal side).* Symmetric, now re-establishing
  chain totality again from Lemma 2 and **no cross-talk** from `tc_sound` (Proposition 3).

Thus the two matching-layer facts feed the two side conditions of the bisimulation:
$`(\text{ii})\Rightarrow`$ chain totality and $`(\text{viii})\Rightarrow`$ no cross-talk,
which is exactly the spine $`(\text{ii})+(\text{viii})\Rightarrow(\text{iii})`$.

**Non-vacuity for (C).** Take $`K\,r:=\mathtt{app}\,0\,[\mathtt{var}]`$ for all $`r`$,
$`\mathit{site}:=\mathrm{id}`$, and $`r_1:=1\neq 2=:r_2`$. Then $`\mathrm{trace}`$ (which
ignores location) agrees, but the sound keys $`\mathrm{Some}(1,0)`$ and $`\mathrm{Some}(2,0)`$
differ, so the two schemes genuinely differ on channel identity while inducing the same
CLTS: the bisimulation is not the trivial "the schemes are identical". $`\blacksquare`$

*Mechanization.* `InRhoSameCLTSWeakBisim.v` — `optimal_visible_equals_sound` (`:142`),
`same_clts_weak_bisim` (`:231`); non-vacuity `optimal_shares_where_sound_separates`
(`:332`); side conditions via `optimal_chain_total_from_O1` / `sound_chain_total_from_O1`
(`:200`), `optimal_no_crosstalk_from_tc` (`:215`).

This is the chain $`(\text{ii}) + (\text{viii}) \Rightarrow (\text{iii})`$ made precise;
§8 threads it to $`(\text{v})`$.

---

## 5. Firing: each family as a single communication (T7–T15)

Each rewrite family lowers to a persistent $`\sigma`$-receiver whose guarded consume fires
as a COMM. The firing results prove, per family, a **step correspondence** (a lowered COMM
is matched by a source step and conversely) with **barb preservation**, plus **atomicity**
(all-or-nothing, no partial consume) and **no fabrication** (every emitted fact is a
$`\sigma`$-delivered reduct).

**Theorem 7 (linear COMM step correspondence — FBase).**
With $`[\![\cdot]\!]=\mathrm{lower\_state}`$, the base rewrite lowering is a
barb-preserving step bisimulation:
```math
[\![ s ]\!]\approx_{\downarrow}s,\quad
[\![ s ]\!]\xrightarrow{\mathrm{comm}}_d r'\Rightarrow\exists s'.\ s\to_d s'\wedge r'\approx_{\downarrow}s',\quad
s\to_d s'\Rightarrow\exists r'.\ [\![ s ]\!]\xrightarrow{\mathrm{comm}}_d r'\wedge r'\approx_{\downarrow}s'.
```

*Proof.* Lowering copies the send/receive multisets, so weak barb-equivalence
(output-membership agreement) is reflexive. **Soundness** unpacks the Rho COMM into
(receive-enabled, datum present, resulting state) and exhibits the mirror source state,
which consumes the datum and appends it to the outputs, with the barb equivalence immediate
from membership agreement. **Completeness** is the exact mirror. These are the FBase arms
`fwd` / `bwd` of the capstone. $`\blacksquare`$

*Mechanization.* `LinearCommCorrespondence.v` — `lower_preserves_barbs` (`:130`),
`comm_step_sound` (`:136`), `comm_step_complete` (`:153`).

**Theorem 8 (contextual atomic polyadic join + plugging — obligation (vii), FContextualJoin).**
The $`n`$-ary contextual join lowering is a barb-preserving step bisimulation (sound and
complete duals over $`n`$ holes), and the plugging context is total, injective on holes,
and reconstructs the redex.

*Proof.* The join consumes the whole hole list atomically and emits the single plugged
reduct $`\mathrm{plug}\,\mathit{holes}::\mathit{outputs}`$, so soundness and completeness
mirror the base COMM proof (Theorem 7) with the polyadic consume in place of the single
datum; barbs agree by the same reflexive membership argument. Plugging totality and
injectivity are structural inductions on the hole list, giving INV-6 (atomic polyadic join)
and INV-2 (plugging stability). $`\blacksquare`$

*Mechanization.* `ContextualAtomicJoinPlugging.v` — `nary_join_sound` (`:152`),
`nary_join_complete` (`:158`), `plug_ctx_total` / `plug_ctx_holes_injective` /
`wrap_plug_reconstructs` (`:177`), assembled at `contextual_join_atomic_and_plugging_stable`
(`:360`).

**Lemma 9 (non-linear equality consistency — obligation (vi)).**
A non-linear rule commits **iff** its repeated occurrences are all equal:
```math
\mathrm{present}(\mathit{facts},\mathit{prem})\wedge\mathrm{all\_equal}(\mathit{occ})\ \Longrightarrow\ \mathit{facts}\ \text{commits to}\ \mathrm{insert}(\mathit{out},\mathit{facts}),
```
and disagreement leaves $`\mathit{facts}`$ unchanged.

*Proof.* The rule's guard is $`\mathrm{all\_equal}(\mathit{occ})`$; commit routes through the
guarded-commit rule under the present premises and a true guard; rejection routes through the
failed-guard rule and consumes nothing. Together these are the two halves of *commit iff
name-equality* — the `merge_substs` semantics the receiver realizes — and no output is
fabricated. This gates the accept-send (role (vi) of §7.4). $`\blacksquare`$

*Mechanization.* `NonLinearEqConsistency.v` — `eq_all_equal_commits` (`:51`),
`eq_unequal_no_commit` (`:63`), with `eq_no_fabrication`.

**Lemma 10 (atomic firing, no partial match — obligation (iv)).**
A guarded consume either adds the whole output or leaves the facts unchanged; no reachable
state consumes a proper subset:
```math
\mathrm{guarded}(\mathit{facts},r,\mathit{next})\ \Longrightarrow\ \mathit{next}=\mathrm{insert}(\mathrm{out}(r),\mathit{facts})\ \vee\ \mathit{next}=\mathit{facts}.
```

*Proof.* By case analysis on the three constructors of the guarded-attempt relation:
commit yields the first disjunct, the two rejection cases the second. No constructor
produces a proper sub-multiset, so a half-consumed state is unreachable by construction.
This is the atomicity that makes `gstep` well-formed (role (iv)). $`\blacksquare`$

*Mechanization.* `AtomicFiringNoPartialMatch.v` — `partial_consume_unreachable` (`:39`),
`accept_atomic_after_verdict` (`:53`).

**Proposition 11 (ambient Open firing — FAcStructural).**
The structural-AC Open rule commits, atomically emitting **both** structural reducts
spliced with the rest, exactly when the ambient names agree, and rests (consuming nothing)
when they disagree; no fact is fabricated.

*Proof.* The guard reduces to name equality $`\mathrm{name\_open}=\mathrm{name\_amb}`$;
commit inserts $`[p;q]`$ under a true guard, disagreement rests. Every post-consume fact is
$`p`$, $`q`$, or previously present — the receiver forwards its $`\sigma`$-reducts, never
fabricating — and the multiset spread is report-faithful. $`\blacksquare`$

*Mechanization.* `AmbientOpenFiring.v` — `open_commits_when_names_agree` (`:155`),
`open_disagree_no_commit` (`:171`), `open_emits_both_reducts_and_splices_rest` (`:210`),
with `open_no_fabrication` and `structural_ac_spread_is_report_faithful`.

**Theorem 12 (ambient In/Out firing, depth-2 — FAcNested).**
The nested (depth-2) structural-AC In/Out rule is a barb-preserving step bisimulation, the
depth-2 twin of Theorem 7.

*Proof.* The lowering field-copies the outer and inner ambient names and the armed flag, so
the cross-level guard survives the lowering; each direction unpacks (armed, guard, result)
and exhibits the mirror configuration appending the fired reduct to the outputs, with barbs
equal by the reflexive membership argument. This arm's non-vacuous discharge through the
capstone is the In/Out witness of Theorem 23. $`\blacksquare`$

*Mechanization.* `AmbientInOutFiring.v` — `inout_step_complete` (`:395`), `inout_step_sound`
(`:402`), `inout_lower_preserves_barbs` (`:421`).

**Proposition 13 (native system-process boundary — FNative).**
A `fold` native process with a resolvable dispatch channel materializes its receiver and
emits exactly the reflected trusted handler value $`[\![ v ]\!]`$, and the emitted location
is a function of the automaton capture, not the report.

*Proof.* Materialization holds iff the fold verdict and a resolvable channel; the payload
equality states that the receiver emits $`[\![ v ]\!]`$ for the injected handler value. For
location separation, two configurations sharing the automaton captures but differing in
report emit the same location — the payload is a **trusted** handler value at the
host-obligation seam, the directed-compute COMM, not a predicate. $`\blacksquare`$

*Mechanization.* `NativeSystemProcessBoundary.v` — `fold_native_process_fires_handler_value`
(`:190`), `emitted_is_reflected_handler_value` (`:228`), `location_from_automaton_not_report`
(`:333`).

**Lemma 14 (linear COMM-rule firing — FAcLinear payload).**
The linear COMM rule commits with its reduct exactly when the receive and send channels
agree, and rests otherwise.

*Proof.* The rule is a two-slot guarded rule; commit reuses the two-slot agreement result
with the channel slots equal, and rejection is its converse. The AC firing **reuses** this
base flat $`\sigma`$-receiver step, so FAcLinear introduces no new transition — the AC bundle
(Proposition 15) certifies its payload and atomicity. $`\blacksquare`$

*Mechanization.* `CommRuleFiring.v` — `comm_commits_when_channels_agree` (`:79`), with
`comm_disagree_no_commit`, `comm_no_fabrication`, `comm_emits_reduct_and_splices_rest`.

**Proposition 15 (the AC bundle — payload and atomicity for the AC families).**
Four results certify that AC firing consumes and reconstructs multisets faithfully and
atomically: *(a)* the AC consume is all-or-nothing and removes exactly the matched selection;
*(b)* the residual remainder is the exact complement, spliced back without loss; *(c)*
non-linear AC — including the depth-2 cross-level guard — commits iff the repeated slots
agree; *(d)* the AC4 Map split preserves key-uniqueness and is permutation-invariant.

*Proof.* Each is a multiset / permutation induction over the multiset-semiring support:
all-or-nothing by case analysis on the consume constructors; complement exactness by
one-element removal preserving permutation; cross-level consistency by lifting the two-slot
agreement result per level; key-uniqueness by invariance of the key list under permutation.
These are **payload and atomicity certificates**, not independent step-correspondences: they
enter the capstone for FAcLinear / FAcStructural / FAcNested (§7.4). $`\blacksquare`$

*Mechanization.* `AcAtomicNoPartialConsume.v` — `ac_consume_all_or_nothing` (`:49`),
`ac_commit_removes_exactly_the_selection` (`:80`); `AcRestReconstruction.v` —
`selection_rest_partition` (`:63`), `flatten_splices_subbag` (`:92`);
`AcNonLinearConsistency.v` — `ac_nl_commits_iff_slots_agree` (`:40`),
`ac_nl_cross_level_commits` (`:147`), `ac_nl_cross_level_reject_safe` (`:165`);
`AcMapKeyUniqueness.v` — `map_split_preserves_uniqueness` (`:139`),
`correlation_perm_invariant` (`:171`).

---

## 6. The binder family: a substitution rewriting system (T16–T20)

The binder family is the terminal endpoint of the development: $`\beta`$ performs its
capture-avoiding substitution as a metered cascade of COMMs (doc
[19](19-in-rho-binder-beta-substitution.md)). Correctness is a classical rewriting result
— SN $`+`$ CR give a unique NF, which is identified with $`b[a/0]`$ — lifted to a weak
bisimulation with abstract $`\beta`$. The cascade is modelled by the term-rewriting system
$`\to`$ (`step`) over the term algebra $`\mathrm{Tm}`$
([EXPLICIT-SUBST-1991](references.md#explicit-subst-1991),
[CURIEN-HARDIN-LEVY-1996](references.md#curien-hardin-levy-1996)). Termination is witnessed
by the weighted interpretation $`\mu:\mathrm{Tm}\to\mathbb{N}`$, defined clause for clause by

```math
\mu(t)=
\begin{cases}
1 & t=\mathtt{bound}\,n\ \text{ or }\ t=\mathtt{free}\,x,\\[2pt]
1+\mu(b) & t=\mathtt{lam}\,b,\\[2pt]
1+\sum_{i=1}^{m}\mu(t_i) & t=\mathtt{node}\,op\,[t_1,\dots,t_m],\\[2pt]
2\,\mu(t') & t=\mathtt{shift}\,c\,t',\\[2pt]
(\mu(a)+2)\cdot 3^{\,k} & t=\mathtt{shiftk}\,k\,a,\\[2pt]
(\mu(a)+2)\cdot 3^{\,j}\cdot 4^{\,\mu(t')} & t=\mathtt{subst}\,j\,a\,t',
\end{cases}
```

together with the positivity fact $`\mu(t)\ge 1`$ for all $`t`$. The load-bearing clause is
the last: the factor $`4^{\mu(t')}`$ is the substitution fuel and $`3^{j}`$, $`3^{k}`$ the
shift fuel, pre-paid so that every rule strictly decreases the measure.

**Theorem 16 (strong normalization via the $`\mu`$-weighted measure).**
The substitution rewriting system is strongly normalizing: there is no infinite chain
$`t_0\to t_1\to\cdots`$. Concretely, every reduction strictly decreases $`\mu`$,
```math
\forall t,u.\ \ t\to u\ \Longrightarrow\ \mu(u)<\mu(t),
```
so $`\to`$ is well-founded.

*Proof.* **Why the naive measure fails.** The obvious lexicographic measure
$`\langle\#\text{nodes},\ \text{size}\rangle`$ is non-monotone: the shift-unfolding rule
$`\mathtt{shiftk}(k{+}1,\,a)\to\mathtt{shift}(0,\ \mathtt{shiftk}(k,\,a))`$ *creates* a fresh
$`\mathtt{shift}`$ node, so the node count strictly increases even though the term is making
progress. No pure structural size decreases here. The repair pre-pays, in the weight of each
$`\mathtt{shiftk}`$ / $`\mathtt{subst}`$ node, all the shift and subst passes it will ever
spawn: losing one unit of $`k`$ divides the weight by $`3`$, which dominates the factor-$`2`$
cost of the spawned $`\mathtt{shift}`$; and descending a $`\mathtt{subst}`$ under a binder
trades a factor $`3`$ (from $`3^{j}\to 3^{j+1}`$) against a factor $`4`$ (the $`\mathtt{lam}`$
body loses one $`\mathtt{lam}`$, so $`4^{\mu}`$ drops by $`4`$), and $`4>3`$.

**Head rules — an exhaustive strict-decrease check.** Reduction is the congruence closure of
ten head contractions; using $`\mu(a)\ge 1`$ and $`3^{k},4^{k}\ge 1`$ throughout, each head
rule strictly decreases $`\mu`$ (write $`\Sigma=\sum_i\mu(t_i)`$ and $`D=(\mu(a)+2)3^{j}\ge 2`$):

| head rule | $`\mu`$ of redex | $`\mu`$ of contractum | strict because |
|---|---|---|---|
| $`\mathtt{shift}\,c\,(\mathtt{bound}\,n)`$ | $`2`$ | $`1`$ | $`1<2`$ |
| $`\mathtt{shift}\,c\,(\mathtt{lam}\,b)`$ | $`2+2\mu(b)`$ | $`1+2\mu(b)`$ | drop of $`1`$ |
| $`\mathtt{shift}\,c\,(\mathtt{free}\,x)`$ | $`2`$ | $`1`$ | $`1<2`$ |
| $`\mathtt{shift}\,c\,(\mathtt{node}\,op\,ts)`$ | $`2+2\Sigma`$ | $`1+2\Sigma`$ | drop of $`1`$ |
| $`\mathtt{shiftk}\,0\,a`$ | $`\mu(a)+2`$ | $`\mu(a)`$ | drop of $`2`$ |
| $`\mathtt{shiftk}(k{+}1)\,a`$ | $`3(\mu(a){+}2)3^{k}`$ | $`2(\mu(a){+}2)3^{k}`$ | $`2<3`$ (the key case) |
| $`\mathtt{subst}\,j\,a\,(\mathtt{bound}\,n)`$ | $`4(\mu(a){+}2)3^{j}`$ | $`(\mu(a){+}2)3^{j}`$ or $`1`$ | three numeral sub-cases |
| $`\mathtt{subst}\,j\,a\,(\mathtt{lam}\,b)`$ | $`4(\mu(a){+}2)3^{j}4^{\mu(b)}`$ | $`1+3(\mu(a){+}2)3^{j}4^{\mu(b)}`$ | $`4>3`$ |
| $`\mathtt{subst}\,j\,a\,(\mathtt{free}\,x)`$ | $`4(\mu(a){+}2)3^{j}`$ | $`1`$ | redex $`\ge 4`$ |
| $`\mathtt{subst}\,j\,a\,(\mathtt{node}\,op\,ts)`$ | $`D\cdot 4^{\,1+\Sigma}`$ | $`1+D\cdot\!\sum_i 4^{\mu(t_i)}`$ | see below |

The two nontrivial entries: the $`\mathtt{bound}`$ case does a three-way split on $`n`$ against
$`j`$ — contractum $`\mathtt{shiftk}\,j\,a`$ (weight $`(\mu(a){+}2)3^{j}`$) when equal, or a bound
leaf (weight $`1`$) otherwise — each below $`4(\mu(a){+}2)3^{j}`$. The $`\mathtt{node}`$ case is
the one genuine inequality: the children's fuels are dominated by the parent's,
$`\sum_i 4^{\mu(t_i)}<4^{\,1+\Sigma}=4\cdot 4^{\Sigma}`$ (a short induction on the child list), and
since $`D\ge 2`$ and the contractum's outer $`\mathtt{node}`$ contributes only $`+1`$, we get
$`1+D\!\sum_i 4^{\mu(t_i)}<D\cdot 4\cdot 4^{\Sigma}`$.

**Congruence closure.** Extend to $`\to`$ by induction on the one-hole context, using strict
monotonicity of $`\mu`$ in each argument slot: under $`\mathtt{lam}`$ ($`\mu\mapsto 1+\mu`$),
under a $`\mathtt{node}`$ child (the child-sum splits additively), under $`\mathtt{shift}`$
(factor $`2`$), under $`\mathtt{shiftk}`$ (factor $`3^{k}\ge 1`$), in the argument of a
$`\mathtt{subst}`$ ($`\mu`$ monotone in the first factor of the monomial
$`(\mu(a)+2)3^{j}4^{\mu(t)}`$), and in its body ($`\mu(t)\mapsto 4^{\mu(t)}`$ is strictly
increasing). Every case yields $`\mu(u)<\mu(t)`$.

**Conclusion.** $`\mu`$ embeds $`\to`$ into the well-order $`(\mathbb{N},<)`$ as a strictly
decreasing map; the inverse image of a well-founded order under any function is well-founded,
so $`\to`$ is well-founded, i.e. strongly normalizing. $`\blacksquare`$

*Mechanization.* `DeBruijnSubstTRS.v` — `subst_trs_terminating` (`:804`), via
`step_decreases_mu` (`:783`); measure `mu` (`:631`), positivity `mu_pos` (`:678`).

**Theorem 17 (confluence by a normalizing interpretation).**
The rewriting system is Church–Rosser: any two reducts share a common reduct,
```math
\forall t,u_1,u_2.\ \ t\twoheadrightarrow u_1\ \wedge\ t\twoheadrightarrow u_2\ \Longrightarrow\ \exists v.\ u_1\twoheadrightarrow v\ \wedge\ u_2\twoheadrightarrow v,
```
where $`\twoheadrightarrow`$ is the reflexive-transitive closure.

*Proof.* The argument is a step-invariant normalizing interpretation — no critical-pair
analysis is needed. Define the evaluation $`\mathrm{norm}:\mathrm{Tm}\to\mathrm{Obj}`$ that
computes every machinery node to its intended object result ($`\mathtt{shift}`$,
$`\mathtt{shiftk}`$, $`\mathtt{subst}`$ become the object operations), and the embedding
$`\mathrm{embed}:\mathrm{Obj}\to\mathrm{Tm}`$. Two facts hold: **(1)** $`\mathrm{norm}`$ is a
reduction invariant, $`t\twoheadrightarrow u\Rightarrow\mathrm{norm}(t)=\mathrm{norm}(u)`$
(each head contraction leaves $`\mathrm{norm}`$ unchanged, then close under congruence); and
**(2)** every term reduces to the embedding of its norm,
$`t\twoheadrightarrow\mathrm{embed}(\mathrm{norm}(t))`$ (structural induction driving each
machinery node to its object value). Given $`t\twoheadrightarrow u_1`$ and
$`t\twoheadrightarrow u_2`$, take the common reduct **explicitly** as
$`v:=\mathrm{embed}(\mathrm{norm}(t))`$. By invariance
$`\mathrm{norm}(u_1)=\mathrm{norm}(t)=\mathrm{norm}(u_2)`$, and by (2) applied to each $`u_i`$,
$`u_i\twoheadrightarrow\mathrm{embed}(\mathrm{norm}(u_i))=v`$. So $`v`$ closes the diamond
directly — the interpretation already pins a canonical reduct for every term. $`\blacksquare`$

*Mechanization.* `DeBruijnSubstTRS.v` — `subst_trs_confluent` (`:612`), via
`star_preserves_norm` and `reduces_to_norm`.

**Corollary 18 (the normal form is the de-Bruijn $`\beta`$-reduct).**
For the seed $`\mathtt{subst}\,0\,[\![ a ]\!]\,[\![ b ]\!]`$,
```math
\mathrm{norm}\big(\mathtt{subst}\,0\,[\![ a ]\!]\,[\![ b ]\!]\big)=b[a/0],
```
and, combining SN (Theorem 16) with CR (Theorem 17), every object term reachable from the
seed under any interleaving of the $`\tau`$-COMMs equals the one normal form
$`[\![\,b[a/0]\,]\!]`$.

*Proof.* Unfolding $`\mathrm{norm}`$ on the seed gives
$`\mathrm{osubst}\,0\,(\mathrm{norm}[\![ a ]\!])\,(\mathrm{norm}[\![ b ]\!])`$; since
$`\mathrm{norm}\circ\mathrm{embed}=\mathrm{id}`$, this is $`\mathrm{osubst}\,0\,a\,b`$, the
definition of $`b[a/0]`$. For uniqueness, any object term is machinery-free, hence its own
norm-embedding $`u=\mathrm{embed}(\mathrm{norm}(u))`$ (structural induction over object
constructors); and $`\mathrm{norm}`$ is a reduction invariant (Theorem 17), so from
$`t\twoheadrightarrow u`$ with $`u`$ an object, $`u=\mathrm{embed}(\mathrm{norm}(t))`$ — every
reachable normal form is *the* one determined by $`t`$. Existence is SN plus the
reduces-to-norm fact; specializing $`t`$ to the seed and rewriting by the first identity
yields $`[\![\,b[a/0]\,]\!]`$, and the cascade actually reaches it. $`\blacksquare`$

*Mechanization.* `DeBruijnSubstTRS.v` — `subst_normal_form_is_debruijn_beta` (`:816`),
`subst_trs_unique_nf` (`:851`), `beta_seed_unique_nf_is_debruijn_beta` (`:862`),
`beta_cascade_reaches_debruijn_nf` (`:823`).

**Theorem 19 ($`\beta`$-cascade weak bisimulation — FBinderBeta).**
Let abstract $`\beta`$ be the object rewrite
$`\mathtt{node}\,op\,[\mathtt{lam}\,b,\ a]\xrightarrow{op}b[a/0]`$, and let the concrete
weak-visible transition be $`\tau^{*}\cdot(\text{seed send})\cdot\tau^{*}`$, whose visible step
is $`\mathtt{node}\,op\,[\mathtt{lam}[\![ b ]\!],\ [\![ a ]\!]]\to\mathtt{subst}\,0\,[\![ a ]\!]\,[\![ b ]\!]`$.
With $`\mathrm{represents}(o,c):\Longleftrightarrow\mathrm{norm}(c)=o`$, the relation
$`\mathrm{represents}`$ is a weak bisimulation between abstract $`\beta`$ and the cascade, and
it is **non-vacuous**.

*Proof.* **Forward (abstract simulated by concrete).** Given $`\mathrm{represents}(o,c)`$ and an
abstract step $`o\xrightarrow{op}o'`$, unpack $`o=\mathtt{node}\,op\,[\mathtt{lam}\,b,\ a]`$ and
$`o'=b[a/0]`$. Since $`\mathrm{norm}(c)=o`$, the term $`c`$ reduces along $`\tau^{*}`$ to the
reflected redex $`\mathtt{node}\,op\,[\mathtt{lam}[\![ b ]\!],\ [\![ a ]\!]]`$; fire the visible
seed COMM to $`\mathtt{subst}\,0\,[\![ a ]\!]\,[\![ b ]\!]`$, with no further $`\tau`$. The
target represents $`o'`$ because the seed's norm is $`b[a/0]`$ (Corollary 18). **Backward
(concrete simulated by abstract).** Given $`\mathrm{represents}(o,c)`$ and a concrete
weak-visible $`c\overset{op}{\Longrightarrow}c'`$, decompose it into the $`\tau`$-prefix
$`c\twoheadrightarrow c_1`$, the visible fire
$`c_1=\mathtt{node}\,op\,[\mathtt{lam}[\![ b ]\!],\ [\![ a ]\!]]\to c_2=\mathtt{subst}\,0\,[\![ a ]\!]\,[\![ b ]\!]`$,
and the $`\tau`$-suffix $`c_2\twoheadrightarrow c'`$. The prefix cannot change $`\mathrm{norm}`$,
so $`o=\mathrm{norm}(c)=\mathrm{norm}(c_1)=\mathtt{node}\,op\,[\mathtt{lam}\,b,\ a]`$; hence
abstract $`\beta`$ fires $`o\xrightarrow{op}b[a/0]`$. The suffix also preserves $`\mathrm{norm}`$,
so $`\mathrm{norm}(c')=\mathrm{norm}(c_2)=b[a/0]`$ (Corollary 18), i.e.
$`\mathrm{represents}(b[a/0],\,c')`$. The single visible label is object-$`\beta`$; each
`^subst` / `^shift` / `^shiftk` / `^cmp` / `^pred` COMM is $`\tau`$; the up-to-$`\tau`$ target is
well defined by Corollary 18.

**Non-vacuity — closing the erasure trap.** A pure $`\tau`$-erasure bisimulation (as in Theorem
6) never inspects what the silent steps compute, so an inert $`\tau`$ backbone would satisfy it
vacuously. Here the backbone does real work: the witness $`(\lambda.\,\underline{0})\,(\mathtt{free}\ A)`$
fires to the seed $`\mathtt{subst}\,0\,(\mathtt{free}\ A)\,\underline{0}`$, which takes the genuine,
non-identity step $`\to\mathtt{shiftk}\,0\,(\mathtt{free}\ A)`$ (numeral dispatch $`n=j=0`$ gives the
equal branch) and then $`\to\mathtt{free}\ A`$ (the $`\mathtt{shiftk}\,0`$ erasure). So the
$`\tau`$-cascade is not inert and the bisimulation is not vacuously satisfied. This is the
capstone's FBinderBeta arm; its `cwvis` shape is the reference for `gstep`. $`\blacksquare`$

*Mechanization.* `InRhoBetaCascadeWeakBisim.v` — `weak_bisim_beta_cascade_vs_abstract_beta`
(`:172`), `beta_cascade_is_nonvacuous` (`:216`); via `reduces_to_reflected_redex`,
`cbeta_fire`, `seed_norm_is_beta`.

**Lemma 20 (binder reflection is total-or-reject and injective).**
The reflection of a runtime term to its reserved-tagged ground image is injective and
collision-free,
```math
\forall t_1,t_2.\ \ \mathrm{mreflect}(t_1)=\mathrm{mreflect}(t_2)\ \Longrightarrow\ t_1=t_2,
```
so the reflected $`\beta`$-redex
$`\mathrm{App}(\text{\textasciicircum}\mathrm{lambda}(F(\text{\textasciicircum}\mathrm{bound}\,Z)),\ A)`$
is an unambiguous automaton subject, and reflection is total with a fail-closed rejection only
for a pre-scope binder lacking a single-child `^lambda` image.

*Proof.* By structural induction on the term, matched against a case split on the second term:
every constructor injects through its reserved list tag, and the `^bound` case reduces to
injectivity of the Peano numeral. The collision-free lemmas show a caret-prefixed reserved tag
never equals a structural-constructor image, and the five reduction shapes are pairwise
distinct. Totality means every runtime term has a ground image, with the fail-closed rejection
the only exception. $`\blacksquare`$

*Mechanization.* `BinderReflectionTotalOrReject.v` — `mreflect_inj` (`:437`), `mpeano_inj`
(`:512`), the collision-free tag lemmas (`:608`), `subst_five_shapes_distinct` / `sbreflect_inj`
(`:621`).

---

## 7. The main theorem: whole-$`[\![ G ]\!]`$ operational correspondence (T21–T23)

The per-step results above are assembled by a **composition harness** into a finite-trace
operational correspondence for the whole encoded language. The harness (a) instantiates an
abstract finite-trace lifting lemma with the whole-$`[\![ G ]\!]`$ CLTS; (b) assembles its
three obligations by a family case split whose arms are the landed per-step results of §5–§6;
and (c) threads obligation (iii) so the result holds over the O1-optimal matching.

### 7.1 A finite-trace lifting lemma (T21)

**Lemma 21 (the finite-trace lift).**
Fix an observed LTS $`(S,A,\mathrm{Obs},\to,\mathrm{barb})`$ and a relation
$`R\subseteq S\times S`$ satisfying the three square conditions
```math
\begin{aligned}
&R_{\mathrm{barb}}:\ R\,s\,t\Rightarrow \mathrm{barb}\,s=\mathrm{barb}\,t,\\
&R_{\mathrm{fwd}}:\ R\,s\,t\wedge s\xrightarrow{l}s'\Rightarrow\exists t'.\ t\xrightarrow{l}t'\wedge R\,s'\,t',\\
&R_{\mathrm{bwd}}:\ R\,s\,t\wedge t\xrightarrow{l}t'\Rightarrow\exists s'.\ s\xrightarrow{l}s'\wedge R\,s'\,t'.
\end{aligned}
```
Then $`R`$ lifts to finite label-indexed traces: for all $`s,t,\mathit{ls}`$ with $`R\,s\,t`$,
every trace from $`s`$ over $`\mathit{ls}`$ is matched by a trace from $`t`$ over the **same**
$`\mathit{ls}`$ ending in an $`R`$-related, barb-equal state, and conversely.

*Proof.* Prove the strengthened forward statement by induction on the derivation of
$`\mathrm{steps}\,s\,\mathit{ls}\,s'`$. **Base** ($`\mathit{ls}=\varepsilon`$, $`s'=s`$): return
$`t`$ itself; the empty trace relates $`t`$ to $`t`$, $`R\,s\,t`$ holds, and
$`\mathrm{barb}\,s=\mathrm{barb}\,t`$ by $`R_{\mathrm{barb}}`$. **Step**
($`\mathit{ls}=l\!:\!\mathit{ls}_0`$, via $`s\xrightarrow{l}s_0`$ and
$`\mathrm{steps}\,s_0\,\mathit{ls}_0\,s'`$): push the head step through $`R_{\mathrm{fwd}}`$ to get
$`t\xrightarrow{l}t_0`$ with $`R\,s_0\,t_0`$; apply the induction hypothesis at $`(s_0,t_0)`$ to get
a tail $`\mathrm{steps}\,t_0\,\mathit{ls}_0\,t'`$ with $`R\,s'\,t'`$ and equal barbs; prepend the
head with the cons rule to obtain $`\mathrm{steps}\,t\,(l\!:\!\mathit{ls}_0)\,t'`$. The backward
statement is the mirror induction using $`R_{\mathrm{bwd}}`$. The final statement projects the
barb equalities out of both directions. The three obligations $`R_{\mathrm{barb}}`$,
$`R_{\mathrm{fwd}}`$, $`R_{\mathrm{bwd}}`$ are premises — universally-quantified antecedents,
discharged where the lemma is applied (§9.3). $`\blacksquare`$

*Mechanization.* `EndToEndCommCorrespondence.v` — `forward_trace_correspondence` (`:60`),
`backward_trace_correspondence` (`:75`), `finite_trace_barb_equivalence` (`:92`).

The three obligations are the **bisimulation squares** of Figure 22-4.

![Figure 22-4 — the finite-trace lifting squares](figures/22-bisimulation-squares.svg)

*Figure 22-4. The three obligations of the finite-trace lift as commuting squares:
$`R_{\mathrm{barb}}`$ (equal observations), $`R_{\mathrm{fwd}}`$ (source step matched by target
step), $`R_{\mathrm{bwd}}`$ (target step matched by source step), each preserving $`R`$. Lemma 21
lifts these from one step to finite label-indexed traces by induction on the trace derivation.
Source: [figures/22-bisimulation-squares.puml](figures/22-bisimulation-squares.puml).*

### 7.2 The family decomposition feeding the main theorem

The capstone CLTS `gstep` is a weak-visible any-family COMM
$`\tau^{*} \cdot c(\ell) \cdot \tau^{*}`$. Its family tag ranges over seven constructors — six
rule families plus the slotted In/Out arm — each discharged by the cited landed result of §5–§6.

![Figure 22-2 — the seven-arm family decomposition feeding the main theorem](figures/22-family-split.svg)

*Figure 22-2. The family case split. The forward and backward assembly destruct the family tag
into seven arms; each arm is a premise in the lifting lemma's obligation shape, discharged at any
concrete instantiation by its cited per-family result (FBase $`\leftarrow`$ T7, FContextualJoin
$`\leftarrow`$ T8, FAcLinear $`\leftarrow`$ T14 $`+`$ T15, FAcStructural $`\leftarrow`$ T11,
FBinderBeta $`\leftarrow`$ T19, FNative $`\leftarrow`$ T13, FAcNested $`\leftarrow`$ T12). The
uncovered-shape branch is closed by the install gate (ix). Source:
[figures/22-family-split.puml](figures/22-family-split.puml).*

### 7.3 The correspondence over the sound baseline (T22)

**Theorem 22 (whole-$`[\![ G ]\!]`$ in-Rho operational correspondence — obligation (v)).**
Every non-semantic-predicate rewrite trace of $`[\![ G ]\!]`$ is matched and fired in-Rho, in
both directions, with equal barbs at every reachable state. For the capstone CLTS with states
$`\mathrm{GConfig}`$, weak-visible transition $`\mathrm{gstep}`$, observation $`\mathrm{gbarb}`$,
and correspondence $`R_{\mathrm{gio}}`$: for all $`s,t,\mathit{ls}`$ with $`R_{\mathrm{gio}}\,s\,t`$,
```math
\big(\forall s'.\ \mathrm{steps}\,s\,\mathit{ls}\,s'\Rightarrow\exists t'.\ \mathrm{steps}\,t\,\mathit{ls}\,t'\wedge \mathrm{gbarb}\,s'=\mathrm{gbarb}\,t'\big)\ \wedge\ \big(\text{the backward dual}\big).
```

*Proof.* The statement is Lemma 21 specialized to
$`(\mathrm{GConfig},\mathrm{CommLabel},\mathrm{Barb},\mathrm{gstep},\mathrm{gbarb},R_{\mathrm{gio}})`$,
so it suffices to discharge the three square obligations. $`R_{\mathrm{barb}}`$ is
$`R_{\mathrm{gio}}`$-barb preservation, a premise of the harness. $`R_{\mathrm{fwd}}`$ and
$`R_{\mathrm{bwd}}`$ are each proved by a **case split on the family tag**
$`\mathrm{family\_of}(l)`$: if it is $`\mathrm{Some}\,f`$, split $`f`$ into the seven
constructors and discharge each arm by its landed per-family result — FBase by Theorem 7,
FContextualJoin by Theorem 8, FAcLinear by Lemma 14 (payload Proposition 15), FAcStructural by
Proposition 11, FBinderBeta by Theorem 19, FNative by Proposition 13, FAcNested by Theorem 12;
if it is $`\mathrm{None}`$ (an uncovered shape), the branch is vacuous, since a gate-admitted
$`[\![ G ]\!]`$ never fires an uncovered shape (obligation (ix)).

**Semantic-predicate exclusion.** Predicates (INV-14) contribute no transition, on two
independent grounds: the family type has no predicate constructor, and a predicate disposition
emits no label — so it yields no `gstep` and is absent from every trace the theorem ranges over.

**Non-vacuity.** Instantiate the whole harness on the common-carrier sum
$`\mathrm{GC}:=\mathrm{GSrc}\mathbin{|}\mathrm{GRho}`$, with $`\mathrm{gstep}`$ dispatching a source
COMM on $`\mathrm{GSrc}`$ and a lowered Rho COMM on $`\mathrm{GRho}`$, $`R_{\mathrm{gio}}`$ the
lowering, and every label tagged FBase. The FBase arm is discharged from the landed
`comm_step_complete` / `comm_step_sound` (Theorem 7), the other six arms hold vacuously (no label
is ever their tag), and the gate holds because every label is $`\mathrm{Some}\,\mathrm{FBase}\neq\mathrm{None}`$.
This yields a concrete finite-trace operational correspondence *through* the capstone, proving the
premise context is inhabited. $`\blacksquare`$

*Mechanization.* `WholeGsltInRhoOpCorrespondence.v` — `whole_gslt_in_rho_opcorrespondence`
(`:356`); semantic-predicate exclusion `semantic_predicates_emit_no_comm` (`:277`); non-vacuity
`swapdemo_base_finite_trace_opcorr` (`:553`).

### 7.4 Which results are step-correspondences, and which are structural

The capstone is explicit about its arm structure:

- **The seven arms that feed $`R_{\mathrm{fwd}}`$ / $`R_{\mathrm{bwd}}`$ are genuine per-step
  correspondences** (Theorems 7, 8, 12, 19; Propositions 11, 13; and Lemma 14 with Proposition
  15).
- **The matching layer (i, ii, iv, vi, viii, x) does not appear as arms.** These are match-logic,
  atomicity, and guard results. They enter only as **`gstep` well-formedness** — (iv) no partial
  match reachable; (vi) the guard gates the accept-send; (x) the $`\tau`$-prefix is deterministic;
  (i) the in-Rho $`\sigma`$ equals the positional $`\sigma`$ — and as **premises of obligation
  (iii)** (ii and viii, via Theorem 6). The capstone *uses* (iii); it does not consume the matching
  layer as arms.
- **The AC bundle (Proposition 15) certifies payload and atomicity**, not a distinct transition:
  AC firing reuses the base flat $`\sigma`$-receiver step (Lemma 14).

### 7.5 The correspondence over the O1-optimal matching (T23)

**Theorem 23 (the main theorem over O1-optimal matching — the `rem:nonopt` discharge).**
The correspondence holds not only for the sound (location-keyed) baseline but over the O1-optimal
($`tc(K)`$-keyed) in-Rho matching. With the source-to-sound correspondence $`R_{\mathrm{gio}}`$ and
the sound-to-optimal transfer $`R_{\mathrm{so}}`$: for all $`s,t,u,\mathit{ls}`$ with
$`R_{\mathrm{gio}}\,s\,t`$ and $`R_{\mathrm{so}}\,t\,u`$,
```math
\big(\forall s'.\ \mathrm{steps}_{\mathrm{gstep}}\,s\,\mathit{ls}\,s'\Rightarrow\exists u'.\ \mathrm{steps}_{\mathrm{gstep\_opt}}\,u\,\mathit{ls}\,u'\wedge \mathrm{gbarb}\,s'=\mathrm{gbarb}\,u'\big)\ \wedge\ \big(\text{the backward dual over }\mathrm{gstep\_opt}\big).
```

*Proof.* The three transfer hypotheses are precisely Theorem 6's barb preservation and its two
bisimulation clauses (the forward hypothesis is "a sound fire is matched on the optimal side"; the
backward hypothesis is its converse). By the same induction on the trace derivation as Lemma 21 —
now carrying $`R_{\mathrm{so}}`$ and relating the distinct step relations $`\mathrm{gstep}`$ and
$`\mathrm{gstep\_opt}`$ — these lift to finite traces. The theorem then composes: **forward** runs
Theorem 22's forward to a sound trace, then the sound-to-optimal lift to an optimal trace, chaining
the two barb equalities to $`\mathrm{gbarb}\,s'=\mathrm{gbarb}\,u'`$; **backward** runs the mirror.
This is exactly $`(\text{v})_{\text{sound}}\wedge(\text{iii})\Rightarrow(\text{v})_{\text{optimal}}`$.

Two provenance points: the transfer hypotheses are backed by the **real** landed obligation (iii)
in the companion `WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v`, instantiated at
`same_clts_weak_bisim` (Theorem 6) — the literal cross-project discharge; and the FAcNested arm's
non-vacuous discharge is the companion `WholeGsltInRhoOpCorrespondenceInOutViaFiring.v`, which
instantiates the same capstone with an In/Out common-carrier sum satisfied from `inout_step_complete`
/ `inout_step_sound` (Theorem 12), putting In/Out on equal footing with the FAcStructural Open arm.
$`\blacksquare`$

*Mechanization.* `WholeGsltInRhoOpCorrespondence.v` — `whole_gslt_opcorr_over_optimal_matching`
(`:438`); companions `WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v` —
`matching_locus_fwd_from_bisim` / `matching_locus_bwd_from_bisim` (`:52`, `:63`);
`WholeGsltInRhoOpCorrespondenceInOutViaFiring.v` — `inoutdemo_nested_finite_trace_opcorr` (`:127`).

---

## 8. Proof of the main theorem: the dependency spine

The main theorem is not a monolith; it is the sink of a directed acyclic dependency graph. The
load-bearing spine is
$`(\text{ii}) + (\text{viii}) \Rightarrow (\text{iii}) \Rightarrow (\text{v})`$: the $`O1`$ totality
(ii) and the $`tc(K)`$ no-cross-talk (viii) discharge the sound-$`\equiv`$-optimal weak bisimulation
(iii, Theorem 6), which — threaded through the finite-trace lift — upgrades the sound-baseline
correspondence (v) to hold over the optimal matching. In parallel, the seven family arms feed the
lifting lemma (Lemma 21) to give the sound-baseline correspondence, and the matching layer supplies
`gstep` well-formedness. Figure 22-1 is the whole graph.

![Figure 22-1 — the dependency graph of the argument: obligations to the main theorem](figures/22-discharge-dag.svg)

*Figure 22-1. The dependency graph. Green nodes are the two main theorems; the amber spine is
$`(\text{ii}) + (\text{viii}) \Rightarrow (\text{iii})`$; the family arms (violet) feed the lifting
lemma (T21); the matching layer (grey) supplies `gstep` well-formedness and the (iii) premises. Every
node is machine-checked (§9). Source: [figures/22-discharge-dag.puml](figures/22-discharge-dag.puml).*

As a proof, the chain reads: by Theorem 6,
$`(\text{ii}) \wedge (\text{viii}) \Rightarrow (\text{iii})`$; by the per-step results T7–T20
assembled through the lifting Lemma 21,
$`\text{(the seven arms)} \Rightarrow (\text{v})_{\text{sound}}`$ (Theorem 22); and by the transitive
composition of Theorem 23,
$`(\text{v})_{\text{sound}} \wedge (\text{iii}) \Rightarrow (\text{v})_{\text{optimal}}`$. The three
implications are the two instantiation steps and one composition step of the argument; no step is left
to the reader.

---

## 9. Mechanization and rigor

The trustworthiness of the results rests on a mechanical guarantee, not a promise. This section
records what "machine-checked" means, the repository check that enforces it, the status of the
composition premises, and the size of the certified corpus.

### 9.1 What "machine-checked" means here

Every numbered result above is machine-checked: its formal proof is *closed under the ambient
theory* — the proof term depends on no assumed proposition, no admitted subgoal, and no abstract
constant. We state this certification once, here, rather than repeating it per result. In logical
terms, a complete formalization introduces none of the following incompleteness devices:

| Device | What it would introduce |
|---|---|
| `Axiom` | an assumed proposition, true by fiat |
| `Conjecture` | an unproven claim admitted as if true |
| `Parameter` | an abstract global constant of a given type |
| `Admitted.` | a proposition whose proof is discharged by admission |
| `admit` | a tactic that closes a subgoal without proof |

Because the development contains none of these, each named result's proof-term audit reports that it
is closed under the ambient global context.

### 9.2 The repository check

The absence of the five devices is enforced mechanically. The scanner
`formal/scripts/check_rocq_zero_admission.py` strips nested comments (preserving line numbers, so a
diagnostic points at the real line) and rejects any line whose head matches a banned command,
tolerating leading modifiers (`Local`, `Global`, `Polymorphic`, `Monomorphic`) and requiring `admit`
to be a standalone tactic. Its self-test fixtures assert each of the five is caught, and a clean
fixture confirms the comment-stripping raises no false positive. The Makefile target
`rocq-critical-zero-admission` (`formal/Makefile`, `:159`) first self-tests the scanner, then scans
the critical suites — `formal/rocq/rho_bridge/theories`, `formal/rocq/advanced_automata/theories`, and
the Dovetail / symbolic-algebra / SFT roots — under the capped build. A single offending line fails the
build. This scan is the mechanical guarantee behind §9.1. Figure 22-3 draws the check as a flow.

![Figure 22-3 — the mechanized-rigor check: closure certificate plus repository scan](figures/22-zero-admission-gate.svg)

*Figure 22-3. The mechanized-rigor check. Each theory compiles and its proof-term audit reports
closure under the ambient context (or the build stops), admitting the result to the certified corpus;
the repository gate then re-scans the sources for any banned command and self-tests the scanner.
Source: [figures/22-zero-admission-gate.puml](figures/22-zero-admission-gate.puml).*

### 9.3 Hypotheses are premises, not axioms

The main theorems and the lifting lemma are stated in the form
$`\forall(\text{premises}).\ \text{premises}\Rightarrow\text{conclusion}`$: their per-family arms and
the (iii) transfer are universally-quantified antecedents (mechanized as Section-generalized `Variable`
/ `Hypothesis` declarations). A premise is discharged where the theorem is applied; it introduces no
global assumption and is not an `Axiom`. The non-vacuity witnesses — `swapdemo_base_finite_trace_opcorr`,
`inoutdemo_nested_finite_trace_opcorr`, `beta_cascade_is_nonvacuous`, and
`optimal_shares_where_sound_separates` — each *discharge* those premises at a concrete instantiation, so
each implication is satisfiable rather than true by an empty antecedent.

### 9.4 The certificate corpus

Across the two development libraries, **310** proof-term audits each report closure under the ambient
context — **161** in `rho_bridge/theories` and **149** in `advanced_automata/theories` — confirming
§9.1 over the whole corpus.

---

## 10. Scope and limitations

This article claims exactly what the results establish, and no more. The following bound the scope
transparently.

1. **The de-Bruijn numeral-dispatch abstraction.** The substitution rewriting system models the
   indices $`j, c, k, n`$ as natural numbers and folds the numeral dispatch (`^cmp` / `^pred`) into the
   $`\mathtt{if}\ n < c`$ and $`\mathtt{match}\ n\ ?=\ j`$ conditionals of the head rules. This is a
   sound, standard abstraction — the dispatch is a bounded, deterministic, terminating sub-cascade
   computing comparison and predecessor — and it is the *more* rigorous choice: embedding Peano numerals
   as reducible subterms would force a non-monotone $`\min`$-interpretation and break the monotone SN
   measure (§6, Theorem 16). The concrete numeral receivers run end-to-end on the live reducer in the
   binder reducer tests, so the abstracted arithmetic is exercised concretely.

2. **Finite-execution scope.** The main theorems (Theorems 22 and 23) are finite-trace correspondences:
   they range over finite label-indexed traces $`\mathrm{steps}\,s\,\mathit{ls}\,s'`$. Divergent (infinite)
   executions lie outside their scope; the object-$`\beta`$ layer is intentionally non-terminating
   (recursion may create new redexes), while the *inner* substitution layer established here is confluent
   and terminating (§6).

3. **The AC and matching layers are match-logic, not per-step-correspondence arms.** The AC bundle
   (Proposition 15) and the matching layer (Propositions 1, 3, 5; Lemmas 2, 4) are match-logic, atomicity,
   and guard results. They enter the capstone as `gstep` well-formedness and as premises of obligation
   (iii) (§7.4) — not as independent forward / backward arms. The seven arms that do feed the
   correspondence are the operational firing results (Theorems 7, 8, 12, 19; Propositions 11, 13; Lemma
   14 with Proposition 15).

4. **Channels are modelled structurally.** The channel-naming map is an injective constructor
   (`Channel := RootChan | ChildChan`, `option (nat * nat)` keys), not the concrete Rholang `GPrivate`
   string. The operational faithfulness of the emitted `Par` to the abstract fold is witnessed by the
   runtime tests (doc 23); the results here establish the *decision logic* and the *correspondence*, and
   the runtime layer establishes the RSpace realization.

5. **Families extend additively.** The seven-arm split is open: a new rule family adds one family
   constructor, one pair of premises, and one landed firing result, leaving every existing certified
   result unchanged (the companion-witness idiom of Theorem 23). The current corpus establishes the seven
   landed families.

Semantic predicates do not fire on the reducer (they are off-machine by construction, INV-14,
`semantic_predicates_emit_no_comm`), and no hidden constant-time substitution is claimed (the cascade
pays the honest cost of doc [19](19-in-rho-binder-beta-substitution.md) §8).

---

## References

See [references.md](references.md). Primary sources for this article:
[KNOTTED-TOPOI-2026](references.md#knotted-topoi-2026) (the `ob:opcorr` obligation and the base-rewrite
desugaring); [OPTIMAL-CHANNEL-NAMING-2026](references.md#optimal-channel-naming-2026) (the $`tc(K)`$
optimal channel scheme and the same-CLTS claim established here as Theorem 6);
[COQ-ROCQ](references.md#coq-rocq) (the mechanization target);
[DEBRUIJN-1972](references.md#debruijn-1972) (the nameless indices and the reduct $`b[a/0]`$); and
[EXPLICIT-SUBST-1991](references.md#explicit-subst-1991) /
[CURIEN-HARDIN-LEVY-1996](references.md#curien-hardin-levy-1996) (the $`\lambda\sigma`$ substitution and
shift lineage and its confluence and termination theory, the basis for Theorems 16–18).
