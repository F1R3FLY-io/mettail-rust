# Evidence-Driven Early Pruning — 01: SOTA Survey of Filtering Approaches

> **Status:** research survey (2026-06-11), foundation document for the pgmcp #21
> evidence-driven-early-pruning design program.
> **Companion documents:**
> - `00-existing-mechanisms-inventory.md` — the 48-mechanism inventory of what already ships.
> - `../parser-fv/evidence-driven-early-pruning.md` — the user-directed principle (levers A/B/C).
> - `../parser-fv/evidence-gated-cross-cat-dispatch.md` — the active Phase 5A target.
> **Mandate this survey serves (verbatim, session 2026-06-10):** *"Alternatives leave
> the live set ONLY via definite, monotone-under-continuation evidence (never
> heuristics). Weights ORDER, never prune. Ambiguity is first-class. Budgets report,
> never silently prune."*
> **Method note:** every surveyed mechanism is tagged with its guarantee class:
> `[DEFINITE]` sound refutation (provably cannot be in any accepting parse) ·
> `[ORDER-ONLY]` reorders work, exact result set preserved ·
> `[EXACT-COLLAPSE]` quotient of observationally-equivalent states, no loss ·
> `[UNSOUND-PER-SE]` can drop viable alternatives (only its sound variant is usable here) ·
> `[REPAIR]` input/state modification for recovery, not evidence ·
> `[LANGUAGE-DEFINING]` changes the accepted language by declaration (sound w.r.t. the *intended* language).

---

## 0. The filtering frame: making the Kalman inspiration exact

### 0.1 The Bayes-filter dictionary

The Kalman filter [K60] is the closed-form special case (linear dynamics, Gaussian
belief) of the general Bayes filter [Sar13]: maintain a belief `b_i(x) = P(x_i | o_1..o_i)`,
alternate a **predict** step through the dynamics and an **update** step that multiplies
by the observation likelihood and renormalizes. For discrete state spaces this is the
HMM **forward algorithm** [R89]. The mapping onto an online parser is exact, not
metaphorical:

| Bayes/Kalman filtering            | WPDA walker (PraTTaIL)                                       |
|-----------------------------------|--------------------------------------------------------------|
| state `x_i`                       | parser configuration: ⟨dispatch state, stack, SPPF cursor⟩   |
| belief `b_i` (support + weights)  | frontier: live `BranchCursor` set + `LexicographicWeight`s   |
| dynamics / predict step           | ε-moves: prediction, closure, delegate dispatch, reductions  |
| observation `o_i`                 | next token (or lex-DAG slice — a *set-valued* observation)   |
| likelihood `O(o_i \| x)`          | shift admissibility: `{0,1}` symbolic, `[0,1]`/semiring weighted |
| posterior support `{x : b_i(x)>0}`| cursors not yet refuted                                      |
| **zero posterior** ⇒ drop         | **definite refutation** ⇒ remove alternative (the only legal drop) |
| re-weighting of survivors         | weight/order update (never a drop)                           |
| innovation / residual             | surprisal `−log P(o_i \| o_1..o_{i−1})` per cursor family    |
| filter divergence alarm           | budget **report** (AmbiguityBudget, MAX_STEPS, REALIZE_CAP)  |

Two flavors of refutation must be distinguished, because they sit at different places
in the filtering picture:

1. **Past-conditioned refutation** — the configuration is inconsistent with the tokens
   already read. This is the native filter update; the walker already performs it
   (failed shift, PathMap trie miss, lex soft-fail). Nothing new is needed here.
2. **Future-conditioned refutation** — the configuration is consistent with the past
   but **no accepting continuation exists** over (an abstraction of) the *remaining*
   input. In filtering terms this is not filtering but **smoothing**: it uses the
   backward message. Define the backward indicator
   `β_i(x) = [∃ suffix-run from configuration x over tokens i..n that accepts]`.
   Exact `β` is the parse itself (circular). The engineering content of this whole
   survey is: **sound over-approximations `β̂ ⊇ β` are cheap, and `β̂(x) = 0` is a
   definite, monotone refutation** — if even the over-approximation admits no
   accepting continuation, the exact system certainly does not.

Every "novel" candidate in §6 is an instance of this one statement at a different
abstraction level; FOLLOW sets are its 1-token shadow; A* outside estimates are its
order-only (weighted) cousin; inside–outside is the fully exact (and fully expensive)
smoother [Goo99].

### 0.2 What the *Kalman* filter specifically contributes: conjugate belief families

The Kalman filter is tractable because Gaussians are **closed under the predict and
update operators** — the belief never leaves a finitely-parameterized family. The
rigorous parsing analog exists and is classical: for pushdown dynamics, **regular sets
of configurations are closed under backward/forward reachability** (`pre*`/`post*` of a
regular configuration set is regular, computable by P-automaton **saturation** in
polynomial time) [BEM97][EHRS00][Sch02]. So the "conjugate family" for a PDA's belief
support is *regular configuration languages*, and the saturation algorithm is the
parser's Riccati equation: a fixed, offline computation that makes every online update
a constant-time table/automaton step. The weighted generalization (semiring-annotated
`pre*`, meet-over-all-paths) is the WPDS framework of Reps–Schwoon–Jha–Melski [RSJM05]
— which is the *native formalism of this parser* (the walker is a weighted PDA).
Candidate A in §6 is exactly this observation operationalized.

The observability question of control theory ("can this state ever influence an
accepted output?" — the observability Gramian) becomes Boolean here:
`x` is *dead* iff `x ∉ pre*(AcceptingConfigs)`. A dead configuration has zero posterior
under **every** continuation — the strongest possible definite evidence, computable
offline.

### 0.3 The mandate, formalized as an abstract-interpretation contract

Let `α` abstract the remaining input `w_{i..n}` (examples: `α = ⊤` ignore it;
`α = Parikh class bitmask`; `α = the suffix DFA state of a regular over-approximation`;
`α = w_{i..n}` exactly). Soundness and monotonicity become one proof obligation pair
in the Galois-connection style of Cousot & Cousot [CC77]:

- **(SOUND / definite)** `refute(x, α(w)) = true ⇒ ∀ w' ∈ γ(α(w)): no accepting run from x on w'`.
  In particular the actual suffix `w ∈ γ(α(w))`, so the dropped alternative is in no
  accepting parse of the *actual* input.
- **(MONOTONE under continuation)** advancing the input only *refines* the abstraction
  (`γ(α(w_{i+1..n})) ⊆ γ(α(w_{i..n}))` after consuming a token), so a refutation once
  established never has to be retracted. No un-refute, no oscillation, no re-spawn.

Weights live below this line: define the support homomorphism
`supp : W → 𝔹, supp(ω) = [ω ≠ 0̄]`. Any operation that changes weights but preserves
`supp` (re-prioritization, demotion, admissible-heuristic ordering) **cannot** change
the accepted set — this is the one-line soundness argument for every `[ORDER-ONLY]`
mechanism, and it is the same observation that makes provenance polynomials work
(§4.2): the accepted set is the Boolean image of the weight semiring [GKT07][Goo99].

Note the mandate is *stronger* than NLP "exact search": Klein–Manning-style exactness
guarantees only the argmax (or k-best list) is correct; PraTTaIL must preserve the
**entire accepting set** (`Ambiguous` is first-class). Mechanisms that are "sound for
Viterbi" (drop things provably not in the *best* parse) are therefore still only
`[ORDER-ONLY]` material here: they may schedule extraction, never delete forest.

---

## 1. Established exact methods (the symbolic instantiation)

### 1.1 Lookahead tables: LL(k) / LR(k) / LALR / IELR — `[DEFINITE]`

Knuth's LR(k) construction [Knu65] is the canonical compile-time future-conditioned
refutation: an action is removed from a state's table entry exactly when **no viable
suffix** of length-k justifies it. The viable-prefix property guarantees online
earliest-error detection: a canonical LR parser (and Earley, §1.3) rejects at the first
token that cannot be extended to a sentence — i.e., the filter support never contains
a past-inconsistent configuration. DeRemer–Pennello [DP82] compute LALR(1) lookahead
sets efficiently; LALR state-merging can delay error detection by (only) reductions but
never accepts outside `L(G)`. Pager's method [Pag77] merges canonical LR(1) states
while preserving language; Denny–Malloy's **IELR(1)** [DM10] shows Pager-style merging
*loses* canonical-LR power when conflicts are resolved by precedence declarations, and
repairs it — i.e., even at the table level, "merging beliefs" must be proven not to
destroy evidence. Isradisaikul–Myers [IM15] generate **counterexamples from parsing
conflicts** (now in Bison): the refutation dual — when evidence is *insufficient*, the
tool exhibits the ambiguity witness instead of letting the grammar author guess.
PraTTaIL's PathMap-trie prefix dispatch is in this family (LL(k)-style definite
dispatch); the lesson to import is IELR's: every state/cohort merge needs a
no-evidence-loss theorem (which is what `CastDelegateMergeBound.v` already does for
the delegate merge).

### 1.2 GLR: forking as belief support, packing as exact marginalization — `[EXACT-COLLAPSE]`

Lang [Lan74] and Tomita [Tom86] keep *all* LR alternatives: the graph-structured stack
(GSS) is precisely a compact factored representation of the belief support, and **local
ambiguity packing** (merge subtrees with identical ⟨nonterminal, span⟩) plus GSS state
re-merging are *exact marginalizations* — quotients by observational equivalence that
lose no parse. Billot–Lang [BL89] established the shared-forest (SPPF) representation;
Rekers [Rek92] the practical GLR forests; Scott–Johnstone repaired Tomita's ε-case with
RNGLR [SJ06] and recast the whole family as GLL [SJ10] with the same GSS sharing.
Tree-sitter inherits exactly this architecture for IDE parsing (GLR + Wagner–Graham
incrementality) [TS][WG98].
**Relevance:** the cursor-merge direction already chosen for the cast-delegate blowup
(`CastDelegateMergeBound.v`, K^d → S·d) *is* GSS/packing — the literature's verdict is
unambiguous: merge first, so that every per-configuration evidence check (§6) is paid
once per equivalence class, not once per cursor. This is also the SMC literature's
"Rao-Blackwellization" (§3) under another name.

### 1.3 Earley: prediction/completion as constraint propagation — `[DEFINITE]`

Earley items [Ear70] are exactly the deduction-rule instantiation of the filter:
*prediction* introduces only items demanded top-down (goal-directed filtering — see
§4.1 for the magic-sets identity), *scanning* is the observation update, *completion*
propagates proven constituents bottom-up. The correct-prefix property is the
past-conditioned refutation guarantee. Aycock–Horspool [AH02] precompute nullability
to remove the ε-bookkeeping; **Leo** [Leo91] memoizes right-recursive completion chains
("transitive items"), achieving linear time for all LR-regular grammars — an
`[EXACT-COLLAPSE]` of completion chains directly relevant to PraTTaIL's chain-absorption
(H3) and the 342k-no-op-step pathology (§6.7): Leo items are the proof that *stepping
through* a deterministic continuation chain can be replaced by a single precomputed
jump with zero loss. **Marpa** [Keg-M][Keg-L] packages Earley+Leo+AH and — the part to
import — exposes the per-position **expected-terminal set** as a first-class query;
its "Ruby Slippers" technique [Keg-RS] then *changes the input* to match expectations
(error recovery / DSL slop): `[REPAIR]`, driven by definite evidence but not itself
evidence. The expected-terminal interface is the user-visible face of candidate A/B
tables and essentially free once those tables exist.

### 1.4 SGLR disambiguation filters — `[LANGUAGE-DEFINING]`, sound w.r.t. the intended language

Scannerless GLR [Vis97] composes lexing into the grammar (cf. PraTTaIL's lex DAGs) and
controls the resulting ambiguity with **declarative filters** [BSVV02]: follow
restrictions (`-/-`, longest-match: a reduction is *refuted* if the next character is
in the restriction — a 1-character future-conditioned gate executed at reduce time),
**reject productions** (language subtraction — "prefer keywords"; PraTTaIL's lex-fork
keyword reservation, commit `51d57c91`, is exactly a reject-production mechanism),
priorities/associativity (deep priority conflicts handled statically in [SdSV18]),
and preferences. Economopoulos–Klint–Vinju [EKV09] show these filters dominate SGLR
performance — early, cheap filter evaluation is the difference between usable and
unusable generalized parsing. These filters *define* the language rather than
approximate it; they are sound because the grammar author declares them as semantics —
the correct home in PraTTaIL is grammar-level guard/disambiguation declarations, never
runtime heuristics.

### 1.5 Extended-window evidence: noncanonical LR, ALL(*), data-dependent grammars

Noncanonical methods (NSLR(1) [Tai79]) postpone a conflicted decision, parse the
*right context* first, and return — widening the evidence window beyond k tokens while
staying `[DEFINITE]`. ANTLR's ALL(*) [PHF14] (after LL(*) [PF11]) is the practical
two-stage architecture: a cheap **SLL** DFA-cached prediction first; if (and only if)
it reports a conflict, retry with full-context **LL** simulation — a *sound
over-approximation with exact fallback*, the same shape as candidate D's coarse gate.
Yakker's data-dependent grammars [JMW10] make semantic predicates and binding part of
the formalism: constraints evaluated on definite values refute alternatives
`[DEFINITE]` (PraTTaIL's typed-sink/`into_term::<T>()` evidence is of this kind; the
directive is to move it earlier, §6.2/B).

### 1.6 Derivative parsing: the belief update in its purest symbolic form — `[DEFINITE]`

Brzozowski derivatives [Brz64] make "consume one token" a *language quotient*:
`D_t(L) = {w : tw ∈ L}`. Might–Darais–Spiewak [MDS11] extend this to CFGs (laziness +
memoization + fixpoints), Adams–Hollenbeck–Might [AHM16] prove cubic worst-case. The
filter reading: the parser state *is* the residual language; **emptiness of the
derivative is refutation**; nullability is acceptance. No practical engine for our
purposes, but the cleanest specification language for FV: candidate proofs can state
"configuration x is refutable iff `Residual(x) ∩ γ(α) = ∅`" and every concrete gate is
an under-approximation of that emptiness test.

### 1.7 Parsing as intersection: the lex-DAG connection — `[DEFINITE]` framework

Bar-Hillel–Perles–Shamir [BPS61]: CFL ∩ regular is CFL, constructively. Lang [Lan88]
applied it to word lattices ("parsing incomplete sentences") — PraTTaIL's lex
DAGs/lattices are exactly this: the parse is `G ∩ Lattice`, and every §6 gate is an
**emptiness test of an abstracted intersection**. Nederhof–Satta [NS03] give the
weighted version (probabilistic parsing as intersection). This is the umbrella theorem
under which candidates A, B, D are all instances: replace one factor of the
intersection by a sound abstraction; if the abstract intersection is empty, so is the
exact one.

---

## 2. The probabilistic filtering family (the Kalman analogy made literal)

### 2.1 Prefix probabilities: Stolcke's Earley = the forward algorithm for CFGs

Jelinek–Lafferty [JL91] computed prefix probabilities for SCFGs bottom-up;
**Stolcke** [Sto95] computes them *incrementally, left-to-right, inside Earley*:
the **forward probability** `α_i` of an item is exactly the Bayes-filter belief mass,
and `P(w_{i} | w_{1..i−1}) = α_i / α_{i−1}` is the filter's normalization constant.
The technically load-bearing detail: left-recursive/unit-production prediction loops
make the predict-step sum infinite; Stolcke closes them **offline** with the
left-corner matrix inversion `R_L = (I − P_L)^{−1}` — the same "closed semiring /
Newton iteration" move as PraTTaIL's `InsideWeightSccClosure.v` (Newton-SCC cyclic
closure in dovetail) and the general Newtonian program analysis of
Esparza–Kiefer–Luttenberger [EKL10], with Mohri's k-closed semiring shortest-distance
framework [Moh02] as the automata-side generalization. **Guarantees:** the forward pass
is *exact*; `α = 0̄` coincides with the symbolic dead-item case `[DEFINITE]`; any
*threshold* on `α > 0` is `[UNSOUND-PER-SE]`. Usable here as: priorities for the work
queue (candidate C) and surprisal reporting (candidate E) — never as a drop criterion.

### 2.2 Surprisal = the innovation residual

Hale [Hal01] read Stolcke's normalization constant as the psycholinguistic **surprisal**
`−log P(w_i | w_{1..i−1})`; Levy [Lev08] generalized it to expectation-based
comprehension. This is verbatim the Kalman *innovation*: how much the observation
deviates from the prediction. Per-cursor(-family) surprisal is computable from weights
the walker already carries, and is the principled signal for candidate E's demotion —
`[ORDER-ONLY]` by the `supp`-homomorphism argument of §0.3.

### 2.3 Inside–outside, semiring parsing, weighted deduction

Inside–outside is forward–backward (smoothing) for grammars; Goodman's **semiring
parsing** [Goo99] unifies recognition/Viterbi/inside/counting as one deduction schema
parameterized by the semiring — the formal license for PraTTaIL's design where the same
walker computes Boolean support and lexicographic weights. Eisner–Goldlust–Smith's Dyna
[EGS05] is the engineering form (weighted Datalog with agenda). **Nederhof** [Ned03]
proves Knuth's lifted Dijkstra [Knu77] gives *exact* best-first weighted deductive
parsing for superior (monotone) weight functions — the theoretical foundation under
dovetail's already-proven exact extractor (`NBestExtraction.v`,
`EnumerationCompleteness.v`) and the correctness frame for candidate C at the *parser*
level. All `[ORDER-ONLY]` (exact answers, scheduled cleverly).

### 2.4 A* parsing: admissible cost-to-go = exact search — `[ORDER-ONLY]`

Klein–Manning [KM03] run Viterbi parsing best-first with priority
`inside(e) ⊗ outside-bound(e)` where the outside bound is **admissible** (never
underestimates the completion score): first dequeue of a goal item is provably the
exact Viterbi parse, worst-case cubic preserved. Estimates come from grammar
*projections* (summary/coarse grammars). Pauls–Klein extend to **hierarchical A***
(cascaded coarse projections whose exact outside scores bound the next level) [PK09a]
and **k-best A*** [PK09b]. The control-theory duality is exact: admissible
outside = optimistic cost-to-go (LQR value bound), inside = cost-so-far. For PraTTaIL:
this is the *ordering* half of the program — it composes with (never replaces) the
definite gates, and it is the disciplined version of "weights order work".

### 2.5 Coarse-to-fine: the sound and unsound halves — `[UNSOUND-PER-SE]` / sound variants

Charniak–Johnson [CJ05] prune with a coarse PCFG's *posteriors* then rerank;
Petrov–Klein [PK07] cascade the grammar's own hierarchical projections with per-level
posterior thresholds (τ tuned so empirical accuracy is unharmed). **No guarantee**: a
viable (even the best) constituent can fall below τ — empirically rare, formally
unsound, hence excluded here as a *drop* rule. The two sound siblings:
1. **Max-marginal / admissible-bound pruning**: if an *upper* bound on the best
   derivation through edge e is below the current best *complete* derivation, e is not
   in any optimal parse — sound for Viterbi-optimality (hierarchical A* is its lazy
   form [PK09a]); under PraTTaIL's full-set mandate this still only licenses extraction
   *ordering*, not forest deletion (§0.3).
2. **Sound coarse gates**: make the coarse level a *superset language* (regular
   over-approximation, §2.6/[Ned00]) — then coarse REJECT is `[DEFINITE]` refutation
   and coarse ACCEPT means "pay for the fine check". ALL(*)'s SLL→LL fallback (§1.5)
   is this pattern in production.

### 2.6 Regular over-approximation of CFGs — the sound coarse level — `[DEFINITE]` when superset

Nederhof [Ned00] surveys/refines constructions of finite automata from CFGs, both
subset and **superset** approximations (superset = the sound side for refutation), with
practical sizes for real grammars; Mohri–Nederhof [MN01] give the standard
transformation making any CFG *strongly regular* (self-embedding removed) — the
canonical superset automaton. Applications historically: speech-lattice filtering —
literally "filter the lattice through the over-approximation before the expensive
parser", which is the architecture candidate D imports per-configuration.

### 2.7 Beam, k-best, and exact frontier scheduling

Viterbi beam pruning (fixed-width frontier truncation) is `[UNSOUND-PER-SE]` — it is
the formal description of PraTTaIL's *forbidden* move (and of the WFST Viterbi beam the
inventory lists as deliberately unused for dropping). Sound members of the family:
**Huang–Chiang lazy k-best** [HC05] (Algorithm 3: exact k-best lists with near-constant
overhead in k — the model for lazy tail realization), **best-first beam search**
[MVC20] (provably the same results as beam search in minimal expansions — i.e., even
*chosen* truncation can be scheduled optimally), and cube pruning [Chi07] as the
explicitly-approximate contrast case. Lesson: laziness (defer) + exact priority
(Knuth/A*) recovers almost all of beam's speed without its loss; truncation itself is
never needed for correctness — only for *budgets*, which in PraTTaIL **report**.

---

## 3. Particle filters / sequential Monte Carlo: the cautionary branch

Levy–Reali–Griffiths [LRG08] adapted the particle filter to incremental parsing as a
*cognitive* model: beliefs approximated by N sampled derivations, resampled per word.
The crucial property for us is their **headline result inverted**: the model's
*successes* are human *failures* — garden-pathing and **digging-in** effects arise
precisely because resampling *loses support* (a viable analysis' particle count hits
zero and can never recover; recent follow-up work analyzes these amplified garden
paths and digging-in as algorithmic signatures of SMC [AGP26]). In other words, the
psycholinguistic evidence *for* particle filters is the engineering evidence *against*
them for a no-loss parser: resampling = silent pruning = exactly the forbidden move
(`weight_drop_can_lose_valid_alternative`).

What survives the mandate:
- **Resampling-as-reordering**: keep the full support in the frontier store; apply
  resampling only to the *scheduling distribution* (which cursor families get steps
  next). Multinomial/systematic resampling [DC05] then permutes work order —
  `[ORDER-ONLY]` by §0.3 — and the "particle weights" are just normalized cursor
  weights.
- **Effective sample size (ESS)** [KLW94] `ESS = (Σw)² / Σw²` over normalized frontier
  weights: the standard degeneracy alarm. This is a *principled, dimensionless* trigger
  for PraTTaIL's budget **reports** (a 16-cursor frontier whose ESS ≈ 1.2 is one
  dominant parse plus noise — report and keep going lazily; ESS ≈ 14 is genuine
  ambiguity — report differently). Diagnosis, never deletion.
- **Rao-Blackwellization** (marginalize analytically the part of the state you can):
  in parsing terms, *pack/merge what is observationally equivalent and only "sample"
  (schedule) over genuinely divergent residue* — the SMC-theoretic justification for
  GSS merging and the cohort/cursor-merge direction (`CastDelegateMergeBound.v`).
- Diversity-preserving selection (e.g. diverse beam search [VCS18]) is still
  truncation; usable only as a *scheduling* diversifier, same caveat as resampling.

---

## 4. Constraint propagation, deduction, and provenance: evidence as algebra

### 4.1 Parsing as deduction; Earley prediction = magic sets — `[DEFINITE]`

Pereira–Warren [PW83] and Shieber–Schabes–Pereira [SSP95] present parsers as inference
systems (items = facts, steps = rules); Sikkel's parsing schemata [Sik97] make the
parser-design space a lattice of such systems related by refinement — the right
vocabulary for proving two PraTTaIL pipeline stages equivalent. The classical
database connection: **Earley prediction is the magic-sets / demand transformation of
the bottom-up (CYK) program** — top-down goal filtering compiled into bottom-up
evaluation [BMSU86][BR91]; subsumptive demand variants strictly dominate
[TL11]. Reading for PraTTaIL: "don't generate superfluous alternatives" (the user's
lever 1) *is* demand transformation — the delegate-dispatch gate of Phase 5A is a
magic-set predicate on the delegate rule ("only dispatch `CrossCatLhs{C}` if a
C-sourced trigger is demanded by the continuation *and* supplied by the lookahead").
Demand transformations carry exactly the right theorem shape: query-equivalence
(no answer lost, irrelevant work avoided).

### 4.2 Provenance semirings: refutation = provenance ≡ 0̄ — `[DEFINITE]` framework

Green–Karvounarakis–Tannen [GKT07]: annotate facts with elements of a commutative
semiring; derived facts carry **provenance polynomials**; specializing the semiring
recovers Boolean truth, counting, probability, why-provenance. For parsing this is
Goodman's [Goo99] result database-theoretically generalized: the SPPF *is* the
provenance structure of the item "this span parses as X". Consequences for the
mandate: (1) an alternative is refutable iff its provenance polynomial is identically
`0̄` under **every** valuation of future facts — definite evidence is provenance-level,
weight-independent; (2) any weight transformation with `supp(ω)` preserved cannot
change the accepted set (§0.3) — the one-line FV lemma for all ordering mechanisms;
(3) absorptive/idempotent semirings characterize when provenance can be *truncated*
safely — the algebraic home of "which dedups are sound" (the `-3!`/semantic-hash
lesson: Display-equality was a non-injective abstraction of provenance; semantic_hash
restored injectivity on the observable quotient).

### 4.3 (Weighted) pushdown reachability: the parser's own model-checking theory — `[DEFINITE]`

Bouajjani–Esparza–Maler [BEM97] and Esparza–Hansel–Rossmanith–Schwoon [EHRS00]:
for a pushdown system P and a *regular* set C of configurations, `pre*(C)` and
`post*(C)` are regular and computable by **saturating a P-automaton** — `pre*` in
`O(|Q|²·|Δ|)` time. Schwoon's thesis [Sch02] is the standard reference; Reps et al.
[RSJM05] add semiring weights (meet-over-all-paths values = generalized dataflow).
For PraTTaIL this is not an analogy but a type match: the walker is a WPDA; "is this
cursor's configuration able to reach an accepting configuration?" is a `pre*` query;
the offline saturation is grammar-only (codegen-time), and the online check is
incremental: annotate each pushed frame with the P-automaton state reached while
reading the stack — membership maintenance is O(1) per push/pop. Candidate A
operationalizes this; the weighted variant simultaneously yields *admissible*
cost-to-go bounds for candidate C (the weight of the saturated transition is exactly
the best-case completion weight — A*'s heuristic for free, from the same table).

---

## 5. Incremental and predictive evidence in production parsers

- **Valid-prefix property** parsers (canonical LR, Earley, GLL/GLR variants) refute at
  the earliest inconsistent token — the online half of the program; PraTTaIL already
  has this via dispatch/lex evidence. `[DEFINITE]`
- **Wagner–Graham incremental parsing** [WG98][Wag98]: optimal subtree reuse under
  edits; evidence bookkeeping is *spatial* (which regions' conclusions survive an
  edit) — the same monotone-evidence discipline applied to the edit dimension;
  basis of tree-sitter [TS]. `[EXACT-COLLAPSE]` across edits.
- **Tree-sitter error recovery**: GLR-style *parallel recovery attempts* with costs,
  compared a few tokens later [TS-ER]; **GLR\*** noise-skipping [LT93] and
  **permissive grammars / derived recovery rules** (de Jonge–Kats–Visser–Söderberg
  [JKVS12], with island grammars) are the systematic forms. All `[REPAIR]`: they *add*
  alternatives (modified inputs) under cost order — the precise dual of pruning, and
  correctly kept on the other side of the evidence ledger in PraTTaIL (recovery edges
  are weighted, reported, never confused with refutation).
- **Marpa events / expected-terminal sets** [Keg-M][Keg-RS]: the per-position evidence
  set as a *queryable API* (what tokens could continue?). PraTTaIL's
  `valid_continuations` WFST is the same object; §6's tables make it
  configuration-indexed rather than position-global.
- **ALL(*) SLL→LL** two-stage prediction [PHF14]: production proof that a sound
  over-approximate gate plus exact fallback is fast in practice (DFA cache hit rates
  dominate). The architecture template for candidate D.

---

## 6. Synthesis: candidate mechanisms for PraTTaIL

### 6.0 One unifying picture

All definite gates below are emptiness tests of `Residual(x) ∩ γ(α(suffix))` (§1.6,
§1.7) at four abstraction levels; all ordering mechanisms are weight-only (§0.3).

```
            abstraction of the remaining input (coarse → exact)
   ┌────────────────────┬──────────────────────┬─────────────────────┬───────────────┐
   │ α = ⊤  (ignore it) │ α = token-class      │ α = regular         │ α = exact     │
   │                    │     Parikh bitmask   │     over-approx DFA │     suffix    │
   ├────────────────────┼──────────────────────┼─────────────────────┼───────────────┤
   │ A: config liveness │ B: must-consume      │ D: residual-DFA     │ the parse     │
   │    x ∈ pre*(F)?    │    obligations ⊆     │    product gate     │ itself        │
   │                    │    available classes │                     │               │
   └────────────────────┴──────────────────────┴─────────────────────┴───────────────┘
        refutation strength →            cost →           (each level sound; each
                                                            subsumes the one left of it)
   orthogonal, weight-level (no drops):  C: forward-weight/A* ordering
                                         E: innovation demotion + ESS reporting
   substrate multiplier (no drops):      F: cursor-merge first (pay per class, not per cursor)
```

### 6.1 Candidate A — Configuration liveness via `pre*` saturation (the Boolean Kalman)

**Mechanism.** At codegen, saturate the P-automaton for `pre*(AcceptingConfigs)` of the
grammar's WPDA [BEM97][EHRS00][RSJM05]. At runtime, annotate every pushed stack frame
with the P-automaton state; a cursor is **dead** the instant its ⟨state, stack⟩ leaves
the regular live set. Optionally product with a *small* fixed lookahead alphabet
(1-token class) to recover classic FOLLOW as the table's last coordinate.
**Soundness.** `x ∉ pre*(F)` ⇒ no run from x reaches acceptance on *any* suffix
(theorem of the saturation construction). Monotone trivially: the test is
input-independent; transitions only move within/out of the live set, and "out" is
permanent for that cursor (dead configurations have no successors in `pre*(F)`).
**Precompute.** `O(|Q|²·|Δ|)` saturation once per grammar at macro-expansion; tables
baked like FIRST/FOLLOW today. **Per-token/per-step.** O(1) amortized (state carried on
frames; one table lookup per push/dispatch).
**What it kills.** The portion of the **342k no-op steps** spent stepping configurations
that can no longer accept *anything* (dead-by-structure cursors detected at the
transition that kills them, not at EOI); the **ProcX root fan**'s structurally-dead
members at dispatch time (those whose death is input-independent); steady frontier
pressure against the **16-cursor saturation**. It does *not* discriminate
input-dependent death (B/D's job). **Bonus:** the weighted saturation simultaneously
yields admissible completion-weight bounds = candidate C's heuristic from the same
table [RSJM05][KM03].
**FV obligation** (model first, per mandate): `PreStarLiveness.v` —
`saturation_sound`/`saturation_complete` (x ∈ pre*(F) ⇔ ∃ accepting continuation),
`refute_definite`, `frame_annotation_correct` (incremental membership = automaton run),
`monotone_under_continuation`.

### 6.2 Candidate B — Suffix token-class obligations (Parikh gate; generalizes the shipped trigger gate)

**Mechanism.** Offline: for every grammar symbol/rule-position compute
`must(·)` = the set of token *classes* that **every** terminal yield must contain
(fixpoint: `must(t)={class(t)}`; `must(A) = ⋂_{A→σ} ⋃_{s∈σ} must(s)`; nullables give ∅;
≤|classes| Kleene iterations, trivial at codegen). A configuration's obligation is the
⋃ of `must` over all remaining stack-frame obligations. Online: one backward O(n) scan
(or backward DP over the lex DAG, O(|E|) — union over lattice paths, sound for any path
[Lan88]) gives `S_i` = bitmask of classes present in the remaining input — monotonically
shrinking. **Refute x iff `must(x) ⊄ S_i`** — one u64/u128 AND per check.
**Soundness.** Necessary-condition refutation: any accepting continuation's yield
contains every obligated class (induction on the derivation = `must_consume_sound`);
if a class is absent from every remaining lattice path, no continuation exists.
Parikh's theorem [Par66][EGKL11] is the umbrella (this is the ⊆-on-supports shadow of
the semilinear image). **Monotone:** `S_i ⊇ S_{i+1}` and `must(x)` fixed per
configuration ⇒ refutation persists; new obligations only *grow* along a derivation.
**Precompute.** O(|G|·|classes|) offline + O(n) per input. **Per-check.** O(1).
**What it kills.** This is the **direct generalization of the shipped
FIRST(infix-trigger) lookahead gate** (the 1-token window becomes the whole suffix):
the **cast-compare delegate fan** dies wherever no `==`/`>=`-class token remains
(`int(3)` at EOI, `int(3) + 3` with no comparison anywhere — dispatch *zero*
cross-cat delegates instead of K); the **22-alt bare-var fan**'s members whose
alternative requires an absent literal class (collection closers, keyword operators)
are refuted at spawn; the **ProcX root fan** loses every category whose obligatory
keyword/sigil classes are absent from the 5-token input; fewer spawns ⇒ the
**16-cursor budget** stops saturating on trivial inputs. Limit: cannot see *order*
(trigger present but only *before* the operand — D's job).
**FV obligation:** `ParikhObligationGate.v` — `must_consume_sound`, `gate_no_loss`
(refuted ⇒ not in any accepting parse of the actual suffix), `gate_monotone`,
`generalizes_trigger_gate` (the shipped gate = 1-token projection of this gate); slots
into the planned `evidence_gated_delegates` refinement of `CastDelegateMergeBound.v`.

### 6.3 Candidate C — Forward-weight priority with admissible completion bounds — `[ORDER-ONLY]`

**Mechanism.** Use Stolcke-style forward weights [Sto95] (in the existing lexicographic
semiring — cyclic predict-closures already solved by the project's Newton-SCC closure
[EKL10], mirroring `R_L = (I−P_L)^{−1}`) as the work-queue priority, optionally
sharpened by admissible completion bounds from candidate A's weighted saturation table
(= grammar-projection outside estimates [KM03][PK09a]); extract lazily best-first
(Knuth's algorithm; exactness per [Knu77][Ned03] — the same theorem family already
proven for dovetail in `NBestExtraction.v`/`EnumerationCompleteness.v`).
**Soundness.** Pure `supp`-preserving re-prioritization (§0.3): the accepted set is
untouched by construction; with admissible bounds, first-goal-dequeued is exact-best
[KM03] — so the *winner* is realized first and the ambiguity tail is materialized only
on demand (the laziness lever). **Precompute.** Reuses A's table; else per-grammar
projection weights. **Per-step.** O(log frontier) heap ops (already paid).
**What it improves.** The **22-alt bare-var fan**: the bare `Var`-in-start-category
reading is realized first; the injection-wrap tail stays an unforced lazy frontier
(BareVarFanQuotient.v's report quotient already handles the inference layer). The
**16-cursor saturation**: budget hits become "the tail was never scheduled" instead of
"the frontier overflowed". Kills nothing — by design.
**FV obligation:** `ForwardOrderOnly.v` — `ordering_preserves_accepted_set` (one-liner
via the support homomorphism), `admissible_bound_exact_first_goal` (port of the
dovetail ORDER theorem to the walker's queue).

### 6.4 Candidate D — Sound coarse gate: regular residual over-approximation — `[DEFINITE]`

**Mechanism.** Offline, per category C build a *superset* automaton `A_C` with
`L(A_C) ⊇ L(C)` (Mohri–Nederhof strongly-regular transformation [MN01][Ned00]) over
token *classes*. Online, each cursor tracks the DFA state of the over-approximated
**residual**: top frame's `A_C` state, with each pushed frame storing the entry state
for the continuation automaton (compositional: residual of a configuration =
concatenation of frame remainders; on pop, resume the saved state — O(1) per
push/pop). A cursor whose residual DFA has no path to acceptance over the *remaining
suffix-class string* (checkable incrementally, or against the suffix-class DFA product)
is **refuted**.
**Soundness.** `L(A) ⊇ L(exact residual)` ⇒ abstract rejection implies exact rejection
(Bar-Hillel emptiness on the abstract intersection [BPS61][Lan88]). **Monotone:** DFA
state advances deterministically with consumed tokens; "no accepting path over what
remains" can only stay true as the remainder shrinks.
**Cost.** The honest one: superset automata can blow up on deeply self-embedding
categories ([Ned00] reports practical sizes for NL grammars; PraTTaIL's per-category
grammars are small); per-token O(1) per *merged* cursor class (hence: after F).
**What it kills (beyond B).** Order-sensitive death: `== int(3)` (trigger present but
*behind* the cursor) — B passes, D refutes; the residue of the **342k no-op steps**
whose configurations are input-dependently dead; the **ProcX fan** members whose
category over-approximation rejects the prefix-to-suffix class string outright.
Strictly subsumes B (B is the Parikh image of D) and A (A is D with `α = ⊤`) — but
stage it *last*: it is the most powerful and the most expensive, and ALL(*)'s lesson
[PHF14] is that the cheap gate catches most of the kill volume.
**FV obligation:** `RegularResidualGate.v` — `overapprox_superset`, `reject_definite`,
`frame_state_compositional`, `monotone_under_continuation`.

### 6.5 Candidate E — Innovation tracking + ESS degeneracy reporting — `[ORDER-ONLY]` + report

**Mechanism.** Per cursor family, accumulate surprisal `−log P(token | prefix)`
[Hal01][Sto95] and an *information-content* flag per step (did this cursor advance by
consuming, or only via ε/recovery edges?). Cursors whose recent window is
recovery/ε-only ("zero-innovation": observations explained without consuming evidence)
are **demoted** in the queue — never dropped (recovery is `[REPAIR]`, §5, and stays
available). Maintain frontier ESS [KLW94] over normalized weights; budget events
(AmbiguityBudget/MAX_STEPS) report ESS alongside the count, distinguishing "1 winner +
noise" from "genuine k-way ambiguity" (the digging-in failure mode of §3 is exactly
what *not* doing this looks like [LRG08][AGP26]).
**Soundness.** Demotion is `supp`-preserving (§0.3); ESS is pure diagnosis. **Cost.**
O(1) per step per cursor; one O(frontier) fold per report.
**What it improves.** The **342k no-op pathology** becomes *self-reporting* (zero-innovation
steps are the metric, demotion starves them of scheduler time); budget saturation
reports become actionable; nothing is lost by construction.
**FV obligation:** `InnovationDemotionOrderOnly.v` — `demotion_preserves_accepted_set`,
`ess_report_no_prune` (the report path mutates no frontier state).

### 6.6 Candidate F (substrate) — Merge first: packing/GSS as Rao-Blackwellization — `[EXACT-COLLAPSE]`

Not new — it is the already-chosen cursor-merge direction (`CastDelegateMergeBound.v`,
K^d → S·d) — but the filtering literature adds the staging argument: GLR packing/GSS
merging [Tom86][BL89][SJ06] = SMC Rao-Blackwellization (§3) = exact marginalization,
and **every per-configuration gate above amortizes per merged equivalence class**.
Merge is therefore not a competitor to A–E but their cost-divisor; implement the merge,
then gate the merged classes. The IELR lesson (§1.1) supplies the proof shape: a merge
is admissible iff it provably preserves the evidence (here: coverage; already the
`merge_covers` obligation in `CastDelegateMergeBound.v`).

### 6.7 Impact matrix (candidates × recorded pathologies)

Pathology data: `00-existing-mechanisms-inventory.md` (gap analysis; pgmcp #21, #307).
ProcX root fan = 12 cursors at root dispatch growing to the 16-cursor AmbiguityBudget,
dying today only at the premature-Accepted EOI filter; bare-var fan = 22 per-category
Var/injection alternatives (cf. `BareVarFanQuotient.v`); 342,699 no-op steps on a
5-token cast-then-infix input; frontier saturation = AmbiguityBudget report storms.

| Candidate (class)                  | ProcX root fan (12→16)            | 22-alt bare-var fan                | 342k no-op steps                     | 16-cursor saturation               |
|------------------------------------|-----------------------------------|------------------------------------|--------------------------------------|------------------------------------|
| A `pre*` liveness `[DEFINITE]`     | kills input-independent dead members at dispatch | minor (alts are mostly live-for-some-input) | **major**: dead configs stop stepping at the killing transition | steady pressure relief             |
| B Parikh obligations `[DEFINITE]`  | **major**: categories w/ absent obligatory classes refuted at spawn | **major**: alts requiring absent literal classes refuted at spawn | **major**: zero delegates dispatched when no trigger class remains (the Phase 5A gate, full-suffix form) | **major**: fans stop reaching 16 on trivial inputs |
| C forward/A* order `[ORDER-ONLY]`  | winner realized first; tail lazy  | **major**: start-category reading first, wrap tail deferred | scheduler starves no-op regions       | budget hit ⇒ "tail unscheduled", not overflow |
| D regular residual `[DEFINITE]`    | refutes order-impossible categories | refutes order-impossible alts     | kills the input-dependent residue A misses | strongest shrink, highest cost     |
| E innovation/ESS `[ORDER-ONLY]`    | diagnosis                          | diagnosis                          | **self-reporting + demotion**         | reports become semantically honest |
| F merge substrate `[EXACT-COLLAPSE]`| fan collapses to shared classes   | shared sub-state paid once         | per-class (not per-cursor) stepping   | K^d → S·d bound (already proven)   |

### 6.8 Staging and FV-first obligations (per the backwards-from-FV mandate)

Recommended order — each stage gets its zero-admission Rocq model **before** code,
each model proves the same four-theorem template
(`refute_definite`, `monotone_under_continuation`, `no_loss` w.r.t. the actual input,
`frontier_shrink` or `set_preservation` as applicable):

1. **F then B** — the already-planned Phase 5A pair: cohort-shared merge
   (`CastDelegateMergeBound.v`, committed) + `evidence_gated_delegates` modeled as the
   1-token projection of `ParikhObligationGate.v`, then generalized to the full-suffix
   bitmask. Cheapest, hits the live blocker (cast-then-compare), generalizes a shipped,
   proven mechanism — the "prefer the generalized solution" path.
2. **A** — codegen-time `pre*` saturation; native to the WPDA; its weighted table also
   feeds C. (`PreStarLiveness.v`.)
3. **C + E** — order-only pair; near-zero risk (support-homomorphism lemma), reuses the
   dovetail exactness proofs; turns budgets into ESS-graded reports. (`ForwardOrderOnly.v`,
   `InnovationDemotionOrderOnly.v`.)
4. **D** — the sound coarse-to-fine endgame, only if B+A leave measurable
   input-dependent dead stepping (measure first; ALL(*) experience says the cheap gates
   take most of it). (`RegularResidualGate.v`.)

Non-goals confirmed by the survey: posterior-threshold coarse-to-fine pruning [CJ05][PK07],
beam truncation, and SMC resampling of the *support* are `[UNSOUND-PER-SE]` and stay
excluded; tree-sitter-style recovery remains `[REPAIR]` on the other side of the
ledger; SGLR-style filters belong in grammar declarations (`[LANGUAGE-DEFINING]`),
never in the runtime.

---

## 7. References

Exact methods / tables / GLR / Earley:
- [Knu65] D. Knuth. *On the Translation of Languages from Left to Right.* Information and Control 8(6):607–639, 1965.
- [DP82] F. DeRemer, T. Pennello. *Efficient Computation of LALR(1) Look-Ahead Sets.* ACM TOPLAS 4(4):615–649, 1982.
- [Pag77] D. Pager. *A Practical General Method for Constructing LR(k) Parsers.* Acta Informatica 7:249–268, 1977.
- [DM10] J. Denny, B. Malloy. *The IELR(1) algorithm for generating minimal LR(1) parser tables for non-LR(1) grammars with conflict resolution.* Science of Computer Programming 75(11):943–979, 2010. https://www.sciencedirect.com/science/article/pii/S0167642309001191 (SAC'08 version: https://malloy.people.clemson.edu/publications/papers/sac08/paper.pdf)
- [IM15] C. Isradisaikul, A. Myers. *Finding Counterexamples from Parsing Conflicts.* PLDI 2015. https://www.cs.cornell.edu/andru/papers/cupex/ (in Bison: https://www.gnu.org/software/bison/manual/html_node/Counterexamples.html)
- [Lan74] B. Lang. *Deterministic Techniques for Efficient Non-deterministic Parsers.* ICALP 1974, LNCS 14.
- [Tom86] M. Tomita. *Efficient Parsing for Natural Language.* Kluwer, 1986.
- [BL89] S. Billot, B. Lang. *The Structure of Shared Forests in Ambiguous Parsing.* ACL 1989.
- [Rek92] J. Rekers. *Parser Generation for Interactive Environments.* PhD thesis, University of Amsterdam, 1992.
- [SJ06] E. Scott, A. Johnstone. *Right Nulled GLR Parsers.* ACM TOPLAS 28(4):577–618, 2006.
- [SJ10] E. Scott, A. Johnstone. *GLL Parsing.* ENTCS 253(7):177–189, 2010. (Also: Afroozeh, Izmaylova. *Faster, Practical GLL Parsing.* CC 2015 [AI15].)
- [Ear70] J. Earley. *An Efficient Context-Free Parsing Algorithm.* CACM 13(2):94–102, 1970.
- [Leo91] J. Leo. *A General Context-Free Parsing Algorithm Running in Linear Time on Every LR(k) Grammar Without Using Lookahead.* Theoretical Computer Science 82(1):165–176, 1991.
- [AH02] J. Aycock, R. N. Horspool. *Practical Earley Parsing.* The Computer Journal 45(6):620–630, 2002.
- [Keg-M] J. Kegler. *Marpa, A Practical General Parser: The Recognizer.* https://www.academia.edu/10341474/Marpa_A_practical_general_parser_the_recognizer ; [Keg-L] *What is the Marpa algorithm?* https://jeffreykegler.github.io/Ocean-of-Awareness-blog/individual/2011/11/what-is-the-marpa-algorithm.html ; [Keg-RS] *Marpa and the Ruby Slippers.* https://jeffreykegler.github.io/Ocean-of-Awareness-blog/individual/2011/11/marpa-and-the-ruby-slippers.html
- [Vis97] E. Visser. *Scannerless Generalized-LR Parsing.* Tech. Rep. P9707, University of Amsterdam, 1997. https://researchr.org/publication/Visser97-SGLR
- [BSVV02] M. van den Brand, J. Scheerder, J. Vinju, E. Visser. *Disambiguation Filters for Scannerless Generalized LR Parsers.* CC 2002.
- [EKV09] G. Economopoulos, P. Klint, J. Vinju. *Faster Scannerless GLR Parsing.* CC 2009. https://homepages.cwi.nl/~jurgenv/papers/CC-2009.pdf
- [SdSV18] L. E. de Souza Amorim, M. Steindorfer, E. Visser. *Towards Zero-Overhead Disambiguation of Deep Priority Conflicts.* 2018. https://arxiv.org/pdf/1803.10215
- [Tai79] K.-C. Tai. *Noncanonical SLR(1) Grammars.* ACM TOPLAS 1(2):295–320, 1979.
- [PF11] T. Parr, K. Fisher. *LL(\*): The Foundation of the ANTLR Parser Generator.* PLDI 2011; [PHF14] T. Parr, S. Harwell, K. Fisher. *Adaptive LL(\*) Parsing: The Power of Dynamic Analysis.* OOPSLA 2014.
- [JMW10] T. Jim, Y. Mandelbaum, D. Walker. *Semantics and Algorithms for Data-Dependent Grammars.* POPL 2010.
- [Brz64] J. Brzozowski. *Derivatives of Regular Expressions.* JACM 11(4):481–494, 1964.
- [MDS11] M. Might, D. Darais, D. Spiewak. *Parsing with Derivatives: A Functional Pearl.* ICFP 2011; [AHM16] M. Adams, C. Hollenbeck, M. Might. *On the Complexity and Performance of Parsing with Derivatives.* PLDI 2016.
- [BPS61] Y. Bar-Hillel, M. Perles, E. Shamir. *On Formal Properties of Simple Phrase Structure Grammars.* Z. Phonetik Sprachwiss. Kommunikationsforsch. 14:143–172, 1961.
- [Lan88] B. Lang. *Parsing Incomplete Sentences.* COLING 1988.
- [GJ08] D. Grune, C. Jacobs. *Parsing Techniques: A Practical Guide*, 2nd ed., Springer 2008. (General reference.)

Probabilistic filtering / A* / coarse-to-fine:
- [JL91] F. Jelinek, J. Lafferty. *Computation of the Probability of Initial Substring Generation by Stochastic Context-Free Grammars.* Computational Linguistics 17(3):315–323, 1991.
- [Sto95] A. Stolcke. *An Efficient Probabilistic Context-Free Parsing Algorithm that Computes Prefix Probabilities.* Computational Linguistics 21(2):165–201, 1995. https://aclanthology.org/J95-2002/
- [Hal01] J. Hale. *A Probabilistic Earley Parser as a Psycholinguistic Model.* NAACL 2001. https://dl.acm.org/doi/10.3115/1073336.1073357
- [Lev08] R. Levy. *Expectation-Based Syntactic Comprehension.* Cognition 106(3):1126–1177, 2008.
- [Goo99] J. Goodman. *Semiring Parsing.* Computational Linguistics 25(4):573–605, 1999.
- [EGS05] J. Eisner, E. Goldlust, N. A. Smith. *Compiling Comp Ling: Weighted Dynamic Programming and the Dyna Language.* HLT/EMNLP 2005.
- [Knu77] D. Knuth. *A Generalization of Dijkstra's Algorithm.* Information Processing Letters 6(1):1–5, 1977.
- [Ned03] M.-J. Nederhof. *Weighted Deductive Parsing and Knuth's Algorithm.* Computational Linguistics 29(1):135–143, 2003.
- [KM03] D. Klein, C. Manning. *A\* Parsing: Fast Exact Viterbi Parse Selection.* HLT-NAACL 2003. https://aclanthology.org/N03-1016/ , https://nlp.stanford.edu/pubs/klein2003astar.pdf
- [PK09a] A. Pauls, D. Klein. *Hierarchical Search for Parsing.* NAACL 2009. https://aclanthology.org/N09-1063.pdf ; [PK09b] *k-Best A\* Parsing.* ACL 2009. https://aclanthology.org/P09-1108.pdf
- [CJ05] E. Charniak, M. Johnson. *Coarse-to-Fine n-Best Parsing and MaxEnt Discriminative Reranking.* ACL 2005.
- [PK07] S. Petrov, D. Klein. *Improved Inference for Unlexicalized Parsing.* HLT-NAACL 2007. https://nlp.cs.berkeley.edu/pubs/Petrov-Klein_2007_Inference_paper.pdf (thesis: *Coarse-to-Fine Natural Language Processing*, UC Berkeley EECS-2009-116, https://www2.eecs.berkeley.edu/Pubs/TechRpts/2009/EECS-2009-116.pdf)
- [HC05] L. Huang, D. Chiang. *Better k-Best Parsing.* IWPT 2005. https://aclanthology.org/W05-1506/
- [Chi07] D. Chiang. *Hierarchical Phrase-Based Translation.* Computational Linguistics 33(2):201–228, 2007. (Cube pruning.)
- [MVC20] C. Meister, T. Vieira, R. Cotterell. *Best-First Beam Search.* TACL 8:795–809, 2020. https://aclanthology.org/2020.tacl-1.51/
- [Ned00] M.-J. Nederhof. *Practical Experiments with Regular Approximation of Context-Free Languages.* Computational Linguistics 26(1):17–44, 2000. https://aclanthology.org/J00-1003/
- [MN01] M. Mohri, M.-J. Nederhof. *Regular Approximation of Context-Free Grammars through Transformation.* In: Robustness in Language and Speech Technology, Kluwer 2001. https://link.springer.com/chapter/10.1007/978-94-015-9719-7_6
- [NS03] M.-J. Nederhof, G. Satta. *Probabilistic Parsing as Intersection.* IWPT 2003.

SMC / particle filtering:
- [LRG08] R. Levy, F. Reali, T. Griffiths. *Modeling the Effects of Memory on Human Online Sentence Processing with Particle Filters.* NIPS 21, 2008. https://papers.nips.cc/paper/3573-modeling-the-effects-of-memory-on-human-online-sentence-processing-with-particle-filters
- [AGP26] *Algorithmic Consequences of Particle Filters for Sentence Processing: Amplified Garden-Paths and Digging-In Effects.* 2026. https://arxiv.org/abs/2603.11412
- [KLW94] A. Kong, J. Liu, W. Wong. *Sequential Imputations and Bayesian Missing Data Problems.* JASA 89(425):278–288, 1994. (ESS.)
- [DC05] R. Douc, O. Cappé. *Comparison of Resampling Schemes for Particle Filtering.* ISPA 2005.
- [VCS18] A. Vijayakumar et al. *Diverse Beam Search.* AAAI 2018.

Deduction / provenance / pushdown reachability:
- [PW83] F. Pereira, D. Warren. *Parsing as Deduction.* ACL 1983.
- [SSP95] S. Shieber, Y. Schabes, F. Pereira. *Principles and Implementation of Deductive Parsing.* J. Logic Programming 24(1–2):3–36, 1995.
- [Sik97] K. Sikkel. *Parsing Schemata.* Springer, 1997.
- [BMSU86] F. Bancilhon, D. Maier, Y. Sagiv, J. Ullman. *Magic Sets and Other Strange Ways to Implement Logic Programs.* PODS 1986; [BR91] C. Beeri, R. Ramakrishnan. *On the Power of Magic.* J. Logic Programming 10(3–4):255–299, 1991; [TL11] K. T. Tekle, Y. A. Liu. *More Efficient Datalog Queries: Subsumptive Tabling Beats Magic Sets.* SIGMOD 2011.
- [GKT07] T. Green, G. Karvounarakis, V. Tannen. *Provenance Semirings.* PODS 2007.
- [BEM97] A. Bouajjani, J. Esparza, O. Maler. *Reachability Analysis of Pushdown Automata: Application to Model-Checking.* CONCUR 1997.
- [EHRS00] J. Esparza, D. Hansel, P. Rossmanith, S. Schwoon. *Efficient Algorithms for Model Checking Pushdown Systems.* CAV 2000.
- [Sch02] S. Schwoon. *Model-Checking Pushdown Systems.* PhD thesis, TU München, 2002.
- [RSJM05] T. Reps, S. Schwoon, S. Jha, D. Melski. *Weighted Pushdown Systems and Their Application to Interprocedural Dataflow Analysis.* Science of Computer Programming 58(1–2):206–263, 2005. https://www.sciencedirect.com/science/article/pii/S0167642305000493
- [EKL10] J. Esparza, S. Kiefer, M. Luttenberger. *Newtonian Program Analysis.* JACM 57(6), 2010.
- [Moh02] M. Mohri. *Semiring Frameworks and Algorithms for Shortest-Distance Problems.* J. Automata, Languages and Combinatorics 7(3):321–350, 2002.
- [DKV09] M. Droste, W. Kuich, H. Vogler (eds.). *Handbook of Weighted Automata.* Springer, 2009.
- [Par66] R. Parikh. *On Context-Free Languages.* JACM 13(4):570–581, 1966; [EGKL11] J. Esparza, P. Ganty, S. Kiefer, M. Luttenberger. *Parikh's Theorem: A Simple and Direct Automaton Construction.* IPL 111(12):614–619, 2011.
- [CC77] P. Cousot, R. Cousot. *Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs.* POPL 1977.

Incremental / recovery / filtering background:
- [WG98] T. Wagner, S. Graham. *Efficient and Flexible Incremental Parsing.* ACM TOPLAS 20(5):980–1013, 1998; [Wag98] T. Wagner. *Practical Algorithms for Incremental Software Development Environments.* PhD thesis, UC Berkeley, 1998.
- [TS] tree-sitter (M. Brunsfeld et al.). https://github.com/tree-sitter/tree-sitter ; [TS-ER] error-recovery strategy discussion: https://github.com/tree-sitter/tree-sitter/issues/224
- [LT93] A. Lavie, M. Tomita. *GLR\* — An Efficient Noise-Skipping Parsing Algorithm for Context-Free Grammars.* IWPT 1993.
- [JKVS12] M. de Jonge, L. Kats, E. Visser, E. Söderberg. *Natural and Flexible Error Recovery for Generated Modular Language Environments.* ACM TOPLAS 34(4), 2012. https://researchr.org/publication/JongeKVS12
- [K60] R. Kalman. *A New Approach to Linear Filtering and Prediction Problems.* J. Basic Engineering 82(1):35–45, 1960.
- [R89] L. Rabiner. *A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition.* Proc. IEEE 77(2):257–286, 1989.
- [Sar13] S. Särkkä. *Bayesian Filtering and Smoothing.* Cambridge University Press, 2013.

Project artifacts cross-referenced: `formal/rocq/prattail_wpda_runtime/theories/{CastCompareFrontierBound.v, CastDelegateMergeBound.v, LexForkKeywordReservation.v, BareVarFanQuotient.v}`, `dovetail/formal/rocq/theories/Extraction/{NBestExtraction.v, EnumerationCompleteness.v}`, `dovetail/formal/rocq/theories/InsideWeights/InsideWeightSccClosure.v`, `dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v`, `formal/rocq/egraph/theories/EGraphBudgetDedup.v`, `docs/design/parser-fv/{evidence-driven-early-pruning.md, evidence-gated-cross-cat-dispatch.md}`, `docs/design/evidence-pruning/00-existing-mechanisms-inventory.md`.
