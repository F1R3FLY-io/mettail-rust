# Graded Compactification of the Hypercomputation Fibration: Conversation Context

A reference document capturing the reading of the hypercomputation fibration as an ordinal-graded Stone-Čech-like compactification of the base category. Companion to `gslt-context.md`. Intended to be reloaded as context in future conversations.

## Setup

Notation and apparatus are inherited from `gslt-context.md`:

- The semantic category of GSLTs has bisimulation-preserving morphisms.
- Its full subcategory of Turing-complete interactive GSLTs is the base of the hypercomputation fibration.
- Over each base $g$, the fiber is Turing's ordinal-indexed tower: $(g, \alpha)$ is $g$ augmented with a level-$\alpha$ halting oracle.
- OSLF generates a Hennessy–Milner-style modal logic from the rewrite system, with adequacy: $P \sim Q$ iff $P, Q$ satisfy the same HML formulae.
- HML modalities are indexed by $\partial T$, contexts in the spatial-splitting sense; formula complexity is read off the contexts' spatial reach.

## The Core Claim

The hypercomputation fibration is, when read through OSLF + Stone duality, an **ordinal-graded Stone–Čech-like compactification** of the base category at HML. Each fiber level is a stratified compactification of the level below; the limit points adjoined are exactly the ultrafilters on the OSLF-generated modal algebra that the lower level cannot realize from finite-cost observation.

## Apparatus

For a base object $g$, define:

- $\mathrm{HML}_\alpha(g)$ — the sub-language of the OSLF-generated HML over $g$ whose modalities use contexts of spatial-reach complexity $\le \alpha$.
- $A_\alpha(g)$ — the Lindenbaum algebra of $\mathrm{HML}_\alpha(g)$.
- $\mathrm{St}_\alpha(g)$ — the Stone space of $A_\alpha(g)$: its set of ultrafilters with the canonical Stone topology.
- $B_\alpha(g)$ — the bisimulation classes of $(g, \alpha)$, the level-$\alpha$ oracle extension of $g$.

Adequacy at level $\alpha$ provides an injection $B_\alpha(g) \hookrightarrow \mathrm{St}_\alpha(g)$ sending each bisimulation class to the principal ultrafilter of the maximally consistent $\le\alpha$-theory it satisfies.

## Definition: α-compactness

$(g, \alpha)$ is **$\alpha$-compact** iff the realization map
$$B_\alpha(g) \hookrightarrow \mathrm{St}_\alpha(g)$$
is surjective. Equivalently: every $\mathrm{HML}_\alpha(g)$-theory finitely satisfiable in $(g, \alpha)$ has a model in $(g, \alpha)$. Equivalently again: every ultrafilter on $A_\alpha(g)$ is realized as a bisimulation class of $(g, \alpha)$.

This is the graded analogue of the classical Stone compactness theorem; the grading is by the ordinal index of the oracle tower, which controls the complexity of the formulae required to be modelled.

## The Graded Compactification Claim

The tower $\{(g, \alpha)\}_{\alpha \in \mathrm{Ord}}$ is the canonical ordinal-graded compactification of $g$, in three senses:

1. $(g, \alpha)$ is $\alpha$-compact for each $\alpha$.
2. The inclusion $(g, \alpha) \hookrightarrow (g, \beta)$ for $\alpha < \beta$ is the minimal extension realizing exactly the ultrafilters of $A_\beta(g) \setminus A_\alpha(g)$.
3. The system of inclusions, viewed Stone-dually, is the inverse system of Stone spaces dual to the colimit $\mathrm{colim}_\alpha A_\alpha(g)$ of algebras.

The fibration is therefore not an ordinal-indexed family of unrelated extensions but a single canonical compactifying tower; the ordinal index records *which formulae of which complexity get models at which fiber level*.

## Two Stone-Dual Views

Passing from $(g, \alpha)$ to $(g, \beta)$ does two things at once, Stone-dually equivalent.

**Test side (algebra).** The new oracle adds modalities indexed by contexts whose decidability requires it. $A_\alpha \hookrightarrow A_\beta$ adds propositions; the algebra grows.

**State side (space).** The same oracle splits previously-bisimilar pairs into distinct classes; the bisimulation relation refines. Bisimulation classes proliferate.

Stone duality identifies these. Refining the relation on points of a Stone space corresponds to extending the dual algebra. The "limit points adjoined" by the next oracle level are simultaneously *new ultrafilters on the bigger algebra* and *new bisimulation classes under the finer relation*.

The compactification reading is most natural at the inverse limit:
$$\mathrm{St}_\infty(g) := \varprojlim_\alpha \mathrm{St}_\alpha(g).$$
Each $\mathrm{St}_\alpha(g)$ is a coarsening of $\mathrm{St}_\infty(g)$; the ordinal grading stratifies $\mathrm{St}_\infty(g)$ by how much oracle help is needed to distinguish a point.

## Why Stone–Čech-like

Stone–Čech compactification adjoins to a space all the limit points of bounded continuous functions — equivalently, all ultrafilters on the algebra $C_b(X)$. Every such ultrafilter is realized as a point in the compactified space.

The graded compactification does the same thing, *graded by definability*: at level $\alpha$, the algebra is $A_\alpha(g)$ instead of "all of $C_b$," and the level-$\alpha$ fiber adjoins the limit points needed to realize every ultrafilter on $A_\alpha(g)$.

The classical case adjoins all idealized points at once. The fibration stratifies the adjunction by an ordinal-indexed measure of how "ideal" a point is, where ideal = how much oracular help its identifying theory requires.

## Limit Ordinals

Successor stages are determinate: $A_{\alpha+1}$ is the closure of $A_\alpha$ under the new oracle's modality, and $\mathrm{St}_{\alpha+1}$ is the corresponding refinement of $\mathrm{St}_\alpha$.

Limit stages carry genuinely new content. For a limit $\lambda$, $A_\lambda = \mathrm{colim}_{\alpha < \lambda} A_\alpha$ and dually $\mathrm{St}_\lambda = \varprojlim_{\alpha < \lambda} \mathrm{St}_\alpha$. The question "is $(g, \lambda)$ $\lambda$-compact?" is nontrivial: there can be theories in $\mathrm{HML}_\lambda$ each of whose finite fragments lives at some $\alpha < \lambda$ and is satisfiable there, but whose totality requires a uniform realization across all $\alpha < \lambda$ that no single fiber below provides.

Adjoining those uniform limit points is the new content of the limit fiber. $\lambda$ is not bookkeeping for its predecessors; it is itself a compactification step. This is the Turing-tower-ordinal-logic phenomenon — that the progression jumps at limits — read as compactification.

## Connections to Surrounding Apparatus

**Graded metric on bisimulation classes.** The ultrafilter metric, weighted by formula complexity, refines into ordinal-indexed scales: distance at the $\alpha$-scale is computable from $\mathrm{HML}_\alpha$ formulae. The metric on $\mathrm{St}_\infty$ is the limit of the stratified metrics. An agent's hypothesis is "$\alpha$-reach $\epsilon$-far" from the truth — $\epsilon$ measurable distance, $\alpha$ how many oracle levels separate agent and truth.

**Stratified measurable noumena.** The Kantian upgrade established in `gslt-context.md` makes the noumenal positively measurable; the graded compactification refines this to a positive ordinal-graded inaccessibility. Some of the noumenal is one oracle level away; some at $\omega$; some at the inverse-limit horizon. The agent's epistemic situation is precisely *where in the tower its decidable reach gives out*.

**OSLF functoriality under oracle extension.** Because OSLF is functorial in the rewrite system and the oracle extends the rewrite system in a controlled way (adding a halting predicate as a new constructor), $\mathrm{HML}_\alpha$ is conjecturally the OSLF image of the $\alpha$-th oracle-extended rewrite system. This is the load-bearing lemma that makes the modalities-and-oracles correspondence a theorem rather than an analogy. Establishing it is a precondition for the graded compactification claim being formal.

## Open Technical Questions

**Indexing.** Recursive ordinals (Kleene's $\mathcal{O}$) are the natural index up to $\omega_1^{\mathrm{CK}}$; admissible ordinals beyond. The technical lemma needed is that "context complexity $\alpha$" and "level-$\alpha$ oracle" coincide as the same ordinal — i.e., the lightface analytical hierarchy of context shapes matches the Turing-tower index.

**Fullness at the inverse limit.** Is $\mathrm{St}_\infty(g)$ the Stone–Čech compactification of $\mathrm{St}_0(g)$ at the *full* OSLF-HML algebra, or only at a natural sub-algebra? Likely the latter; the former would require closure properties on OSLF-generated algebras not yet established.

**Graded morphism lifting.** Bisimulation-preserving base morphisms $g \to g'$ should lift gradedly: a level-$\alpha$ test on the source pulls back to a level-$\alpha$ test on the target. Required for agent-portability in the graded version. Reduces, plausibly, to the OSLF-functoriality-under-oracle-extension lemma.

**Limit-stage axiomatics.** At limit ordinals $\lambda$, what coherence conditions on $\{A_\alpha\}_{\alpha < \lambda}$ guarantee $\lambda$-compactness of $(g, \lambda)$? Candidates: a directed-colimit-of-compact-algebras condition, or a Mittag-Leffler-style condition on the inverse system of Stone spaces.

**Effective vs classical compactness.** $\alpha$-compactness as defined is classical (set-theoretic). The agent-perspective story wants *effective* $\alpha$-compactness — a constructive witness to the realization map's surjectivity. The constructive content is what gives the agent an actual procedure for testing finite-subcover-style claims; phlogiston cost attaches to this constructive witness, not to the existence statement.

## Surrounding Programme (Pointers)

The graded compactification framework engages directly with several adjacent threads:

- **Compactness hypothesis for consensus**: the stratification gives a candidate taxonomy where consensus protocols are classified by the ordinal level at which their cover algebra becomes (effectively) compact. FLP impossibility reads as level-0 non-compactness; failure detectors, randomization, and partial-synchrony assumptions read as oracle-level escalations. The Chandra–Toueg failure-detector hierarchy is then a candidate concrete instance of a graded compactification of the consensus space. This thread is developed in subsequent conversation.
- **Effective descriptive set theory**: the hyperarithmetical and analytical hierarchies are the natural ordinal-indexing for the graded picture; checking the match between their indexing and the OSLF-generated context-complexity indexing is the indexing question above.
- **Realizability**: each oracle level is plausibly a realizability tripos; the graded compactification is then a tower of tripos extensions, with a corresponding stratification of realizable propositions.
- **Topos-theoretic packaging**: the graded structure is a candidate filtration of a higher topos over the base category; whether this is overkill or genuinely needed for the limit-stage axiomatics is open.
