# Graph-Structured Lambda Theories: Conversation Context

A reference document capturing the definition of graph-structured lambda theories (GSLTs) and the surrounding conceptual framing developed in conversation. Intended to be reloaded as context in future conversations.

## Definition

A **graph-structured lambda theory** is given by the following data:

1. **A grammar** specifying a freely generated collection of terms. These terms are to be thought of as *states*.
2. **A collection of equations** identifying some of the terms (states).
3. **A collection of rewrites** describing how states may evolve from one to another.

The "graph" is literally the equation/rewrite structure on the freely generated term set: nodes are terms (states), undirected edges are equations (symmetric identifications), directed edges are rewrites (asymmetric evolutions). The grammar gives the carrier, equations quotient it, rewrites animate it.

## Examples

- **Lambda calculus**: terms are lambda terms; equations are α-equivalence; rewrites are β-reduction.
- **π-calculus, ρ-calculus, ambient calculus, SKI combinators**: all instances.
- **Universal algebra and Lawvere theories**: embed in GSLTs as the degenerate slice where the rewrite collection is empty (or symmetrized into the equations) and the grammar is the algebraic signature. The "no dynamics" slice.

## The Two Categories of Interest

GSLTs come with two distinct categories, distinguished by what their morphisms preserve:

### Syntactic category
- Morphisms preserve **term structure**.
- The "rigid" category: a morphism is essentially a translation of grammars that respects equations and rewrites on the nose.
- This is where the Lawvere-theory embedding lives most naturally — universal algebra wants term-structure-preserving morphisms because there is no nontrivial dynamics to bisimulate against.

### Semantic category
- Morphisms preserve **bisimulation** only.
- The "loose" category: morphisms only need to preserve observational content; bisimilar states go to bisimilar states, with no obligation to track underlying syntactic shape.
- This is where most of the interesting process-calculus equivalences (barbed congruence, weak bisimulation) live, and where translations between calculi (e.g., π into ρ) typically reside — such encodings are usually not term-preserving but are bisimulation-preserving up to some discipline.

### The forgetful functor
There is an evident functor from syntactic to semantic — every term-preserving morphism is in particular bisimulation-preserving — but it is far from full or faithful. The semantic category sees through to the quotient by bisimulation; the syntactic category remembers the presentation.

### Connection to OSLF
This is exactly the setting where OSLF (Operational Semantics in Logical Form) earns its keep. A Hennessy–Milner-style logic generated functorially from the rewrite structure characterizes the bisimulation quotient: P ~ Q iff they satisfy the same formulae. The semantic category is, in a precise sense, the category of GSLTs viewed through the logic OSLF produces; the syntactic-to-semantic functor is the one that forgets everything not visible to that logic.

The natural follow-on question — when does a translation of grammars-with-rewrites descend to the bisimulation quotient — is the operational-correspondence / full-abstraction question, and it has the same shape as the rho calculus full abstraction work being formalized in Lean.

## The Inversion Relative to Classical Mathematics

This way of carving things up is **dramatically distinct from classical mathematics** and its presentation in category theory.

In the traditional category-theoretic presentation of linear algebra (and most classical structures):
- **Structure** is carried by the objects (vector spaces).
- **Behavior and dynamics** are carried by morphisms between objects (linear maps).
- A linear map *is* the dynamics; a group homomorphism *is* the action; a continuous function *is* the process.
- The category is bipartite: nouns at vertices, verbs on edges. The only way to talk about "what a vector space does" is to pick a morphism out of it.

In a GSLT, **the verbs have moved inside the object**:
- A single GSLT already contains its own dynamics as first-class data — rewrites are *part of the object*, not something reached by mapping out.
- Morphisms between GSLTs are a second, higher-level layer of dynamics: dynamics *of theories*, not dynamics *within* a theory.
- This yields a two-tier structure that classical category theory flattens.

### Consequences of the inversion

**Why process calculi never fit Lawvere theories / monads / algebraic theories cleanly.** People kept trying to make rewrites into morphisms of some category whose objects were terms, but that puts the rewrites at the wrong level — it conflates within-theory dynamics with between-theory dynamics. The GSLT framing says: rewrites belong to the object; morphisms are something else.

**Why bisimulation is the right notion of sameness here, not equality-of-morphisms.** In classical category theory, two objects are "the same" when there is an iso between them — and the iso is itself a morphism, a verb-level thing. In the GSLT world, sameness of objects is bisimulation, which is internal-to-the-object: it concerns how the verbs *inside* two objects can simulate each other. The syntactic category uses iso-style sameness (term-structure preservation); the semantic category uses bisimulation-style sameness; they genuinely come apart precisely because objects now carry behavior.

**Why the embedding of classical algebra is faithful but not full in an interesting way.** Classical algebraic structures are GSLTs whose rewrite component is trivial (or symmetric) — objects with no internal verbs, only nouns and identifications. The embedding loses nothing, but it reveals that classical mathematics has been working with a degenerate slice all along, where the only available behavior is behavior between objects, because there is no behavior within them.

### A guiding analogy

Classical category theory treats objects as point-particles whose only dynamics come from external forces (morphisms). GSLTs treat objects as **extended systems with internal degrees of freedom**. Morphisms between GSLTs are then more like maps between *spacetimes* than maps between points — they have to respect both the carrier and the internal causal structure.

## Interactive GSLTs

An **interactive GSLT** is a refinement of a GSLT equipped with a distinguished family of term constructors — denoted K (or a family {K_i}) — characterized by the following criterion:

> **K is the head of the LHS of every base rewrite, where a base rewrite is a rewrite rule with no hypotheses.**

The "no hypothesis" criterion is doing the real definitional work. It picks out exactly the rules that *are* the interactions, as opposed to the rules that *propagate* interactions through context. A base rewrite fires on its own terms, with nothing above the line; everything above the line is structural plumbing.

### K as the program/environment cut

K is the syntactic site at which a state is decomposed into a **program** and an **environment**. Base rewrites are precisely the moves that consume a K-form to produce something new. Whether the program/environment cut is *absolute* or *relative* is a property of K's symmetries:

- **λ-calculus**: K = application. Base rewrite is β: `(λx.M) N → M[N/x]`. Application is non-commutative as a constructor, so the cut is **absolute**: the function side is program, the argument side is environment.
- **π-calculus**: K = parallel composition. The COMM base rewrite `x⟨v⟩.P | x(y).Q → P | Q[v/y]` is symmetric in its two parallel components, so the cut is **relative**: each component is, from the other's perspective, the environment. Program and environment become *roles* a participant occupies during a particular interaction, not intrinsic identities.
- **ρ-calculus**: same as π — K = parallel composition, COMM is symmetric.
- **Ambient calculus**: K = parallel composition, with in/out/open as base rewrites.

So K does two jobs at once: it is the *syntactic locus* of interaction (where rewrites fire without structural premises), and the *ontological locus* of the program/environment cut.

### The family of K's

In full generality, the K's form a **family**, not a single constructor. The family is read off the theory: it is the set of hypothesis-free LHS-heads in the rewrite presentation. In ambient the family is a singleton (parallel) because in/out/open share the same head; in richer calculi (e.g., rholang with both COMM and a reflection-mediated rewrite) the family has multiple elements. The simplified single-K presentation is pedagogical; the general definition allows a family.

### Base rules as the ground of dynamics

The base rules are the **ground of the theory of dynamics** — generators, not derived. They are posited interactions, not theorems. This commitment has several consequences:

- **The K-family is canonical, not presentational.** No admissibility-elimination collapses base rules into derived ones; if a hypothesis-free rule is in the presentation, it is ground.
- **Rule form is principled, not accidental.** Rules with hypotheses are *modes of inference* (lifting dynamics through context); rules without hypotheses are *the dynamics itself*. The horizontal line in an SOS rule does genuinely different jobs depending on whether anything sits above it.
- **Structural rules become a separate layer.** They constitute the *propagation discipline* — the closure operator extending dynamics from K-redexes to all terms. They are not dynamics, they are addressing: they tell you the location of an event, not the event itself.
- **Causal counting becomes principled.** In the synchronization-tree / causal-set view, every step is ultimately a base-rule firing inside a context. The assembly-index-as-open-synchronization-tree-depth thread becomes specifically a count of base-rule firings — ground events, not bookkeeping.
- **Cost accounting is structurally forced.** Phlo (or any cost) attaches per base-rule firing because base rules are the ground events. Charging per structural rule would be charging for inference, not dynamics — a category error. Each K in the family carries its own cost, with exactly as many primitive cost categories as there are hypothesis-free rule heads.

### Structural questions raised by the family

- **The family carries structure.** Different K's interact via the structural rules — a COMM-K firing inside a reflection-K context, etc. The family is plausibly a *signature with arities*, where each K has a declared interaction shape (binary symmetric, n-ary, asymmetric with k program slots and m environment slots), and structural rules specify legal nesting. A coloured-operad framing is plausible.
- **Symmetry classification is per-K.** A theory can have one symmetric K (relative cut) and one asymmetric K (absolute cut) coexisting. Rholang with reflection plausibly exhibits this: COMM symmetric, reflection-mediated rewrites asymmetric because quoting is directional. Program/environment-relativity is therefore a *local* question, relative to which K is firing.
- **Atomic modal granularity.** The HML produced by OSLF inherits its atomic modal steps from K-firings. So an interactive GSLT determines not just *a* HML, but a HML *with a distinguished notion of atomic interaction*. K's symmetries control which modalities are self-dual, which come in pairs, etc.

### Morphisms of interactive GSLTs

A morphism of interactive GSLTs has to preserve the K-family. Three regimes:
- **Strict syntactic**: K-by-K preservation on the nose.
- **Encoded**: a source K is implemented by a combination of target K's plus structural context. This is what encodings like π-into-ρ typically do.
- **Semantic**: K-firings preserved only up to bisimulation.

The middle "encoded" regime is where most of the interesting metatheory of process-calculus encodings lives — neither term-level nor purely bisimulation-level, but at the level of *how one ground is implemented in terms of another*. Operational correspondence and full abstraction live here.

## Three Named Categorical Structures

Three named categorical structures organize the framework. They sit in a clear chain — the syntactic category, with term-structure-preserving morphisms; the semantic category, with bisimulation-preserving morphisms; and the hypercomputation fibration over the Turing-complete interactive sub-category of the semantic category.

### 1. The syntactic category of GSLTs

**Objects**: GSLTs (grammar, equations, rewrites).

**Morphisms**: term-structure-preserving translations. A morphism sends terms to terms in a way that respects grammar, equations, and rewrites on the nose — a "rigid" translation that tracks the syntactic shape of states, the symmetries that identify them, and the rule-schemas that animate them.

This is where the Lawvere-theory embedding of universal algebra lives most naturally; without nontrivial dynamics there is nothing to bisimulate against, and term-structure preservation is what universal algebra wants. The synchronization-tree / causal-set view of a state lives in this category as well, since the unfolding of a state into its synchronization tree is determined by term structure plus rewrite firings.

### 2. The semantic category of GSLTs

**Objects**: GSLTs (same as the syntactic category).

**Morphisms**: bisimulation-preserving translations. A morphism only has to preserve observational content — bisimilar states go to bisimilar states — with no obligation to track underlying syntactic shape.

This is where most process-calculus encodings (π-into-ρ, lambda-into-SKI, etc.) live, since such encodings are typically not term-preserving but are bisimulation-preserving up to some discipline. It is also where the OSLF-generated HML acts coherently: a formula characterizing a bisimulation class at one object translates, under semantic-category morphisms, to a formula characterizing the corresponding class at another object.

There is an evident **forgetful functor** from the syntactic category to the semantic category — every term-preserving morphism is in particular bisimulation-preserving. This functor is faithful but far from full; the semantic category sees through to the bisimulation quotient, while the syntactic category remembers the presentation.

### 3. The hypercomputation fibration

**Base**: the full subcategory of the semantic category whose objects are Turing-complete interactive GSLTs. Morphisms are bisimulation-preserving translations between Turing-complete interactive GSLTs.

**Fiber over a base object g**: Turing's hypercomputational tower over g, indexed by the ordinals. A fiber point (g, α) is g augmented with a level-α halting oracle, in the sense of Turing's *Systems of Logic Based on Ordinals*: level 0 is plain g, level 1 is g plus a halting oracle for ordinary g-computations, level 2 is g plus a halting oracle for level-1 machines, and so on into the transfinite. Each level is strictly more expressive than the previous.

**Fibration structure**: bisimulation-preserving base morphisms g → g' lift to compatible morphisms on the towers, because halting predicates are behavioral and bisimulation between g and g' makes their halting predicates inter-translatable. The total category has fiber points (g, α) and morphisms factoring as a base morphism composed with a fiber morphism within the target's tower.

**Use**: an agent and its environment are both points in this fibration. They need not be at the same point and need not be in the same g — bisimulation-preserving base morphisms make agents portable across substrates. The OSLF-generated HML is portable across the fibration as well, because OSLF generates the HML functorially and bisimulation-preservation carries the modal logic between fiber points. The agent's hypotheses retain their meaning across substrate changes.

## The Agent Perspective

The framework's animating question is not "what is the right formalism for compressed causal graphs?" but **what is it like to be an agent existentially motivated to work out its situation?** Structural commitments unfold from the existential one:

- The agent must compress (full causal graph unworkable).
- Compression must be in rule-form (that is what compressed causal graphs are).
- Hypotheses must be expressible in the agent's own substrate (no metalanguage available).
- Hypotheses must be testable at finite cost (resources are bounded).

Hence: GSLT-shape, internal HML embedding, phlo-paid testing, predictive-economic existence. The framework starts inside the cognizing agent and works outward; this is the same starting point as Kant's transcendental project, executed with resources Kant did not have.

## Space, Splittings, and the Three Views of ∂T

### Space from term structure (location as splitting)

Term structure is the natural — and, from inside the GSLT-shape commitment, only — candidate for space. Adjacency comes from constructors; locality comes from rewrite-locality; the agent's hypotheses already speak about term structure.

A **location** is not a context. A context like λx.[ ] does not locate the subterm N inside λx.(M N) — the same context could equally well surround the subterm P inside λx.(M (N P)). A location is a **splitting** (k, t) of a term graph into a context and a subterm, with the cut between them as the place. This is, in a precise structural sense, like a Dedekind cut or Conway's (L | R) pair: location as partition of a larger whole, with the cut between the parts being the place.

The space ∂T × T of splittings forms a fibration over T via the plug operation. Among splittings, the sub-bundle **Fire** consists of those where t (or its outermost form) matches the LHS of a base rule. Fire-fiber over a state is the discrete tangent space; synchronization-tree paths are integral curves.

**The program/environment cut from interactive GSLTs and the location-as-splitting are the same notion** at different resolutions. Location and interaction are the same notion at different levels of resolution.

### The three views of ∂T (the structure–function unification)

Three apparatuses that look distinct turn out to be three views of the same data:

- **Witnessing**: ∂T as the index set of OSLF-generated HML modalities. ⟨k⟩φ asserts a transition labeled by k after which φ holds.
- **Firing**: ∂T as the label set of LTS transitions. The LTS is *derived from* the rewrite system by the Milner–Sewell–Leifer minimal-context construction (adapted to GSLTs by L. G. Meredith, Christian Wells, et al. — forthcoming paper). Transition labels are contexts, not primitive action names.
- **Placing**: ∂T as the location-side of splittings — locations in the agent's space.

These are the same data viewed in three modes. This is the structure–function correspondence paid careful attention: the rewrite system *generates* the LTS, OSLF *generates* the modal logic, the McBride derivative *generates* the type of contexts, and all three generative passages produce or use the same index set ∂T.

### Adequacy as unification

Hennessy–Milner adequacy (P ~ Q iff same HML formulae satisfied), in the context-labeled presentation, is not the agreement of two separately-developed apparatuses but the assertion that *the modal language and the dynamical structure are one thing seen from two sides*.

### The ultrafilter metric on bisimulation classes

Adequacy + Stone duality on the OSLF-generated modal algebra → bisimulation classes correspond to ultrafilters → the space of ultrafilters carries a natural metric (closeness = formula agreement weighted by formula complexity).

In the context-labeled presentation, the metric's parameters are not arbitrary. **Formula complexity is read off the spatial reach of the contexts the formula's modalities use.** The ultrafilter metric on bisimulation classes is *induced by, and inherits its structure from, the agent's spatial structure*.

### Phenomenal-noumenal metric duality

The phenomenon (term structure with locations as splittings) does not just *reach* the noumenal (bisimulation classes) via Hennessy–Milner adequacy; it *metrically structures* it. The noumenal is not a flat collection of equivalence classes but a metric space whose geometry is read off from the phenomenal.

This is a substantial improvement on Kant. Noumena are not just positively characterizable; they are positively *measurable*. The agent can compute, from its own resources, how far a hypothesis is from the truth — providing the closeness measure the predictive-economy story requires.

### Weights and the metric's character

When base rewrites carry weights, modal contexts inherit them and the ultrafilter metric inherits them in turn:
- **Real weights** → classical metric on bisimulation classes.
- **Complex weights** → Born-rule-like behavior emerges from the modulus-squared structure of complex-weighted ultrafilter agreement. Quantum reading of the framework lives here.

Classical and quantum mechanics are not separate theories of nature in this picture but separate parameterizations of the predictive-agent dynamics, with the parameter being the weight ring of the rewrite system.

## Open Threads

- **Packaging the two-tier structure**: a 2-categorical or double-categorical presentation where within-object rewrites are vertical and between-object morphisms are horizontal, with squares as coherence — natural fit, but possibly over-engineered.
- **Equations vs. rewrites as separate data**: take grammar, equations, rewrites as a tuple, or package equations as the symmetric, cost-free sub-collection of rewrites? The latter is more parsimonious and supports an "everything is dynamics" reading; the former matches how calculi like the lambda calculus actually present (α and β playing genuinely different roles).
- **Limits and colimits in the syntactic category**: colimits (combining theories) likely more tractable than limits.
- **When syntactic morphisms induce semantic ones**: the operational-correspondence / full-abstraction question.
- **Equivalence of grounds**: a notion of equivalence between two interactive GSLTs that is stricter than semantic-category bisimulation but looser than strict K-preservation — something like "the two grounds are reachable from each other by a discipline of derived-rule moves." Likely the natural home for the metatheory of encodings (π-into-ρ etc.): not at the level of terms, not at bisimulation alone, but at the level of *how one ground is implemented in terms of another*.
- **The right structure on the K-family**: signature with arities, coloured operad, or something else. What governs legal nesting of K's under structural rules.

## Surrounding Context (Pointers, Not Re-derivations)

GSLTs sit at the center of a larger research programme connecting them to:
- **Physics**: Hamiltonian/Lagrangian structure via discrete differential geometry; synchronization trees as causal sets.
- **Origins of life**: assembly index as open synchronization tree depth (the synchronization tree is the unfolding of the directed-edge graph from a chosen state; "open" depth is a measure on that unfolding).
- **Sentience and consciousness**: hypercomputational fibration.
- **Concept blending and renormalization**: graph expansion algorithm, path quantale, Loday–Ronco Hopf algebra, Connes–Kreimer.
- **OSLF**: functor on the GSLT category producing Hennessy–Milner logics, with adequacy theorem (P ~ Q iff same formulae satisfied).
- **MeTTaIL (rholang 1.4)**: a means to define languages, where a language consists of a collection of types representing grammar, a collection of equations on types, and a collection of rewrites on types — i.e., a presentation of GSLTs as first-class linguistic objects.
