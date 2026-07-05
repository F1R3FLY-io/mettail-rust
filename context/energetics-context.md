# Energy, Mass, and Phlo in OSLF-Decorated GSLTs: Conversation Context

A reference document capturing the energetic reading of OSLF-generated HML over GSLTs — term assignment, the potential/kinetic decomposition of contexts, mass via information flow, linear discipline as conservation, phlo as action, and mass-energy conversion. Companion to `gslt-context.md` and `graded-compactification-context.md`. Intended to be reloaded as context in future conversations.

## Setup

Notation and apparatus inherited from the companion documents:

- A GSLT is grammar + equations + rewrites; the dynamics-internal-to-the-object framing.
- Interactive GSLTs carry a K-family — the heads of hypothesis-free rewrite LHS — at which interaction occurs and which constitute the program/environment cut.
- $\partial T$ is the space of contexts in the spatial-splitting sense: the unified index set of OSLF-generated modalities, LTS labels, and locations within a term.
- OSLF generates a Hennessy–Milner-style modal logic from the rewrite system; adequacy gives $P \sim Q$ iff $P, Q$ satisfy the same HML formulae.
- Phlogiston (phlo) attaches per K-firing: base rules are the ground events; structural rules are addressing, not dynamics, and incur no primitive cost.
- The hypercomputation fibration has Turing-complete interactive GSLTs as base; fibers are Turing's ordinal-indexed oracle towers; OSLF stratifies into $\mathrm{HML}_\alpha(g)$ by the spatial reach of the contexts modalities use.
- The fibration is a graded Stone–Čech-like compactification at the OSLF algebra: each $(g, \alpha)$ is $\alpha$-compact; the tower realizes ultrafilters on $A_\alpha(g)$ as bisimulation classes of $(g, \alpha)$.

## The Core Claims

1. **Term assignment is automatic.** OSLF-generated HML over a GSLT carries a canonical Curry–Howard term assignment; the proof terms are the synchronization-tree paths of the underlying rewrite system. Program extraction is trivial because modalities are context-decorated.

2. **Contexts carry energy with a PE/KE distinction.** A context $k \in \partial T$ appearing as a modal index is potential energy; the same $k$ appearing inside a term is kinetic energy. The duality is Legendre-style and exact, with cut elimination as the conversion process.

3. **Mass is information flow at a K-firing.** When $K(t, u)$ elaborates so that information flows from a subterm of one party to splittings of the other, the integrated transfer is the mass of the firing. Variables and de Bruijn indices are not atomic; they are splittings — instances of $\partial T$ — at which mass flows.

4. **Linear discipline = conservation of mass.** Multiplicative linear logic's "exactly one use" is mass conservation. Contraction is duplication, weakening is annihilation; exponentials are the controlled creation/annihilation operators.

5. **Phlo = action.** The phlo cost of a K-firing is proportional to a two-pronged complexity measure on the term being communicated: max-space-in-bounded-time and max-time-in-bounded-space. The functional has units of [space × time] — physical action.

6. **Mass-energy conversion: $E_{\mathrm{phlo}} = m \cdot \kappa^2$**, where $\kappa^2$ is the term's intrinsic complexity profile (action per unit information). $\kappa^2$ is graded along the hypercomputation fibration — it ascends with oracle level — giving the formal home of dark mass-energy: the part of the conversion that the agent's level cannot resolve.

## Apparatus

### Term assignment

For OSLF-generated HML formulae:

- $\langle k \rangle \varphi$ — proof terms are pairs $(k, \pi)$ where $k \in \partial T$ is the splitting at which the K-firing occurred and $\pi$ proves $\varphi$ in the result.
- $[k] \varphi$ — proof terms are functions from K-firings at $k$ to proofs of $\varphi$.

Because $k$ is a (context, subterm) pair — a splitting — the proof term natively contains where the action happened and which subterm was consumed. There is no separate "annotate the proof with location" pass; the spatial information was present in the modal index from the start.

A claim worth isolating:

> **OSLF–Curry–Howard.** For each rewrite system $R$, OSLF produces a logic-with-term-assignment whose proof terms are the synchronization-tree paths of $R$. The forgetful functor from OSLF proof terms to synchronization-tree paths is the identity on the underlying combinatorics; only the type decoration is forgotten.

The witnessing/firing/placing trinity (`gslt-context` §"three views of $\partial T$") collapses three would-be-separate facts into one: that the logic admits a Curry–Howard reading, that proof terms are operationally annotated with locations, and that program extraction is sound. They become a single fact because $\partial T$ was a single object all along.

### PE/KE decomposition

For $k \in \partial T$:

| Location of $k$ | Status | Energy reading |
|---|---|---|
| In modality $\langle k \rangle, [k]$ | Configurational, latent capacity | **Potential** |
| In term, applied / consumed | Trajectorial, expended capacity | **Kinetic** |

This is Legendre-dual structure. Formula and proof term are paired by the satisfaction relation $\models$, with cut elimination converting modal-side $k$ (PE) to term-side $k$ (KE). The K-firing happens; capacity becomes motion; total energy is invariant across the conversion.

Read against the two categories of GSLTs (`gslt-context`):

- **Syntactic morphisms** preserve term structure on the nose and so preserve the PE/KE *split* — energy components transported as components.
- **Semantic morphisms** preserve only bisimulation and so preserve only the *total energy budget* visible to the OSLF logic; the PE/KE allocation is gauge.

The forgetful functor from syntactic to semantic forgets the energy decomposition while preserving the total. **Bisimulation = energy-spectrum equivalence.**

### Mass functional

Per K-firing $K(t, u) \rightsquigarrow r$, let $\Sigma$ denote the term structure communicated at the firing — for $\beta$, the argument $N$ being substituted; for COMM in $\pi/\rho$, the message $v$; for the $\rho$-calculus reflective rewrites, the quoted process being unquoted.

> **Mass at a firing.** The mass is the cardinality of the information transfer from subterms of one side to splittings of the other, weighted by the spatial reach of the splittings receiving the transfer.

Examples:

- **β-reduction**: $(\lambda x.M)\, N \rightsquigarrow M\{N/x\}$. Mass $\approx |N| \cdot \#(\text{occurrences of } x \text{ in } M)$, with each occurrence weighted by its splitting depth.
- **COMM in $\pi/\rho$**: $x\langle v \rangle.P \mid x(y).Q \rightsquigarrow P \mid Q\{v/y\}$. Mass = information content of $v$ deposited at the $y$-splittings of $Q$. In $\rho$, $v = @P'$ is a quoted process; the mass is structurally heavier.

Variables and de Bruijn indices are not atomic; they are one-hole contexts — instances of $\partial T$ — and mass flows through them at firings. The same $\partial T$ that indexes modalities, labels LTS transitions, and identifies locations also marks the sites of mass transfer. The witnessing/firing/placing trinity gains a fourth view: $\partial T$ as the locus of mass flow at K-firings.

Mass attaches per K-firing for the same structural reason cost does: base rules are the ground events. There are exactly as many primitive mass categories as hypothesis-free rule heads — one per K. The mass ledger is the same ledger as the cost ledger; only the magnitudes and dimensional units differ.

### Linear discipline as conservation

Multiplicative linear logic — each variable used exactly once — pumps the communicated $\Sigma$ into exactly one splitting per firing. No copying, no deletion. Total mass-content is invariant under reduction.

Without linearity:

- **Contraction** (multiple occurrences of $x$): one $\Sigma$ becomes many. Mass is created from structure. Creation operator's signature.
- **Weakening** (no occurrence): $\Sigma$ silently discarded. Mass annihilated. Annihilation operator.
- **Full intuitionistic**: free creation and annihilation; thermal/open-system regime.

> **Slogan.** Linear logic is mechanics; the exponentials are thermodynamics.

Girard's exponentials $!A$, $?A$ mark which components participate in the conservation law and which are reservoir-coupled. The exponential structure of linear logic is the bookkeeping for which types are sealed against external mass exchange.

Under complex weights (`gslt-context` §"weights and metric character"), linear-discipline conservation becomes unitary — the modulus-squared of the information state is preserved. Linear logic over $\mathbb{C}$ is unitary mechanics; over $\mathbb{R}_{\geq 0}$ classical mechanics; the same syntactic discipline yields different conservation laws depending on the weight ring.

### Phlo as action

For $\Sigma$ the term communicated at a firing, define two complementary complexity measures:

- $\sigma_T(\Sigma)$ — the **maximum space** required to evaluate $\Sigma$ within a bounded time epoch $T$. Width-of-trajectory at fixed duration.
- $\tau_S(\Sigma)$ — the **maximum length** of evaluation $\Sigma$ supports within a bounded space budget $S$. Length-of-trajectory at fixed amplitude.

Each measures the same computational object from a different axis of the time-space plane. The phlo cost is proportional to a combined functional of the pair:

$$
\mathrm{phlo}\bigl(K(t, u) \rightsquigarrow r\bigr) \;\propto\; \mathrm{action}(\Sigma) \;=\; F\bigl(\sigma_T(\Sigma),\, \tau_S(\Sigma)\bigr).
$$

The two arguments of $F$ are dual measurements — one bounds time and asks for max space, the other bounds space and asks for max time — so the action they jointly determine is genuinely two-dimensional, with units of [space × time]. This is the dimensional signature of physical action.

> **Phlo = action.** The cost of a K-firing is the discrete action of the term being communicated, measured along the time-space tradeoff curve.

### Mass-energy conversion

Define the conversion factor

$$
\kappa^2(\Sigma) \;:=\; \frac{\mathrm{phlo}(\text{firing of } \Sigma)}{m(\Sigma)} \;=\; \frac{F(\sigma_T(\Sigma),\, \tau_S(\Sigma))}{m(\Sigma)}.
$$

Then

$$
E_{\mathrm{phlo}} \;=\; m \cdot \kappa^2.
$$

This is $E = mc^2$ in discrete-computational form. $\kappa^2$ is intrinsic to the term: it measures how much computational work a unit of static information can do when evaluated. The squared form is principled — $\kappa$ has units of [space × time]$^{1/2}$, dual to a "velocity of computation" (bandwidth per unit of dual-measurement product). Kinetic energy is quadratic in this velocity.

Three regimes:

- **Low $\kappa^2$** — atomic data, constants, normal forms. Information content is high but evaluation is trivial. Mass $\approx$ phlo. Non-relativistic.
- **Moderate $\kappa^2$** — typical computations whose space and time complexity are polynomially related. Standard feasible regime.
- **High $\kappa^2$** — terms whose evaluation defeats simultaneous time-and-space optimization. Small mass releases vast phlo. Relativistic; arbitrarily near-singular as $\kappa^2 \to \infty$.

Worked case. $(\lambda x.M)\, N$ where $M$ is a normal form using $x$ once and $N$ is a deep computation: $m \leq |N|$; phlo = action of $N$'s evaluation, unboundedly large. The ratio $\kappa^2$ is then $N$'s intrinsic specific energy — the term-level analogue of mass-energy conversion rate.

### Graded conversion

$\kappa^2$ is not a single constant. At fiber level $(g, \alpha)$, $\sigma_T$ and $\tau_S$ are computed relative to what the level-$\alpha$ oracle decides. For $\Sigma$ whose decidability requires level $\beta > \alpha$, the level-$\alpha$ measure is degenerate (the oracle cannot tell the runtime when to stop, so the apparent complexity is unbounded). Crossing to level $\beta$ collapses apparent complexity to a finite figure.

So:
$$
\kappa^2_\alpha(\Sigma) \;<\; \kappa^2_\beta(\Sigma) \quad \text{for } \alpha < \beta \text{ when } \Sigma \text{ requires a level-}\beta\text{ oracle.}
$$

Each compactification level has its own conversion factor.

> **Dark mass-energy.** An agent at $(g, \alpha)$ sees mass-energy conversions whose true factor lives above $\alpha$ as unaccounted books — phlo arriving without proportional mass to draw it from, or mass disappearing without proportional phlo released. The dark components of the agent's accounting are the part of the conversion that its oracle level cannot resolve.

The hypercomputation tower stratifies decidability and conversion rates simultaneously. Graded compactification (`graded-compactification-context`) and graded conversion are a single stratification of the agent's epistemic and energetic horizons.

## Conservation Reread

With phlo identified as action and mass-energy conversion fixed by $\kappa^2$, conservation sharpens. Linear discipline preserves *total mass-energy*:

$$
M_{\mathrm{total}} \;=\; m + \frac{E_{\mathrm{phlo}}}{\kappa^2}.
$$

At each K-firing, an amount $\delta m \cdot \kappa^2$ of rest-energy converts to phlo; rest-mass decreases by $\delta m$; the kinetic budget grows by $\delta m \cdot \kappa^2$; the total is invariant.

Closed-system mechanics: books balance because nothing leaves and nothing arrives; the only motion is conversion between rest and kinetic forms.

With exponentials, a reservoir opens — $!$-marked components admit unaccounted absorption — and linear-discipline closure is broken in the controlled, exponential-bounded way linear logic codifies.

OSLF-generated proof terms are simultaneously syntactic records and energy ledgers. Each cut-elimination step is a balanced energetic transaction: rest-mass down, kinetic energy up, total invariant. Curry–Howard, in this register, is the discrete-computational form of the first law: the total energy of a proof term equals the total energy of the formula it inhabits, with the proof term recording the trajectory of the conversion.

## Connections to Surrounding Apparatus

**The four views of $\partial T$.** The witnessing/firing/placing trinity (`gslt-context`) gains a fourth: $\partial T$ as the locus of mass flow at K-firings, weighted to give action. Same combinatorial object, four mutually-implying functions; structure–function correspondence holds across all four.

**Hamiltonian/Lagrangian discrete differential geometry.** PE/KE is the type-theoretic image of the H/L decomposition on the synchronization-tree-as-causal-set. The Legendre transform between PE-on-modalities and KE-on-terms gives the two formulations a shared categorical home. The symplectic form is the satisfaction pairing $\langle \varphi, \pi \rangle$ between formulae and proof terms.

**Complex weights and the quantum reading.** Born rule via complex-weighted action: under complex $\kappa^2$, the conserved quantity is $|m|^2 \cdot |\kappa^2|^2$, matching the modulus-squared structure already established at the bisimulation-metric level. The quantum reading lifts from metric to energetic.

**Cost-energy-mass triangle.** Three accounting quantities now coexist: cost (what the agent pays, possibly with overhead), energy (what the action functional registers as phlo), and mass (what flows at the firing). The triangle: cost $\geq$ energy $\geq$ mass, with equality at the bottom under linear discipline and saturation of the action functional. Slack = waste heat: phlo charged in excess of action supported.

**Compactness hypothesis for consensus.** Consensus protocols admit a stratification by the level $\alpha$ at which their cover algebra becomes effectively compact (`graded-compactification-context`). The energetic version: each level has a different $\kappa^2$, so consensus protocols at different levels exchange mass-energy at different rates. The Chandra–Toueg failure-detector hierarchy reads as a tower of mass-energy conversion levels.

**Phenomenal-noumenal metric duality.** The Kantian upgrade — phenomenal locality positively measuring noumenal bisimulation classes — extends. The agent now measures not only metric distance to truth (in formula complexity) but energetic distance to truth (in conversion rate). Where in the tower decidable reach gives out is also where conversion rate becomes inaccessible.

## Open Technical Questions

**The action functional $F$.** Specify $F(\sigma_T, \tau_S)$ precisely. Candidates: a product $\sigma_T \cdot \tau_S$ (literal time-space area); a maximum or supremum over a parametric family (envelope of the tradeoff curve); an integral of the tradeoff curve. The criterion: $F$ is the unique functional for which $\frac{d}{dt}\bigl(m + E_{\mathrm{phlo}}/\kappa^2\bigr) = 0$ holds exactly under linear discipline.

**OSLF–Curry–Howard functoriality.** Show OSLF is functorial as a *term-assigning* operation: bisimulation-preserving morphisms $R \to R'$ lift to term-translation operations preserving formula and proof-term structure. Formal version of "term assignment comes for free."

**PE/KE pairing as bilinear form.** Define $\langle \varphi, \pi \rangle$ with the structural properties of a Hamiltonian symplectic form: bilinear, non-degenerate on bisimulation classes, behavior under cut elimination matching Hamiltonian flow. The Legendre transform between modality-side and term-side energy becomes a derived theorem.

**Mass functional definition.** Make the per-firing mass precise, additive across firings, graded by spatial reach $\alpha$, reducing to occurrence-count for trivial grading, and conserved under linear-discipline reductions. Confirm that under complex weights conservation is unitary.

**Calibration to standard complexity.** $\sigma_T$ and $\tau_S$ should match DSPACE/DTIME hierarchies on suitable inputs. NP-complete encodings should produce the expected $\kappa^2$ blowup; P-time terms should have $\kappa^2$ polynomial in mass; primitive recursive terms recursively bounded but unboundedly so. Calibration connects internal accounting to the external complexity-theoretic universe.

**Least-action principle.** Cut elimination chooses one path among many. Conjecture: the chosen path minimizes integrated phlo. Principle of least action becomes a theorem of normalization theory in OSLF–Curry–Howard. The Lean formalization of full abstraction extends naturally to least-action.

**Linear-OSLF.** Identify the sub-fragment of OSLF-generated HML and term assignment corresponding to a linear discipline on the underlying GSLT — the closed-system slice. Plausibly characterized by a sub-functor selecting the multiplicative fragment. Connection to MLL proof nets: linear OSLF proof terms should *be* proof nets for the underlying interactions.

**Gauge symmetry from variable renaming.** $\alpha$-renaming relabels splittings without changing the structural skeleton. By the conservation-law correspondence, $\alpha$-renaming is a gauge symmetry whose conserved quantity is a tautology ($\alpha$-equivalent terms have the same mass-content). This is the type-theoretic image of Brian Beckman's UD-calculus alpha-renaming-as-gauge intuition.

**Cost-energy-mass triangle inequalities.** Formalize cost $\geq$ energy $\geq$ mass. Identify conditions under which the triangle collapses to equalities (linear discipline plus saturated action functional). Identify the slack as waste heat — phlo charged to the agent in excess of action it supports.

**Exponential-bounded $\kappa^2$.** In MLL, $\kappa^2$ is bounded by a structural function of the redex. Compute the bound. Conjecture: polynomial in the largest depth of any K-redex in the system. With $!$, the bound disappears; with $!_n$ (light/soft linear logic), bounds return at controlled rates. Physical reading of light logic systems as bounded-relativistic regimes.

**Born rule via complex-weighted action.** Under complex weights, $\kappa^2$ becomes complex-valued and the conserved quantity is $|m|^2 \cdot |\kappa^2|^2$. Confirm the Born rule emerges from complex-weighted phlo accounting under linear discipline.

**Effective vs classical conversion.** $\kappa^2_\alpha$ as defined is classical (set-theoretic). Effective $\kappa^2_\alpha$ — a constructive witness — is what attaches to the agent's runtime. The constructive content gives the agent an actual procedure for measuring conversions; phlo cost attaches to this constructive witness, not to the existence statement. Parallel to the effective-$\alpha$-compactness question in `graded-compactification-context`.

## Surrounding Programme (Pointers)

The energetics framework engages directly with several adjacent threads:

- **Discrete differential geometry and physics**: PE/KE is the H/L decomposition on the synchronization-tree-as-causal-set; the Legendre transform is the categorical pairing of formula and proof term; least-action is normalization; conservation laws are linear-discipline laws.
- **Origins of life and assembly index**: mass flow per K-firing accumulates along open synchronization-tree paths; assembly index is plausibly a coarse invariant of integrated mass.
- **Sentience and consciousness via the hypercomputational fibration**: agents experience their epistemic horizon as a horizon of conversion factors. What is "felt" at level $\alpha$ as inexplicable surplus or deficit is ordinary bookkeeping at level $\beta$.
- **Concept blending and renormalization**: the graph-expansion algorithm and Connes–Kreimer renormalization sit naturally as $\beta$-reductions of higher-order blends; mass conservation under linear discipline = renormalization-group flow conservation.
- **MeTTaIL (rholang 1.4)**: defining new K's at the language level means defining new mass categories; MeTTaIL's evolutionary programming over GSLTs is dynamics over the space of mass-energy ledgers.
- **F1R3FLY phlogiston economy**: the cost discipline is now derived from a physical principle (action-as-complexity) rather than imposed. Phlo prices map to computational specific energy; market-clearing on phlo prices is market-clearing on conversion rates. Valuable friction acquires a precise dimensional meaning: friction is the action functional resisting motion through the term-energy landscape.
- **MQ-calculus and measurement-as-communication**: communication = measurement; mass flow at communication is the information transferred at the measurement event; linear discipline in MQ gives unitary evolution between measurements; non-linear use breaks unitarity in exactly the way thermodynamic measurement does.
