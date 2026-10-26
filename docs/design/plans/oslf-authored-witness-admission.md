# OSLF authored-witness admission

Status: source-signature ACU admission, source-frame/publication composition,
freshness traversal, iterative term construction, and resolved source/image
correspondence have checked models and executable tests. They are reusable
components, not a complete continued/Cost(G) presentation certificate. The
accepted DDL, serialized V1 records, and ordinary cost-image validation are
unchanged. Specific unresolved compatibility and trust decisions are listed
below.

## Existing authoring contract

Keep typed `Terms`, `Equations`, and `Rewrites` as the language-definition
surface. Derive continued-interaction and cost-construction evidence from those
definitions, or check it through an installer-admitted proof implementation.
Do not treat the prototype witness strings as proofs, and do not turn them
into new mandatory authoring blocks.

This follows the [approved authoring direction](module-ddl-full-surface-syntax.md)
and the [FIP's canonical schema](../../../../../FIPS-mettail-in-rholang-specs/under-review/2026-07-25-MeTTaIL-Language-Specs-in-Rholang/2026-07-25-MeTTaIL-Language-Specs-in-Rholang.md).
The FIP permits local theory labels and installer-admitted, versioned resource
identifiers. It requires checked witnesses for continued theories, but does not
assign an executable namespace and proof contract to each string field.

Source-local structural checking can proceed without adding source syntax or
assigning new meanings to those strings. Changing their compatibility contract
or admitting a new trusted proof implementation is a separate decision; it is
not a prerequisite for the source checks described below.

## Evidence from the current implementation

[`ContinuedDeclV1`](../../../grammar-core/src/language_core.rs) stores its
roles as strings. The [value decoder](../../../mettail-elab/src/schema.rs)
requires nonempty strings; it does not establish their semantic properties.
The schema example uses proof identifiers such as `mtl:proof:wrappable/1`.
It does not supply source definitions for its other witness labels.

The [costed compiler fixture](../../../dovetail-runtime/src/theory_image_compiler.rs)
lists `R1` in `cost.rules` while its actual graded rewrite is `add-zero`.
Its grade row does resolve `add-zero` to an exact root. These are two different
fields, and requiring their lists to coincide would invent a contract.

[`CostImageV1`](../../../grammar-core/src/cost_image.rs) already validates
signature operators, source rewrite references, exact grade roots, and image
identity. Preserve those guarantees. They do not establish the full continued
GSLT structure described by the
[cost-monad manuscript](../../../../../publications/cost-accounting-as-monad/continued-gslt-cost-v2.tex).
A GSLT is a graph-structured lambda theory. Its continued-interactive structure
includes a chosen interaction cut, quotient section, and wrapped contraction.
The same underlying language can support more than one such presentation.

## Proposed resolution of the roles

| Existing fields or obligation | Proposed checked meaning | What must not be inferred |
|---|---|---|
| `interactive.cut`, `k`, `kp`, `ke`, `k_prime` | One identified cut presentation, with typed references to the actual interaction rules and constructor/context roles | Not one fixed arity or four universally required constructor applications. The manuscript's lambda example has a degenerate environment introduction. |
| `near` | The presentation's checked partial surface relation, including its location result and any structurally carried surface | Not a Boolean predicate or universal channel-equality test. |
| `compute`, `wrappability` | The contraction already expressed by the rule's RHS, substitutions, and ordered premises, with evidence that wrapped continuations retain their seals | Not a duplicate action, evaluator, or separately required `Compute` constructor. |
| `section` | A chosen normalization construction for the specified structural-congruence quotient, with totality, quotient invariance, and representative correctness | Not a finite equality-saturation result, raw hash, or successful normalization of a few examples. |
| `quote_faithfulness` | Evidence about an identified theory morphism, its source and target, and its reachable signature domain | Not a property conferred on a language by one string. Funding-map multiplicity preservation is insufficient. |
| `cost.rules` | The selected cost-construction family and its checked association with concrete generated or authored rules | Not an alias for the exact `grade_rules` roster. |
| `eta`, `mu`, `map`, `laws` | Identified operations of the cost construction and the laws they satisfy under the chosen interpretation | `map` is not automatically an object-language constructor. A source equation and evidence for a categorical law are distinct. |

Local names and proof identifiers select existing source definitions or
checked presentation evidence. They do not choose among unrelated namespaces
by string coincidence. The normalized evidence records resolved identities
and roles; a textual label alone cannot construct it. Unknown references,
unresolved ambiguity, type mismatches, or unauthorized references cannot
produce a certified presentation.

The authoring surface remains unchanged. Typed rule arenas, constructor and
binder tables, substitution nodes, and ordered premises are reused. The
existing matcher and semantic-image compiler remain the only execution path.
Structural checking uses bounded iterative traversal of those representations.

## Trust and identity

Keep four guarantees distinct:

| Artifact | What it establishes |
|---|---|
| Checked semantic/cost image | Source-exact executable rules and same-substitution grade construction |
| Checked continued/cost presentation | The selected cut, wrapping, section, and construction obligations for that source |
| Checked theory morphism | The specified endpoint theories, mapping, behavior preservation, and reachable-domain quote-faithfulness |
| Host funding evidence | A checked interpretation, authenticated supply, native funding judgment, and publication/replay obligations |

Presentation evidence must be bound to the exact source and semantic images,
the chosen presentation, the obligation being checked, and the trusted checker
version. Morphism evidence additionally binds both endpoint theories, the
mapping, and its reachable-key domain. Constructing a continued object does
not inherently require selecting an additional morphism. A certificate for one presentation or
morphism cannot be reused for another by relabeling it.

An installer-admitted proof identifier selects a trusted implementation; its
spelling or presence does not admit that implementation. Follow the existing
separation used by
[`FundingProjectionVerifierV2`](../../../grammar-core/src/installed.rs): the
node supplies the implementation, and checks exact source-bound input. Do not
reuse its *funding* verdict as proof of a continued presentation.

The [typed-channel theorem checker](../../../grammar-core/src/theorem.rs)
currently proves category membership or exact-term predicates. It is not a
checker for universal wrappability, quotient sections, or morphism laws. This
proposal does not expand typed channels or revive Reified RSpaces.

The raw, data-faithful representation may still express a proposed theory for
analysis or construction. Parsing that value is separate from certifying its
claimed semantic profile. At certification and installation, unresolved
obligations must yield refusal or an explicit indeterminate result, never a
certified continued/Cost(G) profile. Resource exhaustion is not evidence that
a law is false or true. No author-selected name grants a host capability.

## Formal and executable completion work

Reuse the already checked
[source-admission and interpretation results](../../architecture/authored-cost-interpretation.md).
The remaining work is to instantiate their premises, not copy the native
reduction rules or prove those same conditional results again.

1. Resolve the selected presentation against actual typed source definitions.
   One fully checked, source-bound witness can establish an existential
   presentation property. Exhaustively enumerating alternative proofs is not
   required. A choice that affects runtime semantics must be explicit and
   cannot prune runtime alternatives merely because one proof was found.
2. Check structural cut and wrapping properties across the covered rule family.
   Retain exact rule identities, binders, seal variables, stack residuals,
   grades, and locations. Name matching alone is insufficient.
3. Bind section and morphism evidence to their precise semantic domains.
   Bind the cost operations and law evidence to the same construction.
4. Require those checked results at the semantic-profile installation boundary.
   Keep them distinct from ordinary grade-row validation and host funding.
5. Test renamed valid definitions, incorrect reference kinds, unknown or forged
   proof identifiers, changed source fingerprints, mismatched morphisms,
   degenerate introductions, and incomplete rule coverage. Derive the
   corresponding generated properties from the admitted interpretation model.

The installed source-to-host path also needs refusal, cancellation, replay,
and signed client cost-parameter verification against the existing native gate.
Those are [integration obligations](../../architecture/oslf-integration-verification.md),
not prerequisites for proving an independent source-admission check.

The source-bound frontend implementation now addresses a distinct part of
that path. The actual generated parse constructs a private `ParsedSource`,
which lets the existing stack-safe driver prepare signed query receives and
transparent `PForCostSigned` continuations. AST-only callers retain their
existing refusals. An immutable `PreparedProgram` can retain the exact source,
generated complete-definition fingerprint, and encoded output; its constructor
checks output equality, and the shared node `prepare_program` checks the
requested source, declared language identity, and required binding presence.
The existing Casper offered-source boundary already invokes those checks
before native effects.

This receipt establishes no continued presentation, morphism, native authority,
or signed monetary controls. It adds no digest-injectivity claim. The
[preparation correspondence](../../architecture/oslf-integration-verification.md#signed-preparation-and-native-offer-binding)
records the exact model/test mapping and logical receipt-budget precharge,
including the separate native length-traversal and encoder-table boundaries.
The first current-batch frontend gate,
`target/verification/source-bound-prepared-frontend-r2-20261013.log`, passed
all nineteen tests on 2026-10-13: zero failures or ignored tests, 677 filtered,
5.64 seconds after a 4 minute 43 second build. These cover signed query/marker
differentials, AST-only refusal, exact receipt identity, unsigned/full Regex
preparation, budget/cancellation refusal, and the eight-case signed payload
property. The subsequent native execution/replay differential in
[`rholang_cost_lowering.rs`](../../../rholang-runtime/tests/rholang_cost_lowering.rs)
now passes after the approved `dispatch.rs`/`reduce.rs` correction. The
previous dispatch forwarded consumed receive authority, doubling uniform
continuation demand from `1` to `2`; ordinary continuation evaluation now
starts without that consumed authority and retains its inner signature.
System-body handling remains separate. Independent review found no deviation
from the approved two-file scope. The r5 gate passed all fourteen tests:
zero failed, ignored, or filtered, 0.36 seconds after a 1 minute 46 second
build. Uniform and transfer cases both check output `7`, singleton
continuation authority, positive charges, complete replay/log/root and
economic-trace agreement, and equality with explicit query expansion.

Existing `CAGradedTransition`/`WrappingSubjectReduction`, `SystemResidueSeal`,
`ReducerTailMachine`, and `DetachedParticipantFork` results already state the
needed continuation/seal and execution-context obligations. Their 2026-10-13
`coqc` and independent `coqchk` gate passed under 512 MiB, with 26 closed
printed assumption reports: eleven selected plus fifteen existing reports.
No new proof was needed. This model gate preceded the production correction;
the later r5 native result checks the focused executable correspondence.

Node admission's post-correction protocol-7/`CostV2` r3 gate passed all eighteen
tests: zero failed, ignored, or filtered, 0.56 seconds after a 2.09 second
build. It covers actual native-funded
positives and negative controls preserving prior budget, authority, and
RSpace state. The post-correction selected Casper receipt r3 gate passed
three tests with 634 filtered, zero failed or ignored, in 0.09 seconds after
a 2 minute 43 second build. All 28 earlier compile
diagnostics were corrected through test-only updates for merged APIs in ten
existing files. This Casper preparation result is not a full-suite or
execution/replay result. Nine system-residue checks and the existing
depth-4,096 and mixed-tail depth-4,032 fixed-stack controls also passed.

The epoch correction now uses RSpace's selected codec epoch in
`produce_inner`, `consume_inner`, and `eval_cost_stack`.
This repairs the local mismatch between unversioned registration and
epoch-aware event observation. Introduction identity remains a domain
transform of the complete event-source hash.
Stack receipts instead retain the raw event-source hash.

Before the production edit,
[`NativeSourceEncoding.v`](../../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/NativeSourceEncoding.v)
passed `coqc` and independent `coqchk` under 512 MiB with no swap.
Its ten assumption reports closed, with source/staging SHA-256
`896174f5641b6e4712de22f0f3f81b914158a0a4f6463a7beae85350483273a7`.
The model reuses byte-preservation proofs to establish identity and lookup
agreement for a shared supplied epoch, event-leg encoder, and outer framing.
It does not authenticate that context or prove the concrete Rust codec.
The two cost epochs share the v1 domain member, not necessarily their body
layout. No hash-injectivity premise is used.
Toy length-hash counterexamples demonstrate possible mismatched-preimage
lookup failures. They are distinct from the actual native regression tests.

Both new native admission controls failed before the edit and pass after it.
The node admission r4 gate passed **20/20**, including both controls under
`CostV1`/protocol 6 and `CostV2`/protocol 7.
Located-authority r3 passed **32/32**, including all thirty existing controls
and sixteen generated cases checked in both cost epochs.
The native-source parity gate passed **17/17** selected tests.
These checks support the three-site correction without proving collision
freedom, registry lifetime, or the full integration.
The ledger records the exact logs and model-to-test mapping.

The post-correction MeTTaIL native execution/replay r6 rerun passed **14/14**,
including signed-query native charging, replay, and explicit-source parity.
The earlier Casper, residue, and fixed-stack results retain their
pre-epoch-correction scope.
Campaign gates allow approved overlap with unrelated builds
under a 32 GiB cap, one campaign Cargo job, and no swap. Earlier query and
installed-carrier passes still certify only their recorded snapshots. Native
offer, funding, replay, and publication obligations remain separate; the
integration task and OSLF are not complete. No full suite or fresh public-node
demo has been run for this correction.

### Which execution relation must satisfy the cost laws?

The cost construction acts on the selected interaction dynamics of the guest
theory. Its admission obligation is therefore about that theory's source
derivations, not automatically about individual native Rholang communications.
For the installed-image route, reuse
[`AuthoredSourceExecution.RuleDerivation`](../../../formal/rocq/runtime_grammar/theories/AuthoredSourceExecution.v)
and the existing completed-frame/publication results. Establish the selected
source cut, its gated cases, wrapping preservation, and exact grades against
that relation and the actual source equation quotient.

Keep the three possible claims separate:

| Claim | Required correspondence | What it does not require by itself |
|---|---|---|
| An installed guest has a checked continued/Cost(G) presentation | Its actual source rules realize the selected interaction cut and cost construction, with section and wrapping evidence bound to that presentation. | Translating each guest rewrite into one native communication. |
| A particular guest-to-Rholang lowering preserves behavior | The selected lowering has the demonstrated strong or weak/trace correspondence, with the stated equation and signature obligations. | Strengthening a weak substitution cascade into one native step. |
| Guest grades are adequately funded by the host | The checked projection, authenticated native supply, complete candidate obligations, and native publication/replay checks compose. | Claiming that a funding map is a behavioral or quote-faithful theory morphism. |

The one-native-step hypothesis in
[`AuthoredCostInterpretation.v`](../../../formal/rocq/rho_bridge/theories/AuthoredCostInterpretation.v)
belongs to the second row when that strong interpretation is selected. It is
not a universal admission condition for the first row. The existing native
[`CIObj`](../../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/CACategory.v)
also deliberately models only the carrier, graded transitions, behavioral
equivalence, and reachable signatures used by its categorical results. Building
that record does not establish the manuscript's additional cut, section, and
wrapping data.

The public Regex application currently has no continued/Cost(G) declaration.
Its installed execution tests establish guest execution properties; they do
not select an interaction presentation or establish a quotient section. A
costed generic interpreter executing Regex would likewise not, without a
separate construction and correspondence, establish that the authored Regex
theory itself is Cost(G). Keep this distinction explicit when selecting the
positive end-to-end fixture.

The next admission batch must bind a complete selected presentation to its
source. It must not restart the completed construction/freshness work or turn
each remaining physical representation contract into an unrelated verification
project. Matching, collection decoding, intrinsics, and external guard verdicts
retain their documented implementation boundaries; use the existing models and
properties when composing the selected presentation's checks. A newly supplied
guard evaluator must justify its positive verdicts. The default unavailable
evaluator supplies none.

### Regex section: preserve the authored equations

The [public Regex theory](../../../rholang-runtime/tests/fixtures/regex_gslt_application.rho)
declares ten equations: three alternative identities, four concatenation
identities, and three star identities. It does not declare expansion of `PPlus`,
`POptional`, or `PRepeat` as an equation. Those constructors are interpreted by
the existing surface-evaluation rewrites. Executing a rewrite is not the same
as choosing a representative of the structural-equation quotient.

Consequently, the existing
[`elaborate_surface`](../../../formal/rocq/runtime_grammar/theories/RegexGsltMatch.v)
cannot simply be relabeled as the section for this presentation. For example,
consider the following algebra on Boolean values, used only as a mathematical
countermodel—not as Regex execution or a guest-to-host projection:

| Pattern constructor | Interpretation |
|---|---|
| `PFail`, `PEpsilon` | `false`, `true`, respectively |
| `PAlt`, `PConcat` | Boolean disjunction and conjunction, respectively |
| `PStar` | Constant `true` |
| `PLiteral`, `PAny` | Constant `true` |
| `PPlus` | Constant `false` |

All ten equations hold for every Boolean argument: `false` is the disjunction
unit and conjunction zero, `true` is the conjunction unit, disjunction is
idempotent, and every star expression denotes `true`. Other constructors may
be interpreted by constant functions; applying a function preserves equality,
so the equations remain valid in their surrounding contexts. Yet
`PPlus(PLiteral("a"))` denotes `false`, while its surface expansion
`PConcat(PLiteral("a"), PStar(PLiteral("a")))` denotes `true`. Equality generated
by those ten equations therefore cannot identify this pair. Surface elaboration
would fail representative correctness for this source quotient.

The historical
[`RegexEquationSchema`](../../../formal/rocq/runtime_grammar/theories/RegexGsltSyntax.v)
also contains expansion equations and lacks the source's nested-star equation.
Its sort-preservation theorem remains useful for the schemas it actually
defines; it is not an exact enumeration of the current application equations.
The next section check must bind to the actual source roster, including nested
star, and preserve the non-equated surface constructors. Changing the quotient
to include expansion or full regular-language equivalence is a separate
semantic proposal, not a repair needed to reuse the current matcher.

#### Reuse boundary for the exact-equation section

The adapter in
[`equation_section.rs`](../../../dovetail-runtime/src/semantic_transition_kernel/equation_section.rs)
uses the existing
[`CompiledRuleSet::from_rewrites` and `EGraph::saturate_compiled`](../../../dovetail/src/rules.rs),
then [`Extractor::funded_best`](../../../dovetail/src/extract.rs). It does not
send structural equations through directed semantic normalization, which
deliberately excludes equation origins. Compile the checked, reducing
orientation once and reuse its positional set automata.

Every selected equation collapses to an existing subterm or a declared
constant. The nested-star rule returns the inner star, not an arbitrary new
expression. The finite-carrier extension proves that a root contraction can
reuse an existing child handle or one of the two seeded constant handles.
Replacing a child by an equal-class handle also reuses its parent's cell;
this does not assert that the resulting contextual tree was an original
syntactic subterm. A successful merge is modeled as an onto map identifying
two distinct old classes. Strict class-count decrease follows, bounding the
number of successful merges by the initial carrier. These local results do
not prove the Rust union-find, matcher, or convergence report correct. They do
not make a node-limit or iteration-limit report a successful fixed point.
Source admission must establish the complete equation roster and resolved
constructor roles; additional equations cannot be silently ignored. Roles are
source identities, not hard-coded spellings such as `PAlt` or `PStar`.

The source checker is implemented in
[`source_equation_section.rs`](../../../grammar-core/src/source_equation_section.rs).
`check_source_equation_section` first validates the source/image pair, then
returns either a private borrowed `VerifiedSourceEquationSectionV1` or no
certificate for an unsupported valid profile. Invalid source/image pairs
remain errors. The certificate retains the exact source, semantic image,
resolved roles, and every equation's source index, orientation, schema, and
variable identity. Public witness coordinates cannot construct the private
certificate. Fixed-depth schema reads share the existing source-law arena
helpers; they do not traverse arbitrary substituted terms or allocate a
second term representation. The source-ordered witness vector uses fallible
allocation after bounded source/image validation.

Admission is independent of cost grading. The current Regex theory is
uncosted; requiring `VerifiedCostImageV1` would incorrectly exclude it. Reuse
that type's private, borrowed-certificate design, but bind the section to the
validated source and its **base** semantic image. Existing
[`TheorySemanticImageV1::validate`](../../../grammar-core/src/theory_image.rs)
checks their fingerprints, source programs, and compiled automata. The
installed owner's
[`base_semantic_image`](../../../grammar-core/src/installed.rs) is the relevant
image, not its projection-extended executable image.

The equation-role sort and the selected input carrier are distinct.
`SourceEquationSection::normalize` selects the role sort for convenience.
`normalize_in_sort` accepts an explicit root sort from the same authenticated
image. It applies the same rules within typed children and validates every
input and output against that selected root sort. It does not change the
equations, extraction, collection policy, or budget. The formal results already
cover arbitrary ordered contexts, so this entry point needs no second
normalization algorithm.

For Regex, the equation-role sort is `Pattern`, while guest computation states
have sort `Computation`. For example, normalization maps
`nullable(a|(?!))` to `nullable(a)` without executing `nullable`. The existing
operational rewrites still perform that computation. The selected-carrier
entry point does not itself prove totality for every value of the selected
sort or supply a continued interaction presentation. Its generated
foreign-carrier controls and installed-Regex selected-sort control passed the
recorded 401-test library and installed gates. The later carrier-admission
controls passed the separate 412-test library gate and installed Regex checks
for both `Pattern` and `Computation` certificates, as recorded in the
[verification ledger](../../architecture/oslf-integration-verification.md).

The five candidate roles—zero, unit, alternative, product, and closure—must
resolve to distinct constructors of arities `0, 0, 2, 2, 1`, respectively,
on the selected sort. Recognition checks every source equation, with no
premises, in either authored orientation, and requires coverage of all ten
schemas. This permits duplicate instances of an admitted schema; it does not
require exactly ten rows. Compare source variable identities, not arena-node
indices: two nodes referring to the same input variable express the same
variable. Wrong roles, conditional equations, missing schemas, unsupported
extra equations, and stale source/image pairs cannot mint the certificate.
Diagnostic schema coordinates remain inspectable data, not authority to bypass
these checks.

Orientation-neutral schema recognition does not bypass whole-source admission.
The existing source validator requires right-hand variables to be available
from the authored left-hand side. Reversing the erasing product-zero equations
would introduce an unavailable variable and is therefore a source error today.
The other eight schemas can be tested in either admitted orientation. The
mathematical schema reader's all-reversed control checks recognition only,
not acceptance by the complete source validator. This section adapter does
not relax that validator.

`SourceEquationSection::restore` selects each compiled program by its exact
`Equation { source, direction }` origin, rejecting missing or duplicate
programs. It reuses `flat_pattern_from_roots`, converts the admitted positional
nodes to the existing `Pattern` representation, and constructs one reusable
`CompiledRuleSet`. No equation-index arithmetic, new rule compiler, matcher,
or weight algebra is introduced.

`normalize` consumes an exact `SemanticTransitionInput`. The existing Horn
ground-term validator checks its source sorts, constructor arities, and typed
payloads. A memoized, explicit postorder traversal counts each child edge,
including repeated edges, before invoking saturation. After selected
extraction, another explicit postorder traversal reconstructs the typed
derivation through the existing exact e-graph interner. Traversal memoization
uses live `Rc` addresses only to avoid revisiting the same derivation node;
addresses never determine semantic equality.

The returned `EquationSectionReport` retains both saturation reports and the
exact admitted normal form. `boundary_work` includes input-admission work,
typed validation, representation traversals, stage checkpoints and final
admission. It explicitly excludes unreported internal saturation/extraction
operations. Cancellation is checked at those boundaries, not inside the
existing engine calls. `egraph_nodes`, `saturation_iterations`, term-size
bounds and checked unfolded counts provide separate limits. An exhausted
limit is an error, not a smaller accepted quotient. This resource contract
does not authorize use as an already instruction-metered native service.

The acceptance argument has three distinct parts:

1. Every equality added to the private section graph is an instance of the
   admitted source equations or their congruence closure.
2. The selected finite output contains no reducible occurrence of those
   equations. Check this using the same compiled matcher on the output graph,
   not the saturated graph, which intentionally retains reducible equivalents.
3. The exact admitted equation family has unique normal forms. Equivalent
   inputs therefore yield the same accepted representative, independently of
   allocation order, rule order, or extraction tie-breaking.

The formal section and this bounded executable interface are distinct. The
section needs totality, representative correctness, and quotient invariance.
The runtime may report resource exhaustion rather than return a certificate.
Use existing node, iteration, and output limits; check unfolded occurrence
counts separately from the number of shared e-nodes. A compact shared graph
can denote a much larger unfolded tree. In a backward-reference arena, compute
each node's unfolded size as one plus the sum of its children's sizes, counting
each edge occurrence, including repeated references. Use checked addition and
refuse overflow or an exceeded allowance. The source validator's occurrence
counter, which deliberately saturates at two for a different check, is not an
exact size measure.

The current saturation API supplies node and iteration limits. It does not
supply a per-operation work or cancellation parameter, and neither does
`funded_best`. Those existing limits must not be described as an already
implemented work-accounting or cancellation guarantee. Record the concrete
resource contract when composing these APIs; successful equation certification
alone grants no native funding authority.

A fixed positive node weight can guide existing extraction toward a normal
form without reusing authored parser priorities or semantic resource grades.
The current tropical weight uses floating-point arithmetic. Exact integer
node-count comparisons require an explicit representable-count bound, with
overflow or exhausted allowance reported as refusal, not rounding or clamping.
That optimization/completeness argument is not the accepted-output soundness
argument: source-equation membership, irreducibility, and unique normal form
establish the latter. No new weight algebra is implied by this proposal.

Collapse equalities can create productive cycles in the saturated e-graph.
Use the selected-derivation result of `funded_best`, with its explicit
completeness status; do not require enumeration of every cyclic expansion.
Selecting a unique representative of one structural-equivalence class is not
pruning competing semantic transitions. Run this operation on a private graph
and retain all candidates in ordinary guest execution and lookahead.

Reconstruction must preserve the typed operator and exact payload. Reuse
[`report_from_extraction`](../../../dovetail/src/report.rs) or the selected
typed derivation; the UI-oriented `project_dovetail_report` uses display
strings and is not a lossless reconstruction interface. Ordered children and
repeated edges remain significant. A candidate implementation of the
irreducibility check is a second saturation on a fresh, unmerged output graph
using the same compiled rules, accepting only convergence with no merges.
The source review establishes the following required preconditions; they
remain executable correspondence obligations, not consequences of the
convergence label alone:

- Load the entire finite, acyclic output graph without merges, so class
  equality means exact syntactic equality. Seed the zero and unit constants.
  Partial loading is refusal, not a smaller accepted output.
- Preserve ordered children. The existing machine loader supports a
  `CanonicalExactKey` mode that sorts children; positional section terms must
  instead use `Ordered`. Loader success does not establish source sort or
  constructor-arity validity; source admission establishes those separately.
- Use only the complete ten decreasing positional rules. Every right-hand
  variable occurs on its left, and no native callback or unrelated rule is
  included.
- Run at least one complete iteration and require both `Converged` and
  `stats.total_merges == 0`. A node-limit result or a nonzero merge count is
  refusal. One iteration suffices to check irreducibility; it does not suffice
  to normalize every input.

Under these conditions, each genuine match has a strictly smaller right-hand
tree, so its root cannot already be the same class in the fresh exact graph.
The existing positional matcher visits every class, including repeated-variable
constraints; the existing application path therefore records a merge. All ten
right-hand sides are existing subterms or seeded constants. If a fresh
allocation nevertheless exceeds the graph budget, the engine's sticky limit
flag produces `NodeLimit`, not accepted convergence.

The preconditions matter. An already-merged class containing both `Alt(a,a)`
and `a` may converge without any **new** merge while retaining the redex.
An ill-formed `f(x) -> y` rule skips an unbound right-hand variable, and the
nondecreasing rule `f(x) -> f(x)` can match without a merge. None belongs to
the admitted section profile. These are negative controls for the adapter,
not reasons to alter ordinary saturation semantics.

#### Formal-to-executable verification obligations

The kernel-checked
[`SourceEquationSection.v`](../../../formal/rocq/runtime_grammar/theories/SourceEquationSection.v)
uses the existing structural `LogicTerm` and resolved source arena. Its
reference normalization function proves the equation quotient; production
execution continues to use the existing saturation and extraction machinery.
Compilation and independent kernel checking passed under a 512 MiB memory cap;
the [verification ledger](../../architecture/oslf-integration-verification.md)
records the source-bound evidence. The first row's generic admission tests
have passed in the full affected library suites. The additional installed
Regex control admitted the real equation roster, then exposed an incorrect
test assertion between the base and projected language identities. The test
now checks the distinct source, base-image, projected-image, and installation
links. The corrected installed-Regex test passed. The remaining
rows describe the runtime section adapter's required properties. The adapter
and its
[`runtime` tests](../../../dovetail-runtime/src/theory_image_compiler/tests/equation_section/runtime.rs)
passed the affected library gate (157 Dovetail-runtime and 237 grammar-core
tests). This verifies the raw equation adapter, not the subsequent collection
composition described below; the verification ledger records that distinction.
Checked integer overflow is exercised directly at the private count helper:
fabricating an exponentially large exact-key input is not necessary to test
that arithmetic boundary. Small shared arenas separately exercise the public
occurrence limit and repeated-edge semantics.

| Formal result | Executable property and negative controls |
|---|---|
| `admitted_roster_is_exact_and_complete`, `schema_reader_preserves_actual_source_nodes` | Admit renamed roles, either source-valid orientation, reordered and duplicate schema instances, variable-ID renaming, and shared or duplicated arena nodes. Remove each schema, add a conditional or unsupported equation, change a role or sort, and require refusal. Reject stale image ownership and reversed erasing equations separately through existing image/source validation. |
| `every_contextual_collapse_strictly_decreases_occurrences`, `collapse_reduction_terminates` | Check every reducing schema in generated nested contexts; count repeated child edges exactly. Exercise checked-count overflow and bounded refusal using compact shared arenas, without allocating their unfolded trees. |
| `every_term_has_a_reachable_normal_form`, `congruence_iff_equal_normal_forms` | With sufficient limits, run the real compiled rules and selected extraction on generated terms and both sides of each instantiated equation. Their accepted normal forms must agree. Keep `Plus`, `Optional`, and `Repeat` opaque except for normalization of their children. |
| `admitted_source_section_is_sound_and_idempotent` | Applying the real section adapter to its own accepted output returns the same exact typed term. Preserve payload bytes, ordered children, and repeated edges, including inside opaque constructors. |
| `admitted_source_section_is_quotient_invariant`, `accepted_outputs_do_not_depend_on_extraction_order` | Reorder equation declarations, e-graph insertion, and shared-node layout. For equivalent inputs, compare the exact accepted output rather than allocation-specific class IDs. |
| `admitted_source_accepted_output_is_exact` | A fresh output graph must pass the same compiled-rule irreducibility check. Exercise nonlinear alternatives and productive nested-closure cycles; refuse incomplete extraction, partial loading, and exhausted saturation. Preserve the three invalid-precondition controls above. |

The structural model's operator tags are not source constructor IDs. Exact
typed-operator/payload encoding, declaration membership, source-owner binding,
and physical matcher/extractor correspondence are separate obligations. The
model neither authenticates arbitrary witness strings nor establishes the
remaining continued cut, wrapping, or funding laws.

The equation-family proof and generic source-admission library gates have
passed. The installed-source control and runtime composition with its
model-derived tests must also pass before an output can certify a continued
presentation. The source
cut factorization and wrapping evidence remain separate requirements; a section
alone does not establish Cost(G).

#### Collection composition and the section domain

The ordered-context proof must not be mistaken for a proof that normalization
preserves every built-in collection invariant. A valid Set containing `a`
and `Alt(Zero,a)` has two exact-distinct elements before normalization and two
equal elements afterward. Bags can become misordered, and Map or PathMap keys
can collide. The current adapter's final typed validator refuses such an
invalid reconstruction; it does not publish it. That safety check alone does
not establish success for valid inputs with adequate resources.

The existing
[`canonicalize_collection_children`](../../../dovetail-runtime/src/semantic_transition_kernel.rs)
is the required implementation reuse point. It preserves List order, sorts
Bags without dropping multiplicities, and sorts and deduplicates ordinary
Sets. Map and PathMap construction instead reject duplicate keys, even when
the values agree; PathMap Set mode also rejects duplicates and retains its
explicit mode. A section adapter must not introduce last-write-wins behavior,
freeze equation-reducible keys, or silently drop Map entries.

Reconstruction and equation normalization need a joint fixed point: Set
deduplication can make two enclosing `Alt` arguments equal and thereby expose
another equation redex. The implemented composition reuses the same compiled
equations, engine and collection canonicalizer, with a separate proof that
collection canonicalization does not increase occurrences and every continued
round includes a strictly decreasing equation contraction. The finite-carrier
reuse theorem applies to each equation phase; it does not claim that sorting
or deduplication preserves the original node shapes.

The coordination keeps the raw equation check separate from the collection
check. The following pseudocode describes that boundary; `probe` invokes the
existing compiled matcher for one iteration, rather than implementing another
redex detector:

```text
validate the admitted source and record its unfolded occurrence count
repeat:
    saturate the private graph with only the certified equation directions
    extract and reconstruct a raw representative
    require the raw probe to converge with zero merges
    canonicalize reachable collections using the existing constructor
    validate the resulting exact typed term and count its occurrences
    require nonincrease on the first pass, strict decrease on continued passes
    if there were no reachable collections, publish the checked result
    probe the canonical term and retain that probe's actual engine report
    if the probe converged with zero merges, publish the checked result
    otherwise continue only after a positive merge, keeping its graph private
```

Every engine call consumes the same invocation's remaining iteration allowance;
validation and reconstruction likewise share one boundary-work allowance. A
positive probe mutates its graph, so it must not be presented as a fresh
single-representative input. Its pre-probe canonical occurrence count remains
the next round's progress measure. Reports keep the saturation, raw check, and
optional collection probe separate and ordered. Their class identifiers are
local to the corresponding graphs; these reports are not independently
replayable source certificates or native funding receipts.

The additional
[`SourceEquationCollections.v`](../../../formal/rocq/runtime_grammar/theories/SourceEquationCollections.v)
proof passed compilation and independent kernel checking before the runtime
composition was changed. Its implementation tests reuse the source compiler
and term-construction engine to prepare both inputs and expected collection
values. The affected suites passed 399 tests; exact commands, scope, and proof
hashes are recorded in the [verification ledger](../../architecture/oslf-integration-verification.md).

| Model obligation | Executable correspondence |
|---|---|
| Existing collection equality and nonexpansion | Generated Bag cases force a real key-order reversal and retain every multiplicity. Generated Map and map-mode PathMap cases preserve each key's associated value while reordering entries. |
| A collection pass can expose an equation redex | Generated Set cases collapse distinct source members, deduplicate, and require a subsequent equation phase for the enclosing `Alt`; reapplying the adapter preserves the result. |
| Strict descent and finite coordination | The runtime compares unfolded occurrences before the mutating probe. Continued rounds require strict descent; the Set property also verifies the exact cumulative all-call iteration allowance and one-iteration-short refusal. |
| Duplicate-key refusal and domain boundaries | Generated Map and both valued PathMap-mode cases refuse normalized key collisions, including equal values. Both annihilation directions may erase the problematic branch before reconstruction without publishing it. |
| PathMap mode preservation | The three empty modes remain distinct and retain their exact authenticated mode markers. |

The additional
[`SourceEquationCollectionUniqueness.v`](../../../formal/rocq/runtime_grammar/theories/SourceEquationCollectionUniqueness.v)
now proves uniqueness for the combined quotient. Its proof-only observation
reuses the equation model's smart constructors and the existing generic sort.
It preserves Bag multiplicity, Set membership, whole Map entries, and PathMap
mode markers. Whole-entry observation is defined even when intermediate keys
collide; it does not authorize publishing those intermediate values. On a
jointly normal output, the observation determines the exact canonical term.
Invariance under equations and collection equality therefore proves that
successful runs agree and successful reruns are idempotent.

Compilation and independent kernel checking passed with nine closed-context
reports. This proof adds no namespace restriction or collection collision
policy. The corresponding generated property compares successful results
across collection order, arena sharing, and equation placement. It passed in
the updated 400-test affected-library gate. That gate also checks randomized
equation-roster order in the existing runtime normalization property.
Conditional domain completion still requires its stated closure
evidence, rather than merely a uniqueness theorem or passing collection test.

There is also a genuine totality boundary. A Map with distinct keys `a` and
`Alt(Zero,a)` cannot retain both entries and have fully equation-irreducible,
unique keys. More fuel cannot resolve that contradiction. Collision refusal
must remain explicit. A total continued-theory section therefore needs
source-bound domain-closure evidence, such as equation-invariant key sorts;
the exact-equation roster alone is insufficient. Failure of a particular
section checker is not rejection of language installation or proof that no
other section construction exists. The installed Regex `Pattern` closure
contains `Pattern`, `Scalar`, and `Nat`, not unordered collections, but this
fact must not substitute for the generalized composition obligation.

### Selected-carrier domain admission

The selected carrier is the sort of the term being normalized. It need not
be the sort on which the equations are declared. A carrier certificate must
bind that sort to the already checked source and base semantic image. It must
not infer safety from a category name or from the absence of a collection in
one example term.

The model in
[`SourceEquationCarrierDomain.v`](../../../formal/rocq/runtime_grammar/theories/SourceEquationCarrierDomain.v)
extends the existing equation and collection proofs with typed child contracts.
Compilation and independent kernel checking passed on 2026-10-12 under a
512 MiB hard memory cap with no swap, with fifteen closed primary assumption
reports. The [verification ledger](../../architecture/oslf-integration-verification.md)
records its exact source hash and log. Its local key invariant requires distinct keys
to remain distinct under the combined equation/collection observation. This
does not discard values, merge colliding Map entries, or change PathMap modes.
For an ordinary canonical input, equation-inert key sorts are sufficient:
their values have no reachable equation redex, so their canonical identities
cannot collapse during normalization.

The result establishes a mathematical completion in the combined relation for
each well-typed, collection-canonical input in an admitted carrier. It reuses
the explicit exact-key reflection and collection-profile premises. It does not
prove that a fixed resource budget suffices, authenticate the source-to-table
projection, or verify the physical Rust matcher, extractor, and collection
builder. Agreement of successful results reuses the earlier combined-quotient
uniqueness theorem; it does not require the sufficient inertness test to accept
every possible safe carrier.

The admission adapter must reuse the existing runtime operator-signature and
keyed-collection checks. These determine the dependency edges below.

| Typed operation | Dependency from its result sort |
| --- | --- |
| Declared constructor | Every declared argument sort, in its original signature |
| Abstraction | Binder-domain and body-codomain sorts |
| Substitution | The function sort and its argument-domain sort; the result is the function's codomain |
| Product | Every factor, without an arity limit |
| List, Bag, or Set | Its element sort |
| Map | The checked physical entry Product's key and value sorts; its internal entry contract is not an arbitrary value of the pair sort |
| PathMap | All declared modes: no values in neutral mode, keys in set mode, and the checked entry Product's key/value sorts in map mode |
| Literal | No child sort; retain the existing exact payload and carrier check |

Constructor dependencies also apply to ordinary values when their result has
a rich carrier kind. In particular, following only a sort declaration misses substitutions whose
result is that sort but whose function declaration is elsewhere in the image.
PathMap mode markers and Map entries remain internal child contracts, not new
guest categories or freely constructible standalone values.
The implementation must check `runtime_keyed_collection_sorts` and the physical
Product signature, then follow the key and value dependencies directly. A
general edge from Map to the pair's ordinary value sort would also follow
unrelated constructors returning that sort, even though those constructors
cannot serve as physical Map entries. Such an edge is not the model's
`EntryType` contract.

The bounded iterative check is:

```text
Read the authenticated signature tables with the existing signature checks.
Build ordinary result-to-child edges and their reverse edges.
For keyed collections, validate physical entry/mode contracts and follow only
    their declared key/value dependencies; do not substitute broad pair-sort edges.
Visit dependencies from the selected root sort.
Visit reverse dependencies from the equation-role sort.
For each reachable Map or PathMap:
    If its key sort can reach the equation-role sort, return no certificate.
Return a certificate bound to this owner and selected root sort.
```

Each table entry, edge, and worklist step must consume the declared admission
budget and check cancellation. Use fallible, bounded storage and no recursive
traversal. This is a signature analysis, not another term normalizer. Failure
of this sufficient key-inertness check means that this check did not establish
a universal domain. It must not reject ordinary language installation or
otherwise successful bounded `normalize_in_sort` calls. Invalid identities,
resource exhaustion, cancellation, and allocation failure remain distinct
from that unsupported-evidence result.

The theorem-to-implementation obligations are:

| Formal result | Implementation and property obligation |
|---|---|
| `source_product_projection_retains_arbitrary_arity`, `source_substitution_projection_retains_function_identity`, `source_literal_projection_retains_payload_and_carrier` | Project the checked owner tables into the existing operator contracts. Vary Product arity, constructor names/order, function domain/codomain, exact literal payloads, and source IDs; include a substitution whose result sort is reached only through another declaration. Do not infer dependencies from sort declarations alone. |
| `contextual_equations_preserve_selected_carrier` | Exercise [`normalize_in_sort`](../../../dovetail-runtime/src/semantic_transition_kernel/equation_section.rs) with a selected sort distinct from the equation-role sort. Preserve the outer constructor and exact output sort; refuse a wrong requested sort and malformed typed inputs. The 24-case selected-carrier property passed in the 401-test library gate, alongside the separate installed Regex selected-sort control. |
| `finite_closed_key_domain_is_equation_inert`, `equation_inert_typed_terms_are_irreducible` | Check complete forward/reverse dependency closure, including cycles, declared constructors of ordinary rich-sort values, all function dependencies, and every PathMap mode. Admit reachable collections with inert keys and equation-active values; return no certificate for keys that reach the equation sort. The passing physical-entry control shows that an unrelated constructor returning a pair sort does not invalidate a checked Map/PathMap entry contract. |
| `canonical_input_with_stable_key_sorts_is_in_domain` | Bind the carrier certificate to the exact source, base image, and selected root. Use existing typed collection admission to retain sibling-key uniqueness, Map entry Products, and PathMap mode markers. Reject foreign owners and forged coordinates; ordinary installation remains available when this sufficient check finds no certificate. |
| `typed_equations_preserve_key_domain`, `canonical_pass_available_in_typed_key_domain`, `typed_key_domain_is_closed` | Compose the existing equation engine and collection canonicalizer without losing Bag multiplicity, Set semantics, Map values, or mode identity. Retain collision refusal for uncertified domains and all shared budget/cancellation refusals. The eleven new carrier-admission checks passed in the separate 412-test library gate. |
| `stable_selected_carrier_has_mathematical_completion`, `stable_selected_carrier_successful_results_agree` | On admitted generated carriers, check completion with adequate measured limits, exact rerun identity, and agreement across equivalent inputs and engine orderings. Preserve refusal at exhausted limits. The 401-test selected-sort and 412-test carrier-admission gates are distinct from the previous 400-test collection gate. The subsequent installed Regex test passed with carrier certificates for both `Pattern` and `Computation`. |

[`check_carrier_domain`](../../../dovetail-runtime/src/semantic_transition_kernel/equation_section/carrier.rs)
now implements this owner-bound check. Its
[`eleven focused tests`](../../../dovetail-runtime/src/theory_image_compiler/tests/equation_section/carrier_domain.rs)
comprise four 16-case properties, four 12-case properties, and three explicit
owner, physical-entry, and resource-bound controls. The corrected affected
library gate passed all 175 Dovetail-runtime and 237 grammar-core tests. The
first run's binder fixture used a non-progressing operational rewrite; its
replacement preserves the same abstraction/substitution coverage while meeting
the existing source validator's progress requirement. No validator or collection
collision policy was relaxed. The [verification ledger](../../architecture/oslf-integration-verification.md)
records the completed library and installed certificate results. The installed
test passed in 136.08 seconds, with zero failures or ignored tests and 690
unrelated tests filtered out. It checks each certificate's selected root and
exact source-section owner, as well as normalization in both carriers. These
executable checks do not prove the entire physical engine or
the remaining continued cut, wrapping, and funding obligations.

### Implemented source-local check: signature monoid equations

The signature sort and its unit and product constructors already have explicit
identities and type checks. Unlike the unresolved witness strings, they provide
an unambiguous starting point. The continued-GSLT construction requires their
quotient to satisfy the commutative-monoid laws: associativity, commutativity,
and a unit law.
These are laws of the signature product, not of the interaction cut or token
stack. The manuscript permits noncommutative interaction cuts and requires
token stacks to retain sequential order. This check changes neither.

Reuse the validated `TheoryEquationV1` arenas to recognize unconditional
instances of these schemas, allowing either equation direction:

```text
product(product(x, y), z) = product(x, product(y, z))
product(x, y) = product(y, x)
product(unit(), x) = x
```

Here `product` and `unit` denote the resolved constructor identities, not
mandatory names. The displayed variables are distinct signature-sort input
variables. A right-unit schema can replace the left-unit schema because
commutativity derives the other side. Compare variable identities, not arena
node indices: a source may represent the same variable with multiple nodes.
Diagnostic names, equation order, sharing, and unrelated arena nodes must not
affect the result. Premise-bearing equations cannot certify unconditional laws.

This is a sufficient source-law check, not an equality-saturation search or a
new normalizer. Return the exact equation identities and orientations used.
Failure to find the schemas means *not certified by this check*, not that the
laws are false. Keep this certificate separate from ordinary exact grade-row
validation; do not impose a new meaning on `cost.laws`.

The proof must connect successful recognition to equation instances for all
substitutions in the congruence generated by that source presentation. Reuse
[`ExecutableTheoryCore`](../../../formal/rocq/runtime_grammar/theories/ExecutableTheoryCore.v)
for arena, variable, and constructor types. The existing
[`SignatureMonoid`](../../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/SignatureMonoid.v)
proves the native algebra, but does not inspect authored equations. Its native
laws must not be relabeled as this source-admission proof.

Test renamed constructors and variables, reversed equations, reordered laws,
and shared or duplicated variable nodes. Reject wrong constructors, repeated
variables in distinct schema positions, incorrect sorts, conditional laws,
and missing schemas. Additional equations may collapse signatures while still
preserving all monoid laws. This certificate therefore does not establish a
canonical section, faithful interpretation, or full Cost(G) certification.

#### Certificate interface and execution boundary

The entry point is
[`VerifiedCostImageV1::check_source_signature_acu`](../../../grammar-core/src/cost_image/source_laws.rs).
ACU abbreviates *associativity, commutativity, and unit*. It returns a checked
certificate only when all three obligations have source witnesses. An absent
certificate means this sufficient check could not establish the laws; it is
not a negative logical verdict about the theory.

The certificate retains the borrowed, already verified cost image and the
three source-equation witnesses. Each witness records its equation index,
orientation, and variable identities; the unit witness also identifies the
left or right unit law. The certificate's constructor remains private, and it
is not accepted from serialized data. Its diagnostic witnesses can be inspected
without allowing a caller to turn arbitrary witness data into a certificate.
Keeping the verified owner preserves the source binding without recomputing a
fingerprint for each equation. This is algebraic evidence, not an installed
language handle or a capability to spend native resources.

The checker searches the existing source order independently for each law.
It retains the first checked witness, trying both equation orientations and
both unit sides:

```text
resolve signature sort, unit, and product from the verified cost image
for each obligation in [associativity, commutativity, unit]:
    search authored equations in source order:
        skip equations with premises
        inspect both orientations using borrowed arena nodes
        retain the first witness that establishes this obligation
    if no witness was found, return no certificate
return the three witnesses in a certificate bound to this verified image
```

Choosing a witness does not choose a runtime transition or discard a semantic
candidate. Each witness independently establishes the same universal law.
The checker performs fixed-depth lookups for these finite schemas. It needs
no heap-allocated syntax tree, recursion over the authored theory, or equality
saturation. With the source's name lengths accounted for, work is linear in
the number of inspected equations and auxiliary storage is constant. This is
an admission-time operation, not part of each rewrite step.

The binary-product and nullary-unit checks come from their declared signature
types. They do not impose a maximum arity or nesting depth on other theory
constructors. A deeper or differently presented proof of a monoid law may be
valid but is outside this schema check's completeness claim.

#### Proof and test correspondence

The formal checker and its generated source congruence are defined in
[`SourceSignatureMonoidAdmission.v`](../../../formal/rocq/runtime_grammar/theories/SourceSignatureMonoidAdmission.v).
The congruence is generated by actual unconditional source-equation instances,
reflexivity, symmetry, transitivity, and compatibility with the signature
product. No monoid law is assumed as a generating rule. Its carrier and
substituted values are arbitrary; the schema-depth bound does not restrict
the depth of substituted signature values or exclude other generators.

The following table defines the verification obligations. The presence of a
proof or test source is not itself a passing verification result.

| Invariant | Formal result | Executable property or control |
|---|---|---|
| Exact source nodes and Input-variable identities, independent of node sharing | `read_schema_term_retains_actual_source_shape`, `checked_equation_has_exact_source_schema` | `signature_acu_survives_renaming_order_reversal_and_variable_sharing` |
| The declared constructor roles matter; a same-typed replacement is not implicitly the same operation | `checked_equation_has_exact_source_schema`, `wrong_constructor_is_not_a_signature_law` | `signature_acu_rejects_another_product_with_the_same_signature`, `signature_acu_rejects_another_unit_with_the_same_signature` |
| All three obligations have exact source-equation witnesses | `admitted_acu_retains_three_exact_source_witnesses` | `signature_acu_requires_every_source_law_despite_metadata_labels` |
| Distinct universally quantified positions cannot alias one source variable | `distinct_source_variables_give_universal_law` | `signature_acu_rejects_repeated_variable_ids_even_with_distinct_term_nodes` |
| A premise-bearing equation is not an unconditional law | `premise_bearing_equations_are_refused` | `signature_acu_rejects_conditional_laws_and_non_input_unit_variables` |
| Either unit side suffices, and orientation is retained | `admitted_source_equations_generate_acu` | `signature_acu_accepts_both_unit_sides_and_orientations_with_an_empty_roster` |
| Schema recognition adds no global arity or term-depth restriction | `source_witness_establishes_every_substitution` quantifies over arbitrary carrier values | `signature_acu_schema_depth_does_not_limit_unrelated_terms_or_constructor_arity` checks the executable boundary; it does not replace the universal theorem |
| Evidence belongs to the supplied source and verified image | `found_law_retains_source_equation_and_orientation`; immutable image ownership remains a separate existing boundary | `signature_acu_certificate_retains_its_exact_source_bound_cost_image` |
| An earlier failed schema does not hide later evidence; later duplicates do not replace the first checked witness | `find_source_law` defines the source-order scan; `found_law_retains_source_equation_and_orientation` proves the retained source link, not a separate minimal-index theorem | `signature_acu_skips_earlier_near_misses_and_retains_first_checked_witnesses` |

[`generated_congruence_is_least`](../../../formal/rocq/runtime_grammar/theories/SourceSignatureMonoidAdmission.v)
connects the result to any full source congruence containing those equation
instances and the usual closure rules. This is not a completeness theorem for
bounded equality saturation or a proof of the Rust compiler. Property tests
exercise the implementation-to-model correspondence using the actual source
validator and semantic-image compiler, not a second parser or evaluator.

The actual compiler also rejects non-progressing equations before this checker
is reachable. `reflexive_product_equation_is_rejected_before_signature_certification`
checks that a well-typed `product(x, y) = product(x, y)` source cannot bypass
that existing gate. The test does not manufacture a verified image to exercise
an otherwise unreachable input.

The model and its `ExecutableTheoryCore` dependency were freshly compiled on
2026-10-11, then independently kernel-checked under a 512 MiB memory limit.
All thirteen primary assumption reports were closed. The log is
`target/verification/source-signature-monoid-20261011.log`; both staged source
copies match the current files. The production checker is a reviewed handwritten
translation, not extracted Rust or a mechanized proof of Rust execution.
Its example and property tests are in
[`signature_laws.rs`](../../../dovetail-runtime/src/theory_image_compiler/tests/signature_laws.rs).
All twelve focused tests passed in the fresh 125-test library run on
2026-10-11, including four properties with 32 generated cases each. The log is
`target/verification/source-signature-acu-runtime-20261011.log`.
The [verification ledger](../../architecture/oslf-integration-verification.md)
records executable gate results separately from these proof results.

### Remaining whole-source interpretation

The next interpretation proof must cover the installed source relation, not
only a convenient constructor-only release rule. The
[`RegexGSLT` application](../../../rholang-runtime/tests/fixtures/regex_gslt_application.rho)
uses equations, recursive transition premises, and intrinsic computations.
It does not yet declare a continued/Cost(G) presentation. A certificate for
the manuscript's CCS release example would not certify that application.

The installed route owns the installed language, restored matcher, selected
image route, and authorized handle in
[`InstalledSemanticBundle`](../../../rholang-runtime/src/semantic_service.rs).
It executes typed semantic images through the existing
[`SemanticTransitionMatcher`](../../../dovetail-runtime/src/semantic_transition_kernel.rs).
The existing in-Rholang lowering instead consumes the macro-era language and
pattern representation. These paths have reusable results, but their source
representations and proof premises must be connected explicitly.

The *base image* contains the source-exact guest presentation. Its projection
extension also contains the admitted host signature and projection programs.
They have different fingerprints. The existing bundle uses the extended
execution image for an uncosted installed roster; a costed roster instead
selects the base route to retain its checked cost-image association. Source
correspondence must authenticate the selected execution image and its link to
the base presentation, not assume those image fingerprints are equal. The
uncosted Regex properties check the execution fingerprint against the install
commitment and separately check the projection's base-image commitment.

| Required connection | Reuse and remaining obligation |
|---|---|
| Source rule to published successor | Reuse typed arena/image reference preservation, the actual match substitution, ordered premise execution, and same-substitution RHS/grade construction. Establish that each published candidate denotes a source derivation; do not assume that conclusion as the input. |
| Equations and binding | Preserve the equation-generated congruence and capture-avoiding substitution. Reuse the existing admitted equation-family and substitution machinery; cover other required families explicitly rather than substituting a hash for an equality proof. |
| Complete source coverage | Account for the installed rule roster, recursive transitions, intrinsic premises, and retained alternatives. A finite release-only fragment does not discharge the full source obligation. |
| Cost construction | Bind the selected cut and wrapping construction to that source relation, its substitutions, and its structural equations. Typed grade rows and signature ACU evidence do not themselves construct Cost(G). |

Binding computation already exists in
[`rho_net_lower.rs`](../../../rholang-codegen/src/rho_net_lower.rs), including
`subst_rule_shape`, `lower_subst_rewrite`, and the substitution term-rewriting
system (TRS). The
[`DeBruijnSubstTRS`](../../../formal/rocq/rho_bridge/theories/DeBruijnSubstTRS.v)
and [beta-cascade correspondence](../../../formal/rocq/rho_bridge/theories/InRhoBetaCascadeWeakBisim.v)
results prove its computation and weak operational correspondence. A typed
semantic-image `Substitution` operator or a sort-preservation theorem alone
does not establish that execution connection. Conversely, seeing an ordinary
operator inserted into an arena is not evidence that binding computation is
absent elsewhere. Reuse requires the actual lowering and execution bridge.

The [whole-GSLT correspondence model](../../../formal/rocq/rho_bridge/theories/WholeGsltInRhoOpCorrespondence.v)
retains source-relation, per-family simulation, and complete-installation
coverage premises. Importing its capstone does not instantiate those premises
for an installed theory image.

Transition granularity also matters. `AuthoredCostInterpretation` currently
assumes one native graded step per source step. The beta-cascade result uses
one visible firing and a sequence of internal reductions. That weak/trace
result does not prove the stronger single-step premise. Keep the single-step
theorem for interpretations that satisfy it, and compose a general execution
bridge at its demonstrated transition granularity. Internal native work must
retain its accounting obligations; being observationally internal does not
make it free. The existing
[ordered trace-funding contract](../../architecture/cost-g-trace-transport.md)
is a reuse boundary, not proof that the missing source/execution connection
already exists. This plan does not replace the installed evaluator or mandate
routing every installed invocation through the in-Rholang lowerer.

#### Source-frame and publication composition

The new [source execution model](../../../formal/rocq/runtime_grammar/theories/AuthoredSourceExecution.v)
defines a resolved source view and finite derivations for rules, ordered
premises, quantified premise bodies, and Horn judgments. A *derivation* is
evidence for a particular execution, not an assumption that all recursive
executions terminate. The source view retains multi-source `Map`, `Product`,
typed literal payloads, judgment identity and arguments, all six intrinsic
opcodes and their slots, and guard payloads. These fields were erased or absent
in the older `ExecutableTheoryCore` abstraction. Source IDs, variable
declarations, scoped substitutions, nested-return operations, and quantified
scope operations reuse the existing models.

A *frame* is one active rule instance. Its environment maps that instance's
variables to values. The invariant records exactly which ordered premise
prefix has completed, the resulting environment, and the remaining suffix.
For a successful completed-operation trace, the model establishes a derivation
for the exact source occurrence, with both RHS and grade instantiated under
the final environment. A child transition exports only its declared target;
a quantified body's private bindings do not replace the saved outer scope.

For example, the actual test fixture adds a rule whose pattern is
`Wrap(source)`, whose premise reduces `source` to `target`, and whose result is
`target`. Its grade is `SigOfExpr(target)`. The initial match does not bind
`target`. After the child completes, **both** the result and the grade must
use that derived value. Computing the grade from the original `source`, or
from the initial substitution, would violate the contract even if its sort
were correct.

The proof decomposition mirrors the existing operations:

```text
resolve the exact source rule and observe its complete LHS match
retain the ordered premise roots and the initial environment
for each completed premise operation:
    establish that operation's source premise derivation
    extend the proved prefix with that premise, retaining its final environment
when the pending sequence is empty:
    instantiate the source RHS and declared grade from that same environment
    derive the complete source rule instance
publish only an unchanged candidate produced from such a completed frame
```

This is proof pseudocode, not a second executable evaluator. Runtime search
still uses the existing iterative frontier and frame stack. The formal
`FrameRun` abstracts **completed operations**, not every physical stack push,
pop, allocation, or scheduling step. Nested returns consume a finite child
source derivation; separate lemmas construct it from a completed child frame.
Horn and quantified-premise operations likewise require their source proofs.
Independent replay of the runtime's flat premise receipts is not established
by these statements.

[`SemanticPublicationProvenance`](../../../formal/rocq/runtime_grammar/theories/SemanticPublicationProvenance.v)
imports the existing action collector unchanged. It proves that every
published transition/receipt pair came unchanged from an input candidate.
[`AuthoredSourcePublication`](../../../formal/rocq/runtime_grammar/theories/AuthoredSourcePublication.v)
then composes that provenance with completed-frame evidence. It does not
assume, as an input, the conclusion that every candidate is a source step.
Its input instead supplies the actual source lookup, match observation,
completed-operation trace, construction observations, and exact encoding link.

The older collector's resource envelope contains grade bytes, not the full
cost-image fingerprint and grade sort. The cost composition therefore uses
`CheckedCostImage` and `CostSourceAdmission` separately. It constructs the cost
match from the same frame's owner, rule, output, and final bindings, checks the
exact declared grade root, and retains the checked cost receipt alongside the
published pair. A relation between constructed signature values and the
existing multiset-grade model remains explicit; arbitrary guest values are
not silently coerced to multisets or strings.

| Obligation | Formal boundary | Executable correspondence |
|---|---|---|
| Exact ordered premise prefix | `frame_operation_preserves_exact_source_prefix`, `finished_frame_derives_its_exact_pending_sequence` | Full Regex recursive-wrapper and ordered Unicode intrinsic properties |
| Child bindings stay private | `completed_child_frame_supplies_source_return`, `nested_return_exports_only_declared_target`, `nested_return_cannot_export_child_bindings` | `generated_nested_return_keeps_child_derived_and_local_bindings_private` and the full Regex repeated-activation property |
| Quantified scope restores its parent | `completed_forall_body_supplies_source_element`, `forall_element_restores_exact_outer_environment` | `generated_forall_restores_derived_bindings_before_each_element_and_outer_premise`; not inferred from Regex wrappers |
| One final environment supplies RHS and grade | `completion_uses_one_final_substitution` | Generated costed action/roster property with a premise-derived target |
| Publication introduces no candidate | `proven_successor_has_exact_input_candidate`, `verified_output_has_exact_input_candidate` | Existing cancellation, evidence rejection, and complete-roster tests |
| Completed frames justify source results | `completed_frames_publish_only_their_source_derivations` | Exact source-origin/owner checks in the full installed Regex properties |
| Checked cost metadata accompanies the same source result | `completed_cost_frames_publish_source_and_checked_grade` | Premise-derived grade property checks the actual fingerprint, sort, output, retained grade root, and source program coordinates |

#### Remaining refinement premises and executable gates

The model deliberately names six local observation-to-meaning contracts:
complete source matching, term instantiation, freshness, collection enumeration,
intrinsic computation, and guard truth. Their arguments include the relevant
source arena, root, activation, environment, opcode, or payload. Defining those
contracts does not prove that the Rust operations satisfy them. Authentic
source/image projection, e-graph readback, encoding adequacy, and the precise
grade representation remain explicit obligations as well.

The refinement review identifies the concrete proof reuse for each contract.
Similar names are not interchangeable guarantees: an operator-encoding lemma
does not prove the term builder, and native receive-guard discharge does not
prove an installed semantic guard evaluator.

| Local contract | Existing implementation and reusable model | Connection still required |
|---|---|---|
| Source matching | `match_transition_rules_accounted`, `project_automaton_substitution`, and `flat_pattern_from_roots`; positional dispatch and ordered/unordered partition results | Full pattern and binding correspondence, including repeated variables, binders, remainders, and collection branches. Dispatch coverage alone leaves child matching abstract. |
| Term instantiation | `TermConstructionTask` and `instantiate_rule_term`; operator typing, map telescopes, exact zip, and splice-width lemmas | The construction and resolved-source/image models below establish the continuation invariant and exact source fields. The physical e-class/task/environment view and the five local readback/construction contracts remain to be connected. Existing legacy/core encoding equality does not establish those connections. |
| Freshness | `freshness_holds`; the existing `FreeOccurrence` relation and abstraction-aware `freshness_step` | Visited-worklist completion and the concrete e-class/source-value view. The new worklist model below addresses completion without assuming acyclicity. |
| Collection elements | `concrete_collection_elements`; PathMap marker/mode and canonical-arena membership results | Exact decoder output, with the marker excluded and set-mode keys distinguished from map-mode pairs. |
| Intrinsics | `execute_intrinsic`; UTF-8 scalar, boundary, slice, and concatenation results plus schema arity/field ordering | Typed literal readback and computed-value correspondence for all six actual opcode branches. `Utf8ScalarAt` returns a one-scalar string; checked natural addition uses nonnegative checked `i128` values. |
| Guard truth | `SemanticGuardEvaluator`; exact payload, image, and environment commitment | An injected evaluator's soundness. The default `UnavailableGuardEvaluator` returns indeterminate and cannot furnish a successful guard observation. Native receive-guard proofs do not establish this separate interface. |

#### Freshness worklist invariant

Freshness asks whether a particular value occurs **free** in a target. It is
not a raw search through every child. An abstraction whose binder equals the
needle shields its entire body; an abstraction with another binder visits
only its body, not its binder position. The target itself is checked for
equality before either visited-set membership or node decoding.

[`FreshnessWorklist.v`](../../../formal/rocq/runtime_grammar/theories/FreshnessWorklist.v)
reuses the existing graph, free-occurrence relation, and one-node decision.
Its state consists of visited vertices and a pending worklist. The invariant
retains two facts: every covered vertex is reachable from the original target
along permitted edges, and every inspected vertex's permitted children are
still covered by the visited set or the pending worklist. At exhaustion that
set is closed. Induction on a finite free-occurrence derivation rules out an
occurrence in the closed set even when the graph contains sharing or cycles.

The proof view mirrors the existing iterative algorithm:

```text
start with no visited vertices and the target pending
pop a pending vertex, using its canonical e-class identity
if it equals the needle, return not-fresh
if it was visited, continue without inspecting it again
otherwise inspect its binder-sensitive children and schedule them
when no vertices remain pending, return fresh
```

The exact-verdict theorem concerns successful Boolean returns. A popped,
previously unvisited non-needle vertex requiring malformed decoding cannot
yield a Boolean verdict. A needle can be found before decoding its node, and
a matching binder can shield a malformed body. Cancellation, allocation
failure, or exhausted work do not become `fresh` or `not-fresh`.
The model does not promise termination on an infinite
graph or success under an insufficient budget. Its immutable graph view uses
canonical e-class IDs; constructing that view faithfully from the physical
e-graph and relating its vertices to authored source values are separate
representation obligations. The verification ledger records whether this
model and its executable properties have actually passed their gates.

Three 48-case properties in
[`freshness_worklist.rs`](../../../dovetail-runtime/src/semantic_transition_kernel/tests/freshness_worklist.rs)
compare the existing traversal with an independent finite least-fixed-point
definition of free occurrence. They exercise shared graphs, matching and
different binders, root/child/binder aliases before and after e-graph rebuild,
and six malformed-node cases. Every completed traversal is replayed at its
exact work allowance and at every earlier work/cancellation prefix; earlier
refusal cannot become a Boolean verdict. A merge-built cyclic e-class has
multiple nodes and fails source-input admission, including when a freshness
binder would shield that subtree. The formal single-node-cycle example is
therefore deliberately not described as a tested admitted input.

#### Source instantiation and the existing construction machine

[`AuthoredTermConstruction.v`](../../../formal/rocq/runtime_grammar/theories/AuthoredTermConstruction.v)
connects the four existing `TermConstructionTask` variants to a source-level
instantiation relation. *Instantiation* here means constructing a term from
the selected source root and its environment. Constructing a `Substitution`
node does not itself execute beta reduction. That computation belongs to the
language's equations and execution relation.

The source relation retains variables, constructors, abstractions,
substitutions, collections and remainders, correlated `Map` bodies, `Product`
factors, and every typed literal payload. The source-to-application cases
mirror `compile_term_nodes`. They do not recursively compile the source again.

| Existing task | Exact continuation obligation |
|---|---|
| `Evaluate` | Evaluate the selected source root under its saved environment; append one value after the existing value-stack prefix. |
| `FinishApply` | Consume exactly the scheduled argument values. Place bound slots before arguments, splice collection-comprehension results and the declared remainder, then canonicalize and insert that exact node. |
| `FinishMapSources` | Consume all source values, require equal row counts and binder declarations, check exact parameter types/widths for each actual row, and evaluate each body under a fresh overlay of the same saved parent environment. |
| `FinishMapBodies` | Consume exactly one value per row, retaining row order, then construct the declared target collection using its existing mode policy. |

The continuation invariant records both the pending tasks and the complete
value stack. A successful finite run ending with no tasks and one result
therefore establishes `SourceInstantiation` for the original root and saved
environment. This conclusion supplies the construction obligation used for
RHS terms, grades, and Horn arguments; it is not assumed as an input.
The proof imposes no maximum arity, map width, or source depth.

Construction environments are indexed, parent-linked overlays in the runtime.
The model separately proves that appending another frame preserves existing
lookups, that a newly allocated row frame retains its exact parent, and that
indexed lookup agrees with the scoped overlay. The first local binding
shadows its parent. Unbound variables continue to the parent. A row's bindings
do not modify the parent or another row. Exact zipping reuses the existing
`CollectionComprehension` results rather than truncating to the shorter input.

Five physical-operation contracts remain explicit: collection splice
readback, mode-aware element readback, product-factor readback, canonicalizing
one specified child vector, and inserting one specified node. None accepts a
source root or environment and none can assert whole-builder correctness.
For PathMaps, splice readback can include physical mode markers that the
existing canonicalizer reconciles; element enumeration instead excludes the
marker and respects key-versus-pair mode. The resolved-source/image model
below establishes the exact term-field connection to the construction proof.
Authenticating that resolved view from the concrete source, the physical
task/environment view, and stability of the e-class value projection remain
obligations when composing with actual Rust executions.

Existing executable checks are reused: `correlated_exact_zip_captures_and_rhs_map_splices`,
`rhs_exact_zip_rejects_mismatched_source_lengths`, and
`rhs_map_construction_is_stack_safe_for_wide_sources`. The last constructs
20,000 rows on a 64 KiB thread stack. Source-grade and frame-scope properties
also exercise construction from derived bindings. These tests are evidence
for their stated invariants, not a proof of every physical-operation contract.

The additional generated checks are in
[`term_construction.rs`](../../../dovetail-runtime/src/semantic_transition_kernel/tests/term_construction.rs),
with 48 cases per property:

| Model invariant | Generated implementation check |
|---|---|
| `row_bindings_retain_exact_parameters`, `map_rows_retain_all_source_rows` | Scalar, product, and reordered multi-column inputs retain every row and exact parameter order under rotated variable IDs; unequal lengths, incorrect actual-row widths, and non-binder declarations are refused. |
| `environment_survives_heap_extension`, `allocated_environment_has_exact_parent`, overlay and indexed-lookup lemmas | Nested maps shadow the nearest binding while retaining outer-row and global captures; later row allocations do not change an earlier saved environment. |
| `abstraction_slots_precede_body` | The binder is read from the saved outer row after an inner map finishes, and the resulting abstraction contains the binder before its body. |
| Continuation value-stack widths | A map embedded between other product arguments retains the existing prefix and later sibling; an exact suffix split succeeds, while shorter, longer, or out-of-range requests refuse without consuming any values. |

The nested shadowing fixture deliberately reuses a numeric slot to test the
lowered worker's environment contract. It does not assert that a particular
rich-source binder spelling or comprehension-context graph passes source
admission. Expected results inspect actual constructed nodes; the tests do
not introduce another evaluator. Empty maps have no rows on which to check
a row's parameter telescope, so the worker-level tests do not invent a
stronger empty-row rejection rule.

#### Resolved source-to-image correspondence

An executable image must retain the authored terms, not merely their root
sorts or printed representations. A *resolved* source identifies sorts,
constructors, variables, and terms by their checked declaration positions.
For example, substitution retains the function sort of its abstraction
operand. Another function sort with the same result sort is not an acceptable
replacement. Likewise, a literal's carrier and complete payload are retained;
there is no conversion to a display string.

[`AuthoredSourceImage.v`](../../../formal/rocq/runtime_grammar/theories/AuthoredSourceImage.v)
models the existing term/variable checks shared by `validate_program` and
`validate_judgment_program` in the
[image validator](../../../grammar-core/src/theory_image.rs). Its one-node
projection corresponds to that validator's `expected_term_form` and the
[compiler's `compile_term_nodes`](../../../dovetail-runtime/src/theory_image_compiler.rs).
It reuses the rich source arena and `AuthoredTermConstruction.ApplyShape`.
It neither replaces those implementations nor introduces another evaluator.

The accepted arena has the same numbers of variables and terms as its source.
At every index, variable identity, sort, and role agree; term sort and every
form-specific field agree. Term edges point backward, variable references
are in bounds, and a `Map` has at least one source. Argument, factor, source,
and parameter order are preserved as lists, not just as sets.

```text
compare the variable and term arenas at matching source indices
require each variable's dense ID, sort, and role to match
project each source node into its expected Slot, Apply, or Map form
require exact node equality and backward/bounded references
use the accepted node to dispatch the existing construction task
```

| Accepted image form | Connection to the existing construction proof |
|---|---|
| `Slot` | Exposes the exact source variable; successful lookup supplies the existing variable-construction step. |
| `Apply` | Supplies `SourceApply`, retaining constructor identity, abstraction slots, substitution function sort, collection mode/remainder, product factors, or typed literal payload. The existing argument/finish continuation is unchanged. |
| `Map` | Exposes all source columns, all parameters, and the body. Dispatch also requires the existing runtime checks for nonempty parameters and a collection target; these are not inferred from the reference check alone. |

The model proves exact indexed coverage, uniqueness of an accepted arena for
a fixed resolved source, and refusal of any unequal term/variable arena.
Swapping identical rows is not a change and is not claimed detectable.
No injectivity assumption about a cryptographic hash is needed for these
field-equality results. The `Apply` completion theorem composes directly with
the existing construction theorem, preserving the original root and saved
environment under its five local physical-operation contracts.

The generated properties in
[`source_image_correspondence.rs`](../../../dovetail-runtime/src/theory_image_compiler/tests/source_image_correspondence.rs)
start with source-valid, reachable arenas and call the real compiler and
validator. They vary declaration positions and payloads, cover every rich
form and the eight currently source-admissible literal variants, and exercise
both rewrite and judgment programs using the same arena. `Unit` is retained
by the formal resolved-node projection, but `BuiltinCarrier` currently has no
unit carrier: the executable source-admission control therefore checks its
refusal, not successful installation. Adding a grammar carrier is not part
of this correspondence check. Mutations require the specific source-field
or dense-ID error; a stale fingerprint or automaton cannot make them pass.
Unknown and duplicate declaration names are checked separately as invalid
source. The verification ledger distinguishes written tests from passed gates.

| Formal invariant | Executable correspondence |
|---|---|
| `expected_form_preserves_ordered_references_and_slots` | The generated rich-source property checks concrete argument, binder, factor, Map-source, and Map-parameter lists, then changes their order or contents and requires the precise source-field rejection. |
| `checked_term_arena_has_exact_lengths`, `checked_term_arena_has_exact_variables` | The same property alters arena lengths and variable IDs, sorts, and roles independently for both rule and judgment programs. |
| `checked_term_arena_exposes_exact_construction_view`, `checked_term_arena_covers_every_source_node` | Every source node is checked at its original index, including nested and shared references, complete literal payloads, and substitution function-sort identity. |
| `checked_term_arena_is_unique_for_fixed_source`, `changed_term_arena_is_rejected` | Every negative image control first establishes that the image actually changed; fingerprints and automata remain unchanged. Unknown/duplicate names are separate source-admission controls. |
| The three `checked_*_dispatch_is_existing_construction_step` theorems and the `Apply` completion theorem | Source/image checks supply the existing task cases. The [construction properties](../../../dovetail-runtime/src/semantic_transition_kernel/tests/term_construction.rs) and [source-grade binding property](../../../dovetail-runtime/src/theory_image_compiler/tests/source_grade_binding.rs) separately exercise construction and same-environment publication; they do not discharge all physical e-class premises. |

`unit_literal_projection_is_exact_but_source_admission_refuses_missing_carrier`
also checks the existing raw term lowerer's exact `Unit` fields. Calling that
helper directly is deliberately distinguished from passing full source
admission; its companion control requires the specific carrier mismatch.

This is a proof of the resolved term/variable boundary, not of arbitrary name
resolution, complete source typing, resource accounting, or the whole image
validator. Source validity and declaration ownership come from the existing
`language.validate`, name-indexing, sort, and constructor checks. Binding their
concrete Rust data to the model remains explicit. A changed reference already
fails exact source comparison before the later reference guard; mutation
tests therefore do not claim to isolate that guard. Rule roots, premises,
owner commitments, and costs retain their separate validation obligations.

The generic image validator binds each program to its declared source origin.
It does not, from those per-row checks alone, establish that every source
origin appears exactly once. The compiler's canonical enumeration and the
stronger cost-roster checks supply separate coverage evidence. Positive
source correspondence must not be advertised as exhaustive search or complete
equality saturation.

The new executable properties are in
[`source_derivation.rs`](../../../rholang-runtime/src/language_install/tests/source_derivation.rs)
and [`source_grade_binding.rs`](../../../dovetail-runtime/src/theory_image_compiler/tests/source_grade_binding.rs).
They use the full installed Regex fixture and the existing costed compiler
fixture, respectively. The Regex fixture remains uncosted. The cost property
varies source coordinates, term/variable identities, declaration order,
equation prefixes, and grade declaration order. Neither fixture substitutes
for the other. The rewrite-step roster's multiplicity properties also remain
distinct from the older action collector's provenance theorem, which proves
neither multiplicity nor completeness.

Two further properties in
[`source_frame_scope.rs`](../../../dovetail-runtime/src/theory_image_compiler/tests/source_frame_scope.rs)
exercise the saved-environment invariants directly. The child-frame property
rotates colliding variable IDs across parent and child arenas, introduces
child-private derived bindings, and checks that only the declared result is
exported. The quantified property gives distinct elements distinct derived
results, reuses the same derived slot in every element, and then reuses it in
a following outer premise. The saved outer inputs and collection remainder
must survive, while the quantified parameter and each body's temporary
bindings must not escape. Both properties include a failure after successful
earlier premises and require no published action result or roster occurrence.
Their 32-case generators are executable checks of the actual compiler and
frame machine, not replacements for the unbounded scope theorems.

The [verification ledger](../../architecture/oslf-integration-verification.md)
records completed checks and current limits. Source files and property-test
definitions alone are not evidence that their verification gates passed.

### Decisions that remain distinct from source-local checking

- Which existing quotient-normalization construction supplies a section for
  a particular presentation, with evidence for that quotient.
- Which source/target mapping a quote-faithfulness claim identifies.
- Whether legacy `cut` and `rules` strings remain compatibility metadata or
  acquire a specified executable-selector meaning.
- Which programmatic proof implementations the installer trusts, and the
  exact source-bound input each checks.
- Whether requiring full certification changes installation compatibility.

No part of this proposal authorizes a general-purpose proof oracle, a second
rewrite engine, a new monetary ledger, or acceptance of arbitrary source
claims merely because their names match the manuscript. The precise checker
instances must be established for the presentations they admit.
