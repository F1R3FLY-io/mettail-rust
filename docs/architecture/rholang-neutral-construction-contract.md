# Rholang neutral construction and observation contract

This contract factors the target of the existing
[Rholang lowering worklist](../../rholang-runtime/src/rholang_ast.rs). It does
not add a source language, parser, evaluator, or second lowering traversal.
The [admission contract](rholang-frontend-admission-contract.md) determines
which source forms are supported. A target operation appearing below does not
by itself admit a corresponding source form.

The interface described here is being specified before production factoring.
The existing runtime still constructs node `Par` values. Concrete target laws,
worklist instantiation, constructor-family emission, and final canonical-byte
comparison are separate acceptance boundaries; this document is not evidence
that those implementations are complete.

## Values, references, and observations

A semantic value denotes a Rholang process or datum. A `ValueRef` identifies a
value in one construction session. References are checked, session-relative
indices, not source positions, hashes, capability handles, or arbitrary host
pointers. A source occurrence identifies a particular use of a value; distinct
occurrences remain distinct when they share a semantic value.

The construction interface has two operations, written here as pseudocode:

```text
construct(operation, ordered_child_references)
    -> Result<ValueRef, ConstructionError>

observe(value_reference)
    -> Result<StructuralObservation, ConstructionError>
```

`construct` resolves the ordered references, rejecting the first missing
reference, then validates the operation's child roles, arity, and declared
integer/binder bounds. It then builds the value privately.
Failure returns a typed error, never an empty-process substitute or a partially
published root. Runtime allocation, cancellation, and work limits remain
additional fallible checks; mathematical constructor totality is not permission
to omit them.

`StructuralObservation` provides the exact constructed-head classification and
locally-free/connective information consumed by the current lowerer.
Locally-free information identifies references to enclosing binders.
`connective_used` is the node representation's structural-pattern summary, not
a statement that a process has no effects. Neither field establishes authority,
funding, or semantic decidability.

The interpretation is structural. Constructing a binary operation retains that
operation and its operands; it does not calculate the operation's answer.
Methods likewise retain the receiver, name, and ordered arguments. The existing
reducer owns evaluation, type errors, effects, and charges.

## Required construction vocabulary

The following families are a closed interface inventory, not string-dispatched
opcodes. Implementations use typed variants and typed descriptors. The child
column specifies the order supplied by the existing worklist, before any
target-specific canonical representation is built.

| Family | Payload and ordered child roles | Existing owner |
| --- | --- | --- |
| Empty and parallel append | Empty has no children; append retains all children and their multiplicity | `ParFold`, `ParPair` |
| Native scalar | Checked integer, Boolean, or decoded string value; no process-text payload | Scalar handlers and existing decoders |
| Bound reference | Checked enclosing-binder index | `lower_name_var`, `lower_proc_var` |
| Pattern capture and wildcard | Capture index or explicit wildcard policy; not an enclosing-binder reference | `enter_pattern`, existing variable constructors |
| Captured pattern reference | Checked index and pattern depth, retaining the distinction from a bound variable | Installed pattern preparation |
| Unary/binary expression | Closed operator variant; operand, or left then right | `UnOp`, `BinOp`, shared expression assemblers |
| Addition selection | Left then right; select the existing addition operator from the constructed observations | `Kont::AddParity` |
| Method | Method name; receiver followed by arguments | `method_par` |
| Ordered list | All elements, including empty and repeated elements | `ListLit`, `PatListLit` |
| Map | Explicit ordered key/value pairs, including the empty map | `MapLit`, `PatMapLit` |
| Send | Persistence and payload arity; channel followed by payloads | `send_par`, `send_par_persistent` and existing sugar |
| Fresh scope | Binder count and checked URI/binder association; body | `Kont::New`, `unbind_uri_scope` |
| Receive | Ordered bind descriptors, capture-slot roster, persistence, scoped body and optional condition | Staged `ForSource`, `ForPattern`, `ForBody`, `ForGuard` |
| DDL wire node | Existing structural tag and ordered data children, with its distinct metadata policy | `DdlLowerPlan::finish` |
| Matching expression | Target then pattern; static-false form still consumes the lowered target | Existing matching continuations |
| Spatial pattern connective | Ordered conjunction/disjunction operands, negated pattern, implication, or separating parallel composition; distinct from Boolean expressions | `FormulaAnd`, `FormulaOr`, `FormulaNot`, `FormulaImplies`, `FormulaSeparation` |

List values and send payload vectors are different shapes. Preserve the
existing desugarer's argument-versus-list encoding exactly; the target must
not independently unpack or repack payloads. The desugarer remains responsible
for its current arity encoding.

A receive bind descriptor retains its source, pattern vector, optional
remainder, and checked free-count. The capture-slot roster retains both ordinary
binders and foreign-language-term (FLT) holes in their original combined order.
Source, pattern, body, and condition are distinct roles; a generic list whose
roles must be guessed is insufficient. The body cannot be scheduled until its
patterns establish that roster.

The admitted receive producers all emit exactly **one outer pattern per bind**
and no remainder. A polyadic bind uses one list pattern; an empty input bind
uses one wildcard with zero captures and a false connective flag. It does not
use an empty pattern vector or an empty-list pattern. The descriptor retains
the pattern producer's ordered capture telescope and derives its free-count
from that telescope. The full receive roster is the concatenation of those
telescopes. Equal counts alone do not prove that a telescope belongs to a
particular pattern; the existing producer must establish that correspondence.

Receive persistence is the OR of the bind persistence flags. Mixed persistence
and repeated capture names are not rejected by this interface. The existing
environment insertion rules determine shadowing, while the roster preserves
every slot occurrence. An empty join is rejected; an empty sequence of receive
rows instead schedules its body through the existing `ForRows` owner.

Fresh-scope descriptors distinguish ordinary allocation from URI allocation:

| Descriptor | Preserved data and validation |
| --- | --- |
| Plain | Ordered binder identities, no URIs; zero binders remain representable |
| URI | Nonempty normalized URI–binder pairs from `unbind_uri_scope`; both output projections use the same pairs |

The existing URI owner validates the backtick envelope and nonempty interior,
sorts the pairs, and rejects duplicate URIs. The target checks the normalized
sequence in one forward pass; it neither sorts again nor introduces URI-scheme
validation. Strict ordering establishes uniqueness without a separate
quadratic duplicate scan. The body must be lowered under the binder order
from those same pairs, an explicit producer-refinement obligation.

Signed 32-bit bounds apply to emitted indices, pattern depths, fresh counts,
and receive free/bind counts. The total enclosing scope size is not an emitted
field and must not acquire an implicit signed-32-bit limit from these checks.
Any session-wide environment limit belongs to the declared resource policy.

DDL projection reuses the existing exhaustive plan and captured-string decoder.
Embedded `Data` processes return to the same host worklist. A DDL wire node is
structured data, not an opaque source string or an instruction to parse a
second time. Factoring does not create a second theory composer.

Installed FLTs retain typed staged construction/pattern descriptions, selector
references, ranged text/hole pieces, capture telescopes, and explicit provider
slots. Their existing service envelopes and trampolines compose the operations
above. There is no generic `OpaquePar`, protobuf, executable callback, or
uninterpreted-process escape. Provider slots request later binding; they do not
grant the rights of an installed-language handle.

The concrete descriptor preserves the fields already supplied by
[`FltNode` and `ScopedFltTemplate`](../../runtime/src/flt_node.rs):

| Field group | Retained meaning |
| --- | --- |
| Selector and root category | The scoped reference and exact category spelling; selector spelling is separate diagnostic data |
| Declared telescope | Ordered hole IDs, names and optional category declarations; an absent category stays absent |
| Structural pieces | Exact text strings and hole-ID occurrences, without concatenation across holes or deduplication |
| Provenance and extent | Piece/first-occurrence ranges, delimiters, captured body, opener position and structural byte/count bounds |
| Host use site | Occurrence identity and construction, receive-pattern or predicate role |
| Scope associations | Construction fills and declared-hole associations with the enclosing receive slots |

The existing `runtime_template_parts` projection removes ranges from the
runtime parser input; it does not turn the retained body string into a second
parse input. The original descriptor still owns its provenance. Existing
`FltNode::validate` remains responsible for declaration, range and extent
validation, and the shared guest parser handles the structural pieces.

Declared holes and reflected matching occurrences are different rosters.
A repeated hole keeps one declaration ID but can produce several raw matching
captures. The existing `PreparedCapturePlan::compile` and `project` check
repetitions and project those occurrences back to declaration order. The
frontend retains the declared telescope and scope associations; it does not
replace that matcher-owned plan or treat its occurrence count as a declaration
count.

Use-site roles determine polarity and pending obligations. Receive-pattern
sites request negative matching. Predicate sites request positive construction
followed by observation, while retaining authority, semantic-resource and
funding obligations. A predicate descriptor is not an observation result,
even when it occurs beneath Boolean negation.

## Interpretation and metadata policies

Parallel composition combines process heads, not source syntax tags. In
particular, the existing single-string test is applied after append has removed
empty contributions. These are required observation witnesses:

```text
observe(append(empty, text("a"))).single_string = true
observe(append(text("a"), text("b"))).single_string = false
```

Addition selects string concatenation only when both constructed operands pass
that exact observation. It must not inspect only whether the immediate neutral
node is a text literal. The correspondence is required on the admitted target
image: the existing helper is not an arbitrary hostile-`Par` validator, and its
omission of unrelated envelope fields must not become a security assumption.

Metadata laws are deliberately operation-specific:

| Construction | Locally-free information | Connective flag |
| --- | --- | --- |
| Ordinary binary expression | Union of both operands | OR of both operands |
| Ordinary unary expression | Operand's information | Operand's flag |
| Method, ordinary list/map, send | Union of every relevant ordered child | OR of those children |
| Parallel append | Existing append combination | Existing append combination |
| Bound variable | Singleton enclosing-binder index | Existing caller policy |
| Pattern free variable | Existing explicit free-reference information | True |
| Wildcard | Existing caller policy | Existing caller policy |
| Captured pattern reference | Singleton reference index | True |
| Fresh scope of width $`w`$ | Remove indices below $`w`$; subtract $`w`$ from the rest | Body's flag |
| Receive | Sources plus binder-adjusted body and retained condition | Sources and body only |
| Matching expression | Target and pattern union | False |
| Statically false matching expression | Target's information; target must still lower successfully | False |
| DDL wire list | Existing explicit empty information | False |

Spatial pattern connectives retain the existing formula assembler's separate
policy: connective nodes are structural patterns, not ordinary Boolean
expressions. Implication negates only its antecedent; separating composition
uses the existing parallel append. Their presence in this target vocabulary
does not expand the admitted source profile.

The receive rule does not OR pattern or condition flags into its outer flag.
DDL wire lists do not use the ordinary-list union policy. These distinctions
record current construction semantics; they are not interchangeable policies
that a generic assembler may silently unify. Exact target tests must include
open children and pattern-bearing children so constant-false examples cannot
conceal a mismatch.

Mathematical sets of indices are useful for scope laws but do not by themselves
prove exact metadata bytes. The target adapter must additionally preserve the
existing bit-vector representation and both inner and outer metadata fields.
Canonical node bytes and metadata-complete equality remain emitter obligations.

Extending scope by $`w`$ shifts each existing index by $`w`$. Formal slot $`i`$,
with $`i < w`$, receives index $`w - 1 - i`$. Slot kinds do not change that ordering.
Duplicate names, shadowing, URI permutation, and numeric range checks retain
the existing scope owner; unresolvable public names produce named errors rather
than the integration harness's `mtl:` or `mtl#out` markers.

## Guards, origins, and owned session output

The neutral graph retains guard structure and the requested discharge policy.
It cannot invoke the node-dependent evaluator, discard the policy, or assume
that an installed FLT predicate is a decidable Boolean. The existing node
emission and provider boundaries own discharge and live predicate execution.
Installed predicate obligations stay residual, including beneath negation.

Origin erasure removes diagnostic location data only. It must preserve semantic
operations, ordered children, capture maps, provider references, guard policy,
and pending semantic-resource/authority/funding obligations. A full artifact
still retains original occurrence order and multiplicity.

Per-session descriptors are owned outputs, not thread-local leftovers.
Construction failure cannot publish a root while losing its descriptor table,
and a subsequent session cannot inherit those descriptors. The worklist/session
implementation supplies the bounded cleanup and reentrancy evidence.

## Formal and implementation handoff

The
[construction algebra](../../formal/rocq/rho_bridge/theories/RholangTargetConstruction.v)
defines structured values, append-aware observations, named metadata policies,
ordered references, local scope laws, and origin erasure. The
[checked construction protocol](../../formal/rocq/rho_bridge/theories/RholangConstructionProtocol.v)
connects that algebra to a closed operation vocabulary, checked references,
fresh/receive descriptors, observations, and private append-only construction.
Its `GeneratedArena` relation starts at an empty arena and admits a new value
only through an actual successful interpretation. It is construction provenance,
not an assumed validity flag or proof of correct lexical resolution.

The protocol establishes these connected results:

1. Successful construction resolves the exact ordered children, preserving
   repeated references, and returns their actual interpretation.
2. A successful private step appends that value at the returned index and
   preserves all earlier references. Observation reads the constructed value.
3. A rejected step leaves the private arena unchanged and returns its error;
   missing operands never become empty processes.
4. Checked fresh construction preserves the normalized URI/binder association.
   Checked receive construction preserves its pattern roles, capture roster,
   derived count and persistence, body/condition suffix, and metadata policy.

The [concrete FLT transport model](../../formal/rocq/rho_bridge/theories/RholangFltTransport.v)
additionally preserves exact strings, optional category declarations, hole IDs
and occurrence order, selector/category, bounds, use-site polarity and pending
obligations. It reuses the admission model's reference and obligation vocabulary.
The earlier abstract structural-template model uses numeric text-chunk IDs;
its lexical and graft laws alone do not prove this exact-string transport.

These results do not yet establish full artifact publication. The algebra's
abstract pending context is not a substitute for the concrete FLT descriptions.
The remaining owned session boundary must retain those descriptions and
obligations alongside the graph and root. Current separate fold/native/guard
collectors are implementation reuse points, not a proof of error-path cleanup.
Executable provider implementations and native evaluator closures remain
host-owned; the neutral artifact retains requests and declaration references.

The mathematical range wrapper describes a result, not evaluation order in a
strict programming language. The Rust adapter must check range and resource
limits **before** materializing index-sized metadata; an eagerly evaluated
argument to a checking helper would not establish that ordering.

The construction model must define its interpretation concretely and prove
arity/reference rejection, ordered-child preservation, append-aware observation,
the named metadata laws, scope-index bounds, and origin erasure. An externally
supplied Boolean named `correct` or `canonical` would not establish these laws.

Reuse the existing
[admission protocol](../../formal/rocq/rho_bridge/theories/RholangFrontendAdmission.v)
for retained occurrences and pending obligations. The scoped
[lowering model](../../formal/rocq/rho_bridge/theories/RholangAstLowering.v)
provides transport/order examples, but its out-of-range lookup returns an empty
term and is not the checked-reference contract required here.

The later worklist instantiation reuses
[WorklistFoldEquivalence](../../formal/rocq/trampoline/theories/WorklistFoldEquivalence.v)
where its fixed-tree algebra premises hold. Staged receive scheduling, fallible
construction, resource handling, and concrete target interpretation need their
own correspondence; they do not follow merely from that generic theorem.

Each constructor-family handoff then checks the actual reused lowering path,
exact output and metadata, empty/nonempty cases, invalid references/counts, and
failure without publication. The final node emitter must establish the
commuting result under identical source, environment, options, and session
descriptors. None of these boundaries claims parser completeness, arbitrary
Rust correctness, full language parity, or a runnable public-node application.
