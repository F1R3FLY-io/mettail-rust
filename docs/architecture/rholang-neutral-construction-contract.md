# Rholang neutral construction and observation contract

This contract factors the target of the existing
[Rholang lowering worklist](../../rholang-runtime/src/rholang_ast.rs). It does
not add a source language, parser, evaluator, or second lowering traversal.
The [admission contract](rholang-frontend-admission-contract.md) determines
which source forms are supported. A target operation appearing below does not
by itself admit a corresponding source form.

The initial primitive construction target is implemented; the broader interface
below remains the contract for subsequent constructor families. The existing
runtime still constructs node `Par` values. Worklist instantiation, complete
constructor-family emission, and final canonical-byte comparison are separate
acceptance boundaries; this document is not evidence that they are complete.

## Values, references, and observations

A semantic value denotes a Rholang process or datum. A `ValueRef` identifies a
value in one construction session. References are checked, session-relative
indices, not source positions, hashes, capability handles, or arbitrary host
pointers. A source occurrence identifies a particular use of a value; distinct
occurrences remain distinct when they share a semantic value.

The construction interface provides construction, observation and identity
forwarding, written here as pseudocode:

```text
construct(operation, ordered_child_references)
    -> Result<ValueRef, ConstructionError>

observe(value_reference)
    -> Result<StructuralObservation, ConstructionError>

forward_reference(value_reference)
    -> Result<ValueRef, ConstructionError>
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

Name quotation, process drop and name parentheses forward their child's checked
reference unchanged. They do not allocate a semantic wrapper. Their distinct
source occurrences still receive distinct origin records.

## Required construction vocabulary

The following families are a closed interface inventory, not string-dispatched
opcodes. Implementations use typed variants and typed descriptors. The child
column specifies the order supplied by the existing worklist, before any
target-specific canonical representation is built.

| Family | Payload and ordered child roles | Existing owner |
| --- | --- | --- |
| Empty and parallel append | Empty has no children; append retains all children and their multiplicity | `ParFold`, `ParPair` |
| Native scalar | Checked integer, Boolean, or decoded string value; no process-text payload | Scalar handlers and existing decoders |
| Opaque host name | Exact caller-owned name-table identity and slot; no children or embedded process | Explicit host adapter enrollment and binding |
| Pending installed predicate | Exact retained FLT-use index; selector followed by the use's ordered construction fills | Checked owning session; later guard/provider boundary |
| Service reply scope | Payload count; channel, ordered payloads, then continuation | Existing installed-FLT, pattern-preparation and held-fold reply helpers |
| Bound reference | Checked enclosing-binder index | `lower_name_var`, `lower_proc_var` |
| Pattern capture and wildcard | Capture index or explicit wildcard policy; not an enclosing-binder reference | `enter_pattern`, existing variable constructors |
| Captured pattern reference | Checked index and pattern depth, retaining the distinction from a bound variable | Installed pattern preparation |
| Unary/binary expression | Closed operator variant; operand, or left then right | `UnOp`, `BinOp`, shared expression assemblers |
| Addition selection | Left then right; select the existing addition operator from the constructed observations | `Kont::AddParity` |
| Method | Method name; receiver followed by arguments | `method_par` |
| Ordered list | All elements, including empty and repeated elements | `ListLit`, `PatListLit` |
| Map | Explicit ordered key/value pairs, including the empty map | `MapLit`, `PatMapLit` |
| Send | Persistence and payload arity; channel followed by payloads | `send_par`, `send_par_persistent` and existing sugar |
| Fresh scope | Binder count, checked URI/binder association and ordered injection keys; body followed by injection values | `Kont::New`, `unbind_uri_scope`, pinned node `combine_p_new` |
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
An FLT receive slot retains the hole's name; its optional category belongs to
the separate declared FLT telescope, not to an invented receive-slot field.
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

The caller's entire injection map is retained separately from these URI/binder
pairs. Its ordered keys correspond one-for-one to the children following the
body. The target rejects duplicate/out-of-order keys and mismatched key/value
counts; it does not filter unused entries. Empty maps and empty map keys remain
representable. With no injections, this operation specializes exactly to the
existing fresh construction. Its summary still depends on the shifted body,
not an ordinary union of the injection children.

The node's runtime URI map takes precedence over injections. Its subsequent
runtime extraction rules are not frontend import validators. A quoted admitted
structural value uses ordinary nodes and quote/drop forwarding; it is not
replaced by an opaque process slot. The source-to-target adapter must validate
the declared import domain and preserve the node's existing runtime refusal
behavior for used injections.

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

`HostNameSlot` is restricted to closed opaque **name** data. Its owner and index
resolve against an explicitly retained adapter table, preserving the exact
host identity. Wrong owners and missing slots reject distinctly. The neutral
graph carries neither arbitrary `Par` values nor a name reconstructed from a
fingerprint. Closed, non-string observations rely on checked enrollment into
this name-only domain; empty metadata or a permissive host extractor is not an
enrollment proof. Rights remain subject to the installed service's authority
checks.

Each successful host-name leaf construction appends its slot to the session's
required-name roster. Parent construction reuses already registered children;
it does not rewalk their graphs. Recording other descriptors preserves the
roster, and finishing retains it alongside the graph. Repeated requirements
remain repeated. Before emitting a host artifact, the adapter must resolve all
retained slots against the exact table owner.

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

For a direct guard, `PendingPredicateHead(use_index)` connects the graph to that
exact retained use. Its first child is associated with the descriptor's lexical
selector. Each subsequent child is paired with the corresponding construction
binding, including its hole ID, name and lexical reference. The owning session
checks that the index exists, identifies a predicate site, and receives exactly
one selector plus the declared fill count. All value references then pass the
ordinary construction check. Missing descriptors, wrong roles and missing or
extra inputs consume the session with typed errors and retained diagnostics.

Exact arity prevents a truncated pairing; it does not prove lexical resolution.
The existing producer must resolve the selector and fills in their actual
scope. The pending node derives structural metadata from its explicit inputs
and is distinct from every Boolean literal. Applying ordinary Boolean negation
retains that node as the negated operand; construction never evaluates it.

Its later meaning is an installed, declared observation for the current
candidate's inputs. The guard/provider boundary must select the checked
predicate declaration through the existing semantic service, classify the
complete result roster, retain `Undetermined` diagnostics and revalidate rights,
resource projection and funding at COMM. Category names do not select an action
or authorize it. A reply-channel request executed before candidate matching
does not have these semantics and cannot replace the pending atom.

### Existing FLT request and reply recipes

The [request recipe model](../../formal/rocq/rho_bridge/theories/RholangFltRequestRecipes.v)
specifies the existing `encode_flt_construct_call` and `encode_flt_pattern_call`
layouts in [the language-service implementation](../../rholang-runtime/src/language_install.rs).
These are compositions of checked scalar, ordinary list and map construction,
not another runtime encoder or guest evaluator.

| Field position | Construction request | Pattern-preparation request |
| --- | --- | --- |
| 0 | `mettail-language-flt-construct/1` | `mettail-language-flt-pattern/1` |
| 1 | Installed handle input | Installed handle input |
| 2 | Ordered piece list | Ordered piece list |
| 3 | Declared hole list | Declared hole list |
| 4 | Exact root category string | Exact root category string |
| 5 | Name-keyed fill map | Reply channel |
| 6 | Reply channel | No seventh field |

A text piece is `["text", payload]`; a hole occurrence is `["hole", id]`.
A declaration is `[id, name, optional_category]`. An absent category is the
empty process; a present empty string is a string value and remains distinct.
Hole IDs retain the source's unsigned-32-bit range before using the existing
signed integer constructor. Repeated pieces and hole occurrences remain
repeated. Fills retain the existing ordered map's name/value associations;
duplicate or out-of-order keys reject rather than being silently replaced.
Template validity and exact fill-to-declaration membership remain the existing
validator/service obligations, not conclusions of wire framing.

The fill-map equation retains the **inputs** to the target map operation.
The node's `new_emap_par` delegates to `ParMap` and `Ordering::sort_map`, which
canonicalize values as well as keys. Consequently the neutral pair-preservation
law does not claim that arbitrary host values emerge unchanged. The existing
FLT producer supplies bound-variable fills; the emitter correspondence must
establish their canonical fixed point and string-key ordering. General map
emission retains its existing canonicalization owner, not a second frontend
sorter or an assumption that all imported values are already canonical.

Both request families use ordinary child-derived list/map metadata. The model
proves that the helpers' left-fold union equals the construction algebra's
right fold for the exact bit vectors, including trailing false entries. This
is not just equality of the represented sets of free indices.

`ServiceReplyOp(payload_count)` represents the common existing reply shell:

```text
children = channel :: ordered_payloads ++ [continuation]

new reply in {
    send(channel, ordered_payloads)
    | receive(reply, one_result_capture, continuation)
}
```

This is structural pseudocode, not new Rholang syntax. Its descriptor fixes
one fresh reply binder, one result capture, a nonpersistent send/receive, and
empty URI/injection maps. Child arity and order are checked in one forward
decomposition. The children are already lowered under the reply scope, and the
continuation also sees the result binder; the recipe does not shift them again.
Generated reply scopes do not copy caller URI injections.

Installed FLT construction and pattern preparation send one request payload.
The existing held-fold path sends two separate payloads, the operand and reply
channel. Combining those two into a single list would change the wire behavior.
The one- and two-payload specializations are separate checked laws of the same
shell, not separate evaluators.

The node helper `models/src/rust/utils.rs::new_boundvar_par` computes the reply
channel's free-bit vector from index zero, even though the call supplies an
empty vector. The resulting vector is `[1]`, represented by `[true]` in the
model. The result capture has empty free bits and a true connective flag.
Receive free bits combine that reply-channel vector with the binder-adjusted
continuation; fresh free bits then remove the reply binder from the combined
send/receive value. The receive's inner and outer connective flags and the
fresh value's outer flag are explicitly false, as in the existing helpers.
Send flags remain child-derived. These fixed policies preserve the actual
helper, without allowing arbitrary overrides on ordinary source constructors.

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
| Opaque host name | Empty, under the checked name-only enrollment contract | False |
| Method, ordinary list/map, send | Union of every relevant ordered child | OR of those children |
| Pending installed predicate | Union of selector and fill inputs | OR of those inputs; not an observation result |
| Parallel append | Existing append combination | Existing append combination |
| Bound variable | Singleton enclosing-binder index | Existing caller policy |
| Pattern free variable | Existing explicit free-reference information | True |
| Wildcard | Existing caller policy | Existing caller policy |
| Captured pattern reference | Singleton reference index | True |
| Fresh scope of width $`w`$ | Remove indices below $`w`$; subtract $`w`$ from the rest | Body's flag |
| Generated service reply scope | Remove one reply binder from send plus reply-receive free bits | False; reply receive also explicitly false |
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

The [owned-session model](../../formal/rocq/rho_bridge/theories/RholangOwnedSession.v)
makes the output transitions explicit:

| Input state and action | Result | Retained output |
| --- | --- | --- |
| Open session, successful construction | Open session and exact new value reference | Private graph and all existing descriptors |
| Open session, recording an occurrence or descriptor | Open session and its table index | Exact appended item and every other table |
| Construction or driver failure | Consumed session and typed error | Diagnostics, no executable artifact |
| Finish with one existing root and checked links | Consumed session and owned bundle | Graph, root, occurrences, host-name requirements, FLT uses, guards, provider/fold requests and diagnostics |
| Finish with missing links or zero/multiple roots | Consumed session and typed error | Diagnostics, no elected or fabricated root |
| Any use of the returned consumed session | Rejection | No second publication or inherited registration |

Here, “publication” means returning a private frontend artifact to its caller,
not publishing a process to RSpace. Recording a provider request does not bind
that provider, and recording a predicate does not establish its truth. The
model's original nonempty-bundle witness tests ownership and reference links
only; its Boolean condition is not an implementation of an installed predicate.
The separate `reachable_pending_guard_bundle` witness starts from an empty
session, retains a host-name requirement, constructs a real pending atom, and
registers that atom as the guard condition before finishing. It establishes a
reachable structural handoff, not successful guest observation.

`check_guards` checks that the condition exists and that the listed use indices
identify predicate sites. It does not prove that the list equals the pending
atoms occurring in the condition. The existing producer and target refinement
must preserve that graph-to-guard association, including enclosing Boolean
structure. Likewise, pending-atom contextual validity requires the checked
owning-session transitions, not `GeneratedArena` alone. These obligations do not
require an additional runtime graph traversal.

`OwnedArtifact` is the construction/session component of
`RholangFrontendArtifactV1`, not an alternative complete envelope. The enclosing
preparation contract must also retain source/profile/environment commitments,
complete parse-family evidence and completed preparation usage. Successful
session finishing does not manufacture any of that evidence.

### Connection to source preparation

The enclosing preparation invocation carries one immutable request context:
the exact source, language profile, lowering options and limits, ordered caller
injection image, and identities of the provider-owned reference tables. The
actual admission result and construction outcome belong to that invocation.
Commitment hashes identify the declared artifacts; equality of arbitrary hashes
does not establish equality of source bytes, environments or semantic graphs.

The handoff has four existing responsibilities:

| Boundary | Required input and retained output | Refinement owner |
| --- | --- | --- |
| Source admission | Exact request context and actual `ClassifiedSource` result, including the original candidate roster and pending obligations | Admission implementation and parser-to-forest correspondence |
| Structural lowering | The same context and admitted source drive the existing `Job`/`Kont` worklist; retain the original roster even when one semantically agreeing candidate drives construction | Worklist instantiation and constructor-family correspondence |
| Session finish | The actual successful `OwnedSession.finish` output supplies the graph, root and descriptors without replacement or reconstruction | Owned-session implementation |
| Host preparation | Enclose that construction component with the retained request, admission evidence and completed usage; validate emission and host obligations before producing `PreparedProgram` | Neutral emitter and prepared-admission integration |

This is a data-ownership handoff, not a second classification pass or a second
source traversal. `ClassifiedSource` is the result of the existing
[admission protocol](../../formal/rocq/rho_bridge/theories/RholangFrontendAdmission.v).
Its retained-roster theorem establishes finite coverage and semantic agreement
under that model's premises. It does not certify a parser that has already
discarded alternatives. A construction representative never replaces the
original roster or its occurrence-specific obligations.

Completed usage must come from the same invocation's terminal accounting,
including failure outcomes. Parser statistics and theorem-checker admission
usage alone are not whole-frontend accounting. Logical work, semantic grades
and funding certificates remain distinct; session finishing cannot fabricate
any of them.

The actual owned output establishes which graph this invocation constructed.
It does **not** establish that the graph faithfully lowers the admitted source.
That commuting/refinement obligation belongs to the worklist and target
instantiations under the same context, followed by concrete node emission.
The existing node `ProgramFrontend::prepare` accepts source and environment,
and its non-`Clone` `PreparedProgram` consumes a normalized host process. Neither
already implements this neutral envelope or its accounting record.
`RholangFrontendArtifactV1` remains the specified output contract, not the name
of an implemented Rust type.

## Shared worklist storage

The existing driver now uses the node-independent
[`Worklist<Job, Par>` storage](../../runtime/src/worklist.rs) through its local
`Stacks` wrapper. This is a concrete direct-node storage instantiation, not an
implementation of the full neutral construction target. The driver still owns
its `Job`/`Kont` instructions, scope environment, staged receives, constructors
and session machinery. No second traversal or constructor interpreter was added.

The storage keeps the existing two vectors and initial 64-element capacities.
Work is last-in/first-out; completed values retain source order. The producer's
immutable classifier distinguishes an Enter from a continuation of arity zero.
Its three incremental counters count pending Enters, continuations and operands;
the invariant check is constant-time and runs at complete transition boundaries.
It must not run halfway through scheduling a continuation and its children.

The checked API rejects counter overflow/underflow, unavailable operands,
invalid debt, pending work and zero/multiple final values. Counter errors are
detected before storage mutation. A failed suffix pop preserves the original
values. The current trusted-driver wrapper retains its internal-error panic
behavior and debug checks; future public admission must propagate the checked
errors rather than treating a failed construction as an empty process.

The [storage model](../../formal/rocq/rho_bridge/theories/RholangWorklistStorage.v)
proves exact counter updates over mathematical lists, ordered suffix removal,
zero-arity behavior, debt preservation for complete and staged transitions,
value-carrier mapping and origin erasure, and the singleton completion shape.
It also gives a counterexample: correct global debt does not imply that the
next continuation has enough operands. Local checked pops are still required.

These are not proofs of arbitrary Rust callbacks, machine-word arithmetic,
allocation, recursive value destruction, concrete receive scheduling or host
publication. The classifier must remain stable on each immutable job, and
untrusted arity arithmetic must be checked by its producer. The Rust tests
exercise returned-error atomicity, machine-word overflow without large
allocation, non-palindromic repeated-child order, staged replacement and
20,000 shallow jobs on a 256 KiB thread stack. That last check tests storage,
not lifecycle safety of arbitrary recursively owned payloads.

The existing recursive differential and continuation-coverage tests exercise
the actual Rholang driver. The
[source-correspondence check](../../scripts/verify-worklist-storage-correspondence.mjs)
additionally pins the extraction boundary. It composes with the
[initial target delegation check](../../scripts/verify-initial-target-correspondence.mjs):
undoing exactly the reviewed target call substitutions leaves all code outside
the storage wrapper and its two final count-accessor replacements unchanged.
Environments, FLT/DDL staging and the retained oracle remain unchanged. Operand
reversal and producer mutation controls must fail. These are source-boundary
checks, not general compiler-correctness proofs.

## Initial construction target

The dependency-free
[`mettail-rholang-frontend` package](../../rholang-frontend/src/lib.rs) implements
empty, signed-64-bit integer, Boolean, text and binary append operations.
`ValueTarget::Value` deliberately has no `Clone` bound: the same consuming
algebra accepts either a session reference or an owned node value.

| Target | Value carrier | Construction and ownership |
| --- | --- | --- |
| Neutral | `ValueRef` branded by its session lifetime | Append-only flat nodes; each append retains two ordered earlier references |
| Direct node | Owned `Par` | Existing node constructors; no persistent arena of copied `Par` subtrees |

The [neutral arena](../../rholang-frontend/src/arena.rs) stores a compact
three-case head classification: empty, exactly one string head, or other.
Append combines classifications and exact structural metadata. It does not
copy either child's flattened head list. Thus appending empty to text still
observes as a single string, while appending the same text reference twice
does not. Shared edges preserve multiplicity without expanding the shared
subgraph during construction.

The [compact-fact model](../../formal/rocq/rho_bridge/theories/RholangConstructionFacts.v)
proves that this classification commutes with the existing construction algebra,
that cached observations are exact, and that ordered lookup preserves the first
missing reference. The integer carrier is already range-checked by its producer;
the target does not truncate an arbitrary integer into that carrier.

`with_neutral_target` introduces one fresh invariant lifetime in a higher-ranked
closure. Neither the target nor its references can leave that scope. Their
private fields and invariant lifetime prevent references from different
sessions being exchanged through the safe API, without global identifiers or
identity allocations. Observation borrows the actual target, not merely the
phantom lifetime. A session brand is neither authority nor validation of an
untrusted serialized graph.

For example, this complete Rust function returns an owned construction graph;
returning `text` instead would be rejected by the compiler:

```rust
use mettail_rholang_frontend::{
    arena::{with_neutral_target, ConstructionGraph, ConstructionLimits},
    construction::{ConstructionError, ValueOp, ValueTarget},
};

fn example() -> Result<ConstructionGraph, ConstructionError> {
    let limits = ConstructionLimits {
        nodes: 2, edges: 2, payload_bytes: 1, work: 16,
    };
    with_neutral_target(limits, || false, |mut target| {
        let text = target.construct(ValueOp::Text("a".into()), vec![])?;
        let repeated = target.append(text, text)?;
        target.finish_graph(repeated)
    })
}
```

The [compiler isolation checks](../../scripts/verify-neutral-target-brands.mjs)
compile and execute a positive nested-session client, then require specific
lifetime errors for reference/target escape, both cross-session directions,
outer storage, escaping closures/futures, and type erasure through `Any`.
An unrelated compilation failure cannot satisfy these checks.

Construction checks cancellation, cumulative attempted work, retained nodes,
edges and payload bytes. Failed construction cannot append a partial node;
already-performed work remains charged to construction usage. Allocation errors
are distinct from missing references and malformed arity. These dimensions are
not allocator RSS, semantic cost grades or whole-frontend accounting. In
particular, borrowed observation is constant-time and does not update the meter.
The flat ownership structure supports iterative cleanup; its deep sharing test
constructs 20,000 append nodes on a 256 KiB thread stack without unfolding them.

The [direct adapter](../../rholang-runtime/src/rholang_ast/target.rs) reuses the
existing scalar helpers and `Par::append` exactly. That append helper clones
the left value's vectors and takes the right value's vectors, then concatenation
clones elements from both temporary sequences. This adapter adds no further
subtree clone. Its typed binary entry point also avoids a new
temporary child vector at existing parallel-composition sites. Forwarding moves
an owned `Par` unchanged. Borrowed observation reuses the existing single-string
predicate and exact metadata slices.

The existing lowerer delegates only its initial primitive, parallel-composition
and addition-observation sites through this target. The shared-worklist test
executes one operation program with both carriers and compares intermediate
observations. Direct-target tests compare complete `Par` values and protobuf
bytes against the original helpers, including nontrivial metadata and ordered
operands. These checks do not establish all constructor families or source
lowering into the neutral arena.

### Shared consuming continuation transitions

The production `ParPair` and `ParFold` continuations now use
`Worklist::reduce_pair` and `Worklist::reduce_values`. The first checks that both
operands exist, then pops right followed by left without a temporary vector.
The second extracts the same ordered suffix as before. Its constructor uses
`append_fold`, which constructs empty through the target and appends children
left-to-right. This includes zero children: an empty fold still performs a
checked construction rather than supplying an unchecked default.

Both methods accept consuming constructor callbacks. The caller has already
popped the continuation job; the methods change only the value stack and leave
job classification and scheduling to the existing driver. Neither method
requires cloned values or a frontend dependency on the runtime crate.

| Transition outcome | Remaining values | Constructor behavior |
| --- | --- | --- |
| Insufficient operands | Original stack unchanged | Not called |
| Successful construction | Original prefix followed by one result | Called once with source-ordered operands |
| Failed construction | Original prefix, with operands consumed | No replacement value pushed |

A construction error is terminal to the owning lowering invocation. This is
not a rollback guarantee: a target may have retained intermediate private nodes
and recorded work before rejecting. The public owning-session boundary must
propagate that failure and withhold its artifact. The current trusted direct
driver keeps its internal-error panic contract; its exact-arity empty/append
constructors are total on that admitted carrier.

The [consuming-transition model](../../formal/rocq/rho_bridge/theories/RholangWorklistConstruction.v)
defines these outcomes over the existing checked suffix operation, proves
prefix/order preservation and underflow/constructor rejection, and instantiates
the carrier-mapping law with the concrete append-aware cache. It does not
assume that a Rust callback is correct. Source checks and tests separately
connect that model to the actual shared methods and their production calls.

Tests use both real targets for empty, singleton and repeated non-palindromic
folds and binary composition. Additional tests exercise a move-only carrier,
preserved stack prefixes, underflow without invoking the constructor,
constructor failure without a fabricated result, and early termination of a
failed append-fold. The
[transition source check](../../scripts/verify-worklist-construction-correspondence.mjs)
composes with the earlier target and storage checks; arity, operand-order and
unrelated producer mutations fail.

These are shared production continuation transitions, not a claim that all
`Drive` state is already target-generic. The remaining family migrations must
reuse the same worker and preserve its staged scope/receive/session behavior.

`ConstructionGraph` owns nodes and a checked root, including retained unreachable
nodes. It is only the construction component, not `RholangFrontendArtifactV1`.
Owned FLT/session descriptors, source admission, occurrence maps, host emission,
authority and funding remain their separately checked integration boundaries.

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

The owned-session model connects those concrete FLT descriptions to the graph
and root. Its reachable states arise from actual recording and construction
transitions; successful finishing checks occurrence/value and predicate-role
links, preserves the whole bundle, and consumes the returned session. Semantic
projection removes outer and nested diagnostic origins while retaining capture
associations, extents, guard policy and all pending requirements.

`GeneratedArena` proves only the value-vector projection. It does not prove that
a caller-assembled session retained the requirements of those values. The
handoff therefore retains `ReachableDraft`, which couples actual successful
construction and recording transitions to the descriptor and host-name rosters.
The checked step/finish law preserves that reachability and the exact appended
name requirements. This is a private-session invariant, not a reason to add a
second runtime graph scan.

These results do not establish Rust ownership, producer correctness, complete
preparation or live host admission. The algebra's abstract pending context is
not a substitute for the concrete FLT descriptions. Current separate
fold/native/guard collectors are implementation reuse points, not a proof of
error-path cleanup.
Executable provider implementations and native evaluator closures remain
host-owned; the neutral artifact retains requests and declaration references.

The host-name and injection laws specify exact lookup, ordered association,
failure behavior and requirement retention. The pending-predicate laws connect
an exact descriptor and ordered inputs to an actual residual graph node.
Concrete enrollment, host binding, source/guard correspondence, observation
and node-byte correspondence remain adapter obligations.

The request and service-reply recipes specify that existing composition,
including exact framing, checked IDs/arity, ordinary wire metadata and fixed
reply-scope policies. Production factoring must instantiate those same helpers
and prove its source/target correspondence; a checked recipe is not a claim
that the runtime has already been factored. Direct predicates remain
unevaluated guard atoms until the authorized candidate-COMM observation boundary.

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
