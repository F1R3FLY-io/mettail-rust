# Installed FLT semantic judgments

## Boundary and implementation status

A foreign-language term (FLT) is scoped structural syntax, not an authority
token. A semantic request names an opaque installed-language handle and an
action or declared observation of that language. Its input has already passed
through the language-qualified parser/template path. Execution must not render
the term and parse it again.

The [dispatch model](../../formal/rocq/runtime_grammar/theories/InstalledFltJudgments.v)
specifies the installed-service boundary and precedes its Rust implementation.
The existing semantic kernel and installation services are implemented. The
private reflected-term adapter now connects closed positional constructors and
String, Integer and Boolean atoms to that kernel in both directions. The
typed semantic service connects committed limits, bounded matcher preparation,
exact action/observation selection, existing-kernel execution, complete output and
receipt preparation, and final capability-authorized publication. Its Rholang
wire interface and the node's funding/effect transaction are separate connections
that are not yet implemented by this service.
This document is their implementation contract, not a claim that the node
demonstration is runnable or that every language shape is supported.

## Reuse and representation

| Responsibility | Existing implementation | Required connection |
|---|---|---|
| Resolve authority | `RholangLanguageRuntime::resolve` and `InstalledLanguageTable::authorize_all` | Resolve only the caller's opaque handle and check every operation/action right together |
| Parse and fill syntax | `dynamic_syntax_to_ground_term` and `reflect_flt_construction` | Consume the already reflected value; preserve structural holes and their scope |
| Check reflected syntax | `DynamicSyntaxAdmission` | Factor its structural recognition into a checked inverse with distinct rejection and exhaustion |
| Represent theory operators | `theory_operator_to_machine` | Resolve constructor bindings and literal carriers from the installed theory |
| Admit semantic input | `SemanticTransitionInput::admit_accounted` | Supply the typed structural projection and explicit limits; retain work on every outcome |
| Execute an action | `SemanticTransitionMatcher::execute_action_accounted` | Invoke the existing one-step or normalization policy with the exact restored image, retaining usage on every outcome |
| Commit a service result | `InstalledLanguageTable::with_authorized_all` | Revalidate the same handle while committing the complete prepared result |

The sources are the
[language service](../../rholang-runtime/src/language_install.rs),
[installed table](../../grammar-core/src/installed.rs),
[dynamic reflection](../../rholang-codegen/src/dynamic_reflection.rs),
[structural admission](../../rholang-codegen/src/dynamic_admission.rs), and
[semantic kernel](../../dovetail-runtime/src/semantic_transition_kernel.rs).

The generated `SemanticMachineImage` projection has a different operator
representation from runtime theory execution. Its projector is not a drop-in
replacement for `theory_operator_to_machine`. The new adapter must preserve
the existing reflected ABI and resolve
`TheoryConstructorImageV1::grammar`; equal numeric identifiers in different
tables do not establish a correspondence.

A literal category need not have a constructor. For example, the existing
Regex `Scalar` token produces `DynamicValue::Text`, reflected as an existing
native atom. Decode that atom under the expected theory sort and declared
literal carrier. Do not invent a scalar constructor or reinterpret its text
as source code.

The [structural category-admission contract](dynamic-syntax-admission.md)
describes how constructor and literal alternatives are combined, including
unknown callback output contracts and bounded checking. This checker establishes
structural membership; it is not the bidirectional semantic-kernel adapter.

The adapter must account for every shape used by the practical application.
Unsupported shapes require stable refusal; a required shape is an implementation
blocker, not grounds for silently narrowing the application. Round-trip laws
must cover admitted constructors, literals, ordering, multiplicity and scope.
Their proofs precede the corresponding adapter implementation.

### Installed constructor and sort bindings

The private [installed binding index](../../rholang-runtime/src/installed_flt.rs)
borrows `language_core()` and `semantic_image()` from the same
`InstalledLanguage`. Installation has already checked that pair's fingerprints,
source correspondence and dense semantic identifiers. Building this index does
not repeat image compilation or validation and does not confer operation rights.

Grammar categories and theory sorts have separate coordinate spaces. Join a
Syntax sort to its category by its canonical source name, retain both coordinates,
and retain the exact optional literal carrier from the image. A Syntax sort with
no literal carrier, an unsupported non-Syntax sort and an invalid coordinate are
distinct observations. In particular, lexical token output is not used to infer
a semantic literal carrier. The installed Regex fixture declares String carriers
for Scalar and Text, Integer carriers for Nat and Grade, and a Boolean carrier
for Bool. Native Boolean values coexist with ordinary Boolean constructors.

The immutable index is assembled in declaration order:

```text
reserve private category, sort, constructor and lookup tables
join each admitted Syntax sort to its same-named category
for each grammar production:
    record its constructor ID and label
    accept an identical repeat; reject a different label for that ID
for each semantic constructor, exactly once:
    retain its exact image signature and canonical source label
    check its grammar pair against the recorded production and joined result sort
    reject a reserved label or an occupied (result sort, label) key
    insert that same entry into forward and reverse lookup
publish the complete private index only after every check succeeds
```

Forward lookup uses `(expected theory sort, reflected label)`; reverse lookup
uses the image's dense semantic constructor coordinate. Both retain the same
borrowed signature, including its grammar pair and ordered domain. Repeated
grammar productions do not duplicate semantic entries. Hash iteration does not
assign identifiers or order results, and hash collisions are resolved by exact
key equality rather than treated as identity. Lookup allocates no label String
and does not scan productions for every term occurrence.

Index materialization uses fixed-width logical coordinate-slot reservations,
not Rust pointer sizes. Optional coordinates cost five bytes; coordinate pairs
cost eight; a forward binding costs twelve. Empty optional slots and temporary
maps count too. If $`C`$, $`S`$, $`P`$ and $`K`$ are the category, sort, production
and semantic-constructor counts, the complete logical payload charge is:

```math
13C + 5S + 8P + 20K.
```

This schedule is not another wire encoding. Checked multiplication and paired
work/byte reservations precede allocation; successful temporary reservations
are not refunded. Hash-table overhead, allocator capacity and resident memory
are excluded. Equal admitted rosters have equal logical charges, but this does
not establish identical allocation success on different machines; common
resource profiles and representable limits remain required.

The [binding enrollment model](../../formal/rocq/runtime_grammar/theories/InstalledFltBindingEnrollment.v)
connects named sort joins, exact signature/label assembly and incremental
collision checks to the existing head codec's inverse law. It proves retention
of every constructor entry, not just successful lookup of a subset. Source/image
admission remains the installer's responsibility. These laws do not prove a
worst-case hash-probe count, allocator behavior or elapsed-time bound.

### Borrowed positional and native kernel view

`theory_positional_native_view` exposes the existing theory-machine decoder
without reconstructing a tree. A constructor view borrows its exact installed
signature and ordered child slice. A native view contains a borrowed String or
an exact Integer or Boolean. Boolean decoding is available in ordinary library
builds, not only in the kernel's unit-test configuration.

The view checks the root coordinate, a sole representative, the expected sort,
the existing operator framing and the supported head's signature. Constructor
lookup is shared with the Horn evaluator, and native decoding is shared with
the existing intrinsic evaluator. Neither uses a new encoding or evaluator.
The complete constructor record is retained, including its optional grammar
binding; equal numeric identifiers in unrelated tables are not substituted.

The operation consumes cumulative work: one unit for the node, one for every
constructor child slot, and one for each String byte before UTF-8 validation.
An overdrawn incoming counter is rejected before incrementing it. Returning a
borrowed slice makes no allocation and does not visit or validate descendants.
The adapter must subsequently visit and charge every occurrence, including
repeated references to the same graph vertex.

`Ok(None)` means that no supported local view was established. It deliberately
retains the existing decoder's behavior for unsupported and some malformed
literal forms; it is not evidence of validity or a complete semantic rejection.
Invalid evidence, cancellation and exhaustion remain distinct errors.
This local API does not authenticate an action result or its receipt. The
inverse adapter must retain the actual published result bundle and apply the
separate request, receipt and whole-output checks described below.

### Checked operator materialization

`TheoryPositionalNativeEncoding` borrows a constructor or supported native
operator and computes its size without allocation. Its `encode()` method
reserves the three vector capacities and invokes the existing
`TheoryImageOperatorV1::write_content`; it does not define another encoding.
The caller must charge its cumulative budget before materializing the plan.
Unsupported forms return no plan, separately from arithmetic overflow.

Let $`n`$ be a String's UTF-8 byte length, $`D`$ the machine domain's byte
length, and $`I`$ the inner operator's encoded length. The existing writer gives:

| Operator | $`I`$ |
|---|---:|
| Constructor | 5 |
| String literal | $`14+n`$ |
| Integer literal | 22 |
| Boolean literal | 7 |

The complete framed operator length is $`F=28+D+I`$. The 28 bytes include the
eight-byte frame around the four-byte discriminant and two further length
frames. They must not be mistaken for an unframed discriminant.

For a node with $`d`$ ordered child occurrences, the current e-graph insertion
path materializes the caller node, two canonicalized copies, one class copy,
and one parent-record copy per child. Its conservative logical payload
reservation, including temporary copies and additional coordinates, is:

```math
(d+4)(F+4d)+4d+13.
```

The [materialization model](../../formal/rocq/runtime_grammar/theories/KernelOperatorMaterialization.v)
connects this schedule to the existing writer's exact sizes and cumulative
preallocation. Repeated children count separately. A duplicate may pay this
conservative reservation, but still uses the existing duplicate-before-node-limit
decision. This is not a new e-graph implementation, an exact CPU cost, a bound on
hash probes or an allocator/RSS certificate.

### Strict reflected-head enrollment

The [reflected codec](../../rholang-codegen/src/reflected_codec.rs) shares the
existing positional-envelope, private-tag, native-payload and reflection
helpers. Its `ReflectedPositionalContext` is bound to the exact owner fingerprint
and precomputes the existing true ground marker once. This context is structural
data, not installed-language authority.

The closed adapter has two stricter enrollment conditions than general syntax
admission. A private tag must equal its canonical encoding through the existing
String writer. The protobuf String reader can ignore unknown fields: appending
the bytes `[0x10, 0x00]` can preserve decoded text while changing the actual
private name. Reject this input; do not silently normalize one nominal identity
into another. Similarly, a marked closed constructor must carry the exact
`^gnd` marker. Accepting `^nog` and rebuilding `^gnd` would change its marker.
Native reserved labels remain unmarked. General admission retains its existing
policy; these checks apply to the new closed conversion boundary.

The head view owns one decoded tag and borrows the original ordered children.
Its label is a slice of that tag, avoiding another label allocation. Native
label decoding and encoding reuse the existing lowercase hexadecimal text,
canonical signed integer and Boolean implementations. They do not parse guest
source, select an installed language or validate a complete subtree.

`ReflectedCodecBudget` borrows the caller's cumulative work counter and
cancellation callback and tracks a decreasing payload-byte allowance. Each
reservation checks both dimensions before changing either balance. Failed
reservations spend nothing; later malformed input or allocation failure does
not refund work already performed. Its consuming `finish()` returns unused
bytes so a subsequent kernel call and all output conversions can share the
original allowance without replenishing it.

| Operation | Reservation before materialization |
|---|---|
| Decode a private tag | Its flat encoded ID length, before invoking the existing String decoder |
| Check canonical private identity | The decoded scalar's encoded length, before reencoding with the existing writer |
| Construct the ground-marker context | The checked tag length plus its protobuf String encoding length |
| Decode native text | Input-label scanning, then the decoded byte-buffer length before allocation |
| Encode native text | Prefix length plus twice the UTF-8 byte length, using checked arithmetic |
| Format a native integer | At most 40 decimal bytes, conservatively reserved before formatting |
| Visit constructor slots | Every child slot, including repeated occurrences |

These and the index-slot charges are logical work and payload reservations, not
a claim about allocator capacity or resident memory. Only a flat scalar's
`encoded_len()` is used;
recursive `Par` encoding is not used to estimate traversal cost. The existing
iterative `Par` and `GroundTerm` ownership paths remain responsible for cleanup.

### Shared local output assembly

`ReflectedPositionalContext::assemble` accepts an actual vector of already
reflected children and their ground bits. It reserves an element buffer, then
delegates to the same local body as `assemble_positional_ground_node`. No
placeholder source terms are created. The helper does not establish child
typing or justify its supplied ground bits; the adapter owns those checks.

The body retains the existing label-specific policy: `^bound` is nonground,
`^free` is ground, and other nodes combine all child ground bits. Marked nodes
receive the resulting `^gnd` or `^nog` marker. Unmarked native labels do not
receive a marker. The cached true marker used for closed input enrollment is
not substituted for a newly assembled nonground marker.

Assembly moves children in their original order and preserves the existing
padded `locally_free` byte union. Let $`l_i`$ be the byte length of child
$`i`$'s bitset, $`m_i=\max_{j\leq i}l_j`$ its prefix maximum, and $`M`$ the final
maximum (zero for no children). The existing local body materializes:

```math
L=\sum_i l_i+\sum_i m_i+2M
```

metadata bytes: each child-bitset clone, each prefix union, and two final
bitset copies. A charged flat pass computes $`L`$ without examining descendants.
If $`S`$ counts the tag/marker Strings and their protobuf byte buffers, and
$`m`$ is one for a marked label or zero otherwise, local assembly reserves:

```math
S+L+4\bigl((d+2)+(1+m)+1\bigr).
```

The slot terms cover the element buffer, tag/marker unforgeables and outer
expression. The incoming child-tuple vector is charged by the traversal where
it is created. Checked arithmetic and the combined work/byte reservation precede
allocation. On refusal, owned children use the existing stack-safe destructor.
Not all underlying primitive allocations expose recoverable allocation errors;
the logical reservation is not a promise of allocation success or an RSS bound.

The [local assembly model](../../formal/rocq/runtime_grammar/theories/ReflectedLocalAssembly.v)
proves shared-body equivalence, preservation of ordered child occurrences and
metadata, and the iterative metadata size observer. Tests explicitly compare
root and list metadata bytes because ordinary `Par` equality omits that metadata.

### Bidirectional occurrence traversal

`InstalledFltAdapter` binds the exact installed pair and the existing reflected
owner label derived from its **full language fingerprint**, not its parser-only
fingerprint. Creating this private object does not authorize a request. The
service must resolve and authorize the opaque handle first.

Both directions use the same three work-item forms: visit a typed reference,
advance an ordered child cursor, and assemble a constructor at a saved value-stack
base. The source reference is a borrowed `Par` in the forward direction and a
borrowed e-class coordinate in the inverse direction. The constructor instruction
retains the binding index's exact signature and source label.

```text
push Visit(root, expected_sort)
while a pending work item exists:
    charge one scheduling step
    Visit(reference, sort):
        establish the checked local view under the exact installed image
        native atom: decode/encode its declared carrier and push its value
        constructor: check arity, then schedule Children before Assemble
    Children(first :: rest, first_sort :: later_sorts):
        schedule Visit(first, first_sort) before the remaining child cursor
    Children(empty, empty): finish this cursor
    Assemble(binding, saved_base):
        require exactly binding.arity new values above saved_base
        reserve the child vector and move those values in original order
        invoke the shared local assembler and push its single result
require no pending work and exactly one root value
```

LIFO insertion puts assembly below the child cursor and later children below
the next visit. No whole intermediate `GroundTerm`, flattened instruction
program, guest-source reparse, or recursive traversal is created. Each occurrence
is visited even when several references point to the same graph node.

The forward machine accepts only canonical closed reflected heads, joins the
input category to its theory sort, and checks every child against the declared
domain. Native labels must be nullary and match the exact String, Integer or
Boolean carrier. Moving decoded String ownership uses `mem::take` through a
mutable borrow, preserving `DynamicValue`'s existing iterative destructor.
Unsupported forms are errors, not empty successful results.

Fresh kernel insertion reuses `TheoryPositionalNativeEncoding` and the existing
add-only e-graph. Its node ceiling is bounded by the representable 32-bit class
space; every child is an already-built valid canonical coordinate. Duplicate
insertion is tested before the distinct-node ceiling by the existing e-graph
method. The complete root then enters the existing exact admission/projection
once. There is no second cycle analysis or separate graph validator.

The inverse borrows the original `ProvenSemanticTransitions`, whose private
graph carries the kernel's acyclic publication projection. It checks the declared
result sort and reconstructs **every** transition, in its original order and with
all repeated child occurrences. It neither selects a preferred result nor sorts
or deduplicates roots. A malformed or exhausted later result returns an error,
not an earlier successful prefix. The public transition roster and receipt fields
still require the service's separate validation; a valid local view is not an
authenticated receipt or evidence of the original action-output roster.

Dynamic work/value buffers track logical reserved capacity separately from
`Vec::capacity()`. A full logical buffer grows by the greater of one and its
current logical capacity. Checked capacity addition and byte multiplication,
then cumulative reservation, precede the physical capacity request. Allocator
spare capacity cannot change the logical charge. Slots cost 33 bytes for a work
item, nine for a reflected occurrence plus its ground bit, four for an e-class
coordinate, and eight for an output occurrence reference. These fixed logical
payloads are not Rust layout, physical heap usage or a wire encoding. Temporary
child buffers and the shared operator/assembly payload schedules are charged
separately where they are materialized.

## Exact dispatch and rights

An installed bundle keeps its authoritative language value, admitted semantic
image and restored matcher together. `restore(image)` does not itself retain
an image fingerprint, so the service must prevent pairing that matcher with a
different image. A cache hit never bypasses installation or authorization.

The model's trusted bundle lookup is keyed by the installed authority entry's
commitment. Canonical action/observation names resolve to identifiers only
inside that bundle. The kernel request is built from the resolved call:
installed language/theory/image commitments, selected action, exact input key,
and the handle's actual granted rights. Reflected tags cannot supply any of
these authorities.

| Request | Required rights | Selection |
|---|---|---|
| Reduce an action | `Reduce` plus the action's declared rights | Exactly the named action |
| Observe a declaration | `Observe` plus the action's declared rights | Exactly the action and result sort named by that observation |

An observation does not grant raw `ReflectAst` access. It also does not invent
an unconditional `Reduce` requirement: a one-step observational action may
declare no such right. A normalization action already requires `Reduce` in its
validated declaration. Nested transition and guard requirements remain enforced
by the existing kernel.

Before execution, check the input's expected sort against the selected domain.
Pass the selected result sort into reconstruction. Observation result-sort
mismatch, absent declarations and unsupported input shapes cannot fall back to
another action or parser.

### Installed preparation and exact names

The private [semantic-service support](../../rholang-runtime/src/semantic_service.rs)
owns an `InstalledSemanticBundle`: an authorized `Arc<InstalledLanguage>`, the
matcher restored from that owner's borrowed image, and the same sealed handle.
Its constructor accepts a table, handle and required rights, not a separately
supplied image or matcher. Execution obtains its image from the stored owner and
its grant from the stored handle. There is no matcher cache or second image
compilation in this path. The structural adapter borrows the same owner.

Preparation calls `authorize_all` before any setup or restoration work. A flat
planning pass charges the setup schedule below, then the existing
`SemanticTransitionMatcher::restore` constructs its transition and judgment
automata. Both planning and the final post-restoration check consult cancellation.
The restorer itself has no cancellation callback: this does not promise an
interrupt inside restoration or a wall-clock response bound. A cancellation
observed afterward refuses the still-private bundle.

Exact name selection scans the admitted declaration roster with a bounded,
allocation-free cursor. It does not assume that names are sorted. Each comparison
charges a cursor step and the declaration name's UTF-8 length; the requested name
is also charged before the scan. The existing compiler preserves source action
order when assigning dense image action identifiers. Selection checks the selected
identifier, ordered unary input, input/result sort names and declared rights
against that same owner's image. Observation lookup first selects the declaration,
then its named action, and checks its declared result against the action codomain.
Unknown, differently cased or trailing-NUL names are not aliases.

The operation right and action rights are reserved and collected into one private
slice for the table's existing single-lock authorization. Possessing this selection
or preparation is not permission to publish. Final publication must use the same
sealed handle and complete required-right slice. The final table-read callback
must only move already prepared results: acquiring the capability-directory lock
there would reverse the existing directory-then-table lock order used by revocation.

## Private execution and complete publication

`RholangLanguageRuntime::execute_semantic` accepts a `SemanticServiceRequest`:
an opaque handle `Par`, `SemanticOperation::Reduce(action)` or
`SemanticOperation::Observe(observation)`, an already constructed input `Par`,
and requested `SemanticServiceLimits`. It returns `SemanticServiceReport`.
Success contains every `SemanticServiceResult`, pairing a reflected term with
its complete original `SemanticTransitionReceipt`. Failure contains a typed
`InstalledSemanticError`, not a successful prefix. Both outcomes retain whole-
request work, optional kernel aggregate, effective limits when authorization
reached that stage, and the remaining cumulative boundary payload allowance.

This typed report is not the canonical Rholang wire reply or a node settlement
certificate. The downstream wire layer must carry the remaining allowances and
establish neutral public ordering without discarding results. It must not reset
work or treat the kernel's repeated receipt counters as new execution charges.

The service follows this order. The pseudocode names operations, not new
alternative implementations of the parser or kernel.

```text
resolve the opaque handle and its installed bundle
select the exact action or declared observation
authorize the operation right and all declared action rights
compute installed / host / request limit intersections
decode and type-check the reflected input with a bounded worklist
invoke the bundle's existing kernel with the derived request
propagate Refuted or Undetermined without a successful value
verify every successful transition receipt against that request
check each receipt's repeated work equals the one execution aggregate
reconstruct every output at the declared result sort
prepare the entire canonical reply and complete receipt evidence
check total work, output and receipt limits
revalidate the same handle at the guarded service commit
publish the complete prepared result
```

Reconstruction and encoding are all-or-error traversals. A valid first output
followed by an invalid or exhausted output must expose neither output. The
model retains every source transition and its receipt in order; that is a
transport-preservation theorem, not a proof that an arbitrary input list
contains valid semantic successors. Receipt checks and the exact kernel call
are separate, mandatory premises.

Canonical public order must be independent of temporary e-class or substitution
identifiers. The kernel currently uses such identifiers as internal tie-breakers;
the wire adapter must establish an order from exact structural keys and complete
neutral receipt evidence without pruning alternatives. No internal graph ID is
a public term identity.

`Refuted` is not automatically a Boolean false observation. In particular,
`NoTransition` and a violated determinism claim remain distinct failures.
`Undetermined` is not an empty successful result. An exhausted search cannot
publish a prefix, spend a purse or commit an effect.

## Resource accounting

For each kernel execution dimension, the effective limit is the intersection of the
installed language, host policy and request ceilings:

```math
L_{\mathrm{effective}}(d)=
\min\bigl(L_{\mathrm{installed}}(d),
          L_{\mathrm{host}}(d),
          L_{\mathrm{request}}(d)\bigr).
```

The dimensions include logical work, normalization steps, frontier, proof and
term bounds, and output bounds. `SemanticTransitionLimits::from` does not
perform this intersection; the service must do it. Each stage must check its
allocation/traversal limit before incurring the bounded work, not only after
constructing a large reply.

### Committed host ceilings and setup reservations

`SemanticServiceLimits` contains the existing ten-coordinate
`SemanticTransitionLimits` and a separate `boundary_payload_bytes` allowance.
Execution limits use the intersection above. The boundary allowance is cumulative
logical payload reserved by preparation and conversion; it is not the kernel's
input-key or output-size limit. Because `TheoryLimitsV1` has no cumulative
boundary-allocation coordinate, this allowance meets **host and request only**.
Neither allowance is a semantic `Cost(G)` grade.

The existing theory-to-execution projection is retained exactly:

| Installed theory field | Execution coordinates |
|---|---|
| `max_steps` | `work`, `normalization_steps` |
| `max_frontier` | `outputs`, `frontier`, `proofs` |
| `max_proof_nodes` | `proof_nodes` |
| `max_term_nodes` | `term_nodes` |
| `max_output_nodes` | `output_nodes` |
| `max_output_bytes` | `term_bytes`, `output_bytes` |

Default host execution ceilings use `TheoryLimitsV1::default()` through this
projection. The separately defined default boundary allowance is 16 MiB.
Requests may attenuate any coordinate, including to zero; no minimum amount of
work is silently granted to make a request succeed.

Installation policy commitment domain `mettail-install-policy/6` retains the
existing parser, artifact, grant and capability fields. It additionally commits
the setup and receipt-transport schedule versions and all eleven semantic-service coordinates in fixed
order, each encoded as a sixteen-byte big-endian unsigned word. Pointer width
does not determine the encoding. The semantic-limit builder recomputes the
commitment, and service construction recomputes it from the actual policy fields
so a host's earlier field mutation cannot leave a stale fingerprint. This is a
policy identity change, not a semantic-image ABI change.

Setup schedule version 1 visits the transition automaton followed by the judgment
automaton. It makes no allocation and uses no recursive descent. Every row below
is charged before advancing into the corresponding work-bearing structure:

| Structure | Logical work | Logical payload bytes |
|---|---:|---:|
| Automaton header, including empty rosters | 1 | 16 |
| State: identifier, slot count, tag and argument count | 1 | 17 |
| Fixed operator descriptor, including every non-positional form | 1 | 32 |
| String or Bytes literal payload of length $`n`$ | $`n`$ | $`n`$ |
| Invocation target and parent-slot count | 1 | 12 |
| Parent-slot coordinate | 1 | 4 |
| Entry identifier, rule, root and variable count | 1 | 20 |
| Variable coordinate and reconstructed slot name | 12 | 23 |

The last row reserves a four-byte coordinate, eight-byte length and at most
eleven bytes for the existing `v`-prefixed decimal `u32` name. The fixed operator
descriptor is a padded logical scalar/coordinate reservation, **not** a new
encoder. Actual operator encoding and automaton reconstruction remain in the
existing matcher. Literal lengths are observed without traversing their contents;
all roster and slot walks are incrementally charged. A failed reservation leaves
both balances unchanged and prevents restoration. Accepted earlier charges are
not refunded on later failure.

This schedule measures admitted image structure, not every temporary copy,
hash-table probe, allocation, CPU instruction or byte of resident memory.
Restoration remains constrained by artifact admission as well. The
[service glue model](../../formal/rocq/runtime_grammar/theories/InstalledSemanticService.v)
proves non-amplification, retention of every ordered prehash policy word, exact
name-to-source coordinates, setup prefix conservation and the authorized
same-owner factory contract. It does not prove hash injectivity, arbitrary
restorer correctness or Rust implementation correctness. Focused source tests
exercise all operator forms, both automata, exact/one-less limits, cancellation
prefixes, policy commitments, and actual installed Regex actions and observations.

`ProvenSemanticTransitions::work` is aggregate request work. Each transition's
receipt repeats that aggregate. Charge it once, then add boundary conversion
and encoding work; summing all receipt work fields would multiply the charge
by the number of results. Semantic input admission already included in the
kernel aggregate must not also be counted as boundary decoding.

The adapter uses `ReflectedCodecBudget::run_accounted_stage` to lend the same
cancellation hook and remaining work allowance to a trusted stage whose local
counter starts at zero. Its reported usage is absorbed on success **and** error;
an over-limit report is refused rather than saturated. The converter's remaining
payload allowance is carried unchanged through this handoff.

Specifically, let $`L`$ be the work ceiling, $`C`$ the conversion prefix, $`A`$
the input-admission work, and $`K`$ the later kernel aggregate, which includes
$`A`$. Admission receives at most $`L-C`$ and returns its counter on every
outcome. The legacy `admit` entry delegates to this same body and discards only
the usage observation. Later execution must receive the ceiling $`L-C`$, not
$`L-C-A`$, and its continuation must check $`A\leq K`$ before adding $`K-A`$.
Thus the combined charge is:

```math
(C+A)+(K-A)=C+K\leq L.
```

The [usage model](../../formal/rocq/runtime_grammar/theories/InstalledFltUsage.v)
proves this prefix accounting and shared-body observation, plus the logical
buffer-growth reservation equations. `execute_action_accounted` and its
guard-capable counterpart return the existing decision together with the
aggregate on every outcome. The original execution methods project the
decision from the same once-run body. The qualified service uses that accounted
entrypoint and absorbs only the increment beyond input admission.

The kernel's child-call protocol is:

```text
save the caller's current work
run the child once with the remaining allowance and a fresh local counter
absorb its returned work, checking addition and the caller's ceiling
merge diagnostic counters without erasing the absorbed work on failure
only then handle success, refutation, exhaustion, or another candidate
```

Transition matching, judgment-head matching and Horn proof search all report
their actual terminal counters. Validation failure, an empty match set and a
refuted premise do not imply zero work. A successful automaton scan is absorbed
before subsequent fallible rule selection or allocation. Temporary Horn
evaluators export their counters on failure as well as success. Normalization
uses the same action counter, so failed alternatives remain included in the
normalization hop's work and the final aggregate. Guards already implement
all-outcome reporting and retain that protocol without a second charge.

The [work-transport model](../../formal/rocq/runtime_grammar/theories/SemanticWorkTransport.v)
uses explicit suspended-counter frames. Its finite-trace laws prove that the
active and suspended counters together equal the admission prefix plus every
accepted charge exactly once, with nested ceilings preserved. Child-return
witnesses cover every semantic outcome and a later diagnostic failure. These
are accounting laws, not a proof of the Rust evaluator or its semantic branch
policy; implementation correspondence also requires source review and tests.

An execution request whose admission prefix already exceeds its new work
ceiling is refused without further execution. The separate aggregate retains
the spent admission prefix. For compatibility, this exceptional legacy
`Undetermined` decision still embeds zero; callers must use the accounted
result rather than infer usage from that field. The installed-service protocol
establishes a sufficient incoming ceiling and therefore excludes this overdraw.

Correct accounting can exhaust a tight budget earlier than an implementation
that omitted failed searches. Aggregate and normalization-hop work can increase
accordingly. The semantic branch policy is unchanged, but prior accounting
bytes are not promised to remain identical.

`SemanticInputLimits::bytes` is a separate exact-key/publication-size ceiling.
It is **not** an allocation-usage report or the converter's remaining payload
allowance. Passing it to the existing kernel does not prove pre-allocation
accounting for every kernel-internal allocation. Kernel logical work, converter
payload reservation and kernel structural-size limits remain distinct.

The publication gate also checks that every receipt reports that same aggregate.
Without this equality, request/image binding could accept a receipt reporting
100 units while the separate execution usage reports zero. The closed negative
example in the model exercises exactly that mismatch, with a ceiling of 20;
the revised gate rejects it as invalid internal evidence before encoding.

The dispatch model uses mathematical naturals and abstract receipt/payload
atoms. Its publication bound is not yet a concrete byte-codec or allocation
proof. The implementation must supply exact byte-length and work-count
correspondence, checked integer arithmetic and pre-allocation checks.
The model names the abstract output dimension `OutputAtoms`, not bytes.
Its current execution and codec parameters are checked at publication; these
checks do not prove that computation stops before exceeding a ceiling. Passing
residual work to each stage and proving prefix/pre-allocation enforcement are
mandatory implementation refinements, not consequences of a final bound.

Logical work, semantic `Cost(G)` grades and actual host funding are different
quantities. `NoSemanticGrade` does not mean free host execution. A costed image
without the required resource evidence returns `ResourceGradeUnavailable`;
purity cannot justify manufacturing a grade.

### Complete receipt preparation and transport

The service checks only its own immediate, unmodified kernel result. Publicly
mutable transition records from an external caller do not carry this provenance.
Each fresh receipt must match the installed language/theory/image commitments,
selected action and executable entry rule, exact input key, output sort,
effect/class, resource profile and single kernel work aggregate. The original
input key is retained by an inexpensive shared `ContentKey` handle; successful
kernel execution has already populated its shared flattened-byte cache.

Output-key creation and graph publication are existing kernel responsibilities;
the service does not traverse the graph again to reconstruct every output key.
The inverse adapter still checks and reflects every output at the declared sort.
For normalization, adjacent hop boundaries and the final output must agree.
The first hop begins after the entry rewrite, not at the original input. Nested
premise rule identifiers may differ from the entry rule. Judgment receipts retain
their counts and identifiers; they are not expanded into invented proof trees.

Receipt schedule version 1 reserves every field through a borrowed, flat walk.
Its nesting is finite: receipts contain hops, hops contain proofs, and premises
may contain intrinsic key lists. No recursive serializer is introduced.

| Receipt component | Logical work | Logical payload bytes |
|---|---:|---:|
| Fixed receipt header: commitments, action/rule/effect, class, work | 1 | 117 |
| Variable byte payload of length $`n`$, including its length | $`n+1`$ | $`n+8`$ |
| No-grade resource tag | 1 | 1 |
| Checked-grade descriptor, excluding its variable grade payload | 1 | 37 |
| Premise, hop, proof or intrinsic-key list count | 1 | 8 |
| Common premise descriptor: tag, rule and premise coordinate | 1 | 9 |
| Transition or universal-premise extra coordinate | 1 | 4 |
| Judgment extra coordinates and proof counts | 1 | 12 |
| Guard and evidence commitments | 1 | 64 |
| Intrinsic opcode and recorded work | 1 | 9 |
| Hop's recorded work | 1 | 8 |
| Normalization proof's rule coordinate | 1 | 4 |

Freshness premises need only the common descriptor. Every intrinsic input/output
key, hop boundary, proof boundary and repeated premise is visited and reserved.
Recorded aggregate, hop and intrinsic work values are transported as fixed-width
data; their numeric values are never added again as execution work. The checked-
grade shape is accounted for by the walker but does not authorize a costed action
without the kernel's separately required grade evidence.

After reflection, the term and transition counts must agree before pairing.
Pairing reserves sixteen logical payload bytes per result record, charges the
record roster and each move, and moves the whole receipt without cloning its
payloads. Duplicate derivations remain separate entries. A mismatch, cancellation
or failure after a private prefix returns an error with no exported results.
The final authorization callback only moves the complete prepared result and
never invokes user callbacks while holding the installed-table lock.

The [receipt transport model](../../formal/rocq/runtime_grammar/theories/SemanticReceiptTransport.v)
mirrors all six premise variants and the complete hop/proof records. It proves
both budget-prefix laws, preservation of every receipt field and ordered list,
and rejection of unequal-length pairing. Its envelope projection reuses the
existing binding predicate; it does not independently prove kernel semantics,
fresh-output provenance, a final wire encoding or physical memory bounds.

The [Regex fixture](../../rholang-runtime/tests/fixtures/regex_extension.rho)
explicitly uses the existing finite theory default of 10,000,000 work units.
That source policy covers whole-request processing, not just the rewrite kernel.
Tests separately install an identical theory with a 4,096-unit source ceiling
and require failure without outputs; larger host/request ceilings cannot amplify
it. Each successful action and observation is also exercised at its measured
exact request-work/payload bounds and with either bound one unit smaller.

## Formal correspondence and verification

The model reuses
[installed-language authority](../../formal/rocq/runtime_grammar/theories/InstalledLanguageAuthority.v)
and the
[kernel decision/receipt definitions](../../formal/rocq/runtime_grammar/theories/SemanticTransitionKernel.v).
The kernel is a parameterized execution boundary applied to the exact resolved
request. This establishes routing and checked publication for an implementation
of that boundary; it does not assume or prove that an arbitrary supplied
function implements GSLT semantics. Concrete instantiation uses the existing
kernel and its separate
[normalization model](../../formal/rocq/runtime_grammar/theories/SemanticNormalization.v).

The obligations are deliberately separate:

- Dispatch: exact installed selection, input annotation and output-sort routing.
- Authority: all required rights at the before/after epochs, with revocation
  preventing publication.
- Evidence: every exported receipt binds the derived request and installed image,
  and repeats the single execution work aggregate.
- Transport: all results and modeled receipts survive successful preparation;
  errors discard the private prefix.
- Resources: effective ceilings cannot amplify any source ceiling, and checked
  publication obeys its modeled usage bounds.
- Implementation refinement: actual codec typing, canonical bytes/order, work,
  stack safety and Rust source correspondence remain required before exposing
  the service.

### Structural codec proof layers

The structural adapter is a checked partial isomorphism: it may refuse an
unsupported or malformed term, but a successful conversion must preserve that
term exactly in its supported structural representation. Let $`P_s`$ project a
reflected occurrence tree into semantic terms at expected sort $`s`$, and let
$`R_s`$ restore it. For successful conversions of reflected term $`t`$ and
semantic term $`u`$, the reference model proves:

```math
P_s(t)=u \;\Longrightarrow\; R_s(u)=t,
\qquad
R_s(u)=t \;\Longrightarrow\; P_s(t)=u.
```

The proof layers have distinct responsibilities:

| Model | Established property |
|---|---|
| [Native payload codec](../../formal/rocq/runtime_grammar/theories/NativeReflectionCodec.v) | Exact lowercase hexadecimal bytes, canonical signed 128-bit decimal values, and Boolean payload round trips |
| [Installed constructor heads](../../formal/rocq/runtime_grammar/theories/InstalledFltHeadCodec.v) | Checked unique bindings and reserved-namespace separation; the argument plan uses the same resolved constructor's ordered domain |
| [Finite structural terms](../../formal/rocq/runtime_grammar/theories/InstalledFltTermCodec.v) | Both partial inverses over complete finite occurrence trees, with each node's owner and each child's expected sort checked |
| [Traversal contract](../../formal/rocq/runtime_grammar/theories/InstalledFltTraversal.v) | Reuse of checked stack scheduling and assembly ownership; singleton completion and preservation of the full prior resource charge |
| [Checked occurrence assembly](../../formal/rocq/runtime_grammar/theories/InstalledFltOccurrence.v) | Every successful projection supplies a checked occurrence witness; concrete postorder and borrowed execution return that exact projection and preserve the enclosing value stack |
| [Immediate instruction execution](../../formal/rocq/runtime_grammar/theories/FusedOccurrenceExecution.v) | The existing compiler emits at most one instruction per transition; executing it immediately preserves partial assembly, with exhaustion distinct from rejection |
| [Borrowed traversal](../../formal/rocq/runtime_grammar/theories/BorrowedOccurrenceExecution.v) | Deterministic local lookup has a unique finite unfolding; reference-based steps and runs refine the occurrence machine for sources with such an unfolding |
| [Fresh-arena realization](../../formal/rocq/runtime_grammar/theories/InstalledFltArena.v) | Exact interning preserves existing node meanings and realizes every ordered child occurrence; checked add-only construction supplies a topological arena and hence finite unfolding |
| [Local kernel view](../../formal/rocq/runtime_grammar/theories/KernelPositionalNativeView.v) | Exact octet-width and indexed constructor checks preserve ordered children; native payload observations retain framed text bytes, signed little-endian integer interpretation and canonical Boolean bytes; public entry charging refines the existing cumulative budget |
| [Reachable graph projection](../../formal/rocq/runtime_grammar/theories/InstalledFltGraphProjection.v) | The kernel's existing remapping contract transports every published root's complete finite occurrence, including native payloads and ordered child slots |
| [Reflected Par envelopes](../../formal/rocq/runtime_grammar/theories/ReflectedParEnvelope.v) | All nine executable component families are checked; an accepted expression, private-tag or send envelope cannot hide another executable component, including a conditional |
| [Strict reflected-head enrollment](../../formal/rocq/runtime_grammar/theories/ReflectedHeadEnrollment.v) | Canonical reenrollment preserves nominal bytes and exact owner/label, true ground markers round-trip, and paired work/payload reservations precede modeled allocation events |
| [Installed binding enrollment](../../formal/rocq/runtime_grammar/theories/InstalledFltBindingEnrollment.v) | Named joins retain distinct coordinates and exact optional carriers; complete signature assembly and collision-rejecting roster construction establish the existing constructor inverse premise without dropping entries |
| [Operator materialization](../../formal/rocq/runtime_grammar/theories/KernelOperatorMaterialization.v) | Exact inner and framed sizes agree with the existing writer; the conservative fresh-node payload schedule counts every modeled copy before allocation |
| [Local reflected assembly](../../formal/rocq/runtime_grammar/theories/ReflectedLocalAssembly.v) | Shared-body factoring retains markers, child order and both metadata vectors; the iterative flat length observer counts metadata copies before materialization |
| [Stage usage and logical reservations](../../formal/rocq/runtime_grammar/theories/InstalledFltUsage.v) | Shared admission-body observations retain every terminal counter; residual ceilings preserve prior work; an execution aggregate includes admission exactly once; logical buffer growth reserves enough new slots independently of physical capacity |
| [Nested work transport](../../formal/rocq/runtime_grammar/theories/SemanticWorkTransport.v) | Finite explicit-stack traces retain every accepted child charge on all outcomes, preserve nested ceilings, and retain already-spent admission on preflight overdraw |

For example, the term model distinguishes a native Boolean from an ordinary
constructor returning the Boolean sort. Its mixed-literal witness also uses
deliberately unrelated grammar and semantic identifiers. Replacing its text
child with a Boolean is rejected despite preserving the constructor's arity.
Repeated child occurrences remain repeated; a shared graph vertex is not
permission to omit an occurrence or its conversion charge.

The local-view model also proves that extracting a shared decoder body preserves
all observations for any body, including its error and work results. This is a
refactor law, not an assumption that an arbitrary decoder is correct. Its text
claim concerns the exact bytes submitted to the existing UTF-8 checker; it does
not prove that Rust standard-library checker or integer primitive. Focused tests
exercise the existing operator encoder, malformed framing, signed bounds,
Unicode, repeated child slots, wrong sorts, non-singleton classes, work exhaustion
and cancellation. An external library test checks production Boolean decoding.

The existing reflector reserves all labels beginning with `^` for native and
internal forms. The adapter's binding check must reuse
`ast::validation::is_reserved_reflect_label` and refuse an unrepresentable
constructor explicitly. Signature validity alone does not prevent a constructor
named `^dynamic-text:61` from colliding with the reflected text value `"a"`.
This is a representability condition for the existing reflection ABI, not a
change to Greg's identifier syntax or to the abstract grammar data schema.
Only constructor metadata labels are checked; a grammar may still use `^` in
its source syntax, for example as a regular-expression anchor.

These are proofs about structural observations, not arbitrary `Par` metadata
or protobuf byte strings. The concrete adapter must obtain its carrier map and
constructor bindings from the admitted image, establish native/constructor
separation in the actual reflected tags, and connect its physical source lookup
to the checked structural observation. The existing
[occurrence assembly model](../../formal/rocq/prattail_wpda_runtime/theories/SelectedOccurrencePlan.v)
proves postorder execution preserves declarative partial assembly.
`InstalledFltOccurrence` instantiates it with concrete semantic-node construction
and proves that successful projection supplies the needed witness. The borrowed
walker uses source references; neither its witness tree nor an instruction
program needs to be allocated by the implementation.

A borrowed reference can pair an expected sort with a source coordinate.
Its local view must preserve the exact head and ordered typed children.
The reference-runner theorem is conditional on a finite unfolding, not an
assertion that every graph is acyclic. For reflected `Par`, children are strictly
contained source elements. For a graph, the existing kernel admission and
publication passes use canonical class coordinates and reject cycles before
publishing a fresh, single-representative arena. A repeated sibling or shared
acyclic subtree is still visited at every occurrence during restoration.
Budget interruption or cancellation during lookup is `Undetermined`, not the
pure lookup model's missing-node rejection.

The graph-projection proof interprets both arenas through the same immutable
table of complete heads. A table entry includes native payload and sort identity
or the complete constructor identity and signature; a constructor discriminant
alone is insufficient. Remapping preserves this observation and every child
position without requiring old and new arena identifiers to be equal.

Fresh-arena construction uses the existing e-graph interner. A successful
insertion either reuses an exactly matching node or appends a singleton class
whose children already exist. No merge or rebuild occurs in this phase.
The arena proof connects returned coordinates to complete occurrence meanings
and preserves the meanings of all older coordinates. Each child's coordinate
precedes its parent's, which establishes finite unfolding from construction.
The effective capacity must also prevent the class identifier's integer
representation from overflowing; exact duplicates still succeed at capacity.

The inverse adapter borrows the actual `ProvenSemanticTransitions` bundle for
the whole restoration operation. Its private graph is immutable and has already
passed kernel publication, so the adapter must not add another pass just to
recheck cycles. This path does not accept an arbitrary detached graph or a
graph modified after `into_parts`. Each referenced root still needs `try_find`
and the independently expected sort's typed checks. All outputs are restored
or the operation fails without publishing a prefix.

Only the graph is private: transition roots, sorts and receipts remain publicly
mutable Rust fields. Therefore this boundary proves graph structure, not
receipt authenticity. The service retains the fresh kernel result without
intervening mutation and applies the request, action, image and receipt checks
before publication. A valid interior graph node is not evidence that it was
the action's original output.

The envelope proof separates executable structure from annotations. A
`conditional` alongside an otherwise valid reflected list or private tag is
additional executable content and must be refused, including in nested child
envelopes. This cardinality theorem does not replace the existing checks for
expression variants, private-name framing or ground markers.

Concrete correspondence with kernel admission/publication, fresh-arena
insertion, physical views, iterative destruction and actual per-operation
charging remains required. Control fuel bounds the model's scheduling transitions, not byte
work, allocation or semantic execution cost. A final resource bound on a
supplied charge trace does not itself prove those charges were made.

This model does not prove cryptographic collision freedom, Rust extraction,
the full normalization algorithm, or the later asynchronous RSpace produce and
funding transaction. The node integration must connect the service result to
its actual atomic effect/accounting boundary. The practical demonstration
still requires that public MeTTaIL-only node path and its end-to-end tests.

The before/after authority relation constrains successful publication; it is
not an operational proof that unauthorized requests never invoke the kernel.
The service implementation must enforce that earlier authorization gate.
The original dispatch model's abstract receipt records omit concrete intrinsic
and normalization fields. `SemanticReceiptTransport` adds the complete typed
records and whole-field transport laws. The concrete wire layer has its own
encoding correspondence below; neither model's record is itself the wire ABI.

Run proof compilation and separate kernel checking one at a time under the
repository's resource policy: at most 1 GiB memory, no swap, and generated
proof artifacts under `target/`. Do not invoke the entire formal workspace to
recheck this bounded dependency slice.

## Semantic request preparation and receipt transport

The typed operation and its wire adapter share one private preparation path.
Its prefix records already consumed logical work and boundary payload bytes;
the typed API supplies a zero prefix. Preparation subtracts consumed payload
from the smaller host/request allowance with checked subtraction. The existing
work counter continues under the installed/host/request meet. An overdrawn
prefix is refused, not reset or saturated. Every outcome retains usage, including
cancellation and failure after kernel execution. The kernel's aggregate is
still absorbed only once, excluding its already charged admission prefix.

Successful preparation returns complete private results and retained publication
authority. It neither publishes a reply nor holds an authority lock. This lets
the wire adapter finish bounded encoding before the actual guarded host commit.
The typed API commits the same prepared result directly; it does not rerun the
semantic kernel.

The [service model](../../formal/rocq/runtime_grammar/theories/InstalledSemanticService.v)
proves that resumed payload plus its consumed prefix equals the attenuated
ceiling, and that overdraw cannot replenish the allowance. These arithmetic
laws complement the existing cumulative-work and single-aggregate laws.

The [receipt wire model](../../formal/rocq/runtime_grammar/theories/SemanticReceiptWire.v)
specifies exact tagged lists over unsigned integer atoms and byte-string atoms.
At this layer, a byte string is data, never guest source text. A receipt is the
following 13-field list, in order:

```text
[languageFingerprint, theoryFingerprint, imageFingerprint,
 action, rule, inputKey, outputKey, effect, effectClass,
 resource, premises, normalizationHops, work]
```

Here `premises` and `normalizationHops` are complete ordered lists. The resource
form is `[0]` for no semantic grade, or `[1, sort, gradeKey, costImageFingerprint]`
for a checked grade. Absence is never represented as a zero-valued grade.
Effect-class tags are `0` pure, `1` structural, `2` behavioral, `3` resource,
and `4` external, matching the existing theory-image codec.

| Premise | Exact list fields |
|---|---|
| Freshness | `[0, rule, premise]` |
| Transition | `[1, rule, premise, childRule]` |
| Judgment | `[2, rule, premise, judgment, proofs, proofSteps]` |
| Universal premise | `[3, rule, premise, elements]` |
| Intrinsic | `[4, rule, premise, opcode, inputKeys, outputKeys, work]` |
| Guard | `[5, rule, premise, guardCommitment, evidenceCommitment]` |

Intrinsic opcode tags are `0` exact term equality, `1` UTF-8 end test, `2` UTF-8
scalar lookup, `3` UTF-8 slice, `4` checked natural addition and `5` UTF-8
concatenation. A normalization hop is `[beforeKey, afterKey, proofs, work]`;
each proof is `[rule, beforeKey, afterKey, premises]`. Every exhaustive proof
and repeated premise remains present. Work numbers in these records are
transported values, not additional execution charges.

All layers have executable partial decoders and proved left inverses. Thus
receipt encoding is injective, and decoding a complete encoded roster returns
exactly that roster, including order and multiplicity. Unknown tags, wrong
arities and wrong scalar kinds are rejected by the model. Its 13 printed
theorem contexts were closed after compilation and separate kernel checking.
This structural model deliberately does not prove concrete integer widths, byte ranges,
commitment lengths, `Par` sidecar rejection, canonical sorting, resource bounds
or semantic evidence validity. Those are distinct wire-refinement obligations;
this structural proof alone is not a completed wire implementation.

### Concrete scalar and receipt codecs

The public `semantic_wire` module provides bounded `encode_receipt_v1` and
`decode_receipt_v1` functions for that exact schema. Decoding returns untrusted
receipt data, not a semantic proof or publication capability. Neither function
executes a theory, sorts results, prunes alternatives or parses guest source.

Unsigned values through `i64::MAX` use `GInt`. Larger u64 values use exactly
nine positive signed big-endian `GBigInt` bytes: a zero sign byte followed by
the eight-byte word. The bounded reader rejects negative values, redundant
representations, wrong lengths, executable sidecars and nonliteral metadata;
dense-coordinate and host-index conversions are checked rather than truncated.
The existing signed integer decoder and BigInt writer are reused.

The [scalar model](../../formal/rocq/runtime_grammar/theories/SemanticWireScalar.v)
adapts the existing fixed-width big-endian induction to binary arithmetic, so
the proof checker need not allocate unary representations of 64-bit endpoints.
It proves round trips in both directions on the admitted domain, representation
uniqueness, exact widths and rejection of negative small integers. All eight
printed theorem contexts were closed after compilation and a separate kernel
check. The mathematical decoder is not a proof of the BigInt library; boundary
vectors and 10,000 deterministic Rust samples check that correspondence.

Wire materialization uses a cumulative logical reservation schedule:

| Operation | Additional logical payload reservation |
|---|---|
| Scalar or moved byte-buffer value | 16-byte value descriptor |
| Wide integer | Value descriptor plus nine materialized bytes |
| List encoding or decoded roster | Value descriptor plus eight bytes per child slot |
| Fingerprint encoding | Value descriptor plus 32 copied bytes |
| Borrowed variable-byte decoding | Value descriptor plus the copied bytes |
| Fingerprint decoding | 32 copied bytes |
| Decoded top-level receipt | One value descriptor |

Descriptors and slots are accounting units, not Rust object sizes or a physical
memory guarantee. Encoding an already owned byte buffer moves it; it does not
reserve another copy of its contents. Scalar decoding borrows without allocating.
Each visited wire value contributes one work unit, and materialized or decoded
scalar bytes contribute their byte visits. Roster storage is reserved before
allocation, and variable-size copies use fallible reservation. Previously
charged semantic execution is never repeated because its numeric work value
appears in a receipt.

The eight-test scalar/receipt suite passed locally. It exercises all 60
effect/opcode/resource combinations, complete nested evidence and duplicate
records, exact and one-less work/payload limits, cancellation at every checked
boundary, malformed nested envelopes and a 10,000-premise roster on a 128 KiB
stack. Fixed-depth codecs use iterative loops over variable rosters. These
results establish the scalar/receipt transport contract. Neutral result ordering,
complete request/response accounting and installed system-process integration
have separate contracts and correspondence checks described below.

### Stable result-ordering model

The [merge model](../../formal/rocq/runtime_grammar/theories/SemanticResultMerge.v)
specifies the fallible bottom-up merge algorithm selected for the result
boundary. Its comparison state includes already spent work; a refused comparison
returns that updated state and no result list. Refusal is never treated as an
equal-key comparison. Sorting operates on whole records so it cannot exchange
a term's receipt with another term's receipt.

The algorithm starts with singleton runs. A *run* is a contiguous sorted portion
of the index sequence; each nonfinal run fills the current width. One pass merges
adjacent runs, and the next pass doubles that width:

```text
current := input occurrence indices
width := 1
while width < length(current):
    scratch := empty sequence
    for each adjacent pair of width-sized runs in current:
        merge the runs into scratch
        choose the right head only on Greater; otherwise choose the left
        on comparison refusal, return failure with the updated comparison state
    exchange current and scratch
    width := 2 * width
return current
```

This is algorithmic pseudocode, not a second allocating implementation. The
Rocq specification represents contiguous ranges with `firstn` and `skipn`;
the intended Rust implementation borrows the corresponding index-buffer slices.
Its mathematical fuel parameters bound specification recursion. The termination
proof shows that those indices suffice whenever comparisons succeed; they do
not introduce another runtime allowance or replenish the caller's budget.

The checked laws establish occurrence permutation, exact multiplicities, record
property preservation, aligned-run growth and sorted output. Stability has the
stronger statement that filtering the input and output for any one key yields
the same ordered subsequence of whole records. This requires successful
comparisons to agree with the pure key order; non-strict order soundness alone
does not establish stable ties.

These generic laws still require instantiation with the complete neutral
receipt comparison and concrete byte-comparison charges. Canonical sorted output also does
not imply that comparison work is invariant under permutations of the incoming
roster; the public accounting contract must state its actual guarantee.

The [record-movement model](../../formal/rocq/runtime_grammar/theories/SemanticResultPermutation.v)
connects a successful merge of occurrence indices directly to exact placement
of the original records. For an input of length $`n`$, the scratch array first
receives `destination[order[d]] := d`. The sentinel is `n`, outside the valid
index range; the model proves that each next assignment targets a still
unassigned slot when `order` is a permutation of those indices.

During movement, `destination[p]` means the desired destination of the record
currently at position `p`. It is not a permanently unchanged inverse map.
Each swap exchanges the whole record and its destination entry together,
preserving the invariant

```math
\operatorname{values}[p]
= \operatorname{original}[\operatorname{order}[\operatorname{destination}[p]]].
```

Swapping position `i` with `destination[i]` fixes the target position without
disturbing any already fixed position. The number of misplaced records strictly
decreases. The checked loop therefore performs at most $`n`$ swaps, and its final
record at position `d` is exactly `original[order[d]]`. The model's fuel also
counts cursor advances, giving a sufficient $`2n`$ specification bound; this
ghost bound need not be computed or stored by production Rust.

Both arrays are modeled by finite pointwise views, so no functional-extensionality
axiom, cloning of records, or equality decision on process terms is used.
The composition theorem applies to the merge model's actual output permutation,
not an unrelated ideal sorting function. Concrete fallible allocations,
precharges, array operations and receipt comparisons still require implementation
correspondence and focused tests; the model alone does not certify them.

The [charged-chunk model](../../formal/rocq/runtime_grammar/theories/SemanticChunkComparison.v)
refines the standard-library `list_compare` operation instead of defining a
new lexicographic order. It reserves one entry visit, then charges each bounded
chunk of the common prefix before comparing that chunk. An unequal chunk
decides the result; equal chunks advance both cursors. If an input ends, the
remaining length determines the order. Production code can borrow the byte
slices without constructing a key or copying receipt payloads.

Successful comparisons equal the standard-library result. Refused entry and
chunk charges retain the state returned by the charging operation rather than
returning an empty answer or an equal comparison. Any state property preserved
by each charge is preserved through the entire traversal, including failures.
For positive chunk widths, the common-prefix length provides sufficient
specification fuel whenever charges succeed. These nine theorem checks passed
compilation and separate kernel verification; concrete budget arithmetic and
the receipt-field comparison remain distinct instantiations.

The [complete receipt-order model](../../formal/rocq/runtime_grammar/theories/SemanticReceiptOrder.v)
instantiates that order with the existing receipt schema. It compares output
bytes first, then the complete 13-field receipt tuple. Scalars use numeric order;
byte strings and evidence rosters use lexicographic order, with length deciding
only after an equal common prefix. Premise and resource tags select their
ordered variant payloads. Opcode and effect-class numbers come from the existing
wire encoder, whose checked decoder inverses establish tag-key injectivity.

Its proof-only products and tagged sums retain the existing receipt types.
Small [comparison adapters](../../formal/rocq/runtime_grammar/theories/SemanticComparisonLaws.v)
reuse standard-library list-order laws and the established lexicographic
composition proof. No encoded `Par` comparison, nested evidence sorting, receipt
deduplication, transient graph identity or arbitrary attached-term comparison
participates in this order.

Comparator equality is exactly complete receipt equality. Combined with the
checked merge algorithm, two successful faithful sorts of the same receipt
multiset produce identical neutral receipt sequences. This does not assert
equality of their final comparison states or usage counters. The concrete model's
12 printed theorem contexts and the adapters' seven contexts were closed after
compilation and separate kernel checks.

The [Rust ordering implementation](../../rholang-runtime/src/semantic_wire/ordering.rs)
compares borrowed fields directly in that order. Premise, opcode and effect tags
come from the receipt encoder's shared mappings. Every variable-length roster
uses an iterative cursor; the finite receipt schema bounds the nesting of
comparison calls. No reflected term is cloned, encoded or compared as a key.
The implementation uses the following logical schedule, where $`n`$ denotes
the number of complete result records and $`m`$ the size of a byte chunk.

| Operation | Logical work | Logical payload reservation |
|---|---|---|
| Scalar or variant-tag comparison | One visit | None |
| Byte comparison entry | One visit | None |
| Common-prefix byte chunk, at most 65,536 bytes per side | $`2m`$ visits, before inspection | None |
| Roster comparison entry | One visit, followed by child comparisons | None |
| Two scratch vectors and initial indices | $`n`$ writes | $`32+16n`$ bytes |
| Each bottom-up merge pass | $`n`$ writes, plus comparisons | None beyond reserved scratch |
| Inverse-permutation fill and assignment | $`2n`$ writes | Reuses the second scratch vector |
| Whole-record permutation | $`4n`$ prepaid loop-test and swap allowance | None |

Both scratch allocations are fallible and preceded by checked logical
reservations. The movement allowance covers at most $`n`$ swaps and $`n`$
cursor advances, including both the result-record swap and the corresponding
index swap. Zero-work cancellation checks run throughout movement. Scalar work
fields in a receipt remain data: their numeric values are not recharged as
execution. These logical reservations do not claim to measure allocator
capacity, physical memory or protobuf size.

Comparison or allocation refusal leaves the original result order unchanged.
Cancellation during movement may leave a permutation of the private reply,
but preserves every complete term/receipt pair. The eventual wire caller must
discard the entire private reply on any error; no partially ordered prefix is
publishable. This caller integration remains required.

The [focused correspondence tests](../../rholang-runtime/src/semantic_wire/ordering/tests.rs)
compare against independently constructed wire-level keys for 483 valid
single-field or roster mutations, explicitly covering all 13 receipt fields,
and all pairings of the 60 effect/opcode/resource combinations. They also check
stable duplicate preservation relative to each shuffled or reversed input,
identical canonical receipt sequences across those input permutations,
whole-record pairing, exact and one-less budgets, every cancellation checkpoint,
second-chunk refusal with retained prior charges, malformed permutation refusal,
chunk boundaries, 20,000-element proof rosters and 4,097-result sorting on a
128 KiB thread stack. The combined 16-test scalar/receipt/ordering suite passed locally.
This establishes focused Rust correspondence evidence, not a proof of the
entire Rust program or completion of the system-process request/reply API.

## Guarded host publication contract

The typed service's final authorization does not yet authorize an actual
RSpace reply: the system-contract producer returns a future, and storage is
changed only when that future runs. The host integration therefore requires
a synchronous, one-shot commit callback after asynchronous channel locking
and candidate preparation. The callback must enclose the existing produce
counter, event-log, store, COMM and replay-binding mutations. The authority
guard is released before observer notification and receiver dispatch. A
refused callback must not run any of those mutations.

The [publication control model](../../formal/rocq/runtime_grammar/theories/GuardedReplyPublication.v)
uses the existing installed-authority definition and a finite phase machine:
preparation, authority acquisition, mutation, release, observer invocation,
and receiver invocation, with a separate refusal state. Its mutation function
is universally quantified, not assumed correct. Consequently the refusal and
at-most-once laws apply to all modeled storage, continuation, join, log,
counter, replay and random-state projections. Successful publication applies
exactly the supplied mutation; this alone does not prove that mutation's COMM
semantics. The concrete Rust implementation and correspondence tests remain
required before this host integration is complete.

Replay preparation must read the count which the pending produce would create
without incrementing shared state prematurely. A read-only overlay increments
every lookup of that same produce identity, including repeated occurrences,
unless the produce is persistent. The model proves that the overlay and the
postcommit counter give identical exact repeat-count eligibility tests.

The implementation must retain the existing distinction between the play
event log and replay reporting callbacks. Reporting and step-observer callbacks
run after the guarded mutation; they cannot be silently moved under the
authority lock or mistaken for a second evaluator. A callback may revoke the
handle after publication without undoing the committed reply. These control
laws do not prove callback termination, rollback of later receiver effects,
lock-library correctness, machine-integer overflow behavior or atomicity
against unrelated RSpace readers. They establish the required boundary with
respect to installed-authority revocation.

RSpace's lazy read caches are not the logical storage projection: a cold read
may cache an empty channel without creating a message or changing the committed
root. Its soft checkpoint API also drains the event log and produce counters;
it is not a passive observation. Refusal tests restore those observations,
compare populated cache projections and counters, and separately check that a
cold refusal leaves the complete committed root unchanged.

The generic host guard is trusted Rust code. It must invoke the one-shot
callback exactly once on success, and never on refusal, while holding its
authority protection. A guard which calls the callback and subsequently
returns an error violates that contract: the host reports a distinct protocol
violation, not an atomic refusal. The callback cannot be sandboxed by an
in-process trait. The installed-language implementation must use the actual
installed-table authorization scope; the trait alone does not establish it.

`InstalledSemanticPublication` supplies that concrete implementation. It moves
the already resolved sealed handle and selected required-right roster into a
guard referencing the same installed table. Both the typed service commit and
the host callback reuse `with_authorized_all`; no authorization lease or cached
Boolean is created. A host refusal maps to `ProduceCommitDenied` without invoking
the mutation. Preparing or retaining this guard neither holds the table lock nor
grants additional rights.

The focused correspondence tests exercise the concrete guard with real matched
and unmatched RSpace publication, including revocation after the future is
created but before it is polled. They also reject a handle with only the
operation right when reflection is required, reject an identical language's
foreign table, and allow revocation after a successful commit. The 19-test
semantic-service run and seven-test wrapper run passed locally. These checks
cover this publication adapter, not by themselves the wire encoding and installed
system-process composition described below. They do not establish the public
node frontend or practical Regex application.

### Owned contract-call transport

The [owned contract-call model](../../formal/rocq/runtime_grammar/theories/OwnedContractCall.v)
checks the prerequisite transport extraction: exactly one outer message is
accepted, every request field and the caller's random state is retained, and
the split has an exact inverse on accepted arguments. Binding the final guard
does not acquire authority; publication still executes the existing guarded
host machine with the live authority at the actual mutation boundary. The eight
theorem contexts are closed and separately kernel-checked. Opaque term values
in this model do not establish Rust buffer ownership or freedom from backend
copies; allocation-identity tests and source correspondence cover the owned
glue separately. Incoming replay metadata returned by the split is distinct
from the space's replay state used during actual dispatch.

### Retaining authority across negative outcomes

The [preparation-context model](../../formal/rocq/runtime_grammar/theories/SemanticPreparationContext.v)
separates the operation's result from its retained publication context. Exact
selection determines the complete required-right roster. If selection or full
authorization fails, no publication context exists. Once full authorization
succeeds, the context retains that handle and roster before any fallible
matcher restoration, semantic execution, receipt validation, or reflection.
Every later outcome retains the same context and final usage, including
Refuted, Undetermined, and preparation errors. No negative result acquires
authority merely by having a diagnostic code.

The typed projection preserves the existing service's success/error and usage
behavior. The richer report additionally allows the wire caller to guard
negative publication through the same host mutation boundary as success.
The eight closed, separately kernel-checked theorems reuse the guarded host
machine: missing context cannot invoke it; retained context always rechecks
the complete rights; late revocation refuses publication without mutation.
The model abstracts the fallible semantic pipeline rather than proving its
algorithm, allocator, or lock implementation. Rust correspondence must retain
the context before restoration and carry the budget's final remainder on
both successful and failing exits, without rerunning the kernel.

The service now implements this separation. It moves the selected rights and
resolved handle into the retained context immediately after full authorization,
then restores the matcher from that exact authorized owner. Its typed commit
reauthorizes successful results only, preserving existing typed errors and
usage. The 22-test semantic-service suite passes, including exact-prefix
failure before matcher setup, absent context before full authorization, real
Refuted and Undetermined Regex judgments, and revocation of a retained negative
reply guard. This is preparation evidence; wire publication still requires
the retained context to be passed to the actual owned producer.

### Prepaid reply completion

The [reply-completion model](../../formal/rocq/runtime_grammar/theories/SemanticReplyCompletion.v)
specifies the numeric version-1 envelope `[1, status, body, usage]`. The status
is derived from the same body constructor that determines whether success is
permitted: 0 is Proven, 1 Refuted, 2 Undetermined, and 3 Error. Negative bodies
contain exactly `[domain, code]`, with bounded host-defined codes rather than
caller-controlled diagnostic strings. Successful bodies are prepared and
charged separately; this model treats them as opaque values.

Usage is `[total_work, kernel_work_option, limits_option, remaining_payload]`.
An absent option is `[0]`; a present option is `[1, value]`. The limits value
contains eleven unsigned integers, in order: work, normalization steps,
outputs, frontier, proofs, proof nodes, term nodes, term bytes, output nodes,
output bytes, and boundary payload bytes. The model checks exact decoding
inverses for these structures. Work values are logical accounting, not semantic
resource grades or evidence of host funding settlement.

The completion permit is prepaid so that a bounded failure can still be
reported after execution exhausts its remaining budget. Its reservation is
derived from the existing scalar and tuple encoding schedule:

| Encoded metadata | Maximum logical work | Maximum logical payload bytes |
| --- | ---: | ---: |
| Eleven limits | 111 | 379 |
| Four-field usage, both options present | 146 | 598 |
| Complete negative reply, including usage | 152 | 742 |

The reservation covers either scalar width. Fixed protocol tags use the small
integer encoding; the Rust correspondence must enforce the finite code policy.
Logical payload reservations are not physical memory measurements.

Completion follows this sequence: reserve both quotas against the cumulative
prefix; execute and encode the success body under the remaining allowances;
take the final usage snapshot; consume the permit once to encode the envelope;
then publish through the independently retained authority guard. The local
encoder spends prepaid credit without charging the cumulative counters again
or refunding unused reservation. Failed encoding must also consume the Rust
permit, with no retry credit. Observed cancellation remains sticky and cannot
produce a Proven envelope. Tightened limits must retain checked prefix
subtraction, and final completion checks both cumulative ceilings.

All twelve reported theorem contexts are closed and separately kernel-checked.
They establish metadata inverses, reservation bounds, successful one-shot
completion, unchanged cumulative usage, and rejection of cancelled success or
overdrawn completion. They do not establish semantic correctness, authority,
success-body accounting, physical allocation bounds, or complete Rust
implementation correctness; those require their separate models and concrete
correspondence tests. The wire-service integration remains a separate gate.

The [Rust completion encoder](../../rholang-runtime/src/semantic_wire/completion.rs)
reuses the receipt encoder's scalar and exact-list helpers. Its private permit
is consumed by value, including on failure. The final effective limits are
checked for attenuation from the reservation ceilings and supply both the
reported limits and the remaining-payload check. Cancellation is recorded by
one sticky callback wrapper; negative diagnostics can use the prepaid credit,
but a cancelled success is refused even at the final completion checkpoint.
The successful body must already be closed, prepared, and charged. Moving it
does not traverse or clone its subtree.

Eight focused completion tests pass within the 32-test semantic-wire suite.
They cover metadata order and width, exact quotas and one-less refusals,
malformed options, nonliteral envelopes, all status/domain combinations,
counter resets and amplified limits, cancellation at every completion poll,
and moving or dropping 20,000 nested result nodes on a 128 KiB stack. These
checks establish the local encoder correspondence. Same-request usage and
authority coupling require the installed system-process checks described below.

## Owned request and complete result transport

The [owned request decoder](../../rholang-runtime/src/semantic_wire/request.rs)
accepts one ordinary list datum with exactly six fields:

```text
[1, opaque_handle, declaration_name, structural_input, limits11, reply]
```

The endpoint determines whether the declaration names an action or an
observation. The version and limits use the existing canonical unsigned scalar
codec. The declaration name must be one closed string literal. Validation
borrows these fields; extraction then moves the six values into a fixed array.
The decoder neither parses guest source nor traverses or clones the structural
input and reply subtrees. Handle authorization and input admission belong to
the installed service, not this envelope check. Request decoding contributes to
the cumulative work prefix and allocates no new logical payload.

The [result encoder](../../rholang-runtime/src/semantic_wire/receipt.rs)
consumes fresh service results as a list of pairs:

```text
[[structural_term, complete_receipt13], ...]
```

It first uses the existing complete-receipt stable sorter, moving whole records.
It then iteratively materializes each pair through the existing bounded tuple
and receipt encoders. Terms are already admitted, reflected and charged by the
service; their outer closure metadata is checked before moving them unchanged.
Every receipt field and repeated result occurrence remains present. The encoder
does not re-charge kernel work recorded in receipts, validate external evidence,
or confer authority. Any encoding or sorting failure drops the entire private
result rather than returning a successful prefix.

Four additional theorems in the
[receipt wire model](../../formal/rocq/runtime_grammar/theories/SemanticReceiptWire.v)
compose its existing receipt inverse with the exact two-field pair and roster
decoders. They prove lossless pairing, order and multiplicity of the post-sort
roster for arbitrary opaque term values. The existing sorter laws separately
establish whole-record permutation and canonical order; the composed encoder is
not an inverse for arbitrary original input order. All seventeen reported
contexts are closed, with a separate
kernel check. These laws do not establish term closure, term/receipt semantic
binding, Rust allocation safety or publication; those remain the installed
service's and host's separate obligations.

The 32-test semantic-wire suite includes four request and four result-envelope
tests. These cover exact scalar/list shapes, preserved input/reply/term buffers,
complete receipt roundtrips, duplicate retention, exact quotas and one-less
refusals, every cancellation checkpoint, and moving/dropping 20,000 nested
nodes on a 128 KiB stack. The result tests reuse the receipt fixture containing
all premise forms and maximum-width work values. These local tests do not yet
establish the complete system-process or public-node integration.

## Installed semantic system processes

The [semantic endpoint composition](../../rholang-runtime/src/semantic_service/wire.rs)
registers two processes in the same `RholangLanguageRuntime` used for installation,
construction and pattern preparation:

| URI | Request declaration name | Band index |
| --- | --- | ---: |
| `rho:mettail:flt:reduce` | Exact installed action name | 0 |
| `rho:mettail:flt:observe` | Exact installed observation name | 1 |

Both consume the six-field request above. Their shared system-process band is
10, with channel tag `0xF9` and allocation identity
`mettail-language-semantic/1`. That identity is an internal versioned allocator
input, not a capability or the numeric request version. The existing allocator
supplies channels and body references; no second allocator is introduced.
The endpoints are deterministic operations, outside the host's nondeterministic
operation set. Existing installation, parser, FLT and theorem-channel identifiers
retain their values and order; these two definitions are appended.

The complete reply is one datum:

```text
[1, status, body, [total_work, kernel_option, effective_limits_option, remaining_payload]]
```

Status 0 is Proven and carries the complete sorted result-pair roster. Status 1
is Refuted, status 2 is Undetermined, and status 3 is Error; these three carry
exactly `[domain, code]`. An absent option is `[0]`; a present option is
`[1, value]`. Effective limits use the eleven-field order specified above.
Undetermined is not a Boolean conclusion and must not be negated into success.

Diagnostics use fixed host-assigned integers, never untrusted error text or
debug formatting. The version-one assignments are:

| Domain | Codes in order, starting at zero | Status |
| --- | --- | --- |
| 0: wire | Shape, IntegerRange, NonCanonicalInteger | Error |
| 1: access | WrongRegistry, UnknownLanguage, StaleHandle, Revoked, MissingRight, AmplifiedHandle, EpochExhausted, Poisoned | Error |
| 2: service | InvalidHandleShape, UnknownHandle, MissingSemanticImage, UnknownAction, UnknownObservation, InvalidSelection, InvalidEvidence | Error |
| 3: kernel refutation | RequestRejected, NoTransition, PremiseRefuted, StuckNonterminal, NormalizationDeterminismClaimViolated | Refuted |
| 3: kernel uncertainty | WorkBudgetExhausted, Cancelled, InvalidImageEvidence, PremiseEvaluationUnavailable, ResourceGradeUnavailable, InputLimitExceeded, OutputLimitExceeded, EGraphNodeBudgetExhausted, AllocationFailed, FrontierLimitExceeded, ProofLimitExceeded, NormalizationStepLimitExceeded, NormalizationCycleDetected | Undetermined |
| 4: boundary | UnknownConstructor, ConflictingConstructorLabel, UnknownHole, InvalidHoleId, HoleCategoryConflict, MissingHole, InvalidMapEntry, WorkLimit, PayloadByteLimit, Cancelled, AllocationFailed, InvalidFingerprint | Codes 7–10: Undetermined; others: Error |
| 5: restoration | IdentifierOverflow, Automaton, Allocation | Error |

The status disambiguates the two kernel code rosters. Diagnostic details such
as a constructor label or missing right are deliberately not serialized; full
successful receipts are not truncated by this diagnostic policy.

Preparation follows the existing verified resource and authority contracts:

1. Borrow-decode the request under host ceilings, preserving the consumed prefix.
2. Meet host and requested limits and subtract prior payload consumption with
   checked arithmetic.
3. Prepay the completion envelope, singleton producer payload, and publication
   reference descriptor **before** semantic execution. Together these reserve
   154 work units and 782 logical payload bytes, in addition to header decoding.
4. Invoke the existing installed service with that exact prefix and one sticky
   cancellation source. The service adds installed execution ceilings and
   retains the selected handle and every required right before fallible setup.
5. Continue from the service's returned cumulative work and remaining payload.
   Sort and encode all successful pairs, or retain a finite negative outcome.
   Encoding failure discards all private successful output without refunding
   consumed work or granting a fresh allowance.
6. Snapshot the final counters and consume the one-shot completion permit.
   The already-reserved producer vector receives the completed datum without
   reallocating. Reference materialization consumes its prepaid descriptor;
   no further logical charge can prevent a bounded negative completion.
7. Move payload and reply channel into the existing owned producer, supplying
   the retained full-right guard. Its actual RSpace mutation rechecks live
   authority. Encoding and receiver dispatch do not run under that authority lock.

Missing full publication context yields a bounded outer interpreter error, not
an unguarded semantic reply. A worker failure or inability to form a valid
completion also aborts without publishing a successful prefix. The handler
awaits the producer and returns its downstream dispatch result unchanged; it
does not clone the reply to synthesize another return value.

The host's `ProcessContext` currently has no cancellation callback. The reusable
preparation boundary accepts one for callers and verification, while the
registered endpoint enforces deterministic work ceilings without claiming an
unavailable host cancellation integration. Logical payload reservations are
not physical RSS limits, allocator guarantees, semantic resource grades, or
host funding settlement. Publication authorization is distinct from both
rewrite premises and Rholang `where` predicates.

The combined semantic service and wire suite passes 68 tests, including six
wire-composition tests.
The exact-prefix test checks service work plus result encoding plus header work
plus the 154-unit reservation, and the corresponding 782-byte decrement. The
one-less tests establish that result-encoding exhaustion still produces a
bounded Undetermined envelope. Other tests cover complete receipts, declared
observe routing, cancellation, missing authority, late revocation, and actual
registered endpoint execution.

The [inline application test](../../rholang-runtime/src/semantic_service/wire/tests.rs)
parses a complete Rholang process containing the Greg/Mike Module/Theory fixture,
installs it through `rho:mettail:install`, obtains its scoped handle, constructs
`language:Pattern`-qualified guest syntax, invokes reduce or declared observe,
and destructures the complete reply in a waiting Rholang process. It checks the
returned `PConcat` constructor and complete receipt. A second application
changes only the `ExpandPlus` rule's right-hand side to `PAlt`; the same endpoint
then returns `PAlt` with changed full-language, theory and semantic-image
commitments. The receipt's `language_fingerprint` is the full LanguageCore
commitment, not the separate syntax-only grammar fingerprint. This perturbation
checks dependence on the installed GSLT rather than a fixed handler result.

Run this focused application witness from the implementation repository with
the same serial resource cap used for the broader suite:

```sh
systemd-run --user --scope -p MemoryMax=8G -p MemoryHigh=7G -p MemorySwapMax=0 \
  env CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
  cargo test --locked --offline -p rholang-runtime --no-default-features \
  --features rholang-runtime,bench-naive-baseline --lib \
  semantic_service_wire_inline -- --test-threads=1
```

This establishes the in-memory runtime/library integration. It does not yet
establish public-node activation, practical regex matching/search/replacement,
or FLT predicates in `where` clauses; those remain explicit demo requirements.

## Regex application handoff

The [practical Regex application contract](regex-gslt-application-contract.md)
fixes the required operation forms, Unicode offsets, replacements, direct FLT
predicates in `where`, and public-node acceptance cases. It distinguishes the
existing service from the remaining application and guard integration.

The adapter's signature is language-neutral: any enrolled constructor may have
any finite ordered domain of supported Syntax sorts. The current
[inline Regex fixture](../../rholang-runtime/tests/fixtures/regex_extension.rho)
exercises its actual parser and the `ExpandPlus`, `ExpandOptional` and
`RemoveGroup` kernel rules. It does not yet implement full matching, search or
replacement. The following roster relates that fixture and the existing
[Regex signature model](../../formal/rocq/runtime_grammar/theories/RegexGsltSyntax.v)
to the same structural boundary. Sort names below denote semantic sorts, not
equal-numbered grammar categories.

| Constructors | Ordered domain | Result | Concrete status |
|---|---|---|---|
| `PFail`, `PEpsilon`, `PAny` | Empty | Pattern | Installed fixture |
| `PLiteral` | Scalar | Pattern | Installed fixture; native String child |
| `PGroup`, `PStar`, `PPlus`, `POptional` | Pattern | Pattern | Installed fixture; the abstract model erases grouping |
| `PAlt`, `PConcat` | Pattern, Pattern | Pattern | Installed fixture |
| `PRepeat` | Pattern, Nat, Nat | Pattern | Signature model; application declaration remains required |
| `MatchScan` | Pattern, Text | MatchState | Signature model |
| `SearchScan` | Pattern, Text, Nat | SearchState | Signature model |
| `NoMatch`; `MatchFound` | Empty; Nat, Nat, Text | MatchResult | Signature model |
| `ReplacementEmpty`, `ReplacementWhole` | Empty | ReplacementTemplate | Signature model |
| `ReplacementLiteral`; `ReplacementAppend` | Text; ReplacementTemplate, ReplacementTemplate | ReplacementTemplate | Signature model |
| `OutputPattern`, `OutputBool`, `OutputMatch`, `OutputText` | Pattern; Bool; MatchResult; Text, respectively | Output | Signature model |
| `OutputUndetermined` | Empty | Output | Signature model; not permission to turn service exhaustion into success |
| `TEmpty`; `TCons` | Empty; Scalar, Text | Text | Abstract constructor presentation, not the native String encoding |
| `NZero`; `NSucc` | Empty; Nat | Nat | Abstract constructor presentation, not the native Integer encoding |
| `BFalse`, `BTrue` | Empty | Bool | Ordinary constructors, distinct from native Boolean atoms |

Each concrete application declaration must supply the installed grammar pair
and exact semantic signature used by the index. A semantic-only list used
internally by `Utf8ConcatMany` need not cross the FLT boundary. If an application
exposes that list, a binder, or another unsupported form as an input or result,
the missing boundary support is a blocker; the application must not discard it
to fit this adapter.

The native-carrier and abstract Regex models have separate obligations. In the
[matching model](../../formal/rocq/runtime_grammar/theories/RegexGsltMatch.v),
Scalar is an abstract natural and Text is a list of scalars. Its Unicode
realization must map valid scalar values to their UTF-8 encoding, and Text to
the concatenation of those encodings. The native String codec preserves those
bytes but does not prove this semantic realization or the scalar/byte-position
correspondence required by search. Likewise, the natural-number embedding into
signed 128-bit Integer is partial, with domain $`0\leq n\leq 2^{127}-1`$.
The generic codec intentionally preserves negative Integers too; a sort named
`Nat` does not add an undeclared nonnegativity predicate. Application rules and
checked intrinsics must establish the numeric and UTF-8 premises, not infer them
from the sort's spelling. Native Boolean atoms and `BFalse`/`BTrue` are also
different representations unless the theory explicitly relates them.

The practical application must connect these realizations to the proved
matching/search/[replacement semantics](../../formal/rocq/runtime_grammar/theories/RegexGsltReplace.v).
That is an application refinement, not another decoder or evaluator in the
structural adapter. Request, continuation and `Done(result)` wrappers must be
ordinary declared positional constructors of the application's computation
sort. Endomorphic normalization terminates at a declared terminal wrapper; a
qualified FLT pattern then extracts its result. No terminal outgoing rewrite
or same-sort cross-codomain normalization is invented at this boundary.

The installed adapter tests establish concrete kernel/FLT round trips for the
three existing fixture actions, exact literal preservation, ordered repeated
occurrences, malformed-input refusal, cumulative allowances and deep-stack
cleanup. Separate typed-service tests cover qualified execution, complete receipt
preparation, exact/one-less limits, missing action rights, wrong owner/sort,
cancellation and revocation immediately before final publication. Neither suite
establishes the additional matching/replacement application declarations, the
Rholang wire API or the actual MeTTaIL-only node entrypoint; those retain their
separate implementation and end-to-end gates.
