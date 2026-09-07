# Installed FLT semantic judgments

## Boundary and implementation status

A foreign-language term (FLT) is scoped structural syntax, not an authority
token. A semantic request names an opaque installed-language handle and an
action or declared observation of that language. Its input has already passed
through the language-qualified parser/template path. Execution must not render
the term and parse it again.

The [dispatch model](../../formal/rocq/runtime_grammar/theories/InstalledFltJudgments.v)
specifies the missing installed-service boundary before its Rust implementation.
The existing semantic kernel and installation services are implemented; the
reflected-term adapter, qualified reduce/observe service and service wire are
not yet connected. This document is their implementation contract, not a claim
that the node demonstration is runnable.

## Reuse and representation

| Responsibility | Existing implementation | Required connection |
|---|---|---|
| Resolve authority | `RholangLanguageRuntime::resolve` and `InstalledLanguageTable::authorize_all` | Resolve only the caller's opaque handle and check every operation/action right together |
| Parse and fill syntax | `dynamic_syntax_to_ground_term` and `reflect_flt_construction` | Consume the already reflected value; preserve structural holes and their scope |
| Check reflected syntax | `DynamicSyntaxAdmission` | Factor its structural recognition into a checked inverse with distinct rejection and exhaustion |
| Represent theory operators | `theory_operator_to_machine` | Resolve constructor bindings and literal carriers from the installed theory |
| Admit semantic input | `SemanticTransitionInput::admit` | Supply the typed structural projection and explicit limits |
| Execute an action | `SemanticTransitionMatcher::execute_action` | Invoke the existing one-step or normalization policy, with the exact image used to restore the matcher |
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

## Private execution and complete publication

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

For each resource dimension, the effective limit is the intersection of the
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

`ProvenSemanticTransitions::work` is aggregate request work. Each transition's
receipt repeats that aggregate. Charge it once, then add boundary conversion
and encoding work; summing all receipt work fields would multiply the charge
by the number of results. Semantic input admission already included in the
kernel aggregate must not also be counted as boundary decoding.

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
The modeled receipt records do not yet represent every concrete intrinsic or
normalization receipt field. Their complete wire transport requires an explicit
correspondence proof, not an assertion that the abstract record is the wire ABI.

Run proof compilation and separate kernel checking one at a time under the
repository's resource policy: at most 1 GiB memory, no swap, and generated
proof artifacts under `target/`. Do not invoke the entire formal workspace to
recheck this bounded dependency slice.
