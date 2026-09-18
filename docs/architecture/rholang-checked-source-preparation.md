# Resource-checked Rholang source preparation

Source preparation consumes the syntax tree produced by the generated Rholang
parser. It does not parse source text again. Surface send forms expand into the
same core constructors used by ordinary lowering; an explicit reservation
policy controls when that existing work may run.

## Send expansion

`desugar_surface_sugar_node_preparing` contains the shared constructor match.
`SourceBuilder` supplies its copying, sharing, and allocation operations.
`Drive::desugar_head` repeatedly expands the head and retains each new result
in the existing arena. This loop does not add native call depth as the source
becomes deeper.

The two policies are selected at entry, not after an error:

- `Original` retains the unmetered internal behavior and never invokes the
  reservation callback. This includes the existing query-receive expansion.
- `Checked` is used after public source-profile admission. It reserves logical
  work and retention before the associated operation and propagates refusal
  without retrying under `Original`. Query receives are outside that profile
  and are rejected by admission before preparation.

The policy changes resource admission, not arity or language semantics:

| Source form | Core representation |
| --- | --- |
| Empty send | One payload containing an empty list |
| Polyadic send | One payload containing the ordered argument list |
| Monadic send | Its original single payload, without list wrapping |
| Nil-quoted channel | The quote of `PZero` |
| Name-shaped quoted channel | The quote of the existing name-to-process image |
| Process-shaped quoted channel | A shared reference to the quoted process |
| Persistent send | The corresponding persistent core constructor |

This table describes structural expansion. It does not evaluate payloads or
perform a communication.

## Reservation and copying

The builder reserves the vector header and checked element count before
allocating a polyadic roster. Each source copy uses the existing generated
`CheckedIterativeBinding` worker with `BindingOperation::Clone`. That worker
owns traversal and cleanup accounting; the builder does not introduce another
tree-copy algorithm. Iteration is charged before each advance, including the
terminal advance. Arc allocation, reference sharing, and arena retention have
their own reservations before those operations occur.

An FLT is a foreign-language term. Copying an `Arc<FltNode>` shares that same
node: its pointer identity and scoped selector are preserved. Opening or
closing bindings is a different operation and is not performed by these
copying adapters. This distinction matters when a later body pass locates a
particular FLT occurrence for replacement.

Reservations count logical work, records, and owned bytes where the underlying
copy worker requires them. A record is not an allocator-size estimate. These
charges do not establish physical-memory, CPU-time, or allocator-failure bounds.
Normal error cleanup is part of the checked path; panic recovery is a separate
contract.

## Collection-key inspection and native stack frames

Copying a parallel process reconstructs its `HashBag`, the collection that
retains process multiplicities. Its checked reconstruction inspects the work
needed to hash and compare keys before admitting those native operations. A
map used as a key also requires inspection of its key-ordering work. Sharing
an `Arc<Map>` by itself does not exercise that reconstruction path.

An explicit task stack prevents traversal depth from becoming native call
depth, but a single generated function can still have an oversized native
stack frame. Contribution inspectors therefore select a non-inlined handler
for one constructor instead of retaining every constructor's temporaries in
one large function. Each handler contains its original operation and schedules
children on the existing task stack. The selector does not traverse children.

Selection and invocation reserve three work units and one four-unit retention
record before entering the handler. This charge pays the inspection itself;
it is neither multiplied by the comparison repetition factor nor added to the
receipt for future native execution. Ordinary and checked comparison/hash
execution retain their original operations and receipts.

The `CheckedBindingTaskDispatch` model preserves the complete selected
handler outcome, including partial state and errors. Exact generated-arm and
selector tests check its code-generation premise. Native compilation,
collection-copy tests on a small stack, and emitted-frame measurements are
separate checks: the model alone does not establish a physical stack bound.

## Binder-local body search

The body finder uses one shared `Proc`/`Name`/`Emit` worklist for original and
checked preparation. `Emit` occurs after the node's children, so the first
selected foreign-language term (FLT) is the first eligible postorder
occurrence, not the first distinct pointer or printed term. Send expansion
precedes scheduling. Quoted channels precede send payloads; list elements and
method arguments retain source order. Nested `new` and receive bodies, and
receive patterns, remain opaque to this binder-local search.

Parallel processes use the existing paid `HashBag` entry visitor, expanding
each stored multiplicity and skipping zero repetitions. Maps use the existing
paid entry visitor in insertion order, visiting each key before its value.
The shared paid task-batch reversal puts those occurrences on the last-in,
first-out worklist without reversing their eventual visit order. No key is
hashed, sorted, copied, or deduplicated by this scheduling operation.

Checked search reserves before creating its worklist, pushing and popping
tasks, advancing iterators, retaining expanded nodes, and projecting a result.
The terminal pop and iterator advances are included. A refusal returns the
original error without a search result or fallback; previously accepted
reservations stay spent. Pending tasks only borrow their source nodes.

FLT eligibility uses the original immutable `BoundEnv` identity map. A free
selector must resolve by moniker identity; matching diagnostic spellings or
FLT-hole names do not qualify it. A bound selector is not eligible at this
stage. Successful selection shares the original `Arc<FltNode>`, preserving
the pointer that the replacement pass will recognize.

Native identity lookup is admitted before the unchanged `get().copied()`.
The pinned scalar-hashing, equality, and probe models supply its finite work
allowance; no new dictionary or string comparison is introduced. The map's
clean construction invariant supplies its capacity bound. Empty maps take
the original no-hash shortcut. Checked arithmetic or reservation failure
precedes lookup. These are logical operation allowances, not exact CPU costs.

The negative fold search uses the same paid traversal. Held-fold constructors
are outside the current checked public source profile and are refused before
width evaluation. Internal original preparation retains its existing folds.

The replacement worklist uses the same child order and selects only the first
matching occurrence. Once replaced, later subtrees are copied without further
sugar expansion. Checked copies preserve FLT pointer identity. Each continuation
consumes its saved result-stack suffix after reserving that suffix's storage.
Reconstructed parallel processes sum colliding occurrence counts; reconstructed
maps retain the first equal key object and position but the last value. These
are the existing collection semantics, not a new deduplication policy.

Replacement reserves before copying, scheduling, allocating result slots, and
performing native collection insertion. Refusal returns no transformed body;
already accepted charges remain spent. The caller's local replacement flag is
not a published result and need not be rolled back after refusal.

## Receive preparation and lexical FLT captures

Receive rows borrow their original binds and optional guard. The checked
adapter reserves the ordered roster before allocation and polls before each
iterator advance. Monadic receive patterns retain the payload verbatim;
empty and polyadic receives use the existing list encoding. Pattern copying
uses the generated checked worker. Appending a pattern binder checks the
counter and reserves the copied identity and slot before mutating the state.

An FLT construction hole such as `${text:Text}` names a lexical value. Its
name is not a moniker identity, installed-language handle, or registry lookup.
The environment therefore keeps a separate construction-hole context:

- Source `new` bindings and ordinary receive bindings introduce named slots.
- FLT receive captures introduce slots in the same index space.
- Later source bindings shadow earlier names, using the existing reversed
  de-Bruijn index convention for joint receives.
- Generated construction-return binders shift existing indices but do not
  introduce names. Even an identically spelled user binding is not shadowed
  by an internal temporary.
- Ordinary process/name references and the FLT language selector retain their
  identity-based resolution. Construction aliases never participate in that
  lookup or confer language authority.

Positive FLT construction and qualified `where` predicates share this context.
A predicate is retained as a structural descriptor with its explicit selector
and capture coordinates. The ordinary guard worklist retains Boolean
connectives around those descriptors; it does not construct or evaluate the
guest term during lowering. Runtime predicate evaluation and the atomic
communication decision remain separate obligations of the shared language
service and matcher.

The context extension reuses the ordered insertion, shadowing, and shifted
outer-scope laws in `RholangSourceScope`. Context-copy admission includes the
additional owned entries and names. These laws establish lexical indices,
not a resource bound for descriptor encoding or semantic execution.

## Verification boundary

`RholangPreparationReservation` supplies the checked precharge, exact successful
operation, retained-budget-prefix, and ordered-roster laws. The adapters keep
the same constructor operations and instantiate those laws; the laws alone
are not a proof of all Rust execution.

The focused source tests compare all 17 send-sugar constructors with explicit
core syntax and compare normalized public output bytes. They exercise every
helper reservation cut, exact and insufficient allowances, unchanged borrowed
source, identity-preserving FLT copies, and public-path cancellation through
head retention and terminal inspection. Deep and wide cases additionally run
copying and normal refusal cleanup on 128 KiB stacks.

The body-search tests additionally check explicit postorder traces, original
Map pairs, repeated and zero-count parallel occurrences, FLT pointer identity,
opaque nested scopes, identity-only selector resolution, every reservation
cut, and deep traversal on a small stack. `RholangBodyFirstOccurrence`,
`SourceMapEntryVisit`, `NativeHashBagEntryVisit`, and `PaidTaskBatchReversal`
supply the corresponding order and occurrence laws. The selector adapter
reuses `AdmittedIdentityComparison` and the native probe/candidate bounds.

These adapters cover head expansion, body-site search and replacement, and the
stated receive roster and pattern-copy operations. Complete FLT request/descriptor
encoding and final interpreter-value construction have
separate resource obligations. Passing these focused tests must not be
presented as a bound on the whole prepared application.
