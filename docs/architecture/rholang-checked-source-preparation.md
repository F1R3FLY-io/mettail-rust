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

These adapters cover head expansion and its retained results. Body-site scans,
replacement, receive-pattern preparation, and final interpreter-value
construction have separate resource obligations. Passing the head-expansion
tests must not be presented as a bound on the whole prepared application.
