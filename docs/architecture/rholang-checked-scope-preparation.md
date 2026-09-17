# Checked lexical preparation in Rholang

Budgeted preparation opens Rholang scopes with the existing generated binding
worker and the caller's existing reservation budget. It does not change Rholang
syntax, create another parser, or replace the interpreter. This boundary covers
fresh binders, URI associations, descriptor construction and environment
derivation; it is not a certificate for the remaining preparation stages or
public-node activation.

## Entry policy

`SourcePreparation` is a private policy of the existing lowering worklist.
It is independent of `SourceAdmissionMode`, which controls name resolution.

| Entry | Scope preparation | Purpose |
|---|---|---|
| Existing unmetered lowering | `Original` | Preserve its existing supported families and Moniker behavior. |
| Internal storage-only checks | `Original` | Test worklist storage without claiming complete source admission. |
| Owned budgeted preparation, after the source-profile gate | `Checked` | Require paid opening and propagate every refusal. |

The policy is selected before traversal. A checked failure is never retried
through the original path. Both policies use the same lowering worklist and
environment representation. Budgeted source admission, opening, and lowering
share one budget; there is no reset between them.

## Fresh identities and lexical opening

A binder has a semantic identity and an optional diagnostic name. Names such as
`x` are not identities: distinct binders may have the same spelling.
`Scope::try_unbind` performs these steps:

1. Reserve the fresh roster's storage before allocating it.
2. Visit every original binder occurrence in order, including duplicates.
3. Reserve each name copy and call the existing `FreeVar::fresh` once for that
   occurrence, retaining its optional name.
4. Open the body at depth zero using that exact fresh roster through
   `CheckedIterativeBinding`.
5. Return the roster and opened body together.

The checked operation omits two pure temporary copies from Moniker's
`clone().unbind()` recipe: copying the original pattern before freshening and
copying the fresh pattern into a temporary lookup roster. It does not omit
freshening or opening. Nested bodies use the existing inherited-depth worker;
the outer opening starts at zero, not one.

Failure leaves the original scope unchanged. Previously issued fresh identities
and consumed budget are not rolled back. The existing Moniker allocator remains
responsible for freshness; the positional proofs do not replace that allocator
or assume that issued identities are numerically consecutive.

## Binding worklist and native stack

A pushdown automaton (PDA) stores unfinished traversal work explicitly. The
checked binding PDA retains source pointers, inherited scope state, destination
slots and child-slot ranges in its existing task vector. Children are scheduled
there, not visited by recursively calling the binding driver. Result slots retain
the constructed terms under the existing publication and cleanup protocol.

An explicit worklist alone does not establish native-stack safety. A compiler
can reserve one large native frame for a function containing many mutually
exclusive constructor bodies. Checked binding therefore isolates both dispatch
levels: the driver selects a task helper, and a visit helper selects a constructor
helper. Each selection produces a function pointer; its common call is outside
the selection match. Selected helpers retain separate, non-inlined frames and
execute the original arm. Existing assembly helpers remain separate too.

The traversal proceeds as follows:

1. Admit and pop the next task, retaining its original inherited scope state.
2. Admit task dispatch, select its helper, and call it once.
3. For a visit, admit constructor dispatch and call the selected constructor
   helper; for assembly, use the existing assembly operation.
4. Schedule children or publish the result using the existing paid operations.
5. Return to the driver; propagate any error through the existing cleanup path.

Each added selection stage reserves three work units and one retained record
before selecting or calling. Visits use both stages; assembly uses only the
task stage. A refusal at either stage invokes no selected handler. Successful
dispatch preserves the complete handler result, including partial private state
and the original error when a later operation refuses.

This structure keeps traversal call depth independent of input nesting and
separates constructor-local frames as the number of constructors grows. It does
not imply a universal byte bound for arbitrary Rust payloads, callback error
types or constructor arities. Actual generated-language tests on a small stack
and inspection of compiled native frames are separate obligations from the
semantic model. Ordinary `Clone` generation is not changed by this checked
dispatch refinement.

## URI associations

URI preparation retains the original validation sequence: open the scope, check
nonempty/equal binder and URI counts, validate each URI's backtick envelope and
nonempty contents, sort whole associations, reject duplicate URIs, and construct
the ordered outputs. Removing the already-parsed URI token's envelope is not
another textual grammar parse.

For example, sorting the source roster `[("z", b), ("a", a)]` must move binders
with their URIs:

| Original association | Sorted binder position | Emitted de Bruijn index |
|---|---|---|
| `("z", b)` | Second | `0` |
| `("a", a)` | First | `1` |

The body refers to the fresh binder identities, so ordering URI strings alone
would be incorrect. `try_sort_borrowed_by` carries references to whole pairs
through the existing stable bottom-up merge machine. Its private entry type is
generalized, but its guards, assignments, buffer swaps and equal-left selection
are unchanged. The typed interface does not reconstruct references from raw
pointers, clone source payloads, or drop source terms.

String comparisons use the existing checked native comparison interface and
the same reservation callback. Failed comparison or storage admission returns
an error; it is never converted into an ordering result.

## Descriptor and environment boundaries

`CheckedCallerImports::keys_with_reservation` copies every caller key in the
already validated canonical order. It does not copy the corresponding `Par`
values or reinterpret keys as lexical names. Copying those values into emitted
processes is a separate construction boundary.

`CheckedFreshDescriptor` remains the authority for layout, emitted-count and
arity validation. The adapter prepays borrowed inspection and the unchanged
string validator's comparison allowance before invoking it. Environment key
inspection, copying, slot shifts and retention reuse `EnvArena::derive`; the
scope adapter does not build another environment arena.

Reservation units describe logical work, retained records and owned byte
payloads, not allocator capacity, operating-system memory or elapsed time.
Native process-memory caps remain necessary when executing validation tools.

## Evidence and limits

| Obligation | Existing model or focused check |
|---|---|
| Fresh roster order, names, positions, and elimination of pure copies | [BinderPatternCopy.v](../../formal/rocq/rho_bridge/theories/BinderPatternCopy.v) |
| Exact depth-zero variable opening | [MonikerLeafOperations.v](../../formal/rocq/rho_bridge/theories/MonikerLeafOperations.v) |
| Nested inherited depth and body traversal | [RholangInheritedBindingFold.v](../../formal/rocq/rho_bridge/theories/RholangInheritedBindingFold.v) |
| Exact task and constructor dispatch, paid allowance and error-state preservation | [CheckedBindingTaskDispatch.v](../../formal/rocq/rho_bridge/theories/CheckedBindingTaskDispatch.v) |
| Stable whole-entry sort and native buffer lifecycle | [MergeSortPdaNativeOuter.v](../../formal/rocq/rho_bridge/theories/MergeSortPdaNativeOuter.v) and [AdmittedCollectionSortOwnership.v](../../formal/rocq/rho_bridge/theories/AdmittedCollectionSortOwnership.v) |
| Shared reservation and refusal | [RholangPreparationReservation.v](../../formal/rocq/rho_bridge/theories/RholangPreparationReservation.v) |
| Concrete identity, failure-cut and stable-sort behavior | Runtime checked-scope and collection-comparison unit tests |
| Actual generated bodies and normalized output bytes | `rholang_ast::preparation_scope::tests` |

Model proofs and Rust correspondence checks are distinct evidence. The models
do not prove arbitrary Rust callbacks, every language constructor, allocator
behavior, panic-unwind recovery, or the complete public execution path.
Integration tests cover nested shadowing, URI association and validation,
repeated scopes, nonempty caller contexts, exact and insufficient limits,
normal error cleanup, and generated-body opening on a small thread stack.
