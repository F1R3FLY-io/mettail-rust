# Rholang frontend admission contract

This contract defines checked source admission for the
[practical Regex application](regex-gslt-application-contract.md) and its
subsequent node-independent frontend. The first functional revision uses direct
composition; neutral extraction follows it. Neither path is claimed complete
by this document. Remaining language parity and self-hosting requirements stay
mandatory.

The source language remains the generated
[Rholang specification](../../languages/src/rholang.rs). The existing
[AST lowerer](../../rholang-runtime/src/rholang_ast.rs) supplies the structural
decisions and explicit `Job`/`Kont` worklist. The node's existing
`ProgramFrontend` and non-`Clone` `PreparedProgram` supply the host handoff.
Direct preparation wraps that same whole-body worklist with explicit Public
admission, caller imports, options, resolver, limits and failure-safe owned
side outputs. It does not introduce another parser, normalizer or evaluator.

## Direct composition and subsequent neutral extraction

The first revision prepares an owned normalized `Par` and its auxiliary fold
and guard descriptors. Only after all preparation checks succeed may the trusted
adapter package it in the existing `PreparedProgram`. That type is an ownership
handoff, not itself a certificate of valid source, authority or funding.
Failure publishes no artifact or auxiliary state. Public preparation never uses
Harness unresolved-variable conventions or converts ambiguity into parallelism.

The component dependency direction is:

```text
Node application -> MeTTaIL bridge -> Node core libraries
Node application -----------------> Node core libraries
```

The application supplies the existing shared language runtime and FLT matcher;
the core interpreter, models, RSpace and funding libraries cannot depend back on
MeTTaIL or the application. The node's resolved Cargo package-graph gate checks
normal and build dependencies, including renamed dependencies and proc macros,
with composition features enabled. It rejects forbidden reachability and cycles.
The [component proof](../../formal/rocq/rho_bridge/theories/BridgeInertness.v)
establishes rank-decreasing cross-layer edges and core independence. Actual
package identity, feature selection and within-layer acyclicity remain the
executable gate's obligations, not conclusions of that abstract proof.

Neutral carrier migration, graph replay and neutral emission are subsequent
milestone work. The neutral envelope and graph-specific laws below specify that
required final boundary; a direct `Par` is deliberately not called neutral.
Source semantics, caller identity, stack safety, bounded preparation, authority,
FLT `where` predicates and atomic funded publication apply to the direct path
too. Deferring graph replay does not waive the cost of direct construction or
cleanup.

## Inputs and ownership

The frontend receives explicit inputs, not ambient process state:

| Input | Contract |
|---|---|
| Source | Exact UTF-8 source and its identity; caller-owned provenance label is diagnostic data, not permission to open a file |
| Language profile | Exact host grammar/compiler/checker/Unicode commitments and preparation ABI; neutral ABI additionally applies to the neutral artifact |
| Caller injection environment | Exact caller normalization map, retained in canonical key order as URI injections for each source `new`; distinct from the lexical binder environment |
| Guest context | Explicit read-only compile-time guest descriptions and opaque provider-reference slots; runtime-installed lexical selectors remain staged |
| Lowering options | Explicit policy, including existing guard-discharge options; no environment-variable override |
| Limits and cancellation | Source, parser, retained-family, traversal, environment, term, origin and output limits, with cancellation observable at bounded work points |

Nonempty environments are required. At minimum, their closed values must cover
the admitted scalar, list/map, quoted-name and structural FLT forms. The direct
node interface supplies actual `Par` values: it retains each original opaque
host name or installed handle, without reconstructing it from strings or
fingerprints. It has no synthetic owner/slot fields. The provider checks the
original handle and the requested operation at semantic use; transport does
not grant authority. In the subsequent neutral representation, these names
travel through explicit provider-owned reference slots, whose exact identity
and owner the node adapter validates. Malformed or unsupported
environment values receive a named rejection before source admission. Do not
silently discard the supplied environment or support only the empty map.

The node's `ProgramFrontend::prepare` passes its supplied environment to the
normalizer. `combine_p_new` in
`rholang/src/rust/interpreter/compiler/normalizer/processes/p_new_normalizer.rs`
copies the entire map into each `New.injections` ordered map, including entries
not used by that scope. `eval_new` in
`rholang/src/rust/interpreter/reduce.rs` first uses the runtime URI map and
consults injections only when the URI is absent there. Preserve that precedence,
the exact key/value association and unused entries; do not replace this behavior
with bare-variable substitution. The paths refer to the pinned node source,
not to a new frontend implementation.

Lexical binders still use the existing scope/shadowing rules. A URI-bound name
enters that lexical environment through its `new` binder; an injection-map key
alone does not bind a free source variable. Direct `PNew` and `PNewUris` lowering
use the same checked, immutable caller map; `Kont::New` passes its corresponding
ordered values to the existing checked fresh constructor. Generated fold and
service-reply scopes keep their own empty injection maps. Injection keys are map keys, not
fresh-URI declarations: do not impose the latter's nonempty-key rule on unused
map entries. The adapter validates values without inventing host authority.

### Direct import admission

[`CheckedCallerImports`](../../rholang-runtime/src/rholang_ast/imports.rs)
checks the original values without decoding or normalizing them again. The
currently admitted direct carrier covers integer, Boolean, string, URI, byte
array and raw-bit floating-point literals; present unforgeable names; and
closed lists/maps containing those values. An empty process (`Nil`) may occur
inside a collection but is not an admissible import root. Structural FLTs use
their existing list/name/value representation. A reflected language tag is
data, never a substitute for the provider's installed-language check.

Quoted scalar and collection names have these same `Par` carriers. Arbitrary
quoted executable processes do not: the existing node's injection reducer
accepts a singleton expression or unforgeable name, not an arbitrary process.
Such inputs and expression families outside this profile receive explicit
shape refusals. This boundary does not change their Rholang syntax or claim
that their broader import support is implemented.

Every admitted node must have empty locally-free metadata, no connective-use
flag and no executable sidecars. Collection metadata must also be closed,
remainders absent, and both fields of every map entry present. The check walks
all children, so falsifying only a parent's metadata cannot hide an open child.
Map order, duplicate entries and payload bytes are preserved rather than
silently sorted or deduplicated; only the outer caller-map keys are ordered.
These checks establish the stated closed carrier, not arbitrary `Par`
canonicality or authorization to execute an FLT.

The traversal proceeds as follows:

1. Check cancellation and the complete entry/key-byte bounds before retaining
   the ordered map. Sorting is bounded by those sizes and bracketed by
   cancellation checks.
2. For each root, charge its occurrence, then visit an explicit worklist.
   Check the local shape and payload bound. Before reserving child slots,
   charge their complete count and check required fields.
3. Use the node's existing structural child table, retaining every ordered
   occurrence. Return the original map only after every value succeeds.

The [shape model](../../formal/rocq/rho_bridge/theories/RholangImportShape.v)
proves the modeled field/refusal and bounded-charge laws. The
[transport model](../../formal/rocq/rho_bridge/theories/RholangSourceImports.v)
proves complete association, lexical separation, URI precedence and hereditary
worklist admission. Concrete schema classification, child-table correspondence
and cancellation are checked against the Rust tests; these models are not a
proof of all Rust code. Import-only bounds also do not replace whole-preparation
accounting for repeated source-scope copies and output construction. The checked
frontend must compose that separate budget before exposing this path publicly.

Public source preparation must preserve the node's existing order: negative
initial budget rejects before frontend invocation; preparation failure performs
no budget reset, merge-tracking clear or reducer invocation. A successful
trusted node adapter produces `PreparedProgram` for the existing metered entry,
which owns signature selection, budget reset, random-state preservation and
execution. The neutral frontend receives no live RSpace or mutable funding
ledger. Its accepted artifact is not an execution or funding certificate.

## The subsequent neutral output envelope

`RholangFrontendArtifactV1` names this neutral contract, independently of the
node's `PREPARED_PROGRAM_ABI_V1` and the versions of language/parser/semantic
images. Unsupported versions fail explicitly before payload interpretation.
The output comprises:

1. A finite typed Rholang semantic graph, root and explicit binder/reference
   structure. Its nodes denote the admitted operations below. There is no
   `Par`, protobuf blob, generic opaque process or source-text escape node.
2. Occurrence-based origins separate from shared semantic nodes. Distinct
   occurrences remain distinct when semantic nodes are shared. Origins carry
   source spans where the parser supplies them; generated nodes record their
   parent occurrence and transformation reason, not invented byte spans.
3. Owned per-session declarations and descriptors required to execute the
   graph: staged DDL/FLT obligations, predicate/capture descriptions and any
   admitted auxiliary-service specifications. These are data, not registered
   callbacks or newly granted language capabilities.
4. Stable diagnostics and completed preparation-usage records, including
   parser completeness/disambiguation evidence and the exact source/profile/
   environment commitments to which the result applies.
5. Explicit **pending host obligations** for provider binding, authority,
   semantic-resource projection and funding. A declaration requesting a right
   or a grade is not evidence that the request is authorized or funded.

The [typed graph's construction and observation laws](rholang-neutral-construction-contract.md)
and target homomorphism are a separate implementation boundary.
This envelope must not label a merely well-shaped
graph as canonical node bytes. The node emitter must establish the commuting
property with the reused lowerer under the same source environment, options,
and auxiliary descriptors, then use the existing canonical node operations.
The exact model/protobuf/collection baseline remains the approved node revision
`6781d1d671cc0b98b9de946b3871bdbb8e7f1280` plus reviewed isolated adapter commits.

Semantic identity excludes diagnostic origins, while the full preparation
record retains them and its provenance commitments. Erasing origins must not
erase capture maps, binder identity, operation ordering, obligations or semantic
resource evidence. Source locations and shared-node identifiers are different
coordinate systems; neither is a substitute for the other.

## Required source and operation closure

The concrete existing host-source witness is
[`semantic_service_wire_inline_module_qualified_flt_and_matched_reply`](../../rholang-runtime/src/semantic_service/wire/tests.rs).
It contains URI-bound services, an inline Module, nested receives, method-based
handle extraction, a qualified FLT and a nested reply pattern. It does not yet
contain practical regex rules or the direct installed guard. The complete
admitted closure is that witness **plus every operation and acceptance case in
the application contract**, not that fixture alone.

| Source family | Existing structural reuse | Required preserved meaning and focused checks |
|---|---|---|
| `PZero` | `lower_arm_p_zero` | Empty process, not an error placeholder |
| `PPar`, `PParInfix` | `ParFold`, `ParPair` | Source parallel composition and multiplicity; not parser ambiguity |
| Ordinary, quoted and polyadic sends | `desugar_surface_sugar_node`, send continuations | Existing name/quote semantics, argument versus list shape, persistence and payload order |
| `PNew`, `PNewUris` | `extend_env`, `unbind_uri_scope`, `New` continuation | Exact binder/URI association, shadowing, duplicate and invalid URI rejection |
| `PForUser`, receive rows and joins | `ForRows`, `for_source`, `for_pattern`, `assemble_receive` | Exact receive-slot order, persistence, nested continuation scope, all-or-none join behavior |
| Name quote/drop and variables | `enter_name`, variable handlers | Bound-name/process distinction, exact lexical lookup and quote/drop forwarding, stable unresolved-reference rejection; caller URI injections are handled by `new` |
| Quoted nested list patterns | `enter_pattern`, `PatListLit` | Literal tests and each capture in `[1,0,[[term,receipt]],usage]`; no dropped/reordered binding |
| Int, Bool, String | Existing scalar handlers and decoders | Exact scalar value and closed/open metadata; checked numeric range, no double string decoding |
| List and Map, including `Map()` | Existing container continuations | Ordered list elements; map key/value association and canonical target semantics; no pair flattening |
| Generic `MethodCall` | Existing `method` handler | `.get` and `.nth` for handle extraction; emit operations, leaving evaluation/type errors to the reducer |
| `DdlModule`, `DdlModuleImported`, `DdlTheory` and their declaration categories | `DdlLowerPlan`, `enter_ddl`, DDL continuation | Existing Greg/Mike AST envelope, parameter/module scope and exactly ordered embedded `Data(Proc)` leaves |
| Qualified FLT values and patterns, all three existing delimiters | Existing body staging, structural template and prepared-pattern paths | Exact selector/category, typed pieces/telescope and capture polarity; no text interpolation or second guest parse |
| Receive `where`, `Not`, admitted Boolean comparisons/connectives | Declared guard slots, `ForGuard`, existing guard substrate | Residual installed predicate descriptor and capture mapping; tri-state semantics, authority and funding checked at COMM |

Every generated source constructor reached by these forms must be accounted for
in the implementation matrix, including sugar and embedded DDL process leaves.
The classifier must use exact category/constructor identities from the pinned
specification. A display name, a substring search, or a success on the outer
`DdlModule` node does not cover its reachable children.

All six guest operations—nullable, derivative, full match, search, replace-first
and replace-all—use the same host FLT/service forms. Their computation and
terminal constructors belong to the declared guest grammar, not a growing list
of regex-specific host constructors. The frontend retains the required staged
operation; the provider supplies the installed parser and shared semantic
kernel. The `FullMatch` predicate role and actual atomic guard integration
remain mandatory implementation prerequisites, not unsupported optional forms.

### Pinned constructor inventory and child positions

The following inventory makes the family matrix concrete. It describes reuse
from the pinned specification and lowerer, not a string-based runtime dispatch
table. The implementation must use generated enum variants exhaustively and
retain their exact identities in diagnostics. A family entry does not admit
arbitrary future constructors with a similar name.

| Family | Existing constructors and structural owner | Child-position obligations |
|---|---|---|
| Core processes | `PZero`, `PPar`, `PParInfix`, `PDrop`, `PVar`, `PNew`, `PNewUris`, `PForUser` in `Drive::enter_proc` | Parallel members and bodies are terms; drop operands are names; receive sources, patterns, guards and continuations have distinct contexts |
| Direct sends | `POutput`, `PPersistOutput`, `POutputShort`, `PPersistOutputShort` | Ordinary channels are names; short quoted channels are processes; each payload retains its existing arity encoding |
| Empty/polyadic sends | `POutputEmpty`, `PPersistOutputEmpty`, `POutput2Plus`, `PPersistOutput2Plus`, `POutputShortEmpty`, `PPersistOutputShortEmpty`, `POutputShort2Plus`, `PPersistOutputShort2Plus` in `desugar_surface_sugar_node` | Reuse the empty/list payload construction, with distinct origins for generated list and quote nodes |
| Quoted-name/Nil sends | `POutputNil`, `PPersistOutputNil`, `POutputNilEmpty`, `PPersistOutputNilEmpty`, `POutputNil2Plus`, `PPersistOutputNil2Plus`, `POutputQuoted`, `POutputQuotedEmpty`, `POutputQuoted2Plus` in the same desugarer | Preserve the existing name-to-process conversion; do not invent additional quoting |
| Names and URI leaves | `NQuote`, `NQuoteShort`, `NQuoteNil`, `NParen`, `NVar`, `UriText` | Quotes enter process context, parentheses preserve name context, URI decoding stays with `unbind_uri_scope` |
| Scalars and containers | `CastInt`, `CastBool`, `CastStr`, `CastList`/`ListLit`, `CastMap`/`MapLit`, `MapEmpty` | Reuse native literal decoders; list elements and both map slots preserve their current term or pattern context |
| Methods and guards | `MethodCall`, `Eq`, `Ne`, `Lt`, `Gt`, `LtEq`, `GtEq`, `And`, `Or`, `Not`, `Implies` | Receiver and arguments remain structural operations; installed FLT atoms stay residual under the existing guard combinators |
| Foreign regions | `PFlt`, `PFltFence`, `PFltBrace` | Preserve `FltNode` selector/category and every ranged text/hole piece; construction, receive-pattern and guard positions have different obligations |

Receive row and input-bind decomposition must reuse the existing receive
classifiers, `bind_pattern_proc`, `bind_flt_node`, `ForRows`, `for_source` and
`for_pattern`. The required row constructors are `ForRowSingleNoWhere`,
`ForRowSingleWhere`, `ForRowNoWhere` and `ForRowWhere`. The non-query binding
closure is `InputBind`, `InputBindPersistent`, `InputBindPolyadic`,
`InputBindPersistentPolyadic`, `InputBindEmpty`, `InputBindEmptyPersistent`,
`InputBindQuoted` and `InputBindQuotedPersistent`. The application requires
ordinary quoted patterns, nested list captures, joins and guarded rows.
Their enum-to-slot mapping is part of the
receive implementation gate: no hand-written second parser or inference from
the displayed receive text. Query/other row forms outside the admitted profile
must reject by their exact constructor until their own semantics are admitted.

The structural DDL child closure already has a separate exhaustive owner,
[`DdlLowerPlan`](../../rholang-runtime/src/ddl_ast.rs):

| DDL constructors | Existing plan owner | Required positive and negative obligations |
|---|---|---|
| `DdlModule`, `DdlModuleImported`, `DdlTheory`, `DdlModuleTheoryItem`, `DdlModuleProcItem`, `DdlParamDecl` | Root, module-item and parameter tasks | Preserve declaration order, parameters and embedded process scope; reject malformed projection and unresolved references |
| `DdlPathName`, `DdlPathQualified`, `DdlImportsNonEmpty`, `DdlImportModuleAs`, `DdlImportFromModule` | Path tasks and `import_tasks` | Preserve path components, aliases and decoded URI data; registry resolution remains capability-controlled; disk loading remains unavailable |
| `DdlTheoryDiff`, `DdlTheoryJoin`, `DdlTheoryMeet`, `DdlTheoryEmpty`, `DdlTheoryFree`, `DdlTheoryLet`, `DdlTheoryBraceGroup`, `DdlTheoryParenGroup`, `DdlTheoryApply`, `DdlTheoryRef` | `theory_expression_task` | Preserve theory algebra, grouping, application order and local theory bindings; never reparse theory text |
| `DdlTheoryTypes`, `DdlTheoryExports`, `DdlTheoryReplacements`, `DdlTheoryTerms`, `DdlTheoryEquations`, `DdlTheoryRewrites`, `DdlTheoryData`, and the seven corresponding `Implicit` variants | `theory_expression_task`, `build`, `implicit_build` | Preserve the explicit/implicit Empty base and builder order; each `Data` process re-enters the same scoped host worklist |
| `DdlCategory`, `DdlExportDirect`, `DdlExportRename`, `DdlReplacementRule`, `DdlTerm` | Category/export/replacement/term tasks | Preserve names, result categories and ordered bindings/syntax; reject invalid category/rule references through the shared validator |
| `DdlBindingPlain`, `DdlBindingBinder`, `DdlSortHashBag`, `DdlSortSet`, `DdlSortList`, `DdlSortCategory` | Binding and sort tasks | Preserve binder direction and collection kind; invalid binding/category combinations must not become an untyped list |
| `DdlSyntaxProjection`, `DdlSyntaxTerminal`, `DdlSyntaxArgument` | Syntax-item tasks and shared captured-string decoder | Decode terminals/separators once, retaining literal contents and projection identity; malformed capture rejects |
| `DdlEquationDirect`, `DdlEquationConditional`, `DdlFreshness`, `DdlFreshnessOne`, `DdlFreshnessMore` | Equation tasks and `freshness_tasks` | Preserve every freshness condition and equation operand; no dropped condition |
| `DdlRewriteDirect`, `DdlRewriteConditional`, `DdlPremise`, `DdlPremiseOne`, `DdlPremiseMore` | Rewrite tasks and `premise_tasks` | Preserve every named rewrite and premise in order; no unconditional replacement of conditional rules |
| `DdlRuleAstSubst`, `DdlRuleAstSExp`, `DdlRuleAstAbs`, `DdlRuleAstCollectionEmpty`, `DdlRuleAstCollection`, `DdlRuleAstRemainderOnly`, `DdlRuleAstCollectionRemainder`, `DdlRuleAstVar` | `rule_ast_task` | Preserve substitution/binding, application argument order, collection membership and remainder identity |
| `DdlRuleAstItemOne`, `DdlRuleAstItemMore`, `DdlRuleAstTailRemainder`, `DdlRuleAstTailMore` | `rule_ast_items`, `rule_ast_remainder_tail` | Preserve all items and the final remainder with iterative traversal; no tail omission |

Each row requires a structural preservation test plus its rejection cases when
the target is factored. The practical application supplies required positive
paths; targeted constructor tests cover alternate forms without pretending
they already execute through the public node. The existing exhaustive DDL plan
must remain the owner of this larger child closure, rather than being replaced
with a regex-specific declaration subset.

## Stable rejection, not convenience behavior

The new adapter must not carry two test-runner conventions into public source
admission. Current `lower_name_var` can emit a string beginning `mtl:`, and
`lower_proc_var` can emit a send on `mtl#out` for unresolved references. Public
admission instead reports `UnresolvedName` or `UnresolvedProcess` at the exact
occurrence. Likewise, `lower_proc_alternatives` appends distinct alternatives
into an executable parallel process. The frontend must not call that branch
as its public ambiguity policy.

Complete candidate families may coalesce only readings proved to have the same
exact semantic graph, retaining all relevant occurrence evidence. A digest
match alone is not equality. More than one surviving semantic graph is
`AmbiguousSource`; an incomplete family is `IncompleteParse`, even when its
current prefix has one member. Zero complete readings is `NoParse`. No top-k
cut, first-reading election or executable parallelization resolves ambiguity.

| Rejection family | Required distinction |
|---|---|
| Version/profile | Unsupported neutral ABI, incompatible host/parser/checker/Unicode commitments |
| Parse | No parse, surviving semantic ambiguity, incomplete/exhausted search |
| Constructor | Exact category and constructor not in the admitted profile; do not collapse to `Nil` |
| Environment/scope | Invalid or duplicate binding, unsupported value, unresolved reference, dangling index or invalid URI association |
| Structural DDL/FLT | Existing projection failure, malformed template, wrong category/telescope, missing explicit guest or provider binding |
| Resources | Stage and exhausted dimension; cancellation and allocation failure remain distinguishable |
| Host admission | Missing or stale authority, missing resource evidence, invalid projection or insufficient funding; never a parse-success Boolean |

These are stable typed diagnostic families, not arbitrary panic/debug strings.
Error formatting must be bounded. Required but unimplemented application forms
remain blockers of this profile. Other forms, including unsupported numeric
folds or source-level cost annotations, retain their campaign implementation
owners and must receive explicit rejections until admitted; no fallback to the
legacy parser or omission of their auxiliary machinery is permitted. This does
not waive the existing metered funding path for ordinary unsigned source.

## Session and dependency boundaries

`DdlLowerPlan` already separates text, quoted text, embedded process slots and
postorder node assembly. Factor its `finish(Vec<Par>)` target dependency;
preserve the exact plan and shared string decoder. Embedded process leaves
re-enter the same scoped worklist, including alternating DDL and `Data` nesting.

The current guard-discharge implementation depends on node `Par`, the pure
evaluator and spatial oracle. Retain guards and options in the neutral graph;
reuse that implementation at the node emission boundary. Do not create a
neutral Boolean evaluator or silently disable the production discharge policy.
Installed predicate obligations remain residual regardless of literal
groundness, as specified by the application contract.

### Required direct whole-body session

The first demonstration requires normal success/error cleanup and rejection of
nested lowering. Recovery after an internal Rust panic, including validation of
the compiler backend's unwinding behavior, belongs to the following milestone.
The unwind laws below specify that later recovery contract; they are not a
claim that the demonstration supports catching panics and continuing execution.

Direct lowering must use a private owned-session entry to the existing driver
with `Seed::Body`, preserving whole-body staging rather than substituting the
narrower process entry. Its admission policy must explicitly be `Public`, with
an explicit resolver and
lowering options; production guard options alone do not select Public scope.
The successful low-level result must move ownership of the `Par`, all ordered
`FoldSpec` service descriptions and the `GuardDischargeReport` together. A fold
trampoline without its matching service description is not a complete result.

Fold specifications and guard reports use thread-local storage (TLS). Retain
that existing accumulator pair. The required session bracket makes it private
to one synchronous lowering call while the owner is active.
The ordering matters because a nested call must not erase the outer call's work:

1. Check for an active owned session and reject reentry with
   `ReentrantLoweringSession` before clearing, taking or otherwise touching its
   payload. Rejection leaves the outer session intact.
2. For an accepted entry, establish private empty fold and guard accumulators
   under an unwind-safe ownership guard, then run the same whole-body driver.
3. On direct success, move both accumulators into the result with the returned
   `Par`, release ownership and leave TLS empty. Publish only that complete
   bundle.
4. On lowering failure or stack unwinding, discard both partial outputs and
   release the session. No bundle is published. This unwind requirement is not
   a promise of recovery from process abort or allocator failure.

The gate must cover callbacks as well as nested owned entry. Every raw legacy
or public process, name, formula and term lowering entry must return
`ReentrantLoweringSession` during an active owned session, before entering the
driver, invoking a resolver or performing lowering work. The private owner
entry reaches the same driver without routing through those rejected public
entries. This preserves existing lowering decisions while preventing a callback
from appending to or consuming the outer call's outputs.

Public legacy fold and guard-report clear/take accessors must check for an
active owner before borrowing either accumulator. Their existing signatures
cannot return a lowering error, so misuse must panic with an explicit
owned-session diagnostic. Private owner clear/drain operations remain available
for acquisition, completion and cleanup. A caught accessor panic or handled
lowering rejection leaves the outer state unchanged. If a panic escapes the
callback, unwinding through the owned resource acquisition is initialization
(RAII) guard discards the partial outputs and releases ownership as above.

On successful legacy `lower_rholang_term_with_folds`, release the session,
republish its owned guard report and return the owned process and folds. This
preserves the explicit `take_guard_discharge_report` compatibility accessor;
publication must occur only after ownership is released. The direct API returns
its guard report in the owned bundle and leaves
no report in TLS. An accepted later owned call starts with empty accumulators;
a rejected nested call must not clear a report or folds belonging to its owner.

No asynchronous suspension is permitted while this TLS bracket is live: a
thread-local owner cannot safely follow a suspended task to another thread.
Sequential calls must start without inherited fold or guard output. The parser's
separate thread-local variable cache still needs its own identity-isolation
boundary; owning these lowering outputs does not establish parser isolation.

Fold service indices use the existing one-byte channel representation. Accept
indices 0 through 255 only. If the next index is 256 or greater, reject before
recording its `FoldSpec` or allocating its service channel; truncation would
alias an earlier service. This representability check is not a preparation-work
budget and does not authorize executing otherwise unsupported fold forms.

The [owned-session model](../../formal/rocq/rho_bridge/theories/RholangOwnedSession.v)
is the ownership-protocol reference. Its direct-session extension and concrete
Rust correspondence must establish the bracket, callback rejection,
compatibility publication and index rules above; a finite state model alone does
not prove Rust cleanup, memory bounds or source admission.
These are required semantics, not an implementation-complete claim. Even a
successful low-level bundle is **not a public source admission certificate**:
caller imports, preparation resource budgets, checked frontend adaptation,
provider binding and qualified FLT `where` integration remain required sibling
obligations before public activation.

### Direct driver storage reservations

The direct driver's storage layer borrows a reservation callback from the
existing `ReflectedCodecBudget`. The live session owner supplies that callback;
there is no global meter, new worklist implementation or second lowering pass.
Legacy internal entry retains its explicit unmetered policy. Neither that entry
nor the storage-metered entry alone may certify public preparation.

A **work unit** is a declared logical operation charge. A **slot** is one
temporary roster, pending-job or value-stack position, represented by four
fixed payload-allowance units. These are cumulative reservations, not a peak
heap measurement: native object size, vector spare capacity, allocator overhead,
resident memory and semantic gas are different quantities. Releasing a slot
does not replenish either allowance.

| Storage operation | Work units reserved | Slots reserved |
|---|---:|---:|
| Initial empty job/value stacks | 1 | 128 |
| Seed or subsequent job push | 1 | 1 |
| Job pop, including the final empty probe | 1 | 0 |
| Value push | 1 | 1 |
| Single-value pop | 1 | 0 |
| Ordered suffix of length `n` | `1 + n` | `n` |
| Shared consuming pair reduction | 3 | 1 |
| Shared consuming `n`-value reduction | `2 + n` | `1 + n` |
| Temporary roster with admitted upper bound `n` | `n` | `n` |

Check variable sums, arities and the multiplication by four before reservation.
The shared meter polls cancellation and checks both remaining dimensions before
changing either balance. Only then may the storage operation execute. A later
shape or constructor failure retains earlier charges, preserves any unconsumed
prefix and publishes no substitute result. The driver propagates the error to
the existing owned-session cleanup.

Child scheduling reserves the roster before allocating or advancing its
iterator, polls cancellation before every advance, rejects an exceeded bound
before growing the roster, and checks exact continuation arity before pushing
jobs. Reversed insertion into the unchanged last-in, first-out work stack
preserves source order and multiplicity. Bag/set sorting, formula classification
and DDL planning retain their existing semantics; their immediate temporary
rosters are reserved at their producing call sites. The borrowed formula
classifier's finite separation roster is precharged before invoking it.

The [reservation model](../../formal/rocq/rho_bridge/theories/RholangPreparationReservation.v)
composes the existing atomic-debit and worklist laws. Its generic reservation
theorem applies to the concrete four-unit slot scale; its specialized push and
suffix theorems establish shape and order with abstract slot units. Kernel
checking these laws does not prove all Rust call sites. Concrete tests must
also establish refusal before mutation, checked arithmetic, retained charges,
ordered values, byte-equivalent successful lowering and clean subsequent
sessions.

Storage reservation is only one part of complete preparation accounting.
Scope opening and copying, source analyses, sorting comparisons, constructed
values and metadata, caller-import copies, DDL construction and FLT/service
side outputs still require their own precharges through the same allowance.
Charging the push of an already constructed `Par` does **not** pay for its
construction. Public activation requires that composition; generic allocator
failure and panic recovery are not claims of this storage contract.

### Derived lexical environments

Environment admission wraps the existing `extend_env`, `extend_slots`,
`in_pattern_position` and empty-context helpers. It does not change variable
identity, slot order, shadowing, scope width or lexical resolution. All driver
derivations use the same borrowed reservation callback before constructing
copied maps, not merely before appending an already built environment.

Let $`n`$ count old binder/hole entries plus every added slot occurrence,
including duplicates that an insertion will overwrite. Let $`s`$ count old
entries shifted by an extension; it is zero for a pattern-context copy.
Let $`b`$ be the sum of owned key-byte lengths: optional Moniker pretty names
and FLT-hole strings. An unnamed variable contributes zero bytes but still
counts as an entry. Byte lengths, not character counts, determine this charge.

| Phase | Work allowance | Payload allowance |
|---|---:|---:|
| Borrowed key-length inspection | $`n`$ | 0 |
| Copy, shift and retain the derived environment | $`1+n+s+b`$ | $`4(1+n)+b`$ |

The second phase includes one retained environment record and its arena append;
there is no second append debit. Entries and records use the same four logical
units as driver storage. These are cumulative logical entry/shift/byte charges,
not physical hash-table capacity, collision counts, allocator overhead or a
CPU-time bound. Resolver and checked caller-import services remain shared by
reference; this charge does not copy their contents.

The implementation follows this sequence:

```text
check that the next environment identifier is representable
read container lengths and check the occurrence-count sum
reserve the complete inspection work
for each borrowed key occurrence:
    poll cancellation
    add its byte length with checked arithmetic
poll cancellation after the final occurrence
check and reserve the complete copy/shift/retention cost
invoke the existing environment helper
append its result through the existing fallible environment arena
publish the new identifier only on success
```

Inspection allocates no roster or key copies. Aggregate admission without
cancellation is independent of hash-map iteration order; no per-key payload
debit exposes a partially paid, order-dependent prefix. A returned cancellation
or exhaustion error publishes no derived environment. A later helper or arena
failure retains earlier successful charges. Polling precedes the prepaid
helper; cancellation arriving during that helper is not sampled again before
its arena append. This does not claim interruption inside a standard-library
map operation.

The cached empty context always derives from the root, not the innermost
receive. Public mode retains root policy and service references while clearing
lexical bindings. The explicit compatibility harness retains its existing
fresh-default convention. Empty-context creation still reserves one record,
and the cache is updated only after successful insertion.

The [environment reservation model](../../formal/rocq/rho_bridge/theories/RholangEnvironmentReservation.v)
composes the existing reservation and checked lexical-extension laws. It proves
exact aggregate charges, iteration-order independence without cancellation,
retained charges on refusal and unchanged successful helper results. Concrete
Rust tests establish the borrowed-input, polling, arithmetic and publication
correspondence; the functional proof alone does not establish heap separation.
Scope opening/closing, source AST copies and other source walkers remain
separate parts of complete bounded preparation.

### Subsequent neutral dependency boundary

Neutrality applies to the actual Cargo dependency closure, including proc-macro
and build dependencies. The full backend build retains the path
`languages -> macros -> rholang-codegen -> models`. Disabling only generated
consumer items cannot remove that path. The existing runtime bridge also directly depends on node
Rholang, models, the pure evaluator and RSpace. Factor the pure analyses/types
and target adapters along these existing seams, then check the complete graph.
Neither an API rename nor a target-only dependency report proves independence.

The shared pure analyses now live in the AST crate:
[binder-float analysis](../../ast/src/analysis/binder_float.rs) derives the
declared float satellites and their coverage classification, while
[guard-obligation analysis](../../ast/src/analysis/guard_obligations.rs) collects
the obligations used by both macro generation and backend admission. The old
backend paths re-export those same definitions. Float satellites retain the
first declared occurrence per constructor; guard obligations retain the
existing sorted, deduplicated set. Neither analysis evaluates a guest term or
requires node values. The
[relocation check](../../scripts/verify-pure-analysis-relocation.mjs) compares
their complete implementation bodies with the pinned pre-extraction source,
allowing only explicit module-path changes and formatting. This extraction is
not itself the backend feature gate.

### Parser package isolation

The parser boundary uses distinct Cargo packages, not another language
specification. `mettail-rholang-syntax` loads the existing
[`languages/src/rholang.rs`](../../languages/src/rholang.rs) by source path,
including its existing helper modules. Its `parser-macros` dependency compiles
the same [`macros/src/lib.rs`](../../macros/src/lib.rs) source as the full macro
package, but has no runtime-backend feature or dependency. The definitions and
generators have one source; Cargo compiles them in separate dependency contexts.

| Package | Backend selection | Role |
|---|---|---|
| `macros` | `runtime-codegen`, enabled by default | Existing full generator; language backend features enable it |
| `parser-macros` | No backend feature exists | Shared parser/AST generator with a permanently node-independent dependency closure |
| `mettail-rholang-syntax` | No Rho or Dovetail backend feature exists | Existing Rholang syntax, structural operations, and metadata for the neutral frontend |

Cargo feature selection is additive. A parser consumer requesting no default
features on the full macro package cannot prevent another consumer from
enabling its backend. Distinct package identities prevent that union from
introducing backend edges into the parser package. The
[dependency-isolation check](../../scripts/verify-parser-dependency-isolation.mjs)
walks normal and build dependencies in an all-feature workspace resolution,
with the original backend macro enabled. It rejects reachable node/backend
packages and cycles, and checks that both macro packages use the same source.
This graph evidence does not establish parser equivalence or interpreter wiring.

Host-side selection guards the actual backend-generator invocation, not only
the generated `include!` or module declaration. The enabled branch retains the
existing generator functions and consumer gates. When backend generation is
unselected, each equation orientation, rewrite, and fold receives an explicit
`Suppressed` disposition stating that decision. Order, multiplicity, declared
versus injected origin, and the existing construct census are retained. This
is not a claim of semantic rejection or successful lowering. Source semantic
artifacts, guards, shared structural operations, and parser generation remain
available; no grammar is converted into a semantics-free `parse_only` fixture.

Parser-only generated files live beneath
`target/generated/parser-only/<consumer-package>/<language>/`; full backend
output retains its existing directory. The separate directories prevent the
two builds from overwriting each other's metadata or included source. They do
not select a different grammar.

The [selection model](../../formal/rocq/runtime_grammar/theories/ParserBackendSelection.v)
proves exact enabled output, absence of disabled invocation, retained inventory
projection, and preservation of a closed dependency region under added external
edges. It also exhibits why shared-package feature union defeats local opt-out.
Actual source, manifest, generated-output, and parser tests must discharge the
model's correspondence obligations; the model alone does not prove Rust or
Cargo correct. The neutral lowering and node admission connection remain
separate implementation steps.

The [source-correspondence check](../../scripts/verify-parser-feature-correspondence.mjs)
compares the enabled generator bodies and shared grammar/helpers against the
pre-cut commit. The isolated package also reuses the existing DDL, FLT, and
binder syntax suites by source path, so the boundary is tested with the same
assertions rather than a separate reduced grammar corpus.

All source traversal, target assembly, scope substitution and teardown must
retain explicit worklists or existing stack-safe representations. Charge
bounded work and storage before growth. Preserve collection mode/arity and
ordered repeated occurrences; do not introduce a second canonicalizer while
factoring the target operations.

## Authority, semantic grades and funding

The node already exposes generalized `GsltPresentation` and
`OslfResourceLogic<G>` interfaces, with the Rholang specialization reusing its
existing demand and funding analyzer. The frontend emits the required
structural/semantic evidence requests and commitments; it does not choose a
validator, signature, balance or alternate ledger.

Language installation, FLT construction/matching, reduction/observation and
predicate evaluation each retain their distinct rights and checked receipts.
Provider lifecycle/runtime/matcher integration must bind them to the same
installed-language service. The actual COMM/effect boundary revalidates live
authority and consumes the host's checked resource projection before mutation.
The semantic-grade projection owner must supply any missing required slice;
neither `Pure` nor a successful syntax check proves that slice unnecessary.

Parser ranking, frontend logical work, semantic Cost(G) grade, validator demand
and settlement are separate outputs or obligations. A frontend cannot fabricate
`CostTransitionPlan` or `ResourceCertificate` values. The existing prepared
node handoff performs one metered entry with unchanged random state, without
reparsing. Raw evaluation and checkpointed convenience evaluation retain their
different rollback contracts.

## Acceptance sequence and proof scope

The application matrix drives the admitted-domain model before nontrivial
checking code. The model must cover total form classification, rejection of
unsupported occurrences, complete-family selection, origin erasure and the
separation of declarative obligations from checked host evidence. A Boolean
named `admitted` or `canonical` is not a proof of the actual Rust code.

The closed
[frontend admission protocol model](../../formal/rocq/rho_bridge/theories/RholangFrontendAdmission.v)
defines term, name, pattern, guard and declaration positions; structural
semantic occurrences; separate diagnostic origins; pending obligations; and
typed classification outcomes. Its admission sequence is:

1. Outstanding enumeration work yields `IncompleteParse`.
2. Check that enumerated coordinates are a permutation of the retained finite
   forest's coordinate roster, using the standard library's merge-stack sort.
   Only those coordinates are sorted; original candidates are never reordered.
3. A complete empty forest yields `NoParse`. Otherwise compare every retained
   graph exactly, erasing diagnostic origins only. Unequal graphs yield
   `AmbiguousSource` before support classification can discard an alternative.
4. Scan every retained occurrence with a reverse accumulator. Unsupported
   occurrences reject with their original flattened occurrence coordinate;
   success retains the complete original candidate roster and each occurrence's
   pending obligations.

The proved laws cover exact finite-roster coverage on successful checks,
total modeled-form classification, complete nonempty agreement on success,
original order and multiplicity, first unsupported occurrence with its original
origin, origin-invariant classification, and retained semantic/authority/
projection/funding obligations for every classified FLT guard.

This is a source protocol model, **not** the typed target IR or a proof that the
parser has enumerated every source reading. Parser-to-forest correspondence,
generated-constructor mapping, lexical resolution, structural validation,
canonical target emission, bounded Rust traversal and checked host admission
remain explicit implementation/refinement gates. Exact graph equality is
conservative: the model does not invent alpha-equivalence, normalization or
hash-based equality. Its retained-forest coverage law cannot certify a forest
whose producer has already pruned a source reading.

The existing
[RholangAstLowering model](../../formal/rocq/rho_bridge/theories/RholangAstLowering.v)
proves a small structural transport calculus, list/map/bag preservation and
receive indices. It neither establishes arbitrary canonical protobuf equality
nor justifies public parallel execution of parse alternatives. Reuse those laws
only within their actual scope. Typed IR/target laws, the worklist factoring,
each constructor family, DDL/FLT sessions and full emitter composition need
their own precise source correspondence and focused tests.

Direct-path acceptance proceeds through the checked composition dependency
gate, the reused whole-body worklist with explicit sessions and Public scope,
caller imports and bounded preparation, checked prepared admission, shared
provider and guarded COMM integration, then actual public eval/gRPC. Subsequent
neutral extraction additionally requires pure dependency isolation, typed
IR/target laws, constructor-family migration and node-emission correspondence;
those obligations are retained, not prerequisites to the first direct revision.
The source application must run unchanged through the public path. Compare
canonical node bytes, binders, diagnostics, costs,
receipts, effects and negative/refusal behavior—not merely printed output.
Independent public-node and application gates remain necessary after locally
passing constructor checks. Optimization cannot replace any of these required
semantics or admission obligations.
