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
the admitted scalar, list/map, quoted-name and structural FLT forms. An opaque
host name or installed handle is transported through an explicit provider-owned
reference slot, not serialized as a forgeable string or recreated from a
fingerprint. The node adapter validates the exact slot identity and its owner;
the neutral representation does not grant authority. Malformed or unsupported
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
alone does not bind a free source variable. The current MeTTaIL `Kont::New`
supplies an empty injection map, so nonempty caller-environment support remains
an explicit factoring/emitter obligation. Injection keys are map keys, not
fresh-URI declarations: do not impose the latter's nonempty-key rule on unused
map entries. The adapter validates values without inventing host authority.

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

Fold specifications and guard reports currently use thread-local storage, and
the parser uses a thread-local variable cache. A compilation session must own
its required outputs and isolate variable identity. On success, return every
required descriptor; on failure, discard private partial outputs and clear or
restore session-local state. Reentrant and sequential requests must not inherit
one another's names, fold sites, diagnostics or capability references. An
artifact with a fold trampoline but without its service specification is not
complete.

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

Acceptance proceeds through pure dependency isolation, typed IR/target laws,
the shared worklist and required constructor families, explicit sessions,
node emission/prepared admission, shared provider and guarded COMM integration,
then actual public eval/gRPC. The source application must run unchanged through
that final path. Compare canonical node bytes, binders, diagnostics, costs,
receipts, effects and negative/refusal behavior—not merely printed output.
Independent public-node and application gates remain necessary after locally
passing constructor checks. Optimization cannot replace any of these required
semantics or admission obligations.
